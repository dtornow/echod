//! Bounded Rover trace search.
//!
//! This module is intentionally not part of the trusted argument. [`check`]
//! accepts only after [`super::replay`] independently validates the certificate.

use crate::Time;

use super::replay::{Action, Certificate, ReplayState};
use super::{Proc as ExecProc, Spec as ExecSpec};
use super::super::comm::{BoundaryEvent, ProcessEvent};
use super::super::spec::Spec as SpecModel;

/// Search limits. `max_steps` counts both visible and hidden Rover steps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckConfig {
    pub max_steps: usize,
}

impl CheckConfig {
    /// A Lean-TraceChecker-style default: room for one visible step and
    /// roughly two hidden steps per supplied boundary event.
    pub fn for_trace_len(events: usize) -> Self {
        Self {
            max_steps: events.saturating_mul(3).saturating_add(1),
        }
    }
}

fn visible_action<M: ExecSpec>(
    event: &BoundaryEvent<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >,
) -> Action<
    <M::Spec as SpecModel>::Pid,
    <M::Spec as SpecModel>::Message,
> {
    match event {
        BoundaryEvent::Input {
            recipient,
            at,
            message,
        } => Action::Inject {
            recipient: recipient.clone(),
            at: *at,
            message: message.clone(),
        },
        BoundaryEvent::Output {
            sender,
            at,
            message,
        } => Action::Observe {
            sender: sender.clone(),
            at: *at,
            message: message.clone(),
        },
    }
}

/// Candidate hidden process actions at `at`.
fn hidden_actions<M: ExecSpec>(
    world: &ReplayState<'_, M>,
    at: Time,
) -> Vec<Action<
    <M::Spec as SpecModel>::Pid,
    <M::Spec as SpecModel>::Message,
>> {
    if at < world.now {
        return Vec::new();
    }
    let outside = world.model.outside();
    let processes: Vec<_> = world
        .process
        .iter()
        .enumerate()
        .filter(|(_, (pid, _))| *pid != outside)
        .map(|(slot, (pid, _))| (slot, pid.clone()))
        .collect();
    let mut actions = Vec::new();

    for (slot, process) in processes {
        let mut events = vec![ProcessEvent::Timeout];
        events.extend(
            world
                .network
                .iter()
                .filter(|envelope| envelope.recipient == process)
                .map(|envelope| ProcessEvent::Receive {
                    sender: envelope.sender.clone(),
                    message: envelope.message.clone(),
                }),
        );
        let state = &world.process[slot].1;
        for event in events {
            let outcomes = state.on_event(world.config, at, &event);
            actions.extend((0..outcomes.len()).map(|outcome| Action::Process {
                slot,
                process: process.clone(),
                at,
                event: event.clone(),
                outcome,
            }));
        }
    }
    actions
}

fn search_from<M: ExecSpec>(
    world: ReplayState<'_, M>,
    events: &[BoundaryEvent<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >],
    visible: usize,
    remaining: usize,
    certificate: &mut Certificate<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >,
) -> bool {
    if visible == events.len() {
        return true;
    }
    if remaining == 0 {
        return false;
    }

    // Prefer consuming the visible event now. If that is not yet legal, or
    // leads to a dead end, try hidden process steps first.
    let action = visible_action::<M>(&events[visible]);
    let mut next = world.clone();
    if next.apply(&action).is_ok() {
        certificate.push(action);
        if search_from(next, events, visible + 1, remaining - 1, certificate) {
            return true;
        }
        certificate.pop();
    }

    let target = events[visible].time();
    let mut times = vec![world.now];
    if target != world.now {
        times.push(target);
    }
    for at in times {
        for action in hidden_actions(&world, at) {
            let mut next = world.clone();
            if matches!(next.apply(&action), Ok(None)) {
                if next.same_snapshot(&world) {
                    continue;
                }
                certificate.push(action);
                if search_from(next, events, visible, remaining - 1, certificate) {
                    return true;
                }
                certificate.pop();
            }
        }
    }
    false
}

/// Search for a candidate certificate. Failure means only that this bounded
/// search did not find one; no completeness claim is made.
pub fn search<M: ExecSpec>(
    model: &M,
    config: &<M::Spec as SpecModel>::Config,
    events: &[BoundaryEvent<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >],
    limits: CheckConfig,
) -> Option<Certificate<
    <M::Spec as SpecModel>::Pid,
    <M::Spec as SpecModel>::Message,
>> {
    let world = ReplayState::initial(model, config);
    let mut certificate = Vec::new();
    search_from(world, events, 0, limits.max_steps, &mut certificate).then_some(certificate)
}

/// Search and independently replay. `Some(certificate)` is the acceptance
/// result covered by [`super::replay`]'s Verus soundness theorem.
pub fn check<M: ExecSpec>(
    model: &M,
    config: &<M::Spec as SpecModel>::Config,
    events: &[BoundaryEvent<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >],
    limits: CheckConfig,
) -> Option<Certificate<
    <M::Spec as SpecModel>::Pid,
    <M::Spec as SpecModel>::Message,
>> {
    let certificate = search(model, config, events, limits)?;
    super::replay(model, config, events, &certificate).ok()?;
    Some(certificate)
}
