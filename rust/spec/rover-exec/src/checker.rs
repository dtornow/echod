//! Bounded Rover trace search.
//!
//! This module is intentionally not part of the trusted argument. [`check`]
//! accepts only after [`super::replay`] independently validates the certificate.

use super::replay::{Action, Certificate, ReplayState};
use super::{Proc as ExecProc, Spec as ExecSpec};
use echod_rover::rover::comm::{BoundaryEvent, ProcessEvent, Time};
use echod_rover::rover::spec::Spec as SpecModel;

/// Search limits. `max_steps` counts both visible and hidden Rover steps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckConfig {
    pub max_steps: usize,
    pub max_nodes: usize,
}

impl CheckConfig {
    /// Room for visible events plus request delivery and internal work.
    pub fn for_trace_len(events: usize) -> Self {
        Self {
            max_steps: events.saturating_mul(10).saturating_add(100),
            max_nodes: 100_000,
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
        BoundaryEvent::Clock { at } => Action::Clock { at: *at },
    }
}

/// Candidate hidden process actions at `at`.
fn hidden_actions<M: ExecSpec>(
    world: &ReplayState<'_, M>,
    at: Time,
    duplicate_delivery: bool,
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
        // Prefer the newest delivered message. Visible responses usually come
        // from that transition; timeouts remain available after receives.
        let mut events: Vec<_> =
            world
                .network
                .iter()
                .rev()
                .filter(|envelope| envelope.recipient == process)
                .filter(|envelope| duplicate_delivery || !world.delivered.contains(envelope))
                .map(|envelope| ProcessEvent::Receive {
                    sender: envelope.sender.clone(),
                    message: envelope.message.clone(),
                })
                .collect();
        events.push(ProcessEvent::Timeout);
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

fn produces_target<M: ExecSpec>(
    before: &ReplayState<'_, M>,
    after: &ReplayState<'_, M>,
    target: &BoundaryEvent<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >,
) -> bool {
    let BoundaryEvent::Output { sender, message, .. } = target else {
        return false;
    };
    let outside = before.model.outside();
    after.network[before.network.len()..].iter().any(|envelope| {
        envelope.sender == *sender
            && envelope.recipient == outside
            && envelope.message == *message
    })
}

/// Search for a candidate certificate. Failure means only that this bounded
/// search did not find one; no completeness claim is made.
fn search_with<M: ExecSpec>(
    model: &M,
    config: &<M::Spec as SpecModel>::Config,
    events: &[BoundaryEvent<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >],
    limits: CheckConfig,
    rank: impl Fn(
        &BoundaryEvent<
            <M::Spec as SpecModel>::Pid,
            <M::Spec as SpecModel>::Message,
        >,
        &Action<
            <M::Spec as SpecModel>::Pid,
            <M::Spec as SpecModel>::Message,
        >,
    ) -> usize,
) -> Option<Certificate<
    <M::Spec as SpecModel>::Pid,
    <M::Spec as SpecModel>::Message,
>> {
    let initial = ReplayState::initial(model, config);
    let mut stack = vec![(initial, 0usize, limits.max_steps, Vec::new())];
    let mut explored = 0usize;

    while let Some((world, visible, remaining, certificate)) = stack.pop() {
        if visible == events.len() {
            return Some(certificate);
        }
        if remaining == 0 || explored >= limits.max_nodes {
            continue;
        }
        explored += 1;

        let mut children = Vec::new();
        let visible_action = visible_action::<M>(&events[visible]);
        let mut visible_world = world.clone();
        if visible_world.apply(&visible_action).is_ok() {
            children.push((visible_action, visible_world, visible + 1));
        }

        let target = events[visible].time();
        let mut times = vec![world.now];
        if target != world.now {
            times.push(target);
        }
        for at in times {
            let mut actions = hidden_actions(&world, at, true);
            actions.sort_by_key(|action| rank(&events[visible], action));
            for action in actions {
                let mut next = world.clone();
                if matches!(next.apply(&action), Ok(None)) && !next.same_snapshot(&world) {
                    children.push((action, next, visible));
                }
            }
        }

        // Children are generated in preference order. Reverse-push keeps that
        // order in the depth-first work stack without recursive call frames.
        for (action, next, next_visible) in children.into_iter().rev() {
            let mut next_certificate = certificate.clone();
            next_certificate.push(action);
            stack.push((next, next_visible, remaining - 1, next_certificate));
        }
    }
    None
}

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
    search_with(model, config, events, limits, |_, _| 0)
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

pub fn check_guided<M: ExecSpec>(
    model: &M,
    config: &<M::Spec as SpecModel>::Config,
    events: &[BoundaryEvent<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >],
    limits: CheckConfig,
    rank: impl Fn(
        &BoundaryEvent<
            <M::Spec as SpecModel>::Pid,
            <M::Spec as SpecModel>::Message,
        >,
        &Action<
            <M::Spec as SpecModel>::Pid,
            <M::Spec as SpecModel>::Message,
        >,
        &[echod_rover::rover::comm::Envelope<
            <M::Spec as SpecModel>::Pid,
            <M::Spec as SpecModel>::Message,
        >],
    ) -> usize,
) -> Option<Certificate<
    <M::Spec as SpecModel>::Pid,
    <M::Spec as SpecModel>::Message,
>> {
    const MAX_WIDTH: usize = 64;
    const HIDDEN_WIDTH: usize = MAX_WIDTH / 2;
    let initial = ReplayState::initial(model, config);
    let mut frontier = vec![(initial, Vec::new())];
    let mut explored = 0usize;

    for (event_index, event) in events.iter().enumerate() {
        let mut advanced: Vec<(
            ReplayState<'_, M>,
            Certificate<
                <M::Spec as SpecModel>::Pid,
                <M::Spec as SpecModel>::Message,
            >,
        )> = Vec::new();
        let mut produced_target = 0usize;
        let mut direct: Vec<(
            ReplayState<'_, M>,
            Certificate<
                <M::Spec as SpecModel>::Pid,
                <M::Spec as SpecModel>::Message,
            >,
        )> = Vec::new();

        // Preserve one direct continuation from every candidate before any
        // candidate is allowed to spend the beam on hidden alternatives.
        for (world, certificate) in &frontier {
            let visible = visible_action::<M>(event);
            let mut next = world.clone();
            if next.apply(&visible).is_ok() {
                let mut next_certificate = certificate.clone();
                next_certificate.push(visible);
                if !direct.iter().any(|(have, _)| have.same_snapshot(&next)) {
                    direct.push((next, next_certificate));
                }
            }
        }

        // An input may take effect at its arrival instant. Keep both the
        // injected-only candidate and a few immediate process outcomes.
        if matches!(event, BoundaryEvent::Input { .. }) {
            for (world, certificate) in &direct {
                let mut actions = Vec::new();
                for action in hidden_actions(world, world.now, false) {
                    let mut next = world.clone();
                    if matches!(next.apply(&action), Ok(None)) && !next.same_snapshot(world) {
                        actions.push((
                            rank(event, &action, &next.network[world.network.len()..]),
                            action,
                            next,
                        ));
                    }
                }
                actions.sort_by_key(|(rank, _, _)| *rank);
                let best = actions.first().map(|(rank, _, _)| *rank);
                for (_, action, next) in actions
                    .into_iter()
                    .take_while(|(rank, _, _)| Some(*rank) == best)
                    .take(4)
                {
                    if !advanced.iter().any(|(have, _)| have.same_snapshot(&next)) {
                        let mut next_certificate = certificate.clone();
                        next_certificate.push(action);
                        advanced.push((next, next_certificate));
                    }
                    if advanced.len() >= HIDDEN_WIDTH {
                        break;
                    }
                }
                if advanced.len() >= HIDDEN_WIDTH {
                    break;
                }
            }
            if !advanced.is_empty() {
                frontier = advanced;
                continue;
            }
        }

        for (world, certificate) in frontier {
            if advanced.len() >= HIDDEN_WIDTH {
                break;
            }
            let mut stack = vec![(world, certificate)];
            while let Some((world, certificate)) = stack.pop() {
                if advanced.len() >= HIDDEN_WIDTH {
                    break;
                }
                if certificate.len() >= limits.max_steps || explored >= limits.max_nodes {
                    continue;
                }
                explored += 1;

                let target = event.time();
                let mut times = vec![world.now];
                if target != world.now {
                    times.push(target);
                }
                let mut actions = Vec::new();
                for at in times {
                    actions.extend(hidden_actions(&world, at, false));
                }
                let mut hidden = Vec::new();
                for action in actions {
                    let mut next = world.clone();
                    if matches!(next.apply(&action), Ok(None))
                        && !next.same_snapshot(&world)
                    {
                        let produces = produces_target(&world, &next, event);
                        if produces {
                            produced_target += 1;
                        }
                        hidden.push((
                            produces,
                            rank(
                                event,
                                &action,
                                &next.network[world.network.len()..],
                            ),
                            action,
                            next,
                        ));
                    }
                }
                hidden.sort_by_key(|(produces, rank, _, _)| (!*produces, *rank));
                for (_, _, action, next) in hidden.into_iter().take(4).rev() {
                    if stack.len() >= 128 {
                        break;
                    }
                    let mut next_certificate = certificate.clone();
                    next_certificate.push(action);
                    let visible = visible_action::<M>(event);
                    let mut visible_next = next.clone();
                    if visible_next.apply(&visible).is_ok()
                        && !advanced.iter().any(|(have, _)|
                            have.same_snapshot(&visible_next))
                    {
                        let mut visible_certificate = next_certificate.clone();
                        visible_certificate.push(visible);
                        advanced.push((visible_next, visible_certificate));
                    }
                    stack.push((next, next_certificate));
                }
            }
        }

        let direct_count = direct.len();
        for (state, certificate) in direct {
            if advanced.len() >= MAX_WIDTH {
                break;
            }
            if !advanced.iter().any(|(have, _)| have.same_snapshot(&state)) {
                advanced.push((state, certificate));
            }
        }
        if advanced.is_empty() {
            if std::env::var_os("ROVER_DEBUG").is_some() {
                eprintln!(
                    "Rover history search stopped at visible event {}/{} after exploring {} nodes (direct {}, produced {})",
                    event_index,
                    events.len(),
                    explored,
                    direct_count,
                    produced_target,
                );
            }
            return None;
        }
        frontier = advanced;
    }

    let (_, certificate) = frontier.into_iter().next()?;
    super::replay(model, config, events, &certificate).ok()?;
    Some(certificate)
}
