//! Deterministic, single-path execution of an executable Rover model.
//!
//! A strategy chooses one action at a time. Rover supplies every process and
//! observation action available at the current instant; the strategy may also
//! construct model-specific [`Action::Inject`] and [`Action::Clock`] actions.
//! Every choice crosses the same verified replay boundary used by checking.

use std::collections::BTreeSet;

use super::replay::ReplayState;
use super::{replay, Action, Certificate, Proc as ExecProc, Spec as ExecSpec};
use rover_spec::rover::comm::{BoundaryEvent, ProcessEvent, Time};
use rover_spec::rover::spec::Spec as SpecModel;

/// An action specialized to one executable Rover model.
pub type ModelAction<M> = Action<
    <<M as ExecSpec>::Spec as SpecModel>::Pid,
    <<M as ExecSpec>::Spec as SpecModel>::Message,
>;

/// The choices visible to a strategy before one execution step.
///
/// `internal` contains all process outcomes for timeout and network-delivery
/// events at `now`. `observe` contains all outputs currently present in the
/// append-only network. Their order is deterministic.
pub struct Driver<'a, M: ExecSpec> {
    pub step: usize,
    pub now: Time,
    pub internal: &'a [ModelAction<M>],
    pub observe: &'a [ModelAction<M>],
}

/// Chooses one deterministic path through an executable Rover model.
///
/// Returning `None` ends the execution. A strategy can select a supplied
/// process or observation action, or construct an injection or clock action.
/// Randomness belongs in the strategy, so a seeded strategy remains exactly
/// replayable without coupling Rover to a particular RNG.
pub trait Strategy<M: ExecSpec> {
    fn next(&mut self, driver: Driver<'_, M>) -> Option<ModelAction<M>>;
}

impl<M, F> Strategy<M> for F
where
    M: ExecSpec,
    F: for<'a> FnMut(Driver<'a, M>) -> Option<ModelAction<M>>,
{
    fn next(&mut self, driver: Driver<'_, M>) -> Option<ModelAction<M>> {
        self(driver)
    }
}

/// A complete, independently replayed deterministic execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecResult<P, M> {
    pub trace: Vec<BoundaryEvent<P, M>>,
    pub certificate: Certificate<P, M>,
    pub marks: BTreeSet<&'static str>,
}

/// Why deterministic generation could not produce a certified execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecError {
    /// The strategy selected an action not valid in the current Rover state.
    Rejected { step: usize },
    /// The strategy requested an action beyond the configured step bound.
    StepLimit { max_steps: usize },
    /// Independent replay rejected the generated certificate.
    Replay { visible: usize },
}

fn available<M: ExecSpec>(
    world: &ReplayState<'_, M>,
) -> (Vec<ModelAction<M>>, Vec<ModelAction<M>>) {
    let outside = world.model.outside();
    let mut internal = Vec::new();

    for (slot, (process, state)) in world.process.iter().enumerate() {
        if *process == outside {
            continue;
        }

        for envelope in &world.network {
            if envelope.recipient != *process {
                continue;
            }
            let event = ProcessEvent::Receive {
                sender: envelope.sender.clone(),
                message: envelope.message.clone(),
            };
            let outcomes = state.on_event(world.config, world.now, &event);
            internal.extend((0..outcomes.len()).map(|outcome| Action::Process {
                slot,
                process: process.clone(),
                at: world.now,
                event: event.clone(),
                outcome,
            }));
        }

        let event = ProcessEvent::Timeout;
        let outcomes = state.on_event(world.config, world.now, &event);
        internal.extend((0..outcomes.len()).map(|outcome| Action::Process {
            slot,
            process: process.clone(),
            at: world.now,
            event: event.clone(),
            outcome,
        }));
    }

    let observe = world
        .network
        .iter()
        .filter(|envelope| envelope.recipient == outside)
        .map(|envelope| Action::Observe {
            sender: envelope.sender.clone(),
            at: world.now,
            message: envelope.message.clone(),
        })
        .collect();

    (internal, observe)
}

/// Drive one deterministic execution and independently replay its certificate.
///
/// `max_steps` bounds applied actions. A strategy that still returns an action
/// after that many steps receives [`ExecError::StepLimit`].
pub fn exec<M: ExecSpec>(
    model: &M,
    config: &<M::Spec as SpecModel>::Config,
    max_steps: usize,
    mut strategy: impl Strategy<M>,
) -> Result<ExecResult<<M::Spec as SpecModel>::Pid, <M::Spec as SpecModel>::Message>, ExecError> {
    let mut world = ReplayState::initial(model, config);
    let mut trace = Vec::new();
    let mut certificate = Vec::new();
    let mut all_marks = BTreeSet::new();

    loop {
        let (internal, observe) = available(&world);
        let Some(action) = strategy.next(Driver {
            step: certificate.len(),
            now: world.now,
            internal: &internal,
            observe: &observe,
        }) else {
            break;
        };

        if certificate.len() == max_steps {
            return Err(ExecError::StepLimit { max_steps });
        }
        let shown = world.apply(&action).map_err(|()| ExecError::Rejected {
            step: certificate.len(),
        })?;
        if let Some(event) = shown {
            trace.push(event);
        }
        all_marks.extend(world.marks.iter().copied());
        certificate.push(action);
    }

    replay(model, config, &trace, &certificate).map_err(|visible| ExecError::Replay { visible })?;
    Ok(ExecResult {
        trace,
        certificate,
        marks: all_marks,
    })
}
