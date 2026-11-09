//! A Rust + Verus Rover world.
//!
//! Rover is a small message-passing semantics with an append-only network.
//! Sending appends an envelope; receiving only checks that the envelope was
//! sent, so delay, loss, reordering, and duplicate delivery require no extra
//! rules. One distinguished endpoint is outside the modeled processes.
//!
//! [`RoverSpec`] is the mathematical model used by semantics and refinement.
//! [`RoverExec`] is its optional executable realization, used by bounded
//! search and verified replay. [`check`] performs bounded certificate search.
//! Acceptance is decided only after [`replay`] independently replays that
//! certificate; Verus proves that successful replay implies
//! [`semantics::valid_trace`].

use vstd::prelude::*;

use crate::{Data, Time};

mod checker;
pub mod refinement;
mod replay;
pub mod semantics;

pub use checker::{check, search, CheckConfig};
pub use replay::{replay, Action, Certificate};

verus! {

/// A message in Rover's append-only network.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Envelope<P, M> {
    pub sender: P,
    pub recipient: P,
    pub message: M,
}

/// What one process receives.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProcessEvent<P, M> {
    Receive { sender: P, message: M },
    Timeout,
}

/// One possible transition result of one executable process.
pub struct ProcResult<P: RoverProcExec> {
    pub state: P,
    pub send: Vec<(
        <P::Spec as RoverProc>::Pid,
        <P::Spec as RoverProc>::Message,
    )>,
}

/// An event at the system boundary. Process sends remain hidden until a
/// separate `Output` event observes their envelope.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum BoundaryEvent<P, M> {
    Input { recipient: P, at: Time, message: M },
    Output { sender: P, at: Time, message: M },
}

impl<P, M> BoundaryEvent<P, M> {
    /// The world's monotone time attached to this boundary event.
    pub fn time(&self) -> Time {
        match self {
            BoundaryEvent::Input { at, .. } | BoundaryEvent::Output { at, .. } => *at,
        }
    }
}

/// One stateful process in a Rover world.
///
/// A model-specific enum can implement this trait to present heterogeneous
/// process kinds as one homogeneous process type. The process value is its
/// complete local state; an outcome carries the next complete value.
pub trait RoverProc: Sized {
    type Config;
    type Pid: Data;
    type Message: Data;

    spec fn on_event(
        self,
        config: Self::Config,
        now: Time,
        event: ProcessEvent<Self::Pid, Self::Message>,
    ) -> Seq<semantics::StepResultV<Self, Self::Pid, Self::Message>>;
}

/// A stateful executable process proved to realize one [`RoverProc`].
pub trait RoverProcExec:
    Sized + Clone + Eq + std::fmt::Debug + View<V = Self::Spec>
{
    type Spec: RoverProc;

    fn on_event(
        &self,
        config: &<Self::Spec as RoverProc>::Config,
        now: Time,
        event: &ProcessEvent<
            <Self::Spec as RoverProc>::Pid,
            <Self::Spec as RoverProc>::Message,
        >,
    ) -> (r: Vec<ProcResult<Self>>)
        ensures
            r@.len() == self@.on_event(*config, now, *event).len(),
            forall|i: int| 0 <= i < r@.len() ==> {
                let result = #[trigger] r@[i];
                semantics::StepResultV {
                    state: result.state@,
                    send: result.send@,
                } == self@.on_event(*config, now, *event)[i]
            };
}

/// The mathematical protocol interpreted by the Rover world.
///
/// Semantics and refinement depend only on this trait. Its methods are ghost
/// code and impose no executable state representation on a model.
pub trait RoverSpec: Sized {
    type Config;
    type Pid: Data;
    type Proc: RoverProc<Config = Self::Config, Pid = Self::Pid, Message = Self::Message>;
    type Message: Data;
    /// The only values refinement and clients observe. Internal process ids
    /// and messages do not appear here.
    type Boundary;

    /// The stateless endpoint representing everything outside the model.
    open spec fn spec_outside(&self) -> Self::Pid {
        arbitrary()
    }

    /// All process-local initial states.
    open spec fn spec_initial(&self, config: Self::Config) -> Seq<(Self::Pid, Self::Proc)> {
        arbitrary()
    }

    /// Which messages the environment may inject.
    open spec fn spec_injectable(&self, config: Self::Config, message: Self::Message) -> bool {
        arbitrary()
    }

    /// Every possible result of one local process event.
    /// Project one world label to zero or more clean boundary observations.
    open spec fn spec_observe(
        &self,
        label: semantics::Lab<Self>,
    ) -> Seq<Self::Boundary> {
        arbitrary()
    }

    /// Build the complete Rover world around this model's processes.
    open spec fn init(self, config: Self::Config) -> semantics::World<Self> {
        semantics::WorldV {
            process: self.spec_initial(config),
            network: Seq::empty(),
            now: 0,
        }
    }

    /// One complete world step: input, process delivery, or outside
    /// observation. Process delivery selects a process and invokes its
    /// stateful [`RoverProc::on_event`].
    open spec fn step(
        self,
        config: Self::Config,
        before: semantics::World<Self>,
        label: semantics::Lab<Self>,
        after: semantics::World<Self>,
    ) -> bool {
        match label {
            semantics::Label::Input { recipient, at, message } => {
                &&& before.now <= at
                &&& recipient != self.spec_outside()
                &&& exists|i: int| 0 <= i < before.process.len()
                    && #[trigger] before.process[i].0 == recipient
                &&& self.spec_injectable(config, message)
                &&& after == semantics::inject(
                    before,
                    self.spec_outside(),
                    recipient,
                    at,
                    message,
                )
            }
            semantics::Label::Process { process, at, event, send } => {
                &&& before.now <= at
                &&& process != self.spec_outside()
                &&& semantics::event_valid(before, process, event)
                &&& exists|i: int, j: int|
                    #![trigger before.process[i].1.on_event(config, at, event)[j]]
                {
                    &&& 0 <= i < before.process.len()
                    &&& before.process[i].0 == process
                    &&& {
                        let outcomes = before.process[i].1.on_event(config, at, event);
                        &&& 0 <= j < outcomes.len()
                        &&& outcomes[j].send == send
                        &&& after == semantics::land(before, i, process, at, outcomes[j])
                    }
                }
            }
            semantics::Label::Outside { sender, at, message } => {
                &&& before.now <= at
                &&& exists|i: int| {
                    &&& 0 <= i < before.network.len()
                    &&& #[trigger] before.network[i] == Envelope {
                        sender,
                        recipient: self.spec_outside(),
                        message,
                    }
                }
                &&& after == semantics::observe_outside(before, at)
            }
        }
    }
}

/// An executable realization of a [`RoverSpec`].
///
/// Search and replay require this trait. `Spec` is a distinct type: each
/// method's contract connects the executable representation to that
/// mathematical model. A proof-only model implements `RoverSpec` and stops
/// there.
pub trait RoverExec {
    type Spec: RoverSpec;
    type Proc: RoverProcExec<Spec = <Self::Spec as RoverSpec>::Proc>;

    /// The mathematical model this value executes.
    spec fn spec(&self) -> Self::Spec;

    /// The executable outside endpoint.
    fn outside(&self) -> (r: PidOf<Self>)
        ensures
            r == self.spec().spec_outside();

    /// All process-local initial states. Slots make process lookup executable;
    /// process ids should be unique. The outside endpoint is never stepped,
    /// even if a malformed model includes it in this list.
    fn initial(&self, config: &ConfigOf<Self>) -> (r: Vec<(PidOf<Self>, Self::Proc)>)
        ensures
            r@.map_values(|entry: (PidOf<Self>, Self::Proc)| (entry.0, entry.1@))
                == self.spec().spec_initial(*config),
            r@.map_values(|entry: (PidOf<Self>, Self::Proc)| entry.0).no_duplicates(),
            forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i].0 != self.spec().spec_outside();

    /// Which messages the environment may inject.
    fn injectable(&self, config: &ConfigOf<Self>, message: &MessageOf<Self>) -> (r: bool)
        ensures
            r == self.spec().spec_injectable(*config, *message);

}

} // verus!

/// A boundary event for specification `M`.
pub type EventOf<M> = BoundaryEvent<<M as RoverSpec>::Pid, <M as RoverSpec>::Message>;

/// The mathematical model implemented by executable model `M`.
pub type SpecOf<M> = <M as RoverExec>::Spec;
pub type ConfigOf<M> = <SpecOf<M> as RoverSpec>::Config;
pub type PidOf<M> = <SpecOf<M> as RoverSpec>::Pid;
pub type ProcOf<M> = <SpecOf<M> as RoverSpec>::Proc;
pub type MessageOf<M> = <SpecOf<M> as RoverSpec>::Message;
pub type BoundaryOf<M> = <SpecOf<M> as RoverSpec>::Boundary;
pub type ExecEventOf<M> = EventOf<SpecOf<M>>;
pub type ExecProcOf<M> = <M as RoverExec>::Proc;
pub type StepResult<M> = ProcResult<ExecProcOf<M>>;
