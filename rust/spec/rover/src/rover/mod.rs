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

/// One possible local transition result.
pub struct StepResult<M: RoverExec + ?Sized> {
    pub state: M::State,
    pub send: Vec<(PidOf<M>, MessageOf<M>)>,
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

/// The mathematical protocol interpreted by the Rover world.
///
/// Semantics and refinement depend only on this trait. Its methods are ghost
/// code and impose no executable state representation on a model.
pub trait RoverSpec {
    type Config;
    type Pid: Data;
    type StateV;
    type Message: Data;
    /// The only values refinement and clients observe. Internal process ids
    /// and messages do not appear here.
    type Boundary;

    /// The stateless endpoint representing everything outside the model.
    open spec fn spec_outside(&self) -> Self::Pid {
        arbitrary()
    }

    /// All process-local initial states.
    open spec fn spec_initial(&self, config: Self::Config) -> Seq<(Self::Pid, Self::StateV)> {
        arbitrary()
    }

    /// Which messages the environment may inject.
    open spec fn spec_injectable(&self, config: Self::Config, message: Self::Message) -> bool {
        arbitrary()
    }

    /// Every possible result of one local process event.
    open spec fn spec_on_event(
        &self,
        config: Self::Config,
        pid: Self::Pid,
        state: Self::StateV,
        now: Time,
        event: ProcessEvent<Self::Pid, Self::Message>,
    ) -> Seq<semantics::StepResultV<Self::StateV, Self::Pid, Self::Message>> {
        arbitrary()
    }

    /// Project one world label to zero or more clean boundary observations.
    open spec fn spec_observe(
        &self,
        label: semantics::Lab<Self>,
    ) -> Seq<Self::Boundary> {
        arbitrary()
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
    type State: Clone + Eq + std::fmt::Debug + View<V = <Self::Spec as RoverSpec>::StateV>;

    /// The mathematical model this value executes.
    spec fn spec(&self) -> Self::Spec;

    /// The executable outside endpoint.
    fn outside(&self) -> (r: PidOf<Self>)
        ensures
            r == self.spec().spec_outside();

    /// All process-local initial states. Slots make process lookup executable;
    /// process ids should be unique. The outside endpoint is never stepped,
    /// even if a malformed model includes it in this list.
    fn initial(&self, config: &ConfigOf<Self>) -> (r: Vec<(PidOf<Self>, Self::State)>)
        ensures
            r@.map_values(|entry: (PidOf<Self>, Self::State)| (entry.0, entry.1@))
                == self.spec().spec_initial(*config),
            r@.map_values(|entry: (PidOf<Self>, Self::State)| entry.0).no_duplicates(),
            forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i].0 != self.spec().spec_outside();

    /// Which messages the environment may inject.
    fn injectable(&self, config: &ConfigOf<Self>, message: &MessageOf<Self>) -> (r: bool)
        ensures
            r == self.spec().spec_injectable(*config, *message);

    /// Every possible result of one local process event. Unlike Lean's
    /// `Outcomes`, an empty result is admitted here and means the event is
    /// disabled; models that need input-enabledness prove non-emptiness.
    fn on_event(
        &self,
        config: &ConfigOf<Self>,
        pid: &PidOf<Self>,
        state: &Self::State,
        now: Time,
        event: &ProcessEvent<PidOf<Self>, MessageOf<Self>>,
    ) -> (r: Vec<StepResult<Self>>)
        ensures
            r@.len() == self.spec().spec_on_event(*config, *pid, state@, now, *event).len(),
            forall|i: int| 0 <= i < r@.len() ==> {
                let result = #[trigger] r@[i];
                semantics::StepResultV {
                    state: result.state@,
                    send: result.send@,
                } == self.spec().spec_on_event(*config, *pid, state@, now, *event)[i]
            };

}

/// One process in a [`RoverExec`].
///
/// Every process in a model shares that model's `Pid` and `Message`. `on_event`
/// returns the next instance and the messages it sends. `Config` is the model's
/// configuration; a process that already holds what it needs takes `()`.
pub trait Process<Config, Pid, Message> {
    fn on_event(
        &self,
        config: &Config,
        now: crate::Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (r: Vec<(Self, Vec<(Pid, Message)>)>) where Self: Sized;
}

} // verus!

/// A boundary event for specification `M`.
pub type EventOf<M> = BoundaryEvent<<M as RoverSpec>::Pid, <M as RoverSpec>::Message>;

/// The mathematical model implemented by executable model `M`.
pub type SpecOf<M> = <M as RoverExec>::Spec;
pub type ConfigOf<M> = <SpecOf<M> as RoverSpec>::Config;
pub type PidOf<M> = <SpecOf<M> as RoverSpec>::Pid;
pub type StateVOf<M> = <SpecOf<M> as RoverSpec>::StateV;
pub type MessageOf<M> = <SpecOf<M> as RoverSpec>::Message;
pub type BoundaryOf<M> = <SpecOf<M> as RoverSpec>::Boundary;
pub type ExecEventOf<M> = EventOf<SpecOf<M>>;
