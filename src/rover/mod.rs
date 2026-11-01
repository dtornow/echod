//! A Rust + Verus Rover world.
//!
//! Rover is a small message-passing semantics with an append-only network.
//! Sending appends an envelope; receiving only checks that the envelope was
//! sent, so delay, loss, reordering, and duplicate delivery require no extra
//! rules. One distinguished endpoint is outside the modeled processes.
//!
//! [`RoverModel`] is executable and has specification twins for proofs.
//! [`check`] performs bounded certificate search. Acceptance is decided only
//! after [`replay`] independently replays that certificate; Verus proves that
//! successful replay implies [`semantics::valid_trace`].

use vstd::prelude::*;

use crate::{Data, Time};

mod checker;
pub mod refinement;
mod replay;
pub mod resonate;
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
pub struct StepResult<M: RoverModel + ?Sized> {
    pub state: M::State,
    pub send: Vec<(M::Pid, M::Message)>,
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

/// A protocol interpreted by the Rover world.
///
/// The executable methods have specification twins. A model authored inside
/// `verus!` overrides the twins and verifies each method's `ensures`; ordinary
/// Rust models may use the defaults for trace checking only.
pub trait RoverModel {
    type Config;
    type Pid: Data;
    type StateV;
    type State: Clone + Eq + std::fmt::Debug + View<V = Self::StateV>;
    type Message: Data;
    /// The only values refinement and clients observe. Internal process ids
    /// and messages do not appear here.
    type Boundary;

    /// The stateless endpoint representing everything outside the model.
    fn outside(&self) -> (r: Self::Pid)
        ensures
            r == self.spec_outside();

    /// All process-local initial states. Slots make process lookup executable;
    /// process ids should be unique. The outside endpoint is never stepped,
    /// even if a malformed model includes it in this list.
    fn initial(&self, config: &Self::Config) -> (r: Vec<(Self::Pid, Self::State)>)
        ensures
            r@.map_values(|entry: (Self::Pid, Self::State)| (entry.0, entry.1@))
                == self.spec_initial(*config),
            r@.map_values(|entry: (Self::Pid, Self::State)| entry.0).no_duplicates(),
            forall|i: int| 0 <= i < r@.len() ==> #[trigger] r@[i].0 != self.spec_outside();

    /// Which messages the environment may inject.
    fn injectable(&self, config: &Self::Config, message: &Self::Message) -> (r: bool)
        ensures
            r == self.spec_injectable(*config, *message);

    /// Every possible result of one local process event. Unlike Lean's
    /// `Outcomes`, an empty result is admitted here and means the event is
    /// disabled; models that need input-enabledness prove non-emptiness.
    fn on_event(
        &self,
        config: &Self::Config,
        pid: &Self::Pid,
        state: &Self::State,
        now: Time,
        event: &ProcessEvent<Self::Pid, Self::Message>,
    ) -> (r: Vec<StepResult<Self>>)
        ensures
            r@.len() == self.spec_on_event(*config, *pid, state@, now, *event).len(),
            forall|i: int| 0 <= i < r@.len() ==> {
                let result = #[trigger] r@[i];
                semantics::StepResultV {
                    state: result.state@,
                    send: result.send@,
                } == self.spec_on_event(*config, *pid, state@, now, *event)[i]
            };

    open spec fn spec_outside(&self) -> Self::Pid {
        arbitrary()
    }

    open spec fn spec_initial(&self, config: Self::Config) -> Seq<(Self::Pid, Self::StateV)> {
        arbitrary()
    }

    open spec fn spec_injectable(&self, config: Self::Config, message: Self::Message) -> bool {
        arbitrary()
    }

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

} // verus!

/// A boundary event for `M`.
pub type EventOf<M> = BoundaryEvent<<M as RoverModel>::Pid, <M as RoverModel>::Message>;
