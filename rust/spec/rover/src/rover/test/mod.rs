//! Executable realizations, bounded search, and verified certificate replay.

use vstd::prelude::*;

use crate::Time;

use super::comm::ProcessEvent;
use super::spec::{EventOf, RoverModel, RoverProc};

mod checker;
mod replay;

pub use checker::{check, search, CheckConfig};
pub use replay::{replay, Action, Certificate};

verus! {

/// One possible transition result of one executable process.
pub struct ProcResult<P: RoverProcExec> {
    pub state: P,
    pub send: Vec<(
        <P::Spec as RoverProc>::Pid,
        <P::Spec as RoverProc>::Message,
    )>,
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
                super::spec::StepResultV {
                    state: result.state@,
                    send: result.send@,
                } == self@.on_event(*config, now, *event)[i]
            };
}

/// An executable realization of a distinct [`RoverModel`] and its
/// [`super::spec::RoverSpec`] worlds.
pub trait RoverExec {
    type Spec: RoverModel;
    type Proc: RoverProcExec<Spec = <Self::Spec as RoverModel>::Proc>;

    spec fn spec(&self) -> Self::Spec;

    fn outside(&self) -> (r: PidOf<Self>)
        ensures
            r == self.spec().outside();

    fn initial(&self, config: &ConfigOf<Self>) -> (r: Vec<(PidOf<Self>, Self::Proc)>)
        ensures
            r@.map_values(|entry: (PidOf<Self>, Self::Proc)| (entry.0, entry.1@))
                == self.spec().processes(*config),
            r@.map_values(|entry: (PidOf<Self>, Self::Proc)| entry.0).no_duplicates(),
            forall|i: int| 0 <= i < r@.len()
                ==> #[trigger] r@[i].0 != self.spec().outside();

    fn injectable(&self, config: &ConfigOf<Self>, message: &MessageOf<Self>) -> (r: bool)
        ensures
            r == self.spec().injectable(*config, *message);
}

} // verus!

pub type SpecOf<M> = <M as RoverExec>::Spec;
pub type ConfigOf<M> = <SpecOf<M> as RoverModel>::Config;
pub type PidOf<M> = <SpecOf<M> as RoverModel>::Pid;
pub type ProcOf<M> = <SpecOf<M> as RoverModel>::Proc;
pub type MessageOf<M> = <SpecOf<M> as RoverModel>::Message;
pub type BoundaryOf<M> = <SpecOf<M> as RoverModel>::Boundary;
pub type ExecEventOf<M> = EventOf<SpecOf<M>>;
pub type ExecProcOf<M> = <M as RoverExec>::Proc;
pub type StepResult<M> = ProcResult<ExecProcOf<M>>;
