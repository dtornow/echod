//! Executable realizations, bounded search, and verified certificate replay.

use vstd::prelude::*;

use crate::Time;

use super::comm::ProcessEvent;
use super::spec::{RoverModel, RoverProc};

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
    type Model: RoverModel;
    type Proc: RoverProcExec<Spec = <Self::Model as RoverModel>::Proc>;

    spec fn model(&self) -> Self::Model;

    fn outside(&self) -> (r: <Self::Model as RoverModel>::Pid)
        ensures
            r == self.model().outside();

    fn initial(
        &self,
        config: &<Self::Model as RoverModel>::Config,
    ) -> (r: Vec<(<Self::Model as RoverModel>::Pid, Self::Proc)>)
        ensures
            r@.map_values(
                |entry: (<Self::Model as RoverModel>::Pid, Self::Proc)| (entry.0, entry.1@)
            ) == self.model().processes(*config),
            r@.map_values(
                |entry: (<Self::Model as RoverModel>::Pid, Self::Proc)| entry.0
            ).no_duplicates(),
            forall|i: int| 0 <= i < r@.len()
                ==> #[trigger] r@[i].0 != self.model().outside();

    fn injectable(
        &self,
        config: &<Self::Model as RoverModel>::Config,
        message: &<Self::Model as RoverModel>::Message,
    ) -> (r: bool)
        ensures
            r == self.model().injectable(*config, *message);
}

} // verus!
