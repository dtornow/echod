//! Executable realizations, bounded search, and verified certificate replay.

use vstd::prelude::*;

use echod_rover::rover::comm::{ProcessEvent, Time};
use echod_rover::rover::spec::{Proc as SpecProc, Spec as SpecModel};

mod checker;
mod replay;

pub use checker::{check, check_guided, search, CheckConfig};
pub use replay::{marks, replay, Action, Certificate};

verus! {

/// One possible transition result of one executable process.
pub struct ProcResult<P: Proc> {
    pub state: P,
    pub send: Vec<(
        <P::Spec as SpecProc>::Pid,
        <P::Spec as SpecProc>::Message,
    )>,
    /// Coverage labels; erased from the mathematical process result.
    pub marks: Vec<&'static str>,
}

/// A stateful executable process proved to realize one [`SpecProc`].
pub trait Proc:
    Sized + Clone + Eq + std::fmt::Debug + View<V = Self::Spec>
{
    type Spec: SpecProc;

    fn on_event(
        &self,
        config: &<Self::Spec as SpecProc>::Config,
        now: Time,
        event: &ProcessEvent<
            <Self::Spec as SpecProc>::Pid,
            <Self::Spec as SpecProc>::Message,
        >,
    ) -> (r: Vec<ProcResult<Self>>)
        ensures
            r@.len() == self@.on_event(*config, now, *event).len(),
            forall|i: int| 0 <= i < r@.len() ==> {
                let result = #[trigger] r@[i];
                echod_rover::rover::spec::StepResultV {
                    state: result.state@,
                    send: result.send@,
                } == self@.on_event(*config, now, *event)[i]
            };
}

/// An executable realization of a distinct [`SpecModel`] and its
/// [`super::spec::State`] values.
pub trait Spec {
    type Spec: SpecModel;
    type Proc: Proc<Spec = <Self::Spec as SpecModel>::Proc>;

    spec fn spec(&self) -> Self::Spec;

    fn outside(&self) -> (r: <Self::Spec as SpecModel>::Pid)
        ensures
            r == self.spec().outside();

    fn initial(
        &self,
        config: &<Self::Spec as SpecModel>::Config,
    ) -> (r: Vec<(<Self::Spec as SpecModel>::Pid, Self::Proc)>)
        ensures
            r@.map_values(
                |entry: (<Self::Spec as SpecModel>::Pid, Self::Proc)| (entry.0, entry.1@)
            ) == self.spec().processes(*config),
            r@.map_values(
                |entry: (<Self::Spec as SpecModel>::Pid, Self::Proc)| entry.0
            ).no_duplicates(),
            forall|i: int| 0 <= i < r@.len()
                ==> #[trigger] r@[i].0 != self.spec().outside();

    fn injectable(
        &self,
        config: &<Self::Spec as SpecModel>::Config,
        message: &<Self::Spec as SpecModel>::Message,
    ) -> (r: bool)
        ensures
            r == self.spec().injectable(*config, *message);
}

} // verus!
