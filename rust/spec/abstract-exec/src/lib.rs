//! Executable realization of `echod-abstract`.

use vstd::prelude::*;

use echod_abstract::model::{self as abstract_model, Pid as SpecPid, StateV as SpecState};
use echod_abstract::protocol::Message as SpecMessage;
use echod_abstract::ServerConfig as Config;
use echod_rover::rover::comm::{ProcessEvent, Time as RoverTime};
use echod_rover_exec as RoverExec;

pub mod history;

pub use echod_abstract::*;
pub use history::{
    arbitrary, finish, history_rank, history_responses, next_cron, plain,
    rover_trace, suggest, Action, HistoryEvent, IDS, MARKS, SCHEDULES,
};

verus! {

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct State(pub abstract_model::State);

impl View for State {
    type V = SpecState;

    open spec fn view(&self) -> SpecState {
        self.0@
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Model;

impl RoverExec::Proc for State {
    type Spec = SpecState;

    fn on_event(
        &self,
        config: &Config,
        now: RoverTime,
        event: &ProcessEvent<SpecPid, SpecMessage>,
    ) -> (results: Vec<RoverExec::ProcResult<Self>>) {
        let mut inner = self.0.on_event(config, now, event);
        let ghost all = inner@;
        let mut results: Vec<RoverExec::ProcResult<State>> = Vec::new();
        while !inner.is_empty()
            invariant
                results@.len() + inner@.len() == all.len(),
                inner@ == all.skip(results@.len() as int),
                forall|i: int| 0 <= i < results@.len() ==> {
                    let result = #[trigger] results@[i];
                    let source = all[i];
                    &&& result.state@ == source.state@
                    &&& result.send@ == source.send@
                },
            decreases inner.len(),
        {
            let ghost i = results@.len() as int;
            let source = inner.remove(0);
            proof {
                assert(all.skip(i).remove(0) =~= all.skip(i + 1));
            }
            results.push(RoverExec::ProcResult {
                state: State(source.state),
                send: source.send,
                marks: source.marks,
            });
        }
        results
    }
}

impl RoverExec::Spec for Model {
    type Spec = abstract_model::Spec;
    type Proc = State;

    open spec fn spec(&self) -> abstract_model::Spec {
        abstract_model::Spec
    }

    fn outside(&self) -> SpecPid {
        SpecPid::Outside
    }

    fn initial(&self, config: &Config) -> (states: Vec<(SpecPid, State)>) {
        let mut inner = abstract_model::initial(config);
        let ghost all = inner@;
        let mut states: Vec<(SpecPid, State)> = Vec::new();
        while !inner.is_empty()
            invariant
                states@.len() + inner@.len() == all.len(),
                inner@ == all.skip(states@.len() as int),
                forall|i: int| 0 <= i < states@.len() ==> {
                    let state = #[trigger] states@[i];
                    &&& state.0 == all[i].0
                    &&& state.1@ == all[i].1@
                },
            decreases inner.len(),
        {
            let ghost i = states@.len() as int;
            let (pid, state) = inner.remove(0);
            proof {
                assert(all.skip(i).remove(0) =~= all.skip(i + 1));
            }
            states.push((pid, State(state)));
        }
        proof {
            assert(states@.map_values(|entry: (SpecPid, State)| entry.0)
                =~= all.map_values(|entry: (SpecPid, abstract_model::State)| entry.0));
            assert(all.map_values(|entry: (SpecPid, abstract_model::State)| entry.0)
                .no_duplicates());
        }
        states
    }

    fn injectable(&self, config: &Config, message: &SpecMessage) -> bool {
        abstract_model::injectable(config, message)
    }
}

} // verus!
