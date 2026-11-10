//! Executable realization of `echod_abstract_spec`.

#![allow(non_shorthand_field_patterns)]

use vstd::prelude::*;

use echod_abstract_spec::model::{
    self as abstract_model, Pid as SpecPid, Proc as SpecProc,
};
use echod_abstract_spec::protocol::Message as SpecMessage;
use echod_abstract_spec::ServerConfig as Config;
use rover_spec::rover::comm::{ProcessEvent, Time as RoverTime};
use rover_exec as RoverExec;

mod hashed_map;
pub mod machine;
pub mod model;
pub mod trusted;
pub mod view;
pub mod history;

pub use machine::{Promise, Store, Task};
pub use model::Proc;
pub use trusted::{PMap, PSet};
pub use history::{
    arbitrary, finish, history_rank, history_responses, next_cron, plain,
    rover_trace, suggest, Action, HistoryEvent, IDS, MARKS, SCHEDULES,
};

verus! {

#[derive(Clone, Copy, Debug, Default)]
pub struct Spec;

impl RoverExec::Proc for Proc {
    type Spec = SpecProc;

    fn on_event(
        &self,
        config: &Config,
        now: RoverTime,
        event: &ProcessEvent<SpecPid, SpecMessage>,
    ) -> (results: Vec<RoverExec::ProcResult<Self>>) {
        let mut inner = model::Proc::on_event(self, config, now, event);
        let ghost all = inner@;
        let mut results: Vec<RoverExec::ProcResult<Proc>> = Vec::new();
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
                state: source.state,
                send: source.send,
                marks: source.marks,
            });
        }
        results
    }
}

impl RoverExec::Spec for Spec {
    type Spec = abstract_model::Spec;
    type Proc = Proc;

    open spec fn spec(&self) -> abstract_model::Spec {
        abstract_model::Spec
    }

    fn outside(&self) -> SpecPid {
        SpecPid::Outside
    }

    fn initial(&self, config: &Config) -> (states: Vec<(SpecPid, Proc)>) {
        model::initial(config)
    }

    fn injectable(&self, config: &Config, message: &SpecMessage) -> bool {
        model::injectable(config, message)
    }
}

} // verus!
