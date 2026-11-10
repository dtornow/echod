//! Executable adapter for the Echod concrete world.
//!
//! Production document execution uses `document`; this adapter keeps the
//! executable world used by concrete runtime tests beside that implementation.

use vstd::prelude::*;

pub use echod_concrete_spec::model::{Fleet, Message, Pid};
use echod_concrete_spec::model::{LocalV, LogicV};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::model::{spec_store, spec_world};
#[cfg(test)]
use echod_concrete_spec::model::EchodConcreteSpec;
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::node::NodeV;
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::store::StoreV;
use echod_rover::rover::comm::ProcessEvent;
#[cfg(test)]
use echod_rover::rover::comm::Time;
#[cfg(test)]
use echod_rover_exec as RoverExec;
#[cfg(test)]
use RoverExec::ProcResult;

#[cfg(verus_keep_ghost)]
use crate::concrete::document::node_results_v;
use crate::concrete::document::Node;
use crate::concrete::store::Store;

verus! {

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Logic {
    pub clock: u64,
    pub loops: bool,
    pub stopping: bool,
    pub stopped: bool,
    pub last_wake: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Local {
    Node(Node),
    Store(Store),
}

impl View for Logic {
    type V = LogicV;
    open spec fn view(&self) -> LogicV {
        LogicV {
            clock: self.clock as nat, loops: self.loops, stopping: self.stopping,
            stopped: self.stopped,
            last_wake: match self.last_wake { Some(t) => Some(t as nat), None => None },
        }
    }
}

impl View for Local {
    type V = LocalV;
    open spec fn view(&self) -> LocalV {
        match self {
            Local::Node(node) => LocalV::Node(node@),
            Local::Store(store) => LocalV::Store(store@),
        }
    }
}

pub struct EchodConcreteExec;

pub open spec fn world_v(v: Seq<(Pid, Local)>) -> Seq<(Pid, LocalV)> {
    v.map_values(|entry: (Pid, Local)| (entry.0, entry.1@))
}

pub open spec fn store_results_v(pairs: Seq<(Store, Vec<(Pid, Message)>)>) -> Seq<echod_rover::rover::RoverSpec::StepResultV<LocalV, Pid, Message>> {
    pairs.map_values(|pair: (Store, Vec<(Pid, Message)>)| echod_rover::rover::RoverSpec::StepResultV { state: LocalV::Store(pair.0@), send: pair.1@ })
}

fn same_pid(a: Pid, b: Pid) -> (r: bool)
    ensures r == (a == b),
{
    match (a, b) {
        (Pid::Outside, Pid::Outside) | (Pid::Store, Pid::Store) => true,
        (Pid::Node(x), Pid::Node(y)) => x == y,
        _ => false,
    }
}

fn seen_has(seen: &Vec<(Pid, u64)>, sender: Pid, op: u64) -> (r: bool)
    ensures r == seen@.contains((sender, op)),
{
    let mut i = 0;
    while i < seen.len()
        invariant i <= seen.len(), forall|j: int| 0 <= j < i ==> seen@[j] != (sender, op),
        decreases seen.len() - i,
    {
        let (p, o) = seen[i];
        if same_pid(p, sender) && o == op {
            assert(seen@[i as int] == (sender, op));
            return true;
        }
        i += 1;
    }
    false
}

impl Store {
    pub fn step(&self, event: &ProcessEvent<Pid, Message>) -> (r: Vec<(Store, Vec<(Pid, Message)>)>)
        ensures store_results_v(r@) == spec_store(self@, *event),
    {
        let mut r: Vec<(Store, Vec<(Pid, Message)>)> = Vec::new();
        match event {
            ProcessEvent::Receive { sender, message: Message::StoreReq { op, call } } => {
                if seen_has(&self.seen, *sender, *op) {
                    r.push((self.copy(), Vec::new()));
                    proof { assert(store_results_v(r@) =~~= spec_store(self@, *event)); }
                    return r;
                }
                let (mut next, outcome) = self.apply(call);
                next.seen.push((*sender, *op));
                let mut send = Vec::new();
                send.push((*sender, Message::StoreReply { op: *op, outcome }));
                r.push((next, send));
                proof { assert(store_results_v(r@) =~~= spec_store(self@, *event)); }
                r
            },
            _ => {
                proof { assert(store_results_v(r@) =~~= Seq::<echod_rover::rover::RoverSpec::StepResultV<LocalV, Pid, Message>>::empty()); }
                r
            },
        }
    }
}

#[cfg(test)]
impl RoverExec::Proc for Local {
    type Spec = LocalV;

    fn on_event(&self, _config: &Fleet, now: Time, event: &ProcessEvent<Pid, Message>) -> Vec<ProcResult<Self>> {
        let mut results = Vec::new();
        match self {
            Local::Node(node) => {
                let pairs = node.step(now, event);
                for (node, send) in pairs { results.push(ProcResult { state: Local::Node(node), send, marks: Vec::new() }); }
            },
            Local::Store(store) => {
                let pairs = store.step(event);
                for (store, send) in pairs { results.push(ProcResult { state: Local::Store(store), send, marks: Vec::new() }); }
            },
        }
        results
    }
}

#[cfg(test)]
impl RoverExec::Spec for EchodConcreteExec {
    type Spec = EchodConcreteSpec;
    type Proc = Local;

    open spec fn spec(&self) -> EchodConcreteSpec { EchodConcreteSpec }
    fn outside(&self) -> Pid { Pid::Outside }

    fn initial(&self, config: &Fleet) -> Vec<(Pid, Local)> {
        let mut process = Vec::new();
        let mut id = 0u64;
        while id < config.nodes {
            process.push((Pid::Node(id), Local::Node(Node::new(id, config.nodes, config.loops, config.retry_timeout))));
            id += 1;
        }
        process.push((Pid::Store, Local::Store(Store::empty(config.appendable))));
        process
    }

    fn injectable(&self, _config: &Fleet, message: &Message) -> bool {
        matches!(message, Message::Request(_) | Message::Stop)
    }
}

} // verus!
