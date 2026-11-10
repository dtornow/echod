//! Mathematical concrete Rover model.
//!
//! This crate contains only the `*V` process state, transitions, passive
//! protocol algebra, and `RoverSpec::Spec`. Executable realizations live in
//! `echod-process::concrete`.

use vstd::prelude::*;

use rover_abstract_spec::{BoundaryEvent, Call, Output};
use echod_rover::rover::comm::{ProcessEvent, Time};
use echod_rover::rover::RoverSpec;
use RoverSpec::Label;
#[cfg(verus_keep_ghost)]
use RoverSpec::StepResultV;
use echod_types::Response;

#[cfg(verus_keep_ghost)]
use crate::node::{spec_request, spec_store_reply, spec_timeout, spec_wake, NoteV};
pub use crate::node::NodeV;
#[cfg(verus_keep_ghost)]
use crate::store::spec_apply;
pub use crate::store::{EntryV, StoreV};
use crate::store::{Etag, Read, StoreCall, StoreError, StoreOutcome};

verus! {

// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Pid {
    Outside,
    Node(u64),
    Store,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fleet {
    /// Node ids are `0 .. nodes`.
    pub nodes: u64,
    /// Whether each node keeps its heartbeat and timers after it starts.
    pub loops: bool,
    /// Whether the store accepts an append.
    pub appendable: bool,
    /// How long a pending task waits before it is offered again. The
    /// abstract server's `ServerConfig.retry_timeout`, Lean's `retryTimeout`.
    pub retry_timeout: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
/// The mathematical concrete Rover model, with no executable local state.
pub struct RoverConcreteSpec;

// What crosses the boundary
// ---------------------------------------------------------------------------

/// A message on the concrete network. A client request is a [`Call`] and a
/// client reply is an [`Output`], the same values the abstract model
/// observes. Store traffic stays between a node and the store.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Message {
    Request(Call),
    Output(Output),
    StoreReq { op: u64, call: StoreCall },
    StoreReply { op: u64, outcome: StoreOutcome },
    Stop,
}

// ---------------------------------------------------------------------------
// Local state
// ---------------------------------------------------------------------------

/// Clock and flags: the process shell of a node.
pub struct LogicV {
    pub clock: nat,
    pub loops: bool,
    pub stopping: bool,
    pub stopped: bool,
    pub last_wake: Option<nat>,
}

pub enum LocalV {
    Node(NodeV),
    Store(StoreV),
}

impl RoverSpec::Proc for LocalV {
    type Config = Fleet;
    type Pid = Pid;
    type Message = Message;

    open spec fn on_event(
        self,
        _config: Fleet,
        now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<StepResultV<LocalV, Pid, Message>> {
        match self {
            LocalV::Node(node) => spec_node(node, now, event),
            LocalV::Store(store) => spec_store(store, event),
        }
    }
}

/// The nodes a fleet starts, then the store.
pub open spec fn spec_nodes(config: Fleet, id: u64) -> Seq<(Pid, LocalV)>
    decreases (config.nodes - id) as int
{
    if id >= config.nodes {
        Seq::empty()
    } else {
        seq![(Pid::Node(id), LocalV::Node(spec_initial_node(config, id)))]
            + spec_nodes(config, (id + 1) as u64)
    }
}

pub open spec fn spec_initial_node(config: Fleet, id: u64) -> NodeV {
    NodeV {
        logic: LogicV {
            clock: 0,
            loops: config.loops,
            stopping: false,
            stopped: false,
            last_wake: None,
        },
        wake: None,
        next_request: 1,
        address: id as nat,
        nodes: config.nodes as nat,
        retry_timeout: config.retry_timeout,
        flight: None,
        documents: Seq::empty(),
        pending: Seq::empty(),
        next_op: 1,
    }
}

pub open spec fn spec_world(config: Fleet) -> Seq<(Pid, LocalV)> {
    spec_nodes(config, 0) + seq![(
        Pid::Store,
        LocalV::Store(StoreV {
            entries: Seq::empty(),
            appendable: config.appendable,
            seen: Seq::empty(),
        }),
    )]
}

// The process steps as specifications. `LocalV::on_event` dispatches on the
// model-specific process enum: a node runs one flight, the store applies one
// call. `RoverExec::Proc::on_event` proves the executable process returns these
// results: `Node::step` computes `spec_node` and `Store::step` computes
// `spec_store`.
// ---------------------------------------------------------------------------

/// Opaque: the choice is read through the string lemmas alone.
#[verifier::opaque]
pub open spec fn spec_string(chars: Seq<char>) -> String {
    choose|s: String| s@ == chars
}

/// Opaque: the choice is read through [`crate::simulation::lemma_bytes`] alone.
#[verifier::opaque]
pub open spec fn spec_bytes(body: Seq<u8>) -> Vec<u8> {
    choose|v: Vec<u8>| v@ == body
}

pub open spec fn spec_one(state: LocalV, send: Seq<(Pid, Message)>) -> Seq<StepResultV<LocalV, Pid, Message>> {
    seq![StepResultV { state, send }]
}

pub open spec fn spec_clock(logic: LogicV, now: Time) -> LogicV {
    LogicV { clock: now as nat, ..logic }
}

/// A node event, the same arms as `Node::on_event`. A node whose op counter
/// is spent takes no step that could issue an op: it stutters. The
/// executable node adds one there and would overflow; the model stops one
/// short of that.
pub open spec fn spec_node(node: NodeV, now: Time, event: ProcessEvent<Pid, Message>) -> Seq<StepResultV<LocalV, Pid, Message>> {
    match event {
        ProcessEvent::Timeout => match node.wake {
            Some(at) if at <= now as nat && node.flight is None && node.next_op < u64::MAX => {
                let (next, send) = spec_timeout(node, now);
                spec_one(LocalV::Node(NodeV {
                    logic: LogicV { clock: now as nat, last_wake: None, ..node.logic },
                    wake: spec_wake(next),
                    ..next
                }), send)
            },
            Some(at) if at <= now as nat => spec_one(LocalV::Node(node), Seq::empty()),
            _ => Seq::empty(),
        },
        ProcessEvent::Receive { sender: Pid::Outside, message: Message::Request(call) } => {
            if node.flight is Some || node.next_op == u64::MAX {
                spec_one(LocalV::Node(node), Seq::empty())
            } else {
                let (next, send) = spec_request(node, now, call);
                spec_one(LocalV::Node(NodeV {
                    logic: spec_clock(node.logic, now),
                    next_request: (node.next_request + 1) as u64,
                    wake: spec_wake(next),
                    ..next
                }), send)
            }
        },
        ProcessEvent::Receive { sender: Pid::Store, message: Message::StoreReply { op, outcome } } => {
            if node.flight is None || node.next_op == u64::MAX {
                spec_one(LocalV::Node(node), Seq::empty())
            } else {
                let (next, send) = spec_store_reply(node, op, outcome);
                spec_one(LocalV::Node(NodeV {
                    logic: spec_clock(node.logic, now),
                    wake: spec_wake(next),
                    ..next
                }), send)
            }
        },
        ProcessEvent::Receive { sender: Pid::Outside, message: Message::Stop } => {
            spec_one(LocalV::Node(NodeV {
                logic: LogicV { clock: now as nat, loops: false, stopping: true, ..node.logic },
                ..node
            }), Seq::empty())
        },
        _ => Seq::empty(),
    }
}

/// The store answers each `(sender, op)` once. A delivery it has answered
/// is a stutter, the same arm as `Store::on_event`.
pub open spec fn spec_store(store: StoreV, event: ProcessEvent<Pid, Message>) -> Seq<StepResultV<LocalV, Pid, Message>> {
    match event {
        ProcessEvent::Receive { sender, message: Message::StoreReq { op, call } } => {
            if store.seen.contains((sender, op)) {
                spec_one(LocalV::Store(store), Seq::empty())
            } else {
                let (next, outcome) = spec_apply(store, call);
                spec_one(
                    LocalV::Store(StoreV { seen: store.seen.push((sender, op)), ..next }),
                    seq![(sender, Message::StoreReply { op, outcome })],
                )
            }
        },
        _ => Seq::empty(),
    }
}

pub open spec fn spec_reply(client: Seq<char>, id: u64, response: Response) -> (Pid, Message) {
    (Pid::Outside, Message::Output(Output::Response { client: spec_string(client), id, response }))
}

pub open spec fn spec_get(op: u64, key: Seq<char>) -> (Pid, Message) {
    (Pid::Store, Message::StoreReq { op, call: StoreCall::Get { key: spec_string(key) } })
}

pub open spec fn spec_notify(note: NoteV) -> (Pid, Message) {
    let dispatch = match note {
        NoteV::Execute { id, version } => rover_abstract_spec::Dispatch::Execute { id: spec_string(id), version },
        NoteV::Unblock { address, promise } => rover_abstract_spec::Dispatch::Unblock { address: spec_string(address), promise },
    };
    (Pid::Outside, Message::Output(Output::Dispatch(dispatch)))
}

pub open spec fn spec_notes(notes: Seq<NoteV>) -> Seq<(Pid, Message)>
    decreases notes.len(),
{
    if notes.len() == 0 { Seq::empty() }
    else { seq![spec_notify(notes[0])] + spec_notes(notes.drop_first()) }
}

} // verus!

pub const RETRY_TIMEOUT: u64 = 5_000;

impl Fleet {
    pub fn new(nodes: u64, loops: bool) -> Self {
        Self {
            nodes,
            loops,
            appendable: false,
            retry_timeout: RETRY_TIMEOUT,
        }
    }
}

verus! {


impl RoverSpec::Spec for RoverConcreteSpec {
    type Config = Fleet;
    type Pid = Pid;
    type Proc = LocalV;
    type Message = Message;
    type Boundary = BoundaryEvent;

    open spec fn outside(&self) -> Pid {
        Pid::Outside
    }

    open spec fn processes(&self, config: Fleet) -> Seq<(Pid, LocalV)> {
        spec_world(config)
    }

    open spec fn injectable(&self, _config: Fleet, message: Message) -> bool {
        match message {
            Message::Request(_) | Message::Stop => true,
            Message::Output(_) | Message::StoreReq { .. } | Message::StoreReply { .. } => false,
        }
    }

    /// A call in and an output out. Store traffic and `Stop` stay off the boundary,
    /// the same projection the abstract model uses for its own messages.
    open spec fn observe(&self, label: Label<Pid, Message>) -> Seq<BoundaryEvent> {
        match label {
            Label::Input { at, message: Message::Request(call), .. } => {
                seq![BoundaryEvent::Input { at, call }]
            }
            Label::Outside { at, message: Message::Output(output), .. } => {
                seq![BoundaryEvent::Output { at, output }]
            }
            _ => Seq::empty(),
        }
    }
}

}
