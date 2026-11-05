//! The concrete Rover model.
//!
//! A world is the nodes and one store, an empty network, and time 0. Each
//! node keeps its own documents and one flight. A request or a due
//! document loads, is decided, and is written back. The store applies each
//! call once; Rover may deliver an envelope again, and the store answers a
//! `(node, op)` it has answered with a stutter. The abstract model is a
//! different machine. See `simulation`.
//!
//! The initial world and the step are here twice: as the Rover model the
//! checker runs, and as `spec_world` and `spec_step`, the specification.

use vstd::prelude::*;

use echod_abstract::{BoundaryEvent, Call, Output};
use echod_rover::rover::semantics::Label;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::StepResultV;
use echod_rover::rover::{Process, ProcessEvent, RoverModel, StepResult};
use echod_rover::Time;

use echod_types::Response;

#[cfg(verus_keep_ghost)]
use crate::node::{spec_request, spec_store_reply, spec_timeout, spec_wake, NoteV};
pub use crate::node::{Node, NodeV};
#[cfg(verus_keep_ghost)]
use crate::store::spec_apply;
pub use crate::store::{Entry, EntryV, Store, StoreV};
use crate::store::{Etag, Read, StoreCall, StoreError, StoreOutcome};

verus! {

// ---------------------------------------------------------------------------
// Processes
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
pub struct Model;

// ---------------------------------------------------------------------------
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

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Incoming {
    Receive { sender: Pid, message: Message },
    Timeout,
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

/// One envelope, as Rover stores it: sender, recipient, message.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Envelope {
    pub sender: Pid,
    pub recipient: Pid,
    pub message: Message,
}

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
            clock: self.clock as nat,
            loops: self.loops,
            stopping: self.stopping,
            stopped: self.stopped,
            last_wake: match self.last_wake {
                Some(t) => Some(t as nat),
                None => None,
            },
        }
    }
}

/// The nodes a fleet starts, then the store. The same world `Model::initial` builds.
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

impl View for Local {
    type V = LocalV;
    open spec fn view(&self) -> LocalV {
        match self {
            Local::Node(node) => LocalV::Node(node@),
            Local::Store(store) => LocalV::Store(store@),
        }
    }
}

// ---------------------------------------------------------------------------
// The step, as a specification. `spec_step` is what
// `RoverModel::spec_on_event` returns: a node runs one flight, the store
// applies one call. The executable `on_event` is obliged, by the trait, to
// return results whose views are this sequence. That equality is not proved.
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

pub open spec fn spec_step(
    _config: Fleet,
    pid: Pid,
    state: LocalV,
    now: Time,
    event: ProcessEvent<Pid, Message>,
) -> Seq<StepResultV<LocalV, Pid, Message>> {
    match (pid, state) {
        (Pid::Node(_), LocalV::Node(node)) => spec_node(node, now, event),
        (Pid::Store, LocalV::Store(store)) => spec_store(store, event),
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
        NoteV::Execute { id, version } => echod_abstract::Dispatch::Execute { id: spec_string(id), version },
        NoteV::Unblock { address, promise } => echod_abstract::Dispatch::Unblock { address: spec_string(address), promise },
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

// ---------------------------------------------------------------------------
// The world Rover steps.
// ---------------------------------------------------------------------------

/// The retry timeout the kernel uses.
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

fn route_acts(acts: &[crate::node::Act]) -> Vec<(Pid, Message)> {
    acts.iter()
        .map(|act| match act {
            crate::node::Act::ToStore { op, call } => (
                Pid::Store,
                Message::StoreReq {
                    op: *op,
                    call: call.clone(),
                },
            ),
            crate::node::Act::Reply { client, id, response } => (
                Pid::Outside,
                Message::Output(Output::Response {
                    client: client.clone(),
                    id: *id,
                    response: response.clone(),
                }),
            ),
            crate::node::Act::Notify(note) => (
                Pid::Outside,
                Message::Output(Output::Dispatch(match note {
                    crate::node::Outbound::Execute { id, version } => {
                        echod_abstract::Dispatch::Execute {
                            id: id.clone(),
                            version: *version,
                        }
                    }
                    crate::node::Outbound::Unblock { address, promise } => {
                        echod_abstract::Dispatch::Unblock {
                            address: address.clone(),
                            promise: promise.clone(),
                        }
                    }
                })),
            ),
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition {
    pub state: Local,
    pub send: Vec<(Pid, Message)>,
}

/// The executable world Rover assembles: these processes, no network, time 0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct World {
    pub process: Vec<(Pid, Local)>,
    pub network: Vec<Envelope>,
    pub now: u64,
}

impl Model {
    pub fn world(self, config: &Fleet) -> World {
        let mut process = Vec::new();
        for id in 0..config.nodes {
            process.push((
                Pid::Node(id),
                Local::Node(Node::new(id, config.nodes, config.loops, config.retry_timeout)),
            ));
        }
        process.push((Pid::Store, Local::Store(Store::empty(config.appendable))));
        World {
            process,
            network: Vec::new(),
            now: 0,
        }
    }

    /// `step`, as Rover asks for it.
    pub fn results(
        self,
        pid: &Pid,
        state: &Local,
        now: u64,
        event: &ProcessEvent<Pid, Message>,
    ) -> Vec<StepResult<Model>> {
        let incoming = match event {
            ProcessEvent::Timeout => Incoming::Timeout,
            ProcessEvent::Receive { sender, message } => Incoming::Receive {
                sender: sender.clone(),
                message: message.clone(),
            },
        };
        self.step(pid, state, now, &incoming)
            .into_iter()
            .map(|transition| StepResult {
                state: transition.state,
                send: transition.send,
            })
            .collect()
    }

    pub fn step(self, pid: &Pid, state: &Local, now: u64, event: &Incoming) -> Vec<Transition> {
        let event = match event {
            Incoming::Timeout => ProcessEvent::Timeout,
            Incoming::Receive { sender, message } => ProcessEvent::Receive {
                sender: *sender,
                message: message.clone(),
            },
        };
        match (pid, state) {
            (Pid::Node(_), Local::Node(node)) => node
                .on_event(&(), now, &event)
                .into_iter()
                .map(|(node, send)| Transition {
                    state: Local::Node(node),
                    send,
                })
                .collect(),
            (Pid::Store, Local::Store(store)) => store
                .on_event(&(), now, &event)
                .into_iter()
                .map(|(store, send)| Transition {
                    state: Local::Store(store),
                    send,
                })
                .collect(),
            _ => Vec::new(),
        }
    }
}

impl Process<(), Pid, Message> for Node {
    fn on_event(
        &self,
        _config: &(),
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> Vec<(Self, Vec<(Pid, Message)>)> {
        match event {
            ProcessEvent::Timeout => match self.wake {
                Some(at) if at <= now && !self.busy() => {
                    let mut next = self.clone();
                    next.logic.clock = now;
                    next.logic.last_wake = None;
                    let acts = next.timeout(now);
                    next.wake = next.next_wake();
                    vec![(next, route_acts(&acts))]
                }
                Some(at) if at <= now => vec![(self.clone(), Vec::new())],
                _ => Vec::new(),
            },
            ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(request),
            } => {
                if self.busy() {
                    return vec![(self.clone(), Vec::new())];
                }
                let mut next = self.clone();
                next.logic.clock = now;
                next.next_request += 1;
                let acts = next.request(now, &request.client, request.id, &request.request);
                next.wake = next.next_wake();
                vec![(next, route_acts(&acts))]
            }
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreReply { op, outcome },
            } => {
                if !self.busy() {
                    return vec![(self.clone(), Vec::new())];
                }
                let mut next = self.clone();
                next.logic.clock = now;
                let acts = next.store(now, *op, outcome);
                next.wake = next.next_wake();
                vec![(next, route_acts(&acts))]
            }
            ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Stop,
            } => {
                let mut next = self.clone();
                next.logic.clock = now;
                next.logic.loops = false;
                next.logic.stopping = true;
                vec![(next, Vec::new())]
            }
            _ => Vec::new(),
        }
    }
}

impl Process<(), Pid, Message> for Store {
    fn on_event(
        &self,
        _config: &(),
        _now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> Vec<(Self, Vec<(Pid, Message)>)> {
        match event {
            ProcessEvent::Receive {
                sender,
                message: Message::StoreReq { op, call },
            } => {
                if self.seen.contains(&(*sender, *op)) {
                    return vec![(self.clone(), Vec::new())];
                }
                let (mut next, outcome) = self.apply(call);
                next.seen.push((*sender, *op));
                vec![(
                    next,
                    vec![(*sender, Message::StoreReply { op: *op, outcome })],
                )]
            }
            _ => Vec::new(),
        }
    }
}

verus! {

/// The exec world, transitions, and steps are known to Verus by shape alone:
/// nothing is claimed about `world`, `step`, or `results`. The trait's
/// `ensures` on `initial` and `on_event` below are the exec == spec link; they
/// are not proved, and Verus reports them.
#[verifier::external_type_specification]
pub struct ExWorld(World);

#[verifier::external_type_specification]
pub struct ExTransition(Transition);

pub assume_specification [Model::world](m: Model, config: &Fleet) -> World;

pub assume_specification [Model::step](
    m: Model,
    pid: &Pid,
    state: &Local,
    now: u64,
    event: &Incoming,
) -> Vec<Transition>;

pub assume_specification [Model::results](
    m: Model,
    pid: &Pid,
    state: &Local,
    now: u64,
    event: &ProcessEvent<Pid, Message>,
) -> Vec<StepResult<Model>>;

impl RoverModel for Model {
    type Config = Fleet;
    type Pid = Pid;
    type StateV = LocalV;
    type State = Local;
    type Message = Message;
    type Boundary = BoundaryEvent;

    fn outside(&self) -> Pid {
        Pid::Outside
    }

    fn initial(&self, config: &Fleet) -> Vec<(Pid, Local)> {
        self.world(config).process
    }

    fn injectable(&self, _config: &Fleet, message: &Message) -> bool {
        match message {
            Message::Request(_) | Message::Stop => true,
            _ => false,
        }
    }

    fn on_event(
        &self,
        _config: &Fleet,
        pid: &Pid,
        state: &Local,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> Vec<StepResult<Self>> {
        self.results(pid, state, now, event)
    }

    open spec fn spec_outside(&self) -> Pid {
        Pid::Outside
    }

    open spec fn spec_initial(&self, config: Fleet) -> Seq<(Pid, LocalV)> {
        spec_world(config)
    }

    open spec fn spec_injectable(&self, _config: Fleet, message: Message) -> bool {
        match message {
            Message::Request(_) | Message::Stop => true,
            Message::Output(_) | Message::StoreReq { .. } | Message::StoreReply { .. } => false,
        }
    }

    /// One local step. `spec_step` is that transition. The trait's
    /// `ensures` on `on_event` is the equality with the executable results;
    /// that proof is not written yet.
    open spec fn spec_on_event(
        &self,
        config: Fleet,
        pid: Pid,
        state: LocalV,
        now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<StepResultV<LocalV, Pid, Message>> {
        spec_step(config, pid, state, now, event)
    }

    /// A call in and an output out. Store traffic and `Stop` stay off the boundary,
    /// the same projection the abstract model uses for its own messages.
    open spec fn spec_observe(&self, label: Label<Pid, Message>) -> Seq<BoundaryEvent> {
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
