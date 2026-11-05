//! The concrete Rover model.
//!
//! A world is the nodes and one store, an empty network, and time 0. Each
//! node is `plane`: its own documents and one flight. A request or a due
//! document loads, is decided, and is written back. The store applies each
//! call once; Rover may deliver an envelope again, and the store answers a
//! `(node, op)` it has answered with a stutter. The abstract model is a
//! different machine. See `simulation`.

use vstd::prelude::*;

use echod_abstract::{BoundaryEvent, Call, Output};
use echod_rover::rover::semantics::Label;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::StepResultV;
use echod_rover::rover::{Process, ProcessEvent, RoverModel, StepResult};
use echod_rover::Time;

use crate::store::{Etag, Read, StoreCall, StoreError, StoreOutcome};

pub(crate) mod step;

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

/// Clock and flags. The documents are the node's, on `Plane`.
pub struct LogicV {
    pub clock: nat,
    pub loops: bool,
    pub stopping: bool,
    pub stopped: bool,
    pub last_wake: Option<nat>,
}

pub struct EntryV {
    pub key: Seq<char>,
    pub body: Seq<u8>,
    pub version: nat,
}

pub struct StoreV {
    pub entries: Seq<EntryV>,
    pub appendable: bool,
    /// The `(node, op)` pairs the store has answered. A second delivery of
    /// one is a stutter.
    pub seen: Seq<(Pid, u64)>,
}

pub struct NodeV {
    pub logic: LogicV,
    pub wake: Option<nat>,
    pub next_request: u64,
    pub plane: crate::plane::PlaneV,
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
pub struct Entry {
    pub key: String,
    pub body: Vec<u8>,
    pub version: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Store {
    pub entries: Vec<Entry>,
    pub appendable: bool,
    /// Each call a node makes carries a fresh `op`. The store executes each
    /// `(node, op)` once; Rover may deliver the envelope again, and a real
    /// HTTP exchange runs once. This is the counterpart of the version
    /// compare-and-swap in the Lean physical store: a stale write is never
    /// applied a second time, whatever the body's etag.
    pub seen: Vec<(Pid, u64)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Node {
    pub logic: Logic,
    pub wake: Option<u64>,
    pub next_request: u64,
    /// The node's own machine: documents, one flight, the pending occurrences.
    pub(crate) plane: crate::plane::Plane,
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

impl View for Entry {
    type V = EntryV;
    open spec fn view(&self) -> EntryV {
        EntryV { key: self.key@, body: self.body@, version: self.version as nat }
    }
}

impl View for Store {
    type V = StoreV;
    open spec fn view(&self) -> StoreV {
        StoreV {
            entries: self.entries@.map_values(|e: Entry| e@),
            appendable: self.appendable,
            seen: self.seen@,
        }
    }
}

impl View for Node {
    type V = NodeV;
    closed spec fn view(&self) -> NodeV {
        NodeV {
            logic: self.logic@,
            wake: match self.wake {
                Some(t) => Some(t as nat),
                None => None,
            },
            next_request: self.next_request,
            plane: self.plane@,
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
        seq![(Pid::Node(id), LocalV::Node(spec_node(config, id)))]
            + spec_nodes(config, (id + 1) as u64)
    }
}

pub open spec fn spec_node(config: Fleet, id: u64) -> NodeV {
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
        plane: crate::plane::PlaneV {
            address: id as nat,
            nodes: config.nodes as nat,
            retry_timeout: config.retry_timeout,
            flight: None,
            documents: Seq::empty(),
            pending: Seq::empty(),
            next_op: 1,
        },
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

} // verus!

// ---------------------------------------------------------------------------
// The store, and the world Rover steps.
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

/// The content hash the in-memory store quotes, the same function as the
/// runtime's memory store.
pub fn etag(body: &[u8]) -> Etag {
    crate::store::content_etag(body)
}

fn find_entry(entries: &[Entry], key: &str) -> Option<usize> {
    entries.iter().position(|entry| entry.key == key)
}

fn put_entry(entries: &mut Vec<Entry>, entry: Entry) {
    if let Some(i) = find_entry(entries, &entry.key) {
        entries[i] = entry;
    } else {
        let i = entries
            .iter()
            .position(|old| old.key.as_str() > entry.key.as_str())
            .unwrap_or(entries.len());
        entries.insert(i, entry);
    }
}

impl Store {
    pub fn empty(appendable: bool) -> Self {
        Self {
            entries: Vec::new(),
            appendable,
            seen: Vec::new(),
        }
    }

    pub fn apply(&self, call: &StoreCall) -> (Store, StoreOutcome) {
        let mut next = self.clone();
        let outcome = match call {
            StoreCall::Get { key } => StoreOutcome::Got(find_entry(&self.entries, key).map(|i| {
                let entry = &self.entries[i];
                (entry.body.clone(), etag(&entry.body))
            })),
            StoreCall::GetIfNoneMatch { key, etag: want } => match find_entry(&self.entries, key) {
                None => StoreOutcome::Read(Read::Absent),
                Some(i) => {
                    let entry = &self.entries[i];
                    let have = etag(&entry.body);
                    if &have == want {
                        StoreOutcome::Read(Read::NotModified)
                    } else {
                        StoreOutcome::Read(Read::Body(entry.body.clone(), have))
                    }
                }
            },
            StoreCall::PutIfNoneMatch { key, body } => {
                if find_entry(&self.entries, key).is_some() {
                    StoreOutcome::Failed(StoreError::PreconditionFailed)
                } else {
                    put_entry(
                        &mut next.entries,
                        Entry {
                            key: key.clone(),
                            body: body.clone(),
                            version: 1,
                        },
                    );
                    StoreOutcome::Written(etag(body))
                }
            }
            StoreCall::PutIfMatch {
                key,
                body,
                etag: want,
            } => match find_entry(&self.entries, key) {
                Some(i) if etag(&self.entries[i].body) == *want => {
                    let version = self.entries[i].version + 1;
                    put_entry(
                        &mut next.entries,
                        Entry {
                            key: key.clone(),
                            body: body.clone(),
                            version,
                        },
                    );
                    StoreOutcome::Written(etag(body))
                }
                _ => StoreOutcome::Failed(StoreError::PreconditionFailed),
            },
            StoreCall::AppendIfMatch {
                key,
                offset,
                body,
                etag: want,
            } => {
                if !self.appendable {
                    StoreOutcome::Failed(StoreError::Unavailable(
                        "this store does not append".into(),
                    ))
                } else {
                    match find_entry(&self.entries, key) {
                        Some(i)
                            if etag(&self.entries[i].body) == *want
                                && self.entries[i].body.len() as u64 == *offset =>
                        {
                            let mut joined = self.entries[i].body.clone();
                            joined.extend_from_slice(body);
                            let version = self.entries[i].version + 1;
                            let tag = etag(&joined);
                            put_entry(
                                &mut next.entries,
                                Entry {
                                    key: key.clone(),
                                    body: joined,
                                    version,
                                },
                            );
                            StoreOutcome::Written(tag)
                        }
                        _ => StoreOutcome::Failed(StoreError::PreconditionFailed),
                    }
                }
            }
            StoreCall::Put { key, body } => {
                let version = find_entry(&self.entries, key)
                    .map(|i| self.entries[i].version + 1)
                    .unwrap_or(1);
                put_entry(
                    &mut next.entries,
                    Entry {
                        key: key.clone(),
                        body: body.clone(),
                        version,
                    },
                );
                StoreOutcome::Done
            }
            StoreCall::Delete { key } => {
                if let Some(i) = find_entry(&next.entries, key) {
                    next.entries.remove(i);
                }
                StoreOutcome::Done
            }
            StoreCall::List { prefix, max_keys } => {
                let keys = self
                    .entries
                    .iter()
                    .filter(|entry| entry.key.starts_with(prefix))
                    .take(*max_keys)
                    .map(|entry| entry.key.clone())
                    .collect();
                StoreOutcome::Listed(keys)
            }
            StoreCall::ListPrefixes { prefix } => {
                StoreOutcome::Listed(prefix_children(&self.entries, prefix))
            }
        };
        (next, outcome)
    }
}

fn prefix_children(entries: &[Entry], prefix: &str) -> Vec<String> {
    let mut out = Vec::new();
    for entry in entries.iter().filter(|entry| entry.key.starts_with(prefix)) {
        let tail = &entry.key[prefix.len()..];
        if let Some(i) = tail.find('/') {
            let child = entry.key[..=prefix.len() + i].to_string();
            if out.last() != Some(&child) {
                out.push(child);
            }
        }
    }
    out
}

fn route_acts(acts: &[crate::plane::Act]) -> Vec<(Pid, Message)> {
    acts.iter()
        .map(|act| match act {
            crate::plane::Act::ToStore { op, call } => (
                Pid::Store,
                Message::StoreReq {
                    op: *op,
                    call: call.clone(),
                },
            ),
            crate::plane::Act::Reply { client, id, response } => (
                Pid::Outside,
                Message::Output(Output::Response {
                    client: client.clone(),
                    id: *id,
                    response: response.clone(),
                }),
            ),
            crate::plane::Act::Notify(note) => (
                Pid::Outside,
                Message::Output(Output::Dispatch(match note {
                    crate::plane::Outbound::Execute { id, version } => {
                        echod_abstract::Dispatch::Execute {
                            id: id.clone(),
                            version: *version,
                        }
                    }
                    crate::plane::Outbound::Unblock { address, promise } => {
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

fn started_node(id: u64, nodes: u64, loops: bool, retry_timeout: u64) -> Node {
    Node {
        logic: Logic {
            clock: 0,
            loops,
            stopping: false,
            stopped: false,
            last_wake: None,
        },
        wake: None,
        next_request: 1,
        plane: crate::plane::Plane::new(id, nodes, retry_timeout),
    }
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
                Local::Node(started_node(id, config.nodes, config.loops, config.retry_timeout)),
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
                Some(at) if at <= now && !self.plane.busy() => {
                    let mut next = self.clone();
                    next.logic.clock = now;
                    next.logic.last_wake = None;
                    let acts = next.plane.timeout(now);
                    next.wake = next.plane.next_wake();
                    vec![(next, route_acts(&acts))]
                }
                Some(at) if at <= now => vec![(self.clone(), Vec::new())],
                _ => Vec::new(),
            },
            ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(request),
            } => {
                if self.plane.busy() {
                    return vec![(self.clone(), Vec::new())];
                }
                let mut next = self.clone();
                next.logic.clock = now;
                next.next_request += 1;
                let acts = next.plane.request(now, &request.client, request.id, &request.request);
                next.wake = next.plane.next_wake();
                vec![(next, route_acts(&acts))]
            }
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreReply { op, outcome },
            } => {
                if !self.plane.busy() {
                    return vec![(self.clone(), Vec::new())];
                }
                let mut next = self.clone();
                next.logic.clock = now;
                let acts = next.plane.store(now, *op, outcome);
                next.wake = next.plane.next_wake();
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

    /// One local step. `step::spec_step` is that transition. The trait's
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
        step::spec_step(config, pid, state, now, event)
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
