//! The concrete Rover model.
//!
//! A world is the nodes and one store process, an empty network, and time 0.
//! Rover assembles that from [`Model::initial`]; [`spec_world`] is the same
//! world as a specification. A node keeps its own memory and shares none of
//! it. The bucket is the store process. A `Store` effect is a message to
//! that process, and the answer comes back from it. Each node is a shell
//! around [`spec_logic_on_event`], the specification of `State::on_event`.
//! A `Wake` stays in the shell until a Rover `Timeout` at or after that
//! instant is delivered as `Tick`: that is when the node next looks at its
//! wheel. An origin's timeout is a deadline key in the store's time bucket,
//! `timeouts::commit_origin`, and `timeouts::origins_reflected` says every
//! origin that owes a deadline has that key in the bucket the deadline
//! falls in. The store process applies the `Store` effect the node sent.
//!
//! The handler arms of `spec_logic_on_event` (`spec_start`, `spec_request`,
//! `spec_completed`, `spec_tick`, `spec_stop`) are uninterpreted. The control
//! around them is the control in `State::on_event`.
//!
//! The theorem this model is for is `echod_rover::rover::refinement::refines`
//! of this instantiation against the abstract Rover model. See `refine`.

use vstd::prelude::*;

pub use echod_logic::types::{Etag, Read, StoreCall, StoreError, StoreOutcome};

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
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Model;

// ---------------------------------------------------------------------------
// What crosses the shell
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ClientRequest {
    pub client: String,
    pub id: u64,
    pub kind: String,
}

/// A message on the concrete network. Store traffic is between a node and
/// the store process. `Request` and `Stop` are what outside may inject.
/// What a trace of this world shows. Store traffic is absent.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Boundary {
    Input { at: u64, request: ClientRequest },
    Reply { at: u64, id: u64, status: u16 },
    Send { at: u64, address: String, body: Vec<u8> },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Message {
    Request(ClientRequest),
    Reply { id: u64, status: u16 },
    Send { address: String, body: Vec<u8> },
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

/// What `State::on_event` returns. `Wake` is the only one the shell keeps.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Effect {
    Store { op: u64, call: StoreCall },
    Reply { id: u64, status: u16 },
    Send { address: String, body: Vec<u8> },
    Wake { after_ms: u64 },
    Note,
}

/// Effects of one arm, before `schedule_wake`. The arm does not emit `Wake`.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ArmEffect {
    Store { op: u64, call: StoreCall },
    Reply { id: u64, status: u16 },
    Send { address: String, body: Vec<u8> },
    Note,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum LogicEvent {
    Start { clock: u64, loops: bool },
    Request { id: u64, request: ClientRequest, clock: u64 },
    Completed { op: u64, outcome: StoreOutcome, clock: u64 },
    Tick { clock: u64 },
    Stop { clock: u64 },
}

// ---------------------------------------------------------------------------
// Local state
// ---------------------------------------------------------------------------

/// The fields `State::on_event` itself assigns. `inner` is everything the
/// handlers own: cache, flights, membership, timers.
pub struct LogicV {
    pub clock: nat,
    pub loops: bool,
    pub stopping: bool,
    pub stopped: bool,
    pub last_wake: Option<nat>,
    pub inner: nat,
}

pub struct EntryV {
    pub key: Seq<char>,
    pub body: Seq<u8>,
    pub version: nat,
}

pub struct StoreV {
    pub entries: Seq<EntryV>,
    pub appendable: bool,
}

pub struct NodeV {
    pub logic: LogicV,
    pub wake: Option<nat>,
    pub next_request: u64,
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

/// Rover's initial world for this model: the processes, no network, time 0.
pub struct SpecWorld {
    pub process: Seq<(Pid, LocalV)>,
    pub network: Seq<Envelope>,
    pub now: u64,
}

pub enum Stored {
    Got(Option<(Seq<u8>, Seq<char>)>),
    Absent,
    NotModified,
    Body(Seq<u8>, Seq<char>),
    Written(Seq<char>),
    Done,
    Listed(Seq<Seq<char>>),
    Failed(StoreError),
}

pub enum SpecMsg {
    Reply { id: u64, status: u16 },
    Send { address: Seq<char>, body: Seq<u8> },
    StoreReq { op: u64, call: StoreCall },
    StoreReply { op: u64, stored: Stored },
    Stop,
}

pub struct Outcome {
    pub state: LocalV,
    pub send: Seq<(Pid, SpecMsg)>,
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Node {
    pub logic: Logic,
    pub wake: Option<u64>,
    pub next_request: u64,
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
            inner: 0,
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
        StoreV { entries: self.entries@.map_values(|e: Entry| e@), appendable: self.appendable }
    }
}

impl View for Node {
    type V = NodeV;
    open spec fn view(&self) -> NodeV {
        NodeV { logic: self.logic@, wake: match self.wake {
            Some(t) => Some(t as nat),
            None => None,
        }, next_request: self.next_request }
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

// ---------------------------------------------------------------------------
// The logic step: the control of State::on_event
// ---------------------------------------------------------------------------

pub uninterp spec fn fresh_inner(id: nat) -> nat;

pub uninterp spec fn spec_start(inner: nat, clock: nat) -> (nat, Seq<ArmEffect>);

pub uninterp spec fn spec_request(inner: nat, id: nat, client: Seq<char>, kind: Seq<char>, clock: nat) -> (nat, Seq<ArmEffect>);

/// The third component is `stopped` after a completion. `Leaving` sets it.
pub uninterp spec fn spec_completed(inner: nat, op: nat, stored: Stored, clock: nat) -> (nat, bool, Seq<ArmEffect>);

pub uninterp spec fn spec_tick(inner: nat, clock: nat) -> (nat, Seq<ArmEffect>);

pub uninterp spec fn spec_stop(inner: nat, clock: nat) -> (nat, Seq<ArmEffect>);

/// The absolute instant `schedule_wake` would arm, if the node is looping.
pub uninterp spec fn spec_due(logic: LogicV) -> Option<nat>;

/// `at.saturating_sub(now).max(1)`, with the logic's own `now`.
pub uninterp spec fn spec_wake_delay(logic: LogicV, at: nat) -> u64;

/// Content hash the store quotes as an etag. The executable store computes it.
pub uninterp spec fn spec_etag(body: Seq<u8>) -> Seq<char>;

pub open spec fn fresh_logic(id: u64) -> LogicV {
    LogicV {
        clock: 0,
        loops: false,
        stopping: false,
        stopped: false,
        last_wake: None,
        inner: fresh_inner(id as nat),
    }
}

pub open spec fn lift(effects: Seq<ArmEffect>) -> Seq<Effect>
    decreases effects.len(),
{
    if effects.len() == 0 {
        Seq::empty()
    } else {
        lift(effects.drop_last()).push(match effects.last() {
            ArmEffect::Store { op, call } => Effect::Store { op, call },
            ArmEffect::Reply { id, status } => Effect::Reply { id, status },
            ArmEffect::Send { address, body } => Effect::Send { address, body },
            ArmEffect::Note => Effect::Note,
        })
    }
}

pub enum LogicStep {
    Start { clock: u64, loops: bool },
    Request { id: u64, client: Seq<char>, kind: Seq<char>, clock: u64 },
    Completed { op: u64, stored: Stored, clock: u64 },
    Tick { clock: u64 },
    Stop { clock: u64 },
}

pub open spec fn spec_arm(logic: LogicV, event: LogicStep) -> (LogicV, Seq<ArmEffect>) {
    match event {
        LogicStep::Start { clock, loops } => {
            let (inner, effects) = spec_start(logic.inner, clock as nat);
            (LogicV { clock: clock as nat, loops, inner, ..logic }, effects)
        },
        LogicStep::Request { id, client, kind, clock } => {
            let (inner, effects) = spec_request(logic.inner, id as nat, client, kind, clock as nat);
            (LogicV { clock: clock as nat, inner, ..logic }, effects)
        },
        LogicStep::Completed { op, stored, clock } => {
            let (inner, stopped, effects) = spec_completed(logic.inner, op as nat, stored, clock as nat);
            (LogicV { clock: clock as nat, stopped, inner, ..logic }, effects)
        },
        LogicStep::Tick { clock } => {
            let cleared = LogicV { clock: clock as nat, last_wake: None, ..logic };
            let (inner, effects) = if logic.loops && !logic.stopping {
                spec_tick(cleared.inner, clock as nat)
            } else {
                (cleared.inner, Seq::<ArmEffect>::empty())
            };
            (LogicV { inner, ..cleared }, effects)
        },
        LogicStep::Stop { clock } => {
            let (inner, effects) = spec_stop(logic.inner, clock as nat);
            (LogicV { clock: clock as nat, loops: false, stopping: true, inner, ..logic }, effects)
        },
    }
}

pub open spec fn spec_schedule_wake(logic: LogicV) -> (LogicV, Seq<Effect>) {
    if !logic.loops || logic.stopping {
        (logic, Seq::empty())
    } else {
        let at = spec_due(logic);
        if at == logic.last_wake {
            (logic, Seq::empty())
        } else {
            match at {
                None => (LogicV { last_wake: None, ..logic }, Seq::empty()),
                Some(t) => (
                    LogicV { last_wake: Some(t), ..logic },
                    seq![Effect::Wake { after_ms: spec_wake_delay(logic, t) }],
                ),
            }
        }
    }
}

/// The specification of `State::on_event`: one arm, then `schedule_wake`.
pub open spec fn spec_logic_on_event(logic: LogicV, event: LogicStep) -> (LogicV, Seq<Effect>) {
    let (stepped, arms) = spec_arm(logic, event);
    let (woken, wake) = spec_schedule_wake(stepped);
    (woken, lift(arms) + wake)
}

// ---------------------------------------------------------------------------
// The shell
// ---------------------------------------------------------------------------

pub open spec fn spec_route(effects: Seq<Effect>, now: nat, wake: Option<nat>) -> (Option<nat>, Seq<(Pid, SpecMsg)>)
    decreases effects.len(),
{
    if effects.len() == 0 {
        (wake, Seq::empty())
    } else {
        let (next, send) = spec_route(effects.drop_last(), now, wake);
        match effects.last() {
            Effect::Wake { after_ms } => (Some(now + after_ms as nat), send),
            Effect::Note => (next, send),
            Effect::Store { op, call } => (next, send.push((Pid::Store, SpecMsg::StoreReq { op, call }))),
            Effect::Reply { id, status } => (next, send.push((Pid::Outside, SpecMsg::Reply { id, status }))),
            Effect::Send { address, body } => (
                next,
                send.push((Pid::Outside, SpecMsg::Send { address: address@, body: body@ })),
            ),
        }
    }
}

pub open spec fn apply_logic(node: NodeV, event: LogicStep, now: nat, wake0: Option<nat>) -> (NodeV, Seq<(Pid, SpecMsg)>) {
    let (logic, effects) = spec_logic_on_event(node.logic, event);
    let (wake, send) = spec_route(effects, now, wake0);
    (NodeV { logic, wake, next_request: node.next_request }, send)
}

pub open spec fn no_wake(effects: Seq<Effect>) -> bool
    decreases effects.len(),
{
    effects.len() == 0 || match effects.last() {
        Effect::Wake { .. } => false,
        _ => no_wake(effects.drop_last()),
    }
}

// ---------------------------------------------------------------------------
// The store
// ---------------------------------------------------------------------------

pub open spec fn empty_store(appendable: bool) -> StoreV {
    StoreV { entries: Seq::empty(), appendable }
}

pub open spec fn lookup(entries: Seq<EntryV>, key: Seq<char>) -> Option<EntryV>
    decreases entries.len(),
{
    if entries.len() == 0 {
        None
    } else if entries.last().key == key {
        Some(entries.last())
    } else {
        lookup(entries.drop_last(), key)
    }
}

pub open spec fn without(entries: Seq<EntryV>, key: Seq<char>) -> Seq<EntryV>
    decreases entries.len(),
{
    if entries.len() == 0 {
        Seq::empty()
    } else if entries.last().key == key {
        without(entries.drop_last(), key)
    } else {
        without(entries.drop_last(), key).push(entries.last())
    }
}

pub open spec fn has_prefix(key: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= key.len() && key.subrange(0, prefix.len() as int) == prefix
}

pub open spec fn filter_prefix(entries: Seq<EntryV>, prefix: Seq<char>) -> Seq<Seq<char>>
    decreases entries.len(),
{
    if entries.len() == 0 {
        Seq::empty()
    } else {
        let rest = filter_prefix(entries.drop_last(), prefix);
        if has_prefix(entries.last().key, prefix) { rest.push(entries.last().key) } else { rest }
    }
}

pub open spec fn take_n<T>(s: Seq<T>, n: nat) -> Seq<T>
    decreases s.len(),
{
    if n == 0 || s.len() == 0 {
        Seq::empty()
    } else {
        seq![s[0]] + take_n(s.subrange(1, s.len() as int), (n - 1) as nat)
    }
}

pub open spec fn matched(entries: Seq<EntryV>, key: Seq<char>, etag: Seq<char>) -> bool {
    match lookup(entries, key) {
        Some(entry) => spec_etag(entry.body) == etag,
        None => false,
    }
}

pub open spec fn put_new(store: StoreV, key: Seq<char>, body: Seq<u8>) -> (StoreV, Stored) {
    if lookup(store.entries, key).is_some() {
        (store, Stored::Failed(StoreError::PreconditionFailed))
    } else {
        let entry = EntryV { key, body, version: 1 };
        (StoreV { entries: store.entries.push(entry), ..store }, Stored::Written(spec_etag(body)))
    }
}

pub open spec fn put_match(store: StoreV, key: Seq<char>, body: Seq<u8>, etag: Seq<char>) -> (StoreV, Stored) {
    if matched(store.entries, key, etag) {
        let old = lookup(store.entries, key).unwrap();
        let entry = EntryV { key, body, version: old.version + 1 };
        (StoreV { entries: without(store.entries, key).push(entry), ..store }, Stored::Written(spec_etag(body)))
    } else {
        (store, Stored::Failed(StoreError::PreconditionFailed))
    }
}

pub open spec fn spec_store_call(store: StoreV, call: StoreCall) -> (StoreV, Stored) {
    match call {
        StoreCall::Get { key } => match lookup(store.entries, key@) {
            Some(entry) => (store, Stored::Got(Some((entry.body, spec_etag(entry.body))))),
            None => (store, Stored::Got(None)),
        },
        StoreCall::GetIfNoneMatch { key, etag } => match lookup(store.entries, key@) {
            None => (store, Stored::Absent),
            Some(entry) => if spec_etag(entry.body) == etag.0@ {
                (store, Stored::NotModified)
            } else {
                (store, Stored::Body(entry.body, spec_etag(entry.body)))
            },
        },
        StoreCall::PutIfNoneMatch { key, body } => put_new(store, key@, body@),
        StoreCall::PutIfMatch { key, body, etag } => put_match(store, key@, body@, etag.0@),
        StoreCall::AppendIfMatch { key, offset, body, etag } => {
            if !store.appendable {
                (store, Stored::Failed(StoreError::Unavailable("this store does not append".into())))
            } else if matched(store.entries, key@, etag.0@) {
                let old = lookup(store.entries, key@).unwrap();
                if old.body.len() == offset as nat {
                    let next = old.body + body@;
                    let entry = EntryV { key: key@, body: next, version: old.version + 1 };
                    (StoreV { entries: without(store.entries, key@).push(entry), ..store }, Stored::Written(spec_etag(next)))
                } else {
                    (store, Stored::Failed(StoreError::PreconditionFailed))
                }
            } else {
                (store, Stored::Failed(StoreError::PreconditionFailed))
            }
        },
        StoreCall::Put { key, body } => {
            let version = match lookup(store.entries, key@) {
                Some(entry) => entry.version + 1,
                None => 1,
            };
            let entry = EntryV { key: key@, body: body@, version };
            (StoreV { entries: without(store.entries, key@).push(entry), ..store }, Stored::Done)
        },
        StoreCall::Delete { key } => (StoreV { entries: without(store.entries, key@), ..store }, Stored::Done),
        StoreCall::List { prefix, max_keys } => (
            store,
            Stored::Listed(take_n(filter_prefix(store.entries, prefix@), max_keys as nat)),
        ),
        StoreCall::ListPrefixes { prefix } => (store, Stored::Listed(list_prefixes(filter_prefix(store.entries, prefix@), prefix@))),
    }
}

pub open spec fn list_prefixes(keys: Seq<Seq<char>>, prefix: Seq<char>) -> Seq<Seq<char>>
    decreases keys.len(),
{
    if keys.len() == 0 {
        Seq::empty()
    } else {
        let rest = list_prefixes(keys.drop_last(), prefix);
        match child_prefix(keys.last(), prefix) {
            Some(child) => if rest.len() > 0 && rest.last() == child { rest } else { rest.push(child) },
            None => rest,
        }
    }
}

pub open spec fn child_prefix(key: Seq<char>, prefix: Seq<char>) -> Option<Seq<char>> {
    if prefix.len() > key.len() {
        None
    } else {
        let tail = key.subrange(prefix.len() as int, key.len() as int);
        match find_char(tail, 0) {
            Some(i) => Some(key.subrange(0, prefix.len() as int + i + 1)),
            None => None,
        }
    }
}

pub open spec fn find_char(s: Seq<char>, i: int) -> Option<int>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        None
    } else if s[i] == '/' {
        Some(i)
    } else {
        find_char(s, i + 1)
    }
}

// ---------------------------------------------------------------------------
// One process step, and the world those processes make
// ---------------------------------------------------------------------------

pub open spec fn spec_step(pid: Pid, state: LocalV, now: u64, event: Incoming) -> Seq<Outcome> {
    match (pid, state, event) {
        (Pid::Node(_), LocalV::Node(node), Incoming::Timeout) => match node.wake {
            Some(at) => if at <= now as nat {
                let (next, send) = apply_logic(node, LogicStep::Tick { clock: now }, now as nat, None);
                seq![Outcome { state: LocalV::Node(next), send }]
            } else {
                Seq::empty()
            },
            None => Seq::empty(),
        },
        (Pid::Node(_), LocalV::Node(node), Incoming::Receive { sender: Pid::Outside, message: Message::Request(request) }) => {
            let (mut_node, send) = apply_logic(
                node,
                LogicStep::Request { id: node.next_request, client: request.client@, kind: request.kind@, clock: now },
                now as nat,
                node.wake,
            );
            seq![Outcome {
                state: LocalV::Node(NodeV { next_request: node.next_request + 1, ..mut_node }),
                send,
            }]
        },
        (Pid::Node(_), LocalV::Node(node), Incoming::Receive { sender: Pid::Store, message: Message::StoreReply { op, outcome } }) => {
            let (next, send) = apply_logic(
                node,
                LogicStep::Completed { op, stored: stored_of(outcome), clock: now },
                now as nat,
                node.wake,
            );
            seq![Outcome { state: LocalV::Node(next), send }]
        },
        (Pid::Node(_), LocalV::Node(node), Incoming::Receive { sender: Pid::Outside, message: Message::Stop }) => {
            let (next, send) = apply_logic(node, LogicStep::Stop { clock: now }, now as nat, node.wake);
            seq![Outcome { state: LocalV::Node(next), send }]
        },
        (Pid::Store, LocalV::Store(store), Incoming::Receive { sender, message: Message::StoreReq { op, call } }) => {
            let (next, stored) = spec_store_call(store, call);
            seq![Outcome {
                state: LocalV::Store(next),
                send: seq![(sender, SpecMsg::StoreReply { op, stored })],
            }]
        },
        _ => Seq::empty(),
    }
}

pub open spec fn stored_of(outcome: StoreOutcome) -> Stored {
    match outcome {
        StoreOutcome::Got(None) => Stored::Got(None),
        StoreOutcome::Got(Some((body, etag))) => Stored::Got(Some((body@, etag.0@))),
        StoreOutcome::Read(Read::Absent) => Stored::Absent,
        StoreOutcome::Read(Read::NotModified) => Stored::NotModified,
        StoreOutcome::Read(Read::Body(body, etag)) => Stored::Body(body@, etag.0@),
        StoreOutcome::Written(etag) => Stored::Written(etag.0@),
        StoreOutcome::Done => Stored::Done,
        StoreOutcome::Listed(keys) => Stored::Listed(keys@.map_values(|k: String| k@)),
        StoreOutcome::Failed(fail) => Stored::Failed(fail),
    }
}

pub open spec fn started(id: u64, loops: bool) -> NodeV {
    let (node, _) = apply_logic(
        NodeV { logic: fresh_logic(id), wake: None, next_request: 1 },
        LogicStep::Start { clock: 0, loops },
        0,
        None,
    );
    node
}

pub open spec fn spec_nodes(config: Fleet, i: nat) -> Seq<(Pid, LocalV)>
    decreases config.nodes as nat - i,
{
    if i >= config.nodes as nat {
        Seq::empty()
    } else {
        seq![(Pid::Node(i as u64), LocalV::Node(started(i as u64, config.loops)))]
            + spec_nodes(config, i + 1)
    }
}

pub open spec fn spec_initial(config: Fleet) -> Seq<(Pid, LocalV)> {
    spec_nodes(config, 0) + seq![(Pid::Store, LocalV::Store(empty_store(config.appendable)))]
}

pub open spec fn spec_world(config: Fleet) -> SpecWorld {
    SpecWorld { process: spec_initial(config), network: Seq::empty(), now: 0 }
}

/// A client request and a client reply are boundary events. A store message is not.
pub open spec fn spec_boundary(at: u64, from_outside: bool, message: Message) -> Seq<Boundary> {
    match (from_outside, message) {
        (true, Message::Request(request)) => seq![Boundary::Input { at, request }],
        (false, Message::Reply { id, status }) => seq![Boundary::Reply { at, id, status }],
        (false, Message::Send { address, body }) => seq![Boundary::Send { at, address, body }],
        (_, _) => Seq::empty(),
    }
}

// ---------------------------------------------------------------------------
// What the world and the shell guarantee
// ---------------------------------------------------------------------------

proof fn lemma_nodes_len(config: Fleet, start: nat)
    requires
        start <= config.nodes as nat,
    ensures
        spec_nodes(config, start).len() == config.nodes as nat - start,
    decreases config.nodes as nat - start,
{
    if start < config.nodes as nat {
        lemma_nodes_len(config, start + 1);
        assert(spec_nodes(config, start).len() == 1 + spec_nodes(config, start + 1).len());
    }
}

proof fn lemma_nodes_at(config: Fleet, start: nat, i: nat)
    requires
        start <= i,
        i < config.nodes as nat,
    ensures
        spec_nodes(config, start)[(i - start) as int] == (Pid::Node(i as u64), LocalV::Node(started(i as u64, config.loops))),
    decreases i - start,
{
    if start < i {
        lemma_nodes_at(config, start + 1, i);
    }
}

proof fn lemma_schedule_preserves(logic: LogicV)
    ensures
        spec_schedule_wake(logic).0.clock == logic.clock,
        spec_schedule_wake(logic).0.loops == logic.loops,
        spec_schedule_wake(logic).0.stopping == logic.stopping,
        spec_schedule_wake(logic).0.stopped == logic.stopped,
        spec_schedule_wake(logic).0.inner == logic.inner,
        !logic.loops || logic.stopping ==> spec_schedule_wake(logic).1.len() == 0,
{
}

proof fn lemma_lift_no_wake(effects: Seq<ArmEffect>)
    ensures
        no_wake(lift(effects)),
    decreases effects.len(),
{
    if effects.len() > 0 {
        lemma_lift_no_wake(effects.drop_last());
    }
}

proof fn lemma_cat_no_wake(a: Seq<Effect>, b: Seq<Effect>)
    requires
        no_wake(a),
        no_wake(b),
    ensures
        no_wake(a + b),
    decreases b.len(),
{
    if b.len() > 0 {
        lemma_cat_no_wake(a, b.drop_last());
    }
}

/// A node is born started: clock 0, the configured loops, not stopping.
pub proof fn lemma_started(id: u64, loops: bool)
    ensures
        started(id, loops).logic.clock == 0,
        started(id, loops).logic.loops == loops,
        started(id, loops).logic.stopping == false,
        started(id, loops).logic.stopped == false,
        started(id, loops).next_request == 1,
{
    let fresh = fresh_logic(id);
    let event = LogicStep::Start { clock: 0, loops };
    let (stepped, _) = spec_arm(fresh, event);
    lemma_schedule_preserves(stepped);
    assert(spec_logic_on_event(fresh, event).0 == spec_schedule_wake(stepped).0);
}

/// The initial world is the nodes, then the store. Outside is not a process.
pub proof fn lemma_world(config: Fleet)
    ensures
        spec_world(config).now == 0,
        spec_world(config).network.len() == 0,
        spec_world(config).process.len() == config.nodes as int + 1,
        spec_world(config).process[config.nodes as int].0 == Pid::Store,
        forall|i: int|
            0 <= i < config.nodes as int
                ==> #[trigger] spec_world(config).process[i].0 == Pid::Node(i as u64),
        forall|i: int| 0 <= i < spec_world(config).process.len() ==> spec_world(config).process[i].0 != Pid::Outside,
{
    lemma_nodes_len(config, 0);
    assert(spec_initial(config).len() == config.nodes as int + 1);
    assert forall|i: int| 0 <= i < config.nodes as int implies spec_world(config).process[i].0 == Pid::Node(i as u64) by {
        lemma_nodes_at(config, 0, i as nat);
    };
    assert forall|i: int| 0 <= i < spec_world(config).process.len() implies spec_world(config).process[i].0 != Pid::Outside by {
        if i < config.nodes as int {
            lemma_nodes_at(config, 0, i as nat);
        } else {
            assert(i == config.nodes as int);
        }
    };
}

/// A timeout with no wake due is not a step.
pub proof fn lemma_timeout_waits(node: NodeV, now: u64)
    requires
        match node.wake {
            Some(at) => at > now as nat,
            None => true,
        },
    ensures
        spec_step(Pid::Node(0), LocalV::Node(node), now, Incoming::Timeout) =~= Seq::<Outcome>::empty(),
{
}

/// A due wake is one `Tick`, and the shell has cleared that wake first.
pub proof fn lemma_timeout_is_tick(node: NodeV, now: u64, at: nat)
    requires
        node.wake == Some(at),
        at <= now as nat,
    ensures
        spec_step(Pid::Node(0), LocalV::Node(node), now, Incoming::Timeout).len() == 1,
        ({
            let (next, send) = apply_logic(node, LogicStep::Tick { clock: now }, now as nat, None);
            spec_step(Pid::Node(0), LocalV::Node(node), now, Incoming::Timeout)[0] == (Outcome { state: LocalV::Node(next), send })
        }),
{
}

/// `Wake` replaces the shell's queued instant and sends nothing.
pub proof fn lemma_wake_is_local(now: nat, after_ms: u64, wake: Option<nat>)
    ensures
        spec_route(seq![Effect::Wake { after_ms }], now, wake).0 == Some(now + after_ms as nat),
        spec_route(seq![Effect::Wake { after_ms }], now, wake).1.len() == 0,
{
}

/// Stopping runs `schedule_wake` and that adds no `Wake`.
pub proof fn lemma_stop_emits_no_wake(logic: LogicV, clock: u64)
    ensures
        no_wake(spec_logic_on_event(logic, LogicStep::Stop { clock }).1),
        spec_logic_on_event(logic, LogicStep::Stop { clock }).0.stopping,
        spec_logic_on_event(logic, LogicStep::Stop { clock }).0.loops == false,
{
    let event = LogicStep::Stop { clock };
    let (stepped, arms) = spec_arm(logic, event);
    lemma_schedule_preserves(stepped);
    lemma_lift_no_wake(arms);
    assert(spec_schedule_wake(stepped).1 =~= Seq::<Effect>::empty());
    lemma_cat_no_wake(lift(arms), Seq::<Effect>::empty());
}

pub proof fn lemma_store_traffic_is_hidden(at: u64, op: u64, call: StoreCall)
    ensures
        spec_boundary(at, true, Message::StoreReq { op, call }).len() == 0,
        spec_boundary(at, false, Message::StoreReply { op, outcome: StoreOutcome::Done }).len() == 0,
{
}

/// A missing key is created at version 1. A second create leaves the store.
pub proof fn lemma_put_if_none(store: StoreV, key: Seq<char>, body: Seq<u8>)
    requires
        lookup(store.entries, key).is_none(),
    ensures
        put_new(store, key, body).1 == Stored::Written(spec_etag(body)),
        lookup(put_new(store, key, body).0.entries, key) == Some(EntryV { key, body, version: 1 }),
        lookup(put_new(put_new(store, key, body).0, key, body).0.entries, key)
            == Some(EntryV { key, body, version: 1 }),
        put_new(put_new(store, key, body).0, key, body).1 == Stored::Failed(StoreError::PreconditionFailed),
{
    let created = put_new(store, key, body).0;
    assert(created.entries.last().key == key);
}

/// A conditional put whose etag does not match writes nothing.
pub proof fn lemma_put_if_match_rejects(store: StoreV, key: Seq<char>, body: Seq<u8>, etag: Seq<char>)
    requires
        !matched(store.entries, key, etag),
    ensures
        put_match(store, key, body, etag).0 == store,
        put_match(store, key, body, etag).1 == Stored::Failed(StoreError::PreconditionFailed),
{
}

} // verus!

// ---------------------------------------------------------------------------
// Executable shell and store. The logic arms emit no handler effects: those
// effects are spec_start, spec_request, spec_completed, spec_tick, spec_stop.
// The field updates are the ones State::on_event performs itself.
// ---------------------------------------------------------------------------

impl Fleet {
    pub fn new(nodes: u64, loops: bool) -> Self {
        Self {
            nodes,
            loops,
            appendable: false,
        }
    }
}

/// The content hash the in-memory store quotes, the same function as the
/// runtime's memory store.
pub fn etag(body: &[u8]) -> Etag {
    echod_logic::keys::content_etag(body)
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
                    StoreOutcome::Failed(StoreError::Unavailable("this store does not append".into()))
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

pub fn route_effects(
    effects: &[Effect],
    now: u64,
    mut wake: Option<u64>,
) -> (Option<u64>, Vec<(Pid, Message)>) {
    let mut send = Vec::new();
    for effect in effects {
        match effect {
            Effect::Wake { after_ms } => wake = Some(now.saturating_add(*after_ms)),
            Effect::Note => {}
            Effect::Store { op, call } => send.push((
                Pid::Store,
                Message::StoreReq {
                    op: *op,
                    call: call.clone(),
                },
            )),
            Effect::Reply { id, status } => send.push((
                Pid::Outside,
                Message::Reply {
                    id: *id,
                    status: *status,
                },
            )),
            Effect::Send { address, body } => send.push((
                Pid::Outside,
                Message::Send {
                    address: address.clone(),
                    body: body.clone(),
                },
            )),
        }
    }
    (wake, send)
}

fn logic_on_event(logic: &Logic, event: &LogicEvent) -> (Logic, Vec<Effect>) {
    let mut next = logic.clone();
    let arms: Vec<ArmEffect> = match event {
        LogicEvent::Start { clock, loops } => {
            next.clock = *clock;
            next.loops = *loops;
            Vec::new()
        }
        LogicEvent::Request { clock, .. } => {
            next.clock = *clock;
            Vec::new()
        }
        LogicEvent::Completed { clock, .. } => {
            next.clock = *clock;
            Vec::new()
        }
        LogicEvent::Tick { clock } => {
            next.clock = *clock;
            next.last_wake = None;
            Vec::new()
        }
        LogicEvent::Stop { clock } => {
            next.clock = *clock;
            next.loops = false;
            next.stopping = true;
            Vec::new()
        }
    };
    let (woken, wake) = schedule_wake(next);
    let mut effects = arms.into_iter().map(arm_effect).collect::<Vec<_>>();
    effects.extend(wake);
    (woken, effects)
}

fn arm_effect(effect: ArmEffect) -> Effect {
    match effect {
        ArmEffect::Store { op, call } => Effect::Store { op, call },
        ArmEffect::Reply { id, status } => Effect::Reply { id, status },
        ArmEffect::Send { address, body } => Effect::Send { address, body },
        ArmEffect::Note => Effect::Note,
    }
}

fn schedule_wake(logic: Logic) -> (Logic, Vec<Effect>) {
    if !logic.loops || logic.stopping {
        (logic, Vec::new())
    } else {
        // spec_due is uninterpreted. The executable shell has no deadline
        // until that function is the node's timers, so it emits nothing and
        // leaves last_wake. A Wake the logic does return is still routed.
        (logic, Vec::new())
    }
}

fn apply_event(
    node: &Node,
    event: LogicEvent,
    now: u64,
    wake0: Option<u64>,
) -> (Node, Vec<(Pid, Message)>) {
    let (logic, effects) = logic_on_event(&node.logic, &event);
    let (wake, send) = route_effects(&effects, now, wake0);
    (
        Node {
            logic,
            wake,
            next_request: node.next_request,
        },
        send,
    )
}

fn started_node(loops: bool) -> Node {
    let (node, _) = apply_event(
        &Node {
            logic: Logic {
                clock: 0,
                loops: false,
                stopping: false,
                stopped: false,
                last_wake: None,
            },
            wake: None,
            next_request: 1,
        },
        LogicEvent::Start { clock: 0, loops },
        0,
        None,
    );
    node
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
            process.push((Pid::Node(id), Local::Node(started_node(config.loops))));
        }
        process.push((Pid::Store, Local::Store(Store::empty(config.appendable))));
        World {
            process,
            network: Vec::new(),
            now: 0,
        }
    }

    pub fn step(self, pid: &Pid, state: &Local, now: u64, event: &Incoming) -> Vec<Transition> {
        match (pid, state, event) {
            (Pid::Node(_), Local::Node(node), Incoming::Timeout) => match node.wake {
                Some(at) if at <= now => {
                    let (next, send) =
                        apply_event(node, LogicEvent::Tick { clock: now }, now, None);
                    vec![Transition {
                        state: Local::Node(next),
                        send,
                    }]
                }
                _ => Vec::new(),
            },
            (
                Pid::Node(_),
                Local::Node(node),
                Incoming::Receive {
                    sender: Pid::Outside,
                    message: Message::Request(request),
                },
            ) => {
                let (next, send) = apply_event(
                    node,
                    LogicEvent::Request {
                        id: node.next_request,
                        request: request.clone(),
                        clock: now,
                    },
                    now,
                    node.wake,
                );
                vec![Transition {
                    state: Local::Node(Node {
                        next_request: node.next_request + 1,
                        ..next
                    }),
                    send,
                }]
            }
            (
                Pid::Node(_),
                Local::Node(node),
                Incoming::Receive {
                    sender: Pid::Store,
                    message: Message::StoreReply { op, outcome },
                },
            ) => {
                let (next, send) = apply_event(
                    node,
                    LogicEvent::Completed {
                        op: *op,
                        outcome: outcome.clone(),
                        clock: now,
                    },
                    now,
                    node.wake,
                );
                vec![Transition {
                    state: Local::Node(next),
                    send,
                }]
            }
            (
                Pid::Node(_),
                Local::Node(node),
                Incoming::Receive {
                    sender: Pid::Outside,
                    message: Message::Stop,
                },
            ) => {
                let (next, send) =
                    apply_event(node, LogicEvent::Stop { clock: now }, now, node.wake);
                vec![Transition {
                    state: Local::Node(next),
                    send,
                }]
            }
            (
                Pid::Store,
                Local::Store(store),
                Incoming::Receive {
                    sender,
                    message: Message::StoreReq { op, call },
                },
            ) => {
                let (next, outcome) = store.apply(call);
                vec![Transition {
                    state: Local::Store(next),
                    send: vec![(*sender, Message::StoreReply { op: *op, outcome })],
                }]
            }
            _ => Vec::new(),
        }
    }
}
