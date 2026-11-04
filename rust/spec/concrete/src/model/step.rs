//! The concrete step, as a specification.
//!
//! `spec_step` is what `RoverModel::spec_on_event` returns. A node runs one
//! flight: load a document, decide, write it back, answer. The store applies
//! one call. The executable `on_event` is obliged, by the trait, to return
//! results whose views are this sequence. That equality is not proved here.
//!
//! `spec_decode` and `spec_encode` are the JSON codec of a document, the same
//! kind of trusted boundary as the cron engine. The handlers below are the step.

#![allow(unused_imports, dead_code)]

use vstd::prelude::*;

use echod_rover::rover::semantics::StepResultV;
use echod_rover::rover::ProcessEvent;
use echod_rover::Time;

#[cfg(verus_keep_ghost)]
use echod_types::{origin, same_origin_spec};
use echod_types::{
    PromiseCreateReq, PromiseRecord, PromiseRegisterCallbackReq, PromiseRes, PromiseSettleReq,
    PromiseState, Request, Response, Schedule, ScheduleCreateReq, ScheduleRes, StatusRes, Tags,
    TaskClaimRes, TaskFenceAction, TaskFenceInnerRes, TaskFenceReq, TaskFenceRes, TaskGetRes,
    TaskRecord, TaskRef, TaskState, Value,
};

use crate::plane::{CachedV, FlightV, JobV, NoteV, PendingV, PlaneV};
use crate::store::{Etag, Read, StoreCall, StoreError, StoreOutcome};

use super::{EntryV, LocalV, LogicV, Message, NodeV, Pid, StoreV};

verus! {

use echod_abstract::{Call, Output};

/// JSON of a document. `encode` / `decode` in the node are this. A body that
/// does not parse is the empty document for that key, the same fallback as
/// `decode`.
pub uninterp spec fn spec_decode_raw(body: Seq<u8>) -> Option<DocV>;

pub uninterp spec fn spec_encode(doc: DocV) -> Seq<u8>;

pub open spec fn spec_read(key: Seq<char>, body: Seq<u8>) -> DocV {
    match spec_decode_raw(body) {
        Some(doc) => doc,
        None => spec_empty_doc(key),
    }
}

pub struct PromV {
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
    pub callbacks: Seq<Seq<char>>,
    pub listeners: Seq<Seq<char>>,
}

pub struct TkV {
    pub state: TaskState,
    pub version: u64,
    pub pid: Option<Seq<char>>,
    pub ttl: Option<u64>,
    pub lease_timeout_at: Option<u64>,
    pub retry_timeout_at: Option<u64>,
    pub resumes: Seq<Seq<char>>,
}

pub struct ObjV {
    pub promise: PromV,
    pub task: Option<TkV>,
}

pub enum DocV {
    Origin(Map<Seq<char>, ObjV>),
    Schedule(Option<Schedule>),
}

pub open spec fn spec_string(chars: Seq<char>) -> String {
    choose|s: String| s@ == chars
}

pub open spec fn spec_bytes(body: Seq<u8>) -> Vec<u8> {
    choose|v: Vec<u8>| v@ == body
}

pub open spec fn spec_empty_value() -> Value {
    choose|v: Value| v@ == echod_types::spec::AValue::empty()
}

pub open spec fn spec_wrap_mul(a: u64, b: u64) -> u64 {
    (((a as nat) * (b as nat)) % 0x10000000000000000) as u64
}

pub open spec fn spec_fnv_acc(bytes: Seq<u8>, h: u64) -> u64
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        h
    } else {
        let mixed = h ^ (bytes[0] as u64);
        spec_fnv_acc(bytes.drop_first(), spec_wrap_mul(mixed, 0x00000100000001b3))
    }
}

pub open spec fn spec_utf8(chars: Seq<char>) -> Seq<u8>
    decreases chars.len(),
{
    if chars.len() == 0 {
        Seq::empty()
    } else {
        let c = chars[0] as u64;
        let head = if c < 0x80 {
            seq![c as u8]
        } else if c < 0x800 {
            seq![((c >> 6) | 0xc0) as u8, ((c & 0x3f) | 0x80) as u8]
        } else if c < 0x10000 {
            seq![((c >> 12) | 0xe0) as u8, (((c >> 6) & 0x3f) | 0x80) as u8, ((c & 0x3f) | 0x80) as u8]
        } else {
            seq![
                ((c >> 18) | 0xf0) as u8,
                (((c >> 12) & 0x3f) | 0x80) as u8,
                (((c >> 6) & 0x3f) | 0x80) as u8,
                ((c & 0x3f) | 0x80) as u8,
            ]
        };
        head + spec_utf8(chars.drop_first())
    }
}

pub open spec fn spec_fnv(chars: Seq<char>) -> u64 {
    spec_fnv_acc(spec_utf8(chars), 0xcbf29ce484222325)
}

pub open spec fn spec_owns(plane: PlaneV, key: Seq<char>) -> bool {
    plane.nodes != 0 && spec_fnv(key) % (plane.nodes as u64) == (plane.address as u64)
}

pub open spec fn spec_hex_digit(n: u64) -> char {
    if n == 0 { '0' }
    else if n == 1 { '1' }
    else if n == 2 { '2' }
    else if n == 3 { '3' }
    else if n == 4 { '4' }
    else if n == 5 { '5' }
    else if n == 6 { '6' }
    else if n == 7 { '7' }
    else if n == 8 { '8' }
    else if n == 9 { '9' }
    else if n == 10 { 'a' }
    else if n == 11 { 'b' }
    else if n == 12 { 'c' }
    else if n == 13 { 'd' }
    else if n == 14 { 'e' }
    else { 'f' }
}

pub open spec fn spec_hex_from(n: u64, shift: int) -> Seq<char>
    decreases shift,
{
    let d = (n >> (shift * 4)) & 0xf;
    if shift <= 0 {
        seq![spec_hex_digit(d)]
    } else {
        seq![spec_hex_digit(d)] + spec_hex_from(n, shift - 1)
    }
}

/// `content_etag`: FNV-1a of the lossy UTF-8 view of the body, as sixteen hex digits.
pub open spec fn spec_etag_chars(body: Seq<u8>) -> Seq<char> {
    spec_hex_from(spec_fnv_acc(spec_lossy(body), 0xcbf29ce484222325), 15)
}

pub open spec fn spec_cont(b: u8) -> bool {
    b >= 0x80 && b < 0xc0
}

pub open spec fn spec_utf8_width(lead: u8) -> nat {
    if lead < 0x80 {
        1
    } else if lead >= 0xc2 && lead <= 0xdf {
        2
    } else if lead >= 0xe0 && lead <= 0xef {
        3
    } else if lead >= 0xf0 && lead <= 0xf4 {
        4
    } else {
        0
    }
}

pub open spec fn spec_utf8_ok(lead: u8, pos: nat, b: u8) -> bool {
    if pos == 0 {
        true
    } else if pos == 1 {
        if lead >= 0xc2 && lead <= 0xdf {
            spec_cont(b)
        } else if lead == 0xe0 {
            b >= 0xa0 && b <= 0xbf
        } else if (lead >= 0xe1 && lead <= 0xec) || (lead >= 0xee && lead <= 0xef) {
            spec_cont(b)
        } else if lead == 0xed {
            b >= 0x80 && b <= 0x9f
        } else if lead == 0xf0 {
            b >= 0x90 && b <= 0xbf
        } else if lead >= 0xf1 && lead <= 0xf3 {
            spec_cont(b)
        } else if lead == 0xf4 {
            b >= 0x80 && b <= 0x8f
        } else {
            false
        }
    } else {
        spec_cont(b)
    }
}

/// How many leading bytes form one UTF-8 character, or the maximal subpart
/// of one ill-formed sequence. The same split `String::from_utf8_lossy` uses.
pub open spec fn spec_prefix(bytes: Seq<u8>, width: nat, pos: nat) -> nat
    decreases width - pos,
{
    if pos >= width {
        width
    } else if pos >= bytes.len() || !spec_utf8_ok(bytes[0], pos, bytes[pos]) {
        pos
    } else {
        spec_prefix(bytes, width, pos + 1)
    }
}

pub open spec fn spec_lossy(bytes: Seq<u8>) -> Seq<u8>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        Seq::empty()
    } else {
        let width = spec_utf8_width(bytes[0]);
        if width == 1 {
            seq![bytes[0]] + spec_lossy(bytes.skip(1))
        } else if width == 0 {
            seq![0xefu8, 0xbfu8, 0xbdu8] + spec_lossy(bytes.skip(1))
        } else {
            let prefix = spec_prefix(bytes, width, 1);
            if prefix == width {
                bytes.take(width as int) + spec_lossy(bytes.skip(width as int))
            } else {
                seq![0xefu8, 0xbfu8, 0xbdu8] + spec_lossy(bytes.skip(prefix as int))
            }
        }
    }
}

pub open spec fn spec_sat_add(a: u64, b: u64) -> u64 {
    if (a as nat) + (b as nat) > (u64::MAX as nat) {
        u64::MAX
    } else {
        ((a as nat) + (b as nat)) as u64
    }
}

pub open spec fn spec_etag(body: Seq<u8>) -> Etag {
    Etag(spec_string(spec_etag_chars(body)))
}

pub open spec fn spec_find(entries: Seq<EntryV>, key: Seq<char>, i: int) -> Option<int>
    decreases entries.len() - i,
{
    if i < 0 || i >= entries.len() {
        None
    } else if entries[i].key == key {
        Some(i)
    } else {
        spec_find(entries, key, i + 1)
    }
}

pub open spec fn spec_insert_at(entries: Seq<EntryV>, entry: EntryV, i: int) -> Seq<EntryV>
    decreases entries.len() - i,
{
    if i >= entries.len() {
        entries.push(entry)
    } else if spec_before(entry.key, entries[i].key) {
        entries.take(i).push(entry) + entries.skip(i)
    } else {
        spec_insert_at(entries, entry, i + 1)
    }
}

pub open spec fn spec_before(a: Seq<char>, b: Seq<char>) -> bool
    decreases a.len() + b.len(),
{
    if a.len() == 0 { b.len() != 0 }
    else if b.len() == 0 { false }
    else if a[0] != b[0] { a[0] < b[0] }
    else { spec_before(a.drop_first(), b.drop_first()) }
}

pub open spec fn spec_put(entries: Seq<EntryV>, entry: EntryV) -> Seq<EntryV> {
    match spec_find(entries, entry.key, 0) {
        Some(i) => entries.update(i, entry),
        None => spec_insert_at(entries, entry, 0),
    }
}

pub open spec fn spec_remove_at(entries: Seq<EntryV>, i: int) -> Seq<EntryV> {
    entries.take(i) + entries.skip(i + 1)
}

/// One store call. The same cases as `Store::apply`.
pub open spec fn spec_apply(store: StoreV, call: StoreCall) -> (StoreV, StoreOutcome) {
    match call {
        StoreCall::Get { key } => {
            match spec_find(store.entries, key@, 0) {
                None => (store, StoreOutcome::Got(None)),
                Some(i) => {
                    let body = store.entries[i].body;
                    (store, StoreOutcome::Got(Some((spec_bytes(body), spec_etag(body)))))
                },
            }
        },
        StoreCall::GetIfNoneMatch { key, etag } => {
            match spec_find(store.entries, key@, 0) {
                None => (store, StoreOutcome::Read(Read::Absent)),
                Some(i) => {
                    let body = store.entries[i].body;
                    let have = spec_etag(body);
                    if have == etag {
                        (store, StoreOutcome::Read(Read::NotModified))
                    } else {
                        (store, StoreOutcome::Read(Read::Body(spec_bytes(body), have)))
                    }
                },
            }
        },
        StoreCall::PutIfNoneMatch { key, body } => {
            if spec_find(store.entries, key@, 0) is Some {
                (store, StoreOutcome::Failed(StoreError::PreconditionFailed))
            } else {
                let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version: 1 });
                (StoreV { entries, ..store }, StoreOutcome::Written(spec_etag(body@)))
            }
        },
        StoreCall::PutIfMatch { key, body, etag } => {
            match spec_find(store.entries, key@, 0) {
                Some(i) if spec_etag(store.entries[i].body) == etag => {
                    let version = (store.entries[i].version + 1) as nat;
                    let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version });
                    (StoreV { entries, ..store }, StoreOutcome::Written(spec_etag(body@)))
                },
                _ => (store, StoreOutcome::Failed(StoreError::PreconditionFailed)),
            }
        },
        StoreCall::AppendIfMatch { key, offset, body, etag } => {
            if !store.appendable {
                (store, StoreOutcome::Failed(StoreError::Unavailable(spec_string(seq![
                    't', 'h', 'i', 's', ' ', 's', 't', 'o', 'r', 'e', ' ', 'd', 'o', 'e', 's', ' ',
                    'n', 'o', 't', ' ', 'a', 'p', 'p', 'e', 'n', 'd',
                ]))))
            } else {
                match spec_find(store.entries, key@, 0) {
                    Some(i) if spec_etag(store.entries[i].body) == etag && store.entries[i].body.len() == offset => {
                        let joined = store.entries[i].body + body@;
                        let version = (store.entries[i].version + 1) as nat;
                        let entries = spec_put(store.entries, EntryV { key: key@, body: joined, version });
                        (StoreV { entries, ..store }, StoreOutcome::Written(spec_etag(joined)))
                    },
                    _ => (store, StoreOutcome::Failed(StoreError::PreconditionFailed)),
                }
            }
        },
        StoreCall::Put { key, body } => {
            let version = match spec_find(store.entries, key@, 0) {
                Some(i) => (store.entries[i].version + 1) as nat,
                None => 1,
            };
            let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version });
            (StoreV { entries, ..store }, StoreOutcome::Done)
        },
        StoreCall::Delete { key } => {
            match spec_find(store.entries, key@, 0) {
                Some(i) => (StoreV { entries: spec_remove_at(store.entries, i), ..store }, StoreOutcome::Done),
                None => (store, StoreOutcome::Done),
            }
        },
        StoreCall::List { prefix, max_keys } => {
            (store, StoreOutcome::Listed(spec_bytes_keys(spec_list(store.entries, prefix@, max_keys as nat, 0, Seq::empty()))))
        },
        StoreCall::ListPrefixes { prefix } => {
            (store, StoreOutcome::Listed(spec_bytes_keys(spec_prefixes(store.entries, prefix@, 0, Seq::empty()))))
        },
    }
}

pub open spec fn spec_list(entries: Seq<EntryV>, prefix: Seq<char>, max: nat, i: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases entries.len() - i,
{
    if i < 0 || i >= entries.len() || acc.len() >= max {
        acc
    } else if spec_starts(entries[i].key, prefix) {
        spec_list(entries, prefix, max, i + 1, acc.push(entries[i].key))
    } else {
        spec_list(entries, prefix, max, i + 1, acc)
    }
}

pub open spec fn spec_starts(text: Seq<char>, prefix: Seq<char>) -> bool
    decreases prefix.len(),
{
    if prefix.len() == 0 { true }
    else if text.len() == 0 { false }
    else { text[0] == prefix[0] && spec_starts(text.drop_first(), prefix.drop_first()) }
}

pub open spec fn spec_prefixes(entries: Seq<EntryV>, prefix: Seq<char>, i: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases entries.len() - i,
{
    if i < 0 || i >= entries.len() {
        acc
    } else if spec_starts(entries[i].key, prefix) {
        let tail = entries[i].key.skip(prefix.len() as int);
        match spec_slash(tail, 0) {
            Some(n) => {
                let child = entries[i].key.take(prefix.len() + n + 1);
                let acc = if acc.len() > 0 && acc.last() == child { acc } else { acc.push(child) };
                spec_prefixes(entries, prefix, i + 1, acc)
            },
            None => spec_prefixes(entries, prefix, i + 1, acc),
        }
    } else {
        spec_prefixes(entries, prefix, i + 1, acc)
    }
}

pub open spec fn spec_slash(text: Seq<char>, i: int) -> Option<int>
    decreases text.len() - i,
{
    if i < 0 || i >= text.len() { None }
    else if text[i] == '/' { Some(i) }
    else { spec_slash(text, i + 1) }
}

pub open spec fn spec_bytes_keys(keys: Seq<Seq<char>>) -> Vec<String> {
    choose|v: Vec<String>| v@.map_values(|s: String| s@) == keys
}

pub open spec fn spec_one(state: LocalV, send: Seq<(Pid, Message)>) -> Seq<StepResultV<LocalV, Pid, Message>> {
    seq![StepResultV { state, send }]
}

pub open spec fn spec_clock(logic: LogicV, now: Time) -> LogicV {
    LogicV { clock: now as nat, ..logic }
}

pub open spec fn spec_cached(plane: PlaneV, key: Seq<char>) -> Option<CachedV> {
    spec_cached_from(plane.documents, key, 0)
}

pub open spec fn spec_cached_from(docs: Seq<CachedV>, key: Seq<char>, i: int) -> Option<CachedV>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() { None }
    else if docs[i].key == key { Some(docs[i]) }
    else { spec_cached_from(docs, key, i + 1) }
}

pub open spec fn spec_is_empty(doc: DocV) -> bool {
    match doc {
        DocV::Origin(map) => map.dom().len() == 0,
        DocV::Schedule(slot) => slot is None,
    }
}

/// `remember`: an empty document with no etag leaves the cache.
pub open spec fn spec_keep(docs: Seq<CachedV>, key: Seq<char>, doc: DocV, etag: Option<Seq<char>>) -> Seq<CachedV> {
    if spec_is_empty(doc) && etag is None {
        spec_forget(docs, key, 0)
    } else {
        spec_remember(docs, key, spec_encode(doc), etag, 0)
    }
}

pub open spec fn spec_remember(docs: Seq<CachedV>, key: Seq<char>, body: Seq<u8>, etag: Option<Seq<char>>, i: int) -> Seq<CachedV>
    decreases docs.len() - i,
{
    let entry = CachedV { key, body, etag };
    if i >= docs.len() {
        docs.push(entry)
    } else if docs[i].key == key {
        docs.update(i, entry)
    } else {
        spec_remember(docs, key, body, etag, i + 1)
    }
}

pub open spec fn spec_forget(docs: Seq<CachedV>, key: Seq<char>, i: int) -> Seq<CachedV>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() { docs }
    else if docs[i].key == key { docs.take(i) + docs.skip(i + 1) }
    else { spec_forget(docs, key, i + 1) }
}

/// A node event, the same arms as `Node::on_event`.
pub open spec fn spec_node(node: NodeV, now: Time, event: ProcessEvent<Pid, Message>) -> Seq<StepResultV<LocalV, Pid, Message>> {
    match event {
        ProcessEvent::Timeout => match node.wake {
            Some(at) if at <= now as nat && node.plane.flight is None => {
                let (plane, send) = spec_timeout(node.plane, now);
                spec_one(LocalV::Node(NodeV {
                    logic: LogicV { clock: now as nat, last_wake: None, ..node.logic },
                    wake: spec_wake(plane),
                    plane,
                    ..node
                }), send)
            },
            Some(at) if at <= now as nat => spec_one(LocalV::Node(node), Seq::empty()),
            _ => Seq::empty(),
        },
        ProcessEvent::Receive { sender: Pid::Outside, message: Message::Request(call) } => {
            if node.plane.flight is Some {
                spec_one(LocalV::Node(node), Seq::empty())
            } else {
                let (plane, send) = spec_request(node.plane, now, call);
                spec_one(LocalV::Node(NodeV {
                    logic: spec_clock(node.logic, now),
                    next_request: node.next_request + 1,
                    wake: spec_wake(plane),
                    plane,
                    ..node
                }), send)
            }
        },
        ProcessEvent::Receive { sender: Pid::Store, message: Message::StoreReply { op, outcome } } => {
            if node.plane.flight is None {
                spec_one(LocalV::Node(node), Seq::empty())
            } else {
                let (plane, send) = spec_store_reply(node.plane, op, outcome);
                spec_one(LocalV::Node(NodeV {
                    logic: spec_clock(node.logic, now),
                    wake: spec_wake(plane),
                    plane,
                    ..node
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

pub open spec fn spec_store(store: StoreV, event: ProcessEvent<Pid, Message>) -> Seq<StepResultV<LocalV, Pid, Message>> {
    match event {
        ProcessEvent::Receive { sender, message: Message::StoreReq { op, call } } => {
            let (next, outcome) = spec_apply(store, call);
            spec_one(
                LocalV::Store(next),
                seq![(sender, Message::StoreReply { op, outcome })],
            )
        },
        _ => Seq::empty(),
    }
}

pub open spec fn spec_step(
    _config: super::Fleet,
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

pub open spec fn spec_request(plane: PlaneV, now: Time, call: Call) -> (PlaneV, Seq<(Pid, Message)>) {
    match spec_key(call.request) {
        None => (plane, seq![spec_reply(call.client@, call.id, spec_pure(call.request))]),
        Some(key) => {
            if !spec_owns(plane, key) {
                (plane, seq![spec_reply(call.client@, call.id, spec_unavailable(call.request))])
            } else {
                spec_begin(plane, key, JobV::External(call.request), now, Some((call.client@, call.id)))
            }
        },
    }
}

pub open spec fn spec_timeout(plane: PlaneV, now: Time) -> (PlaneV, Seq<(Pid, Message)>) {
    if plane.flight is Some {
        (plane, Seq::empty())
    } else if plane.pending.len() > 0 {
        let pending = plane.pending[0];
        let plane = PlaneV { pending: plane.pending.skip(1), ..plane };
        let key = spec_origin_key(origin(pending.promise));
        if !spec_owns(plane, key) {
            (plane, Seq::empty())
        } else {
            spec_begin(plane, key, JobV::Occurrence(pending), now, None)
        }
    } else {
        match spec_earliest_key(plane, now) {
            Some(key) => spec_begin(plane, key, JobV::Due, now, None),
            None => (plane, Seq::empty()),
        }
    }
}

pub open spec fn spec_store_reply(plane: PlaneV, op: u64, outcome: StoreOutcome) -> (PlaneV, Seq<(Pid, Message)>) {
    match plane.flight {
        None => (plane, Seq::empty()),
        Some(flight) => {
            if flight.op != op {
                (plane, Seq::empty())
            } else if !flight.writing {
                match outcome {
                    StoreOutcome::Got(got) => {
                        let (doc, etag) = match got {
                            Some((body, tag)) => (spec_read(flight.key, body@), Some(tag.0@)),
                            None => (spec_empty_doc(flight.key), None),
                        };
                        let flight = FlightV { etag, ..flight };
                        spec_decide(PlaneV { flight: None, ..plane }, flight, doc)
                    },
                    StoreOutcome::Failed(_) => spec_fail(PlaneV { flight: None, ..plane }, flight),
                    _ => (plane, Seq::empty()),
                }
            } else {
                match outcome {
                    StoreOutcome::Written(tag) => spec_commit(plane, flight, tag),
                    StoreOutcome::Failed(_) => spec_fail(PlaneV { flight: None, ..plane }, flight),
                    _ => (plane, Seq::empty()),
                }
            }
        },
    }
}

pub open spec fn spec_flight(op: u64, key: Seq<char>, etag: Option<Seq<char>>, now: Time, caller: Option<(Seq<char>, u64)>, job: JobV) -> FlightV {
    FlightV {
        op,
        key,
        writing: false,
        etag,
        now,
        caller,
        job,
        born: Seq::empty(),
        reply: None,
        notify: Seq::empty(),
        decided: None,
    }
}

pub open spec fn spec_begin(plane: PlaneV, key: Seq<char>, job: JobV, now: Time, caller: Option<(Seq<char>, u64)>) -> (PlaneV, Seq<(Pid, Message)>) {
    match spec_cached(plane, key) {
        Some(cached) => spec_decide(plane, spec_flight(0, key, cached.etag, now, caller, job), spec_read(key, cached.body)),
        None => {
            let op = plane.next_op;
            let flight = spec_flight(op, key, None, now, caller, job);
            (PlaneV { flight: Some(flight), next_op: op + 1, ..plane }, seq![spec_get(op, key)])
        },
    }
}

pub open spec fn spec_decide(plane: PlaneV, flight: FlightV, doc: DocV) -> (PlaneV, Seq<(Pid, Message)>) {
    let (next, reply, born, notify) = match flight.job {
        JobV::External(request) => {
            let (next, response) = spec_handle(doc, request, flight.now);
            (next, Some(response), Seq::empty(), Seq::empty())
        },
        JobV::Due => spec_run_due(doc, flight.now),
        JobV::Occurrence(pending) => (spec_occurrence(doc, pending, flight.now), None, Seq::empty(), Seq::empty()),
    };
    let reply = match (flight.caller, reply) {
        (Some((client, id)), Some(response)) => Some((client, id, response)),
        _ => None,
    };
    let previous = match spec_cached(plane, flight.key) {
        Some(cached) => spec_read(flight.key, cached.body),
        None => spec_empty_doc(flight.key),
    };
    if next == previous && born.len() == 0 {
        let plane = PlaneV {
            flight: None,
            documents: spec_keep(plane.documents, flight.key, next, flight.etag),
            ..plane
        };
        let send = match reply {
            Some((client, id, response)) => seq![spec_reply(client, id, response)],
            None => Seq::empty(),
        };
        (plane, send + spec_notes(notify))
    } else {
        let op = plane.next_op;
        let body = spec_encode(next);
        let call = match flight.etag {
            Some(chars) => StoreCall::PutIfMatch {
                key: spec_string(flight.key),
                body: spec_bytes(body),
                etag: Etag(spec_string(chars)),
            },
            None => StoreCall::PutIfNoneMatch { key: spec_string(flight.key), body: spec_bytes(body) },
        };
        let flight = FlightV {
            op,
            writing: true,
            born,
            reply,
            notify,
            decided: Some(body),
            ..flight
        };
        (PlaneV { flight: Some(flight), next_op: op + 1, ..plane }, seq![(Pid::Store, Message::StoreReq { op, call })])
    }
}

pub open spec fn spec_commit(plane: PlaneV, flight: FlightV, tag: Etag) -> (PlaneV, Seq<(Pid, Message)>) {
    let documents = match flight.decided {
        Some(body) => spec_remember(plane.documents, flight.key, body, Some(tag.0@), 0),
        None => plane.documents,
    };
    let plane = PlaneV {
        flight: None,
        documents,
        pending: plane.pending + flight.born,
        ..plane
    };
    let send = match flight.reply {
        Some((client, id, response)) => seq![spec_reply(client, id, response)],
        None => Seq::empty(),
    };
    (plane, send + spec_notes(flight.notify))
}

pub open spec fn spec_fail(plane: PlaneV, flight: FlightV) -> (PlaneV, Seq<(Pid, Message)>) {
    match (flight.job, flight.caller) {
        (JobV::External(request), Some((client, id))) => {
            (plane, seq![spec_reply(client, id, spec_unavailable(request))])
        },
        _ => (plane, Seq::empty()),
    }
}

pub open spec fn spec_origin_key(origin_chars: Seq<char>) -> Seq<char> {
    seq!['o', '/'] + origin_chars
}

pub open spec fn spec_schedule_key(id: Seq<char>) -> Seq<char> {
    seq!['s', '/'] + id
}

pub open spec fn spec_empty_doc(key: Seq<char>) -> DocV {
    if spec_starts(key, seq!['s', '/']) { DocV::Schedule(None) } else { DocV::Origin(Map::empty()) }
}

pub open spec fn spec_key(request: Request) -> Option<Seq<char>> {
    match request {
        Request::PromiseGet(q) => Some(spec_origin_key(origin(q.id@))),
        Request::PromiseCreate(q) => Some(spec_origin_key(origin(q.id@))),
        Request::PromiseSettle(q) => Some(spec_origin_key(origin(q.id@))),
        Request::PromiseRegisterCallback(q) => Some(spec_origin_key(origin(q.awaited@))),
        Request::PromiseRegisterListener(q) => Some(spec_origin_key(origin(q.awaited@))),
        Request::TaskGet(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskCreate(q) => Some(spec_origin_key(origin(q.action.id@))),
        Request::TaskAcquire(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskFulfill(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskRelease(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskHalt(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskContinue(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskFence(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskFenceCheck(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskSuspend(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskHeartbeat(q) => {
            if q.tasks@.len() == 0 { None } else { Some(spec_origin_key(origin(q.tasks@[0].id@))) }
        },
        Request::ScheduleGet(q) => Some(spec_schedule_key(q.id@)),
        Request::ScheduleDelete(q) => Some(spec_schedule_key(q.id@)),
        Request::ScheduleCreate(q) => Some(spec_schedule_key(q.id@)),
    }
}

pub open spec fn spec_promise_res(status: u16, promise: Option<PromiseRecord>) -> Response {
    Response::Promise(PromiseRes { status, promise })
}

pub open spec fn spec_pure(request: Request) -> Response {
    match request {
        Request::TaskHeartbeat(q) if q.tasks@.len() == 0 => Response::Status(StatusRes { status: 200 }),
        other => spec_unavailable(other),
    }
}

pub open spec fn spec_unavailable(request: Request) -> Response {
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => spec_promise_res(503, None),
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => Response::Schedule(ScheduleRes { status: 503, schedule: None }),
        Request::ScheduleDelete(_) | Request::TaskRelease(_) | Request::TaskHalt(_)
        | Request::TaskContinue(_) | Request::TaskHeartbeat(_) | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => Response::Status(StatusRes { status: 503 }),
        Request::TaskGet(_) => Response::TaskGet(TaskGetRes { status: 503, task: None }),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => Response::TaskClaim(TaskClaimRes { status: 503, task: None, promise: None }),
        Request::TaskFulfill(_) => spec_promise_res(503, None),
        Request::TaskFence(_) => Response::TaskFence(TaskFenceRes { status: 503, action: None }),
    }
}

/// One request against one document. The same match as `handle`.
pub open spec fn spec_handle(doc: DocV, request: Request, now: Time) -> (DocV, Response) {
    match request {
        Request::PromiseGet(q) => spec_promise_get(doc, q.id, now),
        Request::PromiseCreate(q) => spec_promise_create(doc, q, now),
        Request::PromiseSettle(q) => spec_promise_settle(doc, q, now),
        Request::PromiseRegisterCallback(q) => spec_register_callback(doc, q.awaited, q.awaiter, now),
        Request::PromiseRegisterListener(q) => spec_register_listener(doc, q.awaited, q.address, now),
        Request::TaskGet(q) => spec_task_get(doc, q.id, now),
        Request::TaskCreate(q) => spec_task_create(doc, q.pid, q.ttl, q.action, now),
        Request::TaskAcquire(q) => spec_task_acquire(doc, q.id, q.version, q.pid, q.ttl, now),
        Request::TaskFulfill(q) => spec_task_fulfill(doc, q.id, q.version, q.action, now),
        Request::TaskRelease(q) => spec_task_release(doc, q.id, q.version, now),
        Request::TaskHalt(q) => spec_task_halt(doc, q.id, now),
        Request::TaskContinue(q) => spec_task_continue(doc, q.id, now),
        Request::TaskHeartbeat(q) => spec_heartbeat(doc, q.pid, q.tasks@, now),
        Request::TaskSuspend(q) => spec_suspend(doc, q.id, q.version, q.actions@, now),
        Request::TaskFence(q) => spec_fence(doc, q.id, q.version, q.action, now),
        Request::TaskFenceCheck(q) => spec_fence_check(doc, q.id, q.version, now),
        Request::ScheduleGet(q) => spec_schedule_get(doc, q.id),
        Request::ScheduleCreate(q) => spec_schedule_create(doc, q, now),
        Request::ScheduleDelete(q) => spec_schedule_delete(doc, q.id),
    }
}

pub open spec fn spec_origin_map(doc: DocV) -> Map<Seq<char>, ObjV> {
    match doc {
        DocV::Origin(map) => map,
        DocV::Schedule(_) => Map::empty(),
    }
}

/// `origin_mut` replaces a schedule document with an empty origin map before it looks anything up.
pub open spec fn spec_opened(doc: DocV) -> DocV {
    DocV::Origin(spec_origin_map(doc))
}

pub open spec fn spec_with_origin(doc: DocV, map: Map<Seq<char>, ObjV>) -> DocV {
    match doc {
        DocV::Schedule(_) => DocV::Origin(map),
        DocV::Origin(_) => DocV::Origin(map),
    }
}

pub open spec fn spec_project_prom(p: PromV, now: Time) -> PromV {
    if p.state == PromiseState::Pending && now >= p.timeout_at {
        PromV {
            state: if spec_timer(p.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
            settled_at: Some(p.timeout_at),
            ..p
        }
    } else {
        p
    }
}

pub open spec fn spec_fulfill_task(t: TkV) -> TkV {
    TkV {
        state: TaskState::Fulfilled,
        pid: None,
        ttl: None,
        lease_timeout_at: None,
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_project_obj(obj: ObjV, now: Time) -> ObjV {
    let promise = spec_project_prom(obj.promise, now);
    let task = match obj.task {
        Some(t) if promise.state != PromiseState::Pending && t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)),
        other => other,
    };
    ObjV { promise, task }
}

pub open spec fn spec_record(id: String, p: PromV) -> PromiseRecord {
    PromiseRecord {
        id,
        state: p.state,
        param: p.param,
        value: p.value,
        tags: p.tags,
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    }
}

pub open spec fn spec_task_record(id: String, t: TkV) -> TaskRecord {
    TaskRecord {
        id,
        state: t.state,
        version: t.version,
        resumes: if t.resumes.len() > u64::MAX as nat { u64::MAX } else { t.resumes.len() as u64 },
        ttl: t.ttl,
        pid: match t.pid { Some(s) => Some(spec_string(s)), None => None },
    }
}

pub open spec fn spec_timer(tags: Tags) -> bool {
    spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r'], seq!['t','r','u','e'], 0)
}

pub open spec fn spec_targeted(tags: Tags) -> bool {
    spec_tag_key(tags, seq!['r','e','s','o','n','a','t','e',':','t','a','r','g','e','t'], 0)
}

pub open spec fn spec_awaitable(tags: Tags) -> bool {
    spec_targeted(tags)
        || spec_timer(tags)
        || spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l'], seq!['t','r','u','e'], 0)
        || spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e'], seq!['g','l','o','b','a','l'], 0)
}

pub open spec fn spec_tag_is(tags: Tags, key: Seq<char>, value: Seq<char>, i: int) -> bool
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() { false }
    else if tags@[i].0@ == key { tags@[i].1@ == value }
    else { spec_tag_is(tags, key, value, i + 1) }
}

pub open spec fn spec_tag_key(tags: Tags, key: Seq<char>, i: int) -> bool
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() { false }
    else if tags@[i].0@ == key { true }
    else { spec_tag_key(tags, key, i + 1) }
}

pub open spec fn spec_offer_at(tags: Tags, now: Time) -> u64 {
    match spec_delay(tags, 0) {
        Some(delay) => if delay > now { delay } else { now },
        None => now,
    }
}

pub open spec fn spec_delay(tags: Tags, i: int) -> Option<u64>
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() { None }
    else if tags@[i].0@ == seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 'd', 'e', 'l', 'a', 'y'] {
        spec_parse_u64(tags@[i].1@)
    } else {
        spec_delay(tags, i + 1)
    }
}

pub open spec fn spec_parse_u64(s: Seq<char>) -> Option<u64> {
    if s.len() == 0 { None } else { spec_parse_acc(s, 0, 0) }
}

pub open spec fn spec_parse_acc(s: Seq<char>, i: int, acc: nat) -> Option<u64>
    decreases s.len() - i,
{
    if i >= s.len() {
        Some(acc as u64)
    } else if s[i] < '0' || s[i] > '9' {
        None
    } else {
        let n = acc * 10 + ((s[i] as u64) - ('0' as u64)) as nat;
        if n > (u64::MAX as nat) { None } else { spec_parse_acc(s, i + 1, n) }
    }
}

pub open spec fn spec_promise_get(doc: DocV, id: String, now: Time) -> (DocV, Response) {
    let doc = spec_opened(doc);
    let map = spec_origin_map(doc);
    if !map.contains_key(id@) {
        (doc, spec_promise_res(404, None))
    } else {
        let obj = spec_project_obj(map[id@], now);
        (doc, spec_promise_res(200, Some(spec_record(id, obj.promise))))
    }
}

pub open spec fn spec_new_obj(timeout_at: u64, now: Time, param: Value, tags: Tags, runnable: bool) -> ObjV {
    let live = timeout_at > now;
    let promise = PromV {
        state: if live { PromiseState::Pending } else if spec_timer(tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
        param,
        value: spec_empty_value(),
        tags,
        timeout_at,
        created_at: if live { now } else { timeout_at },
        settled_at: if live { None } else { Some(timeout_at) },
        callbacks: Seq::empty(),
        listeners: Seq::empty(),
    };
    let task = if runnable {
        Some(TkV {
            state: if live { TaskState::Pending } else { TaskState::Fulfilled },
            version: 0,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: if live { Some(spec_offer_at(tags, now)) } else { None },
            resumes: Seq::empty(),
        })
    } else {
        None
    };
    ObjV { promise, task }
}

pub open spec fn spec_promise_create(doc: DocV, req: PromiseCreateReq, now: Time) -> (DocV, Response) {
    if spec_timer(req.tags) && spec_targeted(req.tags) {
        (doc, spec_promise_res(400, None))
    } else {
        let map = spec_origin_map(doc);
        if map.contains_key(req.id@) {
            let obj = spec_project_obj(map[req.id@], now);
            (doc, spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
        } else {
            let obj = spec_new_obj(req.timeout_at, now, req.param, req.tags, spec_targeted(req.tags));
            (spec_with_origin(doc, map.insert(req.id@, obj)), spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
        }
    }
}

pub open spec fn spec_promise_settle(doc: DocV, req: PromiseSettleReq, now: Time) -> (DocV, Response) {
    if !req.state.spec_settable() {
        (doc, spec_promise_res(400, None))
    } else {
        let doc = spec_opened(doc);
        let map = spec_origin_map(doc);
        if !map.contains_key(req.id@) {
            (doc, spec_promise_res(404, None))
        } else {
            let seen = spec_project_obj(map[req.id@], now);
            if seen.promise.state != PromiseState::Pending {
                (doc, spec_promise_res(200, Some(spec_record(req.id, seen.promise))))
            } else {
                let promise = PromV { state: req.state, value: req.value, settled_at: Some(now), ..seen.promise };
                let task = match seen.task {
                    Some(t) if t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)),
                    other => other,
                };
                let obj = ObjV { promise, task };
                (spec_with_origin(doc, map.insert(req.id@, obj)), spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
            }
        }
    }
}

pub open spec fn spec_register_callback(doc: DocV, awaited: String, awaiter: String, now: Time) -> (DocV, Response) {
    if awaited@ == awaiter@ || !same_origin_spec(awaited@, awaiter@) {
        (doc, spec_promise_res(400, None))
    } else {
        let doc = spec_opened(doc);
        let map = spec_origin_map(doc);
        if !map.contains_key(awaited@) {
            (doc, spec_promise_res(404, None))
        } else if !map.contains_key(awaiter@) {
            (doc, spec_promise_res(422, None))
        } else {
            let awaited_obj = spec_project_obj(map[awaited@], now);
            let awaiter_obj = spec_project_obj(map[awaiter@], now);
            if !spec_targeted(awaiter_obj.promise.tags) || !spec_awaitable(awaited_obj.promise.tags) {
                (doc, spec_promise_res(422, None))
            } else {
                let res = spec_promise_res(200, Some(spec_record(awaited, awaited_obj.promise)));
                if awaited_obj.promise.state == PromiseState::Pending && awaiter_obj.promise.state == PromiseState::Pending {
                    let callbacks = if awaited_obj.promise.callbacks.contains(awaiter@) {
                        awaited_obj.promise.callbacks
                    } else {
                        awaited_obj.promise.callbacks.push(awaiter@)
                    };
                    let awaited_obj = ObjV { promise: PromV { callbacks, ..awaited_obj.promise }, ..awaited_obj };
                    (spec_with_origin(doc, map.insert(awaited@, awaited_obj)), res)
                } else {
                    (doc, res)
                }
            }
        }
    }
}

pub open spec fn spec_register_listener(doc: DocV, awaited: String, address: String, now: Time) -> (DocV, Response) {
    let doc = spec_opened(doc);
    let map = spec_origin_map(doc);
    if !map.contains_key(awaited@) {
        (doc, spec_promise_res(404, None))
    } else {
        let obj = spec_project_obj(map[awaited@], now);
        if !spec_awaitable(obj.promise.tags) {
            (doc, spec_promise_res(422, None))
        } else {
            let res = spec_promise_res(200, Some(spec_record(awaited, obj.promise)));
            if obj.promise.state == PromiseState::Pending {
                let listeners = if obj.promise.listeners.contains(address@) {
                    obj.promise.listeners
                } else {
                    obj.promise.listeners.push(address@)
                };
                let obj = ObjV { promise: PromV { listeners, ..obj.promise }, ..obj };
                (spec_with_origin(doc, map.insert(awaited@, obj)), res)
            } else {
                (doc, res)
            }
        }
    }
}

pub open spec fn spec_task_get(doc: DocV, id: String, now: Time) -> (DocV, Response) {
    let doc = spec_opened(doc);
    let map = spec_origin_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::TaskGet(TaskGetRes { status: 404, task: None }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::TaskGet(TaskGetRes { status: 404, task: None })),
            Some(t) => (doc, Response::TaskGet(TaskGetRes { status: 200, task: Some(spec_task_record(id, t)) })),
        }
    }
}

pub open spec fn spec_acquire(t: TkV, pid: Seq<char>, ttl: u64, now: Time) -> TkV {
    TkV {
        state: TaskState::Acquired,
        version: spec_sat_add(t.version, 1),
        pid: Some(pid),
        ttl: Some(ttl),
        lease_timeout_at: Some(spec_sat_add(now, ttl)),
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_task_create(doc: DocV, pid: String, ttl: u64, action: PromiseCreateReq, now: Time) -> (DocV, Response) {
    if !spec_targeted(action.tags) || spec_timer(action.tags) {
        (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
    } else {
        let (doc, created) = spec_promise_create(doc, action, now);
        match created {
            Response::Promise(inner) if inner.status == 400 => {
                (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
            },
            _ => {
                let map = spec_origin_map(doc);
                if !map.contains_key(action.id@) {
                    (doc, Response::TaskClaim(TaskClaimRes { status: 422, task: None, promise: None }))
                } else {
                    let seen = spec_project_obj(map[action.id@], now);
                    if !spec_targeted(seen.promise.tags) {
                        (doc, Response::TaskClaim(TaskClaimRes { status: 422, task: None, promise: None }))
                    } else {
                        match seen.task {
                            None => (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None })),
                            Some(t) if t.state == TaskState::Fulfilled => (
                                doc,
                                Response::TaskClaim(TaskClaimRes {
                                    status: 200,
                                    task: Some(spec_task_record(action.id, t)),
                                    promise: Some(spec_record(action.id, seen.promise)),
                                }),
                            ),
                            Some(t) if t.state == TaskState::Pending => {
                                let u = spec_acquire(t, pid@, ttl, now);
                                let obj = ObjV { task: Some(u), ..seen };
                                (
                                    spec_with_origin(doc, map.insert(action.id@, obj)),
                                    Response::TaskClaim(TaskClaimRes {
                                        status: 200,
                                        task: Some(spec_task_record(action.id, u)),
                                        promise: Some(spec_record(action.id, obj.promise)),
                                    }),
                                )
                            },
                            _ => (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None })),
                        }
                    }
                }
            },
        }
    }
}

pub enum Held { Ok(ObjV), Missing, Stale }

pub open spec fn spec_held(map: Map<Seq<char>, ObjV>, id: Seq<char>, version: u64, now: Time) -> (Map<Seq<char>, ObjV>, Held) {
    if !map.contains_key(id) {
        (map, Held::Missing)
    } else {
        let obj = spec_project_obj(map[id], now);
        match obj.task {
            None => (map, Held::Missing),
            Some(t) if t.state == TaskState::Acquired && t.version == version && obj.promise.state == PromiseState::Pending => (map, Held::Ok(obj)),
            _ => (map, Held::Stale),
        }
    }
}

pub open spec fn spec_task_acquire(doc: DocV, id: String, version: u64, pid: String, ttl: u64, now: Time) -> (DocV, Response) {
    let doc = spec_opened(doc);
    let map = spec_origin_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::TaskClaim(TaskClaimRes { status: 404, task: None, promise: None }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::TaskClaim(TaskClaimRes { status: 404, task: None, promise: None })),
            Some(t) if t.state != TaskState::Pending || t.version != version || obj.promise.state != PromiseState::Pending => {
                (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None }))
            },
            Some(t) => {
                let u = spec_acquire(t, pid@, ttl, now);
                let obj = ObjV { task: Some(u), ..obj };
                (
                    spec_with_origin(doc, map.insert(id@, obj)),
                    Response::TaskClaim(TaskClaimRes {
                        status: 200,
                        task: Some(spec_task_record(id, u)),
                        promise: Some(spec_record(id, obj.promise)),
                    }),
                )
            },
        }
    }
}

pub open spec fn spec_unlease(t: TkV, state: TaskState, retry: Option<u64>) -> TkV {
    TkV { state, pid: None, ttl: None, lease_timeout_at: None, retry_timeout_at: retry, ..t }
}

pub open spec fn spec_task_release(doc: DocV, id: String, version: u64, now: Time) -> (DocV, Response) {
    let (map, held) = spec_held(spec_origin_map(doc), id@, version, now);
    match held {
        Held::Missing => (spec_with_origin(doc, map), Response::Status(StatusRes { status: 404 })),
        Held::Stale => (spec_with_origin(doc, map), Response::Status(StatusRes { status: 409 })),
        Held::Ok(obj) => {
            let task = match obj.task { Some(t) => Some(spec_unlease(t, TaskState::Pending, Some(now))), None => None };
            (spec_with_origin(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 200 }))
        },
    }
}

pub open spec fn spec_task_fulfill(doc: DocV, id: String, version: u64, action: PromiseSettleReq, now: Time) -> (DocV, Response) {
    if !action.state.spec_settable() {
        (doc, spec_promise_res(400, None))
    } else {
        let (map, held) = spec_held(spec_origin_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_origin(doc, map), spec_promise_res(404, None)),
            Held::Stale => (spec_with_origin(doc, map), spec_promise_res(409, None)),
            Held::Ok(obj) => {
                let promise = PromV { state: action.state, value: action.value, settled_at: Some(now), ..obj.promise };
                let task = match obj.task { Some(t) if t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)), other => other };
                let obj = ObjV { promise, task };
                (spec_with_origin(doc, map.insert(id@, obj)), spec_promise_res(200, Some(spec_record(id, obj.promise))))
            },
        }
    }
}

pub open spec fn spec_task_halt(doc: DocV, id: String, now: Time) -> (DocV, Response) {
    let doc = spec_opened(doc);
    let map = spec_origin_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::Status(StatusRes { status: 404 }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::Status(StatusRes { status: 404 })),
            Some(t) if t.state == TaskState::Fulfilled => (doc, Response::Status(StatusRes { status: 409 })),
            Some(t) if t.state == TaskState::Halted => (doc, Response::Status(StatusRes { status: 200 })),
            Some(t) => {
                let obj = ObjV { task: Some(spec_unlease(t, TaskState::Halted, None)), ..obj };
                (spec_with_origin(doc, map.insert(id@, obj)), Response::Status(StatusRes { status: 200 }))
            },
        }
    }
}

pub open spec fn spec_task_continue(doc: DocV, id: String, now: Time) -> (DocV, Response) {
    let doc = spec_opened(doc);
    let map = spec_origin_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::Status(StatusRes { status: 404 }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::Status(StatusRes { status: 404 })),
            Some(t) if t.state != TaskState::Halted || obj.promise.state != PromiseState::Pending => {
                (doc, Response::Status(StatusRes { status: 409 }))
            },
            Some(t) => {
                let obj = ObjV { task: Some(TkV { state: TaskState::Pending, retry_timeout_at: Some(now), ..t }), ..obj };
                (spec_with_origin(doc, map.insert(id@, obj)), Response::Status(StatusRes { status: 200 }))
            },
        }
    }
}

pub open spec fn spec_heartbeat(doc: DocV, pid: String, tasks: Seq<TaskRef>, now: Time) -> (DocV, Response) {
    if tasks.len() == 0 {
        (doc, Response::Status(StatusRes { status: 200 }))
    } else if !spec_one_origin(tasks, origin(tasks[0].id@), 0) {
        (doc, Response::Status(StatusRes { status: 400 }))
    } else {
        (spec_with_origin(doc, spec_extend(spec_origin_map(doc), pid@, tasks, now, 0)), Response::Status(StatusRes { status: 200 }))
    }
}

pub open spec fn spec_one_origin(tasks: Seq<TaskRef>, origin_chars: Seq<char>, i: int) -> bool
    decreases tasks.len() - i,
{
    if i < 0 || i >= tasks.len() { true }
    else { origin(tasks[i].id@) == origin_chars && spec_one_origin(tasks, origin_chars, i + 1) }
}

pub open spec fn spec_extend(map: Map<Seq<char>, ObjV>, pid: Seq<char>, tasks: Seq<TaskRef>, now: Time, i: int) -> Map<Seq<char>, ObjV>
    decreases tasks.len() - i,
{
    if i < 0 || i >= tasks.len() {
        map
    } else if !map.contains_key(tasks[i].id@) {
        spec_extend(map, pid, tasks, now, i + 1)
    } else {
        let obj = spec_project_obj(map[tasks[i].id@], now);
        match obj.task {
            Some(t) if t.state == TaskState::Acquired && t.version == tasks[i].version && t.pid == Some(pid) => {
                let ttl = match t.ttl { Some(n) => n, None => 0 };
                let at = spec_sat_add(now, ttl);
                let obj = ObjV { task: Some(TkV { lease_timeout_at: Some(at), ..t }), ..obj };
                spec_extend(map.insert(tasks[i].id@, obj), pid, tasks, now, i + 1)
            },
            _ => spec_extend(map, pid, tasks, now, i + 1),
        }
    }
}

pub open spec fn spec_suspend(doc: DocV, id: String, version: u64, actions: Seq<PromiseRegisterCallbackReq>, now: Time) -> (DocV, Response) {
    if actions.len() == 0 || spec_bad_suspend(actions, id@, 0) || !spec_distinct_awaited(actions, 0) {
        (doc, Response::Status(StatusRes { status: 400 }))
    } else {
        let (map, held) = spec_held(spec_origin_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_origin(doc, map), Response::Status(StatusRes { status: 404 })),
            Held::Stale => (spec_with_origin(doc, map), Response::Status(StatusRes { status: 409 })),
            Held::Ok(obj) => {
                if spec_missing_awaited(map, actions, 0) || spec_unawaitable(map, actions, 0) {
                    (spec_with_origin(doc, map), Response::Status(StatusRes { status: 422 }))
                } else if spec_any_settled(map, actions, now, 0) {
                    let task = match obj.task { Some(t) => Some(TkV { resumes: Seq::empty(), ..t }), None => None };
                    (spec_with_origin(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 300 }))
                } else {
                    let map = spec_add_callbacks(map, id@, actions, 0);
                    let obj = map[id@];
                    let task = match obj.task {
                        Some(t) => Some(TkV { resumes: Seq::empty(), ..spec_unlease(t, TaskState::Suspended, None) }),
                        None => None,
                    };
                    (spec_with_origin(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 200 }))
                }
            },
        }
    }
}

pub open spec fn spec_bad_suspend(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else { actions[i].awaited@ == id || !same_origin_spec(actions[i].awaited@, id) || spec_bad_suspend(actions, id, i + 1) }
}

pub open spec fn spec_distinct_awaited(actions: Seq<PromiseRegisterCallbackReq>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { true }
    else { !spec_seen(actions, actions[i].awaited@, 0, i) && spec_distinct_awaited(actions, i + 1) }
}

pub open spec fn spec_seen(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, j: int, stop: int) -> bool
    decreases stop - j,
{
    if j < 0 || j >= stop || j >= actions.len() { false }
    else { actions[j].awaited@ == id || spec_seen(actions, id, j + 1, stop) }
}

pub open spec fn spec_missing_awaited(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else { !map.contains_key(actions[i].awaited@) || spec_missing_awaited(map, actions, i + 1) }
}

pub open spec fn spec_unawaitable(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else {
        (map.contains_key(actions[i].awaited@) && !spec_awaitable(map[actions[i].awaited@].promise.tags))
            || spec_unawaitable(map, actions, i + 1)
    }
}

pub open spec fn spec_any_settled(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, now: Time, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else {
        (map.contains_key(actions[i].awaited@) && spec_project_obj(map[actions[i].awaited@], now).promise.state != PromiseState::Pending)
            || spec_any_settled(map, actions, now, i + 1)
    }
}

pub open spec fn spec_add_callbacks(map: Map<Seq<char>, ObjV>, id: Seq<char>, actions: Seq<PromiseRegisterCallbackReq>, i: int) -> Map<Seq<char>, ObjV>
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { map }
    else if !map.contains_key(actions[i].awaited@) {
        spec_add_callbacks(map, id, actions, i + 1)
    } else {
        let obj = map[actions[i].awaited@];
        let callbacks = if obj.promise.callbacks.contains(id) { obj.promise.callbacks } else { obj.promise.callbacks.push(id) };
        let obj = ObjV { promise: PromV { callbacks, ..obj.promise }, ..obj };
        spec_add_callbacks(map.insert(actions[i].awaited@, obj), id, actions, i + 1)
    }
}

pub open spec fn spec_fence(doc: DocV, id: String, version: u64, action: TaskFenceAction, now: Time) -> (DocV, Response) {
    let target = match action {
        TaskFenceAction::Create(c) => c.id,
        TaskFenceAction::Settle(st) => st.id,
    };
    if target@ == id@ || !same_origin_spec(target@, id@) {
        (doc, Response::TaskFence(TaskFenceRes { status: 400, action: None }))
    } else {
        let (map, held) = spec_held(spec_origin_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_origin(doc, map), Response::TaskFence(TaskFenceRes { status: 404, action: None })),
            Held::Stale => (spec_with_origin(doc, map), Response::TaskFence(TaskFenceRes { status: 409, action: None })),
            Held::Ok(_) => {
                let doc = spec_with_origin(doc, map);
                match action {
                    TaskFenceAction::Create(req) => {
                        let (doc, response) = spec_promise_create(doc, req, now);
                        let inner = match response { Response::Promise(p) => p, _ => PromiseRes { status: 500, promise: None } };
                        (doc, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Create(inner)) }))
                    },
                    TaskFenceAction::Settle(req) => {
                        let (doc, response) = spec_promise_settle(doc, req, now);
                        let inner = match response { Response::Promise(p) => p, _ => PromiseRes { status: 500, promise: None } };
                        (doc, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Settle(inner)) }))
                    },
                }
            },
        }
    }
}

pub open spec fn spec_fence_check(doc: DocV, id: String, version: u64, now: Time) -> (DocV, Response) {
    let (map, held) = spec_held(spec_origin_map(doc), id@, version, now);
    match held {
        Held::Missing => (spec_with_origin(doc, map), Response::Status(StatusRes { status: 404 })),
        Held::Stale => (spec_with_origin(doc, map), Response::Status(StatusRes { status: 409 })),
        Held::Ok(_) => (spec_with_origin(doc, map), Response::Status(StatusRes { status: 200 })),
    }
}

pub open spec fn spec_schedule_get(doc: DocV, id: String) -> (DocV, Response) {
    match doc {
        DocV::Schedule(Some(schedule)) if schedule.id == id => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
        _ => (doc, Response::Schedule(ScheduleRes { status: 404, schedule: None })),
    }
}

pub open spec fn spec_schedule_create(doc: DocV, req: ScheduleCreateReq, now: Time) -> (DocV, Response) {
    if spec_targeted(req.promise_tags) && spec_timer(req.promise_tags) {
        (doc, Response::Schedule(ScheduleRes { status: 400, schedule: None }))
    } else {
        match doc {
            DocV::Schedule(Some(schedule)) => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
            _ => {
                let schedule = Schedule {
                    id: req.id,
                    cron: req.cron,
                    promise_id: req.promise_id,
                    promise_timeout: req.promise_timeout,
                    promise_param: req.promise_param,
                    promise_tags: req.promise_tags,
                    next_run_at: echod_abstract::trusted::spec_next_cron(req.cron@, now),
                    last_run_at: None,
                    created_at: now,
                };
                (DocV::Schedule(Some(schedule)), Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) }))
            },
        }
    }
}

pub open spec fn spec_schedule_delete(doc: DocV, id: String) -> (DocV, Response) {
    match doc {
        DocV::Schedule(Some(schedule)) if schedule.id == id => (DocV::Schedule(None), Response::Status(StatusRes { status: 200 })),
        _ => (doc, Response::Status(StatusRes { status: 404 })),
    }
}

pub open spec fn spec_run_due(doc: DocV, now: Time) -> (DocV, Option<Response>, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocV::Schedule(Some(schedule)) if schedule.next_run_at <= now => {
            let at = schedule.next_run_at;
            let pending = PendingV {
                promise: echod_abstract::trusted::spec_expand(schedule.promise_id@, schedule.id@, at),
                at,
                timeout: schedule.promise_timeout,
                param: schedule.promise_param,
                tags: schedule.promise_tags,
            };
            let schedule = Schedule {
                last_run_at: Some(at),
                next_run_at: echod_abstract::trusted::spec_next_cron(schedule.cron@, at),
                ..schedule
            };
            (DocV::Schedule(Some(schedule)), None, seq![pending], Seq::empty())
        },
        DocV::Origin(map) => {
            match spec_due_id(map, spec_sorted_present(map), now) {
                Some(id) => {
                    let (map, notes) = spec_step_object(map, id, now);
                    (DocV::Origin(map), None, Seq::empty(), notes)
                },
                None => (doc, None, Seq::empty(), Seq::empty()),
            }
        },
        other => (other, None, Seq::empty(), Seq::empty()),
    }
}

pub open spec fn spec_occurrence(doc: DocV, pending: PendingV, now: Time) -> DocV {
    let doc = spec_opened(doc);
    let map = spec_origin_map(doc);
    if map.contains_key(pending.promise) || now < pending.at {
        doc
    } else {
        let timeout_at = spec_sat_add(pending.at, pending.timeout);
        let born = spec_new_obj(timeout_at, now, pending.param, pending.tags, spec_targeted(pending.tags) && !spec_timer(pending.tags));
        let obj = if timeout_at > pending.at {
            ObjV { promise: PromV { created_at: pending.at, ..born.promise }, ..born }
        } else {
            born
        };
        spec_with_origin(doc, map.insert(pending.promise, obj))
    }
}

pub open spec fn spec_due_id(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, now: Time) -> Option<Seq<char>>
    decreases keys.len(),
{
    if keys.len() == 0 { None }
    else if spec_obj_due(map[keys[0]], now) is Some { Some(keys[0]) }
    else { spec_due_id(map, keys.drop_first(), now) }
}

pub open spec fn spec_sorted_present(map: Map<Seq<char>, ObjV>) -> Seq<Seq<char>> {
    spec_sorted(map.dom())
}

pub open spec fn spec_min_key(keys: Set<Seq<char>>) -> Seq<char> {
    choose|k: Seq<char>| keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k)
}

pub open spec fn spec_sorted(keys: Set<Seq<char>>) -> Seq<Seq<char>>
    decreases keys.len(),
{
    if !keys.finite() || keys.len() == 0 { Seq::empty() }
    else {
        let k = spec_min_key(keys);
        seq![k] + spec_sorted(keys.remove(k))
    }
}

pub open spec fn spec_earlier(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    match (a, b) {
        (None, other) => other,
        (other, None) => other,
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    }
}

pub open spec fn spec_promise_due(obj: ObjV, now: Time) -> Option<u64> {
    if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
        Some(obj.promise.timeout_at)
    } else if obj.promise.state != PromiseState::Pending
        && (obj.promise.callbacks.len() > 0 || obj.promise.listeners.len() > 0)
    {
        let at = match obj.promise.settled_at { Some(t) => t, None => 0 };
        if at <= now { Some(at) } else { None }
    } else {
        None
    }
}

pub open spec fn spec_lease_due(obj: ObjV, now: Time) -> Option<u64> {
    match obj.task {
        Some(t) if obj.promise.state == PromiseState::Pending && t.state == TaskState::Acquired => match t.lease_timeout_at {
            Some(at) if at <= now => Some(at),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn spec_retry_due(obj: ObjV, now: Time) -> Option<u64> {
    match obj.task {
        Some(t) if obj.promise.state == PromiseState::Pending && t.state == TaskState::Pending => match t.retry_timeout_at {
            Some(at) if at <= now => Some(at),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn spec_obj_due(obj: ObjV, now: Time) -> Option<u64> {
    spec_earlier(spec_earlier(spec_promise_due(obj, now), spec_lease_due(obj, now)), spec_retry_due(obj, now))
}

pub open spec fn spec_step_object(map: Map<Seq<char>, ObjV>, id: Seq<char>, now: Time) -> (Map<Seq<char>, ObjV>, Seq<NoteV>) {
    if !map.contains_key(id) {
        (map, Seq::empty())
    } else {
        let obj = map[id];
        if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
            (map.insert(id, spec_project_obj(obj, now)), Seq::empty())
        } else if obj.promise.state == PromiseState::Pending {
            match obj.task {
                Some(t) if t.state == TaskState::Acquired && match t.lease_timeout_at { Some(at) => at <= now, None => false } => {
                    let obj = ObjV { task: Some(spec_unlease(t, TaskState::Pending, Some(now))), ..obj };
                    (map.insert(id, obj), Seq::empty())
                },
                Some(t) if t.state == TaskState::Pending && match t.retry_timeout_at { Some(at) => at <= now, None => false } => {
                    let obj = ObjV { task: Some(TkV { retry_timeout_at: Some(spec_sat_add(now, 5000)), ..t }), ..obj };
                    (map.insert(id, obj), seq![NoteV::Execute { id, version: t.version }])
                },
                _ => (map, Seq::empty()),
            }
        } else if obj.promise.callbacks.len() > 0 {
            let awaiter = obj.promise.callbacks[0];
            let obj = ObjV { promise: PromV { callbacks: obj.promise.callbacks.skip(1), ..obj.promise }, ..obj };
            let map = map.insert(id, obj);
            (spec_resume(map, awaiter, id, now), Seq::empty())
        } else if obj.promise.listeners.len() > 0 {
            let address = obj.promise.listeners[0];
            let promise = spec_record(spec_string(id), obj.promise);
            let obj = ObjV { promise: PromV { listeners: obj.promise.listeners.skip(1), ..obj.promise }, ..obj };
            (map.insert(id, obj), seq![NoteV::Unblock { address, promise }])
        } else {
            (map, Seq::empty())
        }
    }
}

pub open spec fn spec_resume(map: Map<Seq<char>, ObjV>, awaiter: Seq<char>, awaited: Seq<char>, now: Time) -> Map<Seq<char>, ObjV> {
    if !map.contains_key(awaiter) {
        map
    } else {
        match map[awaiter].task {
            None => map,
            Some(t) => {
                let t = match t.state {
                    TaskState::Suspended => TkV {
                        state: TaskState::Pending,
                        pid: None,
                        ttl: None,
                        lease_timeout_at: None,
                        retry_timeout_at: Some(now),
                        resumes: seq![awaited],
                        ..t
                    },
                    TaskState::Fulfilled => t,
                    _ => if t.resumes.contains(awaited) { t } else { TkV { resumes: t.resumes.push(awaited), ..t } },
                };
                map.insert(awaiter, ObjV { task: Some(t), ..map[awaiter] })
            },
        }
    }
}

pub open spec fn spec_wake(plane: PlaneV) -> Option<nat> {
    if plane.flight is Some { None } else { spec_next(plane) }
}

pub open spec fn spec_next(plane: PlaneV) -> Option<nat> {
    let from_pending = if plane.pending.len() == 0 { None } else { Some(plane.pending[0].at as nat) };
    spec_min_nat(from_pending, spec_deadlines(plane, plane.documents, 0))
}

pub open spec fn spec_min_nat(a: Option<nat>, b: Option<nat>) -> Option<nat> {
    match (a, b) {
        (None, other) => other,
        (other, None) => other,
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    }
}

pub open spec fn spec_deadlines(plane: PlaneV, docs: Seq<CachedV>, i: int) -> Option<nat>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() {
        None
    } else if !spec_owns(plane, docs[i].key) {
        spec_deadlines(plane, docs, i + 1)
    } else {
        spec_min_nat(spec_doc_deadline(spec_read(docs[i].key, docs[i].body)), spec_deadlines(plane, docs, i + 1))
    }
}

pub open spec fn spec_doc_deadline(doc: DocV) -> Option<nat> {
    match doc {
        DocV::Schedule(Some(schedule)) => Some(schedule.next_run_at as nat),
        DocV::Origin(map) => spec_map_deadline(map, spec_sorted(map.dom())),
        DocV::Schedule(None) => None,
    }
}

pub open spec fn spec_map_deadline(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>) -> Option<nat>
    decreases keys.len(),
{
    if keys.len() == 0 { None }
    else { spec_min_nat(spec_obj_deadline(map[keys[0]]), spec_map_deadline(map, keys.drop_first())) }
}

pub open spec fn spec_obj_deadline(obj: ObjV) -> Option<nat> {
    match spec_obj_due(obj, u64::MAX) {
        Some(at) => Some(at as nat),
        None => None,
    }
}

pub open spec fn spec_earliest_key(plane: PlaneV, now: Time) -> Option<Seq<char>> {
    spec_earliest_from(plane, plane.documents, 0, now, None)
}

pub open spec fn spec_earliest_from(plane: PlaneV, docs: Seq<CachedV>, i: int, now: Time, best: Option<(u64, Seq<char>)>) -> Option<Seq<char>>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() {
        match best { Some((_, key)) => Some(key), None => None }
    } else if !spec_owns(plane, docs[i].key) {
        spec_earliest_from(plane, docs, i + 1, now, best)
    } else {
        match spec_earliest_in(spec_read(docs[i].key, docs[i].body), now) {
            Some(at) => {
                let better = match best { None => true, Some((b, _)) => at < b };
                let best = if better { Some((at, docs[i].key)) } else { best };
                spec_earliest_from(plane, docs, i + 1, now, best)
            },
            None => spec_earliest_from(plane, docs, i + 1, now, best),
        }
    }
}

pub open spec fn spec_earliest_in(doc: DocV, now: Time) -> Option<u64> {
    match doc {
        DocV::Schedule(Some(schedule)) if schedule.next_run_at <= now => Some(schedule.next_run_at),
        DocV::Origin(map) => spec_map_due(map, spec_sorted(map.dom()), now),
        _ => None,
    }
}

pub open spec fn spec_map_due(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, now: Time) -> Option<u64>
    decreases keys.len(),
{
    if keys.len() == 0 { None }
    else { spec_earlier(spec_obj_due(map[keys[0]], now), spec_map_due(map, keys.drop_first(), now)) }
}

}
