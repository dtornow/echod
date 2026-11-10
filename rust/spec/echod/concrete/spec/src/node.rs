//! Mathematical concrete document and node specification.
//!
//! Executable document types and handlers live in `echod-process::concrete`.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

use vstd::prelude::*;

use echod_types::{
    PromiseCreateReq, PromiseRecord, PromiseRegisterCallbackReq,
    PromiseRes, PromiseSettleReq, PromiseState, Request, Response, Schedule, ScheduleCreateReq,
    ScheduleRes, StatusRes, Tags, TaskClaimRes, TaskFenceAction, TaskFenceInnerRes, TaskFenceRes,
    TaskGetRes, TaskRecord, TaskRef, TaskState, Value,
};
use crate::model::LogicV;

#[cfg(verus_keep_ghost)]
use echod_types::{origin, same_origin_spec, AValue};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::Call;
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::{Time, ProcessEvent};
#[cfg(verus_keep_ghost)]
use crate::model::{
    spec_bytes, spec_get, spec_notes, spec_reply, spec_string, Fleet, LocalV, Message, Pid,
};
#[cfg(verus_keep_ghost)]
use crate::store::{spec_before, spec_fnv, spec_sat_add, spec_starts, Etag, Read, StoreCall, StoreError, StoreOutcome};

verus! {

// ---------------------------------------------------------------------------
// The view types
// ---------------------------------------------------------------------------

/// One occurrence the node still owes.
pub struct PendingV {
    pub promise: Seq<char>,
    pub at: u64,
    pub timeout: u64,
    pub param: Value,
    pub tags: Tags,
}

/// A dispatch the flight will send when its write lands.
pub enum NoteV {
    Execute { id: Seq<char>, version: u64 },
    Unblock { address: Seq<char>, promise: PromiseRecord },
}

/// What the open flight is doing.
pub enum JobV {
    External(Request),
    Due,
    Occurrence(PendingV),
}

/// The open flight. A proof reads this instead of the private exec fields.
pub struct FlightV {
    pub op: u64,
    pub key: Seq<char>,
    pub writing: bool,
    pub etag: Option<Seq<char>>,
    pub now: u64,
    pub caller: Option<(Seq<char>, u64)>,
    pub job: JobV,
    pub born: Seq<PendingV>,
    pub reply: Option<(Seq<char>, u64, Response)>,
    pub notify: Seq<NoteV>,
    /// `encode` of the document a write is putting.
    pub decided: Option<Seq<u8>>,
}

/// One cached document: the bytes `encode` would write, and the etag the
/// next conditional write must match. `None` is a document that was loaded
/// as absent and then remembered without a version.
pub struct CachedV {
    pub key: Seq<char>,
    pub body: Seq<u8>,
    pub etag: Option<Seq<char>>,
}

/// A node, as a proof sees it.
pub struct NodeV {
    pub logic: LogicV,
    pub wake: Option<nat>,
    pub next_request: u64,
    pub address: nat,
    pub nodes: nat,
    pub retry_timeout: u64,
    pub flight: Option<FlightV>,
    pub documents: Seq<CachedV>,
    pub pending: Seq<PendingV>,
    pub next_op: u64,
}

// ---------------------------------------------------------------------------
// The node, as a specification. `spec_request`, `spec_timeout`, and
// `spec_store_reply` are the arms of `Node::on_event`; the handlers are the
// step on a document. `spec_decode_raw` and `spec_encode` are the JSON codec of
// a document, the same kind of trusted boundary as the cron engine.
// ---------------------------------------------------------------------------

/// JSON of a document. `encode` / `decode` in the node are this. A body that
/// does not parse is the empty document for that key, the same fallback as
/// `decode`.
pub uninterp spec fn spec_decode_raw(body: Seq<u8>) -> Option<DocV>;

pub uninterp spec fn spec_encode(doc: DocV) -> Seq<u8>;

/// The codec round-trips: what `encode` wrote, `decode` reads back.
pub axiom fn axiom_decode_encode(doc: DocV)
    ensures
        spec_decode_raw(spec_encode(doc)) == Some(doc),
;

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

pub open spec fn spec_empty_value() -> Value {
    Value::spec_empty()
}

pub open spec fn spec_owns(node: NodeV, key: Seq<char>) -> bool {
    node.nodes != 0 && spec_fnv(key) % (node.nodes as u64) == (node.address as u64)
}

pub open spec fn spec_cached(node: NodeV, key: Seq<char>) -> Option<CachedV> {
    spec_cached_from(node.documents, key, 0)
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

pub open spec fn spec_request(node: NodeV, now: Time, call: Call) -> (NodeV, Seq<(Pid, Message)>) {
    match spec_key(call.request) {
        None => (node, seq![spec_reply(call.client@, call.id, spec_pure(call.request))]),
        Some(key) => {
            if !spec_owns(node, key) {
                (node, seq![spec_reply(call.client@, call.id, spec_unavailable(call.request))])
            } else {
                spec_begin(node, key, JobV::External(call.request), now, Some((call.client@, call.id)))
            }
        },
    }
}

pub open spec fn spec_timeout(node: NodeV, now: Time) -> (NodeV, Seq<(Pid, Message)>) {
    if node.flight is Some {
        (node, Seq::empty())
    } else if node.pending.len() > 0 {
        let pending = node.pending[0];
        let node = NodeV { pending: node.pending.skip(1), ..node };
        let key = spec_origin_key(origin(pending.promise));
        if !spec_owns(node, key) {
            (node, Seq::empty())
        } else {
            spec_begin(node, key, JobV::Occurrence(pending), now, None)
        }
    } else {
        match spec_earliest_key(node, now) {
            Some(key) => spec_begin(node, key, JobV::Due, now, None),
            None => (node, Seq::empty()),
        }
    }
}

pub open spec fn spec_store_reply(node: NodeV, op: u64, outcome: StoreOutcome) -> (NodeV, Seq<(Pid, Message)>) {
    match node.flight {
        None => (node, Seq::empty()),
        Some(flight) => {
            if flight.op != op {
                (node, Seq::empty())
            } else if !flight.writing {
                match outcome {
                    StoreOutcome::Got(got) => {
                        let (doc, etag) = match got {
                            Some((body, tag)) => (spec_read(flight.key, body@), Some(tag.0@)),
                            None => (spec_empty_doc(flight.key), None),
                        };
                        let flight = FlightV { etag, ..flight };
                        spec_decide(NodeV { flight: None, ..node }, flight, doc)
                    },
                    StoreOutcome::Failed(_) => spec_fail(NodeV { flight: None, ..node }, flight),
                    _ => (node, Seq::empty()),
                }
            } else {
                match outcome {
                    StoreOutcome::Written(tag) => spec_commit(node, flight, tag),
                    StoreOutcome::Failed(_) => spec_fail(NodeV { flight: None, ..node }, flight),
                    _ => (node, Seq::empty()),
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

pub open spec fn spec_begin(node: NodeV, key: Seq<char>, job: JobV, now: Time, caller: Option<(Seq<char>, u64)>) -> (NodeV, Seq<(Pid, Message)>) {
    match spec_cached(node, key) {
        Some(cached) => spec_decide(node, spec_flight(0, key, cached.etag, now, caller, job), spec_read(key, cached.body)),
        None => {
            let op = node.next_op;
            let flight = spec_flight(op, key, None, now, caller, job);
            (NodeV { flight: Some(flight), next_op: (op + 1) as u64, ..node }, seq![spec_get(op, key)])
        },
    }
}

pub open spec fn spec_decide(node: NodeV, flight: FlightV, doc: DocV) -> (NodeV, Seq<(Pid, Message)>) {
    let (next, reply, born, notify) = match flight.job {
        JobV::External(request) => {
            let (next, response) = spec_handle(doc, request, flight.now);
            (next, Some(response), Seq::empty(), Seq::empty())
        },
        JobV::Due => spec_run_due(doc, flight.now, node.retry_timeout),
        JobV::Occurrence(pending) => (spec_occurrence(doc, pending, flight.now), None, Seq::empty(), Seq::empty()),
    };
    let reply = match (flight.caller, reply) {
        (Some((client, id)), Some(response)) => Some((client, id, response)),
        _ => None,
    };
    let previous = match spec_cached(node, flight.key) {
        Some(cached) => spec_read(flight.key, cached.body),
        None => spec_empty_doc(flight.key),
    };
    if next == previous && born.len() == 0 {
        let node = NodeV {
            flight: None,
            documents: spec_keep(node.documents, flight.key, next, flight.etag),
            ..node
        };
        let send = match reply {
            Some((client, id, response)) => seq![spec_reply(client, id, response)],
            None => Seq::empty(),
        };
        (node, send + spec_notes(notify))
    } else {
        let op = node.next_op;
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
        (NodeV { flight: Some(flight), next_op: (op + 1) as u64, ..node }, seq![(Pid::Store, Message::StoreReq { op, call })])
    }
}

pub open spec fn spec_commit(node: NodeV, flight: FlightV, tag: Etag) -> (NodeV, Seq<(Pid, Message)>) {
    let documents = match flight.decided {
        Some(body) => spec_remember(node.documents, flight.key, body, Some(tag.0@), 0),
        None => node.documents,
    };
    let node = NodeV {
        flight: None,
        documents,
        pending: node.pending + flight.born,
        ..node
    };
    let send = match flight.reply {
        Some((client, id, response)) => seq![spec_reply(client, id, response)],
        None => Seq::empty(),
    };
    (node, send + spec_notes(flight.notify))
}

pub open spec fn spec_fail(node: NodeV, flight: FlightV) -> (NodeV, Seq<(Pid, Message)>) {
    match (flight.job, flight.caller) {
        (JobV::External(request), Some((client, id))) => {
            (node, seq![spec_reply(client, id, spec_unavailable(request))])
        },
        _ => (node, Seq::empty()),
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
                    next_run_at: echod_abstract_spec::trusted::spec_next_cron(req.cron@, now),
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

pub open spec fn spec_run_due(doc: DocV, now: Time, retry_timeout: u64) -> (DocV, Option<Response>, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocV::Schedule(Some(schedule)) if schedule.next_run_at <= now => {
            let at = schedule.next_run_at;
            let pending = PendingV {
                promise: echod_abstract_spec::trusted::spec_expand(schedule.promise_id@, schedule.id@, at),
                at,
                timeout: schedule.promise_timeout,
                param: schedule.promise_param,
                tags: schedule.promise_tags,
            };
            let schedule = Schedule {
                last_run_at: Some(at),
                next_run_at: echod_abstract_spec::trusted::spec_next_cron(schedule.cron@, at),
                ..schedule
            };
            (DocV::Schedule(Some(schedule)), None, seq![pending], Seq::empty())
        },
        DocV::Origin(map) => {
            match spec_due_id(map, spec_sorted_present(map), now) {
                Some(id) => {
                    let (map, notes) = spec_step_object(map, id, now, retry_timeout);
                    (DocV::Origin(map), None, Seq::empty(), notes)
                },
                None => (doc, None, Seq::empty(), Seq::empty()),
            }
        },
        other => (other, None, Seq::empty(), Seq::empty()),
    }
}

/// `spec_run_due` iterated: it stops at a step that leaves the document as it
/// was, or after `limit` steps. The occurrences queued and the notes, in order.
pub open spec fn spec_sweep(doc: DocV, now: Time, retry_timeout: u64, limit: nat) -> (DocV, Seq<PendingV>, Seq<NoteV>)
    decreases limit,
{
    if limit == 0 {
        (doc, Seq::empty(), Seq::empty())
    } else {
        let (next, _, born, notes) = spec_run_due(doc, now, retry_timeout);
        if next == doc {
            (doc, Seq::empty(), Seq::empty())
        } else {
            let (last, more_born, more_notes) = spec_sweep(next, now, retry_timeout, (limit - 1) as nat);
            (last, born + more_born, notes + more_notes)
        }
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
        let promise = if timeout_at > pending.at {
            PromV { created_at: pending.at, ..born.promise }
        } else {
            born.promise
        };
        let task = match born.task {
            Some(t) if t.state == TaskState::Pending => Some(TkV { retry_timeout_at: Some(spec_offer_at(pending.tags, pending.at)), ..t }),
            other => other,
        };
        spec_with_origin(doc, map.insert(pending.promise, ObjV { promise, task }))
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

/// Opaque: the choice is read through `timers::lemma_min_key` alone.
#[verifier::opaque]
pub open spec fn spec_min_key(keys: Set<Seq<char>>) -> Seq<char> {
    choose|k: Seq<char>| keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k)
}

pub open spec fn spec_sorted(keys: Set<Seq<char>>) -> Seq<Seq<char>>
    decreases keys.len(),
    via spec_sorted_decreases
{
    if !keys.finite() || keys.len() == 0 { Seq::empty() }
    else {
        let k = spec_min_key(keys);
        seq![k] + spec_sorted(keys.remove(k))
    }
}

#[via_fn]
proof fn spec_sorted_decreases(keys: Set<Seq<char>>) {
    if keys.finite() && keys.len() > 0 {
        crate::timers::lemma_min_key(keys);
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

pub open spec fn spec_step_object(map: Map<Seq<char>, ObjV>, id: Seq<char>, now: Time, retry_timeout: u64) -> (Map<Seq<char>, ObjV>, Seq<NoteV>) {
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
                    let obj = ObjV { task: Some(TkV { retry_timeout_at: Some(spec_sat_add(now, retry_timeout)), ..t }), ..obj };
                    (map.insert(id, obj), seq![NoteV::Execute { id, version: t.version }])
                },
                _ => (map, Seq::empty()),
            }
        } else if obj.promise.callbacks.len() > 0 {
            let awaiter = obj.promise.callbacks[0];
            let since = match obj.promise.settled_at { Some(t) => t, None => 0 };
            let obj = ObjV { promise: PromV { callbacks: obj.promise.callbacks.skip(1), ..obj.promise }, ..obj };
            let map = map.insert(id, obj);
            (spec_resume(map, awaiter, id, since, now), Seq::empty())
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

/// `resume`: a suspended awaiter is offered again from `since`, the instant
/// the awaited promise settled. The awaiter is read through its projection
/// at `now`: a task whose own promise is settled reads as fulfilled.
pub open spec fn spec_resume(map: Map<Seq<char>, ObjV>, awaiter: Seq<char>, awaited: Seq<char>, since: Time, now: Time) -> Map<Seq<char>, ObjV> {
    if !map.contains_key(awaiter) {
        map
    } else {
        match spec_project_obj(map[awaiter], now).task {
            None => map,
            Some(t) => match t.state {
                TaskState::Suspended => map.insert(awaiter, ObjV {
                    task: Some(TkV {
                        state: TaskState::Pending,
                        pid: None,
                        ttl: None,
                        lease_timeout_at: None,
                        retry_timeout_at: Some(since),
                        resumes: seq![awaited],
                        ..t
                    }),
                    ..map[awaiter]
                }),
                TaskState::Fulfilled => map,
                _ => if t.resumes.contains(awaited) {
                    map
                } else {
                    map.insert(awaiter, ObjV { task: Some(TkV { resumes: t.resumes.push(awaited), ..t }), ..map[awaiter] })
                },
            },
        }
    }
}

pub open spec fn spec_wake(node: NodeV) -> Option<nat> {
    if node.flight is Some { None } else { spec_next(node) }
}

pub open spec fn spec_next(node: NodeV) -> Option<nat> {
    let from_pending = if node.pending.len() == 0 { None } else { Some(node.pending[0].at as nat) };
    spec_min_nat(from_pending, spec_deadlines(node, node.documents, 0))
}

pub open spec fn spec_min_nat(a: Option<nat>, b: Option<nat>) -> Option<nat> {
    match (a, b) {
        (None, other) => other,
        (other, None) => other,
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    }
}

pub open spec fn spec_deadlines(node: NodeV, docs: Seq<CachedV>, i: int) -> Option<nat>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() {
        None
    } else if !spec_owns(node, docs[i].key) {
        spec_deadlines(node, docs, i + 1)
    } else {
        spec_min_nat(spec_doc_deadline(spec_read(docs[i].key, docs[i].body)), spec_deadlines(node, docs, i + 1))
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

pub open spec fn spec_earliest_key(node: NodeV, now: Time) -> Option<Seq<char>> {
    spec_earliest_from(node, node.documents, 0, now, None)
}

pub open spec fn spec_earliest_from(node: NodeV, docs: Seq<CachedV>, i: int, now: Time, best: Option<(u64, Seq<char>)>) -> Option<Seq<char>>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() {
        match best { Some((_, key)) => Some(key), None => None }
    } else if !spec_owns(node, docs[i].key) {
        spec_earliest_from(node, docs, i + 1, now, best)
    } else {
        match spec_earliest_in(spec_read(docs[i].key, docs[i].body), now) {
            Some(at) => {
                let better = match best { None => true, Some((b, _)) => at < b };
                let best = if better { Some((at, docs[i].key)) } else { best };
                spec_earliest_from(node, docs, i + 1, now, best)
            },
            None => spec_earliest_from(node, docs, i + 1, now, best),
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
