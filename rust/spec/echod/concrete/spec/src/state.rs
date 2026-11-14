//! Mathematical concrete state and transitions: node, then store.
//!
//! Executable document types and handlers live in `echod-process::concrete`.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

use vstd::prelude::*;
use vstd::contrib::make_spec_type;

use echod_types::{
    MAX_TIME, MAX_VERSION, PromiseCreateReq, PromiseRecord, PromiseRegisterCallbackReq,
    PromiseRes, PromiseSettleReq, PromiseState, Request, Response, Schedule, ScheduleCreateReq,
    ScheduleRes, StatusRes, Tags, TaskClaimRes, TaskFenceAction, TaskFenceInnerRes, TaskFenceRes,
    TaskGetRes, TaskRecord, TaskRef, TaskState, Value,
};
use crate::rover::{LogicV, Pid};

#[cfg(verus_keep_ghost)]
use echod_types::{origin, same_origin_spec, spec_deadline_bounded, AValue};
#[cfg(verus_keep_ghost)]
use echod_types::Call;
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::{Time, ProcessEvent};
#[cfg(verus_keep_ghost)]
use crate::rover::{
    spec_bytes, spec_get, spec_notes, spec_reply, spec_string, Config, Proc, Message,
};


pub use crate::document::*;

// ---------------------------------------------------------------------------
// Node
// ---------------------------------------------------------------------------

verus! {


/// Request transitions drain their finite workflow to a fixed point.  The
/// executable representation is bounded by addressable memory; using the
/// full `u64` range avoids turning document size into a semantic cutoff.
pub const REQUEST_SWEEP_STEPS: u64 = u64::MAX;


pub open spec fn spec_stored_body(d: StoredDocumentV) -> DocumentBodyV {
    match d {
        StoredDocumentV::Workflow(doc) => DocumentBodyV::Workflow(doc.objects),
        StoredDocumentV::Schedule(doc) => DocumentBodyV::Schedule(doc.schedule),
    }
}


pub open spec fn spec_stored_version(d: StoredDocumentV) -> u64 {
    match d {
        StoredDocumentV::Workflow(doc) => doc.version,
        StoredDocumentV::Schedule(doc) => doc.version,
    }
}


pub open spec fn spec_stored_committed_at(d: StoredDocumentV) -> u64 {
    match d {
        StoredDocumentV::Workflow(doc) => doc.committed_at,
        StoredDocumentV::Schedule(doc) => doc.committed_at,
    }
}


pub open spec fn spec_stored_next_wake_at(d: StoredDocumentV) -> Option<u64> {
    match d {
        StoredDocumentV::Workflow(doc) => doc.next_wake_at,
        StoredDocumentV::Schedule(doc) => doc.next_wake_at,
    }
}


pub open spec fn spec_stored_name(d: StoredDocumentV) -> Seq<char> {
    match d {
        StoredDocumentV::Workflow(doc) => doc.document,
        StoredDocumentV::Schedule(doc) => doc.document,
    }
}


pub open spec fn spec_empty_stored_workflow(document: Seq<char>) -> StoredDocumentV {
    StoredDocumentV::Workflow(WorkflowDocumentV {
        document,
        version: 0,
        committed_at: 0,
        next_wake_at: None,
        objects: Map::empty(),
    })
}


pub open spec fn spec_empty_stored_schedule(document: Seq<char>) -> StoredDocumentV {
    StoredDocumentV::Schedule(ScheduleDocumentV {
        document,
        version: 0,
        committed_at: 0,
        next_wake_at: None,
        schedule: None,
    })
}


pub open spec fn spec_advance_stored(
    before: StoredDocumentV,
    body: DocumentBodyV,
    committed_at: u64,
) -> StoredDocumentV {
    let version = spec_stored_version(before).saturating_add(1);
    let next_wake_at = match spec_body_deadline(body) {
        Some(at) => Some(at as u64),
        None => None,
    };
    match body {
        DocumentBodyV::Workflow(objects) => StoredDocumentV::Workflow(WorkflowDocumentV {
            document: spec_stored_name(before),
            version,
            committed_at,
            next_wake_at,
            objects,
        }),
        DocumentBodyV::Schedule(schedule) => StoredDocumentV::Schedule(ScheduleDocumentV {
            document: spec_stored_name(before),
            version,
            committed_at,
            next_wake_at,
            schedule,
        }),
    }
}


/// How many rows a document holds: its objects, or its one schedule.
pub open spec fn spec_body_len(d: DocumentBodyV) -> nat {
    match d {
        DocumentBodyV::Workflow(m) => m.dom().len(),
        DocumentBodyV::Schedule(Some(_)) => 1,
        DocumentBodyV::Schedule(None) => 0,
    }
}


pub open spec fn nat_v(o: Option<u64>) -> Option<nat> {
    match o { Some(x) => Some(x as nat), None => None }
}


pub open spec fn spec_sent(reply: Option<(Seq<char>, u64, Response)>, notes: Seq<NoteV>) -> Seq<(Pid, Message)> {
    (match reply {
        Some((client, id, response)) => seq![spec_reply(client, id, response)],
        None => Seq::empty(),
    }) + spec_notes(notes)
}
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

/// Idempotency key of an outbound protocol effect.
pub enum NoteKeyV {
    Execute(Seq<char>),
    Unblock(Seq<char>, Seq<char>),
}

pub open spec fn spec_note_key(note: NoteV) -> NoteKeyV {
    match note {
        NoteV::Execute { id, .. } => NoteKeyV::Execute(id),
        NoteV::Unblock { address, promise } => NoteKeyV::Unblock(promise.id@, address),
    }
}

pub open spec fn spec_note_relevant(doc: DocumentBodyV, note: NoteV) -> bool {
    match note {
        NoteV::Execute { id, version } => {
            let objects = spec_workflow_map(doc);
            objects.contains_key(id)
                && match objects[id].task {
                    Some(task) => task.state == TaskState::Pending && task.version == version,
                    None => false,
                }
        },
        NoteV::Unblock { .. } => true,
    }
}

pub open spec fn spec_keyed_insert(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    note: NoteV,
) -> Seq<NoteV> {
    if !spec_note_relevant(doc, note) || exists|i: int| 0 <= i < notes.len()
        && spec_note_key(notes[i]) == spec_note_key(note)
    {
        notes
    } else {
        notes.push(note)
    }
}

pub open spec fn spec_keyed_notes(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        spec_keyed_insert(
            doc,
            spec_keyed_notes(doc, notes, (count - 1) as nat),
            notes[count as int - 1],
        )
    }
}

pub open spec fn spec_execute_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    committed_at: u64,
    keys: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_execute_notes(before, after, committed_at, keys, (count - 1) as nat);
        let id = keys[count as int - 1];
        if crate::document::offer_committed(before, after, id, committed_at) {
            prior.push(NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            })
        } else {
            prior
        }
    }
}

pub open spec fn spec_unblock_notes_for(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    promise: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            (count - 1) as nat,
        );
        let address = listeners[count as int - 1];
        if crate::document::listener_committed(before, after, promise, address) {
            prior.push(NoteV::Unblock {
                address,
                promise: spec_record(spec_string(promise), after[promise].promise),
            })
        } else {
            prior
        }
    }
}

pub open spec fn spec_unblock_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_unblock_notes(before, after, keys, (count - 1) as nat);
        let promise = keys[count as int - 1];
        prior + spec_unblock_notes_for(
            before,
            after,
            promise,
            before[promise].promise.listeners,
            before[promise].promise.listeners.len(),
        )
    }
}

/// Canonical imperative representation of the endpoint-derived effect set.
pub open spec fn spec_committed_notes(
    before: DocumentBodyV,
    after: DocumentBodyV,
    committed_at: u64,
) -> Seq<NoteV> {
    match (before, after) {
        (DocumentBodyV::Workflow(old), DocumentBodyV::Workflow(new)) => {
            let new_keys = spec_sorted_present(new);
            let old_keys = spec_sorted_present(old);
            spec_execute_notes(old, new, committed_at, new_keys, new_keys.len())
                + spec_unblock_notes(old, new, old_keys, old_keys.len())
        },
        _ => Seq::empty(),
    }
}

pub proof fn lemma_keyed_notes_from_input(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    count: nat,
    k: int,
)
    requires
        count <= notes.len(),
        0 <= k < spec_keyed_notes(doc, notes, count).len(),
    ensures
        exists|j: int| 0 <= j < count
            && spec_keyed_notes(doc, notes, count)[k] == notes[j],
    decreases count,
{
    if count > 0 {
        let prior = spec_keyed_notes(doc, notes, (count - 1) as nat);
        let note = notes[count as int - 1];
        if !spec_note_relevant(doc, note) || exists|i: int| 0 <= i < prior.len()
            && spec_note_key(prior[i]) == spec_note_key(note)
        {
            lemma_keyed_notes_from_input(doc, notes, (count - 1) as nat, k);
        } else if k < prior.len() {
            lemma_keyed_notes_from_input(doc, notes, (count - 1) as nat, k);
        } else {
            assert(k == prior.len());
        }
    }
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
// step on a document. `spec_decode_body_raw` and `spec_encode_body` are the JSON codec of
// a document, the same kind of trusted boundary as the cron engine.
// ---------------------------------------------------------------------------

/// JSON of a document. `encode` / `decode` in the node are this. A body that
/// does not parse is the empty document for that key, the same fallback as
/// `decode`.
pub uninterp spec fn spec_decode_body_raw(body: Seq<u8>) -> Option<DocumentBodyV>;

pub uninterp spec fn spec_encode_body(doc: DocumentBodyV) -> Seq<u8>;

/// The codec round-trips: what `encode` wrote, `decode` reads back.
pub axiom fn axiom_decode_encode_body(doc: DocumentBodyV)
    ensures
        spec_decode_body_raw(spec_encode_body(doc)) == Some(doc),
;

pub open spec fn spec_read(key: Seq<char>, body: Seq<u8>) -> DocumentBodyV {
    match spec_decode_body_raw(body) {
        Some(doc) => doc,
        None => spec_empty_body(key),
    }
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

pub open spec fn spec_body_is_empty(doc: DocumentBodyV) -> bool {
    match doc {
        DocumentBodyV::Workflow(map) => map.dom().len() == 0,
        DocumentBodyV::Schedule(slot) => slot is None,
    }
}

/// `remember`: an empty document with no etag leaves the cache.
pub open spec fn spec_keep(docs: Seq<CachedV>, key: Seq<char>, doc: DocumentBodyV, etag: Option<Seq<char>>) -> Seq<CachedV> {
    if spec_body_is_empty(doc) && etag is None {
        spec_forget(docs, key, 0)
    } else {
        spec_remember(docs, key, spec_encode_body(doc), etag, 0)
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

pub open spec fn spec_store_reply(node: NodeV, op: u64, response: StoreRes) -> (NodeV, Seq<(Pid, Message)>) {
    match node.flight {
        None => (node, Seq::empty()),
        Some(flight) => {
            if flight.op != op {
                (node, Seq::empty())
            } else if !flight.writing {
                match response {
                    StoreRes::Get { result: Ok(got) } => {
                        let (doc, etag) = match got {
                            Some((body, tag)) => (spec_read(flight.key, body@), Some(tag.0@)),
                            None => (spec_empty_body(flight.key), None),
                        };
                        let flight = FlightV { etag, ..flight };
                        spec_decide(NodeV { flight: None, ..node }, flight, doc)
                    },
                    StoreRes::Get { result: Err(_) } => spec_fail(NodeV { flight: None, ..node }, flight),
                    _ => (node, Seq::empty()),
                }
            } else {
                match response {
                    StoreRes::PutIfMatch { result: Ok(tag) }
                    | StoreRes::PutIfNoneMatch { result: Ok(tag) } =>
                        spec_commit(node, flight, tag),
                    StoreRes::PutIfMatch { result: Err(_) }
                    | StoreRes::PutIfNoneMatch { result: Err(_) } =>
                        spec_fail(NodeV { flight: None, ..node }, flight),
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

pub open spec fn spec_decide(node: NodeV, flight: FlightV, doc: DocumentBodyV) -> (NodeV, Seq<(Pid, Message)>) {
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
        None => spec_empty_body(flight.key),
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
        let body = spec_encode_body(next);
        let request = match flight.etag {
            Some(chars) => StoreReq::PutIfMatch {
                key: spec_string(flight.key),
                body: spec_bytes(body),
                etag: Etag(spec_string(chars)),
            },
            None => StoreReq::PutIfNoneMatch { key: spec_string(flight.key), body: spec_bytes(body) },
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
        (NodeV { flight: Some(flight), next_op: (op + 1) as u64, ..node }, seq![(Pid::Store, Message::StoreReq { op, request })])
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

pub open spec fn spec_empty_body(key: Seq<char>) -> DocumentBodyV {
    if spec_starts(key, seq!['s', '/']) { DocumentBodyV::Schedule(None) } else { DocumentBodyV::Workflow(Map::empty()) }
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

pub open spec fn spec_request_document(request: Request) -> Option<Seq<char>> {
    match request {
        Request::PromiseGet(q) => Some(origin(q.id@)),
        Request::PromiseCreate(q) => Some(origin(q.id@)),
        Request::PromiseSettle(q) => Some(origin(q.id@)),
        Request::PromiseRegisterCallback(q) => Some(origin(q.awaited@)),
        Request::PromiseRegisterListener(q) => Some(origin(q.awaited@)),
        Request::TaskGet(q) => Some(origin(q.id@)),
        Request::TaskCreate(q) => Some(origin(q.action.id@)),
        Request::TaskAcquire(q) => Some(origin(q.id@)),
        Request::TaskFulfill(q) => Some(origin(q.id@)),
        Request::TaskRelease(q) => Some(origin(q.id@)),
        Request::TaskHalt(q) => Some(origin(q.id@)),
        Request::TaskContinue(q) => Some(origin(q.id@)),
        Request::TaskFence(q) => Some(origin(q.id@)),
        Request::TaskFenceCheck(q) => Some(origin(q.id@)),
        Request::TaskSuspend(q) => Some(origin(q.id@)),
        Request::TaskHeartbeat(q) =>
            if q.tasks@.len() == 0 { None } else { Some(origin(q.tasks@[0].id@)) },
        Request::ScheduleGet(q) => Some(q.id@),
        Request::ScheduleCreate(q) => Some(q.id@),
        Request::ScheduleDelete(q) => Some(q.id@),
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
pub open spec fn spec_handle(doc: DocumentBodyV, request: Request, now: Time) -> (DocumentBodyV, Response) {
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

pub open spec fn spec_workflow_map(doc: DocumentBodyV) -> Map<Seq<char>, ObjV> {
    match doc {
        DocumentBodyV::Workflow(map) => map,
        DocumentBodyV::Schedule(_) => Map::empty(),
    }
}

/// `workflow_mut` replaces a schedule document with an empty origin map before it looks anything up.
pub open spec fn spec_opened(doc: DocumentBodyV) -> DocumentBodyV {
    DocumentBodyV::Workflow(spec_workflow_map(doc))
}

pub open spec fn spec_with_workflow(doc: DocumentBodyV, map: Map<Seq<char>, ObjV>) -> DocumentBodyV {
    match doc {
        DocumentBodyV::Schedule(_) => DocumentBodyV::Workflow(map),
        DocumentBodyV::Workflow(_) => DocumentBodyV::Workflow(map),
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

pub open spec fn spec_promise_get(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
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
            retry_timeout_at: if live { Some(now) } else { None },
            resumes: Seq::empty(),
        })
    } else {
        None
    };
    ObjV { promise, task }
}

pub open spec fn spec_promise_create(doc: DocumentBodyV, req: PromiseCreateReq, now: Time) -> (DocumentBodyV, Response) {
    if req.timeout_at > MAX_TIME || (spec_timer(req.tags) && spec_targeted(req.tags)) {
        (doc, spec_promise_res(400, None))
    } else {
        let map = spec_workflow_map(doc);
        if map.contains_key(req.id@) {
            let obj = spec_project_obj(map[req.id@], now);
            (doc, spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
        } else {
            let obj = spec_new_obj(req.timeout_at, now, req.param, req.tags, spec_targeted(req.tags));
            (spec_with_workflow(doc, map.insert(req.id@, obj)), spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
        }
    }
}

pub open spec fn spec_promise_settle(doc: DocumentBodyV, req: PromiseSettleReq, now: Time) -> (DocumentBodyV, Response) {
    if !req.state.spec_settable() {
        (doc, spec_promise_res(400, None))
    } else {
        let doc = spec_opened(doc);
        let map = spec_workflow_map(doc);
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
                (spec_with_workflow(doc, map.insert(req.id@, obj)), spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
            }
        }
    }
}

pub open spec fn spec_register_callback(doc: DocumentBodyV, awaited: String, awaiter: String, now: Time) -> (DocumentBodyV, Response) {
    if awaited@ == awaiter@ || !same_origin_spec(awaited@, awaiter@) {
        (doc, spec_promise_res(400, None))
    } else {
        let doc = spec_opened(doc);
        let map = spec_workflow_map(doc);
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
                    (spec_with_workflow(doc, map.insert(awaited@, awaited_obj)), res)
                } else {
                    (doc, res)
                }
            }
        }
    }
}

pub open spec fn spec_register_listener(doc: DocumentBodyV, awaited: String, address: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
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
                (spec_with_workflow(doc, map.insert(awaited@, obj)), res)
            } else {
                (doc, res)
            }
        }
    }
}

pub open spec fn spec_task_get(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
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

pub open spec fn spec_task_create(doc: DocumentBodyV, pid: String, ttl: u64, action: PromiseCreateReq, now: Time) -> (DocumentBodyV, Response) {
    if ttl == 0 || ttl > MAX_TIME || action.timeout_at > MAX_TIME
        || !spec_targeted(action.tags) || spec_timer(action.tags) {
        (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
    } else {
        let (doc, created) = spec_promise_create(doc, action, now);
        match created {
            Response::Promise(inner) if inner.status == 400 => {
                (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
            },
            _ => {
                let map = spec_workflow_map(doc);
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
                            Some(t) if t.state == TaskState::Pending && t.version >= MAX_VERSION => {
                                (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None }))
                            },
                            Some(t) if t.state == TaskState::Pending => {
                                let u = spec_acquire(t, pid@, ttl, now);
                                let obj = ObjV { task: Some(u), ..seen };
                                (
                                    spec_with_workflow(doc, map.insert(action.id@, obj)),
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

pub open spec fn spec_task_acquire(doc: DocumentBodyV, id: String, version: u64, pid: String, ttl: u64, now: Time) -> (DocumentBodyV, Response) {
    if ttl == 0 || ttl > MAX_TIME {
        (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
    } else {
        let doc = spec_opened(doc);
        let map = spec_workflow_map(doc);
        if !map.contains_key(id@) {
            (doc, Response::TaskClaim(TaskClaimRes { status: 404, task: None, promise: None }))
        } else {
            let obj = spec_project_obj(map[id@], now);
            match obj.task {
                None => (doc, Response::TaskClaim(TaskClaimRes { status: 404, task: None, promise: None })),
                Some(t) if t.state != TaskState::Pending || t.version != version
                    || obj.promise.state != PromiseState::Pending || t.version >= MAX_VERSION => {
                    (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None }))
                },
                Some(t) => {
                    let u = spec_acquire(t, pid@, ttl, now);
                    let obj = ObjV { task: Some(u), ..obj };
                    (
                        spec_with_workflow(doc, map.insert(id@, obj)),
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
}

pub open spec fn spec_unlease(t: TkV, state: TaskState, retry: Option<u64>) -> TkV {
    TkV { state, pid: None, ttl: None, lease_timeout_at: None, retry_timeout_at: retry, ..t }
}

pub open spec fn spec_task_release(doc: DocumentBodyV, id: String, version: u64, now: Time) -> (DocumentBodyV, Response) {
    let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
    match held {
        Held::Missing => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 404 })),
        Held::Stale => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 409 })),
        Held::Ok(obj) => {
            let task = match obj.task { Some(t) => Some(spec_unlease(t, TaskState::Pending, Some(now))), None => None };
            (spec_with_workflow(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 200 }))
        },
    }
}

pub open spec fn spec_task_fulfill(doc: DocumentBodyV, id: String, version: u64, action: PromiseSettleReq, now: Time) -> (DocumentBodyV, Response) {
    if !action.state.spec_settable() {
        (doc, spec_promise_res(400, None))
    } else {
        let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_workflow(doc, map), spec_promise_res(404, None)),
            Held::Stale => (spec_with_workflow(doc, map), spec_promise_res(409, None)),
            Held::Ok(obj) => {
                let promise = PromV { state: action.state, value: action.value, settled_at: Some(now), ..obj.promise };
                let task = match obj.task { Some(t) if t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)), other => other };
                let obj = ObjV { promise, task };
                (spec_with_workflow(doc, map.insert(id@, obj)), spec_promise_res(200, Some(spec_record(id, obj.promise))))
            },
        }
    }
}

pub open spec fn spec_task_halt(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
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
                (spec_with_workflow(doc, map.insert(id@, obj)), Response::Status(StatusRes { status: 200 }))
            },
        }
    }
}

pub open spec fn spec_task_continue(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
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
                (spec_with_workflow(doc, map.insert(id@, obj)), Response::Status(StatusRes { status: 200 }))
            },
        }
    }
}

pub open spec fn spec_heartbeat(doc: DocumentBodyV, pid: String, tasks: Seq<TaskRef>, now: Time) -> (DocumentBodyV, Response) {
    if tasks.len() == 0 {
        (doc, Response::Status(StatusRes { status: 200 }))
    } else if !spec_one_origin(tasks, origin(tasks[0].id@), 0) {
        (doc, Response::Status(StatusRes { status: 400 }))
    } else {
        (spec_with_workflow(doc, spec_extend(spec_workflow_map(doc), pid@, tasks, now, 0)), Response::Status(StatusRes { status: 200 }))
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

pub open spec fn spec_suspend(doc: DocumentBodyV, id: String, version: u64, actions: Seq<PromiseRegisterCallbackReq>, now: Time) -> (DocumentBodyV, Response) {
    if actions.len() == 0 || spec_bad_suspend(actions, id@, 0) || !spec_distinct_awaited(actions, 0) {
        (doc, Response::Status(StatusRes { status: 400 }))
    } else {
        let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 404 })),
            Held::Stale => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 409 })),
            Held::Ok(obj) => {
                if spec_missing_awaited(map, actions, 0) || spec_unawaitable(map, actions, 0) {
                    (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 422 }))
                } else if spec_any_settled(map, actions, now, 0) {
                    let task = match obj.task { Some(t) => Some(TkV { resumes: Seq::empty(), ..t }), None => None };
                    (spec_with_workflow(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 300 }))
                } else {
                    let map = spec_add_callbacks(map, id@, actions, 0);
                    let obj = map[id@];
                    let task = match obj.task {
                        Some(t) => Some(TkV { resumes: Seq::empty(), ..spec_unlease(t, TaskState::Suspended, None) }),
                        None => None,
                    };
                    (spec_with_workflow(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 200 }))
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

pub open spec fn spec_fence(doc: DocumentBodyV, id: String, version: u64, action: TaskFenceAction, now: Time) -> (DocumentBodyV, Response) {
    let target = match action {
        TaskFenceAction::Create(c) => c.id,
        TaskFenceAction::Settle(st) => st.id,
    };
    if target@ == id@ || !same_origin_spec(target@, id@) {
        (doc, Response::TaskFence(TaskFenceRes { status: 400, action: None }))
    } else {
        let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_workflow(doc, map), Response::TaskFence(TaskFenceRes { status: 404, action: None })),
            Held::Stale => (spec_with_workflow(doc, map), Response::TaskFence(TaskFenceRes { status: 409, action: None })),
            Held::Ok(_) => {
                let doc = spec_with_workflow(doc, map);
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

pub open spec fn spec_fence_check(doc: DocumentBodyV, id: String, version: u64, now: Time) -> (DocumentBodyV, Response) {
    let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
    match held {
        Held::Missing => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 404 })),
        Held::Stale => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 409 })),
        Held::Ok(_) => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 200 })),
    }
}

pub open spec fn spec_schedule_get(doc: DocumentBodyV, id: String) -> (DocumentBodyV, Response) {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.id == id => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
        _ => (doc, Response::Schedule(ScheduleRes { status: 404, schedule: None })),
    }
}

pub open spec fn spec_schedule_create(doc: DocumentBodyV, req: ScheduleCreateReq, now: Time) -> (DocumentBodyV, Response) {
    let next_run_at = echod_abstract_spec::axioms::spec_next_cron(req.cron@, now);
    if !spec_deadline_bounded(next_run_at, req.promise_timeout)
        || (spec_targeted(req.promise_tags) && spec_timer(req.promise_tags))
    {
        (doc, Response::Schedule(ScheduleRes { status: 400, schedule: None }))
    } else {
        match doc {
            DocumentBodyV::Schedule(Some(schedule)) => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
            _ => {
                let schedule = Schedule {
                    id: req.id,
                    cron: req.cron,
                    promise_id: req.promise_id,
                    promise_timeout: req.promise_timeout,
                    promise_param: req.promise_param,
                    promise_tags: req.promise_tags,
                next_run_at,
                    last_run_at: None,
                    created_at: now,
                };
                (DocumentBodyV::Schedule(Some(schedule)), Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) }))
            },
        }
    }
}

pub open spec fn spec_schedule_delete(doc: DocumentBodyV, id: String) -> (DocumentBodyV, Response) {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.id == id => (DocumentBodyV::Schedule(None), Response::Status(StatusRes { status: 200 })),
        _ => (doc, Response::Status(StatusRes { status: 404 })),
    }
}

pub open spec fn spec_run_due(doc: DocumentBodyV, now: Time, retry_timeout: u64) -> (DocumentBodyV, Option<Response>, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.next_run_at <= now => {
            let at = schedule.next_run_at;
            let pending = PendingV {
                promise: echod_abstract_spec::axioms::spec_expand(schedule.promise_id@, schedule.id@, at),
                at,
                timeout: schedule.promise_timeout,
                param: schedule.promise_param,
                tags: schedule.promise_tags,
            };
            let schedule = Schedule {
                last_run_at: Some(at),
                next_run_at: echod_abstract_spec::axioms::spec_next_cron(schedule.cron@, at),
                ..schedule
            };
            (DocumentBodyV::Schedule(Some(schedule)), None, seq![pending], Seq::empty())
        },
        DocumentBodyV::Workflow(map) => {
            match spec_due_id(map, spec_sorted_present(map), now) {
                Some(id) => {
                    let (map, notes) = spec_step_object(map, id, now, retry_timeout);
                    (DocumentBodyV::Workflow(map), None, Seq::empty(), notes)
                },
                None => (doc, None, Seq::empty(), Seq::empty()),
            }
        },
        other => (other, None, Seq::empty(), Seq::empty()),
    }
}

/// `spec_run_due` iterated: it stops at a step that leaves the document as it
/// was, or after `limit` steps. The occurrences queued and the notes, in order.
pub open spec fn spec_sweep(doc: DocumentBodyV, now: Time, retry_timeout: u64, limit: nat) -> (DocumentBodyV, Seq<PendingV>, Seq<NoteV>)
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

/// The complete document-level request transition.  Both closures have the
/// same finite budget.  Exhaustion is an atomic rejection: neither the
/// partially closed document nor any effect escapes.
pub open spec fn spec_request_commits(
    doc: DocumentBodyV,
    request: Request,
    now: Time,
    retry_timeout: u64,
    limit: nat,
) -> bool {
    let (after, response, _, _) =
        spec_request_transition(doc, request, now, retry_timeout, limit);
    response != spec_unavailable(request) && after != doc
}

pub open spec fn spec_request_transition(
    doc: DocumentBodyV,
    request: Request,
    now: Time,
    retry_timeout: u64,
    limit: nat,
) -> (DocumentBodyV, Response, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocumentBodyV::Schedule(_) => {
            let (doc, response) = spec_handle(doc, request, now);
            (doc, response, Seq::empty(), Seq::empty())
        },
        DocumentBodyV::Workflow(_) => {
            let (swept, before_born, before_notes) =
                spec_sweep(doc, now, retry_timeout, limit);
            if spec_earliest_in(swept, now) is Some {
                (doc, spec_unavailable(request), Seq::empty(), Seq::empty())
            } else {
                let (handled, response) = spec_handle(swept, request, now);
                let (closed, after_born, after_notes) =
                    spec_sweep(handled, now, retry_timeout, limit);
                if spec_earliest_in(closed, now) is Some {
                    (doc, spec_unavailable(request), Seq::empty(), Seq::empty())
                } else {
                    (
                        closed,
                        response,
                        before_born + after_born,
                        spec_committed_notes(doc, closed, now),
                    )
                }
            }
        },
    }
}

pub open spec fn spec_occurrence(doc: DocumentBodyV, pending: PendingV, now: Time) -> DocumentBodyV {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
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
            Some(t) if t.state == TaskState::Pending => Some(TkV { retry_timeout_at: Some(now), ..t }),
            other => other,
        };
        spec_with_workflow(doc, map.insert(pending.promise, ObjV { promise, task }))
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

proof fn lemma_before_irrefl(a: Seq<char>)
    ensures
        !spec_before(a, a),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_before_irrefl(a.drop_first());
    }
}

proof fn lemma_before_trans(a: Seq<char>, b: Seq<char>, c: Seq<char>)
    requires
        spec_before(a, b),
        spec_before(b, c),
    ensures
        spec_before(a, c),
    decreases a.len() + b.len() + c.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if c.len() == 0 {
    } else if a[0] != b[0] {
    } else if b[0] != c[0] {
    } else {
        lemma_before_trans(a.drop_first(), b.drop_first(), c.drop_first());
    }
}

spec fn least_key(keys: Set<Seq<char>>, k: Seq<char>) -> bool {
    keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k)
}

proof fn lemma_least_key_exists(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        exists|k: Seq<char>| least_key(keys, k),
    decreases keys.len(),
{
    let x = keys.choose();
    assert(keys.contains(x));
    let rest = keys.remove(x);
    assert(rest.len() == keys.len() - 1);
    if rest.len() == 0 {
        assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, x) by {
            if o != x {
                assert(rest.contains(o));
            } else {
                lemma_before_irrefl(x);
            }
        };
        assert(least_key(keys, x));
    } else {
        lemma_least_key_exists(rest);
        let m = choose|m: Seq<char>| least_key(rest, m);
        assert(keys.contains(m));
        if spec_before(x, m) {
            assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, x) by {
                if o == x {
                    lemma_before_irrefl(x);
                } else {
                    assert(rest.contains(o));
                    if spec_before(o, x) {
                        lemma_before_trans(o, x, m);
                    }
                }
            };
            assert(least_key(keys, x));
        } else {
            assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, m) by {
                if o != x {
                    assert(rest.contains(o));
                }
            };
            assert(least_key(keys, m));
        }
    }
}

/// The concrete sorted-key choice belongs to the finite nonempty input set.
///
/// This is the only key-order proof exported for the refinement crate.
pub proof fn lemma_min_key_present(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        keys.contains(spec_min_key(keys)),
{
    reveal(spec_min_key);
    lemma_least_key_exists(keys);
    let k = choose|k: Seq<char>| least_key(keys, k);
    assert(keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k));
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
        lemma_min_key_present(keys);
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
                        retry_timeout_at: Some(now),
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
        spec_min_nat(spec_body_deadline(spec_read(docs[i].key, docs[i].body)), spec_deadlines(node, docs, i + 1))
    }
}

pub open spec fn spec_body_deadline(doc: DocumentBodyV) -> Option<nat> {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) => Some(schedule.next_run_at as nat),
        DocumentBodyV::Workflow(map) => spec_map_deadline(map, spec_sorted(map.dom())),
        DocumentBodyV::Schedule(None) => None,
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

pub open spec fn spec_earliest_in(doc: DocumentBodyV, now: Time) -> Option<u64> {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.next_run_at <= now => Some(schedule.next_run_at),
        DocumentBodyV::Workflow(map) => spec_map_due(map, spec_sorted(map.dom()), now),
        _ => None,
    }
}

pub open spec fn spec_map_due(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, now: Time) -> Option<u64>
    decreases keys.len(),
{
    if keys.len() == 0 { None }
    else { spec_earlier(spec_obj_due(map[keys[0]], now), spec_map_due(map, keys.drop_first(), now)) }
}



} // verus!

// ---------------------------------------------------------------------------
// Store
// ---------------------------------------------------------------------------

verus! {


#[make_spec_type]
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Etag(pub String);


#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreError {
    /// A conditional write found the object at another version.
    PreconditionFailed,
    /// The store did not answer, or answered with an error: the effect of
    /// a write is unknown.
    Unavailable(String),
}


#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Read {
    Body(Vec<u8>, Etag),
    NotModified,
    Absent,
}


/// A request to the store, as the executor makes it.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreReq {
    Get { key: String },
    GetIfNoneMatch { key: String, etag: Etag },
    PutIfMatch { key: String, body: Vec<u8>, etag: Etag },
    PutIfNoneMatch { key: String, body: Vec<u8> },
    AppIfMatch { key: String, offset: u64, body: Vec<u8>, etag: Etag },
    Put { key: String, body: Vec<u8> },
    Del { key: String },
    List { prefix: String, max_keys: usize },
    ListPrefixes { prefix: String },
}


/// The operation-shaped response from the store.
#[allow(inconsistent_fields)]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreRes {
    Get { result: Result<Option<(Vec<u8>, Etag)>, StoreError> },
    GetIfNoneMatch { result: Result<Read, StoreError> },
    PutIfMatch { result: Result<Etag, StoreError> },
    PutIfNoneMatch { result: Result<Etag, StoreError> },
    AppIfMatch { result: Result<Etag, StoreError> },
    Put { result: Result<(), StoreError> },
    Del { result: Result<(), StoreError> },
    List { result: Result<Vec<String>, StoreError> },
    ListPrefixes { result: Result<Vec<String>, StoreError> },
}


// ---------------------------------------------------------------------------
// The requests and responses as views: strings as their characters
// ---------------------------------------------------------------------------

pub ghost enum StoreErrorSpec {
    PreconditionFailed,
    Unavailable(Seq<char>),
}


impl DeepView for StoreError {
    type V = StoreErrorSpec;
    open spec fn deep_view(&self) -> StoreErrorSpec {
        match self {
            StoreError::PreconditionFailed => StoreErrorSpec::PreconditionFailed,
            StoreError::Unavailable(m) => StoreErrorSpec::Unavailable(m@),
        }
    }
}


#[cfg(verus_keep_ghost)]
pub ghost enum ReadSpec {
    Body(Seq<u8>, EtagSpec),
    NotModified,
    Absent,
}


#[cfg(verus_keep_ghost)]
impl DeepView for Read {
    type V = ReadSpec;
    open spec fn deep_view(&self) -> ReadSpec {
        match self {
            Read::Body(b, e) => ReadSpec::Body(b@, e.deep_view()),
            Read::NotModified => ReadSpec::NotModified,
            Read::Absent => ReadSpec::Absent,
        }
    }
}


#[cfg(verus_keep_ghost)]
pub ghost enum StoreReqSpec {
    Get { key: Seq<char> },
    GetIfNoneMatch { key: Seq<char>, etag: EtagSpec },
    PutIfMatch { key: Seq<char>, body: Seq<u8>, etag: EtagSpec },
    PutIfNoneMatch { key: Seq<char>, body: Seq<u8> },
    AppIfMatch { key: Seq<char>, offset: u64, body: Seq<u8>, etag: EtagSpec },
    Put { key: Seq<char>, body: Seq<u8> },
    Del { key: Seq<char> },
    List { prefix: Seq<char>, max_keys: usize },
    ListPrefixes { prefix: Seq<char> },
}


#[cfg(verus_keep_ghost)]
impl DeepView for StoreReq {
    type V = StoreReqSpec;
    open spec fn deep_view(&self) -> StoreReqSpec {
        match self {
            StoreReq::Get { key } => StoreReqSpec::Get { key: key@ },
            StoreReq::GetIfNoneMatch { key, etag } => StoreReqSpec::GetIfNoneMatch { key: key@, etag: etag.deep_view() },
            StoreReq::PutIfMatch { key, body, etag } => StoreReqSpec::PutIfMatch { key: key@, body: body@, etag: etag.deep_view() },
            StoreReq::PutIfNoneMatch { key, body } => StoreReqSpec::PutIfNoneMatch { key: key@, body: body@ },
            StoreReq::AppIfMatch { key, offset, body, etag } => StoreReqSpec::AppIfMatch { key: key@, offset: *offset, body: body@, etag: etag.deep_view() },
            StoreReq::Put { key, body } => StoreReqSpec::Put { key: key@, body: body@ },
            StoreReq::Del { key } => StoreReqSpec::Del { key: key@ },
            StoreReq::List { prefix, max_keys } => StoreReqSpec::List { prefix: prefix@, max_keys: *max_keys },
            StoreReq::ListPrefixes { prefix } => StoreReqSpec::ListPrefixes { prefix: prefix@ },
        }
    }
}


/// A store's answer is a value a process takes as it is: its deep view is
/// itself.
impl DeepView for StoreRes {
    type V = StoreRes;
    open spec fn deep_view(&self) -> StoreRes {
        *self
    }
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


// ---------------------------------------------------------------------------
// The store, as a specification
// ---------------------------------------------------------------------------

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


/// `spec_prefix` stays within the bytes it reads.
pub proof fn lemma_prefix_bounds(bytes: Seq<u8>, width: nat, pos: nat)
    requires
        pos <= bytes.len(),
        pos <= width,
    ensures
        pos <= spec_prefix(bytes, width, pos) <= bytes.len(),
    decreases width - pos,
{
    if pos >= width {
    } else if pos >= bytes.len() || !spec_utf8_ok(bytes[0], pos, bytes[pos as int]) {
    } else {
        lemma_prefix_bounds(bytes, width, pos + 1);
    }
}


#[via_fn]
proof fn spec_lossy_decreases(bytes: Seq<u8>) {
    if bytes.len() > 0 {
        let width = spec_utf8_width(bytes[0]);
        if width >= 2 {
            lemma_prefix_bounds(bytes, width, 1);
        }
    }
}


/// How many leading bytes form one UTF-8 character, or the maximal subpart
/// of one ill-formed sequence. The same split `String::from_utf8_lossy` uses.
pub open spec fn spec_prefix(bytes: Seq<u8>, width: nat, pos: nat) -> nat
    decreases width - pos,
{
    if pos >= width {
        width
    } else if pos >= bytes.len() || !spec_utf8_ok(bytes[0], pos, bytes[pos as int]) {
        pos
    } else {
        spec_prefix(bytes, width, pos + 1)
    }
}


pub open spec fn spec_lossy(bytes: Seq<u8>) -> Seq<u8>
    decreases bytes.len(),
    via spec_lossy_decreases
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


/// The next version. A `u64` counter stops at its top.
pub open spec fn spec_bump(version: nat) -> nat {
    if version < u64::MAX as nat { version + 1 } else { version }
}


/// One store request. The same cases as `Store::apply`.
pub open spec fn spec_apply(store: StoreV, req: StoreReq) -> (StoreV, StoreRes) {
    match req {
        StoreReq::Get { key } => {
            match spec_find(store.entries, key@, 0) {
                None => (store, StoreRes::Get { result: Ok(None) }),
                Some(i) => {
                    let body = store.entries[i].body;
                    (store, StoreRes::Get { result: Ok(Some((spec_bytes(body), spec_etag(body)))) })
                },
            }
        },
        StoreReq::GetIfNoneMatch { key, etag } => {
            match spec_find(store.entries, key@, 0) {
                None => (store, StoreRes::GetIfNoneMatch { result: Ok(Read::Absent) }),
                Some(i) => {
                    let body = store.entries[i].body;
                    let have = spec_etag(body);
                    if have == etag {
                        (store, StoreRes::GetIfNoneMatch { result: Ok(Read::NotModified) })
                    } else {
                        (store, StoreRes::GetIfNoneMatch { result: Ok(Read::Body(spec_bytes(body), have)) })
                    }
                },
            }
        },
        StoreReq::PutIfNoneMatch { key, body } => {
            if spec_find(store.entries, key@, 0) is Some {
                (store, StoreRes::PutIfNoneMatch { result: Err(StoreError::PreconditionFailed) })
            } else {
                let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version: 1 });
                (StoreV { entries, ..store }, StoreRes::PutIfNoneMatch { result: Ok(spec_etag(body@)) })
            }
        },
        StoreReq::PutIfMatch { key, body, etag } => {
            match spec_find(store.entries, key@, 0) {
                Some(i) if spec_etag(store.entries[i].body) == etag => {
                    let version = spec_bump(store.entries[i].version);
                    let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version });
                    (StoreV { entries, ..store }, StoreRes::PutIfMatch { result: Ok(spec_etag(body@)) })
                },
                _ => (store, StoreRes::PutIfMatch { result: Err(StoreError::PreconditionFailed) }),
            }
        },
        StoreReq::AppIfMatch { key, offset, body, etag } => {
            if !store.appendable {
                (store, StoreRes::AppIfMatch {
                    result: Err(StoreError::Unavailable(spec_string(seq![
                        't', 'h', 'i', 's', ' ', 's', 't', 'o', 'r', 'e', ' ', 'd', 'o', 'e', 's', ' ',
                        'n', 'o', 't', ' ', 'a', 'p', 'p', 'e', 'n', 'd',
                    ]))),
                })
            } else {
                match spec_find(store.entries, key@, 0) {
                    Some(i) if spec_etag(store.entries[i].body) == etag && store.entries[i].body.len() == offset => {
                        let joined = store.entries[i].body + body@;
                        let version = spec_bump(store.entries[i].version);
                        let entries = spec_put(store.entries, EntryV { key: key@, body: joined, version });
                        (StoreV { entries, ..store }, StoreRes::AppIfMatch { result: Ok(spec_etag(joined)) })
                    },
                    _ => (store, StoreRes::AppIfMatch { result: Err(StoreError::PreconditionFailed) }),
                }
            }
        },
        StoreReq::Put { key, body } => {
            let version = match spec_find(store.entries, key@, 0) {
                Some(i) => spec_bump(store.entries[i].version),
                None => 1,
            };
            let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version });
            (StoreV { entries, ..store }, StoreRes::Put { result: Ok(()) })
        },
        StoreReq::Del { key } => {
            match spec_find(store.entries, key@, 0) {
                Some(i) => (StoreV { entries: spec_remove_at(store.entries, i), ..store }, StoreRes::Del { result: Ok(()) }),
                None => (store, StoreRes::Del { result: Ok(()) }),
            }
        },
        StoreReq::List { prefix, max_keys } => {
            (store, StoreRes::List { result: Ok(spec_bytes_keys(spec_list(store.entries, prefix@, max_keys as nat, 0, Seq::empty()))) })
        },
        StoreReq::ListPrefixes { prefix } => {
            (store, StoreRes::ListPrefixes { result: Ok(spec_bytes_keys(spec_prefixes(store.entries, prefix@, 0, Seq::empty()))) })
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


pub open spec fn key_views(v: Seq<String>) -> Seq<Seq<char>> {
    v.map_values(|s: String| s@)
}


} // verus!

#[cfg(not(verus_keep_ghost))]
impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StoreError::PreconditionFailed => f.write_str("precondition failed"),
            StoreError::Unavailable(m) => write!(f, "store unavailable: {m}"),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl std::error::Error for StoreError {

} // verus!
