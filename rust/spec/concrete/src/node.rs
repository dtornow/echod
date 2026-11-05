//! One node. A request or a due document is a flight: load the document,
//! decide, write it back, then answer. The store keeps the bytes. Nothing
//! here calls the abstract model.
//!
//! The executable node first; then the node as a specification, over the
//! view types: `NodeV`, `DocV`, the `spec_*` twins of its handlers and steps.

use std::collections::{BTreeMap, VecDeque};

use vstd::prelude::*;

use echod_types::{
    origin_of, same_origin, PromiseCreateReq, PromiseRecord, PromiseRegisterCallbackReq,
    PromiseRes, PromiseSettleReq, PromiseState, Request, Response, Schedule, ScheduleCreateReq,
    ScheduleRes, StatusRes, Tags, TaskClaimRes, TaskFenceAction, TaskFenceInnerRes, TaskFenceRes,
    TaskGetRes, TaskRecord, TaskRef, TaskState, Value,
};
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};

#[cfg(verus_keep_ghost)]
use echod_abstract::{Call, Output};
use echod_rover::Time;
#[cfg(verus_keep_ghost)]
use echod_types::{origin, same_origin_spec};

#[cfg(verus_keep_ghost)]
use crate::model::{
    spec_bytes, spec_get, spec_notes, spec_reply, spec_string, Message, Pid,
};
use crate::model::{Logic, LogicV};
#[cfg(verus_keep_ghost)]
use crate::store::{spec_before, spec_fnv, spec_sat_add, spec_starts, Read, StoreError};
use crate::store::{fnv1a, Etag, StoreCall, StoreOutcome};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    /// The process shell: clock and flags.
    pub logic: Logic,
    /// When the next timeout is worth delivering.
    pub wake: Option<u64>,
    pub next_request: u64,
    address: u64,
    nodes: u64,
    /// How long a pending task waits before it is offered again.
    retry_timeout: u64,
    flight: Option<Flight>,
    cache: BTreeMap<String, Cached>,
    pending: VecDeque<Pending>,
    next_op: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Cached {
    doc: Doc,
    etag: Option<Etag>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Flight {
    op: u64,
    key: String,
    phase: Phase,
    job: Job,
    etag: Option<Etag>,
    /// The clock of the event that opened the flight.
    now: u64,
    /// The client a request flight answers: its name and the call id.
    caller: Option<(String, u64)>,
    /// The document a write is putting, installed in the cache when it lands.
    decided: Option<Doc>,
    /// Occurrences a schedule step queued, delivered to the pending list when the write lands.
    born: Vec<Pending>,
    reply: Option<(String, u64, Response)>,
    /// Boundary output of a due step, sent when that step's document is committed.
    notify: Vec<Outbound>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Phase {
    Load,
    Write,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Job {
    External { request: Request },
    Due,
    Occurrence(Pending),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Pending {
    promise: String,
    at: u64,
    timeout: u64,
    param: Value,
    tags: Tags,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
enum Doc {
    Origin(BTreeMap<String, Obj>),
    Schedule(Option<Schedule>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
struct Obj {
    promise: Prom,
    task: Option<Tk>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
struct Prom {
    state: PromiseState,
    param: Value,
    value: Value,
    tags: Tags,
    timeout_at: u64,
    created_at: u64,
    settled_at: Option<u64>,
    callbacks: Vec<String>,
    listeners: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
struct Tk {
    state: TaskState,
    version: u64,
    pid: Option<String>,
    ttl: Option<u64>,
    lease_timeout_at: Option<u64>,
    retry_timeout_at: Option<u64>,
    resumes: Vec<String>,
}

/// What a due step tells the outside, once the document that step wrote is the one in the cache.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outbound {
    /// A pending task is offered again.
    Execute { id: String, version: u64 },
    /// A listener's promise has settled.
    Unblock {
        address: String,
        promise: PromiseRecord,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Act {
    ToStore {
        op: u64,
        call: StoreCall,
    },
    Reply {
        client: String,
        id: u64,
        response: Response,
    },
    Notify(Outbound),
}

impl Node {
    pub fn new(address: u64, nodes: u64, loops: bool, retry_timeout: u64) -> Self {
        Self {
            logic: Logic {
                clock: 0,
                loops,
                stopping: false,
                stopped: false,
                last_wake: None,
            },
            wake: None,
            next_request: 1,
            address,
            nodes: nodes.max(1),
            retry_timeout,
            flight: None,
            cache: BTreeMap::new(),
            pending: VecDeque::new(),
            next_op: 1,
        }
    }

    pub fn busy(&self) -> bool {
        self.flight.is_some()
    }

    pub fn request(&mut self, now: u64, client: &str, id: u64, request: &Request) -> Vec<Act> {
        if self.flight.is_some() {
            return Vec::new();
        }
        let answer = |response: Response| Act::Reply {
            client: client.to_string(),
            id,
            response,
        };
        let Some(key) = key_of(request) else {
            return vec![answer(pure(request))];
        };
        if !self.owns(&key) {
            return vec![answer(unavailable(request))];
        }
        self.begin(
            key,
            Job::External {
                request: request.clone(),
            },
            now,
            Some((client.to_string(), id)),
        )
    }

    pub fn store(&mut self, now: u64, op: u64, outcome: &StoreOutcome) -> Vec<Act> {
        let Some(flight) = self.flight.clone() else {
            return Vec::new();
        };
        if flight.op != op {
            return Vec::new();
        }
        match flight.phase {
            Phase::Load => match outcome {
                StoreOutcome::Got(body) => self.loaded(now, flight, body.as_ref()),
                StoreOutcome::Failed(_) => self.fail(flight),
                _ => Vec::new(),
            },
            Phase::Write => match outcome {
                StoreOutcome::Written(tag) => self.committed(now, flight, tag.clone()),
                StoreOutcome::Failed(_) => self.fail(flight),
                _ => Vec::new(),
            },
        }
    }

    /// Run one due document, or nothing when the node is in a flight or nothing is due.
    pub fn timeout(&mut self, now: u64) -> Vec<Act> {
        if self.flight.is_some() {
            return Vec::new();
        }
        if let Some(pending) = self.pending.pop_front() {
            let key = origin_key(&pending.promise);
            if !self.owns(&key) {
                return Vec::new();
            }
            return self.begin(key, Job::Occurrence(pending), now, None);
        }
        let Some(key) = self.earliest_due(now) else {
            return Vec::new();
        };
        self.begin(key, Job::Due, now, None)
    }

    /// When the next timeout is worth delivering. `None` while a flight is open:
    /// that flight continues by a store reply.
    pub fn next_wake(&self) -> Option<u64> {
        if self.flight.is_some() {
            return None;
        }
        let mut best: Option<u64> = self.pending.front().map(|p| p.at);
        for (key, cached) in &self.cache {
            if !self.owns(key) {
                continue;
            }
            if let Some(at) = deadline(&cached.doc) {
                best = Some(best.map_or(at, |b| b.min(at)));
            }
        }
        best
    }

    fn owns(&self, key: &str) -> bool {
        fnv1a(key) % self.nodes == self.address
    }

    fn alloc(&mut self) -> u64 {
        let op = self.next_op;
        self.next_op += 1;
        op
    }

    fn begin(
        &mut self,
        key: String,
        job: Job,
        now: u64,
        caller: Option<(String, u64)>,
    ) -> Vec<Act> {
        if let Some(cached) = self.cache.get(&key).cloned() {
            let flight = Flight {
                op: 0,
                key,
                phase: Phase::Load,
                job,
                etag: cached.etag,
                now,
                caller,
                decided: None,
                born: Vec::new(),
                reply: None,
                notify: Vec::new(),
            };
            return self.decide(flight, cached.doc);
        }
        let op = self.alloc();
        let call = StoreCall::Get { key: key.clone() };
        self.flight = Some(Flight {
            op,
            key,
            phase: Phase::Load,
            job,
            etag: None,
            now,
            caller,
            decided: None,
            born: Vec::new(),
            reply: None,
            notify: Vec::new(),
        });
        vec![Act::ToStore { op, call }]
    }

    fn loaded(&mut self, _now: u64, mut flight: Flight, got: Option<&(Vec<u8>, Etag)>) -> Vec<Act> {
        let (doc, etag) = match got {
            Some((body, tag)) => (decode(&flight.key, body), Some(tag.clone())),
            None => (empty_doc(&flight.key), None),
        };
        flight.etag = etag;
        self.decide(flight, doc)
    }

    fn decide(&mut self, mut flight: Flight, doc: Doc) -> Vec<Act> {
        let now = flight.now;
        let (next, reply, born, notify) = match &flight.job {
            Job::External { request } => {
                let (next, response) = handle(doc, request, now);
                (next, Some(response), Vec::new(), Vec::new())
            }
            Job::Due => {
                let (next, born, notify) = run_due(doc, now, self.retry_timeout);
                (next, None, born, notify)
            }
            Job::Occurrence(pending) => {
                let next = create_occurrence(doc, pending, now);
                (next, None, Vec::new(), Vec::new())
            }
        };
        if let (Some((client, id)), Some(response)) = (flight.caller.clone(), reply) {
            flight.reply = Some((client, id, response));
        }
        flight.notify = notify;
        let previous = self
            .cache
            .get(&flight.key)
            .map(|c| c.doc.clone())
            .unwrap_or_else(|| empty_doc(&flight.key));
        if next == previous && born.is_empty() {
            self.flight = None;
            let key = flight.key.clone();
            let etag = flight.etag.clone();
            let acts = sent(&flight);
            self.remember(&key, next, etag);
            return acts;
        }
        let body = encode(&next);
        let op = self.alloc();
        let call = match &flight.etag {
            Some(tag) => StoreCall::PutIfMatch {
                key: flight.key.clone(),
                body,
                etag: tag.clone(),
            },
            None => StoreCall::PutIfNoneMatch {
                key: flight.key.clone(),
                body,
            },
        };
        flight.op = op;
        flight.phase = Phase::Write;
        flight.decided = Some(next);
        flight.born = born;
        self.flight = Some(flight);
        vec![Act::ToStore { op, call }]
    }

    fn committed(&mut self, _now: u64, flight: Flight, tag: Etag) -> Vec<Act> {
        self.flight = None;
        let Flight {
            key, decided, born, ..
        } = &flight;
        if let Some(doc) = decided.clone() {
            self.remember(key, doc, Some(tag));
        }
        for item in born.clone() {
            self.pending.push_back(item);
        }
        sent(&flight)
    }

    /// Bytes of each cached document, and the occurrences still owed.
    pub fn document_bodies(&self) -> Vec<(String, Vec<u8>)> {
        self.cache
            .iter()
            .map(|(key, cached)| (key.clone(), encode(&cached.doc)))
            .collect()
    }

    pub fn pending_ids(&self) -> Vec<String> {
        self.pending
            .iter()
            .map(|item| item.promise.clone())
            .collect()
    }

    fn pending_items(&self) -> Vec<Pending> {
        self.pending.iter().cloned().collect()
    }

    fn cached_entries(&self) -> Vec<(String, Vec<u8>, Option<String>)> {
        self.cache
            .iter()
            .map(|(key, cached)| {
                (
                    key.clone(),
                    encode(&cached.doc),
                    cached.etag.as_ref().map(|tag| tag.0.clone()),
                )
            })
            .collect()
    }

    /// The open flight's key, and whether it is writing the document back.
    pub fn flight_key(&self) -> Option<(String, bool)> {
        self.flight
            .as_ref()
            .map(|flight| (flight.key.clone(), matches!(flight.phase, Phase::Write)))
    }

    fn fail(&mut self, flight: Flight) -> Vec<Act> {
        self.flight = None;
        match (&flight.job, flight.caller) {
            (Job::External { request }, Some((client, id))) => {
                vec![Act::Reply {
                    client,
                    id,
                    response: unavailable(request),
                }]
            }
            _ => Vec::new(),
        }
    }

    fn remember(&mut self, key: &str, doc: Doc, etag: Option<Etag>) {
        if is_empty(&doc) && etag.is_none() {
            self.cache.remove(key);
        } else {
            self.cache.insert(key.to_string(), Cached { doc, etag });
        }
    }

    fn earliest_due(&self, now: u64) -> Option<String> {
        let mut best: Option<(u64, String)> = None;
        for (key, cached) in &self.cache {
            if !self.owns(key) {
                continue;
            }
            if let Some(at) = earliest_in(&cached.doc, now) {
                if best.as_ref().is_none_or(|(b, _)| at < *b) {
                    best = Some((at, key.clone()));
                }
            }
        }
        best.map(|(_, key)| key)
    }
}

fn sent(flight: &Flight) -> Vec<Act> {
    let mut acts = Vec::new();
    if let Some((client, id, response)) = flight.reply.clone() {
        acts.push(Act::Reply {
            client,
            id,
            response,
        });
    }
    for note in &flight.notify {
        acts.push(Act::Notify(note.clone()));
    }
    acts
}

fn key_of(request: &Request) -> Option<String> {
    let id = match request {
        Request::PromiseGet(q) => q.id.as_str(),
        Request::PromiseCreate(q) => q.id.as_str(),
        Request::PromiseSettle(q) => q.id.as_str(),
        Request::PromiseRegisterCallback(q) => q.awaited.as_str(),
        Request::PromiseRegisterListener(q) => q.awaited.as_str(),
        Request::TaskGet(q) => q.id.as_str(),
        Request::TaskCreate(q) => q.action.id.as_str(),
        Request::TaskAcquire(q) => q.id.as_str(),
        Request::TaskFulfill(q) => q.id.as_str(),
        Request::TaskRelease(q) => q.id.as_str(),
        Request::TaskHalt(q) => q.id.as_str(),
        Request::TaskContinue(q) => q.id.as_str(),
        Request::TaskFence(q) => q.id.as_str(),
        Request::TaskFenceCheck(q) => q.id.as_str(),
        Request::TaskSuspend(q) => q.id.as_str(),
        Request::TaskHeartbeat(q) => return q.tasks.first().map(|t| origin_key(&t.id)),
        Request::ScheduleGet(q) => return Some(schedule_key(&q.id)),
        Request::ScheduleDelete(q) => return Some(schedule_key(&q.id)),
        Request::ScheduleCreate(q) => return Some(schedule_key(&q.id)),
    };
    Some(
        if matches!(
            request,
            Request::ScheduleGet(_) | Request::ScheduleCreate(_) | Request::ScheduleDelete(_)
        ) {
            schedule_key(id)
        } else {
            origin_key(id)
        },
    )
}

fn origin_key(id: &str) -> String {
    format!("o/{}", origin_of(id))
}

fn schedule_key(id: &str) -> String {
    format!("s/{id}")
}

fn empty_doc(key: &str) -> Doc {
    if key.starts_with("s/") {
        Doc::Schedule(None)
    } else {
        Doc::Origin(BTreeMap::new())
    }
}

fn is_empty(doc: &Doc) -> bool {
    match doc {
        Doc::Origin(map) => map.is_empty(),
        Doc::Schedule(slot) => slot.is_none(),
    }
}

#[cfg(not(verus_keep_ghost))]
fn encode(doc: &Doc) -> Vec<u8> {
    serde_json::to_vec(doc).unwrap_or_default()
}

#[cfg(not(verus_keep_ghost))]
fn decode(key: &str, body: &[u8]) -> Doc {
    serde_json::from_slice(body).unwrap_or_else(|_| empty_doc(key))
}

/// Serialization is uninterpreted under Verus (`spec_encode`, `spec_decode_raw`);
/// the records carry no serde there, so the exec codec is a stub.
#[cfg(verus_keep_ghost)]
fn encode(_doc: &Doc) -> Vec<u8> {
    Vec::new()
}

#[cfg(verus_keep_ghost)]
fn decode(key: &str, _body: &[u8]) -> Doc {
    empty_doc(key)
}

fn pure(request: &Request) -> Response {
    match request {
        Request::TaskHeartbeat(q) if q.tasks.is_empty() => {
            Response::Status(StatusRes { status: 200 })
        }
        _ => unavailable(request),
    }
}

fn unavailable(request: &Request) -> Response {
    match request {
        Request::PromiseGet(_)
        | Request::PromiseCreate(_)
        | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_)
        | Request::PromiseRegisterListener(_) => Response::Promise(PromiseRes {
            status: 503,
            promise: None,
        }),
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => Response::Schedule(ScheduleRes {
            status: 503,
            schedule: None,
        }),
        Request::ScheduleDelete(_)
        | Request::TaskRelease(_)
        | Request::TaskHalt(_)
        | Request::TaskContinue(_)
        | Request::TaskHeartbeat(_)
        | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => Response::Status(StatusRes { status: 503 }),
        Request::TaskGet(_) => Response::TaskGet(TaskGetRes {
            status: 503,
            task: None,
        }),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => Response::TaskClaim(TaskClaimRes {
            status: 503,
            task: None,
            promise: None,
        }),
        Request::TaskFulfill(_) => Response::Promise(PromiseRes {
            status: 503,
            promise: None,
        }),
        Request::TaskFence(_) => Response::TaskFence(TaskFenceRes {
            status: 503,
            action: None,
        }),
    }
}

fn status_of(response: &Response) -> u16 {
    match response {
        Response::Promise(r) => r.status,
        Response::Schedule(r) => r.status,
        Response::Status(r) => r.status,
        Response::TaskGet(r) => r.status,
        Response::TaskClaim(r) => r.status,
        Response::TaskFence(r) => r.status,
    }
}

pub fn reply_status(response: &Response) -> u16 {
    status_of(response)
}

fn handle(doc: Doc, request: &Request, now: u64) -> (Doc, Response) {
    match request {
        Request::PromiseGet(q) => promise_get(doc, &q.id, now),
        Request::PromiseCreate(q) => promise_create(doc, q, now),
        Request::PromiseSettle(q) => promise_settle(doc, q, now),
        Request::PromiseRegisterCallback(q) => register_callback(doc, &q.awaited, &q.awaiter, now),
        Request::PromiseRegisterListener(q) => register_listener(doc, &q.awaited, &q.address, now),
        Request::TaskGet(q) => task_get(doc, &q.id, now),
        Request::TaskCreate(q) => task_create(doc, &q.pid, q.ttl, &q.action, now),
        Request::TaskAcquire(q) => task_acquire(doc, &q.id, q.version, &q.pid, q.ttl, now),
        Request::TaskRelease(q) => task_release(doc, &q.id, q.version, now),
        Request::TaskFulfill(q) => task_fulfill(doc, &q.id, q.version, &q.action, now),
        Request::TaskHalt(q) => task_halt(doc, &q.id, now),
        Request::TaskContinue(q) => task_continue(doc, &q.id, now),
        Request::TaskHeartbeat(q) => heartbeat(doc, &q.pid, &q.tasks, now),
        Request::TaskSuspend(q) => suspend(doc, &q.id, q.version, &q.actions, now),
        Request::TaskFence(q) => fence(doc, &q.id, q.version, &q.action, now),
        Request::TaskFenceCheck(q) => fence_check(doc, &q.id, q.version, now),
        Request::ScheduleGet(q) => schedule_get(doc, &q.id),
        Request::ScheduleCreate(q) => schedule_create(doc, q, now),
        Request::ScheduleDelete(q) => schedule_delete(doc, &q.id),
    }
}

fn promise_get(mut doc: Doc, id: &str, now: u64) -> (Doc, Response) {
    let Some(seen) = origin_mut(&mut doc)
        .get(id)
        .cloned()
        .map(|obj| obj.project(now))
    else {
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 404,
                promise: None,
            }),
        );
    };
    let rec = seen.promise.record(id);
    (
        doc,
        Response::Promise(PromiseRes {
            status: 200,
            promise: Some(rec),
        }),
    )
}

fn promise_create(mut doc: Doc, req: &PromiseCreateReq, now: u64) -> (Doc, Response) {
    if timer(&req.tags) && targeted(&req.tags) {
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 400,
                promise: None,
            }),
        );
    }
    if let Some(stored) = origin_mut(&mut doc).get(&req.id).cloned() {
        let seen = stored.project(now);
        let rec = seen.promise.record(&req.id);
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 200,
                promise: Some(rec),
            }),
        );
    }
    let obj = new_object(
        &req.id,
        req.timeout_at,
        now,
        req.param.clone(),
        req.tags.clone(),
        targeted(&req.tags),
    );
    let rec = obj.promise.record(&req.id);
    origin_mut(&mut doc).insert(req.id.clone(), obj);
    (
        doc,
        Response::Promise(PromiseRes {
            status: 200,
            promise: Some(rec),
        }),
    )
}

fn promise_settle(mut doc: Doc, req: &PromiseSettleReq, now: u64) -> (Doc, Response) {
    if !req.state.settable() {
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 400,
                promise: None,
            }),
        );
    }
    let Some(stored) = origin_mut(&mut doc).get(&req.id).cloned() else {
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 404,
                promise: None,
            }),
        );
    };
    let mut seen = stored.project(now);
    if seen.promise.state == PromiseState::Pending {
        seen.promise.state = req.state;
        seen.promise.value = req.value.clone();
        seen.promise.settled_at = Some(now);
        seen.fulfill_task();
        origin_mut(&mut doc).insert(req.id.clone(), seen.clone());
    }
    let rec = seen.promise.record(&req.id);
    (
        doc,
        Response::Promise(PromiseRes {
            status: 200,
            promise: Some(rec),
        }),
    )
}

fn register_callback(mut doc: Doc, awaited: &str, awaiter: &str, now: u64) -> (Doc, Response) {
    let awaited_s = awaited.to_string();
    let awaiter_s = awaiter.to_string();
    if awaited == awaiter || !same_origin(&awaited_s, &awaiter_s) {
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 400,
                promise: None,
            }),
        );
    }
    let map = origin_mut(&mut doc);
    let (Some(mut awaited_obj), Some(mut awaiter_obj)) =
        (map.get(awaited).cloned(), map.get(awaiter).cloned())
    else {
        let status = if map.contains_key(awaited) { 422 } else { 404 };
        return (
            doc,
            Response::Promise(PromiseRes {
                status,
                promise: None,
            }),
        );
    };
    awaited_obj.project_in_place(now);
    awaiter_obj.project_in_place(now);
    if !targeted(&awaiter_obj.promise.tags) || !awaitable(&awaited_obj.promise.tags) {
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 422,
                promise: None,
            }),
        );
    }
    let rec = awaited_obj.promise.record(awaited);
    if awaited_obj.promise.state == PromiseState::Pending
        && awaiter_obj.promise.state == PromiseState::Pending
    {
        if !awaited_obj.promise.callbacks.contains(&awaiter_s) {
            awaited_obj.promise.callbacks.push(awaiter_s.clone());
        }
        map.insert(awaited_s, awaited_obj);
    }
    (
        doc,
        Response::Promise(PromiseRes {
            status: 200,
            promise: Some(rec),
        }),
    )
}

fn register_listener(mut doc: Doc, awaited: &str, address: &str, now: u64) -> (Doc, Response) {
    let Some(stored) = origin_mut(&mut doc).get(awaited).cloned() else {
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 404,
                promise: None,
            }),
        );
    };
    let mut seen = stored.project(now);
    if !awaitable(&seen.promise.tags) {
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 422,
                promise: None,
            }),
        );
    }
    let rec = seen.promise.record(awaited);
    if seen.promise.state == PromiseState::Pending {
        if !seen.promise.listeners.iter().any(|a| a == address) {
            seen.promise.listeners.push(address.to_string());
        }
        origin_mut(&mut doc).insert(awaited.to_string(), seen);
    }
    (
        doc,
        Response::Promise(PromiseRes {
            status: 200,
            promise: Some(rec),
        }),
    )
}

fn task_get(mut doc: Doc, id: &str, now: u64) -> (Doc, Response) {
    let Some(seen) = origin_mut(&mut doc)
        .get(id)
        .cloned()
        .map(|obj| obj.project(now))
    else {
        return (
            doc,
            Response::TaskGet(TaskGetRes {
                status: 404,
                task: None,
            }),
        );
    };
    let Some(task) = seen.task else {
        return (
            doc,
            Response::TaskGet(TaskGetRes {
                status: 404,
                task: None,
            }),
        );
    };
    (
        doc,
        Response::TaskGet(TaskGetRes {
            status: 200,
            task: Some(task.record(id)),
        }),
    )
}

fn task_create(
    doc: Doc,
    pid: &str,
    ttl: u64,
    action: &PromiseCreateReq,
    now: u64,
) -> (Doc, Response) {
    if !targeted(&action.tags) || timer(&action.tags) {
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 400,
                task: None,
                promise: None,
            }),
        );
    }
    let (mut doc, created) = promise_create(doc, action, now);
    if status_of(&created) == 400 {
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 400,
                task: None,
                promise: None,
            }),
        );
    }
    let Some(stored) = origin_mut(&mut doc).get(&action.id).cloned() else {
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 422,
                task: None,
                promise: None,
            }),
        );
    };
    let mut seen = stored.project(now);
    if !targeted(&seen.promise.tags) {
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 422,
                task: None,
                promise: None,
            }),
        );
    }
    let Some(task) = seen.task.clone() else {
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 409,
                task: None,
                promise: None,
            }),
        );
    };
    if task.state == TaskState::Fulfilled {
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 200,
                task: Some(task.record(&action.id)),
                promise: Some(seen.promise.record(&action.id)),
            }),
        );
    }
    if task.state == TaskState::Pending {
        seen.task.as_mut().unwrap().acquire(pid, ttl, now);
        let rec = seen.task.as_ref().unwrap().record(&action.id);
        let promise = seen.promise.record(&action.id);
        origin_mut(&mut doc).insert(action.id.clone(), seen);
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 200,
                task: Some(rec),
                promise: Some(promise),
            }),
        );
    }
    (
        doc,
        Response::TaskClaim(TaskClaimRes {
            status: 409,
            task: None,
            promise: None,
        }),
    )
}

fn task_acquire(
    mut doc: Doc,
    id: &str,
    version: u64,
    pid: &str,
    ttl: u64,
    now: u64,
) -> (Doc, Response) {
    let Some(stored) = origin_mut(&mut doc).get(id).cloned() else {
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 404,
                task: None,
                promise: None,
            }),
        );
    };
    let mut seen = stored.project(now);
    let Some(task) = seen.task.clone() else {
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 404,
                task: None,
                promise: None,
            }),
        );
    };
    if task.state != TaskState::Pending
        || task.version != version
        || seen.promise.state != PromiseState::Pending
    {
        return (
            doc,
            Response::TaskClaim(TaskClaimRes {
                status: 409,
                task: None,
                promise: None,
            }),
        );
    }
    seen.task.as_mut().unwrap().acquire(pid, ttl, now);
    let rec = seen.task.as_ref().unwrap().record(id);
    let promise = seen.promise.record(id);
    origin_mut(&mut doc).insert(id.to_string(), seen);
    (
        doc,
        Response::TaskClaim(TaskClaimRes {
            status: 200,
            task: Some(rec),
            promise: Some(promise),
        }),
    )
}

fn task_release(mut doc: Doc, id: &str, version: u64, now: u64) -> (Doc, Response) {
    match held(origin_mut(&mut doc), id, version, now) {
        Err(code) => (doc, Response::Status(StatusRes { status: code })),
        Ok(()) => {
            let mut obj = origin_mut(&mut doc).get(id).unwrap().clone();
            obj.project_in_place(now);
            obj.task
                .as_mut()
                .unwrap()
                .unlease(TaskState::Pending, Some(now));
            origin_mut(&mut doc).insert(id.to_string(), obj);
            (doc, Response::Status(StatusRes { status: 200 }))
        }
    }
}

fn task_fulfill(
    mut doc: Doc,
    id: &str,
    version: u64,
    action: &PromiseSettleReq,
    now: u64,
) -> (Doc, Response) {
    if !action.state.settable() {
        return (
            doc,
            Response::Promise(PromiseRes {
                status: 400,
                promise: None,
            }),
        );
    }
    match held(origin_mut(&mut doc), id, version, now) {
        Err(code) => (
            doc,
            Response::Promise(PromiseRes {
                status: code,
                promise: None,
            }),
        ),
        Ok(()) => {
            let obj = origin_mut(&mut doc).get_mut(id).unwrap();
            obj.promise.state = action.state;
            obj.promise.value = action.value.clone();
            obj.promise.settled_at = Some(now);
            obj.fulfill_task();
            let rec = obj.promise.record(id);
            (
                doc,
                Response::Promise(PromiseRes {
                    status: 200,
                    promise: Some(rec),
                }),
            )
        }
    }
}

fn task_halt(mut doc: Doc, id: &str, now: u64) -> (Doc, Response) {
    let Some(stored) = origin_mut(&mut doc).get(id).cloned() else {
        return (doc, Response::Status(StatusRes { status: 404 }));
    };
    let mut seen = stored.project(now);
    let Some(task) = seen.task.clone() else {
        return (doc, Response::Status(StatusRes { status: 404 }));
    };
    match task.state {
        TaskState::Fulfilled => (doc, Response::Status(StatusRes { status: 409 })),
        TaskState::Halted => (doc, Response::Status(StatusRes { status: 200 })),
        _ => {
            seen.task.as_mut().unwrap().unlease(TaskState::Halted, None);
            origin_mut(&mut doc).insert(id.to_string(), seen);
            (doc, Response::Status(StatusRes { status: 200 }))
        }
    }
}

fn task_continue(mut doc: Doc, id: &str, now: u64) -> (Doc, Response) {
    let Some(stored) = origin_mut(&mut doc).get(id).cloned() else {
        return (doc, Response::Status(StatusRes { status: 404 }));
    };
    let mut seen = stored.project(now);
    let continues = match seen.task.as_ref() {
        None => {
            return (doc, Response::Status(StatusRes { status: 404 }));
        }
        Some(task) => {
            task.state == TaskState::Halted && seen.promise.state == PromiseState::Pending
        }
    };
    if !continues {
        return (doc, Response::Status(StatusRes { status: 409 }));
    }
    {
        let task = seen.task.as_mut().unwrap();
        task.state = TaskState::Pending;
        task.retry_timeout_at = Some(now);
    }
    origin_mut(&mut doc).insert(id.to_string(), seen);
    (doc, Response::Status(StatusRes { status: 200 }))
}

fn heartbeat(mut doc: Doc, pid: &str, tasks: &[echod_types::TaskRef], now: u64) -> (Doc, Response) {
    if tasks.is_empty() {
        return (doc, Response::Status(StatusRes { status: 200 }));
    }
    let origin = origin_of(&tasks[0].id);
    if tasks.iter().any(|t| origin_of(&t.id) != origin) {
        return (doc, Response::Status(StatusRes { status: 400 }));
    }
    let map = origin_mut(&mut doc);
    for task_ref in tasks {
        if let Some(stored) = map.get(&task_ref.id).cloned() {
            let mut seen = stored.project(now);
            let extends = seen.task.as_ref().is_some_and(|task| {
                task.state == TaskState::Acquired
                    && task.version == task_ref.version
                    && task.pid.as_deref() == Some(pid)
            });
            if extends {
                let ttl = seen.task.as_ref().unwrap().ttl.unwrap_or(0);
                seen.task.as_mut().unwrap().lease_timeout_at = Some(now.saturating_add(ttl));
                map.insert(task_ref.id.clone(), seen);
            }
        }
    }
    (doc, Response::Status(StatusRes { status: 200 }))
}

fn suspend(
    mut doc: Doc,
    id: &str,
    version: u64,
    actions: &[echod_types::PromiseRegisterCallbackReq],
    now: u64,
) -> (Doc, Response) {
    if actions.is_empty()
        || actions
            .iter()
            .any(|a| a.awaited == id || !same_origin(&a.awaited, &id.to_string()))
    {
        return (doc, Response::Status(StatusRes { status: 400 }));
    }
    let mut seen = Vec::new();
    for action in actions {
        if seen.contains(&action.awaited) {
            return (doc, Response::Status(StatusRes { status: 400 }));
        }
        seen.push(action.awaited.clone());
    }
    match held(origin_mut(&mut doc), id, version, now) {
        Err(code) => (doc, Response::Status(StatusRes { status: code })),
        Ok(()) => {
            let map = origin_mut(&mut doc);
            let mut any_settled = false;
            for action in actions {
                let Some(awaited) = map.get(&action.awaited) else {
                    return (doc, Response::Status(StatusRes { status: 422 }));
                };
                let seen = awaited.project(now);
                if !awaitable(&seen.promise.tags) {
                    return (doc, Response::Status(StatusRes { status: 422 }));
                }
                if seen.promise.state != PromiseState::Pending {
                    any_settled = true;
                }
            }
            if any_settled {
                if let Some(task) = map.get_mut(id).and_then(|o| o.task.as_mut()) {
                    task.resumes.clear();
                }
                return (doc, Response::Status(StatusRes { status: 300 }));
            }
            for action in actions {
                if let Some(stored) = map.get(&action.awaited).cloned() {
                    let mut awaited = stored.project(now);
                    if !awaited.promise.callbacks.contains(&id.to_string()) {
                        awaited.promise.callbacks.push(id.to_string());
                    }
                    map.insert(action.awaited.clone(), awaited);
                }
            }
            if let Some(task) = map.get_mut(id).and_then(|o| o.task.as_mut()) {
                task.unlease(TaskState::Suspended, None);
                task.resumes.clear();
            }
            (doc, Response::Status(StatusRes { status: 200 }))
        }
    }
}

fn fence(
    mut doc: Doc,
    id: &str,
    version: u64,
    action: &TaskFenceAction,
    now: u64,
) -> (Doc, Response) {
    let target = match action {
        TaskFenceAction::Create(c) => c.id.as_str(),
        TaskFenceAction::Settle(s) => s.id.as_str(),
    };
    if target == id || !same_origin(&target.to_string(), &id.to_string()) {
        return (
            doc,
            Response::TaskFence(TaskFenceRes {
                status: 400,
                action: None,
            }),
        );
    }
    match held(origin_mut(&mut doc), id, version, now) {
        Err(code) => (
            doc,
            Response::TaskFence(TaskFenceRes {
                status: code,
                action: None,
            }),
        ),
        Ok(()) => match action {
            TaskFenceAction::Create(req) => {
                let (doc, response) = promise_create(doc, req, now);
                let Response::Promise(inner) = response else {
                    unreachable!()
                };
                (
                    doc,
                    Response::TaskFence(TaskFenceRes {
                        status: 200,
                        action: Some(TaskFenceInnerRes::Create(inner)),
                    }),
                )
            }
            TaskFenceAction::Settle(req) => {
                let (doc, response) = promise_settle(doc, req, now);
                let Response::Promise(inner) = response else {
                    unreachable!()
                };
                (
                    doc,
                    Response::TaskFence(TaskFenceRes {
                        status: 200,
                        action: Some(TaskFenceInnerRes::Settle(inner)),
                    }),
                )
            }
        },
    }
}

fn fence_check(mut doc: Doc, id: &str, version: u64, now: u64) -> (Doc, Response) {
    match held(origin_mut(&mut doc), id, version, now) {
        Err(code) => (doc, Response::Status(StatusRes { status: code })),
        Ok(()) => (doc, Response::Status(StatusRes { status: 200 })),
    }
}

fn schedule_get(doc: Doc, id: &str) -> (Doc, Response) {
    match &doc {
        Doc::Schedule(Some(schedule)) if schedule.id == id => (
            doc.clone(),
            Response::Schedule(ScheduleRes {
                status: 200,
                schedule: Some(schedule.clone()),
            }),
        ),
        _ => (
            doc,
            Response::Schedule(ScheduleRes {
                status: 404,
                schedule: None,
            }),
        ),
    }
}

fn schedule_create(doc: Doc, req: &echod_types::ScheduleCreateReq, now: u64) -> (Doc, Response) {
    if targeted(&req.promise_tags) && timer(&req.promise_tags) {
        return (
            doc,
            Response::Schedule(ScheduleRes {
                status: 400,
                schedule: None,
            }),
        );
    }
    let existing = match &doc {
        Doc::Schedule(Some(schedule)) => Some(schedule.clone()),
        _ => None,
    };
    if let Some(schedule) = existing {
        return (
            doc,
            Response::Schedule(ScheduleRes {
                status: 200,
                schedule: Some(schedule),
            }),
        );
    }
    let schedule = Schedule {
        id: req.id.clone(),
        cron: req.cron.clone(),
        promise_id: req.promise_id.clone(),
        promise_timeout: req.promise_timeout,
        promise_param: req.promise_param.clone(),
        promise_tags: req.promise_tags.clone(),
        next_run_at: echod_cron::next_run_at(&req.cron, now),
        last_run_at: None,
        created_at: now,
    };
    (
        Doc::Schedule(Some(schedule.clone())),
        Response::Schedule(ScheduleRes {
            status: 200,
            schedule: Some(schedule),
        }),
    )
}

fn schedule_delete(doc: Doc, id: &str) -> (Doc, Response) {
    match &doc {
        Doc::Schedule(Some(schedule)) if schedule.id == id => (
            Doc::Schedule(None),
            Response::Status(StatusRes { status: 200 }),
        ),
        _ => (doc, Response::Status(StatusRes { status: 404 })),
    }
}

fn held(map: &BTreeMap<String, Obj>, id: &str, version: u64, now: u64) -> Result<(), u16> {
    let Some(obj) = map.get(id) else {
        return Err(404);
    };
    let seen = obj.project(now);
    let Some(task) = &seen.task else {
        return Err(404);
    };
    if task.state != TaskState::Acquired
        || task.version != version
        || seen.promise.state != PromiseState::Pending
    {
        Err(409)
    } else {
        Ok(())
    }
}

fn run_due(mut doc: Doc, now: u64, retry_timeout: u64) -> (Doc, Vec<Pending>, Vec<Outbound>) {
    match &mut doc {
        Doc::Schedule(Some(schedule)) if schedule.next_run_at <= now => {
            let at = schedule.next_run_at;
            let promise = expand(&schedule.promise_id, &schedule.id, at);
            let pending = Pending {
                promise,
                at,
                timeout: schedule.promise_timeout,
                param: schedule.promise_param.clone(),
                tags: schedule.promise_tags.clone(),
            };
            schedule.last_run_at = Some(at);
            schedule.next_run_at = echod_cron::next_run_at(&schedule.cron, at);
            (doc, vec![pending], Vec::new())
        }
        Doc::Origin(map) => {
            let notify = if let Some(id) = map
                .keys()
                .cloned()
                .find(|id| map.get(id).is_some_and(|obj| obj.due(now).is_some()))
            {
                step_object(map, &id, now, retry_timeout)
            } else {
                Vec::new()
            };
            (doc, Vec::new(), notify)
        }
        _ => (doc, Vec::new(), Vec::new()),
    }
}

fn create_occurrence(mut doc: Doc, pending: &Pending, now: u64) -> Doc {
    let map = origin_mut(&mut doc);
    if map.contains_key(&pending.promise) || now < pending.at {
        return doc;
    }
    let timeout_at = pending.at.saturating_add(pending.timeout);
    let runnable = targeted(&pending.tags) && !timer(&pending.tags);
    let obj = new_object(
        &pending.promise,
        timeout_at,
        now,
        pending.param.clone(),
        pending.tags.clone(),
        runnable,
    );
    // A schedule occurrence is created as of its fire instant. `new_object`
    // anchors a request at `now`; shift the birth instant back to `at` when
    // the deadline is still ahead of the fire, and offer the task from `at`.
    let mut obj = obj;
    if timeout_at > pending.at {
        obj.promise.created_at = pending.at;
    }
    if let Some(task) = obj.task.as_mut() {
        if task.state == TaskState::Pending {
            task.retry_timeout_at = Some(offer_at(&pending.tags, pending.at));
        }
    }
    map.insert(pending.promise.clone(), obj);
    doc
}

fn origin_mut(doc: &mut Doc) -> &mut BTreeMap<String, Obj> {
    if !matches!(doc, Doc::Origin(_)) {
        *doc = Doc::Origin(BTreeMap::new());
    }
    match doc {
        Doc::Origin(map) => map,
        Doc::Schedule(_) => unreachable!(),
    }
}

fn deadline(doc: &Doc) -> Option<u64> {
    match doc {
        Doc::Schedule(Some(schedule)) => Some(schedule.next_run_at),
        Doc::Origin(map) => {
            let mut best: Option<u64> = None;
            for obj in map.values() {
                let consider = |best: &mut Option<u64>, at: u64| {
                    *best = Some(best.map_or(at, |b| b.min(at)));
                };
                if let Some(at) = obj.due(u64::MAX) {
                    consider(&mut best, at);
                }
            }
            best
        }
        _ => None,
    }
}

fn earliest_in(doc: &Doc, now: u64) -> Option<u64> {
    match doc {
        Doc::Schedule(Some(schedule)) if schedule.next_run_at <= now => Some(schedule.next_run_at),
        Doc::Origin(map) => map.values().filter_map(|obj| obj.due(now)).min(),
        _ => None,
    }
}

fn new_object(
    id: &str,
    timeout_at: u64,
    now: u64,
    param: Value,
    tags: Tags,
    runnable: bool,
) -> Obj {
    let _ = id;
    let live = timeout_at > now;
    let state = if live {
        PromiseState::Pending
    } else if timer(&tags) {
        PromiseState::Resolved
    } else {
        PromiseState::RejectedTimedout
    };
    let promise = Prom {
        state,
        param,
        value: Value::empty(),
        tags: tags.clone(),
        timeout_at,
        created_at: if live { now } else { timeout_at },
        settled_at: if live { None } else { Some(timeout_at) },
        callbacks: Vec::new(),
        listeners: Vec::new(),
    };
    let task = if runnable {
        let due = offer_at(&tags, now);
        Some(Tk {
            state: if live {
                TaskState::Pending
            } else {
                TaskState::Fulfilled
            },
            version: 0,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: if live { Some(due) } else { None },
            resumes: Vec::new(),
        })
    } else {
        None
    };
    Obj { promise, task }
}

fn timer(tags: &Tags) -> bool {
    tags.iter()
        .any(|(k, v)| k == "resonate:timer" && v == "true")
}

fn targeted(tags: &Tags) -> bool {
    tags.iter().any(|(k, _)| k == "resonate:target")
}

/// Lean's `otype.awaitable`: a target, global scope, an external tag, or a timer.
fn awaitable(tags: &Tags) -> bool {
    targeted(tags)
        || timer(tags)
        || tags
            .iter()
            .any(|(k, v)| k == "resonate:external" && v == "true")
        || tags
            .iter()
            .any(|(k, v)| k == "resonate:scope" && v == "global")
}

/// The first offer of a task born at `at`: its delay, or `at`.
fn offer_at(tags: &Tags, at: u64) -> u64 {
    delay_of(tags).map(|d| d.max(at)).unwrap_or(at)
}

fn delay_of(tags: &Tags) -> Option<u64> {
    tags.iter()
        .find(|(k, _)| k == "resonate:delay")
        .and_then(|(_, v)| v.parse().ok())
}

fn expand(template: &str, id: &str, at: u64) -> String {
    template
        .replace("{{.id}}", id)
        .replace("{{.timestamp}}", &at.to_string())
}

impl Obj {
    fn project(&self, now: u64) -> Self {
        let mut obj = self.clone();
        obj.project_in_place(now);
        obj
    }

    fn project_in_place(&mut self, now: u64) {
        if self.promise.state == PromiseState::Pending && now >= self.promise.timeout_at {
            self.promise.state = if timer(&self.promise.tags) {
                PromiseState::Resolved
            } else {
                PromiseState::RejectedTimedout
            };
            self.promise.settled_at = Some(self.promise.timeout_at);
        }
        if self.promise.state != PromiseState::Pending {
            self.fulfill_task();
        }
    }

    fn fulfill_task(&mut self) {
        if let Some(task) = self.task.as_mut() {
            if task.state != TaskState::Fulfilled {
                task.state = TaskState::Fulfilled;
                task.pid = None;
                task.ttl = None;
                task.lease_timeout_at = None;
                task.retry_timeout_at = None;
                task.resumes.clear();
            }
        }
    }

    fn due(&self, now: u64) -> Option<u64> {
        let mut best = None;
        let consider = |best: &mut Option<u64>, at: u64| {
            if at <= now {
                *best = Some(best.map_or(at, |b| b.min(at)));
            }
        };
        if self.promise.state == PromiseState::Pending {
            consider(&mut best, self.promise.timeout_at);
        } else if !self.promise.callbacks.is_empty() || !self.promise.listeners.is_empty() {
            consider(&mut best, self.promise.settled_at.unwrap_or(0));
        }
        if let Some(task) = &self.task {
            if self.promise.state == PromiseState::Pending {
                if task.state == TaskState::Acquired {
                    if let Some(at) = task.lease_timeout_at {
                        consider(&mut best, at);
                    }
                }
                if task.state == TaskState::Pending {
                    if let Some(at) = task.retry_timeout_at {
                        consider(&mut best, at);
                    }
                }
            }
        }
        best
    }
}

/// One due step of one object: the promise's deadline, its lease, its retry,
/// one callback it owes, or one listener. A retry offers the task. A listener
/// is told the settled promise. Both are the same boundary outputs the
/// abstract model sends.
fn step_object(map: &mut BTreeMap<String, Obj>, id: &str, now: u64, retry_timeout: u64) -> Vec<Outbound> {
    enum Found {
        Quiet,
        Callback(String, u64),
        Execute {
            version: u64,
        },
        Unblock {
            address: String,
            promise: PromiseRecord,
        },
    }
    let found = {
        let Some(obj) = map.get_mut(id) else {
            return Vec::new();
        };
        if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
            obj.project_in_place(now);
            Found::Quiet
        } else if obj.promise.state == PromiseState::Pending {
            if let Some(task) = obj.task.as_mut() {
                if task.state == TaskState::Acquired
                    && task.lease_timeout_at.is_some_and(|at| at <= now)
                {
                    task.unlease(TaskState::Pending, Some(now));
                    Found::Quiet
                } else if task.state == TaskState::Pending
                    && task.retry_timeout_at.is_some_and(|at| at <= now)
                {
                    let version = task.version;
                    task.retry_timeout_at = Some(now.saturating_add(retry_timeout));
                    Found::Execute { version }
                } else {
                    Found::Quiet
                }
            } else {
                Found::Quiet
            }
        } else if !obj.promise.callbacks.is_empty() {
            let since = obj.promise.settled_at.unwrap_or(0);
            Found::Callback(obj.promise.callbacks.remove(0), since)
        } else if !obj.promise.listeners.is_empty() {
            let address = obj.promise.listeners.remove(0);
            let promise = obj.promise.record(id);
            Found::Unblock { address, promise }
        } else {
            Found::Quiet
        }
    };
    match found {
        Found::Quiet => Vec::new(),
        Found::Execute { version } => vec![Outbound::Execute {
            id: id.to_string(),
            version,
        }],
        Found::Unblock { address, promise } => vec![Outbound::Unblock { address, promise }],
        Found::Callback(awaiter, since) => {
            let awaited = id.to_string();
            if let Some(obj) = map.get_mut(&awaiter) {
                // The awaiter is read through its projection, as Lean's
                // `readTaskObject`: once its own promise is settled its
                // task reads as fulfilled and is left alone.
                let settled = obj.promise.state != PromiseState::Pending
                    || now >= obj.promise.timeout_at;
                if let Some(task) = obj.task.as_mut() {
                    if !settled {
                        resume(task, &awaited, since);
                    }
                }
            }
            Vec::new()
        }
    }
}

/// Resume the awaiter: a suspended task is offered again from `since`, the
/// instant the awaited promise settled.
fn resume(task: &mut Tk, awaited: &str, since: u64) {
    match task.state {
        TaskState::Suspended => {
            task.state = TaskState::Pending;
            task.pid = None;
            task.ttl = None;
            task.lease_timeout_at = None;
            task.retry_timeout_at = Some(since);
            task.resumes = vec![awaited.to_string()];
        }
        TaskState::Fulfilled => {}
        _ => {
            if !task.resumes.iter().any(|id| id == awaited) {
                task.resumes.push(awaited.to_string());
            }
        }
    }
}

impl Prom {
    fn record(&self, id: &str) -> PromiseRecord {
        PromiseRecord {
            id: id.to_string(),
            state: self.state,
            param: self.param.clone(),
            value: self.value.clone(),
            tags: self.tags.clone(),
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
        }
    }
}

impl Tk {
    fn record(&self, id: &str) -> TaskRecord {
        TaskRecord {
            id: id.to_string(),
            state: self.state,
            version: self.version,
            resumes: self.resumes.len() as u64,
            ttl: self.ttl,
            pid: self.pid.clone(),
        }
    }

    fn acquire(&mut self, pid: &str, ttl: u64, now: u64) {
        self.state = TaskState::Acquired;
        self.version = self.version.saturating_add(1);
        self.pid = Some(pid.to_string());
        self.ttl = Some(ttl);
        self.lease_timeout_at = Some(now.saturating_add(ttl));
        self.retry_timeout_at = None;
        self.resumes.clear();
    }

    fn unlease(&mut self, state: TaskState, retry: Option<u64>) {
        self.state = state;
        self.pid = None;
        self.ttl = None;
        self.lease_timeout_at = None;
        self.retry_timeout_at = retry;
    }
}

verus! {

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

/// The exec node is opaque to Verus: its documents live in `BTreeMap`s and
/// its bytes come from serde, neither of which Verus reads. Its view is
/// uninterpreted; the proofs are about `NodeV`, and the link from this
/// machine to that view is not claimed.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExNode(Node);

pub uninterp spec fn node_view(node: Node) -> NodeV;

impl View for Node {
    type V = NodeV;
    closed spec fn view(&self) -> NodeV {
        node_view(*self)
    }
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

pub open spec fn spec_run_due(doc: DocV, now: Time, retry_timeout: u64) -> (DocV, Option<Response>, Seq<PendingV>, Seq<NoteV>) {
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
                    let (map, notes) = spec_step_object(map, id, now, retry_timeout);
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
