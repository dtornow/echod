//! One node, as its own machine. A request or a due document is a flight:
//! load the document, decide, write it back, then answer. The store keeps
//! the bytes. Nothing here calls the abstract model.

use std::collections::{BTreeMap, VecDeque};

use vstd::prelude::*;

use echod_types::{
    origin_of, same_origin, PromiseCreateReq, PromiseRecord, PromiseRes, PromiseSettleReq,
    PromiseState, Request, Response, Schedule, ScheduleRes, StatusRes, Tags, TaskClaimRes,
    TaskFenceAction, TaskFenceInnerRes, TaskFenceRes, TaskGetRes, TaskRecord, TaskState, Value,
};
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};

use crate::store::{fnv1a, Etag, StoreCall, StoreOutcome};

/// How long a pending task waits before it is offered again. Lean's
/// `ServerConfig.retryTimeout`.
const RETRY_TIMEOUT: u64 = 5_000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plane {
    address: u64,
    nodes: u64,
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

impl Plane {
    pub fn new(address: u64, nodes: u64) -> Self {
        Self {
            address,
            nodes: nodes.max(1),
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
                let (next, born, notify) = run_due(doc, now);
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

fn run_due(mut doc: Doc, now: u64) -> (Doc, Vec<Pending>, Vec<Outbound>) {
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
                step_object(map, &id, now)
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
fn step_object(map: &mut BTreeMap<String, Obj>, id: &str, now: u64) -> Vec<Outbound> {
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
                    task.retry_timeout_at = Some(now.saturating_add(RETRY_TIMEOUT));
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

/// The node's documents, as a proof sees them.
pub struct PlaneV {
    pub address: nat,
    pub nodes: nat,
    pub flight: Option<FlightV>,
    pub documents: Seq<CachedV>,
    pub pending: Seq<PendingV>,
    pub next_op: u64,
}

/// The exec plane is opaque to Verus: its documents live in `BTreeMap`s and
/// its bytes come from serde, neither of which Verus reads. Its view is
/// uninterpreted; the proofs are about `PlaneV`, and the link from this
/// machine to that view is not claimed.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExPlane(Plane);

pub uninterp spec fn plane_view(plane: Plane) -> PlaneV;

impl View for Plane {
    type V = PlaneV;
    closed spec fn view(&self) -> PlaneV {
        plane_view(*self)
    }
}

}
