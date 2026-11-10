//! The model's vocabulary on the wire: a request as the protocol carries it,
//! and an answer as the model types it. Shared by the driver and the simulator
//! (`#[path]`).

use std::collections::BTreeMap;

use echod_abstract::types as rows;
use echod_abstract_exec::{PMap, PSet, Promise, Store as Model, Task};
use serde_json::{json, Value};

fn tags_out(t: &rows::Tags) -> Value {
    let mut m = serde_json::Map::new();
    for (k, v) in t {
        m.insert(k.clone(), json!(v));
    }
    Value::Object(m)
}

fn value_out(v: &rows::Value) -> Value {
    let mut m = serde_json::Map::new();
    if let Some(d) = &v.data {
        m.insert("data".into(), json!(d));
    }
    if !v.headers.is_empty() {
        m.insert("headers".into(), tags_out(&v.headers));
    }
    Value::Object(m)
}

fn state_name(s: rows::PromiseState) -> &'static str {
    match s {
        rows::PromiseState::Pending => "pending",
        rows::PromiseState::Resolved => "resolved",
        rows::PromiseState::Rejected => "rejected",
        rows::PromiseState::RejectedCanceled => "rejected_canceled",
        rows::PromiseState::RejectedTimedout => "rejected_timedout",
    }
}

fn create_data(c: &rows::PromiseCreateReq) -> Value {
    json!({ "id": c.id, "timeoutAt": c.timeout_at, "param": value_out(&c.param), "tags": tags_out(&c.tags) })
}

fn settle_data(s: &rows::PromiseSettleReq) -> Value {
    json!({ "id": s.id, "state": state_name(s.state), "value": value_out(&s.value) })
}

fn action(kind: &str, data: Value) -> Value {
    json!({ "kind": kind, "head": {}, "data": data })
}

/// The request as the protocol carries it: kind and data.
pub fn encode(req: &rows::Request, _worker: &str) -> (&'static str, Value) {
    match req {
        rows::Request::PromiseCreate(c) => ("promise.create", create_data(c)),
        rows::Request::PromiseGet(q) => ("promise.get", json!({ "id": q.id })),
        rows::Request::PromiseSettle(s) => ("promise.settle", settle_data(s)),
        rows::Request::PromiseRegisterCallback(c) => ("promise.register_callback", json!({ "awaited": c.awaited, "awaiter": c.awaiter })),
        rows::Request::PromiseRegisterListener(c) => ("promise.register_listener", json!({ "awaited": c.awaited, "address": c.address })),
        rows::Request::TaskGet(q) => ("task.get", json!({ "id": q.id })),
        rows::Request::TaskCreate(t) => ("task.create", json!({ "pid": t.pid, "ttl": t.ttl, "action": action("promise.create", create_data(&t.action)) })),
        rows::Request::TaskAcquire(t) => ("task.acquire", json!({ "id": t.id, "version": t.version, "pid": t.pid, "ttl": t.ttl })),
        rows::Request::TaskRelease(t) => ("task.release", json!({ "id": t.id, "version": t.version })),
        rows::Request::TaskFulfill(t) => ("task.fulfill", json!({ "id": t.id, "version": t.version, "action": action("promise.settle", settle_data(&t.action)) })),
        rows::Request::TaskHeartbeat(h) => ("task.heartbeat", json!({ "pid": h.pid, "tasks": h.tasks.iter().map(|t| json!({ "id": t.id, "version": t.version })).collect::<Vec<_>>() })),
        rows::Request::TaskSuspend(s) => (
            "task.suspend",
            json!({ "id": s.id, "version": s.version, "actions": s.actions.iter().map(|a| action("promise.register_callback", json!({ "awaited": a.awaited, "awaiter": a.awaiter }))).collect::<Vec<_>>() }),
        ),
        rows::Request::TaskFence(f) => {
            let action = match &f.action {
                rows::TaskFenceAction::Create(c) => action("promise.create", create_data(c)),
                rows::TaskFenceAction::Settle(s) => action("promise.settle", settle_data(s)),
            };
            ("task.fence", json!({ "id": f.id, "version": f.version, "action": action }))
        }
        rows::Request::TaskFenceCheck(_) => ("task.fence", json!({})),
        rows::Request::TaskHalt(t) => ("task.halt", json!({ "id": t.id })),
        rows::Request::TaskContinue(t) => ("task.continue", json!({ "id": t.id })),
        rows::Request::ScheduleCreate(c) => (
            "schedule.create",
            json!({ "id": c.id, "cron": c.cron, "promiseId": c.promise_id, "promiseTimeout": c.promise_timeout, "promiseParam": value_out(&c.promise_param), "promiseTags": tags_out(&c.promise_tags) }),
        ),
        rows::Request::ScheduleGet(q) => ("schedule.get", json!({ "id": q.id })),
        rows::Request::ScheduleDelete(q) => ("schedule.delete", json!({ "id": q.id })),
    }
}

fn pstate(s: &str) -> Option<rows::PromiseState> {
    Some(match s {
        "pending" => rows::PromiseState::Pending,
        "resolved" => rows::PromiseState::Resolved,
        "rejected" => rows::PromiseState::Rejected,
        "rejected_canceled" => rows::PromiseState::RejectedCanceled,
        "rejected_timedout" => rows::PromiseState::RejectedTimedout,
        _ => return None,
    })
}

fn tstate(s: &str) -> Option<rows::TaskState> {
    Some(match s {
        "pending" => rows::TaskState::Pending,
        "acquired" => rows::TaskState::Acquired,
        "suspended" => rows::TaskState::Suspended,
        "halted" => rows::TaskState::Halted,
        "fulfilled" => rows::TaskState::Fulfilled,
        _ => return None,
    })
}

fn tags_in(t: &Value) -> rows::Tags {
    let mut v: rows::Tags = t.as_object().into_iter().flatten().filter_map(|(k, val)| val.as_str().map(|s| (k.clone(), s.to_string()))).collect();
    v.sort();
    v
}

fn value_in(v: &Value) -> rows::Value {
    rows::Value { headers: if v["headers"].is_object() { tags_in(&v["headers"]) } else { Vec::new() }, data: v["data"].as_str().map(str::to_string) }
}

pub fn prec(p: &Value) -> Option<rows::PromiseRecord> {
    Some(rows::PromiseRecord {
        id: p["id"].as_str()?.to_string(),
        state: pstate(p["state"].as_str()?)?,
        param: value_in(&p["param"]),
        value: value_in(&p["value"]),
        tags: tags_in(&p["tags"]),
        timeout_at: p["timeoutAt"].as_u64()?,
        created_at: p["createdAt"].as_u64()?,
        settled_at: p["settledAt"].as_u64(),
    })
}

pub fn trec(t: &Value) -> Option<rows::TaskRecord> {
    Some(rows::TaskRecord {
        id: t["id"].as_str()?.to_string(),
        state: tstate(t["state"].as_str()?)?,
        version: t["version"].as_u64()?,
        resumes: t["resumes"].as_u64().unwrap_or(0),
        pid: t["pid"].as_str().map(str::to_string),
        ttl: t["ttl"].as_u64(),
    })
}

pub fn srec(c: &Value) -> Option<rows::Schedule> {
    Some(rows::Schedule {
        id: c["id"].as_str()?.to_string(),
        cron: c["cron"].as_str()?.to_string(),
        promise_id: c["promiseId"].as_str()?.to_string(),
        promise_timeout: c["promiseTimeout"].as_u64()?,
        promise_param: value_in(&c["promiseParam"]),
        promise_tags: tags_in(&c["promiseTags"]),
        created_at: c["createdAt"].as_u64()?,
        next_run_at: c["nextRunAt"].as_u64()?,
        last_run_at: c["lastRunAt"].as_u64(),
    })
}

/// The answer as the model types it. `kind` is the request's kind: each kind
/// answers in one shape, and a refusal carries only its status.
pub fn decode(kind: &str, status: u16, data: &Value) -> rows::Response {
    let promise = (status < 400).then(|| prec(&data["promise"])).flatten();
    let task = (status < 400).then(|| trec(&data["task"])).flatten();
    let schedule = (status < 400).then(|| srec(&data["schedule"])).flatten();
    match kind {
        "promise.get" | "promise.create" | "promise.settle" | "promise.register_callback" | "promise.register_listener" | "task.fulfill" => {
            rows::Response::Promise(rows::PromiseRes { status, promise })
        }
        "schedule.get" | "schedule.create" => rows::Response::Schedule(rows::ScheduleRes { status, schedule }),
        "schedule.delete" | "task.release" | "task.halt" | "task.continue" | "task.heartbeat" | "task.suspend" => rows::Response::Status(rows::StatusRes { status }),
        "task.get" => rows::Response::TaskGet(rows::TaskGetRes { status, task }),
        "task.create" | "task.acquire" => rows::Response::TaskClaim(rows::TaskClaimRes { status, task, promise }),
        "task.fence" => {
            let action = if status == 200 {
                let inner = &data["action"];
                let inner_status = inner["head"]["status"].as_u64().unwrap_or(200) as u16;
                let body = rows::PromiseRes { status: inner_status, promise: prec(&inner["data"]["promise"]) };
                match inner["kind"].as_str() {
                    Some("promise.settle") => Some(rows::TaskFenceInnerRes::Settle(body)),
                    Some("promise.create") => Some(rows::TaskFenceInnerRes::Create(body)),
                    _ => None,
                }
            } else {
                None
            };
            rows::Response::TaskFence(rows::TaskFenceRes { status, action })
        }
        _ => rows::Response::Status(rows::StatusRes { status }),
    }
}

/// The model's state, from echod's snapshot: what the suggestions read.
pub fn model_state(snap: &Value) -> Model {
    let mut promises: PMap<Promise> = PMap::empty();
    let mut callbacks: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for c in snap["callbacks"].as_array().into_iter().flatten() {
        if let (Some(a), Some(w)) = (c["awaited"].as_str(), c["awaiter"].as_str()) {
            callbacks.entry(a.to_string()).or_default().push(w.to_string());
        }
    }
    let mut listeners: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for l in snap["listeners"].as_array().into_iter().flatten() {
        if let (Some(id), Some(a)) = (l["id"].as_str(), l["address"].as_str()) {
            listeners.entry(id.to_string()).or_default().push(a.to_string());
        }
    }
    for p in snap["promises"].as_array().into_iter().flatten() {
        let Some(r) = prec(p) else { continue };
        let mut cbs = PSet::empty();
        for w in callbacks.get(&r.id).into_iter().flatten() {
            cbs.insert(w.clone());
        }
        let mut ls = PSet::empty();
        for a in listeners.get(&r.id).into_iter().flatten() {
            ls.insert(a.clone());
        }
        promises.insert(
            r.id.clone(),
            Promise { state: r.state, value: r.value, param: r.param, timeout_at: r.timeout_at, created_at: r.created_at, settled_at: r.settled_at, tags: r.tags, callbacks: cbs, listeners: ls },
        );
    }
    let mut leases: BTreeMap<String, u64> = BTreeMap::new();
    let mut retries: BTreeMap<String, u64> = BTreeMap::new();
    for t in snap["taskTimeouts"].as_array().into_iter().flatten() {
        if let (Some(id), Some(at)) = (t["id"].as_str(), t["timeout"].as_u64()) {
            match t["type"].as_u64() {
                Some(1) => {
                    leases.insert(id.to_string(), at);
                }
                Some(0) => {
                    retries.insert(id.to_string(), at);
                }
                _ => {}
            }
        }
    }
    let mut tasks: PMap<Task> = PMap::empty();
    for t in snap["tasks"].as_array().into_iter().flatten() {
        let Some(r) = trec(t) else { continue };
        let acquired_at = match (leases.get(&r.id), r.ttl) {
            (Some(at), Some(ttl)) => at.saturating_sub(ttl),
            _ => 0,
        };
        let resumes = (0..r.resumes).map(|i| format!("resume-{i}")).collect();
        tasks.insert(r.id.clone(), Task { state: r.state, version: r.version, pid: r.pid, ttl: r.ttl, acquired_at, retry_timeout_at: retries.get(&r.id).copied(), resumes });
    }
    let mut schedules: PMap<rows::Schedule> = PMap::empty();
    for c in snap["schedules"].as_array().into_iter().flatten() {
        if let Some(c) = srec(c) {
            schedules.insert(c.id.clone(), c);
        }
    }
    Model { promises, tasks, schedules }
}
