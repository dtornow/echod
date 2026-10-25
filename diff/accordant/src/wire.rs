//! The model's vocabulary on the wire: a `resonate::Request` as the protocol
//! carries it, and an answer as the model types it. Shared by the driver and
//! the simulator (`#[path]`).

use std::collections::BTreeMap;

use resonate::{Create, Fenced, PMap, PSet, PState, Promise, PromiseRec, Request, Response, Schedule, Server as Model, TState, Tags, Task, TaskRec};
use serde_json::{json, Value};

pub fn tags(t: &Tags, worker: &str) -> Value {
    let mut m = serde_json::Map::new();
    if t.target {
        m.insert("resonate:target".into(), json!(worker));
    }
    if t.external {
        m.insert("resonate:external".into(), json!("true"));
    }
    if t.timer {
        m.insert("resonate:timer".into(), json!("true"));
    }
    if let Some(d) = t.delay {
        m.insert("resonate:delay".into(), json!(d.to_string()));
    }
    Value::Object(m)
}

pub fn value(data: &Option<String>) -> Value {
    match data {
        Some(d) => json!({ "data": d }),
        None => json!({}),
    }
}

pub fn create_data(c: &Create, worker: &str) -> Value {
    json!({ "id": c.id, "timeoutAt": c.timeout_at, "param": value(&c.data), "tags": tags(&c.tags, worker) })
}

/// The request as the protocol carries it: kind and data.
pub fn encode(req: &Request, worker: &str) -> (&'static str, Value) {
    match req {
        Request::Step(_) => unreachable!("a server's own step is not sent"),
        Request::CreatePromise(c) => ("promise.create", create_data(c, worker)),
        Request::GetPromise(id) => ("promise.get", json!({ "id": id })),
        Request::SettlePromise(s) => ("promise.settle", json!({ "id": s.id, "state": s.state, "value": value(&s.data) })),
        Request::RegisterCallback { awaited, awaiter } => ("promise.register_callback", json!({ "awaited": awaited, "awaiter": awaiter })),
        Request::RegisterListener { awaited, address } => ("promise.register_listener", json!({ "awaited": awaited, "address": address })),
        Request::GetTask(id) => ("task.get", json!({ "id": id })),
        Request::CreateTask { pid, ttl, action } => ("task.create", json!({ "pid": pid, "ttl": ttl, "action": { "kind": "promise.create", "head": {}, "data": create_data(action, worker) } })),
        Request::AcquireTask { id, version, pid, ttl } => ("task.acquire", json!({ "id": id, "version": version, "pid": pid, "ttl": ttl })),
        Request::ReleaseTask { id, version } => ("task.release", json!({ "id": id, "version": version })),
        Request::FulfillTask { id, version, state, data } => ("task.fulfill", json!({ "id": id, "version": version, "action": { "kind": "promise.settle", "head": {}, "data": { "id": id, "state": state, "value": value(data) } } })),
        Request::HeartbeatTask { pid, tasks } => ("task.heartbeat", json!({ "pid": pid, "tasks": tasks.iter().map(|t| json!({ "id": t.id, "version": t.version })).collect::<Vec<_>>() })),
        Request::SuspendTask { id, version, awaited } => (
            "task.suspend",
            json!({ "id": id, "version": version, "actions": awaited.iter().map(|a| json!({ "kind": "promise.register_callback", "head": {}, "data": { "awaited": a, "awaiter": id } })).collect::<Vec<_>>() }),
        ),
        Request::FenceTask { id, version, action } => {
            let action = match action {
                Fenced::Create(c) => json!({ "kind": "promise.create", "head": {}, "data": create_data(c, worker) }),
                Fenced::Settle(s) => json!({ "kind": "promise.settle", "head": {}, "data": { "id": s.id, "state": s.state, "value": value(&s.data) } }),
            };
            ("task.fence", json!({ "id": id, "version": version, "action": action }))
        }
        Request::HaltTask(id) => ("task.halt", json!({ "id": id })),
        Request::ContinueTask(id) => ("task.continue", json!({ "id": id })),
        Request::CreateSchedule(c) => (
            "schedule.create",
            json!({ "id": c.id, "cron": c.cron, "promiseId": c.promise_id, "promiseTimeout": c.promise_timeout, "promiseParam": value(&c.promise_param), "promiseTags": tags(&c.promise_tags, worker) }),
        ),
        Request::GetSchedule(id) => ("schedule.get", json!({ "id": id })),
        Request::DeleteSchedule(id) => ("schedule.delete", json!({ "id": id })),
    }
}

pub fn pstate(s: &str) -> Option<PState> {
    Some(match s {
        "pending" => PState::Pending,
        "resolved" => PState::Resolved,
        "rejected" => PState::Rejected,
        "rejected_canceled" => PState::Canceled,
        "rejected_timedout" => PState::TimedOut,
        _ => return None,
    })
}

pub fn tstate(s: &str) -> Option<TState> {
    Some(match s {
        "pending" => TState::Pending,
        "acquired" => TState::Acquired,
        "suspended" => TState::Suspended,
        "halted" => TState::Halted,
        "fulfilled" => TState::Fulfilled,
        _ => return None,
    })
}

pub fn tags_in(t: &Value) -> Tags {
    Tags {
        target: !t["resonate:target"].is_null(),
        external: t["resonate:external"].as_str() == Some("true"),
        timer: t["resonate:timer"].as_str() == Some("true"),
        delay: t["resonate:delay"].as_str().and_then(|d| d.parse().ok()),
    }
}

pub fn prec(p: &Value) -> Option<PromiseRec> {
    Some(PromiseRec {
        id: p["id"].as_str()?.to_string(),
        state: pstate(p["state"].as_str()?)?,
        param: p["param"]["data"].as_str().map(str::to_string),
        value: p["value"]["data"].as_str().map(str::to_string),
        timeout_at: p["timeoutAt"].as_u64()?,
        created_at: p["createdAt"].as_u64()?,
        settled_at: p["settledAt"].as_u64(),
        tags: tags_in(&p["tags"]),
    })
}

pub fn trec(t: &Value) -> Option<TaskRec> {
    Some(TaskRec {
        id: t["id"].as_str()?.to_string(),
        state: tstate(t["state"].as_str()?)?,
        version: t["version"].as_u64()? as u32,
        pid: t["pid"].as_str().map(str::to_string),
        ttl: t["ttl"].as_u64(),
        resumes: t["resumes"].as_u64().unwrap_or(0) as u32,
    })
}

pub fn srec(c: &Value) -> Option<Schedule> {
    Some(Schedule {
        id: c["id"].as_str()?.to_string(),
        cron: c["cron"].as_str()?.to_string(),
        promise_id: c["promiseId"].as_str()?.to_string(),
        promise_timeout: c["promiseTimeout"].as_u64()?,
        promise_param: c["promiseParam"]["data"].as_str().map(str::to_string),
        promise_tags: tags_in(&c["promiseTags"]),
        created_at: c["createdAt"].as_u64()?,
        next_run_at: c["nextRunAt"].as_u64()?,
        last_run_at: c["lastRunAt"].as_u64(),
    })
}

/// The answer as the model types it.
pub fn decode(kind: &str, status: u16, data: &Value) -> Response {
    if status != 200 {
        return Response::Status(status);
    }
    // a fence answers 200 with its action's own envelope inside; the model
    // types the fence as that action's status
    if kind == "task.fence" {
        if let Some(inner) = data["action"]["head"]["status"].as_u64() {
            if inner != 200 {
                return Response::Status(inner as u16);
            }
        }
    }
    let body = if kind == "task.fence" { &data["action"]["data"] } else { data };
    if kind.starts_with("schedule.") {
        return match srec(&body["schedule"]) {
            Some(c) => Response::Schedule(c),
            None => Response::Status(status),
        };
    }
    match (prec(&body["promise"]), trec(&body["task"])) {
        (Some(p), Some(t)) => Response::Both(p, t),
        (None, Some(t)) => Response::Task(t),
        (Some(p), None) => Response::Promise(p),
        (None, None) => Response::Status(status),
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
                Some(1) => leases.insert(id.to_string(), at),
                Some(0) => retries.insert(id.to_string(), at),
                _ => None,
            };
        }
    }
    let mut tasks: PMap<Task> = PMap::empty();
    for t in snap["tasks"].as_array().into_iter().flatten() {
        let Some(r) = trec(t) else { continue };
        let acquired_at = match (leases.get(&r.id), r.ttl) {
            (Some(at), Some(ttl)) => at.saturating_sub(ttl),
            _ => 0,
        };
        // the count is what the record carries; the ids are not
        let resumes = (0..r.resumes).map(|i| format!("resume-{i}")).collect();
        tasks.insert(r.id.clone(), Task { state: r.state, version: r.version, pid: r.pid, ttl: r.ttl, acquired_at, retry_at: retries.get(&r.id).copied(), resumes });
    }
    let mut schedules: PMap<Schedule> = PMap::empty();
    for c in snap["schedules"].as_array().into_iter().flatten() {
        if let Some(c) = srec(c) {
            schedules.insert(c.id.clone(), c);
        }
    }
    Model { promises, tasks, schedules }
}

