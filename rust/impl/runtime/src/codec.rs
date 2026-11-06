//! A document's rows to the protocol, and back.
//!
//! The rows keep tags and headers as ordered pairs and durations as `u64`;
//! the protocol carries maps and `i64`. Everything that crosses is here.
//! The decision core never sees an envelope: it answers with an `Answer`
//! and sends a `Message`, and this file renders both.

use std::collections::HashMap;

use echod_logic::doc::codec::{self, Promise};
use echod_logic::verified as rows;
use resonate_core::types as w;
use serde_json::{json, Value};

pub fn pairs(m: &HashMap<String, String>) -> Vec<(String, String)> {
    let mut v: Vec<(String, String)> = m.iter().map(|(a, b)| (a.clone(), b.clone())).collect();
    v.sort();
    v
}

/// The tags a promise is created with.
///
/// One concession to the SDKs as they are: a sleep is created as a timer
/// *with* a target, because older servers armed only targeted promises and
/// the worker dropped the task that came with it. The specification arms a
/// timer on its own and refuses a targeted timer, so the target is dropped
/// here: the sleep is an external promise, armed, with no task.
pub fn create_tags(m: &HashMap<String, String>) -> Vec<(String, String)> {
    let timer = m.get("resonate:timer").map(String::as_str) == Some("true");
    let mut v: Vec<(String, String)> = m.iter().filter(|(k, _)| !(timer && k.as_str() == "resonate:target")).map(|(a, b)| (a.clone(), b.clone())).collect();
    v.sort();
    v
}

pub fn map(v: &[(String, String)]) -> HashMap<String, String> {
    v.iter().cloned().collect()
}

pub fn value_in(v: &w::PromiseValue) -> rows::Value {
    rows::Value { headers: v.headers.as_ref().map(pairs).unwrap_or_default(), data: v.data.clone() }
}

pub fn value_out(v: &rows::Value) -> w::PromiseValue {
    w::PromiseValue { headers: if v.headers.is_empty() { None } else { Some(map(&v.headers)) }, data: v.data.clone() }
}

pub fn promise_out(r: &rows::PromiseRecord) -> w::PromiseRecord {
    w::PromiseRecord {
        id: r.id.clone(),
        state: state_out(r.state),
        param: value_out(&r.param),
        value: value_out(&r.value),
        tags: map(&r.tags),
        timeout_at: r.timeout_at as i64,
        created_at: r.created_at as i64,
        settled_at: r.settled_at.map(|x| x as i64),
    }
}

pub fn task_out(r: &rows::TaskRecord) -> w::TaskRecord {
    w::TaskRecord {
        id: r.id.clone(),
        state: task_state_out(r.state),
        version: r.version as i64,
        resumes: r.resumes as i64,
        ttl: r.ttl.map(|x| x as i64),
        pid: r.pid.clone(),
    }
}

pub fn schedule_out(c: &rows::Schedule) -> w::ScheduleRecord {
    w::ScheduleRecord {
        id: c.id.clone(),
        cron: c.cron.clone(),
        promise_id: c.promise_id.clone(),
        promise_timeout: c.promise_timeout as i64,
        promise_param: value_out(&c.promise_param),
        promise_tags: map(&c.promise_tags),
        created_at: c.created_at as i64,
        next_run_at: c.next_run_at as i64,
        last_run_at: c.last_run_at.map(|x| x as i64),
    }
}

pub fn state_out(s: rows::PromiseState) -> w::PromiseState {
    match s {
        rows::PromiseState::Pending => w::PromiseState::Pending,
        rows::PromiseState::Resolved => w::PromiseState::Resolved,
        rows::PromiseState::Rejected => w::PromiseState::Rejected,
        rows::PromiseState::RejectedCanceled => w::PromiseState::RejectedCanceled,
        rows::PromiseState::RejectedTimedout => w::PromiseState::RejectedTimedout,
    }
}

pub fn settle_in(s: w::SettleState) -> rows::PromiseState {
    match s {
        w::SettleState::Resolved => rows::PromiseState::Resolved,
        w::SettleState::Rejected => rows::PromiseState::Rejected,
        w::SettleState::RejectedCanceled => rows::PromiseState::RejectedCanceled,
    }
}

pub fn task_state_out(s: rows::TaskState) -> w::TaskState {
    match s {
        rows::TaskState::Pending => w::TaskState::Pending,
        rows::TaskState::Acquired => w::TaskState::Acquired,
        rows::TaskState::Suspended => w::TaskState::Suspended,
        rows::TaskState::Halted => w::TaskState::Halted,
        rows::TaskState::Fulfilled => w::TaskState::Fulfilled,
    }
}

/// A non-negative `i64`, or the field that was not.
pub fn nat(v: i64, field: &str) -> Result<u64, String> {
    u64::try_from(v).map_err(|_| format!("{field} must be non-negative"))
}

pub fn create_in(d: &w::PromiseCreateData) -> Result<rows::PromiseCreateReq, String> {
    if let Some(addr) = d.tags.get("resonate:target") {
        if !resonate_core::is_valid_address(addr) {
            return Err("Invalid resonate:target address".to_string());
        }
    }
    Ok(rows::PromiseCreateReq {
        id: d.id.clone(),
        timeout_at: nat(d.timeout_at, "timeoutAt")?,
        param: value_in(&d.param),
        tags: create_tags(&d.tags),
    })
}

pub fn settle_in_req(d: &w::PromiseSettleData) -> rows::PromiseSettleReq {
    rows::PromiseSettleReq { id: d.id.clone(), state: settle_in(d.state), value: value_in(&d.value) }
}

/// The record a promise's row exposes, as the wire carries it.
pub fn promise_record(p: &Promise) -> w::PromiseRecord {
    promise_out(&rows::PromiseRecord {
        id: p.id.clone(),
        state: p.state,
        param: p.param.clone(),
        value: p.value.clone(),
        tags: p.tags.clone(),
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    })
}

pub fn message(address: &str, outgoing: &echod_logic::Message, server_url: &str) -> (String, w::Message) {
    let msg = match outgoing {
        echod_logic::Message::Execute { task_id, version } => w::Message::Execute(w::ExecuteMsg {
            kind: "execute".to_string(),
            head: w::MessageHead { server_url: server_url.to_string() },
            data: w::ExecuteMsgData { task: w::ExecuteMsgTask { id: task_id.clone(), version: *version as i64 } },
        }),
        echod_logic::Message::Unblock(r) => w::Message::Unblock(w::UnblockMsg {
            kind: "unblock".to_string(),
            head: w::UnblockMsgHead {},
            data: w::UnblockMsgData { promise: promise_out(r) },
        }),
    };
    (address.to_string(), msg)
}

/// What a status says when nothing more is known of why.
fn reason(status: u16) -> &'static str {
    echod_logic::reason::reason(status)
}

/// An envelope: `data` for a successful status, the reason otherwise,
/// which is what every client expects of an error.
pub fn reply(kind: &str, corr_id: &str, status: u16, data: Value) -> w::ResponseEnvelope {
    reply_with(kind, corr_id, status, data, None)
}

fn reply_with(kind: &str, corr_id: &str, status: u16, data: Value, why: Option<&str>) -> w::ResponseEnvelope {
    let data = if status >= 400 { Value::String(why.unwrap_or(reason(status)).to_string()) } else { data };
    w::ResponseEnvelope::new(kind.to_string(), corr_id.to_string(), status as i32, data)
}

pub fn promise_res(kind: &str, corr_id: &str, r: &rows::PromiseRes) -> w::ResponseEnvelope {
    promise_res_with(kind, corr_id, r, None)
}

fn promise_res_with(kind: &str, corr_id: &str, r: &rows::PromiseRes, why: Option<&str>) -> w::ResponseEnvelope {
    match &r.promise {
        Some(p) => reply_with(kind, corr_id, r.status, json!({ "promise": promise_out(p) }), why),
        None => reply_with(kind, corr_id, r.status, json!({}), why),
    }
}

pub fn claim_res(kind: &str, corr_id: &str, r: &rows::TaskClaimRes) -> w::ResponseEnvelope {
    claim_res_with(kind, corr_id, r, None)
}

fn claim_res_with(kind: &str, corr_id: &str, r: &rows::TaskClaimRes, why: Option<&str>) -> w::ResponseEnvelope {
    match (&r.task, &r.promise) {
        (Some(t), Some(p)) => reply_with(kind, corr_id, r.status, json!({ "task": task_out(t), "promise": promise_out(p), "preload": Value::Array(vec![]) }), why),
        _ => reply_with(kind, corr_id, r.status, json!({}), why),
    }
}

pub fn status_res(kind: &str, corr_id: &str, status: u16, data: Value) -> w::ResponseEnvelope {
    reply(kind, corr_id, status, data)
}

/// Any kernel response as the protocol's envelope. A fence's inner action is
/// rendered under its own kind; a suspend carries an empty preload. `why`
/// is the reason a refusal carries, when known.
pub fn response_out(kind: &str, corr: &str, action_kind: Option<&str>, r: &rows::Response, why: Option<&str>) -> w::ResponseEnvelope {
    match r {
        rows::Response::Promise(p) => promise_res_with(kind, corr, p, why),
        rows::Response::Schedule(c) => match &c.schedule {
            Some(sc) => reply_with(kind, corr, c.status, json!({ "schedule": schedule_out(sc) }), why),
            None => reply_with(kind, corr, c.status, json!({}), why),
        },
        rows::Response::Status(st) => {
            let data = if kind == "task.suspend" { json!({ "preload": [] }) } else { json!({}) };
            reply_with(kind, corr, st.status, data, why)
        }
        rows::Response::TaskGet(g) => match &g.task {
            Some(t) => reply_with(kind, corr, g.status, json!({ "task": task_out(t) }), why),
            None => reply_with(kind, corr, g.status, json!({}), why),
        },
        rows::Response::TaskClaim(c) => claim_res_with(kind, corr, c, why),
        rows::Response::TaskFence(f) => match &f.action {
            Some(rows::TaskFenceInnerRes::Create(p)) | Some(rows::TaskFenceInnerRes::Settle(p)) => {
                let inner_kind = action_kind.unwrap_or("");
                let inner_why = (p.status >= 400).then(|| match (inner_kind, p.status) {
                    ("promise.settle", 404) | ("promise.create", 404) => "Promise not found",
                    _ => reason(p.status),
                });
                let inner = promise_res_with(inner_kind, corr, p, inner_why);
                reply_with(kind, corr, f.status, json!({ "action": inner, "preload": [] }), why)
            }
            None => reply_with(kind, corr, f.status, json!({}), why),
        },
    }
}

/// An answer from the core as the protocol's envelope.
pub fn envelope(answer: &echod_logic::Answer) -> w::ResponseEnvelope {
    match answer {
        echod_logic::Answer::Step { kind, corr, action_kind, response, why } => response_out(kind, corr, action_kind.as_deref(), response, why.as_deref()),
        echod_logic::Answer::Debug { kind, corr, status, body } => {
            if *status >= 400 {
                let msg = match body {
                    echod_logic::DebugBody::Message(s) => s.clone(),
                    _ => reason(*status).to_string(),
                };
                return w::ResponseEnvelope::error(kind.clone(), corr.clone(), *status as i32, &msg);
            }
            let data = match body {
                echod_logic::DebugBody::Object => json!({}),
                echod_logic::DebugBody::List => json!([]),
                echod_logic::DebugBody::Message(s) => Value::String(s.clone()),
                echod_logic::DebugBody::Snap { origins, schedules } => {
                    let promises: Vec<Promise> = origins.iter().flat_map(codec::promises).collect();
                    snapshot(&promises, schedules)
                },
            };
            w::ResponseEnvelope::new(kind.clone(), corr.clone(), *status as i32, data)
        }
    }
}

/// The protocol's `Snapshot` of a set of promise rows: the records, the
/// callbacks and listeners they hold, their tasks, and the deadlines they
/// owe. Messages are never queued here: they are routed as they arise.
fn snapshot(promises: &[Promise], schedules: &[rows::Schedule]) -> Value {
    let mut schedules: Vec<&rows::Schedule> = schedules.iter().collect();
    schedules.sort_by(|a, b| a.id.cmp(&b.id));
    let schedules: Vec<Value> = schedules.iter().map(|c| serde_json::to_value(schedule_out(c)).unwrap_or(Value::Null)).collect();
    let mut promises: Vec<&Promise> = promises.iter().collect();
    promises.sort_by(|a, b| a.id.cmp(&b.id));
    let records: Vec<Value> = promises.iter().map(|p| serde_json::to_value(promise_record(p)).unwrap_or(Value::Null)).collect();
    let mut callbacks: Vec<Value> = Vec::new();
    let mut listeners: Vec<Value> = Vec::new();
    let mut tasks: Vec<Value> = Vec::new();
    let mut promise_timeouts: Vec<Value> = Vec::new();
    let mut task_timeouts: Vec<Value> = Vec::new();
    for p in &promises {
        for awaiter in &p.callbacks {
            callbacks.push(json!({ "awaiter": awaiter, "awaited": p.id }));
        }
        for address in &p.listeners {
            listeners.push(json!({ "id": p.id, "address": address }));
        }
        if p.state == rows::PromiseState::Pending && awaitable(&p.tags) {
            promise_timeouts.push(json!({ "id": p.id, "timeout": p.timeout_at }));
        }
        if let Some(t) = &p.task {
            let record = rows::TaskRecord { id: p.id.clone(), state: t.state, version: t.version, resumes: t.resumes.len() as u64, ttl: t.ttl, pid: t.pid.clone() };
            tasks.push(serde_json::to_value(task_out(&record)).unwrap_or(Value::Null));
            if let Some(at) = t.lease_timeout_at {
                task_timeouts.push(json!({ "id": p.id, "type": 1, "timeout": at }));
            }
            if let Some(at) = t.retry_timeout_at {
                task_timeouts.push(json!({ "id": p.id, "type": 0, "timeout": at }));
            }
        }
    }
    json!({
        "promises": records,
        "promiseTimeouts": promise_timeouts,
        "callbacks": callbacks,
        "listeners": listeners,
        "tasks": tasks,
        "taskTimeouts": task_timeouts,
        "schedules": schedules,
        "messages": [],
    })
}

/// A promise another may wait on: targeted, global in scope, marked
/// external, or a timer. Its timeout is a deadline the document owes.
fn awaitable(tags: &rows::Tags) -> bool {
    let is = |k: &str, v: &str| tags.iter().any(|(a, b)| a == k && b == v);
    tags.iter().any(|(k, _)| k == "resonate:target") || is("resonate:scope", "global") || is("resonate:external", "true") || is("resonate:timer", "true")
}
