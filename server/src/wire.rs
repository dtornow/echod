//! The kernel's vocabulary to the protocol's and back.
//!
//! The kernel keeps tags and headers as ordered pairs and durations as `u64`;
//! the protocol carries maps and `i64`. Everything that crosses is here.

use std::collections::HashMap;

use echod_kernel as k;
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

pub fn value_in(v: &w::PromiseValue) -> k::Value {
    k::Value { headers: v.headers.as_ref().map(pairs).unwrap_or_default(), data: v.data.clone() }
}

pub fn value_out(v: &k::Value) -> w::PromiseValue {
    w::PromiseValue { headers: if v.headers.is_empty() { None } else { Some(map(&v.headers)) }, data: v.data.clone() }
}

pub fn promise_out(r: &k::PromiseRecord) -> w::PromiseRecord {
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

pub fn task_out(r: &k::TaskRecord) -> w::TaskRecord {
    w::TaskRecord {
        id: r.id.clone(),
        state: task_state_out(r.state),
        version: r.version as i64,
        resumes: r.resumes as i64,
        ttl: r.ttl.map(|x| x as i64),
        pid: r.pid.clone(),
    }
}

pub fn schedule_out(c: &k::Schedule) -> w::ScheduleRecord {
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

pub fn state_out(s: k::PromiseState) -> w::PromiseState {
    match s {
        k::PromiseState::Pending => w::PromiseState::Pending,
        k::PromiseState::Resolved => w::PromiseState::Resolved,
        k::PromiseState::Rejected => w::PromiseState::Rejected,
        k::PromiseState::RejectedCanceled => w::PromiseState::RejectedCanceled,
        k::PromiseState::RejectedTimedout => w::PromiseState::RejectedTimedout,
    }
}

pub fn settle_in(s: w::SettleState) -> k::PromiseState {
    match s {
        w::SettleState::Resolved => k::PromiseState::Resolved,
        w::SettleState::Rejected => k::PromiseState::Rejected,
        w::SettleState::RejectedCanceled => k::PromiseState::RejectedCanceled,
    }
}

pub fn task_state_out(s: k::TaskState) -> w::TaskState {
    match s {
        k::TaskState::Pending => w::TaskState::Pending,
        k::TaskState::Acquired => w::TaskState::Acquired,
        k::TaskState::Suspended => w::TaskState::Suspended,
        k::TaskState::Halted => w::TaskState::Halted,
        k::TaskState::Fulfilled => w::TaskState::Fulfilled,
    }
}

/// A non-negative `i64`, or the field that was not.
pub fn nat(v: i64, field: &str) -> Result<u64, String> {
    u64::try_from(v).map_err(|_| format!("{field} must be non-negative"))
}

pub fn create_in(d: &w::PromiseCreateData) -> Result<k::PromiseCreateReq, String> {
    Ok(k::PromiseCreateReq {
        id: d.id.clone(),
        timeout_at: nat(d.timeout_at, "timeoutAt")?,
        param: value_in(&d.param),
        tags: create_tags(&d.tags),
    })
}

pub fn settle_in_req(d: &w::PromiseSettleData) -> k::PromiseSettleReq {
    k::PromiseSettleReq { id: d.id.clone(), state: settle_in(d.state), value: value_in(&d.value) }
}

/// The record a kernel promise exposes, as the wire carries it.
pub fn promise_record(p: &k::Promise) -> w::PromiseRecord {
    promise_out(&k::PromiseRecord {
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

/// A kernel outbox entry as the message a worker receives.
pub fn message_out(e: &k::OutboxEntry, server_url: &str) -> (String, w::Message) {
    let msg = match &e.message {
        k::Message::Execute { task_id, version } => w::Message::Execute(w::ExecuteMsg {
            kind: "execute".to_string(),
            head: w::MessageHead { server_url: server_url.to_string() },
            data: w::ExecuteMsgData { task: w::ExecuteMsgTask { id: task_id.clone(), version: *version as i64 } },
        }),
        k::Message::Unblock(r) => w::Message::Unblock(w::UnblockMsg {
            kind: "unblock".to_string(),
            head: w::UnblockMsgHead {},
            data: w::UnblockMsgData { promise: promise_out(r) },
        }),
    };
    (e.address.clone(), msg)
}

/// What a status says when the kernel gives no more than the number.
pub fn reason(status: u16) -> &'static str {
    match status {
        400 => "Bad request",
        403 => "Forbidden",
        404 => "Not found",
        409 => "Conflict",
        422 => "Unprocessable",
        _ => "Error",
    }
}

/// An envelope: `data` for a successful status, a reason string otherwise,
/// which is what every client expects of an error.
pub fn reply(kind: &str, corr_id: &str, status: u16, data: Value) -> w::ResponseEnvelope {
    let data = if status >= 400 { Value::String(reason(status).to_string()) } else { data };
    w::ResponseEnvelope::new(kind.to_string(), corr_id.to_string(), status as i32, data)
}

pub fn promise_res(kind: &str, corr_id: &str, r: &k::PromiseRes) -> w::ResponseEnvelope {
    match &r.promise {
        Some(p) => reply(kind, corr_id, r.status, json!({ "promise": promise_out(p) })),
        None => reply(kind, corr_id, r.status, json!({})),
    }
}

pub fn claim_res(kind: &str, corr_id: &str, r: &k::TaskClaimRes) -> w::ResponseEnvelope {
    match (&r.task, &r.promise) {
        (Some(t), Some(p)) => reply(kind, corr_id, r.status, json!({ "task": task_out(t), "promise": promise_out(p), "preload": Value::Array(vec![]) })),
        _ => reply(kind, corr_id, r.status, json!({})),
    }
}

pub fn status_res(kind: &str, corr_id: &str, status: u16, data: Value) -> w::ResponseEnvelope {
    reply(kind, corr_id, status, data)
}

/// Any kernel response as the protocol's envelope. A fence's inner action is
/// rendered under its own kind; a suspend carries an empty preload.
pub fn response_out(kind: &str, corr: &str, action_kind: Option<&str>, r: &k::Response) -> w::ResponseEnvelope {
    match r {
        k::Response::Promise(p) => promise_res(kind, corr, p),
        k::Response::Schedule(c) => match &c.schedule {
            Some(sc) => status_res(kind, corr, c.status, json!({ "schedule": schedule_out(sc) })),
            None => status_res(kind, corr, c.status, json!({})),
        },
        k::Response::Status(st) => {
            let data = if kind == "task.suspend" { json!({ "preload": [] }) } else { json!({}) };
            status_res(kind, corr, st.status, data)
        }
        k::Response::TaskGet(g) => match &g.task {
            Some(t) => status_res(kind, corr, g.status, json!({ "task": task_out(t) })),
            None => status_res(kind, corr, g.status, json!({})),
        },
        k::Response::TaskClaim(c) => claim_res(kind, corr, c),
        k::Response::TaskFence(f) => match &f.action {
            Some(k::TaskFenceInnerRes::Create(p)) | Some(k::TaskFenceInnerRes::Settle(p)) => {
                let inner = promise_res(action_kind.unwrap_or(""), corr, p);
                status_res(kind, corr, f.status, json!({ "action": inner, "preload": [] }))
            }
            None => status_res(kind, corr, f.status, json!({})),
        },
    }
}
