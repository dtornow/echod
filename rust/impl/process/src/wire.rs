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
    if let Some(addr) = d.tags.get("resonate:target") {
        if !resonate_core::is_valid_address(addr) {
            return Err("Invalid resonate:target address".to_string());
        }
    }
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

/// What a status says when nothing more is known of why.
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

/// The status a kernel response carries.
pub fn status_of(r: &k::Response) -> u16 {
    match r {
        k::Response::Promise(p) => p.status,
        k::Response::Schedule(c) => c.status,
        k::Response::Status(st) => st.status,
        k::Response::TaskGet(g) => g.status,
        k::Response::TaskClaim(c) => c.status,
        k::Response::TaskFence(f) => f.status,
    }
}

fn object<'a>(s: &'a k::State, id: &str) -> Option<&'a k::Promise> {
    s.objects.iter().find(|p| p.id == id)
}

/// Why a request was refused, in the words the reference server uses: by
/// kind and status, and where one status has several causes, by the
/// state the step left, which the refusing checks did not change. The
/// kernel proves the status; the words are the protocol's courtesy.
pub fn reason_for(kind: &str, req: &k::Request, status: u16, s: &k::State) -> String {
    let text = match (kind, status) {
        ("promise.get" | "promise.settle", 404) => "Promise not found",
        ("promise.register_callback" | "promise.register_listener", 404) => "Awaited promise not found",
        ("promise.register_callback", 422) => match req {
            k::Request::PromiseRegisterCallback(c) => match object(s, &c.awaiter) {
                None => "Awaiter promise not found",
                Some(w) if k::tags::exec_otype(&w.tags) != k::tags::OType::Runnable => "Awaiter promise has no resonate:target tag",
                Some(_) => "Awaited promise is not awaitable",
            },
            _ => "Awaited promise is not awaitable",
        },
        ("promise.register_listener", 422) => "Awaited promise is not awaitable",
        ("task.get" | "task.acquire" | "task.release" | "task.fulfill" | "task.suspend" | "task.fence" | "task.halt" | "task.continue", 404) => "Task not found",
        ("task.create", 409) => "Already exists",
        ("task.create", 422) => "The promise does not have a resonate:target tag",
        ("task.acquire", 409) => match req {
            k::Request::TaskAcquire(a) => match object(s, &a.id).and_then(|p| p.task.as_ref()) {
                Some(t) if t.state == k::TaskState::Pending => "Version mismatch",
                _ => "Task is not pending",
            },
            _ => "Task is not pending",
        },
        ("task.release" | "task.fulfill", 409) => "Task version mismatch or invalid state",
        ("task.suspend", 409) => "Task is not acquired or version mismatch",
        ("task.suspend", 422) => match req {
            k::Request::TaskSuspend(q) if q.actions.iter().any(|a| object(s, &a.awaited).is_none()) => "Awaited promise not found",
            _ => "Awaited promise is not awaitable",
        },
        ("task.fence", 409) => "Version mismatch",
        ("task.halt", 409) => "Task is fulfilled",
        ("task.continue", 409) => "Task is not halted",
        ("schedule.get" | "schedule.delete", 404) => "Schedule not found",
        _ => reason(status),
    };
    text.to_string()
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

pub fn promise_res(kind: &str, corr_id: &str, r: &k::PromiseRes) -> w::ResponseEnvelope {
    promise_res_with(kind, corr_id, r, None)
}

fn promise_res_with(kind: &str, corr_id: &str, r: &k::PromiseRes, why: Option<&str>) -> w::ResponseEnvelope {
    match &r.promise {
        Some(p) => reply_with(kind, corr_id, r.status, json!({ "promise": promise_out(p) }), why),
        None => reply_with(kind, corr_id, r.status, json!({}), why),
    }
}

pub fn claim_res(kind: &str, corr_id: &str, r: &k::TaskClaimRes) -> w::ResponseEnvelope {
    claim_res_with(kind, corr_id, r, None)
}

fn claim_res_with(kind: &str, corr_id: &str, r: &k::TaskClaimRes, why: Option<&str>) -> w::ResponseEnvelope {
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
pub fn response_out(kind: &str, corr: &str, action_kind: Option<&str>, r: &k::Response, why: Option<&str>) -> w::ResponseEnvelope {
    match r {
        k::Response::Promise(p) => promise_res_with(kind, corr, p, why),
        k::Response::Schedule(c) => match &c.schedule {
            Some(sc) => reply_with(kind, corr, c.status, json!({ "schedule": schedule_out(sc) }), why),
            None => reply_with(kind, corr, c.status, json!({}), why),
        },
        k::Response::Status(st) => {
            let data = if kind == "task.suspend" { json!({ "preload": [] }) } else { json!({}) };
            reply_with(kind, corr, st.status, data, why)
        }
        k::Response::TaskGet(g) => match &g.task {
            Some(t) => reply_with(kind, corr, g.status, json!({ "task": task_out(t) }), why),
            None => reply_with(kind, corr, g.status, json!({}), why),
        },
        k::Response::TaskClaim(c) => claim_res_with(kind, corr, c, why),
        k::Response::TaskFence(f) => match &f.action {
            Some(k::TaskFenceInnerRes::Create(p)) | Some(k::TaskFenceInnerRes::Settle(p)) => {
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

/// A kernel response rendered with its reason: what the node answers, and
/// what the simulator's model answers, so the two compare as equal.
pub fn render(kind: &str, corr: &str, action_kind: Option<&str>, req: &k::Request, r: &k::Response, after: &k::State) -> w::ResponseEnvelope {
    let status = status_of(r);
    let why = (status >= 400).then(|| reason_for(kind, req, status, after));
    response_out(kind, corr, action_kind, r, why.as_deref())
}
