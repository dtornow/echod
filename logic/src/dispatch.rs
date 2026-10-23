//! The envelope to the kernel's request: the protocol's checks, then the
//! one call the node makes, `handle`, on the document the request names.
//!
//! Pure: an envelope in, a target and a kernel request out, or the error
//! envelope the protocol answers with. The step itself runs in `flight.rs`.

use echod_kernel as k;
use resonate_core::types::{self as w, RequestEnvelope, ResponseEnvelope};
use resonate_core::util;
use serde::de::DeserializeOwned;
use validator::Validate;

use crate::keys::origin_of;
use crate::wire;

/// What a step is run on.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Target {
    Origin(String),
    Schedule(String),
}

impl Target {
    /// The name the keys and the node's decisions go by: the origin, or
    /// `sched:<id>`.
    pub fn name(&self) -> String {
        match self {
            Target::Origin(o) => o.clone(),
            Target::Schedule(id) => format!("sched:{id}"),
        }
    }

    /// The target a timer key's name (`origin` or `sched:<id>`) says.
    pub fn of_name(name: &str) -> Target {
        match name.strip_prefix("sched:") {
            Some(id) => Target::Schedule(id.to_string()),
            None => Target::Origin(name.to_string()),
        }
    }
}

/// A request decoded: where it runs, what the kernel is asked, and, for a
/// fence, the kind its inner action is rendered under.
pub struct Decoded {
    pub target: Target,
    pub request: k::Request,
    pub action_kind: Option<String>,
}

/// Parse and validate a request's `data`.
fn parse<T: DeserializeOwned + Validate>(data: &serde_json::Value) -> Result<T, String> {
    let v: T = serde_json::from_value(data.clone()).map_err(|e| format!("Invalid request data: {e}"))?;
    v.validate().map_err(|e| w::format_validation_errors(&e))?;
    Ok(v)
}

/// The document a request is about. `None` for a request that has none.
/// Schedules are their own objects; the one they fire into is decided when
/// they fire, so a schedule request's "origin" is the schedule's id.
pub fn origin_of_request(req: &RequestEnvelope) -> Result<Option<String>, String> {
    let d = &req.data;
    let id = |k: &str| d.get(k).and_then(|v| v.as_str()).map(|s| s.to_string());
    let origin = match req.kind.as_str() {
        "promise.get" | "promise.create" | "promise.settle" | "task.get" | "task.acquire" | "task.release" | "task.fulfill" | "task.suspend" | "task.fence" | "task.halt" | "task.continue" => {
            id("id").map(|s| origin_of(&s).to_string())
        }
        "promise.register_callback" | "promise.register_listener" => id("awaited").map(|s| origin_of(&s).to_string()),
        "task.create" => d.pointer("/action/data/id").and_then(|v| v.as_str()).map(|s| origin_of(s).to_string()),
        "task.heartbeat" => d.pointer("/tasks/0/id").and_then(|v| v.as_str()).map(|s| origin_of(s).to_string()),
        "schedule.get" | "schedule.create" | "schedule.delete" => id("id"),
        _ => return Ok(None),
    };
    match origin {
        Some(o) if !o.is_empty() => Ok(Some(o)),
        _ => Err("Request data does not name an id".to_string()),
    }
}

/// Decode `req`, decided at `now`: the kernel's request on its document,
/// or the envelope that refuses it.
pub fn decode(req: &RequestEnvelope, now: u64) -> Result<Decoded, ResponseEnvelope> {
    let kind = req.kind.clone();
    let corr = req.head.corr_id.clone();
    let err = |status: u16, msg: &str| Err(ResponseEnvelope::error(kind.clone(), corr.clone(), status as i32, msg));
    let origin = match origin_of_request(req) {
        Ok(o) => o,
        Err(e) => return err(400, &e),
    };
    macro_rules! parsed {
        ($t:ty) => {
            match parse::<$t>(&req.data) {
                Ok(v) => v,
                Err(m) => return err(400, &m),
            }
        };
    }
    let (q, schedule, action_kind): (k::Request, Option<String>, Option<String>) = match kind.as_str() {
        "promise.get" => {
            let d = parsed!(w::PromiseGetData);
            (k::Request::PromiseGet(k::PromiseGetReq { id: d.id }), None, None)
        }
        "promise.create" => {
            let d = parsed!(w::PromiseCreateData);
            match wire::create_in(&d) {
                Ok(q) => (k::Request::PromiseCreate(q), None, None),
                Err(m) => return err(400, &m),
            }
        }
        "promise.settle" => {
            let d = parsed!(w::PromiseSettleData);
            (k::Request::PromiseSettle(wire::settle_in_req(&d)), None, None)
        }
        "promise.register_callback" => {
            let d = parsed!(w::PromiseRegisterCallbackData);
            (k::Request::PromiseRegisterCallback(k::PromiseRegisterCallbackReq { awaited: d.awaited, awaiter: d.awaiter }), None, None)
        }
        "promise.register_listener" => {
            let d = parsed!(w::PromiseRegisterListenerData);
            if !resonate_core::is_valid_address(&d.address) {
                return err(400, "Address must be a URI with a scheme");
            }
            (k::Request::PromiseRegisterListener(k::PromiseRegisterListenerReq { awaited: d.awaited, address: d.address }), None, None)
        }
        "task.get" => {
            let d = parsed!(w::TaskGetData);
            (k::Request::TaskGet(k::TaskGetReq { id: d.id }), None, None)
        }
        "task.create" => {
            let d = parsed!(w::TaskCreateData);
            let action = match wire::create_in(&d.action.data) {
                Ok(q) => q,
                Err(m) => return err(400, &m),
            };
            let ttl = match wire::nat(d.ttl, "ttl") {
                Ok(v) => v,
                Err(m) => return err(400, &m),
            };
            (k::Request::TaskCreate(k::TaskCreateReq { pid: d.pid, ttl, action }), None, None)
        }
        "task.acquire" => {
            let d = parsed!(w::TaskAcquireData);
            let (version, ttl) = match (wire::nat(d.version, "version"), wire::nat(d.ttl, "ttl")) {
                (Ok(v), Ok(t)) => (v, t),
                (Err(m), _) | (_, Err(m)) => return err(400, &m),
            };
            (k::Request::TaskAcquire(k::TaskAcquireReq { id: d.id, version, pid: d.pid, ttl }), None, None)
        }
        "task.release" => {
            let d = parsed!(w::TaskReleaseData);
            let version = match wire::nat(d.version, "version") {
                Ok(v) => v,
                Err(m) => return err(400, &m),
            };
            (k::Request::TaskRelease(k::TaskReleaseReq { id: d.id, version }), None, None)
        }
        "task.fulfill" => {
            let d = parsed!(w::TaskFulfillData);
            let version = match wire::nat(d.version, "version") {
                Ok(v) => v,
                Err(m) => return err(400, &m),
            };
            let q = k::TaskFulfillReq {
                id: d.id,
                version,
                action: k::PromiseSettleReq { id: d.action.data.id, state: wire::settle_in(d.action.data.state), value: wire::value_in(&d.action.data.value) },
            };
            (k::Request::TaskFulfill(q), None, None)
        }
        "task.suspend" => {
            let d = parsed!(w::TaskSuspendData);
            let version = match wire::nat(d.version, "version") {
                Ok(v) => v,
                Err(m) => return err(400, &m),
            };
            let actions = d.actions.into_iter().map(|a| k::PromiseRegisterCallbackReq { awaited: a.data.awaited, awaiter: a.data.awaiter }).collect();
            (k::Request::TaskSuspend(k::TaskSuspendReq { id: d.id, version, actions }), None, None)
        }
        "task.fence" => {
            let d = parsed!(w::TaskFenceData);
            let version = match wire::nat(d.version, "version") {
                Ok(v) => v,
                Err(m) => return err(400, &m),
            };
            // A fence and its action commit as one write on one document,
            // so the action must live in the task's origin.
            if let Some(aid) = d.action.data.get("id").and_then(|v| v.as_str()) {
                if origin_of(aid) != origin_of(&d.id) {
                    return err(400, "Action must belong to the task's origin");
                }
            }
            let action = match d.action.kind.as_str() {
                "promise.create" => match parse::<w::PromiseCreateData>(&d.action.data).and_then(|c| wire::create_in(&c)) {
                    Ok(c) => k::TaskFenceAction::Create(c),
                    Err(m) => return err(400, &m),
                },
                "promise.settle" => match parse::<w::PromiseSettleData>(&d.action.data) {
                    Ok(c) => k::TaskFenceAction::Settle(wire::settle_in_req(&c)),
                    Err(m) => return err(400, &m),
                },
                other => return err(400, &format!("Unsupported fence action: {other}")),
            };
            (k::Request::TaskFence(k::TaskFenceReq { id: d.id, version, action }), None, Some(d.action.kind))
        }
        "task.heartbeat" => {
            let d = parsed!(w::TaskHeartbeatData);
            let mut tasks = Vec::with_capacity(d.tasks.len());
            for t in d.tasks {
                match wire::nat(t.version, "version") {
                    Ok(v) => tasks.push(k::TaskRef { id: t.id, version: v }),
                    Err(m) => return err(400, &m),
                }
            }
            (k::Request::TaskHeartbeat(k::TaskHeartbeatReq { pid: d.pid, tasks }), None, None)
        }
        "task.halt" => {
            let d = parsed!(w::TaskHaltData);
            (k::Request::TaskHalt(k::TaskHaltReq { id: d.id }), None, None)
        }
        "task.continue" => {
            let d = parsed!(w::TaskContinueData);
            (k::Request::TaskContinue(k::TaskContinueReq { id: d.id }), None, None)
        }
        "schedule.get" => {
            let d = parsed!(w::ScheduleGetData);
            (k::Request::ScheduleGet(k::ScheduleGetReq { id: d.id.clone() }), Some(d.id), None)
        }
        "schedule.create" => {
            let d = parsed!(w::ScheduleCreateData);
            if !util::is_valid_cron(&d.cron) {
                return err(400, "Invalid cron expression");
            }
            let promise_timeout = match wire::nat(d.promise_timeout, "promiseTimeout") {
                Ok(v) => v,
                Err(m) => return err(400, &m),
            };
            let next = util::compute_next_cron(&d.cron, now as i64).max(now as i64 + 1) as u64;
            let id = d.id.clone();
            let q = k::ScheduleCreateReq {
                id: d.id,
                cron: d.cron,
                promise_id: d.promise_id,
                promise_timeout,
                promise_param: wire::value_in(&d.promise_param),
                promise_tags: wire::create_tags(&d.promise_tags),
                next_run_at: next,
            };
            (k::Request::ScheduleCreate(q), Some(id), None)
        }
        "schedule.delete" => {
            let d = parsed!(w::ScheduleDeleteData);
            (k::Request::ScheduleDelete(k::ScheduleDeleteReq { id: d.id.clone() }), Some(d.id), None)
        }
        "promise.search" | "task.search" | "schedule.search" => return err(403, "Search operations are not supported"),
        "debug.reset" | "debug.snap" | "debug.tick" => return err(403, "Debug operations are not supported"),
        _ => return err(400, &format!("Unknown request kind: {kind}")),
    };
    // A request about a schedule is served on its document; the rest on
    // their id's origin.
    let target = match (schedule, origin) {
        (Some(id), _) => Target::Schedule(id),
        (None, Some(o)) => Target::Origin(o),
        (None, None) => return err(400, "Request data does not name an id"),
    };
    Ok(Decoded { target, request: q, action_kind })
}
