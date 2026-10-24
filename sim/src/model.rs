//! The specification: the kernel, one operation at a time.
//!
//! The model is what the applier runs, without the store around it: a
//! `handle` on one origin's state, then the drain. Its answers are
//! rendered by the same `wire` functions the server uses, so a history entry
//! and a model step compare as `(status, data)` exactly.

use echod_kernel as k;
use echod_logic::wire;
use serde_json::Value;

use crate::workload::Op;

pub fn tags(m: &std::collections::BTreeMap<String, String>) -> Vec<(String, String)> {
    let hm: std::collections::HashMap<String, String> = m.iter().map(|(a, b)| (a.clone(), b.clone())).collect();
    wire::create_tags(&hm)
}

fn value(data: &str) -> k::Value {
    k::Value { headers: vec![], data: Some(data.to_string()) }
}

fn create_req(id: &str, timeout_at: u64, t: &std::collections::BTreeMap<String, String>, data: Option<&str>) -> k::PromiseCreateReq {
    k::PromiseCreateReq { id: id.to_string(), timeout_at, param: k::Value { headers: vec![], data: data.map(str::to_string) }, tags: tags(t) }
}

/// Apply `op` at `now` to `s`, drain, and answer as the node would. The
/// step is decided no earlier than the document's stamp, the instant of the
/// last write; a write moves the stamp, as the node's header does. A sweep
/// always writes: what it fired, or the rewrite that collects its key. An
/// advance writes when it lands. A fire writes only what it changed: an
/// occurrence fired again, by a node that lost the race or came later,
/// changes nothing and writes nothing. A schedule's next run is computed
/// from the request's instant, before the stamp, as the dispatch does.
pub fn step(s: &mut k::State, stamp: &mut u64, op: &Op, now: u64, cfg: &k::Config, corr: &str) -> (u16, Value) {
    let asked = now;
    let now = echod_kernel::steps::clamp_now(*stamp, now);
    let before = canon_state(s);
    let kind = op.kind();
    let out = match op {
        Op::Sweep => {
            echod_kernel::steps::sweep(s, now, cfg);
            wire::status_res(kind, corr, 200, serde_json::json!({}))
        }
        Op::Fire { schedule, at, promise_id, next } => {
            // the kernel's step on the row beside the origin's objects; the row
            // is the schedule's document's, not this one's
            s.schedules = vec![schedule.0.clone()];
            let req = k::ScheduleTimeoutReq { schedule: schedule.0.id.clone(), occurrences: vec![k::Occurrence { at: *at, promise_id: promise_id.clone() }], next_run_at: *next };
            s.process_schedule(&req, now, cfg);
            s.schedules.clear();
            wire::status_res(kind, corr, 200, serde_json::json!({}))
        }
        Op::Advance { id, at, next } => {
            // conditional on the version loaded with the origin: the row still at the occurrence
            match s.schedules.iter_mut().find(|c| c.id == *id) {
                Some(c) if c.next_run_at == *at => {
                    c.last_run_at = Some(*at);
                    c.next_run_at = *next;
                    wire::status_res(kind, corr, 200, serde_json::json!({}))
                }
                _ => wire::status_res(kind, corr, 409, serde_json::json!({})),
            }
        }
        _ => {
            let (q, action_kind) = request_of(op, asked).expect("a client's request");
            let r = s.handle(&q, now, cfg);
            wire::render(kind, corr, action_kind, &q, &r, s)
        }
    };
    echod_kernel::steps::drain(s, now, cfg);
    s.outbox.clear();
    let wrote = match op {
        Op::Sweep => true,
        Op::Advance { .. } => out.head.status == 200,
        _ => canon_state(s) != before,
    };
    if wrote {
        *stamp = now;
    }
    (out.head.status as u16, out.data)
}

/// The kernel's request for an operation, with the kind of a fence's inner
/// action; none for an internal step. `now` is the request's instant, which
/// a schedule's next run is computed from.
pub fn request_of(op: &Op, now: u64) -> Option<(k::Request, Option<&'static str>)> {
    let q = match op {
        Op::PromiseGet { id } => k::Request::PromiseGet(k::PromiseGetReq { id: id.clone() }),
        Op::PromiseCreate { id, timeout_at, tags: t, data } => k::Request::PromiseCreate(create_req(id, *timeout_at, t, Some(data))),
        Op::PromiseSettle { id, state, data } => k::Request::PromiseSettle(k::PromiseSettleReq { id: id.clone(), state: *state, value: value(data) }),
        Op::RegisterCallback { awaited, awaiter } => k::Request::PromiseRegisterCallback(k::PromiseRegisterCallbackReq { awaited: awaited.clone(), awaiter: awaiter.clone() }),
        Op::RegisterListener { awaited, address } => k::Request::PromiseRegisterListener(k::PromiseRegisterListenerReq { awaited: awaited.clone(), address: address.clone() }),
        Op::TaskGet { id } => k::Request::TaskGet(k::TaskGetReq { id: id.clone() }),
        Op::TaskCreate { pid, ttl, id, timeout_at, tags: t } => k::Request::TaskCreate(k::TaskCreateReq { pid: pid.clone(), ttl: *ttl, action: create_req(id, *timeout_at, t, None) }),
        Op::TaskAcquire { id, version, pid, ttl } => k::Request::TaskAcquire(k::TaskAcquireReq { id: id.clone(), version: *version, pid: pid.clone(), ttl: *ttl }),
        Op::TaskFulfill { id, version, state, data } => {
            k::Request::TaskFulfill(k::TaskFulfillReq { id: id.clone(), version: *version, action: k::PromiseSettleReq { id: id.clone(), state: *state, value: value(data) } })
        }
        Op::TaskRelease { id, version } => k::Request::TaskRelease(k::TaskReleaseReq { id: id.clone(), version: *version }),
        Op::TaskHeartbeat { pid, tasks } => {
            k::Request::TaskHeartbeat(k::TaskHeartbeatReq { pid: pid.clone(), tasks: tasks.iter().map(|(id, v)| k::TaskRef { id: id.clone(), version: *v }).collect() })
        }
        Op::TaskSuspend { id, version, awaited } => {
            let actions = awaited.iter().map(|a| k::PromiseRegisterCallbackReq { awaited: a.clone(), awaiter: id.clone() }).collect();
            k::Request::TaskSuspend(k::TaskSuspendReq { id: id.clone(), version: *version, actions })
        }
        Op::TaskFenceCreate { id, version, child, timeout_at, tags: t } => {
            let q = k::TaskFenceReq { id: id.clone(), version: *version, action: k::TaskFenceAction::Create(create_req(child, *timeout_at, t, None)) };
            return Some((k::Request::TaskFence(q), Some("promise.create")));
        }
        Op::TaskFenceSettle { id, version, target, state, data } => {
            let q = k::TaskFenceReq { id: id.clone(), version: *version, action: k::TaskFenceAction::Settle(k::PromiseSettleReq { id: target.clone(), state: *state, value: value(data) }) };
            return Some((k::Request::TaskFence(q), Some("promise.settle")));
        }
        Op::TaskHalt { id } => k::Request::TaskHalt(k::TaskHaltReq { id: id.clone() }),
        Op::TaskContinue { id } => k::Request::TaskContinue(k::TaskContinueReq { id: id.clone() }),
        Op::ScheduleGet { id } => k::Request::ScheduleGet(k::ScheduleGetReq { id: id.clone() }),
        Op::ScheduleCreate { id, cron, promise_id, promise_timeout, tags: t } => {
            let next = resonate_core::util::compute_next_cron(cron, now as i64).max(now as i64 + 1) as u64;
            k::Request::ScheduleCreate(k::ScheduleCreateReq {
                id: id.clone(),
                cron: cron.clone(),
                promise_id: promise_id.clone(),
                promise_timeout: *promise_timeout,
                promise_param: k::Value { headers: vec![], data: None },
                promise_tags: tags(t),
                next_run_at: next,
            })
        }
        Op::ScheduleDelete { id } => k::Request::ScheduleDelete(k::ScheduleDeleteReq { id: id.clone() }),
        Op::Sweep | Op::Fire { .. } | Op::Advance { .. } => return None,
    };
    Some((q, None))
}

/// A fresh, empty state.
pub fn state() -> k::State {
    k::State { objects: vec![], schedules: vec![], outbox: vec![] }
}

/// The state's rows of both kinds, canonically.
pub fn canon_state(s: &k::State) -> Value {
    let mut c: Vec<(String, Value)> = s.schedules.iter().map(|c| (c.id.clone(), serde_json::to_value(c).unwrap())).collect();
    c.sort_by(|a, b| a.0.cmp(&b.0));
    serde_json::json!({ "objects": canon(&s.objects), "schedules": c.into_iter().map(|(_, v)| v).collect::<Vec<_>>() })
}

pub fn clone_state(s: &k::State) -> k::State {
    k::State { objects: s.objects.clone(), schedules: s.schedules.clone(), outbox: vec![] }
}

/// The rows by id, canonically: what two states are compared on.
pub fn canon(rows: &[k::Promise]) -> Value {
    let mut v: Vec<(String, Value)> = rows.iter().map(|p| (p.id.clone(), serde_json::to_value(p).unwrap())).collect();
    v.sort_by(|a, b| a.0.cmp(&b.0));
    Value::Array(v.into_iter().map(|(_, p)| p).collect())
}
