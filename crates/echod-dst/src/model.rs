//! The specification: the kernel, one operation at a time.
//!
//! The model is what the applier runs, without the store around it: a
//! kernel handler on one origin's state, then the drain. Its answers are
//! rendered by the same `wire` functions the server uses, so a history entry
//! and a model step compare as `(status, data)` exactly.

use echod_kernel as k;
use echod_server::wire;
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

/// Apply `op` at `now` to `s`, drain, and answer as the server would.
pub fn step(s: &mut k::State, op: &Op, now: u64, cfg: &k::Config, corr: &str) -> (u16, Value) {
    let kind = op.kind();
    let out = match op {
        Op::PromiseGet { id } => wire::promise_res(kind, corr, &s.promise_get(&k::PromiseGetReq { id: id.clone() }, now, cfg)),
        Op::PromiseCreate { id, timeout_at, tags: t, data } => wire::promise_res(kind, corr, &s.promise_create(&create_req(id, *timeout_at, t, Some(data)), now, cfg)),
        Op::PromiseSettle { id, state, data } => {
            wire::promise_res(kind, corr, &s.promise_settle(&k::PromiseSettleReq { id: id.clone(), state: *state, value: value(data) }, now, cfg))
        }
        Op::RegisterCallback { awaited, awaiter } => {
            wire::promise_res(kind, corr, &s.promise_register_callback(&k::PromiseRegisterCallbackReq { awaited: awaited.clone(), awaiter: awaiter.clone() }, now, cfg))
        }
        Op::RegisterListener { awaited, address } => {
            wire::promise_res(kind, corr, &s.promise_register_listener(&k::PromiseRegisterListenerReq { awaited: awaited.clone(), address: address.clone() }, now, cfg))
        }
        Op::TaskGet { id } => {
            let r = s.task_get(&k::TaskGetReq { id: id.clone() }, now, cfg);
            match &r.task {
                Some(t) => wire::status_res(kind, corr, r.status, serde_json::json!({ "task": wire::task_out(t) })),
                None => wire::status_res(kind, corr, r.status, serde_json::json!({})),
            }
        }
        Op::TaskCreate { pid, ttl, id, timeout_at, tags: t } => {
            wire::claim_res(kind, corr, &s.task_create(&k::TaskCreateReq { pid: pid.clone(), ttl: *ttl, action: create_req(id, *timeout_at, t, None) }, now, cfg))
        }
        Op::TaskAcquire { id, version, pid, ttl } => {
            wire::claim_res(kind, corr, &s.task_acquire(&k::TaskAcquireReq { id: id.clone(), version: *version, pid: pid.clone(), ttl: *ttl }, now, cfg))
        }
        Op::TaskFulfill { id, version, state, data } => wire::promise_res(
            kind,
            corr,
            &s.task_fulfill(&k::TaskFulfillReq { id: id.clone(), version: *version, action: k::PromiseSettleReq { id: id.clone(), state: *state, value: value(data) } }, now, cfg),
        ),
        Op::TaskRelease { id, version } => {
            let r = s.task_release(&k::TaskReleaseReq { id: id.clone(), version: *version }, now, cfg);
            wire::status_res(kind, corr, r.status, serde_json::json!({}))
        }
        Op::TaskHeartbeat { pid, tasks } => {
            let r = s.task_heartbeat(&k::TaskHeartbeatReq { pid: pid.clone(), tasks: tasks.iter().map(|(id, v)| k::TaskRef { id: id.clone(), version: *v }).collect() }, now, cfg);
            wire::status_res(kind, corr, r.status, serde_json::json!({}))
        }
        Op::TaskSuspend { id, version, awaited } => {
            let actions = awaited.iter().map(|a| k::PromiseRegisterCallbackReq { awaited: a.clone(), awaiter: id.clone() }).collect();
            let r = s.task_suspend(&k::TaskSuspendReq { id: id.clone(), version: *version, actions }, now, cfg);
            wire::status_res(kind, corr, r.status, serde_json::json!({ "preload": [] }))
        }
        Op::TaskFenceCreate { id, version, child, timeout_at, tags: t } => {
            let r = s.task_fence(&k::TaskFenceReq { id: id.clone(), version: *version, action: k::TaskFenceAction::Create(create_req(child, *timeout_at, t, None)) }, now, cfg);
            fence_res(kind, corr, "promise.create", &r)
        }
        Op::TaskFenceSettle { id, version, target, state, data } => {
            let r = s.task_fence(
                &k::TaskFenceReq { id: id.clone(), version: *version, action: k::TaskFenceAction::Settle(k::PromiseSettleReq { id: target.clone(), state: *state, value: value(data) }) },
                now,
                cfg,
            );
            fence_res(kind, corr, "promise.settle", &r)
        }
        Op::TaskHalt { id } => {
            let r = s.task_halt(&k::TaskHaltReq { id: id.clone() }, now, cfg);
            wire::status_res(kind, corr, r.status, serde_json::json!({}))
        }
        Op::TaskContinue { id } => {
            let r = s.task_continue(&k::TaskContinueReq { id: id.clone() }, now, cfg);
            wire::status_res(kind, corr, r.status, serde_json::json!({}))
        }
        Op::Sweep => {
            echod_server::step::sweep(s, now, cfg);
            wire::status_res(kind, corr, 200, serde_json::json!({}))
        }
    };
    echod_server::step::drain(s, now, cfg);
    s.outbox.clear();
    (out.head.status as u16, out.data)
}

fn fence_res(kind: &str, corr: &str, action_kind: &str, r: &k::TaskFenceRes) -> resonate_core::types::ResponseEnvelope {
    match &r.action {
        Some(k::TaskFenceInnerRes::Create(p)) | Some(k::TaskFenceInnerRes::Settle(p)) => {
            let inner = wire::promise_res(action_kind, corr, p);
            wire::status_res(kind, corr, r.status, serde_json::json!({ "action": inner, "preload": [] }))
        }
        None => wire::status_res(kind, corr, r.status, serde_json::json!({})),
    }
}

/// A fresh state over `rows`.
pub fn state(rows: &[k::Promise]) -> k::State {
    k::State { objects: rows.to_vec(), schedules: vec![], outbox: vec![] }
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
