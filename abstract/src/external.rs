//! All 21 external semantic actions from `02-abstract/external.lean`.
//!
//! Search actions intentionally return 501 because that is their complete
//! Lean semantics. No action records Invoke/Return observations.

use vstd::prelude::*;
use crate::state::*;
use crate::types::*;

verus! {

fn promise_error(status: u16) -> PromiseRes {
    PromiseRes { status, promise: None }
}

fn claim_error(status: u16) -> TaskClaimRes {
    TaskClaimRes {
        status, task: None, promise: None, preload: Vec::new(),
    }
}

fn claim_ok(o: &Object, t: &TaskObject) -> TaskClaimRes {
    TaskClaimRes {
        status: 200,
        task: Some(t.to_record(&o.id)),
        promise: Some(o.promise.to_record(&o.id)),
        preload: Vec::new(),
    }
}

pub fn promise_get_action(
    state: &State, req: &PromiseGetReq, now: u64, materialize: bool,
) -> Transition<PromiseGetRes> {
    let read = read_object(state, &req.id, now, materialize);
    match read.object {
        None => Transition { response: promise_error(404), effects: read.effects },
        Some(o) => Transition {
            response: PromiseRes { status: 200, promise: Some(o.promise.to_record(&o.id)) },
            effects: read.effects,
        },
    }
}

pub fn promise_create_action(
    state: &State, req: PromiseCreateReq, now: u64, materialize: bool,
) -> Transition<PromiseCreateRes> {
    if tags_timer_targeted(&req.tags) {
        return Transition { response: promise_error(400), effects: Vec::new() };
    }
    let read = read_object(state, &req.id, now, materialize);
    match read.object {
        Some(o) => Transition {
            response: PromiseRes { status: 200, promise: Some(o.promise.to_record(&o.id)) },
            effects: read.effects,
        },
        None => {
            let made = create_promise(req, now);
            Transition {
                response: PromiseRes {
                    status: 200,
                    promise: Some(made.object.promise.to_record(&made.object.id)),
                },
                effects: append_effects(read.effects, made.effects),
            }
        }
    }
}

pub fn promise_settle_action(
    state: &State, req: PromiseSettleReq, now: u64, materialize: bool,
) -> Transition<PromiseSettleRes> {
    if !req.state.settable() {
        return Transition { response: promise_error(400), effects: Vec::new() };
    }
    let read = read_object(state, &req.id, now, materialize);
    match read.object {
        None => Transition { response: promise_error(404), effects: read.effects },
        Some(o) => {
            if o.promise.state == PromiseState::Pending {
                let mut p = o.promise.dup();
                p.state = req.state;
                p.value = req.value;
                p.settled_at = Some(now);
                let rec = p.to_record(&o.id);
                Transition {
                    response: PromiseRes { status: 200, promise: Some(rec) },
                    effects: append_effects(read.effects, set_settled_effects(&o, &p)),
                }
            } else {
                Transition {
                    response: PromiseRes {
                        status: 200, promise: Some(o.promise.to_record(&o.id)),
                    },
                    effects: read.effects,
                }
            }
        }
    }
}

pub fn promise_register_callback_action(
    state: &State, req: &PromiseRegisterCallbackReq, now: u64, materialize: bool,
) -> Transition<PromiseRegisterCallbackRes> {
    if ident_eq(&req.awaited, &req.awaiter) || !req.awaited.same_origin(&req.awaiter) {
        return Transition { response: promise_error(400), effects: Vec::new() };
    }
    let awaited = read_object(state, &req.awaited, now, materialize);
    let oa = match awaited.object {
        None => return Transition { response: promise_error(404), effects: awaited.effects },
        Some(o) => o,
    };
    let awaiter = read_object(state, &req.awaiter, now, materialize);
    let mut effects = append_effects(awaited.effects, awaiter.effects);
    let ow = match awaiter.object {
        None => return Transition { response: promise_error(422), effects },
        Some(o) => o,
    };
    if ow.promise.otype() != OType::Runnable || !oa.promise.otype().awaitable() {
        return Transition { response: promise_error(422), effects };
    }
    if oa.promise.state == PromiseState::Pending && ow.promise.state == PromiseState::Pending {
        effects.push(Effect::SetPromise(
            oa.id.dup(), oa.promise.dup().add_callback(&req.awaiter),
        ));
    }
    Transition {
        response: PromiseRes {
            status: 200, promise: Some(oa.promise.to_record(&oa.id)),
        },
        effects,
    }
}

pub fn promise_register_listener_action(
    state: &State, req: &PromiseRegisterListenerReq, now: u64, materialize: bool,
) -> Transition<PromiseRegisterListenerRes> {
    let read = read_object(state, &req.awaited, now, materialize);
    match read.object {
        None => Transition { response: promise_error(404), effects: read.effects },
        Some(o) => {
            if !o.promise.otype().awaitable() {
                return Transition { response: promise_error(422), effects: read.effects };
            }
            let mut effects = read.effects;
            if o.promise.state == PromiseState::Pending {
                effects.push(Effect::SetPromise(
                    o.id.dup(), o.promise.dup().add_listener(&req.address),
                ));
            }
            Transition {
                response: PromiseRes {
                    status: 200, promise: Some(o.promise.to_record(&o.id)),
                },
                effects,
            }
        }
    }
}

pub fn promise_search_action(
    _state: &State, _req: &PromiseSearchReq, _now: u64, _materialize: bool,
) -> Transition<PromiseSearchRes> {
    Transition {
        response: PromiseSearchRes { status: 501, promises: Vec::new(), cursor: None },
        effects: Vec::new(),
    }
}

pub fn task_get_action(
    state: &State, req: &TaskGetReq, now: u64, materialize: bool,
) -> Transition<TaskGetRes> {
    let read = read_task_object(state, &req.id, now, materialize);
    match read.object {
        None => Transition {
            response: TaskGetRes { status: 404, task: None }, effects: read.effects,
        },
        Some(o) => match &o.task {
            None => Transition {
                response: TaskGetRes { status: 404, task: None }, effects: read.effects,
            },
            Some(t) => Transition {
                response: TaskGetRes { status: 200, task: Some(t.to_record(&o.id)) },
                effects: read.effects,
            },
        },
    }
}

pub fn task_create_action(
    state: &State, req: TaskCreateReq, now: u64, materialize: bool,
) -> Transition<TaskCreateRes> {
    let a = req.action;
    if tags_otype(&a.tags) != OType::Runnable || tags_timer_targeted(&a.tags)
    {
        return Transition { response: claim_error(400), effects: Vec::new() };
    }
    let read = read_object(state, &a.id, now, materialize);
    match read.object {
        None => {
            let id = a.id;
            let p = if a.timeout_at > now {
                PromiseObject {
                    state: PromiseState::Pending, param: a.param, value: Value::empty(),
                    tags: a.tags, timeout_at: a.timeout_at, created_at: now,
                    settled_at: None, callbacks: Vec::new(), listeners: Vec::new(),
                }
            } else {
                PromiseObject {
                    state: PromiseState::RejectedTimedout, param: a.param,
                    value: Value::empty(), tags: a.tags, timeout_at: a.timeout_at,
                    created_at: a.timeout_at, settled_at: Some(a.timeout_at),
                    callbacks: Vec::new(), listeners: Vec::new(),
                }
            };
            let t = if p.state == PromiseState::Pending {
                TaskObject {
                    state: TaskState::Acquired, version: 1, ttl: Some(req.ttl),
                    pid: Some(req.pid), lease_timeout_at: Some(checked_add(now, req.ttl)),
                    retry_timeout_at: None, resumes: Vec::new(),
                }
            } else {
                TaskObject {
                    state: TaskState::Fulfilled, version: 0, ttl: None, pid: None,
                    lease_timeout_at: None, retry_timeout_at: None, resumes: Vec::new(),
                }
            };
            let object = Object { id: id.dup(), promise: p.dup(), task: Some(t.dup()) };
            let mut effects = read.effects;
            effects.push(Effect::SetPromise(id.dup(), p));
            effects.push(Effect::SetTask(id, t.dup()));
            Transition { response: claim_ok(&object, &t), effects }
        }
        Some(o) => {
            if o.promise.otype() != OType::Runnable {
                return Transition { response: claim_error(422), effects: read.effects };
            }
            let t0 = match &o.task {
                None => return Transition { response: claim_error(409), effects: read.effects },
                Some(t) => t,
            };
            if t0.state == TaskState::Fulfilled {
                return Transition { response: claim_ok(&o, t0), effects: read.effects };
            }
            if t0.state != TaskState::Pending {
                return Transition { response: claim_error(409), effects: read.effects };
            }
            let next_version = t0.version.saturating_add(1);
            let mut t = t0.dup();
            t.state = TaskState::Acquired;
            t.version = next_version;
            t.ttl = Some(req.ttl);
            t.pid = Some(req.pid);
            t.lease_timeout_at = Some(checked_add(now, req.ttl));
            t.retry_timeout_at = None;
            t.resumes = Vec::new();
            let mut effects = read.effects;
            effects.push(Effect::SetTask(o.id.dup(), t.dup()));
            Transition { response: claim_ok(&o, &t), effects }
        }
    }
}

pub fn task_acquire_action(
    state: &State, req: TaskAcquireReq, now: u64, materialize: bool,
) -> Transition<TaskAcquireRes> {
    let read = read_task_object(state, &req.id, now, materialize);
    let o = match read.object {
        None => return Transition { response: claim_error(404), effects: read.effects },
        Some(o) => o,
    };
    let t0 = match &o.task {
        None => return Transition { response: claim_error(404), effects: read.effects },
        Some(t) => t,
    };
    if t0.state != TaskState::Pending || o.promise.state != PromiseState::Pending
        || t0.version != req.version
    {
        return Transition { response: claim_error(409), effects: read.effects };
    }
    let next_version = t0.version.saturating_add(1);
    let mut t = t0.dup();
    t.state = TaskState::Acquired;
    t.version = next_version;
    t.ttl = Some(req.ttl);
    t.pid = Some(req.pid);
    t.lease_timeout_at = Some(checked_add(now, req.ttl));
    t.retry_timeout_at = None;
    t.resumes = Vec::new();
    let mut effects = read.effects;
    effects.push(Effect::SetTask(o.id.dup(), t.dup()));
    Transition { response: claim_ok(&o, &t), effects }
}

pub fn task_fence_action(
    state: &State, req: TaskFenceReq, now: u64, materialize: bool,
) -> Transition<TaskFenceRes> {
    let target = match &req.action {
        TaskFenceAction::Create(x) => &x.id,
        TaskFenceAction::Settle(x) => &x.id,
    };
    if ident_eq(target, &req.id) || !target.same_origin(&req.id) {
        return Transition {
            response: TaskFenceRes { status: 400, action: None, preload: Vec::new() },
            effects: Vec::new(),
        };
    }
    let read = read_task_object(state, &req.id, now, materialize);
    let o = match read.object {
        None => return Transition {
            response: TaskFenceRes { status: 404, action: None, preload: Vec::new() },
            effects: read.effects,
        },
        Some(o) => o,
    };
    let t = match &o.task {
        None => return Transition {
            response: TaskFenceRes { status: 404, action: None, preload: Vec::new() },
            effects: read.effects,
        },
        Some(t) => t,
    };
    if t.state != TaskState::Acquired || o.promise.state != PromiseState::Pending
        || t.version != req.version
    {
        return Transition {
            response: TaskFenceRes { status: 409, action: None, preload: Vec::new() },
            effects: read.effects,
        };
    }
    match req.action {
        TaskFenceAction::Create(x) => {
            let inner = promise_create_action(state, x, now, materialize);
            Transition {
                response: TaskFenceRes {
                    status: 200, action: Some(TaskFenceInnerRes::Create(inner.response)),
                    preload: Vec::new(),
                },
                effects: append_effects(read.effects, inner.effects),
            }
        }
        TaskFenceAction::Settle(x) => {
            let inner = promise_settle_action(state, x, now, materialize);
            Transition {
                response: TaskFenceRes {
                    status: 200, action: Some(TaskFenceInnerRes::Settle(inner.response)),
                    preload: Vec::new(),
                },
                effects: append_effects(read.effects, inner.effects),
            }
        }
    }
}

fn heartbeat_one(
    state: &State, pid: &Text, r: &TaskRef, now: u64, materialize: bool,
) -> Vec<Effect> {
    let read = read_task_object(state, &r.id, now, materialize);
    let o = match read.object {
        None => return read.effects,
        Some(o) => o,
    };
    let t0 = match &o.task {
        None => return read.effects,
        Some(t) => t,
    };
    let owns = match &t0.pid { Some(p) => text_eq(p, pid), None => false };
    let mut effects = read.effects;
    if t0.state == TaskState::Acquired && t0.version == r.version && owns
        && o.promise.state == PromiseState::Pending
    {
        let mut t = t0.dup();
        t.lease_timeout_at = Some(checked_add(now, match t.ttl { Some(x) => x, None => 0 }));
        effects.push(Effect::SetTask(o.id, t));
    }
    effects
}

pub fn task_heartbeat_action(
    state: &State, req: &TaskHeartbeatReq, now: u64, materialize: bool,
) -> Transition<TaskHeartbeatRes> {
    let mut effects = Vec::new();
    let mut i: usize = 0;
    while i < req.tasks.len()
        decreases req.tasks@.len() - i,
    {
        effects = append_effects(
            effects, heartbeat_one(state, &req.pid, &req.tasks[i], now, materialize),
        );
        i += 1;
    }
    Transition { response: StatusRes { status: 200 }, effects }
}

fn invalid_suspend_actions(actions: &Vec<PromiseRegisterCallbackReq>, id: &Ident) -> bool {
    if actions.len() == 0 { return true; }
    let mut i: usize = 0;
    while i < actions.len()
        invariant i <= actions@.len(),
        decreases actions@.len() - i,
    {
        if ident_eq(&actions[i].awaited, id) || !actions[i].awaited.same_origin(id) {
            return true;
        }
        let mut j: usize = 0;
        while j < i
            invariant j <= i, i < actions@.len(),
            decreases i - j,
        {
            if ident_eq(&actions[j].awaited, &actions[i].awaited) { return true; }
            j += 1;
        }
        i += 1;
    }
    false
}

pub fn task_suspend_action(
    state: &State, req: &TaskSuspendReq, now: u64, materialize: bool,
) -> Transition<TaskSuspendRes> {
    if invalid_suspend_actions(&req.actions, &req.id) {
        return Transition {
            response: TaskSuspendRes { status: 400, preload: Vec::new() },
            effects: Vec::new(),
        };
    }
    let read = read_task_object(state, &req.id, now, materialize);
    let o = match read.object {
        None => return Transition {
            response: TaskSuspendRes { status: 404, preload: Vec::new() },
            effects: read.effects,
        },
        Some(o) => o,
    };
    let t0 = match &o.task {
        None => return Transition {
            response: TaskSuspendRes { status: 404, preload: Vec::new() },
            effects: read.effects,
        },
        Some(t) => t,
    };
    if t0.state != TaskState::Acquired || o.promise.state != PromiseState::Pending
        || t0.version != req.version
    {
        return Transition {
            response: TaskSuspendRes { status: 409, preload: Vec::new() },
            effects: read.effects,
        };
    }

    let mut effects = read.effects;
    let mut settled = false;
    let mut i: usize = 0;
    while i < req.actions.len()
        decreases req.actions@.len() - i,
    {
        let rr = read_object(state, &req.actions[i].awaited, now, materialize);
        effects = append_effects(effects, rr.effects);
        let awaited = match rr.object {
            None => return Transition {
                response: TaskSuspendRes { status: 422, preload: Vec::new() }, effects,
            },
            Some(x) => x,
        };
        if !awaited.promise.otype().awaitable() {
            return Transition {
                response: TaskSuspendRes { status: 422, preload: Vec::new() }, effects,
            };
        }
        if awaited.promise.state != PromiseState::Pending { settled = true; }
        i += 1;
    }

    if settled {
        let mut t = t0.dup();
        t.resumes = Vec::new();
        effects.push(Effect::SetTask(o.id, t));
        return Transition {
            response: TaskSuspendRes { status: 300, preload: Vec::new() }, effects,
        };
    }

    i = 0;
    while i < req.actions.len()
        decreases req.actions@.len() - i,
    {
        let rr = read_object(state, &req.actions[i].awaited, now, materialize);
        effects = append_effects(effects, rr.effects);
        match rr.object {
            Some(x) => effects.push(Effect::SetPromise(
                x.id, x.promise.add_callback(&req.id),
            )),
            None => {}
        }
        i += 1;
    }
    let mut t = t0.dup();
    t.state = TaskState::Suspended;
    t.pid = None;
    t.ttl = None;
    t.lease_timeout_at = None;
    t.retry_timeout_at = None;
    t.resumes = Vec::new();
    effects.push(Effect::SetTask(o.id, t));
    Transition {
        response: TaskSuspendRes { status: 200, preload: Vec::new() }, effects,
    }
}

pub fn task_fulfill_action(
    state: &State, req: TaskFulfillReq, now: u64, materialize: bool,
) -> Transition<TaskFulfillRes> {
    if !req.action.state.settable() {
        return Transition {
            response: TaskFulfillRes { status: 400, promise: None },
            effects: Vec::new(),
        };
    }
    let read = read_task_object(state, &req.id, now, materialize);
    let o = match read.object {
        None => return Transition {
            response: TaskFulfillRes { status: 404, promise: None }, effects: read.effects,
        },
        Some(o) => o,
    };
    let t = match &o.task {
        None => return Transition {
            response: TaskFulfillRes { status: 404, promise: None }, effects: read.effects,
        },
        Some(t) => t,
    };
    if t.state != TaskState::Acquired || o.promise.state != PromiseState::Pending
        || t.version != req.version
    {
        return Transition {
            response: TaskFulfillRes { status: 409, promise: None }, effects: read.effects,
        };
    }
    let mut p = o.promise.dup();
    p.state = req.action.state;
    p.value = req.action.value;
    p.settled_at = Some(now);
    let rec = p.to_record(&o.id);
    Transition {
        response: TaskFulfillRes { status: 200, promise: Some(rec) },
        effects: append_effects(read.effects, set_settled_effects(&o, &p)),
    }
}

fn task_version_action(
    state: &State, id: &Ident, version: u64, now: u64, materialize: bool, release: bool,
) -> Transition<StatusRes> {
    let read = read_task_object(state, id, now, materialize);
    let o = match read.object {
        None => return Transition { response: StatusRes { status: 404 }, effects: read.effects },
        Some(o) => o,
    };
    let t0 = match &o.task {
        None => return Transition { response: StatusRes { status: 404 }, effects: read.effects },
        Some(t) => t,
    };
    if t0.state != TaskState::Acquired || o.promise.state != PromiseState::Pending
        || t0.version != version
    {
        return Transition { response: StatusRes { status: 409 }, effects: read.effects };
    }
    let mut t = t0.dup();
    if release {
        t.state = TaskState::Pending;
        t.pid = None;
        t.ttl = None;
        t.lease_timeout_at = None;
        t.retry_timeout_at = Some(now);
    }
    let mut effects = read.effects;
    effects.push(Effect::SetTask(o.id, t));
    Transition { response: StatusRes { status: 200 }, effects }
}

pub fn task_release_action(
    state: &State, req: &TaskReleaseReq, now: u64, materialize: bool,
) -> Transition<TaskReleaseRes> {
    task_version_action(state, &req.id, req.version, now, materialize, true)
}

pub fn task_halt_action(
    state: &State, req: &TaskHaltReq, now: u64, materialize: bool,
) -> Transition<TaskHaltRes> {
    let read = read_task_object(state, &req.id, now, materialize);
    let o = match read.object {
        None => return Transition { response: StatusRes { status: 404 }, effects: read.effects },
        Some(o) => o,
    };
    let t0 = match &o.task {
        None => return Transition { response: StatusRes { status: 404 }, effects: read.effects },
        Some(t) => t,
    };
    if t0.state == TaskState::Fulfilled {
        return Transition { response: StatusRes { status: 409 }, effects: read.effects };
    }
    if t0.state == TaskState::Halted {
        return Transition { response: StatusRes { status: 200 }, effects: read.effects };
    }
    let mut t = t0.dup();
    t.state = TaskState::Halted;
    t.pid = None;
    t.ttl = None;
    t.lease_timeout_at = None;
    t.retry_timeout_at = None;
    let mut effects = read.effects;
    effects.push(Effect::SetTask(o.id, t));
    Transition { response: StatusRes { status: 200 }, effects }
}

pub fn task_continue_action(
    state: &State, req: &TaskContinueReq, now: u64, materialize: bool,
) -> Transition<TaskContinueRes> {
    let read = read_task_object(state, &req.id, now, materialize);
    let o = match read.object {
        None => return Transition { response: StatusRes { status: 404 }, effects: read.effects },
        Some(o) => o,
    };
    let t0 = match &o.task {
        None => return Transition { response: StatusRes { status: 404 }, effects: read.effects },
        Some(t) => t,
    };
    if t0.state != TaskState::Halted || o.promise.state != PromiseState::Pending {
        return Transition { response: StatusRes { status: 409 }, effects: read.effects };
    }
    let mut t = t0.dup();
    t.state = TaskState::Pending;
    t.retry_timeout_at = Some(now);
    let mut effects = read.effects;
    effects.push(Effect::SetTask(o.id, t));
    Transition { response: StatusRes { status: 200 }, effects }
}

pub fn task_search_action(
    _state: &State, _req: &TaskSearchReq, _now: u64, _materialize: bool,
) -> Transition<TaskSearchRes> {
    Transition {
        response: TaskSearchRes { status: 501, tasks: Vec::new(), cursor: None },
        effects: Vec::new(),
    }
}

pub fn schedule_get_action(
    state: &State, req: &ScheduleGetReq, _now: u64, _materialize: bool,
) -> Transition<ScheduleGetRes> {
    match state.find_schedule(&req.id) {
        None => Transition {
            response: ScheduleRes { status: 404, schedule: None }, effects: Vec::new(),
        },
        Some(i) => Transition {
            response: ScheduleRes { status: 200, schedule: Some(state.schedules[i].dup()) },
            effects: Vec::new(),
        },
    }
}

pub fn schedule_create_action(
    state: &State, req: ScheduleCreateReq, now: u64, _materialize: bool,
) -> Transition<ScheduleCreateRes> {
    if tags_timer_targeted(&req.promise_tags) {
        return Transition {
            response: ScheduleRes { status: 400, schedule: None }, effects: Vec::new(),
        };
    }
    match state.find_schedule(&req.id) {
        Some(i) => Transition {
            response: ScheduleRes { status: 200, schedule: Some(state.schedules[i].dup()) },
            effects: Vec::new(),
        },
        None => {
            let s = Schedule {
                id: req.id, cron: req.cron, promise_id: req.promise_id,
                promise_timeout: req.promise_timeout, promise_param: req.promise_param,
                promise_tags: req.promise_tags, next_run_at: req.next_run_at,
                last_run_at: None, created_at: now,
            };
            let mut effects = Vec::new();
            effects.push(Effect::SetSchedule(s.dup()));
            Transition {
                response: ScheduleRes { status: 200, schedule: Some(s) }, effects,
            }
        }
    }
}

pub fn schedule_delete_action(
    state: &State, req: &ScheduleDeleteReq, _now: u64, _materialize: bool,
) -> Transition<ScheduleDeleteRes> {
    match state.find_schedule(&req.id) {
        None => Transition {
            response: ScheduleDeleteRes { status: 404 }, effects: Vec::new(),
        },
        Some(i) => {
            let mut effects = Vec::new();
            effects.push(Effect::DeleteSchedule(state.schedules[i].id.dup()));
            Transition { response: ScheduleDeleteRes { status: 200 }, effects }
        }
    }
}

pub fn schedule_search_action(
    _state: &State, _req: &ScheduleSearchReq, _now: u64, _materialize: bool,
) -> Transition<ScheduleSearchRes> {
    Transition {
        response: ScheduleSearchRes { status: 501, schedules: Vec::new(), cursor: None },
        effects: Vec::new(),
    }
}

} // verus!
