//! Handler specifications. Each `spec_*` is the mathematical step.
//! `promise_create` and the other handlers in the kernel are proved equal to these.

use vstd::prelude::*;

use crate::object::*;
use crate::properties::*;
use crate::state::*;
use crate::tags::OType;
use crate::tags::*;
use crate::types::*;

verus! {

/// The step wrote no object outside `ids`, and no schedule or outbox entry.
pub open spec fn touches_only(a: AState, b: AState, ids: spec_fn(Seq<char>) -> bool) -> bool {
    &&& forall|z: Seq<char>| !ids(z) ==>
        (a.objects.contains_key(z) <==> #[trigger] b.objects.contains_key(z))
        && (a.objects.contains_key(z) ==> a.objects[z] == b.objects[z])
    &&& b.schedules == a.schedules
    &&& b.outbox == a.outbox
}


// ---------------------------------------------------------------------------
// The handlers as functions of the abstract state
// ---------------------------------------------------------------------------
//
// Each `spec_*` is the handler's meaning: the state it leaves and the
// response it gives, in the vocabulary of `object.rs`. The executable
// handler below ensures it computes its `spec_*`, and `external_proof`
// proves the catalogue of each `spec_*`. The system model carries requests
// into steps through these.

/// `readObject` as a function of the state: the object at `id`, projected
/// at `now` and persisted; nothing if there is none.
pub open spec fn spec_read(a: AState, id: Seq<char>, now: nat) -> AState {
    if a.objects.contains_key(id) {
        AState { objects: a.objects.insert(id, a.objects[id].project(now)), ..a }
    } else {
        a
    }
}

/// `readTaskObject`: as `spec_read`, for an object with a task.
pub open spec fn spec_read_task(a: AState, id: Seq<char>, now: nat) -> AState {
    if a.has_task(id) { spec_read(a, id, now) } else { a }
}

pub open spec fn with_objects(a: AState, objects: Map<Seq<char>, APromise>) -> AState {
    AState { objects, ..a }
}

pub open spec fn spec_promise_get(a: AState, req: APromiseGetReq, now: nat) -> (AState, APromiseRes) {
    if a.objects.contains_key(req.id) {
        let b = spec_read(a, req.id, now);
        (b, APromiseRes { status: 200, promise: Some(b.objects[req.id].to_record()) })
    } else {
        (a, APromiseRes { status: 404, promise: None })
    }
}

pub open spec fn spec_promise_create(a: AState, req: APromiseCreateReq, now: nat) -> (AState, APromiseRes) {
    if crate::tags::timer_targeted(req.tags) || req.timeout_at > MAX_TIME {
        (a, APromiseRes { status: 400, promise: None })
    } else if a.objects.contains_key(req.id) {
        let b = spec_read(a, req.id, now);
        (b, APromiseRes { status: 200, promise: Some(b.objects[req.id].to_record()) })
    } else {
        let p = spec_create(req, now);
        (with_objects(a, a.objects.insert(req.id, p)), APromiseRes { status: 200, promise: Some(p.to_record()) })
    }
}

pub open spec fn spec_promise_settle(a: AState, req: APromiseSettleReq, now: nat) -> (AState, APromiseRes) {
    if !req.state.spec_settable() {
        (a, APromiseRes { status: 400, promise: None })
    } else if !a.objects.contains_key(req.id) {
        (a, APromiseRes { status: 404, promise: None })
    } else {
        let b = spec_read(a, req.id, now);
        if b.objects[req.id].state == PromiseState::Pending {
            let c = with_objects(b, b.objects.insert(req.id, b.objects[req.id].settle(req.state, req.value, now)));
            (c, APromiseRes { status: 200, promise: Some(c.objects[req.id].to_record()) })
        } else {
            (b, APromiseRes { status: 200, promise: Some(b.objects[req.id].to_record()) })
        }
    }
}

pub open spec fn spec_promise_register_callback(a: AState, req: APromiseRegisterCallbackReq, now: nat) -> (AState, APromiseRes) {
    let x = req.awaited;
    let y = req.awaiter;
    if x == y || !crate::types::same_origin_spec(x, y) {
        (a, APromiseRes { status: 400, promise: None })
    } else if !a.objects.contains_key(x) {
        (a, APromiseRes { status: 404, promise: None })
    } else {
        let a1 = spec_read(a, x, now);
        if !a1.objects.contains_key(y) {
            (a1, APromiseRes { status: 422, promise: None })
        } else {
            let a2 = spec_read(a1, y, now);
            if a2.objects[y].otype() != OType::Runnable || !a2.objects[x].otype().awaitable() {
                (a2, APromiseRes { status: 422, promise: None })
            } else if a2.objects[x].state == PromiseState::Pending && a2.objects[y].state == PromiseState::Pending {
                let a3 = with_objects(a2, a2.objects.insert(x, a2.objects[x].add_callback(y)));
                (a3, APromiseRes { status: 200, promise: Some(a3.objects[x].to_record()) })
            } else {
                (a2, APromiseRes { status: 200, promise: Some(a2.objects[x].to_record()) })
            }
        }
    }
}

pub open spec fn spec_promise_register_listener(a: AState, req: APromiseRegisterListenerReq, now: nat) -> (AState, APromiseRes) {
    let x = req.awaited;
    if !a.objects.contains_key(x) {
        (a, APromiseRes { status: 404, promise: None })
    } else {
        let b = spec_read(a, x, now);
        if !b.objects[x].otype().awaitable() {
            (b, APromiseRes { status: 422, promise: None })
        } else if b.objects[x].state == PromiseState::Pending {
            let c = with_objects(b, b.objects.insert(x, b.objects[x].add_listener(req.address)));
            (c, APromiseRes { status: 200, promise: Some(c.objects[x].to_record()) })
        } else {
            (b, APromiseRes { status: 200, promise: Some(b.objects[x].to_record()) })
        }
    }
}

pub open spec fn spec_schedule_get(a: AState, req: AScheduleGetReq, now: nat) -> (AState, AScheduleRes) {
    if a.schedules.contains_key(req.id) {
        (a, AScheduleRes { status: 200, schedule: Some(a.schedules[req.id]) })
    } else {
        (a, AScheduleRes { status: 404, schedule: None })
    }
}

/// The schedule `schedule.create` writes.
pub open spec fn spec_new_schedule(req: AScheduleCreateReq, now: nat) -> ASchedule {
    ASchedule {
        id: req.id,
        cron: req.cron,
        promise_id: req.promise_id,
        promise_timeout: req.promise_timeout,
        promise_param: req.promise_param,
        promise_tags: req.promise_tags,
        next_run_at: req.next_run_at,
        last_run_at: None,
        created_at: now as u64,
    }
}

pub open spec fn spec_schedule_create(a: AState, req: AScheduleCreateReq, now: nat) -> (AState, AScheduleRes) {
    if crate::tags::timer_targeted(req.promise_tags) || req.promise_timeout > MAX_TIME || req.next_run_at < now {
        (a, AScheduleRes { status: 400, schedule: None })
    } else if a.schedules.contains_key(req.id) {
        (a, AScheduleRes { status: 200, schedule: Some(a.schedules[req.id]) })
    } else {
        let c = spec_new_schedule(req, now);
        (AState { schedules: a.schedules.insert(req.id, c), ..a }, AScheduleRes { status: 200, schedule: Some(c) })
    }
}

pub open spec fn spec_schedule_delete(a: AState, req: AScheduleDeleteReq, now: nat) -> (AState, AStatusRes) {
    if a.schedules.contains_key(req.id) {
        (AState { schedules: a.schedules.remove(req.id), ..a }, AStatusRes { status: 200 })
    } else {
        (a, AStatusRes { status: 404 })
    }
}


pub open spec fn spec_task_get(a: AState, req: ATaskGetReq, now: nat) -> (AState, ATaskGetRes) {
    if !a.has_task(req.id) {
        (a, ATaskGetRes { status: 404, task: None })
    } else {
        let b = spec_read_task(a, req.id, now);
        match b.objects[req.id].task {
            None => (b, ATaskGetRes { status: 404, task: None }),
            Some(t) => (b, ATaskGetRes { status: 200, task: Some(t.to_record(req.id)) }),
        }
    }
}

/// The records a claim answers with: the task's and the promise's.
pub open spec fn claim_of(p: APromise) -> ATaskClaimRes {
    ATaskClaimRes {
        status: 200,
        task: match p.task { Some(t) => Some(t.to_record(p.id)), None => None },
        promise: Some(p.to_record()),
    }
}

pub open spec fn claim_err(status: u16) -> ATaskClaimRes {
    ATaskClaimRes { status, task: None, promise: None }
}

pub open spec fn spec_task_create(a: AState, req: ATaskCreateReq, now: nat) -> (AState, ATaskClaimRes) {
    let act = req.action;
    if crate::tags::otype(act.tags) != OType::Runnable || crate::tags::timer_targeted(act.tags)
        || act.timeout_at > MAX_TIME || req.ttl > MAX_TIME {
        (a, claim_err(400))
    } else if !a.objects.contains_key(act.id) {
        let p = if act.timeout_at > now { spec_create_acquired(act, req.pid, req.ttl as nat, now) } else { spec_create(act, now) };
        (with_objects(a, a.objects.insert(act.id, p)), claim_of(p))
    } else {
        let b = spec_read(a, act.id, now);
        let p = b.objects[act.id];
        if p.otype() != OType::Runnable {
            (b, claim_err(422))
        } else {
            match p.task {
                None => (b, claim_err(409)),
                Some(t) => {
                    if t.state == TaskState::Fulfilled {
                        (b, claim_of(p))
                    } else if t.state != TaskState::Pending || t.version >= MAX_VERSION {
                        (b, claim_err(409))
                    } else {
                        let c = with_objects(b, b.objects.insert(act.id, p.with_task(t.acquire(req.pid, req.ttl as nat, now))));
                        (c, claim_of(c.objects[act.id]))
                    }
                }
            }
        }
    }
}

pub open spec fn spec_task_acquire(a: AState, req: ATaskAcquireReq, now: nat) -> (AState, ATaskClaimRes) {
    if req.ttl > MAX_TIME {
        (a, claim_err(400))
    } else if !a.has_task(req.id) {
        (a, claim_err(404))
    } else {
        let b = spec_read_task(a, req.id, now);
        let p = b.objects[req.id];
        match p.task {
            None => (b, claim_err(404)),
            Some(t) => {
                if t.state != TaskState::Pending || p.state != PromiseState::Pending || t.version != req.version || t.version >= MAX_VERSION {
                    (b, claim_err(409))
                } else {
                    let c = with_objects(b, b.objects.insert(req.id, p.with_task(t.acquire(req.pid, req.ttl as nat, now))));
                    (c, claim_of(c.objects[req.id]))
                }
            }
        }
    }
}

pub open spec fn spec_task_fulfill(a: AState, req: ATaskFulfillReq, now: nat) -> (AState, APromiseRes) {
    if !req.action.state.spec_settable() {
        (a, APromiseRes { status: 400, promise: None })
    } else if !a.has_task(req.id) {
        (a, APromiseRes { status: 404, promise: None })
    } else {
        let b = spec_read_task(a, req.id, now);
        let p = b.objects[req.id];
        match p.task {
            None => (b, APromiseRes { status: 404, promise: None }),
            Some(t) => {
                if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != req.version {
                    (b, APromiseRes { status: 409, promise: None })
                } else {
                    let c = with_objects(b, b.objects.insert(req.id, p.settle(req.action.state, req.action.value, now)));
                    (c, APromiseRes { status: 200, promise: Some(c.objects[req.id].to_record()) })
                }
            }
        }
    }
}

pub open spec fn spec_task_release(a: AState, req: ATaskReleaseReq, now: nat) -> (AState, AStatusRes) {
    if !a.has_task(req.id) {
        (a, AStatusRes { status: 404 })
    } else {
        let b = spec_read_task(a, req.id, now);
        let p = b.objects[req.id];
        match p.task {
            None => (b, AStatusRes { status: 404 }),
            Some(t) => {
                if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != req.version {
                    (b, AStatusRes { status: 409 })
                } else {
                    (with_objects(b, b.objects.insert(req.id, p.with_task(t.release(now)))), AStatusRes { status: 200 })
                }
            }
        }
    }
}

pub open spec fn spec_task_halt(a: AState, req: ATaskHaltReq, now: nat) -> (AState, AStatusRes) {
    if !a.has_task(req.id) {
        (a, AStatusRes { status: 404 })
    } else {
        let b = spec_read_task(a, req.id, now);
        let p = b.objects[req.id];
        match p.task {
            None => (b, AStatusRes { status: 404 }),
            Some(t) => {
                if t.state == TaskState::Fulfilled {
                    (b, AStatusRes { status: 409 })
                } else if t.state == TaskState::Halted {
                    (b, AStatusRes { status: 200 })
                } else {
                    (with_objects(b, b.objects.insert(req.id, p.with_task(t.halt()))), AStatusRes { status: 200 })
                }
            }
        }
    }
}

pub open spec fn spec_task_continue(a: AState, req: ATaskContinueReq, now: nat) -> (AState, AStatusRes) {
    if !a.has_task(req.id) {
        (a, AStatusRes { status: 404 })
    } else {
        let b = spec_read_task(a, req.id, now);
        let p = b.objects[req.id];
        match p.task {
            None => (b, AStatusRes { status: 404 }),
            Some(t) => {
                if t.state != TaskState::Halted || p.state != PromiseState::Pending {
                    (b, AStatusRes { status: 409 })
                } else {
                    (with_objects(b, b.objects.insert(req.id, p.with_task(t.continue_(now)))), AStatusRes { status: 200 })
                }
            }
        }
    }
}

pub open spec fn fence_target(act: ATaskFenceAction) -> Seq<char> {
    match act {
        ATaskFenceAction::Create(c) => c.id,
        ATaskFenceAction::Settle(c) => c.id,
    }
}

pub open spec fn spec_task_fence(a: AState, req: ATaskFenceReq, now: nat) -> (AState, ATaskFenceRes) {
    let target = fence_target(req.action);
    if target == req.id || !crate::types::same_origin_spec(target, req.id) {
        (a, ATaskFenceRes { status: 400, action: None })
    } else if !a.has_task(req.id) {
        (a, ATaskFenceRes { status: 404, action: None })
    } else {
        let b = spec_read_task(a, req.id, now);
        let p = b.objects[req.id];
        match p.task {
            None => (b, ATaskFenceRes { status: 404, action: None }),
            Some(t) => {
                if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != req.version {
                    (b, ATaskFenceRes { status: 409, action: None })
                } else {
                    match req.action {
                        ATaskFenceAction::Create(c) => {
                            let (d, r) = spec_promise_create(b, c, now);
                            (d, ATaskFenceRes { status: 200, action: Some(ATaskFenceInnerRes::Create(r)) })
                        }
                        ATaskFenceAction::Settle(c) => {
                            let (d, r) = spec_promise_settle(b, c, now);
                            (d, ATaskFenceRes { status: 200, action: Some(ATaskFenceInnerRes::Settle(r)) })
                        }
                    }
                }
            }
        }
    }
}


/// `task.fence` with no action: the check alone. A fence whose create targets
/// another origin runs the create first, as a request of its own on that
/// origin's document, and then this on the task's: the two documents commit one
/// at a time, the create before the check, so a stale fence still leaves the
/// promise created and answers its 409.
pub open spec fn spec_task_fence_check(a: AState, req: ATaskFenceCheckReq, now: nat) -> (AState, AStatusRes) {
    if !a.has_task(req.id) {
        (a, AStatusRes { status: 404 })
    } else {
        let b = spec_read_task(a, req.id, now);
        let p = b.objects[req.id];
        match p.task {
            None => (b, AStatusRes { status: 404 }),
            Some(t) => {
                if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != req.version {
                    (b, AStatusRes { status: 409 })
                } else {
                    (b, AStatusRes { status: 200 })
                }
            }
        }
    }
}

// --- task.heartbeat: a fold over the refs ---

/// Some ref among the first `k` names `x`.
pub open spec fn ref_touched(refs: Seq<ATaskRef>, k: int, x: Seq<char>) -> bool {
    exists|j: int| 0 <= j < k && #[trigger] refs[j].id == x
}

/// Some ref names `x`.
pub open spec fn ref_of(refs: Seq<ATaskRef>, x: Seq<char>) -> bool {
    ref_touched(refs, refs.len() as int, x)
}

/// One ref of a heartbeat: the task object read and, if it is the lease
/// named, acquired by `pid` and live, its lease refreshed.
pub open spec fn spec_heartbeat_one(a: AState, pid: Seq<char>, r: ATaskRef, now: nat) -> AState {
    if !a.has_task(r.id) {
        a
    } else {
        let b = spec_read_task(a, r.id, now);
        let p = b.objects[r.id];
        match p.task {
            Some(t) => {
                if t.state == TaskState::Acquired && t.version == r.version && t.pid == Some(pid) && p.state == PromiseState::Pending {
                    with_objects(b, b.objects.insert(r.id, p.with_task(t.heartbeat(now))))
                } else {
                    b
                }
            }
            None => b,
        }
    }
}

/// The first `k` refs, one after the other.
pub open spec fn spec_heartbeat_fold(a: AState, pid: Seq<char>, refs: Seq<ATaskRef>, k: int, now: nat) -> AState
    decreases k,
{
    if k <= 0 { a } else { spec_heartbeat_one(spec_heartbeat_fold(a, pid, refs, k - 1, now), pid, refs[k - 1], now) }
}

pub open spec fn spec_task_heartbeat(a: AState, req: ATaskHeartbeatReq, now: nat) -> (AState, AStatusRes) {
    (spec_heartbeat_fold(a, req.pid, req.tasks, req.tasks.len() as int, now), AStatusRes { status: 200 })
}

// --- task.suspend: two folds over the actions ---

/// Some action among the first `k` awaits `x`.
pub open spec fn awaited_touched(actions: Seq<APromiseRegisterCallbackReq>, k: int, x: Seq<char>) -> bool {
    exists|j: int| 0 <= j < k && #[trigger] actions[j].awaited == x
}

/// Some action awaits `x`.
pub open spec fn awaited_of(actions: Seq<APromiseRegisterCallbackReq>, x: Seq<char>) -> bool {
    awaited_touched(actions, actions.len() as int, x)
}

pub open spec fn awaited_distinct(actions: Seq<APromiseRegisterCallbackReq>) -> bool {
    forall|i: int, j: int| 0 <= i < actions.len() && 0 <= j < actions.len()
        && #[trigger] actions[i].awaited == #[trigger] actions[j].awaited ==> i == j
}

/// The door checks of `task.suspend`: some action, each awaiting a distinct
/// promise of the task's own origin, never the task itself.
pub open spec fn suspend_doors(actions: Seq<APromiseRegisterCallbackReq>, id: Seq<char>) -> bool {
    &&& actions.len() > 0
    &&& awaited_distinct(actions)
    &&& forall|j: int| 0 <= j < actions.len() ==>
        #[trigger] actions[j].awaited != id && crate::types::same_origin_spec(actions[j].awaited, id)
}

/// The first `k` awaited promises, read: each projected where it exists.
pub open spec fn spec_awaited_read(a: AState, actions: Seq<APromiseRegisterCallbackReq>, k: int, now: nat) -> AState
    decreases k,
{
    if k <= 0 { a } else { spec_read(spec_awaited_read(a, actions, k - 1, now), actions[k - 1].awaited, now) }
}

/// The check an awaited promise fails: it is not there, or not awaitable.
pub open spec fn awaited_fails(a: AState, act: APromiseRegisterCallbackReq) -> bool {
    !a.objects.contains_key(act.awaited) || !a.objects[act.awaited].otype().awaitable()
}

/// The first of the first `k` actions that fails the check, if any.
pub open spec fn first_failing(a: AState, actions: Seq<APromiseRegisterCallbackReq>, k: int) -> Option<int>
    decreases k,
{
    if k <= 0 {
        None
    } else {
        match first_failing(a, actions, k - 1) {
            Some(j) => Some(j),
            None => if awaited_fails(a, actions[k - 1]) { Some(k - 1) } else { None },
        }
    }
}

/// Some awaited promise is settled at `now`.
pub open spec fn any_settled(a: AState, actions: Seq<APromiseRegisterCallbackReq>, now: nat) -> bool {
    exists|j: int| 0 <= j < actions.len() && a.objects[#[trigger] actions[j].awaited].project(now).state != PromiseState::Pending
}

/// `id` registered as a callback on the first `k` awaited promises.
pub open spec fn spec_awaited_register(a: AState, actions: Seq<APromiseRegisterCallbackReq>, k: int, id: Seq<char>) -> AState
    decreases k,
{
    if k <= 0 {
        a
    } else {
        let s = spec_awaited_register(a, actions, k - 1, id);
        let w = actions[k - 1].awaited;
        with_objects(s, s.objects.insert(w, s.objects[w].add_callback(id)))
    }
}

pub open spec fn spec_task_suspend(a: AState, req: ATaskSuspendReq, now: nat) -> (AState, AStatusRes) {
    let id = req.id;
    let acts = req.actions;
    let n = acts.len() as int;
    if !suspend_doors(acts, id) {
        (a, AStatusRes { status: 400 })
    } else if !a.has_task(id) {
        (a, AStatusRes { status: 404 })
    } else {
        let b = spec_read_task(a, id, now);
        let p = b.objects[id];
        match p.task {
            None => (b, AStatusRes { status: 404 }),
            Some(t) => {
                if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != req.version {
                    (b, AStatusRes { status: 409 })
                } else {
                    match first_failing(b, acts, n) {
                        // the check stopped at `j`: what it had read stays read
                        Some(j) => {
                            let m = if b.objects.contains_key(acts[j].awaited) { j + 1 } else { j };
                            (spec_awaited_read(b, acts, m, now), AStatusRes { status: 422 })
                        }
                        None => {
                            let c = spec_awaited_read(b, acts, n, now);
                            if any_settled(b, acts, now) {
                                (with_objects(c, c.objects.insert(id, c.objects[id].with_task(t.clear_resumes()))), AStatusRes { status: 300 })
                            } else {
                                let d = spec_awaited_register(c, acts, n, id);
                                (with_objects(d, d.objects.insert(id, d.objects[id].with_task(t.suspend()))), AStatusRes { status: 200 })
                            }
                        }
                    }
                }
            }
        }
    }
}

/// A request about a schedule: served on the schedule's document, where
/// there are no objects; every other request on its id's origin, where
/// there are no schedules.
pub open spec fn is_schedule_request(req: ARequest) -> bool {
    match req {
        ARequest::ScheduleGet(_) | ARequest::ScheduleCreate(_) | ARequest::ScheduleDelete(_) => true,
        _ => false,
    }
}

/// Any request, as a function of the abstract state: the handler for its
/// kind. What the system model carries a request into a step through.
pub open spec fn spec_handle(a: AState, req: ARequest, now: nat) -> (AState, AResponse) {
    match req {
        ARequest::PromiseGet(q) => { let (b, r) = spec_promise_get(a, q, now); (b, AResponse::Promise(r)) }
        ARequest::PromiseCreate(q) => { let (b, r) = spec_promise_create(a, q, now); (b, AResponse::Promise(r)) }
        ARequest::PromiseSettle(q) => { let (b, r) = spec_promise_settle(a, q, now); (b, AResponse::Promise(r)) }
        ARequest::PromiseRegisterCallback(q) => { let (b, r) = spec_promise_register_callback(a, q, now); (b, AResponse::Promise(r)) }
        ARequest::PromiseRegisterListener(q) => { let (b, r) = spec_promise_register_listener(a, q, now); (b, AResponse::Promise(r)) }
        ARequest::ScheduleGet(q) => { let (b, r) = spec_schedule_get(a, q, now); (b, AResponse::Schedule(r)) }
        ARequest::ScheduleCreate(q) => { let (b, r) = spec_schedule_create(a, q, now); (b, AResponse::Schedule(r)) }
        ARequest::ScheduleDelete(q) => { let (b, r) = spec_schedule_delete(a, q, now); (b, AResponse::Status(r)) }
        ARequest::TaskGet(q) => { let (b, r) = spec_task_get(a, q, now); (b, AResponse::TaskGet(r)) }
        ARequest::TaskCreate(q) => { let (b, r) = spec_task_create(a, q, now); (b, AResponse::TaskClaim(r)) }
        ARequest::TaskAcquire(q) => { let (b, r) = spec_task_acquire(a, q, now); (b, AResponse::TaskClaim(r)) }
        ARequest::TaskFulfill(q) => { let (b, r) = spec_task_fulfill(a, q, now); (b, AResponse::Promise(r)) }
        ARequest::TaskRelease(q) => { let (b, r) = spec_task_release(a, q, now); (b, AResponse::Status(r)) }
        ARequest::TaskHalt(q) => { let (b, r) = spec_task_halt(a, q, now); (b, AResponse::Status(r)) }
        ARequest::TaskContinue(q) => { let (b, r) = spec_task_continue(a, q, now); (b, AResponse::Status(r)) }
        ARequest::TaskFence(q) => { let (b, r) = spec_task_fence(a, q, now); (b, AResponse::TaskFence(r)) }
        ARequest::TaskFenceCheck(q) => { let (b, r) = spec_task_fence_check(a, q, now); (b, AResponse::Status(r)) }
        ARequest::TaskHeartbeat(q) => { let (b, r) = spec_task_heartbeat(a, q, now); (b, AResponse::Status(r)) }
        ARequest::TaskSuspend(q) => { let (b, r) = spec_task_suspend(a, q, now); (b, AResponse::Status(r)) }
    }
}

/// The pointer frame of a step that keeps every object's tags and loses no
/// callback: what `lemma_task_edit_frame` needs of the rest of the store.
pub open spec fn pointer_frame(a: AState, b: AState) -> bool {
    forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z)
}

// ---------------------------------------------------------------------------
// Shapes a loop leaves behind
// ---------------------------------------------------------------------------

/// What a heartbeat leaves at `x`: the object untouched, projected, or its
/// acquired lease refreshed.
pub open spec fn heartbeat_shape(now: nat, a: AState, b: AState, x: Seq<char>) -> bool {
    &&& !a.objects.contains_key(x) ==> !b.objects.contains_key(x)
    &&& a.objects.contains_key(x) ==> b.objects.contains_key(x) && {
        let p = a.objects[x];
        ||| b.objects[x] == p
        ||| b.objects[x] == p.project(now)
        ||| (p.task is Some && p.task.unwrap().state == TaskState::Acquired
                && p.state == PromiseState::Pending && p.timeout_at > now
                && b.objects[x] == p.with_task(p.task.unwrap().heartbeat(now)))
    }
}

/// The task `task.suspend` found: acquired, on a pending promise ahead of its
/// deadline — so its projection was the identity.
pub open spec fn suspend_base(now: nat, a: AState, id: Seq<char>) -> bool {
    &&& inv(now, a)
    &&& a.objects.contains_key(id)
    &&& a.objects[id].task is Some
    &&& a.objects[id].task.unwrap().state == TaskState::Acquired
    &&& a.objects[id].state == PromiseState::Pending
    &&& a.objects[id].timeout_at > now
}

pub open spec fn unchanged_at(a: AState, b: AState, x: Seq<char>) -> bool {
    (a.objects.contains_key(x) <==> b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x])
}


} // verus!
