//! External steps: the request handlers.
//!
//! Each handler is `spec/02-abstract/external.lean`'s, under the
//! materialising reading (`mat = true`): a read projects the object at `now`
//! and persists what the projection moved. Every handler takes `now` and
//! the configuration, and ensures the whole catalogue: `inv` on the state it
//! leaves and `legal` on the pair. The promise handlers, then the schedule
//! handlers, then the task handlers: first those that touch one object, then
//! `task.fence`, which runs a promise handler on behalf of a task,
//! `task.heartbeat`, which refreshes many leases, and `task.suspend`, which
//! registers a task on many promises.
//!
//! The spec functions the contracts name are here; the lemmas the bodies
//! invoke are in `external_proof`.

use vstd::prelude::*;

use crate::external_proof::*;
use crate::object::*;
use crate::properties::*;
use crate::properties_proof::*;
use crate::store::*;
use crate::store_proof::*;
use crate::tags::OType;
use crate::types::*;

verus! {

/// What every handler requires of its inputs.
pub open spec fn pre(s: State, now: u64, cfg: Config) -> bool {
    &&& s.wf()
    &&& inv(now as nat, s@)
    &&& now <= MAX_TIME
    &&& cfg.wf()
}

/// What every handler ensures of its outputs.
pub open spec fn post(a: State, b: State, now: u64) -> bool {
    &&& b.wf()
    &&& inv(now as nat, b@)
    &&& legal(now as nat, a@, b@)
}

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
                    } else if t.state != TaskState::Pending || t.version >= MAX_TIME {
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
                if t.state != TaskState::Pending || p.state != PromiseState::Pending || t.version != req.version || t.version >= MAX_TIME {
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
        ARequest::TaskHeartbeat(q) => { let (b, r) = spec_task_heartbeat(a, q, now); (b, AResponse::Status(r)) }
        ARequest::TaskSuspend(q) => { let (b, r) = spec_task_suspend(a, q, now); (b, AResponse::Status(r)) }
    }
}

impl State {
    /// Any request: the handler for its kind. Computes `spec_handle`.
    pub fn handle(&mut self, req: &Request, now: u64, cfg: &Config) -> (r: Response)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_handle(old(self)@, req@, now as nat).0,
            r@ == spec_handle(old(self)@, req@, now as nat).1,
    {
        match req {
            Request::PromiseGet(q) => Response::Promise(self.promise_get(q, now, cfg)),
            Request::PromiseCreate(q) => Response::Promise(self.promise_create(q, now, cfg)),
            Request::PromiseSettle(q) => Response::Promise(self.promise_settle(q, now, cfg)),
            Request::PromiseRegisterCallback(q) => Response::Promise(self.promise_register_callback(q, now, cfg)),
            Request::PromiseRegisterListener(q) => Response::Promise(self.promise_register_listener(q, now, cfg)),
            Request::ScheduleGet(q) => Response::Schedule(self.schedule_get(q, now, cfg)),
            Request::ScheduleCreate(q) => Response::Schedule(self.schedule_create(q, now, cfg)),
            Request::ScheduleDelete(q) => Response::Status(self.schedule_delete(q, now, cfg)),
            Request::TaskGet(q) => Response::TaskGet(self.task_get(q, now, cfg)),
            Request::TaskCreate(q) => Response::TaskClaim(self.task_create(q, now, cfg)),
            Request::TaskAcquire(q) => Response::TaskClaim(self.task_acquire(q, now, cfg)),
            Request::TaskFulfill(q) => Response::Promise(self.task_fulfill(q, now, cfg)),
            Request::TaskRelease(q) => Response::Status(self.task_release(q, now, cfg)),
            Request::TaskHalt(q) => Response::Status(self.task_halt(q, now, cfg)),
            Request::TaskContinue(q) => Response::Status(self.task_continue(q, now, cfg)),
            Request::TaskFence(q) => Response::TaskFence(self.task_fence(q, now, cfg)),
            Request::TaskHeartbeat(q) => Response::Status(self.task_heartbeat(q, now, cfg)),
            Request::TaskSuspend(q) => Response::Status(self.task_suspend(q, now, cfg)),
        }
    }

    /// `readObject`: find the object, project it at `now`, persist the
    /// projection. Returns its row index.
    pub fn read_object(&mut self, id: &String, now: u64) -> (r: Option<usize>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).schedules == old(self).schedules,
            final(self).outbox == old(self).outbox,
            final(self)@.schedules == old(self)@.schedules,
            final(self)@.outbox == old(self)@.outbox,
            match r {
                None => {
                    &&& !old(self)@.objects.contains_key(id@)
                    &&& *final(self) == *old(self)
                },
                Some(i) => {
                    &&& i < final(self).objects@.len()
                    &&& final(self).objects@ == old(self).objects@.update(i as int, final(self).objects@[i as int])
                    &&& old(self).objects@[i as int].id@ == id@
                    &&& final(self).objects@[i as int]@ == old(self).objects@[i as int]@.project(now as nat)
                    &&& final(self).objects@[i as int].id@ == id@
                    &&& old(self)@.objects.contains_key(id@)
                    &&& final(self).objects@[i as int]@ == old(self)@.objects[id@].project(now as nat)
                    &&& final(self)@.objects == old(self)@.objects.insert(id@, old(self)@.objects[id@].project(now as nat))
                },
            },
    {
        match self.find_object(id) {
            None => None,
            Some(i) => {
                let ghost before = self.objects@;
                proof {
                    self.lemma_object_at(i as int);
                }
                self.objects[i].project(now);
                proof {
                    crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                }
                Some(i)
            }
        }
    }

    /// `promise.get`.
    pub fn promise_get(&mut self, req: &PromiseGetReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_get(old(self)@, req@, now as nat).0,
            r@ == spec_promise_get(old(self)@, req@, now as nat).1,
            match r.promise {
                None => r.status == 404 && !old(self)@.objects.contains_key(req.id@),
                Some(p) => r.status == 200 && old(self)@.objects.contains_key(req.id@)
                    && p@ == old(self)@.objects[req.id@].project(now as nat).to_record(),
            },
    {
        let ghost a = self@;
        match self.read_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                PromiseRes { status: 404, promise: None }
            }
            Some(i) => {
                let rec = self.objects[i].to_record();
                proof {
                    lemma_project_legal(now as nat, a, self@, req.id@);
                }
                PromiseRes { status: 200, promise: Some(rec) }
            }
        }
    }

    /// `promise.create`.
    pub fn promise_create(&mut self, req: &PromiseCreateReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_create(old(self)@, req@, now as nat).0,
            r@ == spec_promise_create(old(self)@, req@, now as nat).1,
            touches_only(old(self)@, final(self)@, |z: Seq<char>| z == req.id@),
            r.status == 200 || r.status == 400,
    {
        let ghost a = self@;
        if crate::tags::exec_timer_targeted(&req.tags) || req.timeout_at > MAX_TIME {
            proof { crate::properties_proof::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        match self.read_object(&req.id, now) {
            Some(i) => {
                let rec = self.objects[i].to_record();
                proof { lemma_project_legal(now as nat, a, self@, req.id@); }
                PromiseRes { status: 200, promise: Some(rec) }
            }
            None => {
                let p = create_promise(req, now);
                let rec = p.to_record();
                self.push_object(p);
                proof { lemma_create_legal(now as nat, a, self@, req@); }
                PromiseRes { status: 200, promise: Some(rec) }
            }
        }
    }

    /// `promise.settle`.
    pub fn promise_settle(&mut self, req: &PromiseSettleReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_settle(old(self)@, req@, now as nat).0,
            r@ == spec_promise_settle(old(self)@, req@, now as nat).1,
            touches_only(old(self)@, final(self)@, |z: Seq<char>| z == req.id@),
            r.status == 200 || r.status == 400 || r.status == 404,
    {
        let ghost a = self@;
        if !req.state.settable() {
            proof { crate::properties_proof::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        match self.read_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                PromiseRes { status: 404, promise: None }
            }
            Some(i) => {
                if self.objects[i].state == PromiseState::Pending {
                    let ghost before = self.objects@;
                    self.objects[i].settle(req.state, req.value.dup(), now);
                    proof {
                        crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                        assert(self@.objects =~= a.objects.insert(req.id@, a.objects[req.id@].project(now as nat).settle(req.state, req.value@, now as nat)));
                        lemma_settle_legal(now as nat, a, self@, req.id@, req.state, req.value@);
                    }
                    let rec = self.objects[i].to_record();
                    PromiseRes { status: 200, promise: Some(rec) }
                } else {
                    let rec = self.objects[i].to_record();
                    proof { lemma_project_legal(now as nat, a, self@, req.id@); }
                    PromiseRes { status: 200, promise: Some(rec) }
                }
            }
        }
    }

    /// `promise.callback`: register `awaiter` to be resumed when `awaited` settles.
    pub fn promise_register_callback(&mut self, req: &PromiseRegisterCallbackReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_register_callback(old(self)@, req@, now as nat).0,
            r@ == spec_promise_register_callback(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 422,
    {
        let ghost a = self@;
        if req.awaited == req.awaiter || !crate::types::same_origin(&req.awaited, &req.awaiter) {
            proof { crate::properties_proof::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        let i = match self.read_object(&req.awaited, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                return PromiseRes { status: 404, promise: None };
            }
            Some(i) => i,
        };
        let ghost a1 = self@;
        let j = match self.read_object(&req.awaiter, now) {
            None => {
                proof { lemma_project_legal(now as nat, a, self@, req.awaited@); }
                return PromiseRes { status: 422, promise: None };
            }
            Some(j) => j,
        };
        proof {
            assert(i != j);
            self.lemma_object_at(i as int);
            self.lemma_object_at(j as int);
            assert(self@.objects[req.awaited@] == a.objects[req.awaited@].project(now as nat));
            assert(self@.objects[req.awaiter@] == a.objects[req.awaiter@].project(now as nat));
            lemma_project_many(now as nat, a, self@, |x: Seq<char>| x == req.awaited@ || x == req.awaiter@);
        }
        if self.objects[j].otype() != OType::Runnable || !self.objects[i].otype().is_awaitable() {
            return PromiseRes { status: 422, promise: None };
        }
        if self.objects[i].state == PromiseState::Pending && self.objects[j].state == PromiseState::Pending {
            let ghost a2 = self@;
            let ghost before = self.objects@;
            self.objects[i].add_callback(&req.awaiter);
            proof {
                let x = req.awaited@;
                let y = req.awaiter@;
                assert(a.objects[x].project(now as nat).state == PromiseState::Pending);
                assert(a.objects[y].project(now as nat).state == PromiseState::Pending);
                assert(a2.objects[x] == a.objects[x]);
                assert(a2.objects[y] == a.objects[y]);
                crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                assert(self@.objects =~= a.objects.insert(x, a.objects[x].add_callback(y)));
                lemma_add_callback_legal(now as nat, a, self@, x, y);
                assert(a2.objects =~= spec_read(spec_read(a, x, now as nat), y, now as nat).objects);
                assert(self@.objects =~= spec_promise_register_callback(a, req@, now as nat).0.objects);
            }
        }
        let rec = self.objects[i].to_record();
        PromiseRes { status: 200, promise: Some(rec) }
    }

    /// `promise.listener`: register `address` to be told when `awaited` settles.
    pub fn promise_register_listener(&mut self, req: &PromiseRegisterListenerReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_register_listener(old(self)@, req@, now as nat).0,
            r@ == spec_promise_register_listener(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404 || r.status == 422,
    {
        let ghost a = self@;
        let i = match self.read_object(&req.awaited, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                return PromiseRes { status: 404, promise: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.awaited@);
        }
        if !self.objects[i].otype().is_awaitable() {
            return PromiseRes { status: 422, promise: None };
        }
        if self.objects[i].state == PromiseState::Pending {
            let ghost before = self.objects@;
            self.objects[i].add_listener(&req.address);
            proof {
                let x = req.awaited@;
                assert(a.objects[x].project(now as nat).state == PromiseState::Pending);
                assert(a.objects[x].project(now as nat) == a.objects[x]);
                crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                assert(self@.objects =~= a.objects.insert(x, a.objects[x].add_listener(req.address@)));
                lemma_add_listener_legal(now as nat, a, self@, x, req.address@);
            }
        }
        let rec = self.objects[i].to_record();
        PromiseRes { status: 200, promise: Some(rec) }
    }
}

impl Schedule {
    pub fn dup(&self) -> (r: Schedule)
        ensures r@ == self@,
    {
        Schedule {
            id: self.id.clone(),
            cron: self.cron.clone(),
            promise_id: self.promise_id.clone(),
            promise_timeout: self.promise_timeout,
            promise_param: self.promise_param.dup(),
            promise_tags: clone_tags(&self.promise_tags),
            next_run_at: self.next_run_at,
            last_run_at: self.last_run_at,
            created_at: self.created_at,
        }
    }
}

impl State {
    /// `schedule.get`.
    pub fn schedule_get(&mut self, req: &ScheduleGetReq, now: u64, cfg: &Config) -> (r: ScheduleRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_schedule_get(old(self)@, req@, now as nat).0,
            r@ == spec_schedule_get(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404,
    {
        proof { crate::properties_proof::lemma_noop(now as nat, self@); }
        match self.find_schedule(&req.id) {
            None => ScheduleRes { status: 404, schedule: None },
            Some(i) => {
                proof { self.lemma_schedule_at(i as int); }
                ScheduleRes { status: 200, schedule: Some(self.schedules[i].dup()) }
            }
        }
    }

    /// `schedule.create`. `req.next_run_at` is `nextCron cron now`, from the
    /// caller's cron engine; it must not precede `now`.
    pub fn schedule_create(&mut self, req: &ScheduleCreateReq, now: u64, cfg: &Config) -> (r: ScheduleRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_schedule_create(old(self)@, req@, now as nat).0,
            r@ == spec_schedule_create(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400,
    {
        let ghost a = self@;
        if crate::tags::exec_timer_targeted(&req.promise_tags) || req.promise_timeout > MAX_TIME || req.next_run_at < now {
            proof { crate::properties_proof::lemma_noop(now as nat, a); }
            return ScheduleRes { status: 400, schedule: None };
        }
        match self.find_schedule(&req.id) {
            Some(i) => {
                proof {
                    crate::properties_proof::lemma_noop(now as nat, a);
                    self.lemma_schedule_at(i as int);
                }
                ScheduleRes { status: 200, schedule: Some(self.schedules[i].dup()) }
            }
            None => {
                let c = Schedule {
                    id: req.id.clone(),
                    cron: req.cron.clone(),
                    promise_id: req.promise_id.clone(),
                    promise_timeout: req.promise_timeout,
                    promise_param: req.promise_param.dup(),
                    promise_tags: clone_tags(&req.promise_tags),
                    next_run_at: req.next_run_at,
                    last_run_at: None,
                    created_at: now,
                };
                let out = c.dup();
                self.push_schedule(c);
                proof { lemma_schedule_create_legal(now as nat, a, self@, req.id@); }
                ScheduleRes { status: 200, schedule: Some(out) }
            }
        }
    }

    /// `schedule.delete`.
    pub fn schedule_delete(&mut self, req: &ScheduleDeleteReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_schedule_delete(old(self)@, req@, now as nat).0,
            r@ == spec_schedule_delete(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404,
    {
        let ghost a = self@;
        match self.find_schedule(&req.id) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                StatusRes { status: 404 }
            }
            Some(i) => {
                proof { self.lemma_schedule_at(i as int); }
                self.remove_schedule(i);
                proof {
                    lemma_schedule_delete_legal(now as nat, a, self@, req.id@);
                    assert(self@ == spec_schedule_delete(a, req@, now as nat).0);
                }
                StatusRes { status: 200 }
            }
        }
    }
}

impl State {
    /// `readTaskObject`: the object, if it has a task; projected at `now`.
    pub fn read_task_object(&mut self, id: &String, now: u64) -> (r: Option<usize>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).schedules == old(self).schedules,
            final(self).outbox == old(self).outbox,
            final(self)@.schedules == old(self)@.schedules,
            final(self)@.outbox == old(self)@.outbox,
            match r {
                None => {
                    &&& *final(self) == *old(self)
                    &&& !old(self)@.has_task(id@)
                },
                Some(i) => {
                    &&& i < final(self).objects@.len()
                    &&& final(self).objects@ == old(self).objects@.update(i as int, final(self).objects@[i as int])
                    &&& old(self).objects@[i as int].id@ == id@
                    &&& final(self).objects@[i as int]@ == old(self).objects@[i as int]@.project(now as nat)
                    &&& final(self).objects@[i as int].id@ == id@
                    &&& old(self)@.objects.contains_key(id@)
                    &&& old(self)@.objects[id@].task is Some
                    &&& final(self).objects@[i as int]@ == old(self)@.objects[id@].project(now as nat)
                    &&& final(self)@.objects == old(self)@.objects.insert(id@, old(self)@.objects[id@].project(now as nat))
                },
            },
    {
        match self.find_object(id) {
            None => None,
            Some(i) => {
                proof { self.lemma_object_at(i as int); }
                if self.objects[i].task.is_none() {
                    return None;
                }
                let ghost before = self.objects@;
                self.objects[i].project(now);
                proof {
                    crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                }
                Some(i)
            }
        }
    }

    /// `task.get`.
    pub fn task_get(&mut self, req: &TaskGetReq, now: u64, cfg: &Config) -> (r: TaskGetRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_get(old(self)@, req@, now as nat).0,
            r@ == spec_task_get(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404,
    {
        let ghost a = self@;
        match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                TaskGetRes { status: 404, task: None }
            }
            Some(i) => {
                proof {
                    lemma_project_legal(now as nat, a, self@, req.id@);
                    assert(self@ == spec_read_task(a, req.id@, now as nat));
                }
                match &self.objects[i].task {
                    None => TaskGetRes { status: 404, task: None },
                    Some(t) => TaskGetRes { status: 200, task: Some(t.to_record(&self.objects[i].id)) },
                }
            }
        }
    }

    /// `task.create`.
    pub fn task_create(&mut self, req: &TaskCreateReq, now: u64, cfg: &Config) -> (r: TaskClaimRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_create(old(self)@, req@, now as nat).0,
            r@ == spec_task_create(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 409 || r.status == 422,
    {
        let ghost a = self@;
        let act = &req.action;
        if crate::tags::exec_otype(&act.tags) != OType::Runnable || crate::tags::exec_timer_targeted(&act.tags)
            || act.timeout_at > MAX_TIME || req.ttl > MAX_TIME {
            proof { crate::properties_proof::lemma_noop(now as nat, a); }
            return TaskClaimRes { status: 400, task: None, promise: None };
        }
        match self.read_object(&act.id, now) {
            None => {
                if act.timeout_at > now {
                    let p = create_promise_acquired(act, &req.pid, req.ttl, now);
                    let rec = p.to_record();
                    let trec = match &p.task { Some(t) => Some(t.to_record(&p.id)), None => None };
                    self.push_object(p);
                    proof { lemma_create_acquired_legal(now as nat, a, self@, act@, req.pid@, req.ttl as nat); }
                    TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
                } else {
                    let p = create_promise(act, now);
                    let rec = p.to_record();
                    let trec = match &p.task { Some(t) => Some(t.to_record(&p.id)), None => None };
                    self.push_object(p);
                    proof { lemma_create_legal(now as nat, a, self@, act@); }
                    TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
                }
            }
            Some(i) => {
                proof {
                    self.lemma_object_at(i as int);
                    lemma_project_legal(now as nat, a, self@, act.id@);
                    assert(self@ == spec_read(a, act.id@, now as nat));
                }
                if self.objects[i].otype() != OType::Runnable {
                    return TaskClaimRes { status: 422, task: None, promise: None };
                }
                let (state, version) = match &self.objects[i].task {
                    None => { return TaskClaimRes { status: 409, task: None, promise: None }; }
                    Some(t) => (t.state, t.version),
                };
                if state == TaskState::Fulfilled {
                    let rec = self.objects[i].to_record();
                    let trec = match &self.objects[i].task { Some(t) => Some(t.to_record(&self.objects[i].id)), None => None };
                    return TaskClaimRes { status: 200, task: trec, promise: Some(rec) };
                }
                if state != TaskState::Pending || version >= MAX_TIME {
                    return TaskClaimRes { status: 409, task: None, promise: None };
                }
                let ghost before = self.objects@;
                self.objects[i].task_acquire(&req.pid, req.ttl, now);
                proof {
                    let x = act.id@;
                    crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                    lemma_projected_task_identity(now as nat, a, x);
                    assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().acquire(req.pid@, req.ttl as nat, now as nat))));
                    lemma_acquire_legal(now as nat, a, self@, x, req.pid@, req.ttl as nat);
                    assert(self@.objects =~= spec_task_create(a, req@, now as nat).0.objects);
                }
                let rec = self.objects[i].to_record();
                let trec = match &self.objects[i].task { Some(t) => Some(t.to_record(&self.objects[i].id)), None => None };
                TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
            }
        }
    }

    /// `task.acquire`.
    pub fn task_acquire(&mut self, req: &TaskAcquireReq, now: u64, cfg: &Config) -> (r: TaskClaimRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_acquire(old(self)@, req@, now as nat).0,
            r@ == spec_task_acquire(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        if req.ttl > MAX_TIME {
            proof { crate::properties_proof::lemma_noop(now as nat, a); }
            return TaskClaimRes { status: 400, task: None, promise: None };
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                return TaskClaimRes { status: 404, task: None, promise: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return TaskClaimRes { status: 404, task: None, promise: None }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Pending || self.objects[i].state != PromiseState::Pending
            || version != req.version || version >= MAX_TIME {
            return TaskClaimRes { status: 409, task: None, promise: None };
        }
        let ghost before = self.objects@;
        self.objects[i].task_acquire(&req.pid, req.ttl, now);
        proof {
            let x = req.id@;
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().acquire(req.pid@, req.ttl as nat, now as nat))));
            lemma_acquire_legal(now as nat, a, self@, x, req.pid@, req.ttl as nat);
            assert(self@.objects =~= spec_task_acquire(a, req@, now as nat).0.objects);
        }
        let rec = self.objects[i].to_record();
        let trec = match &self.objects[i].task { Some(t) => Some(t.to_record(&self.objects[i].id)), None => None };
        TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
    }

    /// `task.fulfill`.
    pub fn task_fulfill(&mut self, req: &TaskFulfillReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_fulfill(old(self)@, req@, now as nat).0,
            r@ == spec_task_fulfill(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        if !req.action.state.settable() {
            proof { crate::properties_proof::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                return PromiseRes { status: 404, promise: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return PromiseRes { status: 404, promise: None }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return PromiseRes { status: 409, promise: None };
        }
        let ghost before = self.objects@;
        self.objects[i].settle(req.action.state, req.action.value.dup(), now);
        proof {
            let x = req.id@;
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].project(now as nat).settle(req.action.state, req.action.value@, now as nat)));
            lemma_settle_legal(now as nat, a, self@, x, req.action.state, req.action.value@);
            assert(self@.objects =~= spec_task_fulfill(a, req@, now as nat).0.objects);
        }
        let rec = self.objects[i].to_record();
        PromiseRes { status: 200, promise: Some(rec) }
    }

    /// `task.release`.
    pub fn task_release(&mut self, req: &TaskReleaseReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_release(old(self)@, req@, now as nat).0,
            r@ == spec_task_release(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return StatusRes { status: 409 };
        }
        let ghost before = self.objects@;
        self.objects[i].task_release(now);
        proof {
            let x = req.id@;
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().release(now as nat))));
            lemma_release_legal(now as nat, a, self@, x);
            assert(self@.objects =~= spec_task_release(a, req@, now as nat).0.objects);
        }
        StatusRes { status: 200 }
    }

    /// `task.halt`.
    pub fn task_halt(&mut self, req: &TaskHaltReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_halt(old(self)@, req@, now as nat).0,
            r@ == spec_task_halt(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let state = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => t.state,
        };
        if state == TaskState::Fulfilled {
            return StatusRes { status: 409 };
        }
        if state == TaskState::Halted {
            return StatusRes { status: 200 };
        }
        let ghost before = self.objects@;
        self.objects[i].task_halt();
        proof {
            let x = req.id@;
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().halt())));
            lemma_halt_legal(now as nat, a, self@, x);
            assert(self@.objects =~= spec_task_halt(a, req@, now as nat).0.objects);
        }
        StatusRes { status: 200 }
    }

    /// `task.continue`.
    pub fn task_continue(&mut self, req: &TaskContinueReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_continue(old(self)@, req@, now as nat).0,
            r@ == spec_task_continue(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let state = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => t.state,
        };
        if state != TaskState::Halted || self.objects[i].state != PromiseState::Pending {
            return StatusRes { status: 409 };
        }
        let ghost before = self.objects@;
        self.objects[i].task_continue(now);
        proof {
            let x = req.id@;
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().continue_(now as nat))));
            lemma_continue_legal(now as nat, a, self@, x);
            assert(self@.objects =~= spec_task_continue(a, req@, now as nat).0.objects);
        }
        StatusRes { status: 200 }
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

impl State {
    /// `task.fence`.
    pub fn task_fence(&mut self, req: &TaskFenceReq, now: u64, cfg: &Config) -> (r: TaskFenceRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_fence(old(self)@, req@, now as nat).0,
            r@ == spec_task_fence(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let target: &String = match &req.action {
            TaskFenceAction::Create(c) => &c.id,
            TaskFenceAction::Settle(c) => &c.id,
        };
        if *target == req.id || !crate::types::same_origin(target, &req.id) {
            proof { crate::properties_proof::lemma_noop(now as nat, a); }
            return TaskFenceRes { status: 400, action: None };
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                return TaskFenceRes { status: 404, action: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return TaskFenceRes { status: 404, action: None }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return TaskFenceRes { status: 409, action: None };
        }
        let ghost a1 = self@;
        let inner = match &req.action {
            TaskFenceAction::Create(c) => TaskFenceInnerRes::Create(self.promise_create(c, now, cfg)),
            TaskFenceAction::Settle(c) => TaskFenceInnerRes::Settle(self.promise_settle(c, now, cfg)),
        };
        proof { lemma_fence_legal(now as nat, a, a1, self@, req.id@, target@); }
        TaskFenceRes { status: 200, action: Some(inner) }
    }

    /// `task.heartbeat`.
    pub fn task_heartbeat(&mut self, req: &TaskHeartbeatReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_heartbeat(old(self)@, req@, now as nat).0,
            r@ == spec_task_heartbeat(old(self)@, req@, now as nat).1,
            r.status == 200,
    {
        let ghost a = self@;
        let ghost pid = req.pid@;
        let ghost refs: Seq<ATaskRef> = req.tasks.deep_view();
        let mut k: usize = 0;
        while k < req.tasks.len()
            invariant
                a == old(self)@,
                k <= refs.len(),
                refs == req.tasks.deep_view(),
                pid == req.pid@,
                now <= MAX_TIME,
                inv(now as nat, a),
                self.wf(),
                self@ == spec_heartbeat_fold(a, pid, refs, k as int, now as nat),
            decreases refs.len() - k,
        {
            let ghost s0 = self@;
            let ghost r = refs[k as int];
            proof {
                lemma_spec_heartbeat_fold_inv(now as nat, a, pid, refs, k as int);
                assert(r == req.tasks@[k as int]@);
            }
            let x = &req.tasks[k].id;
            match self.read_task_object(x, now) {
                None => {
                    proof { assert(self@ == spec_heartbeat_one(s0, pid, r, now as nat)); }
                }
                Some(i) => {
                    proof {
                        self.lemma_object_at(i as int);
                        lemma_project_legal(now as nat, s0, self@, x@);
                        assert(self@ == spec_read_task(s0, x@, now as nat));
                    }
                    let ok = match &self.objects[i].task {
                        Some(t) => t.state == TaskState::Acquired && t.version == req.tasks[k].version
                            && (match &t.pid { Some(p) => *p == req.pid, None => false })
                            && self.objects[i].state == PromiseState::Pending,
                        None => false,
                    };
                    if ok {
                        let ghost s1 = self@;
                        let ghost before = self.objects@;
                        proof {
                            lemma_projected_task_identity(now as nat, s0, x@);
                            lemma_inv_pointwise(now as nat, s1);
                            assert(inv_obj(now as nat, s1, x@));
                        }
                        self.objects[i].task_heartbeat(now);
                        proof {
                            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                            assert(self@.objects =~= s1.objects.insert(x@, s1.objects[x@].with_task(s1.objects[x@].task.unwrap().heartbeat(now as nat))));
                            assert(self@ == spec_heartbeat_one(s0, pid, r, now as nat));
                        }
                    } else {
                        proof { assert(self@ == spec_heartbeat_one(s0, pid, r, now as nat)); }
                    }
                }
            }
            proof { assert(self@ == spec_heartbeat_fold(a, pid, refs, k as int + 1, now as nat)); }
            k += 1;
        }
        proof { lemma_spec_task_heartbeat(now as nat, a, req@); }
        StatusRes { status: 200 }
    }

    /// `task.suspend`.
    pub fn task_suspend(&mut self, req: &TaskSuspendReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_suspend(old(self)@, req@, now as nat).0,
            r@ == spec_task_suspend(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 300 || r.status == 400 || r.status == 404 || r.status == 409 || r.status == 422,
    {
        let ghost a = self@;
        let ghost acts: Seq<APromiseRegisterCallbackReq> = req.actions.deep_view();
        let ghost id = req.id@;
        let n = req.actions.len();
        proof {
            assert(acts == req@.actions);
            assert forall|j: int| 0 <= j < acts.len() implies #[trigger] acts[j].awaited == req.actions@[j].awaited@ by {}
        }
        let crosses = awaits_self_or_crosses(&req.actions, &req.id);
        let twice = awaits_twice(&req.actions);
        if n == 0 || crosses || twice {
            proof {
                crate::properties_proof::lemma_noop(now as nat, a);
                assert(!suspend_doors(acts, id));
            }
            return StatusRes { status: 400 };
        }
        proof { assert(suspend_doors(acts, id)); }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::properties_proof::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, id);
            assert(self@ == spec_read_task(a, id, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return StatusRes { status: 409 };
        }
        // the state the check loop reads from: the task object, projected, which was the identity
        let ghost rb = self@;
        let ghost t0 = rb.objects[id].task.unwrap();
        proof {
            lemma_projected_task_identity(now as nat, a, id);
            assert(suspend_base(now as nat, a, id));
            assert(self.objects@[i as int]@ == a.objects[id]);
            assert(rb.objects =~= a.objects);
            assert(rb == a);
            assert(spec_read_task(a, id, now as nat) == a);
            assert(t0.version == req.version);
            assert forall|x: Seq<char>| !awaited_touched(acts, 0, x) implies #[trigger] unchanged_at(a, self@, x) by {}
            assert forall|j: int| 0 <= j < n implies rb.objects.contains_key(#[trigger] acts[j].awaited) == a.objects.contains_key(acts[j].awaited)
                && (a.objects.contains_key(acts[j].awaited) ==> rb.objects[acts[j].awaited] == a.objects[acts[j].awaited]) by {}
        }
        // checkAwaited
        let mut settled = false;
        let mut k: usize = 0;
        while k < n
            invariant
                a == old(self)@,
                k <= n,
                n == acts.len(),
                acts == req.actions.deep_view(),
                forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == req.actions@[j].awaited@,
                id == req.id@,
                now <= MAX_TIME,
                suspend_base(now as nat, a, id),
                suspend_doors(acts, id),
                rb == a,
                spec_read_task(a, id, now as nat) == a,
                t0 == a.objects[id].task.unwrap(),
                t0.version == req.version,
                self.wf(),
                inv(now as nat, self@),
                self@.schedules == a.schedules,
                self@.outbox == a.outbox,
                i < self.objects@.len(),
                self.objects@[i as int].id@ == id,
                self.objects@[i as int]@ == a.objects[id],
                self@ == spec_awaited_read(rb, acts, k as int, now as nat),
                first_failing(rb, acts, k as int) is None,
                forall|x: Seq<char>| !awaited_touched(acts, k as int, x) ==> #[trigger] unchanged_at(a, self@, x),
                forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int, x) ==>
                    a.objects.contains_key(x)
                    && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x].project(now as nat),
                forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int, x) ==> a.objects[x].otype().awaitable(),
                settled == exists|j: int| 0 <= j < k && a.objects[#[trigger] acts[j].awaited].project(now as nat).state != PromiseState::Pending,
            decreases n - k,
        {
            let ghost s0 = self@;
            let w = &req.actions[k].awaited;
            proof {
                assert(acts[k as int].awaited == w@);
                assert(w@ != id);
            }
            let j = match self.read_object(w, now) {
                None => {
                    proof {
                        let ids = |x: Seq<char>| awaited_touched(acts, k as int, x);
                        assert forall|x: Seq<char>| #[trigger] ids(x) implies
                            a.objects.contains_key(x) && self@.objects.contains_key(x)
                            && self@.objects[x] == a.objects[x].project(now as nat) by {
                            assert(awaited_touched(acts, k as int, x));
                        }
                        assert forall|x: Seq<char>| !ids(x) implies
                            (a.objects.contains_key(x) <==> #[trigger] self@.objects.contains_key(x))
                            && (a.objects.contains_key(x) ==> a.objects[x] == self@.objects[x]) by {
                            assert(!awaited_touched(acts, k as int, x));
                            assert(unchanged_at(a, self@, x));
                        }
                        lemma_project_many(now as nat, a, self@, ids);
                        // the check failed here: nothing at `w`
                        if awaited_touched(acts, k as int, w@) {
                            assert(s0.objects.contains_key(w@));
                            assert(false);
                        }
                        assert(unchanged_at(a, s0, w@));
                        assert(!rb.objects.contains_key(w@));
                        assert(awaited_fails(rb, acts[k as int]));
                        lemma_first_failing_at(rb, acts, k as int, n as int);
                        assert(self@ == spec_task_suspend(a, req@, now as nat).0);
                    }
                    return StatusRes { status: 422 };
                }
                Some(j) => j,
            };
            proof {
                self.lemma_object_at(j as int);
                lemma_project_legal(now as nat, s0, self@, w@);
                assert(j != i);
                // the shape after this read, relative to `a`
                if awaited_touched(acts, k as int, w@) {
                    lemma_project_idem(a.objects[w@], now as nat);
                } else {
                    assert(unchanged_at(a, s0, w@));
                }
                assert(self@.objects[w@] == a.objects[w@].project(now as nat));
                assert(a.objects.contains_key(w@));
                assert(self@ == spec_awaited_read(rb, acts, k as int + 1, now as nat));
                assert forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int + 1, x) implies
                    a.objects.contains_key(x)
                    && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x].project(now as nat) by {
                    if x == w@ {
                    } else {
                        let jj = choose|jj: int| 0 <= jj < k as int + 1 && #[trigger] acts[jj].awaited == x;
                        assert(jj < k as int);
                        assert(awaited_touched(acts, k as int, x));
                    }
                }
                assert forall|x: Seq<char>| !awaited_touched(acts, k as int + 1, x) implies #[trigger] unchanged_at(a, self@, x) by {
                    assert(!awaited_touched(acts, k as int, x));
                    assert(acts[k as int].awaited != x);
                    assert(unchanged_at(a, s0, x));
                }
            }
            if !self.objects[j].otype().is_awaitable() {
                proof {
                    // The lemma's preconditions, stated on the closure it is
                    // handed, so the match does not rest on trigger luck.
                    let ids = |x: Seq<char>| awaited_touched(acts, k as int + 1, x);
                    assert forall|x: Seq<char>| #[trigger] ids(x) implies
                        a.objects.contains_key(x) && self@.objects.contains_key(x)
                        && self@.objects[x] == a.objects[x].project(now as nat) by {
                        assert(awaited_touched(acts, k as int + 1, x));
                    }
                    assert forall|x: Seq<char>| !ids(x) implies
                        (a.objects.contains_key(x) <==> #[trigger] self@.objects.contains_key(x))
                        && (a.objects.contains_key(x) ==> a.objects[x] == self@.objects[x]) by {
                        assert(!awaited_touched(acts, k as int + 1, x));
                        assert(unchanged_at(a, self@, x));
                    }
                    lemma_project_many(now as nat, a, self@, ids);
                    // the check failed here: not awaitable
                    assert(a.objects[w@].otype() == self@.objects[w@].otype());
                    assert(awaited_fails(rb, acts[k as int]));
                    lemma_first_failing_at(rb, acts, k as int, n as int);
                    assert(self@ == spec_task_suspend(a, req@, now as nat).0);
                }
                return StatusRes { status: 422 };
            }
            proof {
                assert(a.objects[w@].otype() == self@.objects[w@].otype());
                assert(!awaited_fails(rb, acts[k as int]));
                assert(first_failing(rb, acts, k as int + 1) is None);
                assert forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int + 1, x) implies a.objects[x].otype().awaitable() by {
                    if x != w@ {
                        let jj = choose|jj: int| 0 <= jj < k as int + 1 && #[trigger] acts[jj].awaited == x;
                        assert(jj < k as int);
                        assert(awaited_touched(acts, k as int, x));
                    }
                }
            }
            if self.objects[j].state != PromiseState::Pending {
                settled = true;
            }
            proof {
                assert(a.objects[acts[k as int].awaited].project(now as nat).state == self@.objects[w@].state);
            }
            k += 1;
        }
        proof {
            assert(settled == any_settled(rb, acts, now as nat));
        }
        if settled {
            let ghost s_prev = self@;
            let ghost before = self.objects@;
            proof { self.lemma_object_at(i as int); }
            self.objects[i].task_clear_resumes();
            proof {
                crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                let ghost b = self@;
                assert(b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().clear_resumes()));
                assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
                    a.objects.contains_key(x) && x != id
                    && b.objects.contains_key(x) && b.objects[x] == a.objects[x].project(now as nat) by {
                    assert(awaited_touched(acts, n as int, x));
                    let jj = choose|jj: int| 0 <= jj < n && #[trigger] acts[jj].awaited == x;
                    assert(s_prev.objects.contains_key(x) && s_prev.objects[x] == a.objects[x].project(now as nat));
                }
                assert forall|x: Seq<char>| !awaited_of(acts, x) && x != id implies #[trigger] unchanged_at(a, b, x) by {
                    assert(!awaited_touched(acts, n as int, x));
                    assert(unchanged_at(a, s_prev, x));
                    assert(b.objects.contains_key(x) == s_prev.objects.contains_key(x));
                }
                lemma_suspend_300_legal(now as nat, a, b, id, acts);
                assert(s_prev.objects[id] == a.objects[id]);
                assert(b.objects =~= s_prev.objects.insert(id, s_prev.objects[id].with_task(t0.clear_resumes())));
                assert(b == spec_task_suspend(a, req@, now as nat).0);
            }
            return StatusRes { status: 300 };
        }
        // registerAwaited: every awaited promise is pending, so its projection was the identity
        let ghost c = self@;
        proof {
            assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
                a.objects.contains_key(x) && a.objects[x].otype().awaitable()
                && a.objects[x].state == PromiseState::Pending && a.objects[x].timeout_at > now
                && x != id && crate::types::same_origin_spec(x, id)
                && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x] by {
                assert(awaited_touched(acts, n as int, x));
                let jj = choose|jj: int| 0 <= jj < n && #[trigger] acts[jj].awaited == x;
                assert(a.objects[acts[jj].awaited].project(now as nat).state == PromiseState::Pending);
            }
            assert forall|j: int| 0 <= j < n implies self@.objects.contains_key(#[trigger] acts[j].awaited)
                && self@.objects[acts[j].awaited] == a.objects[acts[j].awaited] by {
                assert(awaited_touched(acts, n as int, acts[j].awaited));
                assert(awaited_of(acts, acts[j].awaited));
            }
            assert forall|x: Seq<char>| !awaited_of(acts, x) implies #[trigger] unchanged_at(a, self@, x) by {
                assert(!awaited_touched(acts, n as int, x));
            }
        }
        k = 0;
        while k < n
            invariant
                a == old(self)@,
                k <= n,
                n == acts.len(),
                acts == req.actions.deep_view(),
                forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == req.actions@[j].awaited@,
                id == req.id@,
                now <= MAX_TIME,
                suspend_base(now as nat, a, id),
                suspend_doors(acts, id),
                rb == a,
                spec_read_task(a, id, now as nat) == a,
                t0 == a.objects[id].task.unwrap(),
                t0.version == req.version,
                c == spec_awaited_read(rb, acts, n as int, now as nat),
                first_failing(rb, acts, n as int) is None,
                !any_settled(rb, acts, now as nat),
                self.wf(),
                inv(now as nat, self@),
                self@.schedules == a.schedules,
                self@.outbox == a.outbox,
                i < self.objects@.len(),
                self.objects@[i as int].id@ == id,
                self.objects@[i as int]@ == a.objects[id],
                self@ == spec_awaited_register(c, acts, k as int, id),
                forall|x: Seq<char>| !awaited_of(acts, x) ==> #[trigger] unchanged_at(a, self@, x),
                forall|x: Seq<char>| #[trigger] awaited_of(acts, x) ==>
                    a.objects.contains_key(x) && a.objects[x].otype().awaitable()
                    && a.objects[x].state == PromiseState::Pending && a.objects[x].timeout_at > now
                    && x != id && crate::types::same_origin_spec(x, id),
                forall|j: int| 0 <= j < k ==> self@.objects.contains_key(#[trigger] acts[j].awaited)
                    && self@.objects[acts[j].awaited] == a.objects[acts[j].awaited].add_callback(id),
                forall|j: int| k <= j < n ==> self@.objects.contains_key(#[trigger] acts[j].awaited)
                    && self@.objects[acts[j].awaited] == a.objects[acts[j].awaited],
            decreases n - k,
        {
            let ghost s0 = self@;
            let w = &req.actions[k].awaited;
            proof {
                assert(acts[k as int].awaited == w@);
                assert(awaited_of(acts, w@));
                assert(s0.objects.contains_key(w@));
            }
            let j = match self.find_object(w) {
                None => {
                    proof { assert(false); }
                    return StatusRes { status: 422 };
                }
                Some(j) => j,
            };
            proof {
                self.lemma_object_at(j as int);
                assert(j != i);
                assert(s0.objects[w@] == a.objects[w@]);
                assert(unchanged_at(a, s0, id));
                assert(s0.objects[id] == a.objects[id]);
            }
            let ghost before = self.objects@;
            self.objects[j].add_callback(&req.id);
            proof {
                crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), j as int, self.objects@[j as int]);
                assert(self@.objects =~= s0.objects.insert(w@, s0.objects[w@].add_callback(id)));
                assert(self@ == spec_awaited_register(c, acts, k as int + 1, id));
                assert(a.objects[w@].project(now as nat) == a.objects[w@]);
                assert(a.objects[id].project(now as nat) == a.objects[id]);
                lemma_inv_pointwise(now as nat, s0);
                assert(inv_obj(now as nat, s0, id));
                assert(s0.objects[id].otype() == OType::Runnable);
                lemma_add_callback_legal(now as nat, s0, self@, w@, id);
                let ghost b = self@;
                assert forall|jj: int| 0 <= jj < k as int + 1 implies b.objects.contains_key(#[trigger] acts[jj].awaited)
                    && b.objects[acts[jj].awaited] == a.objects[acts[jj].awaited].add_callback(id) by {
                    if jj < k as int {
                        assert(acts[jj].awaited != w@);
                    }
                }
                assert forall|jj: int| k as int + 1 <= jj < n implies b.objects.contains_key(#[trigger] acts[jj].awaited)
                    && b.objects[acts[jj].awaited] == a.objects[acts[jj].awaited] by {
                    assert(acts[jj].awaited != w@);
                }
                assert forall|x: Seq<char>| !awaited_of(acts, x) implies #[trigger] unchanged_at(a, b, x) by {
                    assert(unchanged_at(a, s0, x));
                    assert(x != w@);
                }
            }
            k += 1;
        }
        let ghost s_prev = self@;
        let ghost before = self.objects@;
        proof { self.lemma_object_at(i as int); }
        self.objects[i].task_suspend();
        proof {
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            let ghost b = self@;
            assert(b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().suspend()));
            assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
                b.objects.contains_key(x) && b.objects[x] == a.objects[x].add_callback(id) by {
                assert(awaited_touched(acts, n as int, x));
                let jj = choose|jj: int| 0 <= jj < n && #[trigger] acts[jj].awaited == x;
                assert(s_prev.objects.contains_key(x) && s_prev.objects[x] == a.objects[x].add_callback(id));
            }
            assert forall|x: Seq<char>| !awaited_of(acts, x) && x != id implies #[trigger] unchanged_at(a, b, x) by {
                assert(unchanged_at(a, s_prev, x));
                assert(b.objects.contains_key(x) == s_prev.objects.contains_key(x));
            }
            lemma_suspend_legal(now as nat, a, b, id, acts);
            assert(s_prev.objects[id] == a.objects[id]);
            assert(b.objects =~= s_prev.objects.insert(id, s_prev.objects[id].with_task(t0.suspend())));
            assert(b == spec_task_suspend(a, req@, now as nat).0);
        }
        StatusRes { status: 200 }
    }
}

// ---------------------------------------------------------------------------
// Door checks
// ---------------------------------------------------------------------------

/// Does any action await the task itself, or a promise of another origin?
pub fn awaits_self_or_crosses(actions: &Vec<PromiseRegisterCallbackReq>, id: &String) -> (r: bool)
    ensures
        r == exists|j: int| 0 <= j < actions.deep_view().len()
            && (#[trigger] actions.deep_view()[j].awaited == id@ || !crate::types::same_origin_spec(actions.deep_view()[j].awaited, id@)),
{
    let ghost acts: Seq<APromiseRegisterCallbackReq> = actions.deep_view();
    proof {
        assert forall|j: int| 0 <= j < acts.len() implies #[trigger] acts[j].awaited == actions@[j].awaited@ by {}
    }
    let mut k: usize = 0;
    while k < actions.len()
        invariant
            acts == actions.deep_view(),
            forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == actions@[j].awaited@,
            k <= acts.len(),
            forall|j: int| 0 <= j < k ==>
                #[trigger] acts[j].awaited != id@ && crate::types::same_origin_spec(acts[j].awaited, id@),
        decreases acts.len() - k,
    {
        if actions[k].awaited == *id || !crate::types::same_origin(&actions[k].awaited, id) {
            proof { assert(acts[k as int].awaited == actions@[k as int].awaited@); }
            return true;
        }
        k += 1;
    }
    false
}

/// Does any promise appear twice?
pub fn awaits_twice(actions: &Vec<PromiseRegisterCallbackReq>) -> (r: bool)
    ensures r == !awaited_distinct(actions.deep_view()),
{
    let ghost acts: Seq<APromiseRegisterCallbackReq> = actions.deep_view();
    proof {
        assert forall|j: int| 0 <= j < acts.len() implies #[trigger] acts[j].awaited == actions@[j].awaited@ by {}
    }
    let mut k: usize = 0;
    while k < actions.len()
        invariant
            acts == actions.deep_view(),
            forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == actions@[j].awaited@,
            k <= acts.len(),
            forall|i: int, j: int| 0 <= i < k && 0 <= j < acts.len()
                && #[trigger] acts[i].awaited == #[trigger] acts[j].awaited ==> i == j,
        decreases acts.len() - k,
    {
        let mut m: usize = 0;
        while m < actions.len()
            invariant
                acts == actions.deep_view(),
                forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == actions@[j].awaited@,
                k < acts.len(),
                m <= acts.len(),
                forall|i: int, j: int| 0 <= i < k && 0 <= j < acts.len()
                    && #[trigger] acts[i].awaited == #[trigger] acts[j].awaited ==> i == j,
                forall|j: int| 0 <= j < m && j != k ==> #[trigger] acts[j].awaited != acts[k as int].awaited,
            decreases acts.len() - m,
        {
            if m != k && actions[m].awaited == actions[k].awaited {
                proof {
                    assert(acts[m as int].awaited == acts[k as int].awaited);
                    assert(!awaited_distinct(acts));
                }
                return true;
            }
            m += 1;
        }
        k += 1;
    }
    false
}

} // verus!
