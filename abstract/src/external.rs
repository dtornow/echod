//! All 21 external semantic actions from `02-abstract/external.lean`.
//!
//! Search actions intentionally return 501 because that is their complete
//! Lean semantics. No action records Invoke/Return observations.

use vstd::prelude::*;
use crate::promise_spec::*;
use crate::schedule_spec::*;
use crate::state::*;
use crate::task_spec::*;
use crate::types::*;

verus! {

fn promise_error(status: u16) -> (r: PromiseRes)
    ensures r@ == spec_promise_error(status),
{
    PromiseRes { status, promise: None }
}

fn claim_error(status: u16) -> (r: TaskClaimRes)
    ensures r@ == spec_task_claim_error(status),
{
    let preload = Vec::new();
    assert(preload.deep_view() =~= Seq::<APromiseRecord>::empty());
    let r = TaskClaimRes {
        status, task: None, promise: None, preload,
    };
    assert(r@ == spec_task_claim_error(status));
    r
}

fn claim_ok(o: &Object, t: &TaskObject) -> (r: TaskClaimRes)
    ensures r@ == spec_task_claim_ok(o@, t@),
{
    let preload = Vec::new();
    assert(preload.deep_view() =~= Seq::<APromiseRecord>::empty());
    let r = TaskClaimRes {
        status: 200,
        task: Some(t.to_record(&o.id)),
        promise: Some(o.promise.to_record(&o.id)),
        preload,
    };
    assert(r@ == spec_task_claim_ok(o@, t@));
    r
}

fn fence_error(status: u16) -> (r: TaskFenceRes)
    ensures r@ == spec_task_fence_error(status),
{
    let preload = Vec::new();
    assert(preload.deep_view() =~= Seq::<APromiseRecord>::empty());
    let r = TaskFenceRes { status, action: None, preload };
    assert(r@ == spec_task_fence_error(status));
    r
}

fn fence_create_ok(response: PromiseCreateRes) -> (r: TaskFenceRes)
    ensures r@ == (ATaskFenceRes {
        status: 200,
        action: Some(ATaskFenceInnerRes::Create(response@)),
        preload: Seq::empty(),
    }),
{
    let ghost response_spec = response@;
    let preload = Vec::new();
    assert(preload.deep_view() =~= Seq::<APromiseRecord>::empty());
    let r = TaskFenceRes {
        status: 200,
        action: Some(TaskFenceInnerRes::Create(response)),
        preload,
    };
    assert(r@ == (ATaskFenceRes {
        status: 200,
        action: Some(ATaskFenceInnerRes::Create(response_spec)),
        preload: Seq::empty(),
    }));
    r
}

fn fence_settle_ok(response: PromiseSettleRes) -> (r: TaskFenceRes)
    ensures r@ == (ATaskFenceRes {
        status: 200,
        action: Some(ATaskFenceInnerRes::Settle(response@)),
        preload: Seq::empty(),
    }),
{
    let ghost response_spec = response@;
    let preload = Vec::new();
    assert(preload.deep_view() =~= Seq::<APromiseRecord>::empty());
    let r = TaskFenceRes {
        status: 200,
        action: Some(TaskFenceInnerRes::Settle(response)),
        preload,
    };
    assert(r@ == (ATaskFenceRes {
        status: 200,
        action: Some(ATaskFenceInnerRes::Settle(response_spec)),
        preload: Seq::empty(),
    }));
    r
}

fn suspend_response(status: u16) -> (r: TaskSuspendRes)
    ensures r@ == (ATaskSuspendRes {
        status,
        preload: Seq::empty(),
    }),
{
    let preload = Vec::new();
    assert(preload.deep_view() =~= Seq::<APromiseRecord>::empty());
    let r = TaskSuspendRes { status, preload };
    assert(r@ == (ATaskSuspendRes { status, preload: Seq::empty() }));
    r
}

fn task_search_unsupported() -> (r: TaskSearchRes)
    ensures r@ == (ATaskSearchRes {
        status: 501,
        tasks: Seq::empty(),
        cursor: None,
    }),
{
    let tasks = Vec::new();
    assert(tasks.deep_view() =~= Seq::<ATaskRecord>::empty());
    let r = TaskSearchRes { status: 501, tasks, cursor: None };
    assert(r@ == (ATaskSearchRes {
        status: 501,
        tasks: Seq::empty(),
        cursor: None,
    }));
    r
}

fn claim_task(
    task: &TaskObject, pid: Text, ttl: u64, now: u64,
) -> (r: TaskObject)
    ensures r.deep_view() == spec_task_claimed(task.deep_view(), pid@, ttl, now),
{
    let ghost original = task.deep_view();
    let ghost owner = pid@;
    let mut r = task.dup();
    r.state = TaskState::Acquired;
    r.version = checked_add(r.version, 1);
    r.ttl = Some(ttl);
    r.pid = Some(pid);
    r.lease_timeout_at = Some(checked_add(now, ttl));
    r.retry_timeout_at = None;
    r.resumes = Vec::new();
    assert(r.deep_view().state == TaskState::Acquired);
    assert(r.deep_view().version == spec_task_sat_add(original.version, 1));
    assert(r.deep_view().ttl == Some(ttl));
    assert(r.deep_view().pid == Some(owner));
    assert(r.deep_view().lease_timeout_at == Some(spec_task_sat_add(now, ttl)));
    assert(r.deep_view().retry_timeout_at is None);
    assert(r.deep_view().resumes =~= Seq::<AIdent>::empty());
    assert(r.deep_view() == spec_task_claimed(original, owner, ttl, now));
    r
}

pub fn promise_get_action(
    state: &State, req: &PromiseGetReq, now: u64, materialize: bool,
) -> (result: Transition<PromiseGetRes>)
    ensures
        result.response@ ==
            spec_promise_get_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_promise_get_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_promise_get_action(state@, req@, now, materialize).next_state,
{
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
) -> (result: Transition<PromiseCreateRes>)
    ensures
        result.response@ ==
            spec_promise_create_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_promise_create_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_promise_create_action(state@, req@, now, materialize).next_state,
{
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
) -> (result: Transition<PromiseSettleRes>)
    ensures
        result.response@ ==
            spec_promise_settle_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_promise_settle_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_promise_settle_action(state@, req@, now, materialize).next_state,
{
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
) -> (result: Transition<PromiseRegisterCallbackRes>)
    ensures
        result.response@ ==
            spec_promise_register_callback_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_promise_register_callback_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_promise_register_callback_action(state@, req@, now, materialize).next_state,
{
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
        push_effect(&mut effects, Effect::SetPromise(
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
) -> (result: Transition<PromiseRegisterListenerRes>)
    ensures
        result.response@ ==
            spec_promise_register_listener_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_promise_register_listener_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_promise_register_listener_action(state@, req@, now, materialize).next_state,
{
    let read = read_object(state, &req.awaited, now, materialize);
    match read.object {
        None => Transition { response: promise_error(404), effects: read.effects },
        Some(o) => {
            if !o.promise.otype().awaitable() {
                return Transition { response: promise_error(422), effects: read.effects };
            }
            let mut effects = read.effects;
            if o.promise.state == PromiseState::Pending {
                push_effect(&mut effects, Effect::SetPromise(
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
    state: &State, req: &PromiseSearchReq, now: u64, materialize: bool,
) -> (result: Transition<PromiseSearchRes>)
    ensures
        result.response@ ==
            spec_promise_search_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_promise_search_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_promise_search_action(state@, req@, now, materialize).next_state,
{
    let promises = Vec::new();
    let effects = Vec::new();
    proof {
        assert(promises.deep_view() =~= Seq::<APromiseRecord>::empty());
        assert(effects.deep_view() =~= Seq::<AEffect>::empty());
    }
    Transition {
        response: PromiseSearchRes { status: 501, promises, cursor: None },
        effects,
    }
}

pub fn task_get_action(
    state: &State, req: &TaskGetReq, now: u64, materialize: bool,
) -> (result: Transition<TaskGetRes>)
    ensures
        result.response@ ==
            spec_task_get_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_task_get_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_task_get_action(state@, req@, now, materialize).next_state,
{
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
) -> (result: Transition<TaskCreateRes>)
    ensures
        result.response@ ==
            spec_task_create_action(state@, req@, now, materialize).response,
        result.effects.deep_view() ==
            spec_task_create_action(state@, req@, now, materialize).effects,
        spec_apply_all(
            state@,
            spec_task_create_action(state@, req@, now, materialize).effects,
        ) ==
            spec_task_create_action(state@, req@, now, materialize).next_state,
{
    proof {
        lemma_task_create_next_state(state@, req@, now, materialize);
    }
    let ghost request = req@;
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
                let p = PromiseObject {
                    state: PromiseState::Pending, param: a.param, value: Value::empty(),
                    tags: a.tags, timeout_at: a.timeout_at, created_at: now,
                    settled_at: None, callbacks: Vec::new(), listeners: Vec::new(),
                };
                assert(p@.state == PromiseState::Pending);
                assert(p@.created_at == now);
                p
            } else {
                let p = PromiseObject {
                    state: PromiseState::RejectedTimedout, param: a.param,
                    value: Value::empty(), tags: a.tags, timeout_at: a.timeout_at,
                    created_at: a.timeout_at, settled_at: Some(a.timeout_at),
                    callbacks: Vec::new(), listeners: Vec::new(),
                };
                assert(p@.state == PromiseState::RejectedTimedout);
                assert(p@.created_at == request.action.timeout_at);
                p
            };
            assert(p@.param == request.action.param);
            assert(p@.value == spec_value_empty());
            assert(p@.tags == request.action.tags);
            assert(p@.timeout_at == request.action.timeout_at);
            assert(p@.callbacks =~= Seq::<AIdent>::empty());
            assert(p@.listeners =~= Seq::<AText>::empty());
            assert(p@ == spec_task_created_promise(request.action, now));
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
            assert(t.deep_view() == spec_task_created_task(request, p@, now));
            let object = Object { id: id.dup(), promise: p.dup(), task: Some(t.dup()) };
            assert(object@ == (AObject {
                id: request.action.id,
                promise: p@,
                task: Some(t.deep_view()),
            }));
            let mut effects = read.effects;
            effects.push(Effect::SetPromise(id.dup(), p));
            effects.push(Effect::SetTask(id, t.dup()));
            assert(effects.deep_view() =~= crate::state::spec_read_effects(
                state@, request.action.id, now, materialize,
            ) + seq![AEffect::SetPromise(request.action.id, object@.promise)]
                + seq![AEffect::SetTask(request.action.id, t.deep_view())]);
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
            let t = claim_task(t0, req.pid, req.ttl, now);
            let mut effects = read.effects;
            effects.push(Effect::SetTask(o.id.dup(), t.dup()));
            Transition { response: claim_ok(&o, &t), effects }
        }
    }
}

pub fn task_acquire_action(
    state: &State, req: TaskAcquireReq, now: u64, materialize: bool,
) -> (result: Transition<TaskAcquireRes>)
    ensures
        result.response@ ==
            spec_task_acquire_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_task_acquire_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_task_acquire_action(state@, req@, now, materialize).next_state,
{
    let ghost request = req@;
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
    let t = claim_task(t0, req.pid, req.ttl, now);
    let mut effects = read.effects;
    effects.push(Effect::SetTask(o.id.dup(), t.dup()));
    Transition { response: claim_ok(&o, &t), effects }
}

pub fn task_fence_action(
    state: &State, req: TaskFenceReq, now: u64, materialize: bool,
) -> (result: Transition<TaskFenceRes>)
    ensures
        result.response@ ==
            spec_task_fence_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_task_fence_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_task_fence_action(state@, req@, now, materialize).next_state,
{
    let target = match &req.action {
        TaskFenceAction::Create(x) => &x.id,
        TaskFenceAction::Settle(x) => &x.id,
    };
    if ident_eq(target, &req.id) || !target.same_origin(&req.id) {
        return Transition {
            response: fence_error(400),
            effects: Vec::new(),
        };
    }
    let read = read_task_object(state, &req.id, now, materialize);
    let o = match read.object {
        None => return Transition {
            response: fence_error(404),
            effects: read.effects,
        },
        Some(o) => o,
    };
    let t = match &o.task {
        None => return Transition {
            response: fence_error(404),
            effects: read.effects,
        },
        Some(t) => t,
    };
    if t.state != TaskState::Acquired || o.promise.state != PromiseState::Pending
        || t.version != req.version
    {
        return Transition {
            response: fence_error(409),
            effects: read.effects,
        };
    }
    match req.action {
        TaskFenceAction::Create(x) => {
            let inner = promise_create_action(state, x, now, materialize);
            Transition {
                response: fence_create_ok(inner.response),
                effects: append_effects(read.effects, inner.effects),
            }
        }
        TaskFenceAction::Settle(x) => {
            let inner = promise_settle_action(state, x, now, materialize);
            Transition {
                response: fence_settle_ok(inner.response),
                effects: append_effects(read.effects, inner.effects),
            }
        }
    }
}

fn heartbeat_one(
    state: &State, pid: &Text, r: &TaskRef, now: u64, materialize: bool,
) -> (effects: Vec<Effect>)
    ensures effects.deep_view()
        == spec_task_heartbeat_one(state@, pid@, r@, now, materialize),
{
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
) -> (result: Transition<TaskHeartbeatRes>)
    ensures
        result.response@ ==
            spec_task_heartbeat_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_task_heartbeat_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_task_heartbeat_action(state@, req@, now, materialize).next_state,
{
    let ghost tasks = req.tasks.deep_view();
    let mut effects = Vec::new();
    let mut i: usize = 0;
    while i < req.tasks.len()
        invariant
            i <= req.tasks@.len(),
            req.tasks.deep_view() == tasks,
            effects.deep_view() == spec_task_heartbeat_all(
                state@, req@.pid, tasks.take(i as int), now, materialize,
            ),
        decreases req.tasks@.len() - i,
    {
        effects = append_effects(
            effects, heartbeat_one(state, &req.pid, &req.tasks[i], now, materialize),
        );
        let ghost prefix = tasks.take(i as int);
        let ghost next = tasks[i as int];
        assert(prefix.push(next).drop_last() =~= prefix);
        assert(prefix.push(next).last() == next);
        assert(tasks.take(i as int + 1) =~= prefix.push(next));
        i += 1;
    }
    assert(tasks.take(tasks.len() as int) =~= tasks);
    Transition { response: StatusRes { status: 200 }, effects }
}

fn invalid_suspend_actions(
    actions: &Vec<PromiseRegisterCallbackReq>, id: &Ident,
) -> (invalid: bool)
    ensures invalid == spec_task_invalid_suspend_actions(actions.deep_view(), id@),
{
    if actions.len() == 0 { return true; }
    let mut i: usize = 0;
    while i < actions.len()
        invariant
            i <= actions@.len(),
            forall|k: int| 0 <= k < i ==>
                actions.deep_view()[k].awaited != id@
                && actions.deep_view()[k].awaited.origin == id@.origin,
            forall|j: int, k: int| 0 <= j < k < i ==>
                actions.deep_view()[j].awaited
                    != actions.deep_view()[k].awaited,
        decreases actions@.len() - i,
    {
        if ident_eq(&actions[i].awaited, id) || !actions[i].awaited.same_origin(id) {
            assert(actions.deep_view()[i as int].awaited == id@
                || actions.deep_view()[i as int].awaited.origin != id@.origin);
            assert(!(forall|k: int| 0 <= k < actions.deep_view().len() ==>
                actions.deep_view()[k].awaited != id@
                    && actions.deep_view()[k].awaited.origin == id@.origin)) by {
                assert(0 <= (i as int) < actions.deep_view().len());
                assert(actions.deep_view()[i as int].awaited == id@
                    || actions.deep_view()[i as int].awaited.origin != id@.origin);
            }
            return true;
        }
        let mut j: usize = 0;
        while j < i
            invariant
                j <= i,
                i < actions@.len(),
                forall|k: int| 0 <= k < j ==>
                    actions.deep_view()[k].awaited
                        != actions.deep_view()[i as int].awaited,
            decreases i - j,
        {
            if ident_eq(&actions[j].awaited, &actions[i].awaited) {
                assert(actions.deep_view()[j as int].awaited
                    == actions.deep_view()[i as int].awaited);
                assert(!(forall|a: int, b: int|
                    0 <= a < b < actions.deep_view().len() ==>
                    actions.deep_view()[a].awaited
                        != actions.deep_view()[b].awaited)) by {
                    assert(0 <= (j as int) < (i as int)
                        < actions.deep_view().len());
                }
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}

fn suspend_register_one(
    state: &State,
    action: &PromiseRegisterCallbackReq,
    task_id: &Ident,
    now: u64,
    materialize: bool,
) -> (effects: Vec<Effect>)
    ensures effects.deep_view() == spec_task_suspend_register_one(
        state@, action@, task_id@, now, materialize,
    ),
{
    let rr = read_object(state, &action.awaited, now, materialize);
    let mut effects = rr.effects;
    match rr.object {
        Some(object) => push_effect(
            &mut effects,
            Effect::SetPromise(
                object.id, object.promise.add_callback(task_id),
            ),
        ),
        None => {}
    }
    effects
}

pub fn task_suspend_action(
    state: &State, req: &TaskSuspendReq, now: u64, materialize: bool,
) -> (result: Transition<TaskSuspendRes>)
    ensures
        result.response@ ==
            spec_task_suspend_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_task_suspend_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_task_suspend_action(state@, req@, now, materialize).next_state,
{
    let ghost request = req@;
    if invalid_suspend_actions(&req.actions, &req.id) {
        return Transition {
            response: suspend_response(400),
            effects: Vec::new(),
        };
    }
    assert(!spec_task_invalid_suspend_actions(request.actions, request.id));
    let read = read_task_object(state, &req.id, now, materialize);
    let ghost task_read_object = read.object.deep_view();
    let ghost task_read_effects = read.effects.deep_view();
    let o = match read.object {
        None => return Transition {
            response: suspend_response(404),
            effects: read.effects,
        },
        Some(o) => o,
    };
    assert(task_read_object == Some(o@));
    assert(spec_task_read(
        state@, request.id, now, materialize,
    ).object == Some(o@));
    assert(spec_task_read(
        state@, request.id, now, materialize,
    ).effects == task_read_effects);
    let t0 = match &o.task {
        None => return Transition {
            response: suspend_response(404),
            effects: read.effects,
        },
        Some(t) => t,
    };
    assert(o@.task == Some(t0.deep_view()));
    if t0.state != TaskState::Acquired || o.promise.state != PromiseState::Pending
        || t0.version != req.version
    {
        return Transition {
            response: suspend_response(409),
            effects: read.effects,
        };
    }
    assert(t0.deep_view().state == TaskState::Acquired);
    assert(o@.promise.state == PromiseState::Pending);
    assert(t0.deep_view().version == request.version);

    let mut effects = read.effects;
    let ghost read_effects = effects.deep_view();
    assert(read_effects == task_read_effects);
    let ghost actions = req.actions.deep_view();
    assert(request.actions == actions);
    let mut settled = false;
    let mut i: usize = 0;
    while i < req.actions.len()
        invariant
            i <= req.actions@.len(),
            request == req@,
            read_effects == task_read_effects,
            !spec_task_invalid_suspend_actions(request.actions, request.id),
            spec_task_read(
                state@, request.id, now, materialize,
            ).object == Some(o@),
            spec_task_read(
                state@, request.id, now, materialize,
            ).effects == task_read_effects,
            o@.task == Some(t0.deep_view()),
            t0.deep_view().state == TaskState::Acquired,
            o@.promise.state == PromiseState::Pending,
            t0.deep_view().version == request.version,
            req.actions.deep_view() == actions,
            effects.deep_view() == read_effects
                + spec_task_suspend_check(
                    state@, actions.take(i as int), now, materialize,
                ).effects,
            spec_task_suspend_check(
                state@, actions.take(i as int), now, materialize,
            ).valid,
            settled == spec_task_suspend_check(
                state@, actions.take(i as int), now, materialize,
            ).settled,
        decreases req.actions@.len() - i,
    {
        let ghost prior_effects = effects.deep_view();
        let rr = read_object(state, &req.actions[i].awaited, now, materialize);
        let ghost rr_effects = rr.effects.deep_view();
        effects = append_effects(effects, rr.effects);
        assert(effects.deep_view() == prior_effects + rr_effects);
        let ghost prefix = actions.take(i as int);
        let ghost action = actions[i as int];
        assert(prefix.push(action).drop_last() =~= prefix);
        assert(prefix.push(action).last() == action);
        assert(actions.take(i as int + 1) =~= prefix.push(action));
        let awaited = match rr.object {
            None => {
                assert(spec_task_suspend_check(
                    state@, prefix.push(action), now, materialize,
                ) == (ASuspendCheck {
                    valid: false,
                    settled,
                    effects: spec_task_suspend_check(
                        state@, prefix, now, materialize,
                    ).effects + rr_effects,
                }));
                let ghost bad = prefix.push(action);
                let ghost suffix = actions.skip(i as int + 1);
                assert(bad + suffix =~= actions);
                assert(bad + suffix == actions);
                assert(request.actions == actions);
                proof {
                    lemma_task_suspend_check_invalid_extension(
                        state@, bad, suffix, now, materialize,
                    );
                }
                assert(spec_task_suspend_check(
                    state@, request.actions, now, materialize,
                ) == spec_task_suspend_check(
                    state@, bad, now, materialize,
                ));
                assert(!spec_task_suspend_check(
                    state@, request.actions, now, materialize,
                ).valid);
                assert(prior_effects == task_read_effects
                    + spec_task_suspend_check(
                        state@, prefix, now, materialize,
                    ).effects);
                assert(effects.deep_view() == task_read_effects
                    + spec_task_suspend_check(
                        state@, request.actions, now, materialize,
                    ).effects);
                assert(spec_task_suspend_action(
                    state@, request, now, materialize,
                ) == spec_task_finish(
                    state@,
                    ATaskSuspendRes {
                        status: 422,
                        preload: Seq::empty(),
                    },
                    task_read_effects + spec_task_suspend_check(
                        state@, request.actions, now, materialize,
                    ).effects,
                ));
                assert(spec_task_suspend_action(
                    state@, request, now, materialize,
                ).effects == effects.deep_view());
                return Transition {
                    response: suspend_response(422), effects,
                };
            }
            Some(x) => x,
        };
        if !awaited.promise.otype().awaitable() {
            assert(spec_task_suspend_check(
                state@, prefix.push(action), now, materialize,
            ) == (ASuspendCheck {
                valid: false,
                settled,
                effects: spec_task_suspend_check(
                    state@, prefix, now, materialize,
                ).effects + rr_effects,
            }));
            let ghost bad = prefix.push(action);
            let ghost suffix = actions.skip(i as int + 1);
            assert(bad + suffix =~= actions);
            assert(bad + suffix == actions);
            assert(request.actions == actions);
            proof {
                lemma_task_suspend_check_invalid_extension(
                    state@, bad, suffix, now, materialize,
                );
            }
            assert(spec_task_suspend_check(
                state@, request.actions, now, materialize,
            ) == spec_task_suspend_check(
                state@, bad, now, materialize,
            ));
            assert(!spec_task_suspend_check(
                state@, request.actions, now, materialize,
            ).valid);
            assert(prior_effects == task_read_effects
                + spec_task_suspend_check(
                    state@, prefix, now, materialize,
                ).effects);
            assert(effects.deep_view() == task_read_effects
                + spec_task_suspend_check(
                    state@, request.actions, now, materialize,
                ).effects);
            assert(spec_task_suspend_action(
                state@, request, now, materialize,
            ) == spec_task_finish(
                state@,
                ATaskSuspendRes {
                    status: 422,
                    preload: Seq::empty(),
                },
                task_read_effects + spec_task_suspend_check(
                    state@, request.actions, now, materialize,
                ).effects,
            ));
            assert(spec_task_suspend_action(
                state@, request, now, materialize,
            ).effects == effects.deep_view());
            return Transition {
                response: suspend_response(422), effects,
            };
        }
        if awaited.promise.state != PromiseState::Pending { settled = true; }
        assert(spec_task_suspend_check(
            state@, prefix.push(action), now, materialize,
        ).valid);
        assert(spec_task_suspend_check(
            state@, prefix.push(action), now, materialize,
        ).settled == settled);
        assert(read_effects + spec_task_suspend_check(
            state@, prefix.push(action), now, materialize,
        ).effects == effects.deep_view());
        i += 1;
    }
    assert(actions.take(actions.len() as int) =~= actions);
    assert(spec_task_suspend_check(
        state@, request.actions, now, materialize,
    ).valid);
    assert(effects.deep_view() == task_read_effects
        + spec_task_suspend_check(
            state@, request.actions, now, materialize,
        ).effects);

    if settled {
        let mut t = t0.dup();
        t.resumes = Vec::new();
        let ghost next = t.deep_view();
        assert(next.state == t0.deep_view().state);
        assert(next.version == t0.deep_view().version);
        assert(next.ttl == t0.deep_view().ttl);
        assert(next.pid == t0.deep_view().pid);
        assert(next.lease_timeout_at == t0.deep_view().lease_timeout_at);
        assert(next.retry_timeout_at == t0.deep_view().retry_timeout_at);
        assert(next.resumes =~= Seq::<AIdent>::empty());
        assert(next == (ATaskObject {
            resumes: Seq::empty(),
            ..t0.deep_view()
        }));
        effects.push(Effect::SetTask(o.id, t));
        assert(spec_task_suspend_action(
            state@, request, now, materialize,
        ).effects == effects.deep_view());
        return Transition {
            response: suspend_response(300), effects,
        };
    }

    let ghost checked_effects = effects.deep_view();
    i = 0;
    while i < req.actions.len()
        invariant
            i <= req.actions@.len(),
            request == req@,
            req.actions.deep_view() == actions,
            effects.deep_view() == checked_effects
                + spec_task_suspend_register(
                    state@, actions.take(i as int), req@.id, now, materialize,
                ),
        decreases req.actions@.len() - i,
    {
        effects = append_effects(
            effects,
            suspend_register_one(
                state, &req.actions[i], &req.id, now, materialize,
            ),
        );
        let ghost prefix = actions.take(i as int);
        let ghost action = actions[i as int];
        assert(prefix.push(action).drop_last() =~= prefix);
        assert(prefix.push(action).last() == action);
        assert(actions.take(i as int + 1) =~= prefix.push(action));
        assert(effects.deep_view() == checked_effects
            + spec_task_suspend_register(
                state@, prefix.push(action), req@.id, now, materialize,
            ));
        i += 1;
    }
    assert(actions.take(actions.len() as int) =~= actions);
    assert(effects.deep_view() == checked_effects
        + spec_task_suspend_register(
            state@, request.actions, request.id, now, materialize,
        ));
    let mut t = t0.dup();
    t.state = TaskState::Suspended;
    t.pid = None;
    t.ttl = None;
    t.lease_timeout_at = None;
    t.retry_timeout_at = None;
    t.resumes = Vec::new();
    let ghost next = t.deep_view();
    assert(next.state == TaskState::Suspended);
    assert(next.version == t0.deep_view().version);
    assert(next.pid is None);
    assert(next.ttl is None);
    assert(next.lease_timeout_at is None);
    assert(next.retry_timeout_at is None);
    assert(next.resumes =~= Seq::<AIdent>::empty());
    assert(next == (ATaskObject {
        state: TaskState::Suspended,
        pid: None,
        ttl: None,
        lease_timeout_at: None,
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t0.deep_view()
    }));
    effects.push(Effect::SetTask(o.id, t));
    assert(spec_task_suspend_action(
        state@, request, now, materialize,
    ).effects == effects.deep_view());
    Transition {
        response: suspend_response(200), effects,
    }
}

pub fn task_fulfill_action(
    state: &State, req: TaskFulfillReq, now: u64, materialize: bool,
) -> (result: Transition<TaskFulfillRes>)
    ensures
        result.response@ ==
            spec_task_fulfill_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_task_fulfill_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_task_fulfill_action(state@, req@, now, materialize).next_state,
{
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
) -> (result: Transition<StatusRes>)
    requires release,
    ensures
        result.response@ == spec_task_release_action(
            state@, ATaskReleaseReq { id: id@, version }, now, materialize,
        ).response,
        result.effects.deep_view() =~= spec_task_release_action(
            state@, ATaskReleaseReq { id: id@, version }, now, materialize,
        ).effects,
{
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
) -> (result: Transition<TaskReleaseRes>)
    ensures
        result.response@ ==
            spec_task_release_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_task_release_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_task_release_action(state@, req@, now, materialize).next_state,
{
    task_version_action(state, &req.id, req.version, now, materialize, true)
}

pub fn task_halt_action(
    state: &State, req: &TaskHaltReq, now: u64, materialize: bool,
) -> (result: Transition<TaskHaltRes>)
    ensures
        result.response@ ==
            spec_task_halt_action(state@, req@, now, materialize).response,
        result.effects.deep_view() ==
            spec_task_halt_action(state@, req@, now, materialize).effects,
        spec_apply_all(
            state@,
            spec_task_halt_action(state@, req@, now, materialize).effects,
        ) ==
            spec_task_halt_action(state@, req@, now, materialize).next_state,
{
    proof {
        lemma_task_halt_next_state(state@, req@, now, materialize);
    }
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
) -> (result: Transition<TaskContinueRes>)
    ensures
        result.response@ ==
            spec_task_continue_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_task_continue_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_task_continue_action(state@, req@, now, materialize).next_state,
{
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
    state: &State, req: &TaskSearchReq, now: u64, materialize: bool,
) -> (result: Transition<TaskSearchRes>)
    ensures
        result.response@ ==
            spec_task_search_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_task_search_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_task_search_action(state@, req@, now, materialize).next_state,
{
    Transition {
        response: task_search_unsupported(),
        effects: Vec::new(),
    }
}

pub fn schedule_get_action(
    state: &State, req: &ScheduleGetReq, now: u64, materialize: bool,
) -> (result: Transition<ScheduleGetRes>)
    ensures
        result.response@ ==
            spec_schedule_get_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_schedule_get_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_schedule_get_action(state@, req@, now, materialize).next_state,
{
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
    state: &State, req: ScheduleCreateReq, now: u64, materialize: bool,
) -> (result: Transition<ScheduleCreateRes>)
    ensures
        result.response@ == spec_schedule_create_action(
            state@, req@, req@.next_run_at, now, materialize,
        ).response,
        result.effects.deep_view() == spec_schedule_create_action(
            state@, req@, req@.next_run_at, now, materialize,
        ).effects,
        spec_apply_all(
            state@,
            spec_schedule_create_action(
                state@, req@, req@.next_run_at, now, materialize,
            ).effects,
        ) ==
            spec_schedule_create_action(
                state@, req@, req@.next_run_at, now, materialize,
            ).next_state,
{
    proof {
        lemma_schedule_create_next_state(
            state@, req@, req@.next_run_at, now, materialize,
        );
    }
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
    state: &State, req: &ScheduleDeleteReq, now: u64, materialize: bool,
) -> (result: Transition<ScheduleDeleteRes>)
    ensures
        result.response@ ==
            spec_schedule_delete_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_schedule_delete_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_schedule_delete_action(state@, req@, now, materialize).next_state,
{
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
    state: &State, req: &ScheduleSearchReq, now: u64, materialize: bool,
) -> (result: Transition<ScheduleSearchRes>)
    ensures
        result.response@ ==
            spec_schedule_search_action(state@, req@, now, materialize).response,
        result.effects.deep_view() =~=
            spec_schedule_search_action(state@, req@, now, materialize).effects,
        spec_apply_all(state@, result.effects.deep_view()) ==
            spec_schedule_search_action(state@, req@, now, materialize).next_state,
{
    let schedules = Vec::new();
    let effects = Vec::new();
    proof {
        assert(schedules.deep_view() =~= Seq::<ASchedule>::empty());
        assert(effects.deep_view() =~= Seq::<AEffect>::empty());
    }
    Transition {
        response: ScheduleSearchRes { status: 501, schedules, cursor: None },
        effects,
    }
}

} // verus!
