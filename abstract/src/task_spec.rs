//! Pure ghost semantics for every Abstract Task external action.
//!
//! No definition in this file calls an executable handler or another model
//! level.  Reads always use the immutable transition pre-state, while effects
//! are concatenated in Lean writer order and committed only at the end.

use vstd::prelude::*;
use crate::promise_spec::*;
use crate::state::*;
use crate::types::*;

verus! {

#[cfg(verus_keep_ghost)]
pub struct ATaskActionResult<R> {
    pub response: R,
    pub effects: Seq<AEffect>,
    pub next_state: AState,
}

#[cfg(verus_keep_ghost)]
pub struct ATaskReadResult {
    pub object: Option<AObject>,
    pub effects: Seq<AEffect>,
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_finish<R>(
    state: AState,
    response: R,
    effects: Seq<AEffect>,
) -> ATaskActionResult<R> {
    ATaskActionResult {
        response,
        effects,
        next_state: spec_apply_all(state, effects),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_read(
    state: AState,
    id: AIdent,
    now: u64,
    materialize: bool,
) -> ATaskReadResult {
    ATaskReadResult {
        object: spec_read_task_object(state, id, now),
        effects: spec_read_task_effects(state, id, now, materialize),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_record(t: ATaskObject, id: AIdent) -> ATaskRecord {
    ATaskRecord {
        id,
        state: t.state,
        version: t.version,
        resumes: t.resumes.len() as u64,
        ttl: t.ttl,
        pid: t.pid,
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_claim_error(status: u16) -> ATaskClaimRes {
    ATaskClaimRes {
        status,
        task: None,
        promise: None,
        preload: Seq::empty(),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_claim_ok(
    object: AObject,
    task: ATaskObject,
) -> ATaskClaimRes {
    ATaskClaimRes {
        status: 200,
        task: Some(spec_task_record(task, object.id)),
        promise: Some(spec_promise_record(object.promise, object.id)),
        preload: Seq::empty(),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_fence_error(status: u16) -> ATaskFenceRes {
    ATaskFenceRes {
        status,
        action: None,
        preload: Seq::empty(),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_sat_add(a: u64, b: u64) -> u64 {
    if b <= u64::MAX - a { (a + b) as u64 } else { u64::MAX }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_get_action(
    state: AState,
    req: ATaskGetReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<ATaskGetRes> {
    let read = spec_task_read(state, req.id, now, materialize);
    match read.object {
        Some(object) => match object.task {
            Some(task) => spec_task_finish(
                state,
                ATaskGetRes {
                    status: 200,
                    task: Some(spec_task_record(task, object.id)),
                },
                read.effects,
            ),
            None => spec_task_finish(
                state,
                ATaskGetRes { status: 404, task: None },
                read.effects,
            ),
        },
        None => spec_task_finish(
            state,
            ATaskGetRes { status: 404, task: None },
            read.effects,
        ),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_created_promise(
    req: APromiseCreateReq,
    now: u64,
) -> APromiseObject {
    if req.timeout_at > now {
        APromiseObject {
            state: PromiseState::Pending,
            param: req.param,
            value: spec_value_empty(),
            tags: req.tags,
            timeout_at: req.timeout_at,
            created_at: now,
            settled_at: None,
            callbacks: Seq::empty(),
            listeners: Seq::empty(),
        }
    } else {
        APromiseObject {
            state: PromiseState::RejectedTimedout,
            param: req.param,
            value: spec_value_empty(),
            tags: req.tags,
            timeout_at: req.timeout_at,
            created_at: req.timeout_at,
            settled_at: Some(req.timeout_at),
            callbacks: Seq::empty(),
            listeners: Seq::empty(),
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_created_task(
    req: ATaskCreateReq,
    promise: APromiseObject,
    now: u64,
) -> ATaskObject {
    if promise.state == PromiseState::Pending {
        ATaskObject {
            state: TaskState::Acquired,
            version: 1,
            ttl: Some(req.ttl),
            pid: Some(req.pid),
            lease_timeout_at: Some(spec_task_sat_add(now, req.ttl)),
            retry_timeout_at: None,
            resumes: Seq::empty(),
        }
    } else {
        ATaskObject {
            state: TaskState::Fulfilled,
            version: 0,
            ttl: None,
            pid: None,
            lease_timeout_at: None,
            retry_timeout_at: None,
            resumes: Seq::empty(),
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_claimed(
    task: ATaskObject,
    pid: AText,
    ttl: u64,
    now: u64,
) -> ATaskObject {
    ATaskObject {
        state: TaskState::Acquired,
        version: spec_task_sat_add(task.version, 1),
        ttl: Some(ttl),
        pid: Some(pid),
        lease_timeout_at: Some(spec_task_sat_add(now, ttl)),
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..task
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_create_action(
    state: AState,
    req: ATaskCreateReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<ATaskClaimRes> {
    if spec_tags_otype(req.action.tags) != OType::Runnable
        || spec_tags_timer_targeted(req.action.tags)
    {
        spec_task_finish(state, spec_task_claim_error(400), Seq::empty())
    } else {
        let read = crate::promise_spec::spec_read_object(
            state, req.action.id, now, materialize,
        );
        match read.object {
            None => {
                let promise = spec_task_created_promise(req.action, now);
                let task = spec_task_created_task(req, promise, now);
                let object = AObject {
                    id: req.action.id,
                    promise,
                    task: Some(task),
                };
                let effects = read.effects
                    + seq![AEffect::SetPromise(object.id, promise)]
                    + seq![AEffect::SetTask(object.id, task)];
                spec_task_finish(state, spec_task_claim_ok(object, task), effects)
            }
            Some(object) => {
                if spec_tags_otype(object.promise.tags) != OType::Runnable {
                    spec_task_finish(state, spec_task_claim_error(422), read.effects)
                } else {
                    match object.task {
                        None => spec_task_finish(
                            state, spec_task_claim_error(409), read.effects,
                        ),
                        Some(task) => {
                            if task.state == TaskState::Fulfilled {
                                spec_task_finish(
                                    state, spec_task_claim_ok(object, task), read.effects,
                                )
                            } else if task.state != TaskState::Pending {
                                spec_task_finish(
                                    state, spec_task_claim_error(409), read.effects,
                                )
                            } else {
                                let claimed = spec_task_claimed(
                                    task, req.pid, req.ttl, now,
                                );
                                spec_task_finish(
                                    state,
                                    spec_task_claim_ok(object, claimed),
                                    read.effects.push(AEffect::SetTask(
                                        object.id, claimed,
                                    )),
                                )
                            }
                        }
                    }
                }
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_acquire_action(
    state: AState,
    req: ATaskAcquireReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<ATaskClaimRes> {
    let read = spec_task_read(state, req.id, now, materialize);
    match read.object {
        None => spec_task_finish(state, spec_task_claim_error(404), read.effects),
        Some(object) => match object.task {
            None => spec_task_finish(state, spec_task_claim_error(404), read.effects),
            Some(task) => {
                if task.state != TaskState::Pending
                    || object.promise.state != PromiseState::Pending
                    || task.version != req.version
                {
                    spec_task_finish(state, spec_task_claim_error(409), read.effects)
                } else {
                    let claimed = spec_task_claimed(task, req.pid, req.ttl, now);
                    spec_task_finish(
                        state,
                        spec_task_claim_ok(object, claimed),
                        read.effects.push(AEffect::SetTask(object.id, claimed)),
                    )
                }
            }
        },
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_fence_target(action: ATaskFenceAction) -> AIdent {
    match action {
        ATaskFenceAction::Create(req) => req.id,
        ATaskFenceAction::Settle(req) => req.id,
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_fence_action(
    state: AState,
    req: ATaskFenceReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<ATaskFenceRes> {
    let target = spec_task_fence_target(req.action);
    if target == req.id || target.origin != req.id.origin {
        spec_task_finish(state, spec_task_fence_error(400), Seq::empty())
    } else {
        let read = spec_task_read(state, req.id, now, materialize);
        match read.object {
            None => spec_task_finish(
                state, spec_task_fence_error(404), read.effects,
            ),
            Some(object) => match object.task {
                None => spec_task_finish(
                    state, spec_task_fence_error(404), read.effects,
                ),
                Some(task) => {
                    if task.state != TaskState::Acquired
                        || object.promise.state != PromiseState::Pending
                        || task.version != req.version
                    {
                        spec_task_finish(
                            state, spec_task_fence_error(409), read.effects,
                        )
                    } else {
                        match req.action {
                            ATaskFenceAction::Create(action) => {
                                let inner = spec_promise_create_action(
                                    state, action, now, materialize,
                                );
                                spec_task_finish(
                                    state,
                                    ATaskFenceRes {
                                        status: 200,
                                        action: Some(ATaskFenceInnerRes::Create(
                                            inner.response,
                                        )),
                                        preload: Seq::empty(),
                                    },
                                    read.effects + inner.effects,
                                )
                            }
                            ATaskFenceAction::Settle(action) => {
                                let inner = spec_promise_settle_action(
                                    state, action, now, materialize,
                                );
                                spec_task_finish(
                                    state,
                                    ATaskFenceRes {
                                        status: 200,
                                        action: Some(ATaskFenceInnerRes::Settle(
                                            inner.response,
                                        )),
                                        preload: Seq::empty(),
                                    },
                                    read.effects + inner.effects,
                                )
                            }
                        }
                    }
                }
            },
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_heartbeat_one(
    state: AState,
    pid: AText,
    task_ref: ATaskRef,
    now: u64,
    materialize: bool,
) -> Seq<AEffect> {
    let read = spec_task_read(state, task_ref.id, now, materialize);
    match read.object {
        Some(object) => match object.task {
            Some(task) if task.state == TaskState::Acquired
                && task.version == task_ref.version
                && task.pid == Some(pid)
                && object.promise.state == PromiseState::Pending => {
                let ttl = match task.ttl { Some(value) => value, None => 0 };
                read.effects.push(AEffect::SetTask(
                    object.id,
                    ATaskObject {
                        lease_timeout_at: Some(spec_task_sat_add(now, ttl)),
                        ..task
                    },
                ))
            }
            _ => read.effects,
        },
        None => read.effects,
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_heartbeat_all(
    state: AState,
    pid: AText,
    tasks: Seq<ATaskRef>,
    now: u64,
    materialize: bool,
) -> Seq<AEffect>
    decreases tasks.len(),
{
    if tasks.len() == 0 {
        Seq::empty()
    } else {
        spec_task_heartbeat_all(
            state, pid, tasks.drop_last(), now, materialize,
        ) + spec_task_heartbeat_one(
            state, pid, tasks.last(), now, materialize,
        )
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_heartbeat_action(
    state: AState,
    req: ATaskHeartbeatReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<AStatusRes> {
    spec_task_finish(
        state,
        AStatusRes { status: 200 },
        spec_task_heartbeat_all(state, req.pid, req.tasks, now, materialize),
    )
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_invalid_suspend_actions(
    actions: Seq<APromiseRegisterCallbackReq>,
    id: AIdent,
) -> bool {
    actions.len() == 0
        || !(forall|i: int| 0 <= i < actions.len() ==>
            actions[i].awaited != id
                && actions[i].awaited.origin == id.origin)
        || !(forall|j: int, i: int| 0 <= j < i < actions.len() ==>
            actions[j].awaited != actions[i].awaited)
}

#[cfg(verus_keep_ghost)]
pub struct ASuspendCheck {
    pub valid: bool,
    pub settled: bool,
    pub effects: Seq<AEffect>,
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_suspend_check(
    state: AState,
    actions: Seq<APromiseRegisterCallbackReq>,
    now: u64,
    materialize: bool,
) -> ASuspendCheck
    decreases actions.len(),
{
    if actions.len() == 0 {
        ASuspendCheck {
            valid: true,
            settled: false,
            effects: Seq::empty(),
        }
    } else {
        let prior = spec_task_suspend_check(
            state, actions.drop_last(), now, materialize,
        );
        if !prior.valid {
            prior
        } else {
            let read = crate::promise_spec::spec_read_object(
                state, actions.last().awaited, now, materialize,
            );
            let effects = prior.effects + read.effects;
            match read.object {
                Some(object) if spec_awaitable(
                    spec_tags_otype(object.promise.tags),
                ) => ASuspendCheck {
                    valid: true,
                    settled: prior.settled
                        || object.promise.state != PromiseState::Pending,
                    effects,
                },
                _ => ASuspendCheck {
                    valid: false,
                    settled: prior.settled,
                    effects,
                },
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_task_suspend_check_invalid_extension(
    state: AState,
    prefix: Seq<APromiseRegisterCallbackReq>,
    suffix: Seq<APromiseRegisterCallbackReq>,
    now: u64,
    materialize: bool,
)
    requires !spec_task_suspend_check(state, prefix, now, materialize).valid,
    ensures spec_task_suspend_check(
        state, prefix + suffix, now, materialize,
    ) == spec_task_suspend_check(state, prefix, now, materialize),
    decreases suffix.len(),
{
    if suffix.len() > 0 {
        lemma_task_suspend_check_invalid_extension(
            state, prefix, suffix.drop_last(), now, materialize,
        );
        assert((prefix + suffix).drop_last()
            =~= prefix + suffix.drop_last());
        assert((prefix + suffix).last() == suffix.last());
    } else {
        assert(prefix + suffix =~= prefix);
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_suspend_register_one(
    state: AState,
    action: APromiseRegisterCallbackReq,
    task_id: AIdent,
    now: u64,
    materialize: bool,
) -> Seq<AEffect> {
    let read = crate::promise_spec::spec_read_object(
        state, action.awaited, now, materialize,
    );
    let write = match read.object {
        Some(object) => seq![AEffect::SetPromise(
            object.id,
            crate::state::spec_add_callback(object.promise, task_id),
        )],
        None => Seq::empty(),
    };
    read.effects + write
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_suspend_register(
    state: AState,
    actions: Seq<APromiseRegisterCallbackReq>,
    task_id: AIdent,
    now: u64,
    materialize: bool,
) -> Seq<AEffect>
    decreases actions.len(),
{
    if actions.len() == 0 {
        Seq::empty()
    } else {
        let prior = spec_task_suspend_register(
            state, actions.drop_last(), task_id, now, materialize,
        );
        prior + spec_task_suspend_register_one(
            state, actions.last(), task_id, now, materialize,
        )
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_suspend_action(
    state: AState,
    req: ATaskSuspendReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<ATaskSuspendRes> {
    if spec_task_invalid_suspend_actions(req.actions, req.id) {
        spec_task_finish(
            state,
            ATaskSuspendRes { status: 400, preload: Seq::empty() },
            Seq::empty(),
        )
    } else {
        let read = spec_task_read(state, req.id, now, materialize);
        match read.object {
            None => spec_task_finish(
                state,
                ATaskSuspendRes { status: 404, preload: Seq::empty() },
                read.effects,
            ),
            Some(object) => match object.task {
                None => spec_task_finish(
                    state,
                    ATaskSuspendRes { status: 404, preload: Seq::empty() },
                    read.effects,
                ),
                Some(task) => {
                    if task.state != TaskState::Acquired
                        || object.promise.state != PromiseState::Pending
                        || task.version != req.version
                    {
                        spec_task_finish(
                            state,
                            ATaskSuspendRes {
                                status: 409,
                                preload: Seq::empty(),
                            },
                            read.effects,
                        )
                    } else {
                        let checked = spec_task_suspend_check(
                            state, req.actions, now, materialize,
                        );
                        let checked_effects = read.effects + checked.effects;
                        if !checked.valid {
                            spec_task_finish(
                                state,
                                ATaskSuspendRes {
                                    status: 422,
                                    preload: Seq::empty(),
                                },
                                checked_effects,
                            )
                        } else if checked.settled {
                            let next = ATaskObject {
                                resumes: Seq::empty(),
                                ..task
                            };
                            spec_task_finish(
                                state,
                                ATaskSuspendRes {
                                    status: 300,
                                    preload: Seq::empty(),
                                },
                                checked_effects.push(AEffect::SetTask(
                                    object.id, next,
                                )),
                            )
                        } else {
                            let next = ATaskObject {
                                state: TaskState::Suspended,
                                pid: None,
                                ttl: None,
                                lease_timeout_at: None,
                                retry_timeout_at: None,
                                resumes: Seq::empty(),
                                ..task
                            };
                            spec_task_finish(
                                state,
                                ATaskSuspendRes {
                                    status: 200,
                                    preload: Seq::empty(),
                                },
                                checked_effects
                                    + spec_task_suspend_register(
                                        state,
                                        req.actions,
                                        req.id,
                                        now,
                                        materialize,
                                    )
                                    + seq![AEffect::SetTask(object.id, next)],
                            )
                        }
                    }
                }
            },
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_fulfill_action(
    state: AState,
    req: ATaskFulfillReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<ATaskFulfillRes> {
    if !spec_settable(req.action.state) {
        spec_task_finish(
            state,
            ATaskFulfillRes { status: 400, promise: None },
            Seq::empty(),
        )
    } else {
        let read = spec_task_read(state, req.id, now, materialize);
        match read.object {
            None => spec_task_finish(
                state,
                ATaskFulfillRes { status: 404, promise: None },
                read.effects,
            ),
            Some(object) => match object.task {
                None => spec_task_finish(
                    state,
                    ATaskFulfillRes { status: 404, promise: None },
                    read.effects,
                ),
                Some(task) => {
                    if task.state != TaskState::Acquired
                        || object.promise.state != PromiseState::Pending
                        || task.version != req.version
                    {
                        spec_task_finish(
                            state,
                            ATaskFulfillRes { status: 409, promise: None },
                            read.effects,
                        )
                    } else {
                        let promise = APromiseObject {
                            state: req.action.state,
                            value: req.action.value,
                            settled_at: Some(now),
                            ..object.promise
                        };
                        spec_task_finish(
                            state,
                            ATaskFulfillRes {
                                status: 200,
                                promise: Some(spec_promise_record(
                                    promise, object.id,
                                )),
                            },
                            read.effects
                                + crate::state::spec_set_settled_effects(
                                    object, promise,
                                ),
                        )
                    }
                }
            },
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_release_action(
    state: AState,
    req: ATaskReleaseReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<AStatusRes> {
    let read = spec_task_read(state, req.id, now, materialize);
    match read.object {
        None => spec_task_finish(
            state, AStatusRes { status: 404 }, read.effects,
        ),
        Some(object) => match object.task {
            None => spec_task_finish(
                state, AStatusRes { status: 404 }, read.effects,
            ),
            Some(task) => {
                if task.state != TaskState::Acquired
                    || object.promise.state != PromiseState::Pending
                    || task.version != req.version
                {
                    spec_task_finish(
                        state, AStatusRes { status: 409 }, read.effects,
                    )
                } else {
                    let next = ATaskObject {
                        state: TaskState::Pending,
                        pid: None,
                        ttl: None,
                        lease_timeout_at: None,
                        retry_timeout_at: Some(now),
                        ..task
                    };
                    spec_task_finish(
                        state,
                        AStatusRes { status: 200 },
                        read.effects.push(AEffect::SetTask(object.id, next)),
                    )
                }
            }
        },
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_halt_action(
    state: AState,
    req: ATaskHaltReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<AStatusRes> {
    let read = spec_task_read(state, req.id, now, materialize);
    match read.object {
        None => spec_task_finish(
            state, AStatusRes { status: 404 }, read.effects,
        ),
        Some(object) => match object.task {
            None => spec_task_finish(
                state, AStatusRes { status: 404 }, read.effects,
            ),
            Some(task) => {
                if task.state == TaskState::Fulfilled {
                    spec_task_finish(
                        state, AStatusRes { status: 409 }, read.effects,
                    )
                } else if task.state == TaskState::Halted {
                    spec_task_finish(
                        state, AStatusRes { status: 200 }, read.effects,
                    )
                } else {
                    let next = ATaskObject {
                        state: TaskState::Halted,
                        pid: None,
                        ttl: None,
                        lease_timeout_at: None,
                        retry_timeout_at: None,
                        ..task
                    };
                    spec_task_finish(
                        state,
                        AStatusRes { status: 200 },
                        read.effects.push(AEffect::SetTask(object.id, next)),
                    )
                }
            }
        },
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_continue_action(
    state: AState,
    req: ATaskContinueReq,
    now: u64,
    materialize: bool,
) -> ATaskActionResult<AStatusRes> {
    let read = spec_task_read(state, req.id, now, materialize);
    match read.object {
        None => spec_task_finish(
            state, AStatusRes { status: 404 }, read.effects,
        ),
        Some(object) => match object.task {
            None => spec_task_finish(
                state, AStatusRes { status: 404 }, read.effects,
            ),
            Some(task) => {
                if task.state != TaskState::Halted
                    || object.promise.state != PromiseState::Pending
                {
                    spec_task_finish(
                        state, AStatusRes { status: 409 }, read.effects,
                    )
                } else {
                    let next = ATaskObject {
                        state: TaskState::Pending,
                        retry_timeout_at: Some(now),
                        ..task
                    };
                    spec_task_finish(
                        state,
                        AStatusRes { status: 200 },
                        read.effects.push(AEffect::SetTask(object.id, next)),
                    )
                }
            }
        },
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_search_action(
    state: AState,
    _req: ATaskSearchReq,
    _now: u64,
    _materialize: bool,
) -> ATaskActionResult<ATaskSearchRes> {
    spec_task_finish(
        state,
        ATaskSearchRes {
            status: 501,
            tasks: Seq::empty(),
            cursor: None,
        },
        Seq::empty(),
    )
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_task_create_next_state(
    state: AState,
    req: ATaskCreateReq,
    now: u64,
    materialize: bool,
)
    ensures spec_task_create_action(state, req, now, materialize).next_state
        == spec_apply_all(
            state,
            spec_task_create_action(state, req, now, materialize).effects,
        ),
{
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_task_halt_next_state(
    state: AState,
    req: ATaskHaltReq,
    now: u64,
    materialize: bool,
)
    ensures spec_task_halt_action(state, req, now, materialize).next_state
        == spec_apply_all(
            state,
            spec_task_halt_action(state, req, now, materialize).effects,
        ),
{
}

} // verus!
