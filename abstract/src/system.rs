//! Semantic dispatch and, separately, observation bookkeeping.
//!
//! `handle_external`/`handle_internal` know nothing about calls or clocks.
//! `Bookkeeping` knows nothing about `State`, effects, or handlers. This
//! prevents Invoke/Return/Receive/Clock trace maintenance from becoming an
//! accidental semantic action.

use vstd::prelude::*;
use crate::external::*;
use crate::internal::*;
use crate::state::*;
use crate::types::*;

verus! {

pub enum ExternalAction {
    PromiseGet(PromiseGetReq),
    PromiseCreate(PromiseCreateReq),
    PromiseSettle(PromiseSettleReq),
    PromiseRegisterCallback(PromiseRegisterCallbackReq),
    PromiseRegisterListener(PromiseRegisterListenerReq),
    PromiseSearch(PromiseSearchReq),
    ScheduleGet(ScheduleGetReq),
    ScheduleCreate(ScheduleCreateReq),
    ScheduleDelete(ScheduleDeleteReq),
    ScheduleSearch(ScheduleSearchReq),
    TaskGet(TaskGetReq),
    TaskCreate(TaskCreateReq),
    TaskAcquire(TaskAcquireReq),
    TaskFence(TaskFenceReq),
    TaskHeartbeat(TaskHeartbeatReq),
    TaskSuspend(TaskSuspendReq),
    TaskFulfill(TaskFulfillReq),
    TaskRelease(TaskReleaseReq),
    TaskHalt(TaskHaltReq),
    TaskContinue(TaskContinueReq),
    TaskSearch(TaskSearchReq),
    /// The second half of a detached fence; see `decompose`.
    TaskFenceCheck(TaskFenceCheckReq),
}

pub enum InternalAction {
    PromiseTimeout(PromiseTimeoutReq),
    Callback(PromiseRegisterCallbackReq),
    Listener(PromiseRegisterListenerReq),
    TaskLeaseTimeout(TaskLeaseTimeoutReq),
    TaskRetryTimeout(TaskRetryTimeoutReq),
    /// A schedule's occurrence becomes a promise.
    ScheduleFire(ScheduleFireReq),
    /// A schedule moves past an occurrence whose promise exists.
    ScheduleAdvance(ScheduleAdvanceReq),
}

pub enum SemanticAction {
    External(ExternalAction),
    Internal(InternalAction),
    Idle,
}

pub enum Response {
    PromiseGet(PromiseGetRes),
    PromiseCreate(PromiseCreateRes),
    PromiseSettle(PromiseSettleRes),
    PromiseRegisterCallback(PromiseRegisterCallbackRes),
    PromiseRegisterListener(PromiseRegisterListenerRes),
    PromiseSearch(PromiseSearchRes),
    ScheduleGet(ScheduleGetRes),
    ScheduleCreate(ScheduleCreateRes),
    ScheduleDelete(ScheduleDeleteRes),
    ScheduleSearch(ScheduleSearchRes),
    TaskGet(TaskGetRes),
    TaskCreate(TaskCreateRes),
    TaskAcquire(TaskAcquireRes),
    TaskFence(TaskFenceRes),
    TaskHeartbeat(TaskHeartbeatRes),
    TaskSuspend(TaskSuspendRes),
    TaskFulfill(TaskFulfillRes),
    TaskRelease(TaskReleaseRes),
    TaskHalt(TaskHaltRes),
    TaskContinue(TaskContinueRes),
    TaskSearch(TaskSearchRes),
    TaskFenceCheck(StatusRes),
    Silent,
}

// Protocol requests that are more than one action ---------------------------

/// How a protocol request runs: as the one action it names, or, for a fence
/// whose create lives in another origin than the task, as two. The create
/// commits first, on its own; the fence's check follows on the task's. Any
/// action may interleave between them, and a stale fence still leaves the
/// promise created and answers its 409. The atomic `TaskFence` action keeps
/// refusing such a request with 400: it is the dispatcher that splits it,
/// exactly as the node's does.
pub enum Request {
    Whole(ExternalAction),
    Detached { create: PromiseCreateReq, check: TaskFenceCheckReq },
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_detached(
    id: AIdent, version: u64, action: ATaskFenceAction,
) -> Option<(APromiseCreateReq, ATaskFenceCheckReq)> {
    match action {
        ATaskFenceAction::Create(create) if create.id.origin != id.origin =>
            Some((create, ATaskFenceCheckReq { id, version })),
        _ => None,
    }
}

pub fn decompose(action: ExternalAction) -> (r: Request)
    ensures match action {
        ExternalAction::TaskFence(q) => match spec_detached(q@.id, q@.version, q@.action) {
            Some((create, check)) => r is Detached
                && r->create@ == create && r->check@ == check,
            None => r is Whole && r->Whole_0 == action,
        },
        _ => r is Whole && r->Whole_0 == action,
    },
{
    match action {
        ExternalAction::TaskFence(q) => {
            let cross = match &q.action {
                TaskFenceAction::Create(c) => !c.id.same_origin(&q.id),
                TaskFenceAction::Settle(_) => false,
            };
            if cross {
                match q.action {
                    TaskFenceAction::Create(create) => Request::Detached {
                        create,
                        check: TaskFenceCheckReq { id: q.id, version: q.version },
                    },
                    TaskFenceAction::Settle(settle) => {
                        // unreachable: `cross` is false for a settle
                        assert(false);
                        Request::Whole(ExternalAction::TaskFence(TaskFenceReq {
                            id: q.id, version: q.version, action: TaskFenceAction::Settle(settle),
                        }))
                    }
                }
            } else {
                Request::Whole(ExternalAction::TaskFence(q))
            }
        }
        other => Request::Whole(other),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_compose_detached(
    inner: APromiseRes, check: AStatusRes,
) -> ATaskFenceRes {
    ATaskFenceRes {
        status: check.status,
        action: if check.status == 200 {
            Some(ATaskFenceInnerRes::Create(inner))
        } else {
            None
        },
        preload: Seq::empty(),
    }
}

/// The fence's answer: the check's status, with the create's record inside
/// when the check held.
pub fn compose_detached(inner: PromiseRes, check: StatusRes) -> (r: TaskFenceRes)
    ensures r@ == spec_compose_detached(inner@, check@),
{
    let ghost inner_spec = inner@;
    let preload = Vec::new();
    assert(preload.deep_view() =~= Seq::<APromiseRecord>::empty());
    let action = if check.status == 200 {
        Some(TaskFenceInnerRes::Create(inner))
    } else {
        None
    };
    let r = TaskFenceRes { status: check.status, action, preload };
    assert(r@ == spec_compose_detached(inner_spec, check@));
    r
}

pub fn handle_external(
    state: &State, action: ExternalAction, now: u64, materialize: bool,
) -> Transition<Response> {
    match action {
        ExternalAction::PromiseGet(q) => {
            let x = promise_get_action(state, &q, now, materialize);
            Transition { response: Response::PromiseGet(x.response), effects: x.effects }
        }
        ExternalAction::PromiseCreate(q) => {
            let x = promise_create_action(state, q, now, materialize);
            Transition { response: Response::PromiseCreate(x.response), effects: x.effects }
        }
        ExternalAction::PromiseSettle(q) => {
            let x = promise_settle_action(state, q, now, materialize);
            Transition { response: Response::PromiseSettle(x.response), effects: x.effects }
        }
        ExternalAction::PromiseRegisterCallback(q) => {
            let x = promise_register_callback_action(state, &q, now, materialize);
            Transition { response: Response::PromiseRegisterCallback(x.response), effects: x.effects }
        }
        ExternalAction::PromiseRegisterListener(q) => {
            let x = promise_register_listener_action(state, &q, now, materialize);
            Transition { response: Response::PromiseRegisterListener(x.response), effects: x.effects }
        }
        ExternalAction::PromiseSearch(q) => {
            let x = promise_search_action(state, &q, now, materialize);
            Transition { response: Response::PromiseSearch(x.response), effects: x.effects }
        }
        ExternalAction::ScheduleGet(q) => {
            let x = schedule_get_action(state, &q, now, materialize);
            Transition { response: Response::ScheduleGet(x.response), effects: x.effects }
        }
        ExternalAction::ScheduleCreate(q) => {
            let x = schedule_create_action(state, q, now, materialize);
            Transition { response: Response::ScheduleCreate(x.response), effects: x.effects }
        }
        ExternalAction::ScheduleDelete(q) => {
            let x = schedule_delete_action(state, &q, now, materialize);
            Transition { response: Response::ScheduleDelete(x.response), effects: x.effects }
        }
        ExternalAction::ScheduleSearch(q) => {
            let x = schedule_search_action(state, &q, now, materialize);
            Transition { response: Response::ScheduleSearch(x.response), effects: x.effects }
        }
        ExternalAction::TaskGet(q) => {
            let x = task_get_action(state, &q, now, materialize);
            Transition { response: Response::TaskGet(x.response), effects: x.effects }
        }
        ExternalAction::TaskCreate(q) => {
            let x = task_create_action(state, q, now, materialize);
            Transition { response: Response::TaskCreate(x.response), effects: x.effects }
        }
        ExternalAction::TaskAcquire(q) => {
            let x = task_acquire_action(state, q, now, materialize);
            Transition { response: Response::TaskAcquire(x.response), effects: x.effects }
        }
        ExternalAction::TaskFence(q) => {
            let x = task_fence_action(state, q, now, materialize);
            Transition { response: Response::TaskFence(x.response), effects: x.effects }
        }
        ExternalAction::TaskHeartbeat(q) => {
            let x = task_heartbeat_action(state, &q, now, materialize);
            Transition { response: Response::TaskHeartbeat(x.response), effects: x.effects }
        }
        ExternalAction::TaskSuspend(q) => {
            let x = task_suspend_action(state, &q, now, materialize);
            Transition { response: Response::TaskSuspend(x.response), effects: x.effects }
        }
        ExternalAction::TaskFulfill(q) => {
            let x = task_fulfill_action(state, q, now, materialize);
            Transition { response: Response::TaskFulfill(x.response), effects: x.effects }
        }
        ExternalAction::TaskRelease(q) => {
            let x = task_release_action(state, &q, now, materialize);
            Transition { response: Response::TaskRelease(x.response), effects: x.effects }
        }
        ExternalAction::TaskHalt(q) => {
            let x = task_halt_action(state, &q, now, materialize);
            Transition { response: Response::TaskHalt(x.response), effects: x.effects }
        }
        ExternalAction::TaskContinue(q) => {
            let x = task_continue_action(state, &q, now, materialize);
            Transition { response: Response::TaskContinue(x.response), effects: x.effects }
        }
        ExternalAction::TaskSearch(q) => {
            let x = task_search_action(state, &q, now, materialize);
            Transition { response: Response::TaskSearch(x.response), effects: x.effects }
        }
        ExternalAction::TaskFenceCheck(q) => {
            let x = task_fence_check_action(state, &q, now, materialize);
            Transition { response: Response::TaskFenceCheck(x.response), effects: x.effects }
        }
    }
}

pub fn handle_internal(
    state: &State, action: InternalAction, now: u64, config: &Config,
) -> Vec<Effect> {
    match action {
        InternalAction::PromiseTimeout(q) =>
            process_promise_timeout_action(state, &q, now, config),
        InternalAction::Callback(q) =>
            process_callback_action(state, &q, now, config),
        InternalAction::Listener(q) =>
            process_listener_action(state, &q, now, config),
        InternalAction::TaskLeaseTimeout(q) =>
            process_lease_timeout_action(state, &q, now, config),
        InternalAction::TaskRetryTimeout(q) =>
            process_retry_timeout_action(state, &q, now, config),
        InternalAction::ScheduleFire(q) =>
            process_schedule_fire_action(state, &q, now, config),
        InternalAction::ScheduleAdvance(q) =>
            process_schedule_advance_action(state, &q, now, config),
    }
}

pub fn handle_semantic(
    state: &State,
    action: SemanticAction,
    now: u64,
    materialize: bool,
    config: &Config,
) -> Transition<Response> {
    match action {
        SemanticAction::External(x) => handle_external(state, x, now, materialize),
        SemanticAction::Internal(x) => Transition {
            response: Response::Silent,
            effects: handle_internal(state, x, now, config),
        },
        SemanticAction::Idle => Transition {
            response: Response::Silent,
            effects: Vec::new(),
        },
    }
}

pub fn run_external(
    state: State, action: ExternalAction, now: u64, materialize: bool,
) -> (Response, State) {
    let step = handle_external(&state, action, now, materialize);
    (step.response, apply_all(state, step.effects))
}

pub fn run_internal(
    state: State, action: InternalAction, now: u64, config: &Config,
) -> State {
    let effects = handle_internal(&state, action, now, config);
    apply_all(state, effects)
}

pub fn run_semantic(
    state: State,
    action: SemanticAction,
    now: u64,
    materialize: bool,
    config: &Config,
) -> (Response, State) {
    let step = handle_semantic(&state, action, now, materialize, config);
    (step.response, apply_all(state, step.effects))
}

// Observation bookkeeping --------------------------------------------------

pub enum Observation {
    Invoke { call: u64, action: ExternalAction },
    Return { call: u64, response: Response },
    Receive { message: Message },
    Clock { at: u64 },
}

pub struct Bookkeeping {
    pub observations: Vec<Observation>,
}

impl Bookkeeping {
    pub fn new() -> Bookkeeping {
        Bookkeeping { observations: Vec::new() }
    }

    /// Pure trace append: deliberately no `State`, `Effect`, or handler.
    pub fn record(&mut self, observation: Observation) {
        self.observations.push(observation);
    }
}

} // verus!
