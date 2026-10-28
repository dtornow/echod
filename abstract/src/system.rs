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
}

pub enum InternalAction {
    PromiseTimeout(PromiseTimeoutReq),
    Callback(PromiseRegisterCallbackReq),
    Listener(PromiseRegisterListenerReq),
    TaskLeaseTimeout(TaskLeaseTimeoutReq),
    TaskRetryTimeout(TaskRetryTimeoutReq),
    ScheduleTimeout(ScheduleTimeoutReq),
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
    Silent,
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
        InternalAction::ScheduleTimeout(q) =>
            process_schedule_action(state, &q, now, config),
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
