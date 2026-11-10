//! Resonate conformance properties over Rover's abstract state.
//!
//! Upstream's catalogue has 93 entries. 82 are directly expressible against
//! Rover's server state (38 state and 44 transition properties). The remaining
//! 11 mention the coalesced model's outbox:
//!
//! - new-message claims translate to the selected `StepResultV.send`;
//! - persistence translates to Rover's generic proved append-only-network
//!   theorem, `semantics::step_preserves_network`;
//! - outbox-key uniqueness is structural there but deliberately false of
//!   Rover's duplicate-delivery network;
//! - execute-address/target-tag equality is not recoverable because Rover
//!   compresses the target tag and its `Execute` dispatch carries no address.
//!
//! Two additional internal-provenance checks need the timeout event plus the
//! selected pending work; response properties need the request and emitted
//! response. True liveness needs a future infinite-execution/fairness layer,
//! while algebraic properties are equations between `on_event` compositions.
//!
//! The predicates below retain upstream names wherever their meaning survives.
//! `on_event_preserves_catalogue` is the explicit, unassumed preservation
//! obligation while handler proofs are ported.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use rover_spec::rover::comm::ProcessEvent;
use rover_spec::rover::RoverSpec::{Proc as _, StepResultV};
use rover_spec::rover::comm::Time;

use super::model::{Pid, Proc};
#[cfg(verus_keep_ghost)]
use super::trusted::origin;
use echod_types::{PromiseState, TaskState};
use super::machine::Config;
use super::protocol::Message;
#[cfg(verus_keep_ghost)]
use super::view::distinct;
use super::view::{Chars, PromiseV, ScheduleV, TaskV};

verus! {

// ---------------------------------------------------------------------------
// State properties
// ---------------------------------------------------------------------------

pub open spec fn well_formed_promise_created_at_lte_timeout_at_at(
    promise: PromiseV,
) -> bool {
    promise.created_at <= promise.timeout_at
}

pub open spec fn well_formed_promise_created_at_lte_timeout_at(
    _now: Time,
    state: Proc,
) -> bool {
    forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_created_at_lte_timeout_at_at(
            state.store.promises[id],
        )
}

pub open spec fn well_formed_promise_settled_at_lte_timeout_at_at(
    promise: PromiseV,
) -> bool {
    match promise.settled_at {
        Some(settled_at) => settled_at <= promise.timeout_at,
        None => true,
    }
}

pub open spec fn well_formed_promise_settled_at_lte_timeout_at(
    _now: Time,
    state: Proc,
) -> bool {
    forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_settled_at_lte_timeout_at_at(
            state.store.promises[id],
        )
}

pub open spec fn well_formed_promise_created_at_lte_settled_at_at(
    promise: PromiseV,
) -> bool {
    match promise.settled_at {
        Some(settled_at) => promise.created_at <= settled_at,
        None => true,
    }
}

pub open spec fn well_formed_promise_created_at_lte_settled_at(
    _now: Time,
    state: Proc,
) -> bool {
    forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_created_at_lte_settled_at_at(
            state.store.promises[id],
        )
}

pub open spec fn well_formed_promise_settled_at_iff_not_pending_at(
    promise: PromiseV,
) -> bool {
    (promise.state != PromiseState::Pending) == (promise.settled_at is Some)
}

pub open spec fn well_formed_promise_settled_at_iff_not_pending(
    _now: Time,
    state: Proc,
) -> bool {
    forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_settled_at_iff_not_pending_at(
            state.store.promises[id],
        )
}

pub open spec fn well_formed_promise_pending_created_before_deadline_at(
    promise: PromiseV,
) -> bool {
    promise.state != PromiseState::Pending || promise.created_at < promise.timeout_at
}

pub open spec fn well_formed_promise_pending_has_no_value_at(
    promise: PromiseV,
) -> bool {
    promise.state != PromiseState::Pending || promise.value.data is None
}

pub open spec fn well_formed_promise_deadline_settlement_has_no_value_at(
    promise: PromiseV,
) -> bool {
    promise.settled_at != Some(promise.timeout_at) || promise.value.data is None
}

pub open spec fn well_formed_promise_timedout_is_server_owned_at(
    promise: PromiseV,
) -> bool {
    promise.state != PromiseState::RejectedTimedout
        || promise.settled_at == Some(promise.timeout_at)
}

pub open spec fn well_formed_promise_callbacks_unique_at(
    promise: PromiseV,
) -> bool {
    // Rover stores callbacks as a set; duplicate callbacks are
    // unrepresentable rather than a separately checked row property.
    true
}

pub open spec fn well_formed_promise_listeners_unique_at(
    promise: PromiseV,
) -> bool {
    // Rover stores listeners as a set for the same reason.
    true
}

pub open spec fn well_formed_promise_awaiter_is_not_self_at(
    id: Chars,
    promise: PromiseV,
) -> bool {
    !promise.callbacks.contains(id)
}

pub open spec fn well_formed_promise_callbacks_same_origin_at(
    id: Chars,
    promise: PromiseV,
) -> bool {
    forall|awaiter: Chars| promise.callbacks.contains(awaiter) ==>
        origin(id) == origin(awaiter)
}

pub open spec fn well_formed_promise_created_at_lte_now_at(
    now: Time,
    promise: PromiseV,
) -> bool {
    promise.created_at <= now
}

pub open spec fn well_formed_promise_settled_at_lte_now_at(
    now: Time,
    promise: PromiseV,
) -> bool {
    match promise.settled_at {
        Some(settled_at) => settled_at <= now,
        None => true,
    }
}

pub open spec fn well_formed_task_acquired_iff_has_pid_at(task: TaskV) -> bool {
    (task.state == TaskState::Acquired) == (task.pid is Some)
}

pub open spec fn well_formed_task_acquired_iff_has_ttl_at(task: TaskV) -> bool {
    (task.state == TaskState::Acquired) == (task.ttl is Some)
}

pub open spec fn well_formed_task_pending_iff_has_retry_timeout_at_at(
    task: TaskV,
) -> bool {
    (task.state == TaskState::Pending) == (task.retry_timeout_at is Some)
}

pub open spec fn task_cleared(task: TaskV) -> bool {
    task.pid is None && task.ttl is None && task.retry_timeout_at is None
}

pub open spec fn well_formed_task_fulfilled_is_cleared_at(task: TaskV) -> bool {
    task.state != TaskState::Fulfilled || task_cleared(task)
}

pub open spec fn well_formed_task_suspended_is_cleared_at(task: TaskV) -> bool {
    task.state != TaskState::Suspended || task_cleared(task)
}

pub open spec fn well_formed_task_halted_is_cleared_at(task: TaskV) -> bool {
    task.state != TaskState::Halted || task_cleared(task)
}

pub open spec fn well_formed_task_suspended_has_no_resumes_at(
    task: TaskV,
) -> bool {
    task.state != TaskState::Suspended || task.resumes.len() == 0
}

pub open spec fn well_formed_task_resumes_unique_at(task: TaskV) -> bool {
    distinct(task.resumes)
}

pub open spec fn well_formed_task_acquired_version_positive_at(
    task: TaskV,
) -> bool {
    task.state != TaskState::Acquired || task.version > 0
}

pub open spec fn well_formed_schedule_created_at_lte_next_run_at_at(
    schedule: ScheduleV,
) -> bool {
    schedule.created_at <= schedule.next_run_at
}

pub open spec fn well_formed_schedule_created_at_lte_last_run_at_at(
    schedule: ScheduleV,
) -> bool {
    match schedule.last_run_at {
        Some(last) => schedule.created_at <= last,
        None => true,
    }
}

pub open spec fn well_formed_schedule_last_run_at_lt_next_run_at_at(
    schedule: ScheduleV,
) -> bool {
    match schedule.last_run_at {
        Some(last) => last < schedule.next_run_at,
        None => true,
    }
}

/// Object ids are map keys in Rover, so duplicate rows are unrepresentable.
pub open spec fn well_formed_store_object_ids_unique(_state: Proc) -> bool {
    true
}

/// Schedule ids are map keys for the same reason.
pub open spec fn well_formed_store_schedule_ids_unique(_state: Proc) -> bool {
    true
}

pub open spec fn state_catalogue(now: Time, state: Proc) -> bool {
    &&& well_formed_promise_created_at_lte_timeout_at(now, state)
    &&& well_formed_promise_settled_at_lte_timeout_at(now, state)
    &&& well_formed_promise_created_at_lte_settled_at(now, state)
    &&& well_formed_promise_settled_at_iff_not_pending(now, state)
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_pending_created_before_deadline_at(
            state.store.promises[id],
        )
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_pending_has_no_value_at(
            state.store.promises[id],
        )
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_deadline_settlement_has_no_value_at(
            state.store.promises[id],
        )
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_timedout_is_server_owned_at(
            state.store.promises[id],
        )
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_callbacks_unique_at(state.store.promises[id])
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_listeners_unique_at(state.store.promises[id])
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_awaiter_is_not_self_at(
            id,
            state.store.promises[id],
        )
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_callbacks_same_origin_at(
            id,
            state.store.promises[id],
        )
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_created_at_lte_now_at(
            now,
            state.store.promises[id],
        )
    &&& forall|id: Chars| state.store.promises.contains_key(id) ==>
        well_formed_promise_settled_at_lte_now_at(
            now,
            state.store.promises[id],
        )
    &&& forall|id: Chars| state.store.tasks.contains_key(id) ==>
        well_formed_task_acquired_iff_has_pid_at(state.store.tasks[id])
    &&& forall|id: Chars| state.store.tasks.contains_key(id) ==>
        well_formed_task_acquired_iff_has_ttl_at(state.store.tasks[id])
    &&& forall|id: Chars| state.store.tasks.contains_key(id) ==>
        well_formed_task_pending_iff_has_retry_timeout_at_at(
            state.store.tasks[id],
        )
    &&& forall|id: Chars| state.store.tasks.contains_key(id) ==>
        well_formed_task_fulfilled_is_cleared_at(state.store.tasks[id])
    &&& forall|id: Chars| state.store.tasks.contains_key(id) ==>
        well_formed_task_suspended_is_cleared_at(state.store.tasks[id])
    &&& forall|id: Chars| state.store.tasks.contains_key(id) ==>
        well_formed_task_halted_is_cleared_at(state.store.tasks[id])
    &&& forall|id: Chars| state.store.tasks.contains_key(id) ==>
        well_formed_task_suspended_has_no_resumes_at(state.store.tasks[id])
    &&& forall|id: Chars| state.store.tasks.contains_key(id) ==>
        well_formed_task_resumes_unique_at(state.store.tasks[id])
    &&& forall|id: Chars| state.store.tasks.contains_key(id) ==>
        well_formed_task_acquired_version_positive_at(state.store.tasks[id])
    &&& forall|id: Chars| state.store.schedules.contains_key(id) ==>
        well_formed_schedule_created_at_lte_next_run_at_at(
            state.store.schedules[id],
        )
    &&& forall|id: Chars| state.store.schedules.contains_key(id) ==>
        well_formed_schedule_created_at_lte_last_run_at_at(
            state.store.schedules[id],
        )
    &&& forall|id: Chars| state.store.schedules.contains_key(id) ==>
        well_formed_schedule_last_run_at_lt_next_run_at_at(
            state.store.schedules[id],
        )
    &&& well_formed_store_object_ids_unique(state)
    &&& well_formed_store_schedule_ids_unique(state)
}

// ---------------------------------------------------------------------------
// Transition and event properties
// ---------------------------------------------------------------------------

pub open spec fn monotone_promise_set_grows(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars| before.store.promises.contains_key(id) ==>
        after.store.promises.contains_key(id)
}

pub open spec fn monotone_task_set_grows(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars| before.store.tasks.contains_key(id) ==>
        after.store.tasks.contains_key(id)
}

pub open spec fn preserved_promise_birth_fields_immutable(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars|
        before.store.promises.contains_key(id)
        && after.store.promises.contains_key(id)
        ==> {
            let a = before.store.promises[id];
            let b = after.store.promises[id];
            &&& a.created_at == b.created_at
            &&& a.timeout_at == b.timeout_at
            &&& a.param == b.param
            &&& a.tags == b.tags
        }
}

pub open spec fn preserved_schedule_birth_fields_immutable(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars|
        before.store.schedules.contains_key(id)
        && after.store.schedules.contains_key(id)
        ==> {
            let a = before.store.schedules[id];
            let b = after.store.schedules[id];
            &&& a.created_at == b.created_at
            &&& a.cron == b.cron
            &&& a.promise_id == b.promise_id
            &&& a.promise_timeout == b.promise_timeout
            &&& a.promise_param == b.promise_param
            &&& a.promise_tags == b.promise_tags
        }
}

pub open spec fn preserved_promise_settlement_is_one_way(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars|
        before.store.promises.contains_key(id)
        && after.store.promises.contains_key(id)
        && before.store.promises[id].settled_at is Some
        ==> after.store.promises[id].settled_at
            == before.store.promises[id].settled_at
}

pub open spec fn preserved_promise_state_frozen_once_settled(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars|
        before.store.promises.contains_key(id)
        && after.store.promises.contains_key(id)
        && before.store.promises[id].state != PromiseState::Pending
        ==> after.store.promises[id].state
            == before.store.promises[id].state
}

pub open spec fn preserved_promise_value_until_settlement(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars|
        before.store.promises.contains_key(id)
        && after.store.promises.contains_key(id)
        && before.store.promises[id].state == PromiseState::Pending
        && after.store.promises[id].state == PromiseState::Pending
        ==> after.store.promises[id].value
            == before.store.promises[id].value
}

pub open spec fn monotone_task_version(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars|
        before.store.tasks.contains_key(id)
        && after.store.tasks.contains_key(id)
        ==> after.store.tasks[id].version >= before.store.tasks[id].version
}

pub open spec fn monotone_promise_callbacks_while_pending(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars, callback: Chars|
        before.store.promises.contains_key(id)
        && after.store.promises.contains_key(id)
        && before.store.promises[id].state == PromiseState::Pending
        && after.store.promises[id].state == PromiseState::Pending
        && before.store.promises[id].callbacks.contains(callback)
        ==> after.store.promises[id].callbacks.contains(callback)
}

pub open spec fn monotone_promise_listeners_while_pending(
    _now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    forall|id: Chars, listener: Chars|
        before.store.promises.contains_key(id)
        && after.store.promises.contains_key(id)
        && before.store.promises[id].state == PromiseState::Pending
        && after.store.promises[id].state == PromiseState::Pending
        && before.store.promises[id].listeners.contains(listener)
        ==> after.store.promises[id].listeners.contains(listener)
}

pub open spec fn transition_catalogue(
    now: Time,
    before: Proc,
    after: Proc,
) -> bool {
    &&& monotone_promise_set_grows(now, before, after)
    &&& monotone_task_set_grows(now, before, after)
    &&& preserved_promise_birth_fields_immutable(now, before, after)
    &&& preserved_schedule_birth_fields_immutable(now, before, after)
    &&& preserved_promise_settlement_is_one_way(now, before, after)
    &&& preserved_promise_state_frozen_once_settled(now, before, after)
    &&& preserved_promise_value_until_settlement(now, before, after)
    &&& monotone_task_version(now, before, after)
    &&& monotone_promise_callbacks_while_pending(now, before, after)
    &&& monotone_promise_listeners_while_pending(now, before, after)
}

pub open spec fn step_catalogue(
    now: Time,
    before: Proc,
    event: ProcessEvent<Pid, Message>,
    outcome: StepResultV<Proc, Pid, Message>,
) -> bool {
    &&& state_catalogue(now, outcome.state)
    &&& transition_catalogue(now, before, outcome.state)
}

// ---------------------------------------------------------------------------
// Preservation obligation
// ---------------------------------------------------------------------------

/// The exact obligation every allowed `on_event` outcome must discharge.
pub open spec fn on_event_preserves_catalogue(config: Config) -> bool {
    forall|before: Proc, now: Time, event: ProcessEvent<Pid, Message>, i: int|
        #![trigger before.on_event(config, now, event)[i]]
        state_catalogue(now, before)
        && 0 <= i
        && i < before.on_event(config, now, event).len()
        ==> step_catalogue(
            now,
            before,
            event,
            before.on_event(config, now, event)[i],
        )
}

} // verus!
