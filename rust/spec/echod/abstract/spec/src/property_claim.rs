//! property_claim definitions for the abstract model.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::contrib::make_spec_type;
use echod_types::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::*;
use rover_spec::rover::comm::{Sched, ProcessEvent};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
use crate::state::{Time, Chars, PromiseV, TaskV, ScheduleV, Proc};
use crate::rover::{Config};
#[cfg(verus_keep_ghost)]
use crate::handler::{on_event, distinct};
use crate::rover::{Pid, empty_store};
#[cfg(verus_keep_ghost)]
use crate::axioms::*;

verus! {
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

pub open spec fn well_formed_task_has_matching_promise(
    _now: Time,
    state: Proc,
) -> bool {
    forall|id: Chars| state.store.tasks.contains_key(id) ==>
        state.store.promises.contains_key(id)
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

pub open spec fn well_formed_store_object_ids_unique(_state: Proc) -> bool {
    true
}

pub open spec fn well_formed_store_schedule_ids_unique(_state: Proc) -> bool {
    true
}

pub open spec fn state_properties(now: Time, state: Proc) -> bool {
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
    &&& well_formed_task_has_matching_promise(now, state)
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

pub open spec fn transition_properties(
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

pub open spec fn step_properties(
    now: Time,
    before: Proc,
    event: ProcessEvent<Pid, Message>,
    outcome: StepResultV<Proc, Pid, Message>,
) -> bool {
    &&& state_properties(now, outcome.state)
    &&& transition_properties(now, before, outcome.state)
}

pub open spec fn property_claim(config: Config) -> bool {
    &&& state_properties(
        0,
        Proc {
            store: super::rover::empty_store(),
            pending: Seq::empty(),
        },
    )
    &&& forall|before: Proc, now: Time, event: ProcessEvent<Pid, Message>, i: int|
            #![trigger before.on_event(config, now, event)[i]]
            state_properties(now, before)
            && 0 <= i
            && i < before.on_event(config, now, event).len()
            ==> step_properties(
                now,
                before,
                event,
                before.on_event(config, now, event)[i],
            )
}
}
