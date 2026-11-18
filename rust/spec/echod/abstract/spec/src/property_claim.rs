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
pub open spec fn installed_origin_frame(live: crate::state::StoreV, evaluated: crate::state::StoreV, workflow: Chars) -> bool {
    let installed = crate::handler::spec_install_origin(live, evaluated, workflow);
    &&& installed.schedules == live.schedules
    &&& forall|id: Chars| {
        let source = if origin(id) == workflow { evaluated } else { live };
        &&& #[trigger] installed.promises.contains_key(id) == source.promises.contains_key(id)
        &&& #[trigger] installed.tasks.contains_key(id) == source.tasks.contains_key(id)
        &&& (installed.promises.contains_key(id) ==> installed.promises[id] == source.promises[id])
        &&& (installed.tasks.contains_key(id) ==> installed.tasks[id] == source.tasks[id])
    }
}

pub open spec fn installed_schedule_frame(live: crate::state::StoreV, evaluated: crate::state::StoreV, schedule: Chars) -> bool {
    let installed = crate::handler::spec_install_schedule(live, evaluated, schedule);
    &&& installed.promises == live.promises
    &&& installed.tasks == live.tasks
    &&& forall|id: Chars| {
        let source = if id == schedule { evaluated } else { live };
        &&& #[trigger] installed.schedules.contains_key(id) == source.schedules.contains_key(id)
        &&& (installed.schedules.contains_key(id) ==> installed.schedules[id] == source.schedules[id])
    }
}

pub open spec fn callback_plans_permute(
    config: crate::rover::Config, s: crate::state::StoreV, source: Seq<char>,
    a: Seq<Seq<char>>, b: Seq<Seq<char>>, now: u64,
) -> bool {
    let aa = crate::handler::spec_drain_timed_callback_plan(config, s, source, a, a.len(), now);
    let bb = crate::handler::spec_drain_timed_callback_plan(config, s, source, b, b.len(), now);
    aa.0 == bb.0 && aa.1.to_multiset() == bb.1.to_multiset()
}

pub open spec fn listener_plans_permute(
    s: crate::state::StoreV, source: Seq<char>, a: Seq<Seq<char>>, b: Seq<Seq<char>>, now: u64,
) -> bool {
    let aa = crate::handler::spec_drain_timed_listener_plan(s, source, a, a.len(), now);
    let bb = crate::handler::spec_drain_timed_listener_plan(s, source, b, b.len(), now);
    aa.0 == bb.0 && aa.1.to_multiset() == bb.1.to_multiset()
}

pub open spec fn callback_drain_ready(s: crate::state::StoreV, source: Seq<char>, now: u64) -> bool {
    &&& s.promises.contains_key(source)
    &&& s.promises[source].state != echod_types::PromiseState::Pending
    &&& drain_target_ready(s, source, now)
    &&& forall|target: Seq<char>| #[trigger] s.promises[source].callbacks.contains(target) ==> drain_target_ready(s, target, now)
}

pub open spec fn listener_drain_ready(s: crate::state::StoreV, source: Seq<char>, now: u64) -> bool {
    s.promises.contains_key(source) && s.promises[source].state != echod_types::PromiseState::Pending
        && drain_target_ready(s, source, now)
}

pub open spec fn drain_target_ready(s: crate::state::StoreV, target: Seq<char>, now: u64) -> bool {
    &&& (s.tasks.contains_key(target) ==> s.promises.contains_key(target))
    &&& (s.promises.contains_key(target) ==> {
        &&& (s.promises[target].state == echod_types::PromiseState::Pending ==> now < s.promises[target].timeout_at)
        &&& (s.tasks.contains_key(target) && s.promises[target].state != echod_types::PromiseState::Pending
            ==> s.tasks[target].state == echod_types::TaskState::Fulfilled)
    })
}

pub open spec fn same_source_callbacks_commute(
    config: crate::rover::Config, s: crate::state::StoreV, source: Seq<char>,
    a: Seq<char>, b: Seq<char>, now: u64,
) -> bool {
    let (after_a, send_a) = crate::handler::spec_drain_timed_callback(config, s, source, a, now);
    let (after_ab, send_b_after_a) = crate::handler::spec_drain_timed_callback(config, after_a, source, b, now);
    let (after_b, send_b) = crate::handler::spec_drain_timed_callback(config, s, source, b, now);
    let (after_ba, send_a_after_b) = crate::handler::spec_drain_timed_callback(config, after_b, source, a, now);
    a != b ==> after_ab == after_ba && send_a == send_a_after_b && send_b == send_b_after_a
}

pub open spec fn same_source_listeners_commute(
    s: crate::state::StoreV, source: Seq<char>, a: Seq<char>, b: Seq<char>, now: u64,
) -> bool {
    let after_a = crate::handler::spec_listener(s, source, a, now);
    let after_ab = crate::handler::spec_listener(after_a.next, source, b, now);
    let after_b = crate::handler::spec_listener(s, source, b, now);
    let after_ba = crate::handler::spec_listener(after_b.next, source, a, now);
    a != b ==> after_ab.next == after_ba.next && after_a.send == after_ba.send && after_b.send == after_ab.send
}

pub open spec fn timed_continuation_preserves_admission(work: crate::state::TimedWorkV, response: echod_types::Response) -> bool {
    match crate::handler::spec_continue_timed(work, response) {
        None => true,
        Some(next) => next.call == work.call && next.admitted_at == work.admitted_at,
    }
}

pub open spec fn timed_check_preserves_current_store(
    config: crate::rover::Config, work: crate::state::TimedWorkV, current: crate::state::StoreV, read_committed_at: u64,
) -> bool {
    work.stage is DetachedCheck ==> {
        let outcomes = crate::handler::spec_timed_handler_outcomes(config, work, current, read_committed_at);
        outcomes.len() == 1 && outcomes[0].next == current
    }
}

pub open spec fn detached_fence_preserves_committed_store(
    pending: crate::state::DetachedFenceV,
    store: crate::state::StoreV,
) -> bool {
    let outcomes = crate::handler::spec_detached_fence(pending, store);
    &&& outcomes.len() == 1
    &&& outcomes[0].next == store
    &&& outcomes[0].work.len() == 0
    &&& outcomes[0].send.len() == 0
}

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
    match schedule.next_run_at {
        Some(next) => schedule.created_at <= next,
        None => true,
    }
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
        Some(last) => match schedule.next_run_at {
            Some(next) => last < next,
            None => true,
        },
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
            detached: Seq::empty(),
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
