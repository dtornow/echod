//! property_proof definitions for the abstract model.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::contrib::make_spec_type;
use echod_types::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::*;
use rover_spec::rover::comm::{Sched, ProcessEvent};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
use crate::state::{Time, Chars, PromiseV, TaskV, StoreV, InternalV, OutV, SpecHeld, Proc};
use crate::rover::{Config};
#[cfg(verus_keep_ghost)]
use crate::handler::{on_event, strs, schedule_v, sat_add, distinct, all_in_origin, lift_dispatch, spec_before, spec_min_key, spec_sorted, least, spec_keys, spec_is_timer, spec_has_target, spec_delay, spec_external, spec_string, spec_empty_value, spec_acquire, spec_schedule_value, spec_new_object, spec_status_res, spec_held, spec_promise_create, spec_promise_settle, spec_task_create, spec_awaited, spec_callbacks, spec_any_settled, spec_refs_one_origin, spec_extend, spec_handler, spec_body, spec_process_work, spec_send, spec_request_outcome, spec_shed, spec_lose, spec_losses, spec_ready, spec_internal_result, spec_idle, spec_run, spec_due_result, spec_queue, spec_keep, spec_over_callbacks, spec_over_listeners, spec_over_promises, spec_over_tasks, spec_over_schedules, spec_derived, spec_run_timeout, spec_service};
use crate::rover::{Pid, empty_store};
#[cfg(verus_keep_ghost)]
use crate::property_claim::{well_formed_promise_created_at_lte_timeout_at_at, well_formed_promise_created_at_lte_timeout_at, well_formed_promise_settled_at_lte_timeout_at_at, well_formed_promise_settled_at_lte_timeout_at, well_formed_promise_created_at_lte_settled_at_at, well_formed_promise_created_at_lte_settled_at, well_formed_promise_settled_at_iff_not_pending_at, well_formed_promise_settled_at_iff_not_pending, well_formed_promise_pending_created_before_deadline_at, well_formed_promise_pending_has_no_value_at, well_formed_promise_deadline_settlement_has_no_value_at, well_formed_promise_timedout_is_server_owned_at, well_formed_promise_awaiter_is_not_self_at, well_formed_promise_callbacks_same_origin_at, well_formed_promise_created_at_lte_now_at, well_formed_promise_settled_at_lte_now_at, well_formed_task_acquired_iff_has_pid_at, well_formed_task_acquired_iff_has_ttl_at, well_formed_task_pending_iff_has_retry_timeout_at_at, well_formed_task_fulfilled_is_cleared_at, well_formed_task_suspended_is_cleared_at, well_formed_task_halted_is_cleared_at, well_formed_task_suspended_has_no_resumes_at, well_formed_task_resumes_unique_at, well_formed_task_acquired_version_positive_at, well_formed_task_has_matching_promise, well_formed_store_object_ids_unique, well_formed_store_schedule_ids_unique, state_properties, monotone_promise_set_grows, monotone_task_set_grows, preserved_promise_birth_fields_immutable, preserved_schedule_birth_fields_immutable, preserved_promise_settlement_is_one_way, preserved_promise_state_frozen_once_settled, preserved_promise_value_until_settlement, monotone_task_version, monotone_promise_callbacks_while_pending, monotone_promise_listeners_while_pending, transition_properties, step_properties, property_claim};
#[cfg(verus_keep_ghost)]
use crate::axioms::*;

verus! {
pub broadcast proof fn lemma_mv_empty<A, B>(f: spec_fn(A) -> B)
    ensures
        #[trigger] Seq::<A>::empty().map_values(f) == Seq::<B>::empty(),
{
    assert(Seq::<A>::empty().map_values(f) =~= Seq::<B>::empty());
}

pub broadcast proof fn lemma_mv_push<A, B>(v: Seq<A>, x: A, f: spec_fn(A) -> B)
    ensures
        #[trigger] v.push(x).map_values(f) == v.map_values(f).push(f(x)),
{
    assert(v.push(x).map_values(f) =~= v.map_values(f).push(f(x)));
}

pub broadcast proof fn lemma_mv_add<A, B>(a: Seq<A>, b: Seq<A>, f: spec_fn(A) -> B)
    ensures
        #[trigger] (a + b).map_values(f) == a.map_values(f) + b.map_values(f),
{
    assert((a + b).map_values(f) =~= a.map_values(f) + b.map_values(f));
}

pub broadcast proof fn lemma_mv_take<A, B>(v: Seq<A>, i: int, f: spec_fn(A) -> B)
    requires
        0 <= i <= v.len(),
    ensures
        #[trigger] v.take(i).map_values(f) == v.map_values(f).take(i),
{
    assert(v.take(i).map_values(f) =~= v.map_values(f).take(i));
}

pub broadcast proof fn lemma_map_values_insert<A, B>(m: Map<Chars, A>, k: Chars, v: A, f: spec_fn(A) -> B)
    ensures
        #[trigger] m.insert(k, v).map_values(f) == m.map_values(f).insert(k, f(v)),
{
    assert(m.insert(k, v).map_values(f) =~= m.map_values(f).insert(k, f(v)));
}

pub broadcast proof fn lemma_map_values_remove<A, B>(m: Map<Chars, A>, k: Chars, f: spec_fn(A) -> B)
    ensures
        #[trigger] m.remove(k).map_values(f) == m.map_values(f).remove(k),
{
    assert(m.remove(k).map_values(f) =~= m.map_values(f).remove(k));
}

pub broadcast proof fn lemma_strs_len(v: Seq<String>)
    ensures
        #[trigger] strs(v).len() == v.len(),
{
}

pub broadcast proof fn lemma_strs_index(v: Seq<String>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] strs(v)[i] == v[i]@,
{
}

pub broadcast proof fn lemma_strs_empty(v: Seq<String>)
    requires
        v.len() == 0,
    ensures
        #[trigger] strs(v) == Seq::<Chars>::empty(),
{
    assert(strs(v) =~= Seq::<Chars>::empty());
}

pub broadcast group group_views {
    lemma_strs_len,
    lemma_strs_index,
    lemma_strs_empty,
    lemma_mv_empty,
    lemma_mv_push,
    lemma_mv_add,
    lemma_mv_take,
    lemma_map_values_insert,
    lemma_map_values_remove,
    axiom_pset_seq,
}

#[verifier::external_body]
pub proof fn axiom_realised(d: DispatchV)
    ensures
        lift_dispatch(d)@ == d,
{
}

pub proof fn lemma_prec_ext(a: PromiseRecord, b: PromiseRecord)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_record_ext(a, b);
}

pub proof fn lemma_dispatch_ext(a: Dispatch, b: Dispatch)
    requires
        a@ == b@,
    ensures
        a == b,
{
    match (a, b) {
        (Dispatch::Execute { id: x, .. }, Dispatch::Execute { id: y, .. }) => axiom_string_ext(x, y),
        (Dispatch::Unblock { address: x, promise: p }, Dispatch::Unblock { address: y, promise: q }) => {
            axiom_string_ext(x, y);
            lemma_prec_ext(p, q);
        },
        _ => {},
    }
}

pub proof fn lemma_lift_dispatch(d: Dispatch)
    ensures
        lift_dispatch(d@) == d,
{
    axiom_realised(d@);
    lemma_dispatch_ext(lift_dispatch(d@), d);
}



pub proof fn lemma_before_irrefl(a: Seq<char>)
    ensures
        !spec_before(a, a),
    decreases a.len(),
{
    if a.len() == 0 {
    } else {
        lemma_before_irrefl(a.drop_first());
    }
}

pub proof fn lemma_before_trans(a: Seq<char>, b: Seq<char>, c: Seq<char>)
    requires
        spec_before(a, b),
        spec_before(b, c),
    ensures
        spec_before(a, c),
    decreases a.len() + b.len() + c.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if c.len() == 0 {
    } else if a[0] != b[0] {
    } else if b[0] != c[0] {
    } else {
        lemma_before_trans(a.drop_first(), b.drop_first(), c.drop_first());
    }
}

pub proof fn lemma_least_exists(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        exists|k: Seq<char>| least(keys, k),
    decreases keys.len(),
{
    let x = keys.choose();
    assert(keys.contains(x));
    let rest = keys.remove(x);
    assert(rest.len() == keys.len() - 1);
    if rest.len() == 0 {
        assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, x) by {
            if o != x {
                assert(rest.contains(o));
            } else {
                lemma_before_irrefl(x);
            }
        };
        assert(least(keys, x));
    } else {
        lemma_least_exists(rest);
        let m = choose|m: Seq<char>| least(rest, m);
        assert(keys.contains(m));
        if spec_before(x, m) {
            assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, x) by {
                if o == x {
                    lemma_before_irrefl(x);
                } else {
                    assert(rest.contains(o));
                    if spec_before(o, x) {
                        lemma_before_trans(o, x, m);
                    }
                }
            };
            assert(least(keys, x));
        } else {
            assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, m) by {
                if o != x {
                    assert(rest.contains(o));
                }
            };
            assert(least(keys, m));
        }
    }
}

pub proof fn lemma_min_key(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        keys.contains(spec_min_key(keys)),
{
    reveal(spec_min_key);
    lemma_least_exists(keys);
    let k = choose|k: Seq<char>| least(keys, k);
    assert(keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k));
}

pub proof fn lemma_schedule_ext(a: Schedule, b: Schedule)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_string_ext(a.id, b.id);
    axiom_string_ext(a.cron, b.cron);
    axiom_string_ext(a.promise_id, b.promise_id);
    lemma_value_ext(a.promise_param, b.promise_param);
    lemma_tags_ext(a.promise_tags, b.promise_tags);
}

pub proof fn lemma_schedule_value(c: Schedule)
    ensures
        spec_schedule_value(schedule_v(c)) == c,
{
    lemma_string_of(c.id);
    lemma_string_of(c.cron);
    lemma_string_of(c.promise_id);
}

pub proof fn lemma_string_of(s: String)
    ensures
        spec_string(s@) == s,
{
    reveal(spec_string);
    axiom_string_ext(spec_string(s@), s);
}

pub proof fn lemma_refs_one_origin(refs: Seq<TaskRef>, j: int)
    requires
        1 <= j,
    ensures
        spec_refs_one_origin(refs, j) <==> (forall|k: int| j <= k < refs.len() ==> origin(#[trigger] refs[k].id@) == origin(refs[0].id@)),
    decreases refs.len() - j,
{
    if j < refs.len() {
        lemma_refs_one_origin(refs, j + 1);
    }
}

pub proof fn lemma_losses_map(before: Proc, call: Call, outcomes: Seq<OutV>)
    ensures
        spec_losses(before, call, outcomes) == outcomes.map_values(|o: OutV| spec_lose(before, call, o)),
    decreases outcomes.len(),
{
    if outcomes.len() == 0 {
        assert(spec_losses(before, call, outcomes) =~= outcomes.map_values(|o: OutV| spec_lose(before, call, o)));
    } else {
        lemma_losses_map(before, call, outcomes.skip(1));
        assert(spec_losses(before, call, outcomes) =~= outcomes.map_values(|o: OutV| spec_lose(before, call, o)));
    }
}

pub proof fn lemma_shed_is_last(
    config: Config,
    state: Proc,
    now: Time,
    call: Call,
)
    ensures
        ({
            let event = ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            };
            let outcomes = state.on_event(config, now, event);
            &&& outcomes.len() > 0
            &&& outcomes[outcomes.len() as int - 1] == spec_shed(state, call)
        }),
{
    let event = ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(call),
    };
    let outcomes = state.on_event(config, now, event);
    let served = spec_run(config, state, call, now);
    let lost = spec_losses(state, call, spec_handler(config, call.request, state.store, now));
    let shed = seq![spec_shed(state, call)];
    assert(outcomes == served + lost + shed);
    let prefix = served + lost;
    vstd::seq::lemma_seq_add_len(prefix, shed);
    vstd::seq::lemma_seq_push_len(Seq::<StepResultV<Proc, Pid, Message>>::empty(), spec_shed(state, call));
    assert(shed.len() == 1);
    let j = prefix.len() as int;
    vstd::seq::lemma_seq_add_index2(prefix, shed, j);
    vstd::seq::lemma_seq_push_index_same(
        Seq::<StepResultV<Proc, Pid, Message>>::empty(),
        spec_shed(state, call),
        0,
    );
    assert(shed[0] == spec_shed(state, call));
    assert(outcomes[j] == spec_shed(state, call));
    assert(j == outcomes.len() as int - 1);
}

pub proof fn lemma_empty_heartbeat_is_first(
    config: Config,
    state: Proc,
    now: Time,
    call: Call,
)
    requires
        match call.request {
            Request::TaskHeartbeat(q) => q.tasks@.len() == 0,
            _ => false,
        },
    ensures
        ({
            let event = ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            };
            let outcomes = state.on_event(config, now, event);
            &&& outcomes.len() > 0
            &&& outcomes[0].state == state
            &&& outcomes[0].send == spec_send(
                call,
                Response::Status(echod_types::StatusRes { status: 200 }),
                Seq::empty(),
            )
        }),
{
    let event = ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(call),
    };
    let outcomes = state.on_event(config, now, event);
    let handler = spec_handler(config, call.request, state.store, now);
    assert(handler.len() == 1);
    let outcome = handler[0];
    assert(outcome.resp == spec_status_res(200));
    assert(spec_status_res(200) == Response::Status(echod_types::StatusRes { status: 200 }));
    assert(outcome.work =~= Seq::empty());
    assert(outcome.send =~= Seq::empty());
    assert(outcome.next == state.store);
    let served = spec_run(config, state, call, now);
    assert(served.len() == 1);
    assert(served[0] == spec_request_outcome(state, call, outcome));
    assert(served[0].state == state);
    assert(served[0].send == spec_send(
        call,
        Response::Status(echod_types::StatusRes { status: 200 }),
        Seq::empty(),
    ));
    let lost = spec_losses(state, call, handler);
    let shed = seq![spec_shed(state, call)];
    assert(outcomes == served + lost + shed);
    vstd::seq::lemma_seq_add_index1(served, lost + shed, 0);
    assert(outcomes[0] == served[0]);
}

proof fn initial_state_properties()
    ensures
        state_properties(
            0,
            Proc {
                store: empty_store(),
                pending: Seq::empty(),
            },
        ),
{
    reveal(state_properties);
    reveal(well_formed_promise_created_at_lte_timeout_at);
    reveal(well_formed_promise_settled_at_lte_timeout_at);
    reveal(well_formed_promise_created_at_lte_settled_at);
    reveal(well_formed_promise_settled_at_iff_not_pending);
    reveal(well_formed_task_has_matching_promise);
    reveal(well_formed_store_object_ids_unique);
    reveal(well_formed_store_schedule_ids_unique);
}

proof fn lemma_empty_value_has_no_data(empty: Value)
    requires
        empty@ == echod_types::AValue::empty(),
    ensures
        spec_empty_value().data is None,
{
    assert(exists|value: Value| value@ == echod_types::AValue::empty()) by {
        assert(empty@ == echod_types::AValue::empty());
    }
    reveal(spec_empty_value);
    reveal(echod_types::Value::spec_empty);
    assert(spec_empty_value()@ == echod_types::AValue::empty());
    assert(echod_types::AValue::empty().data is None);
}

proof fn lemma_new_object_well_formed(
    timeout_at: Time,
    at: Time,
    now: Time,
    param: Value,
    tags: Tags,
    runnable: bool,
)
    requires
        at <= now,
        spec_empty_value().data is None,
    ensures
        ({
            let pair = spec_new_object(timeout_at, at, now, param, tags, runnable);
            let promise = pair.0;
            &&& well_formed_promise_created_at_lte_timeout_at_at(promise)
            &&& well_formed_promise_settled_at_lte_timeout_at_at(promise)
            &&& well_formed_promise_created_at_lte_settled_at_at(promise)
            &&& well_formed_promise_settled_at_iff_not_pending_at(promise)
            &&& well_formed_promise_pending_created_before_deadline_at(promise)
            &&& well_formed_promise_pending_has_no_value_at(promise)
            &&& well_formed_promise_deadline_settlement_has_no_value_at(promise)
            &&& well_formed_promise_timedout_is_server_owned_at(promise)
            &&& forall|id: Chars| well_formed_promise_awaiter_is_not_self_at(id, promise)
            &&& forall|id: Chars| well_formed_promise_callbacks_same_origin_at(id, promise)
            &&& well_formed_promise_created_at_lte_now_at(now, promise)
            &&& well_formed_promise_settled_at_lte_now_at(now, promise)
            &&& match pair.1 {
                Some(task) => {
                    &&& well_formed_task_acquired_iff_has_pid_at(task)
                    &&& well_formed_task_acquired_iff_has_ttl_at(task)
                    &&& well_formed_task_pending_iff_has_retry_timeout_at_at(task)
                    &&& well_formed_task_fulfilled_is_cleared_at(task)
                    &&& well_formed_task_suspended_is_cleared_at(task)
                    &&& well_formed_task_halted_is_cleared_at(task)
                    &&& well_formed_task_suspended_has_no_resumes_at(task)
                    &&& well_formed_task_resumes_unique_at(task)
                    &&& well_formed_task_acquired_version_positive_at(task)
                },
                None => true,
            }
        }),
{
    reveal(spec_new_object);
    reveal(spec_empty_value);
    reveal(echod_types::Value::spec_empty);
    reveal(well_formed_task_resumes_unique_at);
    reveal(distinct);
    let pair = spec_new_object(timeout_at, at, now, param, tags, runnable);
    let promise = pair.0;
    assert(spec_empty_value().data is None);
    assert(well_formed_promise_created_at_lte_timeout_at_at(promise));
    assert(well_formed_promise_settled_at_lte_timeout_at_at(promise));
    assert(well_formed_promise_created_at_lte_settled_at_at(promise));
    assert(well_formed_promise_settled_at_iff_not_pending_at(promise));
    assert(well_formed_promise_pending_created_before_deadline_at(promise));
    assert(well_formed_promise_pending_has_no_value_at(promise));
    assert(well_formed_promise_deadline_settlement_has_no_value_at(promise));
    assert(well_formed_promise_timedout_is_server_owned_at(promise));
    assert forall|id: Chars| well_formed_promise_awaiter_is_not_self_at(id, promise) by {};
    assert forall|id: Chars| well_formed_promise_callbacks_same_origin_at(id, promise) by {};
    assert(well_formed_promise_created_at_lte_now_at(now, promise));
    assert(well_formed_promise_settled_at_lte_now_at(now, promise));
    match spec_delay(tags) {
        Some(_) => {},
        None => {},
    }
    match pair.1 {
        Some(task) => {
            assert(well_formed_task_acquired_iff_has_pid_at(task));
            assert(well_formed_task_acquired_iff_has_ttl_at(task));
            assert(well_formed_task_pending_iff_has_retry_timeout_at_at(task));
            assert(well_formed_task_fulfilled_is_cleared_at(task));
            assert(well_formed_task_suspended_is_cleared_at(task));
            assert(well_formed_task_halted_is_cleared_at(task));
            assert(well_formed_task_suspended_has_no_resumes_at(task));
            assert(well_formed_task_resumes_unique_at(task));
            assert(well_formed_task_acquired_version_positive_at(task));
        },
        None => {},
    }
}

proof fn lemma_task_create_new_well_formed(
    pid: String,
    ttl: Time,
    req: PromiseCreateReq,
    now: Time,
)
    requires
        spec_empty_value().data is None,
    ensures
        ({
            let live = req.timeout_at > now;
            let promise = PromiseV {
                state: if live { echod_types::PromiseState::Pending } else {
                    echod_types::PromiseState::RejectedTimedout
                },
                value: spec_empty_value(),
                param: req.param,
                timeout_at: req.timeout_at,
                created_at: if live { now } else { req.timeout_at },
                settled_at: if live { None } else { Some(req.timeout_at) },
                tags: req.tags,
                callbacks: Set::empty(),
                listeners: Set::empty(),
            };
            let born = TaskV {
                state: echod_types::TaskState::Fulfilled,
                version: 0,
                pid: None,
                ttl: None,
                acquired_at: 0,
                retry_timeout_at: None,
                resumes: Seq::empty(),
            };
            let task = if live { spec_acquire(born, 1, pid@, ttl, now) } else { born };
            &&& well_formed_promise_created_at_lte_timeout_at_at(promise)
            &&& well_formed_promise_settled_at_lte_timeout_at_at(promise)
            &&& well_formed_promise_created_at_lte_settled_at_at(promise)
            &&& well_formed_promise_settled_at_iff_not_pending_at(promise)
            &&& well_formed_promise_pending_created_before_deadline_at(promise)
            &&& well_formed_promise_pending_has_no_value_at(promise)
            &&& well_formed_promise_deadline_settlement_has_no_value_at(promise)
            &&& well_formed_promise_timedout_is_server_owned_at(promise)
            &&& forall|id: Chars| well_formed_promise_awaiter_is_not_self_at(id, promise)
            &&& forall|id: Chars| well_formed_promise_callbacks_same_origin_at(id, promise)
            &&& well_formed_promise_created_at_lte_now_at(now, promise)
            &&& well_formed_promise_settled_at_lte_now_at(now, promise)
            &&& well_formed_task_acquired_iff_has_pid_at(task)
            &&& well_formed_task_acquired_iff_has_ttl_at(task)
            &&& well_formed_task_pending_iff_has_retry_timeout_at_at(task)
            &&& well_formed_task_fulfilled_is_cleared_at(task)
            &&& well_formed_task_suspended_is_cleared_at(task)
            &&& well_formed_task_halted_is_cleared_at(task)
            &&& well_formed_task_suspended_has_no_resumes_at(task)
            &&& well_formed_task_resumes_unique_at(task)
            &&& well_formed_task_acquired_version_positive_at(task)
        }),
{
    reveal(spec_empty_value);
    reveal(echod_types::Value::spec_empty);
    reveal(spec_acquire);
    reveal(well_formed_task_resumes_unique_at);
    reveal(distinct);
    let live = req.timeout_at > now;
    assert(spec_empty_value().data is None);
    let promise = PromiseV {
        state: if live { echod_types::PromiseState::Pending } else {
            echod_types::PromiseState::RejectedTimedout
        },
        value: spec_empty_value(),
        param: req.param,
        timeout_at: req.timeout_at,
        created_at: if live { now } else { req.timeout_at },
        settled_at: if live { None } else { Some(req.timeout_at) },
        tags: req.tags,
        callbacks: Set::empty(),
        listeners: Set::empty(),
    };
    let born = TaskV {
        state: echod_types::TaskState::Fulfilled,
        version: 0,
        pid: None,
        ttl: None,
        acquired_at: 0,
        retry_timeout_at: None,
        resumes: Seq::empty(),
    };
    let task = if live { spec_acquire(born, 1, pid@, ttl, now) } else { born };
    assert(well_formed_promise_created_at_lte_timeout_at_at(promise));
    assert(well_formed_promise_settled_at_lte_timeout_at_at(promise));
    assert(well_formed_promise_created_at_lte_settled_at_at(promise));
    assert(well_formed_promise_settled_at_iff_not_pending_at(promise));
    assert(well_formed_promise_pending_created_before_deadline_at(promise));
    assert(well_formed_promise_pending_has_no_value_at(promise));
    assert(well_formed_promise_deadline_settlement_has_no_value_at(promise));
    assert(well_formed_promise_timedout_is_server_owned_at(promise));
    assert forall|id: Chars| well_formed_promise_awaiter_is_not_self_at(id, promise) by {};
    assert forall|id: Chars| well_formed_promise_callbacks_same_origin_at(id, promise) by {};
    assert(well_formed_promise_created_at_lte_now_at(now, promise));
    assert(well_formed_promise_settled_at_lte_now_at(now, promise));
    assert(well_formed_task_acquired_iff_has_pid_at(task));
    assert(well_formed_task_acquired_iff_has_ttl_at(task));
    assert(well_formed_task_pending_iff_has_retry_timeout_at_at(task));
    assert(well_formed_task_fulfilled_is_cleared_at(task));
    assert(well_formed_task_suspended_is_cleared_at(task));
    assert(well_formed_task_halted_is_cleared_at(task));
    assert(well_formed_task_suspended_has_no_resumes_at(task));
    assert(well_formed_task_resumes_unique_at(task));
    assert(well_formed_task_acquired_version_positive_at(task));
}

spec fn same_task_except_acquired_at(old: TaskV, new: TaskV) -> bool {
    &&& old.state == new.state
    &&& old.version == new.version
    &&& old.pid == new.pid
    &&& old.ttl == new.ttl
    &&& old.retry_timeout_at == new.retry_timeout_at
    &&& old.resumes == new.resumes
}

spec fn task_maps_same_except_acquired_at(
    old: Map<Chars, TaskV>,
    new: Map<Chars, TaskV>,
) -> bool {
    &&& old.dom() == new.dom()
    &&& forall|id: Chars| old.contains_key(id) ==>
        same_task_except_acquired_at(old[id], new[id])
}

proof fn lemma_extend_from(
    store: StoreV,
    pid: Chars,
    refs: Seq<echod_types::TaskRef>,
    now: Time,
    i: int,
    tasks: Map<Chars, TaskV>,
)
    requires
        0 <= i,
        task_maps_same_except_acquired_at(store.tasks, tasks),
    ensures
        task_maps_same_except_acquired_at(
            store.tasks,
            spec_extend(store, pid, refs, now, i, tasks),
        ),
    decreases refs.len() - i,
{
    reveal(task_maps_same_except_acquired_at);
    reveal(same_task_except_acquired_at);
    if i < refs.len() {
        let id = refs[i].id@;
        let next = match spec_held(store, id, refs[i].version, now) {
            SpecHeld::Ok(task) if task.pid == Some(pid) => {
                tasks.insert(id, TaskV { acquired_at: now, ..task })
            },
            _ => tasks,
        };
        assert(task_maps_same_except_acquired_at(store.tasks, next)) by {
            match spec_held(store, id, refs[i].version, now) {
                SpecHeld::Ok(task) if task.pid == Some(pid) => {
                    assert(store.tasks.contains_key(id));
                    assert(task == store.tasks[id]);
                    assert(tasks.contains_key(id));
                    assert(next.dom() == tasks.dom());
                    assert(next.dom() == store.tasks.dom());
                    assert forall|key: Chars| store.tasks.contains_key(key) implies
                        same_task_except_acquired_at(store.tasks[key], next[key]) by {
                        if key == id {
                        } else {
                            assert(next[key] == tasks[key]);
                        }
                    }
                },
                _ => {},
            }
        }
        lemma_extend_from(store, pid, refs, now, i + 1, next);
    }
}

proof fn lemma_extend(
    store: StoreV,
    pid: Chars,
    refs: Seq<echod_types::TaskRef>,
    now: Time,
)
    ensures
        task_maps_same_except_acquired_at(
            store.tasks,
            spec_extend(store, pid, refs, now, 0, store.tasks),
        ),
{
    reveal(task_maps_same_except_acquired_at);
    reveal(same_task_except_acquired_at);
    lemma_extend_from(store, pid, refs, now, 0, store.tasks);
}

spec fn promises_extended_with_callback(
    old: Map<Chars, PromiseV>,
    new: Map<Chars, PromiseV>,
    awaiter: Chars,
) -> bool {
    &&& old.dom() == new.dom()
    &&& forall|id: Chars| old.contains_key(id) ==> {
        let a = old[id];
        let b = new[id];
        &&& a.state == b.state
        &&& a.value == b.value
        &&& a.param == b.param
        &&& a.timeout_at == b.timeout_at
        &&& a.created_at == b.created_at
        &&& a.settled_at == b.settled_at
        &&& a.tags == b.tags
        &&& a.listeners == b.listeners
        &&& a.callbacks.subset_of(b.callbacks)
        &&& forall|callback: Chars| b.callbacks.contains(callback)
            ==> a.callbacks.contains(callback) || callback == awaiter
        &&& b.callbacks.contains(awaiter) && !a.callbacks.contains(awaiter)
            ==> id != awaiter && origin(id) == origin(awaiter)
    }
}

proof fn lemma_callbacks_from(
    old: Map<Chars, PromiseV>,
    ids: Seq<Chars>,
    awaiter: Chars,
    i: int,
    promises: Map<Chars, PromiseV>,
)
    requires
        0 <= i,
        promises_extended_with_callback(old, promises, awaiter),
        forall|j: int| i <= j < ids.len() ==> promises.contains_key(#[trigger] ids[j]),
        forall|j: int| i <= j < ids.len() ==> #[trigger] ids[j] != awaiter,
        forall|j: int| i <= j < ids.len() ==> origin(#[trigger] ids[j]) == origin(awaiter),
    ensures
        promises_extended_with_callback(
            old,
            spec_callbacks(promises, ids, awaiter, i),
            awaiter,
        ),
    decreases ids.len() - i,
{
    reveal(promises_extended_with_callback);
    if i < ids.len() {
        let id = ids[i];
        let promise = promises[id];
        let updated = PromiseV {
            callbacks: promise.callbacks.insert(awaiter),
            ..promise
        };
        let next = promises.insert(id, updated);
        assert(promises_extended_with_callback(old, next, awaiter)) by {
            assert(promises.contains_key(id));
            assert(next.dom() == promises.dom());
            assert(next.dom() == old.dom());
            assert forall|key: Chars| old.contains_key(key) implies {
                let a = old[key];
                let b = next[key];
                &&& a.state == b.state
                &&& a.value == b.value
                &&& a.param == b.param
                &&& a.timeout_at == b.timeout_at
                &&& a.created_at == b.created_at
                &&& a.settled_at == b.settled_at
                &&& a.tags == b.tags
                &&& a.listeners == b.listeners
                &&& a.callbacks.subset_of(b.callbacks)
                &&& forall|callback: Chars| b.callbacks.contains(callback)
                    ==> a.callbacks.contains(callback) || callback == awaiter
                &&& b.callbacks.contains(awaiter) && !a.callbacks.contains(awaiter)
                    ==> key != awaiter && origin(key) == origin(awaiter)
            } by {
                if key == id {
                } else {
                    assert(next[key] == promises[key]);
                }
            }
        }
        lemma_callbacks_from(old, ids, awaiter, i + 1, next);
    }
}

proof fn lemma_callbacks(
    promises: Map<Chars, PromiseV>,
    ids: Seq<Chars>,
    awaiter: Chars,
)
    requires
        forall|j: int| 0 <= j < ids.len() ==> promises.contains_key(#[trigger] ids[j]),
        forall|j: int| 0 <= j < ids.len() ==> #[trigger] ids[j] != awaiter,
        forall|j: int| 0 <= j < ids.len() ==> origin(#[trigger] ids[j]) == origin(awaiter),
    ensures
        promises_extended_with_callback(
            promises,
            spec_callbacks(promises, ids, awaiter, 0),
            awaiter,
        ),
{
    reveal(promises_extended_with_callback);
    lemma_callbacks_from(promises, ids, awaiter, 0, promises);
}

proof fn lemma_handler_integrity(
    config: Config,
    request: Request,
    before: Proc,
    now: Time,
    i: int,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
        0 <= i < spec_handler(config, request, before.store, now).len(),
    ensures
        ({
            let outcome = spec_handler(config, request, before.store, now)[i];
            let after = Proc {
                store: outcome.next,
                pending: before.pending + outcome.work,
            };
            &&& state_properties(now, after)
            &&& transition_properties(now, before, after)
        }),
    decreases
        match request {
            Request::TaskFence(_) => 1nat,
            _ => 0nat,
        },
{
    let outcomes = spec_handler(config, request, before.store, now);
    let outcome = outcomes[i];
    let after = Proc {
        store: outcome.next,
        pending: before.pending + outcome.work,
    };
    reveal(state_properties);
    reveal(well_formed_promise_created_at_lte_timeout_at);
    reveal(well_formed_promise_settled_at_lte_timeout_at);
    reveal(well_formed_promise_created_at_lte_settled_at);
    reveal(well_formed_promise_settled_at_iff_not_pending);
    reveal(well_formed_task_has_matching_promise);
    reveal(well_formed_store_object_ids_unique);
    reveal(well_formed_store_schedule_ids_unique);
    reveal(transition_properties);
    reveal(monotone_promise_set_grows);
    reveal(monotone_task_set_grows);
    reveal(preserved_promise_birth_fields_immutable);
    reveal(preserved_schedule_birth_fields_immutable);
    reveal(preserved_promise_settlement_is_one_way);
    reveal(preserved_promise_state_frozen_once_settled);
    reveal(preserved_promise_value_until_settlement);
    reveal(monotone_task_version);
    reveal(monotone_promise_callbacks_while_pending);
    reveal(monotone_promise_listeners_while_pending);
    reveal(well_formed_task_resumes_unique_at);
    reveal(distinct);
    match request {
        Request::PromiseCreate(req) => {
            reveal(spec_promise_create);
            if !spec_is_timer(req.tags) || !spec_has_target(req.tags) {
                if !before.store.promises.contains_key(req.id@) {
                    lemma_new_object_well_formed(
                        req.timeout_at,
                        now,
                        now,
                        req.param,
                        req.tags,
                        spec_has_target(req.tags),
                    );
                }
            }
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::PromiseGet(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::PromiseSettle(req) => {
            reveal(spec_promise_settle);
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::PromiseRegisterCallback(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::PromiseRegisterListener(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskGet(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskCreate(req) => {
            reveal(spec_task_create);
            if spec_has_target(req.action.tags) && !spec_is_timer(req.action.tags)
                && !before.store.promises.contains_key(req.action.id@)
            {
                lemma_task_create_new_well_formed(req.pid, req.ttl, req.action, now);
            }
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskAcquire(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskRelease(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskFulfill(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskHeartbeat(req) => {
            lemma_extend(before.store, req.pid@, req.tasks@, now);
            reveal(task_maps_same_except_acquired_at);
            reveal(same_task_except_acquired_at);
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskSuspend(req) => {
            let ids = spec_awaited(req.actions@);
            let id = req.id@;
            if ids.len() != 0 && !ids.contains(id) && distinct(ids)
                && all_in_origin(ids, id)
            {
                match spec_held(before.store, id, req.version, now) {
                    SpecHeld::Ok(_) => {
                        if !(exists|j: int| 0 <= j < ids.len()
                            && !before.store.promises.contains_key(ids[j]))
                            && !(exists|j: int| 0 <= j < ids.len()
                                && !spec_external(before.store.promises[ids[j]]))
                            && !spec_any_settled(before.store, ids, now, 0)
                        {
                            assert forall|j: int| 0 <= j < ids.len() implies
                                before.store.promises.contains_key(#[trigger] ids[j]) by {};
                            assert forall|j: int| 0 <= j < ids.len() implies
                                #[trigger] ids[j] != id by {};
                            assert forall|j: int| 0 <= j < ids.len() implies
                                origin(#[trigger] ids[j]) == origin(id) by {};
                            lemma_callbacks(before.store.promises, ids, id);
                            reveal(promises_extended_with_callback);
                        }
                    },
                    _ => {},
                }
            }
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskFence(req) => {
            let id = req.id;
            let target = match req.action {
                echod_types::TaskFenceAction::Create(create) => create.id,
                echod_types::TaskFenceAction::Settle(settle) => settle.id,
            };
            if target@ != id@ && same_origin_spec(target@, id@) {
                match spec_held(before.store, id@, req.version, now) {
                    SpecHeld::Ok(_) => {
                        match req.action {
                            echod_types::TaskFenceAction::Create(create) => {
                                assert(spec_handler(
                                    config,
                                    Request::PromiseCreate(create),
                                    before.store,
                                    now,
                                ).len() > 0);
                                lemma_handler_integrity(
                                    config,
                                    Request::PromiseCreate(create),
                                    before,
                                    now,
                                    0,
                                );
                            },
                            echod_types::TaskFenceAction::Settle(settle) => {
                                assert(spec_handler(
                                    config,
                                    Request::PromiseSettle(settle),
                                    before.store,
                                    now,
                                ).len() > 0);
                                lemma_handler_integrity(
                                    config,
                                    Request::PromiseSettle(settle),
                                    before,
                                    now,
                                    0,
                                );
                            },
                        }
                    },
                    _ => {},
                }
            }
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskFenceCheck(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskHalt(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::TaskContinue(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::ScheduleCreate(req) => {
            if !spec_is_timer(req.promise_tags) || !spec_has_target(req.promise_tags) {
                if !before.store.schedules.contains_key(req.id@) {
                    axiom_next_cron_after(req.cron@, now);
                }
            }
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::ScheduleGet(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        Request::ScheduleDelete(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
    }
}

proof fn lemma_work_integrity(
    config: Config,
    work: InternalV,
    before: Proc,
    now: Time,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        ({
            let outcome = spec_process_work(config, work, before.store, now);
            let after = Proc {
                store: outcome.next,
                pending: before.pending + outcome.work,
            };
            &&& state_properties(now, after)
            &&& transition_properties(now, before, after)
        }),
{
    let outcome = spec_process_work(config, work, before.store, now);
    let after = Proc {
        store: outcome.next,
        pending: before.pending + outcome.work,
    };
    reveal(state_properties);
    reveal(well_formed_promise_created_at_lte_timeout_at);
    reveal(well_formed_promise_settled_at_lte_timeout_at);
    reveal(well_formed_promise_created_at_lte_settled_at);
    reveal(well_formed_promise_settled_at_iff_not_pending);
    reveal(well_formed_task_has_matching_promise);
    reveal(well_formed_store_object_ids_unique);
    reveal(well_formed_store_schedule_ids_unique);
    reveal(transition_properties);
    reveal(monotone_promise_set_grows);
    reveal(monotone_task_set_grows);
    reveal(preserved_promise_birth_fields_immutable);
    reveal(preserved_schedule_birth_fields_immutable);
    reveal(preserved_promise_settlement_is_one_way);
    reveal(preserved_promise_state_frozen_once_settled);
    reveal(preserved_promise_value_until_settlement);
    reveal(monotone_task_version);
    reveal(monotone_promise_callbacks_while_pending);
    reveal(monotone_promise_listeners_while_pending);
    reveal(well_formed_task_resumes_unique_at);
    reveal(distinct);
    match work {
        InternalV::PromiseTimeout(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        InternalV::Callback { .. } => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        InternalV::Listener { .. } => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        InternalV::TaskLeaseTimeout(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        InternalV::TaskRetryTimeout(_) => {
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        InternalV::ScheduleTimeout { id, .. } => {
            if before.store.schedules.contains_key(id)
                && before.store.schedules[id].next_run_at <= now
            {
                let schedule = before.store.schedules[id];
                axiom_next_cron_after(schedule.cron, schedule.next_run_at);
            }
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
        InternalV::Occurrence { at, timeout, param, tags, .. } => {
            if at <= now {
                lemma_new_object_well_formed(
                    sat_add(at, timeout),
                    at,
                    now,
                    param,
                    tags,
                    spec_has_target(tags) && !spec_is_timer(tags),
                );
            }
            assert(state_properties(now, after));
            assert(transition_properties(now, before, after));
        },
    }
}

spec fn result_integrity(
    now: Time,
    before: Proc,
    result: StepResultV<Proc, Pid, Message>,
) -> bool {
    state_properties(now, result.state)
        && transition_properties(now, before, result.state)
}

spec fn results_integrity(
    now: Time,
    before: Proc,
    results: Seq<StepResultV<Proc, Pid, Message>>,
) -> bool {
    forall|i: int| 0 <= i < results.len() ==>
        result_integrity(now, before, #[trigger] results[i])
}

proof fn lemma_concat_integrity(
    now: Time,
    before: Proc,
    left: Seq<StepResultV<Proc, Pid, Message>>,
    right: Seq<StepResultV<Proc, Pid, Message>>,
)
    requires
        results_integrity(now, before, left),
        results_integrity(now, before, right),
    ensures
        results_integrity(now, before, left + right),
{
    reveal(results_integrity);
    assert forall|i: int| 0 <= i < (left + right).len() implies
        result_integrity(now, before, #[trigger] (left + right)[i]) by {
        if i < left.len() {
            assert((left + right)[i] == left[i]);
        } else {
            assert((left + right)[i] == right[i - left.len()]);
        }
    }
}

proof fn lemma_unchanged_result_integrity(
    now: Time,
    before: Proc,
    result: StepResultV<Proc, Pid, Message>,
)
    requires
        state_properties(now, before),
        result.state == before,
    ensures
        result_integrity(now, before, result),
{
    reveal(result_integrity);
    reveal(transition_properties);
    reveal(monotone_promise_set_grows);
    reveal(monotone_task_set_grows);
    reveal(preserved_promise_birth_fields_immutable);
    reveal(preserved_schedule_birth_fields_immutable);
    reveal(preserved_promise_settlement_is_one_way);
    reveal(preserved_promise_state_frozen_once_settled);
    reveal(preserved_promise_value_until_settlement);
    reveal(monotone_task_version);
    reveal(monotone_promise_callbacks_while_pending);
    reveal(monotone_promise_listeners_while_pending);
}

proof fn lemma_run_integrity(
    config: Config,
    before: Proc,
    call: Call,
    now: Time,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        results_integrity(now, before, spec_run(config, before, call, now)),
{
    let handlers = spec_handler(config, call.request, before.store, now);
    let results = spec_run(config, before, call, now);
    reveal(results_integrity);
    assert forall|i: int| 0 <= i < results.len() implies
        result_integrity(now, before, #[trigger] results[i]) by {
        assert(results.len() == handlers.len());
        lemma_handler_integrity(config, call.request, before, now, i);
        assert(results[i] == spec_request_outcome(before, call, handlers[i]));
        reveal(result_integrity);
    }
}

proof fn lemma_losses_integrity(
    config: Config,
    before: Proc,
    call: Call,
    now: Time,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        results_integrity(
            now,
            before,
            spec_losses(
                before,
                call,
                spec_handler(config, call.request, before.store, now),
            ),
        ),
{
    let handlers = spec_handler(config, call.request, before.store, now);
    let results = spec_losses(before, call, handlers);
    lemma_losses_map(before, call, handlers);
    reveal(results_integrity);
    assert forall|i: int| 0 <= i < results.len() implies
        result_integrity(now, before, #[trigger] results[i]) by {
        assert(results.len() == handlers.len());
        lemma_handler_integrity(config, call.request, before, now, i);
        assert(results[i] == spec_lose(before, call, handlers[i]));
        reveal(result_integrity);
    }
}

proof fn lemma_work_due_result_integrity(
    config: Config,
    before: Proc,
    work: InternalV,
    now: Time,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        result_integrity(
            now,
            before,
            spec_due_result(
                before,
                spec_process_work(config, work, before.store, now),
            ),
        ),
{
    lemma_work_integrity(config, work, before, now);
    reveal(result_integrity);
}

proof fn lemma_work_internal_result_integrity(
    config: Config,
    before: Proc,
    work: InternalV,
    now: Time,
    i: int,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        result_integrity(
            now,
            before,
            spec_internal_result(
                before,
                i,
                spec_process_work(config, work, before.store, now),
            ),
        ),
{
    lemma_work_integrity(config, work, before, now);
    reveal(result_integrity);
}

proof fn lemma_keep_integrity(
    config: Config,
    before: Proc,
    now: Time,
    work: InternalV,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        results_integrity(
            now,
            before,
            spec_keep(config, before, now, work, Seq::empty()),
        ),
{
    let outcome = spec_process_work(config, work, before.store, now);
    if !outcome.not_due {
        lemma_work_due_result_integrity(config, before, work, now);
    }
    reveal(results_integrity);
}

proof fn lemma_queue_integrity(
    config: Config,
    before: Proc,
    now: Time,
    i: int,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
        0 <= i,
    ensures
        results_integrity(now, before, spec_queue(config, before, now, i)),
    decreases before.pending.len() - i,
{
    if i < before.pending.len() {
        let work = spec_body(before.pending[i]);
        let outcome = spec_process_work(config, work, before.store, now);
        let tail = spec_queue(config, before, now, i + 1);
        lemma_queue_integrity(config, before, now, i + 1);
        if spec_ready(work, now) && !outcome.not_due {
            lemma_work_internal_result_integrity(config, before, work, now, i);
            let head = seq![spec_internal_result(before, i, outcome)];
            reveal(results_integrity);
            assert(results_integrity(now, before, head));
            lemma_concat_integrity(now, before, head, tail);
        }
    }
    reveal(results_integrity);
}

proof fn lemma_over_callbacks_integrity(
    config: Config,
    before: Proc,
    now: Time,
    awaited: Chars,
    awaiters: Seq<Chars>,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        results_integrity(
            now,
            before,
            spec_over_callbacks(config, before, now, awaited, awaiters),
        ),
    decreases awaiters.len(),
{
    if awaiters.len() > 0 {
        let head = spec_keep(
            config,
            before,
            now,
            InternalV::Callback { awaited, awaiter: awaiters[0] },
            Seq::empty(),
        );
        let tail = spec_over_callbacks(
            config,
            before,
            now,
            awaited,
            awaiters.drop_first(),
        );
        lemma_keep_integrity(
            config,
            before,
            now,
            InternalV::Callback { awaited, awaiter: awaiters[0] },
        );
        lemma_over_callbacks_integrity(
            config,
            before,
            now,
            awaited,
            awaiters.drop_first(),
        );
        lemma_concat_integrity(now, before, head, tail);
    }
    reveal(results_integrity);
}

proof fn lemma_over_listeners_integrity(
    config: Config,
    before: Proc,
    now: Time,
    awaited: Chars,
    listeners: Seq<Chars>,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        results_integrity(
            now,
            before,
            spec_over_listeners(config, before, now, awaited, listeners),
        ),
    decreases listeners.len(),
{
    if listeners.len() > 0 {
        let head = spec_keep(
            config,
            before,
            now,
            InternalV::Listener { awaited, address: listeners[0] },
            Seq::empty(),
        );
        let tail = spec_over_listeners(
            config,
            before,
            now,
            awaited,
            listeners.drop_first(),
        );
        lemma_keep_integrity(
            config,
            before,
            now,
            InternalV::Listener { awaited, address: listeners[0] },
        );
        lemma_over_listeners_integrity(
            config,
            before,
            now,
            awaited,
            listeners.drop_first(),
        );
        lemma_concat_integrity(now, before, head, tail);
    }
    reveal(results_integrity);
}

proof fn lemma_spec_keys_are_keys<V>(map: Map<Chars, V>)
    ensures
        forall|i: int| 0 <= i < spec_keys(map).len() ==>
            map.contains_key(#[trigger] spec_keys(map)[i]),
    decreases map.dom().len(),
{
    let keys = map.dom();
    if keys.len() == 0 {
        assert(spec_keys(map) == Seq::<Chars>::empty());
    } else {
        lemma_min_key(keys);
        let key = spec_min_key(keys);
        let rest = keys.remove(key);
        let rest_map = Map::new(
            rest,
            |candidate: Chars| map[candidate],
        );
        assert(rest_map.dom() == rest);
        lemma_spec_keys_are_keys(rest_map);
        assert(spec_keys(map) == seq![key] + spec_sorted(rest));
        assert(spec_keys(rest_map) == spec_sorted(rest));
        assert forall|i: int| 0 <= i < spec_keys(map).len() implies
            map.contains_key(#[trigger] spec_keys(map)[i]) by {
            if i == 0 {
                assert(spec_keys(map)[0] == key);
            } else {
                assert(spec_keys(map)[i] == spec_keys(rest_map)[i - 1]);
                assert(rest_map.contains_key(spec_keys(rest_map)[i - 1]));
            }
        }
    }
}

proof fn lemma_over_promises_integrity(
    config: Config,
    before: Proc,
    now: Time,
    keys: Seq<Chars>,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
        forall|i: int| 0 <= i < keys.len() ==>
            before.store.promises.contains_key(#[trigger] keys[i]),
    ensures
        results_integrity(
            now,
            before,
            spec_over_promises(config, before, now, keys),
        ),
    decreases keys.len(),
{
    if keys.len() > 0 {
        let id = keys[0];
        let promise = before.store.promises[id];
        let timeouts = spec_keep(
            config,
            before,
            now,
            InternalV::PromiseTimeout(id),
            Seq::empty(),
        );
        let callbacks = spec_over_callbacks(
            config,
            before,
            now,
            id,
            super::axioms::pset_seq(promise.callbacks),
        );
        let listeners = spec_over_listeners(
            config,
            before,
            now,
            id,
            super::axioms::pset_seq(promise.listeners),
        );
        let tail_keys = keys.drop_first();
        let tail = spec_over_promises(config, before, now, tail_keys);
        assert forall|i: int| 0 <= i < tail_keys.len() implies
            before.store.promises.contains_key(#[trigger] tail_keys[i]) by {
            assert(tail_keys[i] == keys[i + 1]);
        }
        lemma_keep_integrity(
            config,
            before,
            now,
            InternalV::PromiseTimeout(id),
        );
        lemma_over_callbacks_integrity(
            config,
            before,
            now,
            id,
            super::axioms::pset_seq(promise.callbacks),
        );
        lemma_over_listeners_integrity(
            config,
            before,
            now,
            id,
            super::axioms::pset_seq(promise.listeners),
        );
        lemma_over_promises_integrity(config, before, now, tail_keys);
        lemma_concat_integrity(now, before, timeouts, callbacks);
        lemma_concat_integrity(now, before, timeouts + callbacks, listeners);
        lemma_concat_integrity(
            now,
            before,
            timeouts + callbacks + listeners,
            tail,
        );
    }
    reveal(results_integrity);
}

proof fn lemma_over_tasks_integrity(
    config: Config,
    before: Proc,
    now: Time,
    keys: Seq<Chars>,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
        forall|i: int| 0 <= i < keys.len() ==>
            before.store.tasks.contains_key(#[trigger] keys[i]),
    ensures
        results_integrity(
            now,
            before,
            spec_over_tasks(config, before, now, keys),
        ),
    decreases keys.len(),
{
    if keys.len() > 0 {
        let id = keys[0];
        let task = before.store.tasks[id];
        let lease = spec_keep(
            config,
            before,
            now,
            InternalV::TaskLeaseTimeout(id),
            Seq::empty(),
        );
        let retry = match task.retry_timeout_at {
            Some(_) => spec_keep(
                config,
                before,
                now,
                InternalV::TaskRetryTimeout(id),
                Seq::empty(),
            ),
            None => Seq::empty(),
        };
        let tail_keys = keys.drop_first();
        let tail = spec_over_tasks(config, before, now, tail_keys);
        assert forall|i: int| 0 <= i < tail_keys.len() implies
            before.store.tasks.contains_key(#[trigger] tail_keys[i]) by {
            assert(tail_keys[i] == keys[i + 1]);
        }
        lemma_keep_integrity(
            config,
            before,
            now,
            InternalV::TaskLeaseTimeout(id),
        );
        match task.retry_timeout_at {
            Some(_) => {
                lemma_keep_integrity(
                    config,
                    before,
                    now,
                    InternalV::TaskRetryTimeout(id),
                );
            },
            None => {
                reveal(results_integrity);
            },
        }
        lemma_over_tasks_integrity(config, before, now, tail_keys);
        lemma_concat_integrity(now, before, lease, retry);
        lemma_concat_integrity(now, before, lease + retry, tail);
    }
    reveal(results_integrity);
}

proof fn lemma_over_schedules_integrity(
    config: Config,
    before: Proc,
    now: Time,
    keys: Seq<Chars>,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
        forall|i: int| 0 <= i < keys.len() ==>
            before.store.schedules.contains_key(#[trigger] keys[i]),
    ensures
        results_integrity(
            now,
            before,
            spec_over_schedules(config, before, now, keys),
        ),
    decreases keys.len(),
{
    if keys.len() > 0 {
        let id = keys[0];
        let schedule = before.store.schedules[id];
        let work = InternalV::ScheduleTimeout {
            id,
            promise: echod_types::common::spec_expand(
                schedule.promise_id,
                id,
                schedule.next_run_at,
            ),
        };
        let head = spec_keep(config, before, now, work, Seq::empty());
        let tail_keys = keys.drop_first();
        let tail = spec_over_schedules(config, before, now, tail_keys);
        assert forall|i: int| 0 <= i < tail_keys.len() implies
            before.store.schedules.contains_key(#[trigger] tail_keys[i]) by {
            assert(tail_keys[i] == keys[i + 1]);
        }
        lemma_keep_integrity(config, before, now, work);
        lemma_over_schedules_integrity(config, before, now, tail_keys);
        lemma_concat_integrity(now, before, head, tail);
    }
    reveal(results_integrity);
}

proof fn lemma_derived_integrity(
    config: Config,
    before: Proc,
    now: Time,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        results_integrity(now, before, spec_derived(config, before, now)),
{
    let promise_keys = spec_keys(before.store.promises);
    let task_keys = spec_keys(before.store.tasks);
    let schedule_keys = spec_keys(before.store.schedules);
    lemma_spec_keys_are_keys(before.store.promises);
    lemma_spec_keys_are_keys(before.store.tasks);
    lemma_spec_keys_are_keys(before.store.schedules);
    lemma_over_promises_integrity(config, before, now, promise_keys);
    lemma_over_tasks_integrity(config, before, now, task_keys);
    lemma_over_schedules_integrity(config, before, now, schedule_keys);
    let promises = spec_over_promises(config, before, now, promise_keys);
    let tasks = spec_over_tasks(config, before, now, task_keys);
    let schedules = spec_over_schedules(config, before, now, schedule_keys);
    lemma_concat_integrity(now, before, promises, tasks);
    lemma_concat_integrity(now, before, promises + tasks, schedules);
}

proof fn lemma_run_timeout_integrity(
    config: Config,
    before: Proc,
    now: Time,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        results_integrity(now, before, spec_run_timeout(config, before, now)),
{
    let queued = spec_queue(config, before, now, 0);
    let derived = spec_derived(config, before, now);
    lemma_queue_integrity(config, before, now, 0);
    lemma_derived_integrity(config, before, now);
    lemma_concat_integrity(now, before, queued, derived);
}

proof fn lemma_request_service_integrity(
    config: Config,
    before: Proc,
    call: Call,
    now: Time,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        results_integrity(
            now,
            before,
            spec_service(
                config,
                before,
                now,
                ProcessEvent::Receive {
                    sender: Pid::Outside,
                    message: Message::Request(call),
                },
            ),
        ),
{
    let served = spec_run(config, before, call, now);
    let lost = spec_losses(
        before,
        call,
        spec_handler(config, call.request, before.store, now),
    );
    let shed = seq![spec_shed(before, call)];
    lemma_run_integrity(config, before, call, now);
    lemma_losses_integrity(config, before, call, now);
    lemma_unchanged_result_integrity(now, before, spec_shed(before, call));
    reveal(results_integrity);
    assert(results_integrity(now, before, shed));
    lemma_concat_integrity(now, before, served, lost);
    lemma_concat_integrity(now, before, served + lost, shed);
}

proof fn lemma_service_integrity(
    config: Config,
    before: Proc,
    now: Time,
    event: ProcessEvent<Pid, Message>,
)
    requires
        state_properties(now, before),
        spec_empty_value().data is None,
    ensures
        results_integrity(
            now,
            before,
            spec_service(config, before, now, event),
        ),
{
    match event {
        ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(call),
        } => {
            lemma_request_service_integrity(config, before, call, now);
        },
        ProcessEvent::Timeout => {
            let results = spec_run_timeout(config, before, now);
            lemma_run_timeout_integrity(config, before, now);
            if results.len() == 0 {
                let idle = spec_idle(before);
                let result = idle[0];
                lemma_unchanged_result_integrity(now, before, result);
                reveal(results_integrity);
            }
        },
        _ => {
            let idle = spec_idle(before);
            let result = idle[0];
            lemma_unchanged_result_integrity(now, before, result);
            reveal(results_integrity);
        },
    }
}

proof fn property_proof_with_empty_value(config: Config)
    requires
        spec_empty_value().data is None,
    ensures
        property_claim(config),
{
    initial_state_properties();
    assert forall|before: Proc, now: Time, event: ProcessEvent<Pid, Message>, i: int|
        #![trigger before.on_event(config, now, event)[i]]
        state_properties(now, before)
        && 0 <= i
        && i < before.on_event(config, now, event).len()
        implies step_properties(
            now,
            before,
            event,
            before.on_event(config, now, event)[i],
        ) by {
        lemma_service_integrity(config, before, now, event);
        let results = before.on_event(config, now, event);
        assert(result_integrity(now, before, results[i]));
        reveal(result_integrity);
        reveal(step_properties);
    }
    reveal(property_claim);
}

pub fn property_proof(config: Config)
    ensures
        property_claim(config),
{
    let empty = Value::empty();
    proof {
        lemma_empty_value_has_no_data(empty);
        property_proof_with_empty_value(config);
    }
}
}
