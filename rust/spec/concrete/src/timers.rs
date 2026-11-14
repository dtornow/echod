//! Atomic workflow transitions and schedule occurrences agree.
//!
//! A workflow timeout offer represents one whole-origin transition. Schedule
//! occurrences remain independent and use `createPromiseAt` against
//! `spec_create_if_absent`. The module ends
//! in [`lemma_agreement`]: at the configuration the node implements, the
//! handlers, the due step, and the occurrence all agree. Cargo erases these
//! bodies; a Verus run is what checks them.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::handlers::{
    lemma_finite_at, lemma_promises_kept, lemma_skip_no_duplicates, lemma_tasks_kept,
    lemma_within_one,
};
#[cfg(verus_keep_ghost)]
use crate::interpret::{
    abstract_task, callbacks_in, changed_within, doc_rel, finite_store, lemma_contains_to_set,
    lemma_empty_to_set, lemma_offer, lemma_origin_doc, lemma_origin_reads, lemma_origin_update,
    lemma_others_kept_schedule, lemma_others_kept_within, lemma_project_object, lemma_record,
    lemma_sat_add, lemma_schedule_key, lemma_starts_split, lemma_targeted, lemma_timer, object_rel,
    origin_prefix, origin_rel, promise_rel, schedule_prefix, schedule_rel, slot_rel, task_rel,
};
#[cfg(verus_keep_ghost)]
use crate::model::spec_string as c_string;
#[cfg(verus_keep_ghost)]
use crate::node::{
    spec_due_transition, spec_min_key as c_min_key, spec_new_obj, spec_obj_due, spec_occurrence,
    spec_offer_at, spec_opened, spec_origin_key, spec_project_due_object, spec_project_keys,
    spec_project_obj, spec_record, spec_schedule_key, spec_sorted as c_sorted, spec_sorted_present,
    spec_sweep, spec_targeted, spec_timer, spec_unlease as c_unlease, spec_workflow_map,
    DocumentBodyV, NoteV, ObjV, PendingV, PromV, TkV,
};
#[cfg(verus_keep_ghost)]
use crate::relation::{
    agreement, as_item, due_agrees, dues_agree, items, note_sends, occurrence_agrees,
    occurrences_agree, spec_timeout_trace, timeout_trace_legal, TimeoutTraceV,
};
#[cfg(verus_keep_ghost)]
use crate::store::{spec_before as c_before, spec_sat_add, spec_starts};
#[cfg(verus_keep_ghost)]
use echod_abstract::machine::{
    spec_callback, spec_callback_apply, spec_create_if_absent, spec_did, spec_has_target,
    spec_is_timer, spec_lease, spec_lease_at, spec_listener, spec_new_object, spec_process_work,
    spec_project_promise, spec_project_task, spec_promise_record, spec_retry, spec_schedule_step,
    spec_string as a_string, spec_unlease as a_unlease,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::model::{
    spec_derived, spec_due_result, spec_keep, spec_over_callbacks, spec_over_listeners,
    spec_over_promises, spec_over_schedules, spec_over_tasks, spec_queue, spec_run_timeout,
    Pid as APid, StateV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::protocol::Message as AMessage;
#[cfg(verus_keep_ghost)]
use echod_abstract::trusted::{axiom_pset_seq, pset_seq, spec_expand, spec_next_cron};
#[cfg(verus_keep_ghost)]
use echod_abstract::view::{
    least as a_least, lemma_least_exists as a_lemma_least_exists, lemma_min_key as a_lemma_min_key,
    lift_dispatch, sat_add, spec_before as a_before, spec_keys, spec_min_key as a_min_key,
    spec_sorted as a_sorted, DispatchV, InOutV, InternalV, PromiseV, ScheduleV, StoreV as AStore,
    TaskV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::{Dispatch, Output, ServerConfig};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::StepResultV;
#[cfg(verus_keep_ghost)]
use echod_rover::{Sched, Time};
#[cfg(verus_keep_ghost)]
use echod_types::{origin, PromiseRecord, PromiseState, Request, Response, Schedule, TaskState, MAX_TIME};

verus! {

broadcast use
    vstd::seq::group_seq_lemmas,
    vstd::set::group_set_lemmas,
    echod_abstract::view::group_views;

/// One abstract step result.
#[cfg(verus_keep_ghost)]
pub type AResult = StepResultV<StateV, APid, AMessage>;

// ---------------------------------------------------------------------------
// The key order
// ---------------------------------------------------------------------------

/// The two copies of the order are one order.
pub proof fn lemma_before_same(a: Seq<char>, b: Seq<char>)
    ensures
        c_before(a, b) == a_before(a, b),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if a[0] != b[0] {
    } else {
        lemma_before_same(a.drop_first(), b.drop_first());
    }
}

/// The chosen minimums, both of them, are keys. The abstract order has a
/// least key; by [`lemma_before_same`] it is least in the concrete order too.
pub proof fn lemma_min_key(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        keys.contains(c_min_key(keys)),
        keys.contains(a_min_key(keys)),
{
    reveal(crate::node::spec_min_key);
    a_lemma_min_key(keys);
    a_lemma_least_exists(keys);
    let k = choose|k: Seq<char>| a_least(keys, k);
    assert forall|o: Seq<char>| keys.contains(o) implies !c_before(o, k) by {
        lemma_before_same(o, k);
    };
    assert(keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !c_before(o, k));
}

/// The concrete sorted keys are the keys.
pub proof fn lemma_c_sorted(keys: Set<Seq<char>>)
    requires
        keys.finite(),
    ensures
        c_sorted(keys).len() == keys.len(),
        forall|i: int| 0 <= i < keys.len() ==> keys.contains(#[trigger] c_sorted(keys)[i]),
        forall|id: Seq<char>| keys.contains(id) ==> c_sorted(keys).contains(id),
    decreases keys.len(),
{
    if keys.len() == 0 {
        assert(c_sorted(keys) == Seq::<Seq<char>>::empty());
    } else {
        lemma_min_key(keys);
        let k = c_min_key(keys);
        let rest = keys.remove(k);
        assert(rest.len() == keys.len() - 1);
        lemma_c_sorted(rest);
        let sorted = c_sorted(keys);
        assert(sorted == seq![k] + c_sorted(rest));
        assert forall|i: int| 0 <= i < keys.len() implies keys.contains(#[trigger] sorted[i]) by {
            if i > 0 {
                assert(sorted[i] == c_sorted(rest)[i - 1]);
            }
        };
        assert forall|id: Seq<char>| keys.contains(id) implies sorted.contains(id) by {
            if id == k {
                assert(sorted[0] == k);
            } else {
                assert(rest.contains(id));
                let j = choose|j: int| 0 <= j < c_sorted(rest).len() && c_sorted(rest)[j] == id;
                assert(sorted[j + 1] == id);
            }
        };
    }
}

/// The abstract sorted keys are the keys.
pub proof fn lemma_a_sorted(keys: Set<Seq<char>>)
    requires
        keys.finite(),
    ensures
        a_sorted(keys).len() == keys.len(),
        forall|i: int| 0 <= i < keys.len() ==> keys.contains(#[trigger] a_sorted(keys)[i]),
        forall|id: Seq<char>| keys.contains(id) ==> a_sorted(keys).contains(id),
    decreases keys.len(),
{
    if keys.len() == 0 {
        assert(a_sorted(keys) == Seq::<Seq<char>>::empty());
    } else {
        lemma_min_key(keys);
        let k = a_min_key(keys);
        let rest = keys.remove(k);
        assert(rest.len() == keys.len() - 1);
        lemma_a_sorted(rest);
        let sorted = a_sorted(keys);
        assert(sorted == seq![k] + a_sorted(rest));
        assert forall|i: int| 0 <= i < keys.len() implies keys.contains(#[trigger] sorted[i]) by {
            if i > 0 {
                assert(sorted[i] == a_sorted(rest)[i - 1]);
            }
        };
        assert forall|id: Seq<char>| keys.contains(id) implies sorted.contains(id) by {
            if id == k {
                assert(sorted[0] == k);
            } else {
                assert(rest.contains(id));
                let j = choose|j: int| 0 <= j < a_sorted(rest).len() && a_sorted(rest)[j] == id;
                assert(sorted[j + 1] == id);
            }
        };
    }
}

/// The sorted keys are the keys, on both sides.
pub proof fn lemma_sorted(keys: Set<Seq<char>>)
    requires
        keys.finite(),
    ensures
        c_sorted(keys).len() == keys.len(),
        a_sorted(keys).len() == keys.len(),
        forall|i: int| 0 <= i < keys.len() ==> keys.contains(#[trigger] c_sorted(keys)[i]),
        forall|i: int| 0 <= i < keys.len() ==> keys.contains(#[trigger] a_sorted(keys)[i]),
        forall|id: Seq<char>| keys.contains(id) ==> c_sorted(keys).contains(id),
        forall|id: Seq<char>| keys.contains(id) ==> a_sorted(keys).contains(id),
{
    lemma_c_sorted(keys);
    lemma_a_sorted(keys);
}

// ---------------------------------------------------------------------------
// Membership in the offers
// ---------------------------------------------------------------------------

/// The outcome of `work`, when due, is among `results`.
pub open spec fn offered(
    config: ServerConfig,
    state: StateV,
    now: Time,
    work: InternalV,
    results: Seq<AResult>,
) -> bool {
    let outcome = spec_process_work(config, work, state.store, now);
    !outcome.not_due ==> results.contains(spec_due_result(state, outcome))
}

/// A due schedule is represented by one exact abstract timeout result.
pub open spec fn schedule_due_exact(
    config: ServerConfig,
    key: Seq<char>,
    doc: DocumentBodyV,
    state: StateV,
    now: Time,
) -> bool {
    let (next, _, born, _) =
        spec_due_transition(doc, now, config.retry_timeout);
    let results = spec_run_timeout(config, state, now);
    exists|j: int|
        #![trigger results[j]]
        0 <= j < results.len()
            && results[j].state.pending
                == state.pending + items(born)
            && doc_rel(key, next, results[j].state.store)
            && crate::interpret::others_kept(
                key, state.store, results[j].state.store,
            )
            && finite_store(results[j].state.store)
}

pub proof fn lemma_contains_left<T>(a: Seq<T>, b: Seq<T>, x: T)
    requires
        a.contains(x),
    ensures
        (a + b).contains(x),
{
    let j = choose|j: int| 0 <= j < a.len() && a[j] == x;
    assert((a + b)[j] == x);
}

pub proof fn lemma_contains_right<T>(a: Seq<T>, b: Seq<T>, x: T)
    requires
        b.contains(x),
    ensures
        (a + b).contains(x),
{
    let j = choose|j: int| 0 <= j < b.len() && b[j] == x;
    assert((a + b)[a.len() + j] == x);
}

pub proof fn lemma_offered_left(
    config: ServerConfig,
    state: StateV,
    now: Time,
    work: InternalV,
    a: Seq<AResult>,
    b: Seq<AResult>,
)
    requires
        offered(config, state, now, work, a),
    ensures
        offered(config, state, now, work, a + b),
{
    let outcome = spec_process_work(config, work, state.store, now);
    if !outcome.not_due {
        lemma_contains_left(a, b, spec_due_result(state, outcome));
    }
}

pub proof fn lemma_offered_right(
    config: ServerConfig,
    state: StateV,
    now: Time,
    work: InternalV,
    a: Seq<AResult>,
    b: Seq<AResult>,
)
    requires
        offered(config, state, now, work, b),
    ensures
        offered(config, state, now, work, a + b),
{
    let outcome = spec_process_work(config, work, state.store, now);
    if !outcome.not_due {
        lemma_contains_right(a, b, spec_due_result(state, outcome));
    }
}

pub proof fn lemma_keep_offered(config: ServerConfig, state: StateV, now: Time, work: InternalV)
    ensures
        offered(config, state, now, work, spec_keep(config, state, now, work, Seq::empty())),
{
    let outcome = spec_process_work(config, work, state.store, now);
    if !outcome.not_due {
        let r = spec_due_result(state, outcome);
        let kept = spec_keep(config, state, now, work, Seq::empty());
        assert(kept == seq![r] + Seq::<AResult>::empty());
        assert(kept[0] == r);
    }
}

pub proof fn lemma_over_callbacks_offered(
    config: ServerConfig,
    state: StateV,
    now: Time,
    awaited: Seq<char>,
    callbacks: Seq<Seq<char>>,
    awaiter: Seq<char>,
)
    requires callbacks.contains(awaiter),
    ensures offered(
        config,
        state,
        now,
        InternalV::Callback { awaited, awaiter },
        spec_over_callbacks(
            config, state, now, awaited, callbacks,
        ),
    ),
    decreases callbacks.len(),
{
    let work = InternalV::Callback { awaited, awaiter };
    let first = spec_keep(
        config,
        state,
        now,
        InternalV::Callback {
            awaited,
            awaiter: callbacks[0],
        },
        Seq::empty(),
    );
    let rest = spec_over_callbacks(
        config, state, now, awaited, callbacks.drop_first(),
    );
    if callbacks[0] == awaiter {
        lemma_keep_offered(config, state, now, work);
        lemma_offered_left(config, state, now, work, first, rest);
    } else {
        let j = choose|j: int|
            0 <= j < callbacks.len() && callbacks[j] == awaiter;
        assert(callbacks.drop_first()[j - 1] == awaiter);
        lemma_over_callbacks_offered(
            config,
            state,
            now,
            awaited,
            callbacks.drop_first(),
            awaiter,
        );
        lemma_offered_right(
            config, state, now, work, first, rest,
        );
    }
}

pub proof fn lemma_over_listeners_offered(
    config: ServerConfig,
    state: StateV,
    now: Time,
    awaited: Seq<char>,
    listeners: Seq<Seq<char>>,
    address: Seq<char>,
)
    requires listeners.contains(address),
    ensures offered(
        config,
        state,
        now,
        InternalV::Listener { awaited, address },
        spec_over_listeners(
            config, state, now, awaited, listeners,
        ),
    ),
    decreases listeners.len(),
{
    let work = InternalV::Listener { awaited, address };
    let first = spec_keep(
        config,
        state,
        now,
        InternalV::Listener {
            awaited,
            address: listeners[0],
        },
        Seq::empty(),
    );
    let rest = spec_over_listeners(
        config, state, now, awaited, listeners.drop_first(),
    );
    if listeners[0] == address {
        lemma_keep_offered(config, state, now, work);
        lemma_offered_left(config, state, now, work, first, rest);
    } else {
        let j = choose|j: int|
            0 <= j < listeners.len() && listeners[j] == address;
        assert(listeners.drop_first()[j - 1] == address);
        lemma_over_listeners_offered(
            config,
            state,
            now,
            awaited,
            listeners.drop_first(),
            address,
        );
        lemma_offered_right(
            config, state, now, work, first, rest,
        );
    }
}

pub proof fn lemma_over_promises_work_offered(
    config: ServerConfig,
    state: StateV,
    now: Time,
    keys: Seq<Seq<char>>,
    work: InternalV,
)
    requires
        keys.len() > 0,
        forall|i: int| 0 <= i < keys.len() ==>
            state.store.promises.contains_key(
                #[trigger] keys[i],
            ),
        match work {
            InternalV::PromiseTimeout(id) => keys.contains(id),
            InternalV::Callback { awaited, awaiter } =>
                keys.contains(awaited)
                    && state.store.promises[awaited]
                        .callbacks.contains(awaiter),
            InternalV::Listener { awaited, address } =>
                keys.contains(awaited)
                    && state.store.promises[awaited]
                        .listeners.contains(address),
            _ => false,
        },
    ensures offered(
        config,
        state,
        now,
        work,
        spec_over_promises(config, state, now, keys),
    ),
    decreases keys.len(),
{
    let id = keys[0];
    let promise = state.store.promises[id];
    let timed = spec_keep(
        config,
        state,
        now,
        InternalV::PromiseTimeout(id),
        Seq::empty(),
    );
    let called = spec_over_callbacks(
        config,
        state,
        now,
        id,
        pset_seq(promise.callbacks),
    );
    let listened = spec_over_listeners(
        config,
        state,
        now,
        id,
        pset_seq(promise.listeners),
    );
    let rest = spec_over_promises(
        config, state, now, keys.drop_first(),
    );
    if match work {
        InternalV::PromiseTimeout(target) => target == id,
        InternalV::Callback { awaited, .. } => awaited == id,
        InternalV::Listener { awaited, .. } => awaited == id,
        _ => false,
    } {
        match work {
            InternalV::PromiseTimeout(_) => {
                lemma_keep_offered(config, state, now, work);
                lemma_offered_left(
                    config, state, now, work, timed, called,
                );
                lemma_offered_left(
                    config, state, now, work,
                    timed + called, listened,
                );
                lemma_offered_left(
                    config, state, now, work,
                    timed + called + listened, rest,
                );
            },
            InternalV::Callback { awaiter, .. } => {
                axiom_pset_seq(promise.callbacks);
                assert(pset_seq(promise.callbacks).contains(awaiter));
                lemma_over_callbacks_offered(
                    config,
                    state,
                    now,
                    id,
                    pset_seq(promise.callbacks),
                    awaiter,
                );
                lemma_offered_right(
                    config, state, now, work, timed, called,
                );
                lemma_offered_left(
                    config, state, now, work,
                    timed + called, listened,
                );
                lemma_offered_left(
                    config, state, now, work,
                    timed + called + listened, rest,
                );
            },
            InternalV::Listener { address, .. } => {
                axiom_pset_seq(promise.listeners);
                assert(pset_seq(promise.listeners).contains(address));
                lemma_over_listeners_offered(
                    config,
                    state,
                    now,
                    id,
                    pset_seq(promise.listeners),
                    address,
                );
                lemma_offered_right(
                    config, state, now, work,
                    timed + called, listened,
                );
                lemma_offered_left(
                    config, state, now, work,
                    timed + called + listened, rest,
                );
            },
            _ => {},
        }
    } else {
        match work {
            InternalV::PromiseTimeout(target) => {
                assert(target != id);
                lemma_contains_after_first(keys, target);
            },
            InternalV::Callback { awaited, .. }
            | InternalV::Listener { awaited, .. } => {
                assert(awaited != id);
                lemma_contains_after_first(keys, awaited);
            },
            _ => {},
        }
        assert forall|i: int|
            0 <= i < keys.drop_first().len() implies
                state.store.promises.contains_key(
                    #[trigger] keys.drop_first()[i],
                ) by {
            assert(keys.drop_first()[i] == keys[i + 1]);
        };
        lemma_over_promises_work_offered(
            config, state, now, keys.drop_first(), work,
        );
        lemma_offered_right(
            config,
            state,
            now,
            work,
            timed + called + listened,
            rest,
        );
    }
}

pub proof fn lemma_over_tasks_work_offered(
    config: ServerConfig,
    state: StateV,
    now: Time,
    keys: Seq<Seq<char>>,
    work: InternalV,
)
    requires
        keys.len() > 0,
        forall|i: int| 0 <= i < keys.len() ==>
            state.store.tasks.contains_key(#[trigger] keys[i]),
        match work {
            InternalV::TaskLeaseTimeout(id)
            | InternalV::TaskRetryTimeout(id) => keys.contains(id),
            _ => false,
        },
    ensures offered(
        config,
        state,
        now,
        work,
        spec_over_tasks(config, state, now, keys),
    ),
    decreases keys.len(),
{
    let id = keys[0];
    let task = state.store.tasks[id];
    let lease = spec_keep(
        config,
        state,
        now,
        InternalV::TaskLeaseTimeout(id),
        Seq::empty(),
    );
    let retry = match task.retry_timeout_at {
        Some(_) => spec_keep(
            config,
            state,
            now,
            InternalV::TaskRetryTimeout(id),
            Seq::empty(),
        ),
        None => Seq::empty(),
    };
    let rest =
        spec_over_tasks(config, state, now, keys.drop_first());
    if match work {
        InternalV::TaskLeaseTimeout(target)
        | InternalV::TaskRetryTimeout(target) => target == id,
        _ => false,
    } {
        match work {
            InternalV::TaskLeaseTimeout(_) => {
                lemma_keep_offered(config, state, now, work);
                lemma_offered_left(
                    config, state, now, work, lease, retry,
                );
                lemma_offered_left(
                    config, state, now, work,
                    lease + retry, rest,
                );
            },
            InternalV::TaskRetryTimeout(_) => {
                if !spec_process_work(
                    config, work, state.store, now,
                ).not_due {
                    assert(task.retry_timeout_at is Some);
                    lemma_keep_offered(config, state, now, work);
                    lemma_offered_right(
                        config, state, now, work, lease, retry,
                    );
                    lemma_offered_left(
                        config, state, now, work,
                        lease + retry, rest,
                    );
                }
            },
            _ => {},
        }
    } else {
        match work {
            InternalV::TaskLeaseTimeout(target)
            | InternalV::TaskRetryTimeout(target) => {
                assert(target != id);
                lemma_contains_after_first(keys, target);
            },
            _ => {},
        }
        assert forall|i: int|
            0 <= i < keys.drop_first().len() implies
                state.store.tasks.contains_key(
                    #[trigger] keys.drop_first()[i],
                ) by {
            assert(keys.drop_first()[i] == keys[i + 1]);
        };
        lemma_over_tasks_work_offered(
            config, state, now, keys.drop_first(), work,
        );
        lemma_offered_right(
            config, state, now, work, lease + retry, rest,
        );
    }
}

pub proof fn lemma_contains_after_first<A>(
    values: Seq<A>,
    value: A,
)
    requires
        values.len() > 0,
        values.contains(value),
        values[0] != value,
    ensures
        values.drop_first().contains(value),
{
    let i = choose|i: int|
        0 <= i < values.len() && values[i] == value;
    assert(i > 0);
    assert(values.drop_first()[i - 1] == value);
}

pub proof fn lemma_contains_add<A>(
    left: Seq<A>,
    right: Seq<A>,
    value: A,
)
    ensures
        (left + right).contains(value)
            == (left.contains(value) || right.contains(value)),
{
    if left.contains(value) {
        let i = choose|i: int|
            0 <= i < left.len() && left[i] == value;
        assert((left + right)[i] == value);
    }
    if right.contains(value) {
        let i = choose|i: int|
            0 <= i < right.len() && right[i] == value;
        assert((left + right)[left.len() + i] == value);
    }
    if (left + right).contains(value) {
        let i = choose|i: int|
            0 <= i < (left + right).len()
                && (left + right)[i] == value;
        if i < left.len() {
            assert(left[i] == value);
        } else {
            assert(right[i - left.len()] == value);
        }
    }
}

proof fn lemma_singleton_contains<A>(value: A)
    ensures
        seq![value].contains(value),
{
    assert(seq![value].len() == 1);
    assert(seq![value][0] == value);
    assert(exists|i: int|
        0 <= i < seq![value].len() && seq![value][i] == value) by {
        let i: int = 0;
        assert(0 <= i < seq![value].len());
        assert(seq![value][i] == value);
    }
}

/// The timeout work of a schedule.
pub open spec fn schedule_work(s: AStore, id: Seq<char>) -> InternalV {
    let c = s.schedules[id];
    InternalV::ScheduleTimeout { id, promise: spec_expand(c.promise_id, id, c.next_run_at) }
}

pub proof fn lemma_over_schedules_offered(
    config: ServerConfig,
    state: StateV,
    now: Time,
    keys: Seq<Seq<char>>,
    id: Seq<char>,
)
    requires
        keys.contains(id),
    ensures
        offered(
            config,
            state,
            now,
            schedule_work(state.store, id),
            spec_over_schedules(config, state, now, keys),
        ),
    decreases keys.len(),
{
    let head = keys[0];
    let first = spec_keep(config, state, now, schedule_work(state.store, head), Seq::empty());
    let rest = spec_over_schedules(config, state, now, keys.drop_first());
    assert(spec_over_schedules(config, state, now, keys) == first + rest);
    if head == id {
        lemma_keep_offered(config, state, now, schedule_work(state.store, id));
        lemma_offered_left(config, state, now, schedule_work(state.store, id), first, rest);
    } else {
        let j = choose|j: int| 0 <= j < keys.len() && keys[j] == id;
        assert(keys.drop_first()[j - 1] == id);
        lemma_over_schedules_offered(config, state, now, keys.drop_first(), id);
        lemma_offered_right(config, state, now, schedule_work(state.store, id), first, rest);
    }
}

/// `work` names objects the store holds, so the timeout step offers it.
pub open spec fn work_known(s: AStore, work: InternalV, now: Time) -> bool {
    match work {
        InternalV::PromiseTimeout(id) =>
            s.promises.contains_key(id),
        InternalV::Callback { awaited, awaiter } =>
            s.promises.contains_key(awaited)
                && s.promises[awaited].callbacks.contains(awaiter),
        InternalV::Listener { awaited, address } =>
            s.promises.contains_key(awaited)
                && s.promises[awaited].listeners.contains(address),
        InternalV::TaskLeaseTimeout(id)
        | InternalV::TaskRetryTimeout(id) =>
            s.tasks.contains_key(id),
        InternalV::ScheduleTimeout { id, promise } => s.schedules.contains_key(id)
            && work == schedule_work(s, id),
        InternalV::Occurrence { .. } => false,
    }
}

/// One offer, read off [`lemma_timeout_offered`]. The universal facts stay
/// inside this lemma.
pub proof fn lemma_work_offered(config: ServerConfig, state: StateV, now: Time, work: InternalV)
    requires
        finite_store(state.store),
        work_known(state.store, work, now),
    ensures
        offered(config, state, now, work, spec_run_timeout(config, state, now)),
{
    let s = state.store;
    let results = spec_run_timeout(config, state, now);
    let queued = spec_queue(config, state, now, 0);
    let op = spec_over_promises(
        config, state, now, spec_keys(s.promises),
    );
    let ot =
        spec_over_tasks(config, state, now, spec_keys(s.tasks));
    let os = spec_over_schedules(
        config, state, now, spec_keys(s.schedules),
    );
    assert(spec_derived(config, state, now) == op + ot + os);
    assert(results == queued + (op + ot + os));
    lemma_sorted(s.promises.dom());
    lemma_sorted(s.tasks.dom());
    lemma_sorted(s.schedules.dom());
    match work {
        InternalV::PromiseTimeout(id)
        | InternalV::Callback { awaited: id, .. }
        | InternalV::Listener { awaited: id, .. } => {
            assert(spec_keys(s.promises).contains(id));
            assert forall|i: int|
                0 <= i < spec_keys(s.promises).len() implies
                    s.promises.contains_key(
                        #[trigger] spec_keys(s.promises)[i],
                    ) by {
                lemma_sorted(s.promises.dom());
            };
            lemma_over_promises_work_offered(
                config, state, now, spec_keys(s.promises), work,
            );
            lemma_offered_left(
                config, state, now, work, op, ot,
            );
            lemma_offered_left(
                config, state, now, work, op + ot, os,
            );
            lemma_offered_right(
                config, state, now, work, queued, op + ot + os,
            );
        },
        InternalV::TaskLeaseTimeout(id)
        | InternalV::TaskRetryTimeout(id) => {
            assert(spec_keys(s.tasks).contains(id));
            assert forall|i: int|
                0 <= i < spec_keys(s.tasks).len() implies
                    s.tasks.contains_key(
                        #[trigger] spec_keys(s.tasks)[i],
                    ) by {
                lemma_sorted(s.tasks.dom());
            };
            lemma_over_tasks_work_offered(
                config, state, now, spec_keys(s.tasks), work,
            );
            lemma_offered_right(
                config, state, now, work, op, ot,
            );
            lemma_offered_left(
                config, state, now, work, op + ot, os,
            );
            lemma_offered_right(
                config, state, now, work, queued, op + ot + os,
            );
        },
        InternalV::ScheduleTimeout { id, promise } => {
            assert(spec_keys(s.schedules).contains(id));
            lemma_over_schedules_offered(
                config, state, now, spec_keys(s.schedules), id,
            );
            lemma_offered_right(
                config, state, now, work, op + ot, os,
            );
            lemma_offered_right(
                config, state, now, work, queued, op + ot + os,
            );
        },
        InternalV::Occurrence { .. } => {},
    }
}

pub proof fn lemma_timeout_trace_add(
    config: ServerConfig,
    state: StateV,
    now: Time,
    first: Seq<InternalV>,
    second: Seq<InternalV>,
)
    ensures
        ({
            let head =
                spec_timeout_trace(config, state, now, first);
            let tail = spec_timeout_trace(
                config, head.state, now, second,
            );
            &&& spec_timeout_trace(
                config, state, now, first + second,
            ) == TimeoutTraceV {
                state: tail.state,
                send: head.send + tail.send,
            }
            &&& timeout_trace_legal(
                config, state, now, first + second,
            ) == (
                timeout_trace_legal(
                    config, state, now, first,
                )
                && timeout_trace_legal(
                    config, head.state, now, second,
                )
            )
        }),
    decreases first.len(),
{
    reveal(spec_timeout_trace);
    reveal(timeout_trace_legal);
    if first.len() > 0 {
        assert((first + second)[0] == first[0]);
        assert((first + second).drop_first()
            =~= first.drop_first() + second);
        let outcome = spec_process_work(
            config, first[0], state.store, now,
        );
        if outcome.not_due {
            lemma_timeout_trace_add(
                config,
                state,
                now,
                first.drop_first(),
                second,
            );
            let rest = spec_timeout_trace(
                config,
                state,
                now,
                first.drop_first(),
            );
            let tail = spec_timeout_trace(
                config, rest.state, now, second,
            );
            let combined = spec_timeout_trace(
                config, state, now, first + second,
            );
            assert(combined.state == tail.state);
            assert(combined.send == rest.send + tail.send);
        } else {
            let result = spec_due_result(state, outcome);
            lemma_timeout_trace_add(
                config,
                result.state,
                now,
                first.drop_first(),
                second,
            );
            let rest = spec_timeout_trace(
                config,
                result.state,
                now,
                first.drop_first(),
            );
            let tail = spec_timeout_trace(
                config, rest.state, now, second,
            );
            let head = spec_timeout_trace(
                config, state, now, first,
            );
            let combined = spec_timeout_trace(
                config, state, now, first + second,
            );
            assert(head.state == rest.state);
            assert(head.send == result.send + rest.send);
            assert(combined.state == tail.state);
            assert(combined.send
                == result.send + (rest.send + tail.send));
            assert(result.send + (rest.send + tail.send)
                == (result.send + rest.send) + tail.send);
        }
    } else {
        assert(first =~= Seq::<InternalV>::empty());
        assert(first + second =~= second);
    }
}

pub proof fn lemma_one_timeout_legal(
    config: ServerConfig,
    state: StateV,
    now: Time,
    work: InternalV,
)
    requires
        finite_store(state.store),
        work_known(state.store, work, now),
    ensures
        timeout_trace_legal(
            config, state, now, seq![work],
        ),
{
    reveal(timeout_trace_legal);
    assert(seq![work].drop_first()
        =~= Seq::<InternalV>::empty());
    let outcome =
        spec_process_work(config, work, state.store, now);
    if !outcome.not_due {
        lemma_work_offered(config, state, now, work);
        reveal(offered);
        assert(spec_run_timeout(config, state, now).contains(
            spec_due_result(state, outcome),
        ));
        assert(timeout_trace_legal(
            config,
            spec_due_result(state, outcome).state,
            now,
            Seq::empty(),
        )) by {
            reveal(timeout_trace_legal);
        };
    } else {
        assert(timeout_trace_legal(
            config, state, now, Seq::empty(),
        )) by {
            reveal(timeout_trace_legal);
        };
    }
}

pub proof fn lemma_one_timeout_result(
    config: ServerConfig,
    state: StateV,
    now: Time,
    work: InternalV,
)
    ensures
        spec_timeout_trace(
            config, state, now, seq![work],
        ) == {
            let outcome =
                spec_process_work(config, work, state.store, now);
            if outcome.not_due {
                TimeoutTraceV {
                    state,
                    send: Seq::empty(),
                }
            } else {
                let result = spec_due_result(state, outcome);
                TimeoutTraceV {
                    state: result.state,
                    send: result.send,
                }
            }
        },
{
    reveal(spec_timeout_trace);
    assert(seq![work].drop_first()
        =~= Seq::<InternalV>::empty());
    let outcome =
        spec_process_work(config, work, state.store, now);
    if outcome.not_due {
        assert(spec_timeout_trace(
            config, state, now, Seq::empty(),
        ) == TimeoutTraceV {
            state,
            send: Seq::empty(),
        }) by {
            reveal(spec_timeout_trace);
        };
    } else {
        let result = spec_due_result(state, outcome);
        assert(spec_timeout_trace(
            config, result.state, now, Seq::empty(),
        ) == TimeoutTraceV {
            state: result.state,
            send: Seq::empty(),
        }) by {
            reveal(spec_timeout_trace);
        };
    }
}

pub proof fn lemma_not_due_timeout(
    config: ServerConfig,
    state: StateV,
    now: Time,
    work: InternalV,
)
    requires
        spec_process_work(
            config, work, state.store, now,
        ).not_due,
    ensures
        timeout_trace_legal(
            config, state, now, seq![work],
        ),
        spec_timeout_trace(
            config, state, now, seq![work],
        ) == (TimeoutTraceV {
            state,
            send: Seq::empty(),
        }),
{
    lemma_one_timeout_result(config, state, now, work);
    reveal(timeout_trace_legal);
    assert(seq![work].drop_first()
        =~= Seq::<InternalV>::empty());
    assert(timeout_trace_legal(
        config, state, now, Seq::empty(),
    )) by {
        reveal(timeout_trace_legal);
    };
}

pub open spec fn workflow_timeout_work(
    work: InternalV,
) -> bool {
    match work {
        InternalV::PromiseTimeout(_)
        | InternalV::Callback { .. }
        | InternalV::Listener { .. }
        | InternalV::TaskLeaseTimeout(_)
        | InternalV::TaskRetryTimeout(_) => true,
        _ => false,
    }
}

proof fn lemma_workflow_work_add(
    left: Seq<InternalV>,
    right: Seq<InternalV>,
)
    requires
        forall|i: int| 0 <= i < left.len() ==>
            workflow_timeout_work(#[trigger] left[i]),
        forall|i: int| 0 <= i < right.len() ==>
            workflow_timeout_work(#[trigger] right[i]),
    ensures
        forall|i: int| 0 <= i < (left + right).len() ==>
            workflow_timeout_work(#[trigger] (left + right)[i]),
{
    assert forall|i: int| 0 <= i < (left + right).len() implies
        workflow_timeout_work(#[trigger] (left + right)[i]) by {
        if i < left.len() {
            assert((left + right)[i] == left[i]);
        } else {
            assert((left + right)[i] == right[i - left.len()]);
        }
    };
}

pub proof fn lemma_workflow_trace_keeps_schedules(
    config: ServerConfig,
    state: StateV,
    now: Time,
    work: Seq<InternalV>,
)
    requires
        forall|i: int| 0 <= i < work.len() ==>
            workflow_timeout_work(#[trigger] work[i]),
    ensures
        spec_timeout_trace(config, state, now, work)
            .state.store.schedules
            == state.store.schedules,
    decreases work.len(),
{
    reveal(spec_timeout_trace);
    if work.len() > 0 {
        let outcome = spec_process_work(
            config, work[0], state.store, now,
        );
        assert(outcome.next.schedules
            == state.store.schedules);
        assert forall|i: int|
            0 <= i < work.drop_first().len() implies
                workflow_timeout_work(
                    #[trigger] work.drop_first()[i],
                ) by {
            assert(work.drop_first()[i] == work[i + 1]);
        };
        if outcome.not_due {
            lemma_workflow_trace_keeps_schedules(
                config,
                state,
                now,
                work.drop_first(),
            );
        } else {
            lemma_workflow_trace_keeps_schedules(
                config,
                spec_due_result(state, outcome).state,
                now,
                work.drop_first(),
            );
        }
    }
}

pub open spec fn spec_phase1_object_work(
    id: Seq<char>,
) -> Seq<InternalV> {
    seq![
        InternalV::PromiseTimeout(id),
        InternalV::TaskLeaseTimeout(id),
        InternalV::TaskRetryTimeout(id),
    ]
}

pub open spec fn spec_phase1_work(
    keys: Seq<Seq<char>>,
    count: nat,
) -> Seq<InternalV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        spec_phase1_work(keys, (count - 1) as nat)
            + spec_phase1_object_work(keys[count as int - 1])
    }
}

pub open spec fn spec_callback_work(
    map: Map<Seq<char>, ObjV>,
    awaited: Seq<char>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Seq<InternalV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior_map = crate::node::spec_drain_callbacks(
            map,
            awaited,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = spec_callback_work(
            map,
            awaited,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let awaiter =
            prior_map[awaited].promise.callbacks[0];
        let callback =
            seq![InternalV::Callback { awaited, awaiter }];
        if spec_callback_notes(prior_map, awaiter, now).len() > 0 {
            prior + callback.push(
                InternalV::TaskRetryTimeout(awaiter),
            )
        } else {
            prior + callback
        }
    }
}

pub open spec fn spec_listener_work(
    awaited: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
) -> Seq<InternalV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        spec_listener_work(
            awaited, listeners, (count - 1) as nat,
        ).push(InternalV::Listener {
            awaited,
            address: listeners[count as int - 1],
        })
    }
}

pub open spec fn spec_callback_object_work(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: Time,
    retry_timeout: u64,
) -> Seq<InternalV> {
    if !map.contains_key(id)
        || map[id].promise.state == PromiseState::Pending
    {
        Seq::empty()
    } else {
        spec_callback_work(
            map,
            id,
            map[id].promise.callbacks.len(),
            now,
            retry_timeout,
        )
    }
}

pub open spec fn spec_callback_keys_work(
    projected: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Seq<InternalV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior_map = crate::node::spec_drain_callback_keys(
            projected,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        spec_callback_keys_work(
            projected,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        ) + spec_callback_object_work(
            prior_map,
            keys[count as int - 1],
            now,
            retry_timeout,
        )
    }
}

pub open spec fn spec_listener_object_work(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
) -> Seq<InternalV> {
    if !map.contains_key(id)
        || map[id].promise.state == PromiseState::Pending
    {
        Seq::empty()
    } else {
        spec_listener_work(
            id,
            map[id].promise.listeners,
            map[id].promise.listeners.len(),
        )
    }
}

pub open spec fn spec_listener_keys_work(
    resumed: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
) -> Seq<InternalV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = crate::node::spec_clear_listener_keys(
            resumed, keys, (count - 1) as nat,
        );
        spec_listener_keys_work(
            resumed, keys, (count - 1) as nat,
        ) + spec_listener_object_work(
            prior, keys[count as int - 1],
        )
    }
}

pub open spec fn spec_phase2_work(
    projected: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Seq<InternalV> {
    let resumed = crate::node::spec_drain_callback_keys(
        projected, keys, count, now, retry_timeout,
    );
    spec_callback_keys_work(
        projected, keys, count, now, retry_timeout,
    ) + spec_listener_keys_work(resumed, keys, count)
}

pub proof fn lemma_phase1_work_is_workflow(
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires count <= keys.len(),
    ensures
        forall|i: int|
            0 <= i < spec_phase1_work(keys, count).len() ==>
                workflow_timeout_work(
                    #[trigger] spec_phase1_work(keys, count)[i],
                ),
    decreases count,
{
    if count > 0 {
        lemma_phase1_work_is_workflow(
            keys, (count - 1) as nat,
        );
        let prior =
            spec_phase1_work(keys, (count - 1) as nat);
        let object_work =
            spec_phase1_object_work(keys[count as int - 1]);
        assert forall|i: int| 0 <= i < object_work.len() implies
            workflow_timeout_work(#[trigger] object_work[i]) by {
        };
        lemma_workflow_work_add(prior, object_work);
    }
}

pub proof fn lemma_callback_work_is_workflow(
    map: Map<Seq<char>, ObjV>,
    awaited: Seq<char>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        map.contains_key(awaited),
        count <= map[awaited].promise.callbacks.len(),
    ensures
        forall|i: int|
            0 <= i < spec_callback_work(
                map, awaited, count, now, retry_timeout,
            ).len() ==> workflow_timeout_work(
                #[trigger] spec_callback_work(
                    map, awaited, count, now, retry_timeout,
                )[i],
            ),
    decreases count,
{
    if count > 0 {
        lemma_callback_work_is_workflow(
            map,
            awaited,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = spec_callback_work(
            map,
            awaited,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior_map = crate::node::spec_drain_callbacks(
            map,
            awaited,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let awaiter =
            prior_map[awaited].promise.callbacks[0];
        let callback =
            seq![InternalV::Callback { awaited, awaiter }];
        let next = if spec_callback_notes(
            prior_map, awaiter, now,
        ).len() > 0 {
            callback.push(InternalV::TaskRetryTimeout(awaiter))
        } else {
            callback
        };
        assert forall|i: int| 0 <= i < next.len() implies
            workflow_timeout_work(#[trigger] next[i]) by {
        };
        lemma_workflow_work_add(prior, next);
    }
}

pub proof fn lemma_listener_work_is_workflow(
    awaited: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
)
    requires count <= listeners.len(),
    ensures
        forall|i: int|
            0 <= i < spec_listener_work(
                awaited, listeners, count,
            ).len() ==> workflow_timeout_work(
                #[trigger] spec_listener_work(
                    awaited, listeners, count,
                )[i],
            ),
    decreases count,
{
    if count > 0 {
        lemma_listener_work_is_workflow(
            awaited, listeners, (count - 1) as nat,
        );
        let prior = spec_listener_work(
            awaited, listeners, (count - 1) as nat,
        );
        let next = seq![InternalV::Listener {
            awaited,
            address: listeners[count as int - 1],
        }];
        assert forall|i: int| 0 <= i < next.len() implies
            workflow_timeout_work(#[trigger] next[i]) by {
        };
        lemma_workflow_work_add(prior, next);
        assert(prior + next
            =~= prior.push(InternalV::Listener {
                awaited,
                address: listeners[count as int - 1],
            }));
    }
}

pub proof fn lemma_callback_keys_work_is_workflow(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
        forall|i: int| 0 <= i < count ==>
            map.contains_key(#[trigger] keys[i]),
    ensures
        forall|i: int|
            0 <= i < spec_callback_keys_work(
                map, keys, count, now, retry_timeout,
            ).len() ==> workflow_timeout_work(
                #[trigger] spec_callback_keys_work(
                    map, keys, count, now, retry_timeout,
                )[i],
            ),
    decreases count,
{
    if count > 0 {
        lemma_callback_keys_work_is_workflow(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_drain_callback_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let id = keys[count as int - 1];
        if prior.contains_key(id)
            && prior[id].promise.state
                != PromiseState::Pending
        {
            lemma_callback_work_is_workflow(
                prior,
                id,
                prior[id].promise.callbacks.len(),
                now,
                retry_timeout,
            );
        }
        let old_work = spec_callback_keys_work(
            map, keys, (count - 1) as nat, now, retry_timeout,
        );
        let object_work =
            spec_callback_object_work(
                prior, id, now, retry_timeout,
            );
        assert forall|i: int| 0 <= i < object_work.len() implies
            workflow_timeout_work(#[trigger] object_work[i]) by {
        };
        lemma_workflow_work_add(old_work, object_work);
    }
}

pub proof fn lemma_listener_keys_work_is_workflow(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= keys.len(),
        forall|i: int| 0 <= i < count ==>
            map.contains_key(#[trigger] keys[i]),
    ensures
        forall|i: int|
            0 <= i < spec_listener_keys_work(
                map, keys, count,
            ).len() ==> workflow_timeout_work(
                #[trigger] spec_listener_keys_work(
                    map, keys, count,
                )[i],
            ),
    decreases count,
{
    if count > 0 {
        lemma_listener_keys_work_is_workflow(
            map, keys, (count - 1) as nat,
        );
        let prior = crate::node::spec_clear_listener_keys(
            map, keys, (count - 1) as nat,
        );
        let id = keys[count as int - 1];
        if prior.contains_key(id)
            && prior[id].promise.state
                != PromiseState::Pending
        {
            lemma_listener_work_is_workflow(
                id,
                prior[id].promise.listeners,
                prior[id].promise.listeners.len(),
            );
        }
        let old_work = spec_listener_keys_work(
            map, keys, (count - 1) as nat,
        );
        let object_work =
            spec_listener_object_work(prior, id);
        assert forall|i: int| 0 <= i < object_work.len() implies
            workflow_timeout_work(#[trigger] object_work[i]) by {
        };
        lemma_workflow_work_add(old_work, object_work);
    }
}

// ---------------------------------------------------------------------------
// Dispatches and sends
// ---------------------------------------------------------------------------

/// A lifted execute is the execute of the string.
pub proof fn lemma_lift_execute(id: Seq<char>, version: u64)
    ensures
        lift_dispatch(DispatchV::Execute { id, version }) == (Dispatch::Execute { id: c_string(id), version }),
{
    crate::interpret::lemma_string_same(id);
    reveal(lift_dispatch);
}

/// A lifted unblock is the unblock of the string.
pub proof fn lemma_lift_unblock(address: Seq<char>, promise: PromiseRecord)
    ensures
        lift_dispatch(DispatchV::Unblock { address, promise }) == (Dispatch::Unblock {
            address: c_string(address),
            promise,
        }),
{
    crate::interpret::lemma_string_same(address);
    reveal(lift_dispatch);
}

/// The sends of a due result, from its dispatches.
pub open spec fn sends_of(send: Seq<DispatchV>) -> Seq<(APid, AMessage)> {
    send.map_values(|dispatch: DispatchV| (
        APid::Outside,
        AMessage::Output(Output::Dispatch(lift_dispatch(dispatch))),
    ))
}

/// A due result sends the lift of each dispatch.
pub proof fn lemma_sends_of(state: StateV, outcome: InOutV)
    ensures
        spec_due_result(state, outcome).send == sends_of(outcome.send),
{
    let a = spec_due_result(state, outcome).send;
    let b = sends_of(outcome.send);
    assert(a.len() == b.len());
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        assert(a[i] == (
            APid::Outside,
            AMessage::Output(Output::Dispatch(lift_dispatch(outcome.send[i]))),
        ));
        assert(b[i] == (
            APid::Outside,
            AMessage::Output(Output::Dispatch(lift_dispatch(outcome.send[i]))),
        ));
    };
    assert(a =~= b);
}

pub proof fn lemma_sends_none()
    ensures
        sends_of(Seq::empty()) == note_sends(Seq::empty()),
{
    assert(sends_of(Seq::empty()) =~= note_sends(Seq::empty()));
}

pub proof fn lemma_sends_execute(id: Seq<char>, version: u64)
    ensures
        sends_of(seq![DispatchV::Execute { id, version }]) == note_sends(seq![NoteV::Execute { id, version }]),
{
    lemma_lift_execute(id, version);
    let a = sends_of(seq![DispatchV::Execute { id, version }]);
    let b = note_sends(seq![NoteV::Execute { id, version }]);
    assert(a.len() == 1);
    assert(b.len() == 1);
    assert(a[0] == b[0]);
    assert(a =~= b);
}

pub proof fn lemma_sends_unblock(address: Seq<char>, promise: PromiseRecord)
    ensures
        sends_of(seq![DispatchV::Unblock { address, promise }]) == note_sends(
            seq![NoteV::Unblock { address, promise }],
        ),
{
    lemma_lift_unblock(address, promise);
    let a = sends_of(seq![DispatchV::Unblock { address, promise }]);
    let b = note_sends(seq![NoteV::Unblock { address, promise }]);
    assert(a.len() == 1);
    assert(b.len() == 1);
    assert(a[0] == b[0]);
    assert(a =~= b);
}

// ---------------------------------------------------------------------------
// Atomic workflow trace alignment
// ---------------------------------------------------------------------------

pub proof fn lemma_one_changed(
    map: Map<Seq<char>, ObjV>,
    origin_chars: Seq<char>,
    store: AStore,
    id: Seq<char>,
    object: ObjV,
    promise: PromiseV,
    task: Option<TaskV>,
    next: AStore,
)
    requires
        map.dom().finite(),
        origin_rel(map, origin_chars, store),
        finite_store(store),
        origin(id) == origin_chars,
        object_rel(object, promise, task),
        callbacks_in(object.promise.callbacks, origin_chars),
        next.promises == store.promises.insert(id, promise),
        next.tasks == match task {
            Some(value) => store.tasks.insert(id, value),
            None => store.tasks.remove(id),
        },
        next.schedules == store.schedules,
    ensures
        map.insert(id, object).dom().finite(),
        origin_rel(
            map.insert(id, object), origin_chars, next,
        ),
        changed_within(store, next, origin_chars),
        finite_store(next),
{
    lemma_origin_update(
        map,
        origin_chars,
        store,
        id,
        object,
        promise,
        task,
        next,
    );
    assert(map.insert(id, object).dom()
        == map.dom().insert(id));
    crate::handlers::lemma_within_one(store, next, id);
    assert(next.promises.dom()
        == store.promises.dom().insert(id));
    match task {
        Some(_) => {
            assert(next.tasks.dom()
                == store.tasks.dom().insert(id));
        },
        None => {
            assert(next.tasks.dom()
                == store.tasks.dom().remove(id));
        },
    }
}

pub proof fn lemma_within_two(
    store: AStore,
    next: AStore,
    first: Seq<char>,
    second: Seq<char>,
)
    requires
        origin(second) == origin(first),
        forall|other: Seq<char>|
            other != first && other != second ==>
                #[trigger] next.promises.contains_key(other)
                    == store.promises.contains_key(other)
                && (store.promises.contains_key(other) ==>
                    next.promises[other]
                        == store.promises[other]),
        forall|other: Seq<char>|
            other != first && other != second ==>
                #[trigger] next.tasks.contains_key(other)
                    == store.tasks.contains_key(other)
                && (store.tasks.contains_key(other) ==>
                    next.tasks[other] == store.tasks[other]),
    ensures
        changed_within(store, next, origin(first)),
{
    assert forall|other: Seq<char>|
        #![trigger origin(other)]
        origin(other) != origin(first) implies {
            &&& store.promises.contains_key(other)
                == next.promises.contains_key(other)
            &&& (store.promises.contains_key(other) ==>
                store.promises[other] == next.promises[other])
            &&& store.tasks.contains_key(other)
                == next.tasks.contains_key(other)
            &&& (store.tasks.contains_key(other) ==>
                store.tasks[other] == next.tasks[other])
        } by {
        assert(other != first);
        assert(other != second);
    };
}

pub open spec fn spec_phase1_object_notes(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: Time,
) -> Seq<NoteV> {
    if !map.contains_key(id) {
        Seq::empty()
    } else {
        let object = map[id];
        if object.promise.state == PromiseState::Pending
            && object.promise.timeout_at > now
        {
            match object.task {
                Some(task) if task.state == TaskState::Acquired
                    && match task.lease_timeout_at {
                        Some(at) => at <= now,
                        None => false,
                    } => seq![NoteV::Execute {
                        id,
                        version: task.version,
                    }],
                Some(task) if task.state == TaskState::Pending
                    && match task.retry_timeout_at {
                        Some(at) => at <= now,
                        None => false,
                    } => seq![NoteV::Execute {
                        id,
                        version: task.version,
                    }],
                _ => Seq::empty(),
            }
        } else {
            Seq::empty()
        }
    }
}

pub open spec fn spec_retry_map(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV> {
    if map.contains_key(id)
        && map[id].promise.state == PromiseState::Pending
        && map[id].promise.timeout_at > now
        && map[id].task is Some
        && map[id].task.unwrap().state == TaskState::Pending
        && match map[id].task.unwrap().retry_timeout_at {
            Some(at) => at <= now,
            None => false,
        }
    {
        let object = map[id];
        map.insert(id, ObjV {
            task: Some(TkV {
                retry_timeout_at: Some(spec_sat_add(
                    now, retry_timeout,
                )),
                ..object.task.unwrap()
            }),
            ..object
        })
    } else {
        map
    }
}

pub open spec fn spec_retry_notes(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: Time,
) -> Seq<NoteV> {
    if map.contains_key(id)
        && map[id].promise.state == PromiseState::Pending
        && map[id].promise.timeout_at > now
        && map[id].task is Some
        && map[id].task.unwrap().state == TaskState::Pending
        && match map[id].task.unwrap().retry_timeout_at {
            Some(at) => at <= now,
            None => false,
        }
    {
        seq![NoteV::Execute {
            id,
            version: map[id].task.unwrap().version,
        }]
    } else {
        Seq::empty()
    }
}

pub proof fn lemma_retry_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        map.contains_key(id),
    ensures
        ({
            let work = InternalV::TaskRetryTimeout(id);
            let trace = spec_timeout_trace(
                config, state, now, seq![work],
            );
            &&& timeout_trace_legal(
                config, state, now, seq![work],
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(
                spec_retry_notes(map, id, now),
            )
            &&& origin_rel(
                spec_retry_map(
                    map, id, now, config.retry_timeout,
                ),
                origin_chars,
                trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
        }),
{
    let object = map[id];
    let promise = state.store.promises[id];
    let task = abstract_task(state.store, id);
    let work = InternalV::TaskRetryTimeout(id);
    let outcome = spec_process_work(
        config, work, state.store, now,
    );
    lemma_one_timeout_result(config, state, now, work);
    if object.promise.state == PromiseState::Pending
        && object.promise.timeout_at > now
        && object.task is Some
        && object.task.unwrap().state == TaskState::Pending
        && match object.task.unwrap().retry_timeout_at {
            Some(at) => at <= now,
            None => false,
        }
    {
        assert(object_rel(object, promise, task));
        assert(task is Some);
        let stored = task.unwrap();
        let concrete_task = TkV {
            retry_timeout_at: Some(spec_sat_add(
                now, config.retry_timeout,
            )),
            ..object.task.unwrap()
        };
        lemma_sat_add(now, config.retry_timeout);
        let abstract_task = TaskV {
            retry_timeout_at: Some(sat_add(
                now, config.retry_timeout,
            )),
            ..stored
        };
        let next_store = AStore {
            tasks: state.store.tasks.insert(id, abstract_task),
            ..state.store
        };
        assert(outcome == spec_retry(
            config, state.store, id, now,
        ));
        assert(outcome == spec_did(
            next_store,
            Seq::empty(),
            seq![DispatchV::Execute {
                id,
                version: stored.version,
            }],
        ));
        lemma_one_timeout_legal(config, state, now, work);
        assert(task_rel(concrete_task, abstract_task));
        let next_object = ObjV {
            task: Some(concrete_task),
            ..object
        };
        assert(object_rel(
            next_object, promise, Some(abstract_task),
        ));
        lemma_promises_kept(state.store, id);
        lemma_one_changed(
            map,
            origin_chars,
            state.store,
            id,
            next_object,
            promise,
            Some(abstract_task),
            next_store,
        );
        lemma_sends_execute(
            id, object.task.unwrap().version,
        );
        lemma_sends_of(state, outcome);
    } else {
        assert(outcome.not_due);
        lemma_not_due_timeout(
            config, state, now, work,
        );
        assert(spec_retry_map(
            map, id, now, config.retry_timeout,
        ) == map);
        assert(spec_retry_notes(map, id, now).len() == 0);
        lemma_sends_none();
        assert(changed_within(
            state.store, state.store, origin_chars,
        ));
    }
    let trace = spec_timeout_trace(
        config, state, now, seq![work],
    );
    assert(trace.state.pending == state.pending);
    assert(trace.send == note_sends(
        spec_retry_notes(map, id, now),
    ));
    assert(origin_rel(
        spec_retry_map(
            map, id, now, config.retry_timeout,
        ),
        origin_chars,
        trace.state.store,
    ));
    assert(changed_within(
        state.store, trace.state.store, origin_chars,
    ));
    assert(finite_store(trace.state.store));
}

pub proof fn lemma_phase1_object_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        origin_rel(map, origin_chars, state.store),
        map.contains_key(id),
        finite_store(state.store),
    ensures
        ({
            let next = map.insert(
                id,
                spec_project_due_object(
                    map[id], now, config.retry_timeout,
                ),
            );
            let works = spec_phase1_object_work(id);
            let trace =
                spec_timeout_trace(config, state, now, works);
            &&& timeout_trace_legal(
                config, state, now, works,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(
                spec_phase1_object_notes(map, id, now),
            )
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
        }),
{
    let object = map[id];
    let promise = state.store.promises[id];
    let task = abstract_task(state.store, id);
    assert(origin(id) == origin_chars);
    assert(object_rel(object, promise, task));
    let promise_work = InternalV::PromiseTimeout(id);
    let lease_work = InternalV::TaskLeaseTimeout(id);
    let retry_work = InternalV::TaskRetryTimeout(id);
    let first = spec_timeout_trace(
        config, state, now, seq![promise_work],
    );
    lemma_one_timeout_result(
        config, state, now, promise_work,
    );
    lemma_one_timeout_legal(config, state, now, promise_work);
    let projected_promise = spec_project_promise(promise, now);
    let concrete_promised =
        if object.promise.state == PromiseState::Pending
            && object.promise.timeout_at <= now
        {
            spec_project_obj(object, now)
        } else {
            object
        };
    if object.promise.state == PromiseState::Pending
        && object.promise.timeout_at <= now
    {
        let abstract_promised = match task {
            Some(value) => Some(spec_project_task(
                value, projected_promise,
            )),
            None => None,
        };
        let projected_tasks = match task {
            Some(_) => state.store.tasks.insert(
                id,
                abstract_promised.unwrap(),
            ),
            None => state.store.tasks,
        };
        let projected_store = AStore {
            promises: state.store.promises.insert(
                id, projected_promise,
            ),
            tasks: projected_tasks,
            ..state.store
        };
        let promise_outcome = spec_process_work(
            config, promise_work, state.store, now,
        );
        lemma_project_object(object, promise, task, now);
        assert(!spec_process_work(
            config, promise_work, state.store, now,
        ).not_due);
        assert(promise_outcome == spec_did(
            projected_store,
            Seq::empty(),
            Seq::empty(),
        ));
        assert(first.state.store == projected_store);
        match task {
            Some(_) => {
                assert(state.store.tasks.contains_key(id));
            },
            None => {
                assert(!state.store.tasks.contains_key(id));
                assert(state.store.tasks.remove(id)
                    =~= state.store.tasks);
            },
        }
        assert(object_rel(
            concrete_promised,
            projected_promise,
            abstract_promised,
        ));
        lemma_one_changed(
            map,
            origin_chars,
            state.store,
            id,
            concrete_promised,
            projected_promise,
            abstract_promised,
            first.state.store,
        );
    } else {
        assert(spec_process_work(
            config, promise_work, state.store, now,
        ).not_due);
        assert(first.state == state);
        assert(concrete_promised == object);
    }
    assert(origin_rel(
        map.insert(id, concrete_promised),
        origin_chars,
        first.state.store,
    ));
    let after_lease = spec_timeout_trace(
        config, first.state, now, seq![lease_work],
    );
    lemma_one_timeout_result(
        config, first.state, now, lease_work,
    );
    if concrete_promised.promise.state == PromiseState::Pending
        && concrete_promised.task is Some
        && concrete_promised.task.unwrap().state
            == TaskState::Acquired
        && match concrete_promised.task.unwrap().lease_timeout_at {
            Some(at) => at <= now,
            None => false,
        }
    {
        let stored = first.state.store.tasks[id];
        let concrete_task = c_unlease(
            concrete_promised.task.unwrap(),
            TaskState::Pending,
            Some(now),
        );
        let abstract_task =
            a_unlease(stored, TaskState::Pending, Some(now));
        let leased_store = AStore {
            tasks: first.state.store.tasks.insert(
                id, abstract_task,
            ),
            ..first.state.store
        };
        let lease_outcome = spec_process_work(
            config, lease_work, first.state.store, now,
        );
        assert(!spec_process_work(
            config, lease_work, first.state.store, now,
        ).not_due);
        lemma_one_timeout_legal(
            config, first.state, now, lease_work,
        );
        assert(lease_outcome
            == spec_lease(first.state.store, id, now));
        assert(lease_outcome == spec_did(
            leased_store,
            Seq::empty(),
            Seq::empty(),
        ));
        assert(after_lease.state.store == leased_store);
        assert(task_rel(concrete_task, abstract_task));
        let concrete_leased = ObjV {
            task: Some(concrete_task),
            ..concrete_promised
        };
        lemma_promises_kept(first.state.store, id);
        lemma_one_changed(
            map.insert(id, concrete_promised),
            origin_chars,
            first.state.store,
            id,
            concrete_leased,
            first.state.store.promises[id],
            Some(abstract_task),
            after_lease.state.store,
        );
    } else {
        assert(spec_process_work(
            config, lease_work, first.state.store, now,
        ).not_due);
        lemma_not_due_timeout(
            config, first.state, now, lease_work,
        );
        assert(after_lease.state == first.state);
    }
    let leased_object =
        if concrete_promised.promise.state == PromiseState::Pending
            && concrete_promised.task is Some
            && concrete_promised.task.unwrap().state
                == TaskState::Acquired
            && match concrete_promised.task.unwrap().lease_timeout_at {
                Some(at) => at <= now,
                None => false,
            }
        {
            ObjV {
                task: Some(c_unlease(
                    concrete_promised.task.unwrap(),
                    TaskState::Pending,
                    Some(now),
                )),
                ..concrete_promised
            }
        } else {
            concrete_promised
        };
    assert(origin_rel(
        map.insert(id, leased_object),
        origin_chars,
        after_lease.state.store,
    ));
    let after_retry = spec_timeout_trace(
        config, after_lease.state, now, seq![retry_work],
    );
    lemma_one_timeout_result(
        config, after_lease.state, now, retry_work,
    );
    let final_trace = spec_timeout_trace(
        config,
        state,
        now,
        spec_phase1_object_work(id),
    );
    lemma_timeout_trace_add(
        config,
        state,
        now,
        seq![promise_work],
        seq![lease_work, retry_work],
    );
    assert(spec_phase1_object_work(id)
        =~= seq![promise_work] + seq![lease_work, retry_work]);
    assert(spec_phase1_object_work(id)
        == seq![promise_work] + seq![lease_work, retry_work]);
    lemma_timeout_trace_add(
        config,
        first.state,
        now,
        seq![lease_work],
        seq![retry_work],
    );
    let lease_retry_trace = spec_timeout_trace(
        config,
        first.state,
        now,
        seq![lease_work, retry_work],
    );
    assert(seq![lease_work, retry_work]
        =~= seq![lease_work] + seq![retry_work]);
    assert(seq![lease_work, retry_work]
        == seq![lease_work] + seq![retry_work]);
    assert(lease_retry_trace.state == after_retry.state);
    assert(final_trace.state == lease_retry_trace.state);
    let final_object =
        spec_project_due_object(
            object, now, config.retry_timeout,
        );
    lemma_retry_matches(
        config,
        origin_chars,
        map.insert(id, leased_object),
        after_lease.state,
        now,
        id,
    );
    assert(spec_retry_map(
        map.insert(id, leased_object),
        id,
        now,
        config.retry_timeout,
    ) == map.insert(id, final_object));
    assert(spec_retry_notes(
        map.insert(id, leased_object), id, now,
    ) == spec_phase1_object_notes(map, id, now));
    assert(timeout_trace_legal(
        config,
        first.state,
        now,
        seq![lease_work],
    ));
    assert(timeout_trace_legal(
        config,
        after_lease.state,
        now,
        seq![retry_work],
    ));
    assert(timeout_trace_legal(
        config,
        first.state,
        now,
        seq![lease_work, retry_work],
    ));
    assert(final_trace.state == after_retry.state);
    assert(final_trace.state.pending == state.pending);
    assert(origin_rel(
        map.insert(id, final_object),
        origin_chars,
        final_trace.state.store,
    ));
    assert(changed_within(
        state.store,
        final_trace.state.store,
        origin_chars,
    )) by {
        assert forall|other: Seq<char>|
            #![trigger origin(other)]
            origin(other) != origin_chars implies {
                &&& state.store.promises.contains_key(other)
                    == final_trace.state.store.promises
                        .contains_key(other)
                &&& (state.store.promises.contains_key(other)
                    ==> state.store.promises[other]
                        == final_trace.state.store.promises[other])
                &&& state.store.tasks.contains_key(other)
                    == final_trace.state.store.tasks
                        .contains_key(other)
                &&& (state.store.tasks.contains_key(other)
                    ==> state.store.tasks[other]
                        == final_trace.state.store.tasks[other])
            } by {
                assert(other != id);
            };
    };
    assert(timeout_trace_legal(
        config,
        state,
        now,
        spec_phase1_object_work(id),
    ));
    assert(final_trace.state.pending == state.pending);
    assert(final_trace.send == note_sends(
        spec_phase1_object_notes(map, id, now),
    ));
    assert(finite_store(final_trace.state.store));
}

pub open spec fn spec_phase1_notes(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_project_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        spec_phase1_notes(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        ) + spec_phase1_object_notes(
            prior, keys[count as int - 1], now,
        )
    }
}

pub proof fn lemma_project_keys_preserves_unlisted(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
    id: Seq<char>,
)
    requires
        count <= keys.len(),
        !keys.take(count as int).contains(id),
    ensures
        spec_project_keys(
            map, keys, count, now, retry_timeout,
        ).contains_key(id) == map.contains_key(id),
        map.contains_key(id) ==> spec_project_keys(
            map, keys, count, now, retry_timeout,
        )[id] == map[id],
    decreases count,
{
    if count > 0 {
        lemma_project_keys_preserves_unlisted(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
            id,
        );
        assert(keys.take(count as int)
            == keys.take(count as int - 1).push(
                keys[count as int - 1],
            ));
        if keys[count as int - 1] == id {
            lemma_singleton_contains(id);
            lemma_contains_add(
                keys.take(count as int - 1),
                seq![id],
                id,
            );
            assert(keys.take(count as int - 1).push(id)
                =~= keys.take(count as int - 1) + seq![id]);
            assert(keys.take(count as int).contains(id));
        }
        assert(keys[count as int - 1] != id);
    }
}

pub proof fn lemma_phase1_notes_cover(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
        keys.take(count as int).no_duplicates(),
        forall|i: int| 0 <= i < count ==>
            map.contains_key(#[trigger] keys[i]),
    ensures
        ({
            let next = spec_project_keys(
                map, keys, count, now, retry_timeout,
            );
            let notes = spec_phase1_notes(
                map, keys, count, now, retry_timeout,
            );
            forall|id: Seq<char>|
                crate::document::offer_committed(
                    map, next, id, now,
                ) ==> notes.contains(NoteV::Execute {
                    id,
                    version: next[id].task.unwrap().version,
                })
        }),
    decreases count,
{
    if count == 0 {
    } else {
        lemma_phase1_notes_cover(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = spec_project_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        crate::quick_n_dirty::lemma_project_keys_keeps_domain(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let id = keys[count as int - 1];
        let next = spec_project_keys(
            map, keys, count, now, retry_timeout,
        );
        let object = prior[id];
        let projected = spec_project_due_object(
            object, now, retry_timeout,
        );
        let prior_notes = spec_phase1_notes(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let object_notes =
            spec_phase1_object_notes(prior, id, now);
        assert(spec_phase1_notes(
            map, keys, count, now, retry_timeout,
        ) == prior_notes + object_notes);
        assert(next == prior.insert(id, projected));
        assert(!keys.take((count - 1) as int).contains(id)) by {
            if keys.take((count - 1) as int).contains(id) {
                let i = choose|i: int|
                    0 <= i < count - 1
                        && keys[i] == id;
                assert(keys.take(count as int)[i]
                    == keys.take(count as int)[
                        count as int - 1
                    ]);
            }
        };
        lemma_project_keys_preserves_unlisted(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
            id,
        );
        assert(prior[id] == map[id]);
        assert forall|target: Seq<char>|
            crate::document::offer_committed(
                map, next, target, now,
            ) implies spec_phase1_notes(
                map, keys, count, now, retry_timeout,
            ).contains(NoteV::Execute {
                id: target,
                version: next[target].task.unwrap().version,
            }) by {
            lemma_contains_add(
                prior_notes,
                object_notes,
                NoteV::Execute {
                    id: target,
                    version: next[target].task
                        .unwrap().version,
                },
            );
            if target == id {
                assert(object == map[id]);
                if object.promise.state == PromiseState::Pending
                    && object.promise.timeout_at > now
                {
                    match object.task {
                        Some(task) => {
                            match task.state {
                                TaskState::Acquired => {
                                    match task.lease_timeout_at {
                                        Some(at) => {
                                            assert(at <= now);
                                            assert(object_notes
                                                == seq![NoteV::Execute {
                                                    id,
                                                    version: projected.task
                                                        .unwrap().version,
                                                }]);
                                            assert(next[id] == projected);
                                            lemma_singleton_contains(NoteV::Execute {
                                                id,
                                                version: projected.task
                                                    .unwrap().version,
                                            });
                                            assert(object_notes.contains(
                                                NoteV::Execute {
                                                    id,
                                                    version: next[id].task
                                                        .unwrap().version,
                                                },
                                            ));
                                            assert((prior_notes
                                                + object_notes).contains(
                                                NoteV::Execute {
                                                    id,
                                                    version: next[id].task
                                                        .unwrap().version,
                                                },
                                            ));
                                        },
                                        None => {},
                                    }
                                },
                                TaskState::Pending => {
                                    match task.retry_timeout_at {
                                        Some(at) => {
                                            assert(at <= now);
                                            assert(object_notes
                                                == seq![NoteV::Execute {
                                                    id,
                                                    version: projected.task
                                                        .unwrap().version,
                                                }]);
                                            assert(next[id] == projected);
                                            lemma_singleton_contains(NoteV::Execute {
                                                id,
                                                version: projected.task
                                                    .unwrap().version,
                                            });
                                            assert(object_notes.contains(
                                                NoteV::Execute {
                                                    id,
                                                    version: next[id].task
                                                        .unwrap().version,
                                                },
                                            ));
                                            assert((prior_notes
                                                + object_notes).contains(
                                                NoteV::Execute {
                                                    id,
                                                    version: next[id].task
                                                        .unwrap().version,
                                                },
                                            ));
                                        },
                                        None => {},
                                    }
                                },
                                _ => {},
                            }
                        },
                        None => {},
                    }
                }
            } else {
                assert(next[target] == prior[target]);
                assert(crate::document::offer_committed(
                    map, prior, target, now,
                ));
                assert(prior_notes.contains(
                    NoteV::Execute {
                        id: target,
                        version: prior[target].task
                            .unwrap().version,
                    },
                ));
                assert((prior_notes + object_notes).contains(
                    NoteV::Execute {
                        id: target,
                        version: next[target].task
                            .unwrap().version,
                    },
                ));
            }
        };
    }
}

pub proof fn lemma_phase1_fold_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    state: StateV,
    now: Time,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        count <= keys.len(),
        forall|i: int| 0 <= i < count ==>
            map.contains_key(#[trigger] keys[i]),
    ensures
        ({
            let next = spec_project_keys(
                map,
                keys,
                count,
                now,
                config.retry_timeout,
            );
            let works = spec_phase1_work(keys, count);
            let trace =
                spec_timeout_trace(config, state, now, works);
            &&& timeout_trace_legal(
                config, state, now, works,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(spec_phase1_notes(
                map,
                keys,
                count,
                now,
                config.retry_timeout,
            ))
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
        }),
    decreases count,
{
    if count == 0 {
        assert(spec_timeout_trace(
            config, state, now, Seq::empty(),
        ) == TimeoutTraceV {
            state,
            send: Seq::empty(),
        });
        assert(changed_within(
            state.store, state.store, origin_chars,
        ));
    } else {
        lemma_phase1_fold_matches(
            config,
            origin_chars,
            map,
            keys,
            (count - 1) as nat,
            state,
            now,
        );
        let prior_map = spec_project_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            config.retry_timeout,
        );
        let prior_work =
            spec_phase1_work(keys, (count - 1) as nat);
        let prior_trace = spec_timeout_trace(
            config, state, now, prior_work,
        );
        let id = keys[count as int - 1];
        crate::quick_n_dirty::lemma_project_keys_keeps_domain(
            map,
            keys,
            (count - 1) as nat,
            now,
            config.retry_timeout,
        );
        assert(prior_map.contains_key(id));
        lemma_phase1_object_matches(
            config,
            origin_chars,
            prior_map,
            prior_trace.state,
            now,
            id,
        );
        lemma_timeout_trace_add(
            config,
            state,
            now,
            prior_work,
            spec_phase1_object_work(id),
        );
        let all_work = spec_phase1_work(keys, count);
        let all_trace = spec_timeout_trace(
            config, state, now, all_work,
        );
        assert(all_work
            == prior_work + spec_phase1_object_work(id));
        assert(timeout_trace_legal(
            config, state, now, all_work,
        ));
        assert(all_trace.state.pending == state.pending);
        assert(origin_rel(
            spec_project_keys(
                map,
                keys,
                count,
                now,
                config.retry_timeout,
            ),
            origin_chars,
            all_trace.state.store,
        ));
        assert(changed_within(
            state.store,
            all_trace.state.store,
            origin_chars,
        )) by {
            let middle = prior_trace.state.store;
            assert forall|other: Seq<char>|
                #![trigger origin(other)]
                origin(other) != origin_chars implies {
                    &&& state.store.promises
                        .contains_key(other)
                        == all_trace.state.store.promises
                            .contains_key(other)
                    &&& (state.store.promises
                        .contains_key(other)
                        ==> state.store.promises[other]
                            == all_trace.state.store.promises[other])
                    &&& state.store.tasks.contains_key(other)
                        == all_trace.state.store.tasks
                            .contains_key(other)
                    &&& (state.store.tasks.contains_key(other)
                        ==> state.store.tasks[other]
                            == all_trace.state.store.tasks[other])
                } by {
                };
        };
    }
}

pub open spec fn spec_callback_notes(
    map: Map<Seq<char>, ObjV>,
    awaiter: Seq<char>,
    now: Time,
) -> Seq<NoteV> {
    if map.contains_key(awaiter) {
        let projected = spec_project_obj(map[awaiter], now);
        match projected.task {
            Some(task) if task.state == TaskState::Suspended =>
                seq![NoteV::Execute {
                    id: awaiter,
                    version: task.version,
                }],
            _ => Seq::empty(),
        }
    } else {
        Seq::empty()
    }
}

pub open spec fn spec_callback_fold_notes(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = crate::node::spec_drain_callbacks(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        spec_callback_fold_notes(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        ) + spec_callback_notes(
            prior,
            prior[id].promise.callbacks[0],
            now,
        )
    }
}

pub proof fn lemma_callback_apply_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        map.contains_key(id),
        map[id].promise.state != PromiseState::Pending,
        map[id].promise.callbacks.len() > 0,
    ensures
        ({
            let object = map[id];
            let awaiter = object.promise.callbacks[0];
            let since = object.promise.settled_at.unwrap();
            let popped = map.insert(id, ObjV {
                promise: PromV {
                    callbacks: object.promise.callbacks.skip(1),
                    ..object.promise
                },
                ..object
            });
            let next = crate::node::spec_resume(
                popped, awaiter, id, since, now, 0,
            );
            let work =
                InternalV::Callback { awaited: id, awaiter };
            let trace = spec_timeout_trace(
                config, state, now, seq![work],
            );
            &&& timeout_trace_legal(
                config, state, now, seq![work],
            )
            &&& trace.state.pending == state.pending
            &&& trace.send.len() == 0
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
        }),
{
    let store = state.store;
    let object = map[id];
    let promise = store.promises[id];
    let task = abstract_task(store, id);
    let callbacks = object.promise.callbacks;
    let awaiter = callbacks[0];
    assert(origin(id) == origin_chars);
    assert(object_rel(object, promise, task));
    assert(promise_rel(object.promise, promise));
    lemma_contains_to_set(callbacks, awaiter);
    assert(promise.callbacks.contains(awaiter));
    assert(origin(awaiter) == origin_chars);
    let since = object.promise.settled_at.unwrap();
    let work = InternalV::Callback {
        awaited: id,
        awaiter,
    };
    lemma_one_timeout_legal(config, state, now, work);
    lemma_one_timeout_result(config, state, now, work);
    let outcome =
        spec_process_work(config, work, store, now);
    let trace =
        spec_timeout_trace(config, state, now, seq![work]);
    assert(!outcome.not_due);
    assert(spec_project_promise(promise, now) == promise);
    let q = PromiseV {
        callbacks: promise.callbacks.remove(awaiter),
        ..promise
    };
    lemma_skip_no_duplicates(callbacks);
    let popped_object = ObjV {
        promise: PromV {
            callbacks: callbacks.skip(1),
            ..object.promise
        },
        ..object
    };
    assert(promise_rel(popped_object.promise, q));
    assert(object_rel(popped_object, q, task));
    let popped = map.insert(id, popped_object);
    let next = crate::node::spec_resume(
        popped,
        awaiter,
        id,
        since,
        now,
        0,
    );
    let callback = spec_callback(store, id, awaiter, now);
    assert(!callback.not_due);
    if !map.contains_key(awaiter) || awaiter == id {
        assert(next == popped);
    } else {
        let awaiter_object = map[awaiter];
        let awaiter_promise = store.promises[awaiter];
        let awaiter_task = abstract_task(store, awaiter);
        lemma_project_object(
            awaiter_object,
            awaiter_promise,
            awaiter_task,
            now,
        );
    }
    assert(origin_rel(
        next, origin_chars, trace.state.store,
    ));
    assert(trace.state.pending == state.pending);
    assert(changed_within(
        store, trace.state.store, origin_chars,
    )) by {
        assert forall|other: Seq<char>|
            #![trigger origin(other)]
            origin(other) != origin_chars implies {
                &&& store.promises.contains_key(other)
                    == trace.state.store.promises.contains_key(other)
                &&& (store.promises.contains_key(other)
                    ==> store.promises[other]
                        == trace.state.store.promises[other])
                &&& store.tasks.contains_key(other)
                    == trace.state.store.tasks.contains_key(other)
                &&& (store.tasks.contains_key(other)
                    ==> store.tasks[other]
                        == trace.state.store.tasks[other])
            } by {
        };
    };
    assert(finite_store(trace.state.store));
    lemma_sends_none();
    lemma_sends_of(state, outcome);
}

pub proof fn lemma_callback_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        map.contains_key(id),
        map[id].promise.state != PromiseState::Pending,
        map[id].promise.callbacks.len() > 0,
    ensures
        ({
            let object = map[id];
            let awaiter = object.promise.callbacks[0];
            let since = object.promise.settled_at.unwrap();
            let popped = map.insert(id, ObjV {
                promise: PromV {
                    callbacks: object.promise.callbacks.skip(1),
                    ..object.promise
                },
                ..object
            });
            let next = crate::node::spec_resume(
                popped,
                awaiter,
                id,
                since,
                now,
                config.retry_timeout,
            );
            let callback =
                seq![InternalV::Callback { awaited: id, awaiter }];
            let work = if spec_callback_notes(
                map, awaiter, now,
            ).len() > 0 {
                callback.push(
                    InternalV::TaskRetryTimeout(awaiter),
                )
            } else {
                callback
            };
            let trace =
                spec_timeout_trace(config, state, now, work);
            &&& timeout_trace_legal(
                config, state, now, work,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(
                spec_callback_notes(map, awaiter, now),
            )
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
        }),
{
    let object = map[id];
    let awaiter = object.promise.callbacks[0];
    let since = object.promise.settled_at.unwrap();
    let popped = map.insert(id, ObjV {
        promise: PromV {
            callbacks: object.promise.callbacks.skip(1),
            ..object.promise
        },
        ..object
    });
    let callback_work =
        InternalV::Callback { awaited: id, awaiter };
    let retry_work =
        InternalV::TaskRetryTimeout(awaiter);
    lemma_callback_apply_matches(
        config, origin_chars, map, state, now, id,
    );
    let callback_trace = spec_timeout_trace(
        config, state, now, seq![callback_work],
    );
    let intermediate = crate::node::spec_resume(
        popped, awaiter, id, since, now, 0,
    );
    let next = crate::node::spec_resume(
        popped,
        awaiter,
        id,
        since,
        now,
        config.retry_timeout,
    );
    let callback = seq![callback_work];
    let work = if spec_callback_notes(
        map, awaiter, now,
    ).len() > 0 {
        callback.push(
            InternalV::TaskRetryTimeout(awaiter),
        )
    } else {
        callback
    };
    let trace =
        spec_timeout_trace(config, state, now, work);
    if spec_callback_notes(map, awaiter, now).len() > 0 {
        reveal(spec_callback_notes);
        assert(map.contains_key(awaiter));
        assert(awaiter != id) by {
            if awaiter == id {
                assert(spec_project_obj(map[id], now)
                    .promise.state != PromiseState::Pending);
            }
        };
        assert(popped[awaiter] == map[awaiter]);
        let projected =
            spec_project_obj(map[awaiter], now);
        assert(projected.task is Some);
        assert(projected.task.unwrap().state
            == TaskState::Suspended);
        assert(projected.promise.state
            == PromiseState::Pending);
        assert(projected.promise.timeout_at > now);
        assert(projected.promise
            == map[awaiter].promise);
        assert(map[awaiter].promise.state
            == PromiseState::Pending);
        assert(map[awaiter].promise.timeout_at > now);
        let intermediate_task = TkV {
            state: TaskState::Pending,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: Some(now),
            resumes: seq![id],
            ..projected.task.unwrap()
        };
        let intermediate_object = ObjV {
            task: Some(intermediate_task),
            ..popped[awaiter]
        };
        let resumed_task = TkV {
            retry_timeout_at: Some(spec_sat_add(
                now, config.retry_timeout,
            )),
            ..intermediate_task
        };
        let resumed_object = ObjV {
            task: Some(resumed_task),
            ..popped[awaiter]
        };
        assert(intermediate
            == popped.insert(
                awaiter, intermediate_object,
            ));
        assert(intermediate[awaiter]
            == intermediate_object);
        assert(next
            == popped.insert(awaiter, resumed_object));
        let retry_trace = spec_timeout_trace(
            config,
            callback_trace.state,
            now,
            seq![retry_work],
        );
        assert(intermediate.contains_key(awaiter));
        lemma_retry_matches(
            config,
            origin_chars,
            intermediate,
            callback_trace.state,
            now,
            awaiter,
        );
        lemma_timeout_trace_add(
            config,
            state,
            now,
            seq![callback_work],
            seq![retry_work],
        );
        reveal(crate::node::spec_resume);
        reveal(spec_retry_map);
        reveal(spec_retry_notes);
        assert(spec_retry_map(
            intermediate,
            awaiter,
            now,
            config.retry_timeout,
        ) == next);
        assert(spec_retry_notes(
            intermediate, awaiter, now,
        ) == spec_callback_notes(map, awaiter, now));
        assert(changed_within(
            state.store,
            retry_trace.state.store,
            origin_chars,
        )) by {
            assert forall|other: Seq<char>|
                #![trigger origin(other)]
                origin(other) != origin_chars implies {
                    &&& state.store.promises.contains_key(other)
                        == retry_trace.state.store.promises
                            .contains_key(other)
                    &&& (state.store.promises.contains_key(other)
                        ==> state.store.promises[other]
                            == retry_trace.state.store.promises[other])
                    &&& state.store.tasks.contains_key(other)
                        == retry_trace.state.store.tasks
                            .contains_key(other)
                    &&& (state.store.tasks.contains_key(other)
                        ==> state.store.tasks[other]
                            == retry_trace.state.store.tasks[other])
                } by {
            };
        };
        assert(work == callback + seq![retry_work]);
        assert(trace == TimeoutTraceV {
            state: retry_trace.state,
            send: callback_trace.send + retry_trace.send,
        });
        assert(timeout_trace_legal(
            config, state, now, work,
        ));
        assert(trace.state.pending == state.pending);
        assert(trace.send == note_sends(
            spec_callback_notes(map, awaiter, now),
        ));
        assert(origin_rel(
            next, origin_chars, trace.state.store,
        ));
        assert(finite_store(trace.state.store));
    } else {
        reveal(spec_callback_notes);
        reveal(crate::node::spec_resume);
        assert(next == intermediate);
        assert(note_sends(
            spec_callback_notes(map, awaiter, now),
        ).len() == 0);
        assert(work == callback);
        assert(trace == callback_trace);
        assert(timeout_trace_legal(
            config, state, now, work,
        ));
        assert(trace.state.pending == state.pending);
        assert(trace.send == note_sends(
            spec_callback_notes(map, awaiter, now),
        ));
        assert(origin_rel(
            next, origin_chars, trace.state.store,
        ));
        assert(changed_within(
            state.store, trace.state.store, origin_chars,
        ));
        assert(finite_store(trace.state.store));
    }
    assert(timeout_trace_legal(
        config, state, now, work,
    ));
    assert(trace.state.pending == state.pending);
    assert(trace.send == note_sends(
        spec_callback_notes(map, awaiter, now),
    ));
    assert(origin_rel(
        next, origin_chars, trace.state.store,
    ));
    assert(changed_within(
        state.store, trace.state.store, origin_chars,
    ));
    assert(finite_store(trace.state.store));
}

pub proof fn lemma_listener_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        map.contains_key(id),
        map[id].promise.state != PromiseState::Pending,
        map[id].promise.listeners.len() > 0,
    ensures
        ({
            let object = map[id];
            let address = object.promise.listeners[0];
            let next = map.insert(id, ObjV {
                promise: PromV {
                    listeners: object.promise.listeners.skip(1),
                    ..object.promise
                },
                ..object
            });
            let work =
                InternalV::Listener { awaited: id, address };
            let trace = spec_timeout_trace(
                config, state, now, seq![work],
            );
            let record =
                spec_record(c_string(id), object.promise);
            &&& timeout_trace_legal(
                config, state, now, seq![work],
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(seq![
                NoteV::Unblock {
                    address,
                    promise: record,
                },
            ])
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
        }),
{
    let store = state.store;
    let object = map[id];
    let promise = store.promises[id];
    let task = abstract_task(store, id);
    let listeners = object.promise.listeners;
    let address = listeners[0];
    assert(origin(id) == origin_chars);
    assert(object_rel(object, promise, task));
    assert(promise_rel(object.promise, promise));
    lemma_contains_to_set(listeners, address);
    assert(promise.listeners.contains(address));
    let work = InternalV::Listener {
        awaited: id,
        address,
    };
    lemma_one_timeout_legal(config, state, now, work);
    lemma_one_timeout_result(config, state, now, work);
    let outcome =
        spec_process_work(config, work, store, now);
    assert(!outcome.not_due);
    let q = PromiseV {
        listeners: promise.listeners.remove(address),
        ..promise
    };
    let next_object = ObjV {
        promise: PromV {
            listeners: listeners.skip(1),
            ..object.promise
        },
        ..object
    };
    lemma_skip_no_duplicates(listeners);
    assert(promise_rel(next_object.promise, q));
    assert(object_rel(next_object, q, task));
    lemma_tasks_kept(store, id);
    lemma_one_changed(
        map,
        origin_chars,
        store,
        id,
        next_object,
        q,
        task,
        outcome.next,
    );
    crate::interpret::lemma_string_same(id);
    lemma_record(c_string(id), object.promise, promise);
    lemma_sends_unblock(
        address,
        spec_record(c_string(id), object.promise),
    );
    lemma_sends_of(state, outcome);
}

pub open spec fn spec_listener_fold_notes(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV> {
    listeners.take(count as int).map_values(
        |address: Seq<char>| NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(id), map[id].promise,
            ),
        },
    )
}

pub proof fn lemma_callback_fold_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    count: nat,
    state: StateV,
    now: Time,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        map.contains_key(id),
        map[id].promise.state != PromiseState::Pending,
        count <= map[id].promise.callbacks.len(),
    ensures
        ({
            let next = crate::node::spec_drain_callbacks(
                map,
                id,
                count,
                now,
                config.retry_timeout,
            );
            let works = spec_callback_work(
                map,
                id,
                count,
                now,
                config.retry_timeout,
            );
            let trace =
                spec_timeout_trace(config, state, now, works);
            &&& timeout_trace_legal(
                config, state, now, works,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(
                spec_callback_fold_notes(
                    map,
                    id,
                    count,
                    now,
                    config.retry_timeout,
                ),
            )
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
        }),
    decreases count,
{
    if count == 0 {
        assert(changed_within(
            state.store, state.store, origin_chars,
        ));
    } else {
        lemma_callback_fold_matches(
            config,
            origin_chars,
            map,
            id,
            (count - 1) as nat,
            state,
            now,
        );
        let prior = crate::node::spec_drain_callbacks(
            map,
            id,
            (count - 1) as nat,
            now,
            config.retry_timeout,
        );
        let prior_work = spec_callback_work(
            map,
            id,
            (count - 1) as nat,
            now,
            config.retry_timeout,
        );
        let prior_trace = spec_timeout_trace(
            config, state, now, prior_work,
        );
        lemma_callback_drain_length(
            map,
            id,
            (count - 1) as nat,
            now,
            config.retry_timeout,
        );
        assert(prior[id].promise.callbacks.len() > 0);
        lemma_callback_matches(
            config,
            origin_chars,
            prior,
            prior_trace.state,
            now,
            id,
        );
        let awaiter = prior[id].promise.callbacks[0];
        let callback = seq![InternalV::Callback {
            awaited: id,
            awaiter,
        }];
        let one = if spec_callback_notes(
            prior, awaiter, now,
        ).len() > 0 {
            callback.push(
                InternalV::TaskRetryTimeout(awaiter),
            )
        } else {
            callback
        };
        lemma_timeout_trace_add(
            config, state, now, prior_work, one,
        );
    }
}

pub proof fn lemma_callback_drain_length(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        map.contains_key(id),
        count <= map[id].promise.callbacks.len(),
    ensures
        ({
            let drained = crate::node::spec_drain_callbacks(
                map, id, count, now, retry_timeout,
            );
            &&& drained.contains_key(id)
            &&& drained[id].promise.callbacks.len()
                == map[id].promise.callbacks.len() - count
            &&& drained[id].promise.state
                == map[id].promise.state
            &&& drained[id].promise.listeners
                == map[id].promise.listeners
        }),
    decreases count,
{
    reveal(crate::node::spec_drain_callbacks);
    if count > 0 {
        lemma_callback_drain_length(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_drain_callbacks(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        assert(prior[id].promise.callbacks.len() > 0);
        let object = prior[id];
        let popped = prior.insert(id, ObjV {
            promise: PromV {
                callbacks: object.promise.callbacks.skip(1),
                ..object.promise
            },
            ..object
        });
        reveal(crate::node::spec_resume);
    }
}

pub proof fn lemma_drain_callbacks_preserves_task_versions(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= if map.contains_key(id) {
            map[id].promise.callbacks.len()
        } else {
            0
        },
    ensures
        ({
            let next = crate::node::spec_drain_callbacks(
                map, id, count, now, retry_timeout,
            );
            forall|target: Seq<char>|
                #[trigger] next.contains_key(target) ==>
                {
                    &&& (next[target].task is Some)
                        == (map[target].task is Some)
                    &&& (next[target].task is Some ==>
                        next[target].task.unwrap().version
                            == map[target].task.unwrap().version)
                }
        }),
    decreases count,
{
    reveal(crate::node::spec_drain_callbacks);
    if count > 0 {
        lemma_drain_callbacks_preserves_task_versions(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_drain_callbacks(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        if prior.contains_key(id)
            && prior[id].promise.callbacks.len() > 0
        {
            let object = prior[id];
            let awaiter = object.promise.callbacks[0];
            let popped = prior.insert(id, ObjV {
                promise: PromV {
                    callbacks: object.promise.callbacks.skip(1),
                    ..object.promise
                },
                ..object
            });
            let since = match object.promise.settled_at {
                Some(at) => at,
                None => 0,
            };
            let next = crate::node::spec_resume(
                popped,
                awaiter,
                id,
                since,
                now,
                retry_timeout,
            );
            reveal(crate::node::spec_resume);
            assert forall|target: Seq<char>|
                #[trigger] next.contains_key(target) implies {
                    &&& (next[target].task is Some)
                        == (map[target].task is Some)
                    &&& (next[target].task is Some ==>
                        next[target].task.unwrap().version
                            == map[target].task.unwrap().version)
                } by {
                if target == awaiter {
                    assert((spec_project_obj(
                        popped[target], now,
                    ).task is Some)
                        == (popped[target].task is Some));
                    if popped[target].task is Some {
                        assert(spec_project_obj(
                            popped[target], now,
                        ).task.unwrap().version
                            == popped[target].task.unwrap().version);
                    }
                }
            };
        }
    }
}

pub proof fn lemma_callback_fold_notes_cover(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        map.contains_key(id),
        map[id].promise.state != PromiseState::Pending,
        count <= map[id].promise.callbacks.len(),
    ensures
        ({
            let next = crate::node::spec_drain_callbacks(
                map, id, count, now, retry_timeout,
            );
            let notes = spec_callback_fold_notes(
                map, id, count, now, retry_timeout,
            );
            forall|target: Seq<char>|
                crate::document::offer_committed(
                    map, next, target, now,
                ) ==> notes.contains(NoteV::Execute {
                    id: target,
                    version: next[target].task.unwrap().version,
                })
        }),
    decreases count,
{
    if count > 0 {
        lemma_callback_fold_notes_cover(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        lemma_callback_drain_length(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        crate::quick_n_dirty::lemma_drain_callbacks_keeps_domain(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_drain_callbacks(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let object = prior[id];
        let awaiter = object.promise.callbacks[0];
        let popped = prior.insert(id, ObjV {
            promise: PromV {
                callbacks: object.promise.callbacks.skip(1),
                ..object.promise
            },
            ..object
        });
        let since = match object.promise.settled_at {
            Some(at) => at,
            None => 0,
        };
        let next = crate::node::spec_resume(
            popped,
            awaiter,
            id,
            since,
            now,
            retry_timeout,
        );
        let prior_notes = spec_callback_fold_notes(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let one = spec_callback_notes(
            prior, awaiter, now,
        );
        assert(spec_callback_fold_notes(
            map, id, count, now, retry_timeout,
        ) == prior_notes + one);
        assert forall|target: Seq<char>|
            crate::document::offer_committed(
                map, next, target, now,
            ) implies (prior_notes + one).contains(
                NoteV::Execute {
                    id: target,
                    version: next[target].task.unwrap().version,
                },
            ) by {
            let note = NoteV::Execute {
                id: target,
                version: next[target].task.unwrap().version,
            };
            lemma_contains_add(prior_notes, one, note);
            if crate::document::offer_committed(
                map, prior, target, now,
            ) {
                assert(prior_notes.contains(NoteV::Execute {
                    id: target,
                    version: prior[target].task.unwrap().version,
                }));
                reveal(crate::node::spec_resume);
                if target != awaiter {
                    assert(next[target].task
                        == prior[target].task);
                } else if spec_project_obj(
                    prior[awaiter], now,
                ).task is Some
                    && spec_project_obj(
                        prior[awaiter], now,
                    ).task.unwrap().state
                        == TaskState::Suspended
                {
                    reveal(spec_callback_notes);
                    assert(one.contains(NoteV::Execute {
                        id: target,
                        version: next[target].task
                            .unwrap().version,
                    }));
                }
            } else {
                reveal(crate::node::spec_resume);
                reveal(spec_callback_notes);
                assert(target == awaiter);
                assert(prior.contains_key(awaiter));
                assert(awaiter != id) by {
                    if awaiter == id {
                        assert(spec_project_obj(
                            prior[id], now,
                        ).promise.state
                            != PromiseState::Pending);
                    }
                };
                assert(popped[awaiter] == prior[awaiter]);
                assert(spec_project_obj(
                    prior[awaiter], now,
                ).task is Some);
                assert(spec_project_obj(
                    prior[awaiter], now,
                ).task.unwrap().state
                    == TaskState::Suspended);
                assert(next[target].task.unwrap().version
                    == spec_project_obj(
                        prior[awaiter], now,
                    ).task.unwrap().version);
                assert(one == seq![NoteV::Execute {
                    id: target,
                    version: next[target].task.unwrap().version,
                }]);
                lemma_singleton_contains(NoteV::Execute {
                    id: target,
                    version: next[target].task.unwrap().version,
                });
                assert(one.contains(NoteV::Execute {
                    id: target,
                    version: next[target].task.unwrap().version,
                }));
            }
        };
    }
}

pub proof fn lemma_listener_fold_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
    state: StateV,
    now: Time,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        map.contains_key(id),
        map[id].promise.state != PromiseState::Pending,
        map[id].promise.listeners == listeners,
        count <= listeners.len(),
    ensures
        ({
            let next = map.insert(id, ObjV {
                promise: PromV {
                    listeners: listeners.skip(count as int),
                    ..map[id].promise
                },
                ..map[id]
            });
            let works =
                spec_listener_work(id, listeners, count);
            let trace =
                spec_timeout_trace(config, state, now, works);
            &&& timeout_trace_legal(
                config, state, now, works,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(
                spec_listener_fold_notes(
                    map, id, listeners, count,
                ),
            )
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
        }),
    decreases count,
{
    if count == 0 {
        assert(listeners.skip(0) == listeners);
        assert(map.insert(id, map[id]) =~= map);
        assert(changed_within(
            state.store, state.store, origin_chars,
        ));
    } else {
        lemma_listener_fold_matches(
            config,
            origin_chars,
            map,
            id,
            listeners,
            (count - 1) as nat,
            state,
            now,
        );
        let prior_map = map.insert(id, ObjV {
            promise: PromV {
                listeners: listeners.skip((count - 1) as int),
                ..map[id].promise
            },
            ..map[id]
        });
        let prior_work = spec_listener_work(
            id, listeners, (count - 1) as nat,
        );
        let prior_trace = spec_timeout_trace(
            config, state, now, prior_work,
        );
        assert(prior_map[id].promise.listeners.len() > 0);
        lemma_listener_matches(
            config,
            origin_chars,
            prior_map,
            prior_trace.state,
            now,
            id,
        );
        let address =
            prior_map[id].promise.listeners[0];
        lemma_timeout_trace_add(
            config,
            state,
            now,
            prior_work,
            seq![InternalV::Listener {
                awaited: id,
                address,
            }],
        );
        let one = seq![InternalV::Listener {
            awaited: id,
            address,
        }];
        assert(spec_listener_work(id, listeners, count)
            =~= prior_work + one);
        assert(spec_listener_work(id, listeners, count)
            == prior_work + one);
        let prior_notes = spec_listener_fold_notes(
            map, id, listeners, (count - 1) as nat,
        );
        let one_note = seq![NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(id), map[id].promise,
            ),
        }];
        assert(spec_listener_fold_notes(
            map, id, listeners, count,
        ) =~= prior_notes + one_note);
        assert(spec_listener_fold_notes(
            map, id, listeners, count,
        ) == prior_notes + one_note);
        assert(spec_record(
            c_string(id), prior_map[id].promise,
        ) == spec_record(c_string(id), map[id].promise));
        let one_trace = spec_timeout_trace(
            config,
            prior_trace.state,
            now,
            one,
        );
        let all_trace = spec_timeout_trace(
            config,
            state,
            now,
            spec_listener_work(id, listeners, count),
        );
        assert(all_trace == TimeoutTraceV {
            state: one_trace.state,
            send: prior_trace.send + one_trace.send,
        });
        assert(all_trace.state == one_trace.state);
        assert(all_trace.send
            == prior_trace.send + one_trace.send);
        assert(one_trace.send == note_sends(one_note));
        assert(prior_trace.send == note_sends(prior_notes));
        assert(note_sends(prior_notes + one_note)
            == note_sends(prior_notes)
                + note_sends(one_note));
        let one_next = prior_map.insert(id, ObjV {
            promise: PromV {
                listeners: prior_map[id].promise.listeners.skip(1),
                ..prior_map[id].promise
            },
            ..prior_map[id]
        });
        let next = map.insert(id, ObjV {
            promise: PromV {
                listeners: listeners.skip(count as int),
                ..map[id].promise
            },
            ..map[id]
        });
        assert(listeners.skip((count - 1) as int).skip(1)
            =~= listeners.skip(count as int));
        assert(one_next == next);
        assert(origin_rel(
            next, origin_chars, all_trace.state.store,
        ));
    }
    let next = map.insert(id, ObjV {
        promise: PromV {
            listeners: listeners.skip(count as int),
            ..map[id].promise
        },
        ..map[id]
    });
    let works = spec_listener_work(id, listeners, count);
    let trace =
        spec_timeout_trace(config, state, now, works);
    assert(timeout_trace_legal(
        config, state, now, works,
    ));
    assert(trace.state.pending == state.pending);
    assert(trace.send == note_sends(
        spec_listener_fold_notes(
            map, id, listeners, count,
        ),
    ));
    assert(origin_rel(
        next, origin_chars, trace.state.store,
    ));
    assert(changed_within(
        state.store, trace.state.store, origin_chars,
    ));
    assert(finite_store(trace.state.store));
}

pub open spec fn spec_callback_object_notes(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: Time,
    retry_timeout: u64,
) -> Seq<NoteV> {
    if !map.contains_key(id)
        || map[id].promise.state == PromiseState::Pending
    {
        Seq::empty()
    } else {
        let callbacks = map[id].promise.callbacks;
        spec_callback_fold_notes(
            map,
            id,
            callbacks.len(),
            now,
            retry_timeout,
        )
    }
}

pub proof fn lemma_callback_object_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        map.contains_key(id),
    ensures
        ({
            let next = crate::node::spec_drain_settled_callbacks(
                map, id, now, config.retry_timeout,
            );
            let works = spec_callback_object_work(
                map, id, now, config.retry_timeout,
            );
            let trace =
                spec_timeout_trace(config, state, now, works);
            &&& timeout_trace_legal(
                config, state, now, works,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(
                spec_callback_object_notes(
                    map, id, now, config.retry_timeout,
                ),
            )
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
            &&& next.dom() == map.dom()
        }),
{
    if map[id].promise.state == PromiseState::Pending {
        assert(spec_callback_object_work(
            map, id, now, config.retry_timeout,
        ).len() == 0);
        assert(crate::node::spec_drain_settled_callbacks(
            map, id, now, config.retry_timeout,
        ) == map);
        assert(changed_within(
            state.store, state.store, origin_chars,
        ));
    } else {
        let callbacks = map[id].promise.callbacks;
        lemma_callback_fold_matches(
            config,
            origin_chars,
            map,
            id,
            callbacks.len(),
            state,
            now,
        );
        reveal(crate::node::spec_drain_settled_callbacks);
        crate::quick_n_dirty::lemma_drain_callbacks_keeps_domain(
            map,
            id,
            callbacks.len(),
            now,
            config.retry_timeout,
        );
    }
}

pub open spec fn spec_callback_keys_notes(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = crate::node::spec_drain_callback_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        spec_callback_keys_notes(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        ) + spec_callback_object_notes(
            prior,
            keys[count as int - 1],
            now,
            retry_timeout,
        )
    }
}

pub proof fn lemma_callback_keys_preserves_task_versions(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
    ensures
        ({
            let next = crate::node::spec_drain_callback_keys(
                map, keys, count, now, retry_timeout,
            );
            forall|target: Seq<char>|
                #[trigger] next.contains_key(target) ==>
                {
                    &&& (next[target].task is Some)
                        == (map[target].task is Some)
                    &&& (next[target].task is Some ==>
                        next[target].task.unwrap().version
                            == map[target].task.unwrap().version)
                }
        }),
    decreases count,
{
    crate::quick_n_dirty::lemma_drain_callback_keys_keeps_domain(
        map, keys, count, now, retry_timeout,
    );
    if count > 0 {
        lemma_callback_keys_preserves_task_versions(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        crate::quick_n_dirty::lemma_drain_callback_keys_keeps_domain(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_drain_callback_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let id = keys[count as int - 1];
        reveal(crate::node::spec_drain_settled_callbacks);
        if prior.contains_key(id)
            && prior[id].promise.state
                != PromiseState::Pending
        {
            lemma_drain_callbacks_preserves_task_versions(
                prior,
                id,
                prior[id].promise.callbacks.len(),
                now,
                retry_timeout,
            );
        }
    }
}

pub proof fn lemma_project_keys_preserves_task_versions(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
    ensures
        ({
            let next = crate::node::spec_project_keys(
                map, keys, count, now, retry_timeout,
            );
            forall|target: Seq<char>|
                #[trigger] next.contains_key(target) ==>
                {
                    &&& (next[target].task is Some)
                        == (map[target].task is Some)
                    &&& (next[target].task is Some ==>
                        next[target].task.unwrap().version
                            == map[target].task.unwrap().version)
                }
        }),
    decreases count,
{
    crate::quick_n_dirty::lemma_project_keys_keeps_domain(
        map, keys, count, now, retry_timeout,
    );
    if count > 0 {
        lemma_project_keys_preserves_task_versions(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_project_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let id = keys[count as int - 1];
        reveal(crate::node::spec_project_due_object);
        reveal(crate::node::spec_project_obj);
        reveal(crate::node::spec_fulfill_task);
        reveal(crate::node::spec_unlease);
        assert forall|target: Seq<char>|
            #[trigger] crate::node::spec_project_keys(
                map, keys, count, now, retry_timeout,
            ).contains_key(target) implies
            {
                let next = crate::node::spec_project_keys(
                    map, keys, count, now, retry_timeout,
                );
                &&& (next[target].task is Some)
                    == (map[target].task is Some)
                &&& (next[target].task is Some ==>
                    next[target].task.unwrap().version
                        == map[target].task.unwrap().version)
            } by {
            if target != id {
                assert(crate::node::spec_project_keys(
                    map, keys, count, now, retry_timeout,
                )[target] == prior[target]);
            }
        };
    }
}

pub proof fn lemma_project_keys_pending_reflects(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
    ensures
        ({
            let next = crate::node::spec_project_keys(
                map, keys, count, now, retry_timeout,
            );
            forall|target: Seq<char>|
                #[trigger] next.contains_key(target)
                    && next[target].promise.state
                        == PromiseState::Pending ==>
                {
                    &&& map.contains_key(target)
                    &&& map[target].promise.state
                        == PromiseState::Pending
                }
        }),
    decreases count,
{
    crate::quick_n_dirty::lemma_project_keys_keeps_domain(
        map, keys, count, now, retry_timeout,
    );
    if count > 0 {
        lemma_project_keys_pending_reflects(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_project_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let id = keys[count as int - 1];
        reveal(crate::node::spec_project_due_object);
        reveal(crate::node::spec_project_obj);
        reveal(crate::node::spec_project_prom);
        assert forall|target: Seq<char>|
            #[trigger] crate::node::spec_project_keys(
                map, keys, count, now, retry_timeout,
            ).contains_key(target)
                && crate::node::spec_project_keys(
                    map, keys, count, now, retry_timeout,
                )[target].promise.state
                    == PromiseState::Pending implies
            {
                &&& map.contains_key(target)
                &&& map[target].promise.state
                    == PromiseState::Pending
            } by {
            if target != id {
                assert(crate::node::spec_project_keys(
                    map, keys, count, now, retry_timeout,
                )[target] == prior[target]);
            }
        };
    }
}

pub proof fn lemma_offer_endpoint_decompose(
    before: Map<Seq<char>, ObjV>,
    middle: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: Time,
)
    requires
        crate::document::offer_committed(
            before, after, id, now,
        ),
        middle.contains_key(id),
        middle[id].promise.state == after[id].promise.state,
    ensures
        crate::document::offer_committed(
            before, middle, id, now,
        ) || crate::document::offer_committed(
            middle, after, id, now,
        ),
{
    reveal(crate::document::offer_committed);
    if middle.contains_key(id) {
        match middle[id].task {
            Some(task) => {},
            None => {},
        }
    }
}

pub proof fn lemma_callback_keys_notes_cover(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
        forall|i: int| 0 <= i < count ==>
            map.contains_key(#[trigger] keys[i]),
    ensures
        ({
            let next = crate::node::spec_drain_callback_keys(
                map, keys, count, now, retry_timeout,
            );
            let notes = spec_callback_keys_notes(
                map, keys, count, now, retry_timeout,
            );
            forall|target: Seq<char>|
                crate::document::offer_committed(
                    map, next, target, now,
                ) ==> notes.contains(NoteV::Execute {
                    id: target,
                    version: next[target].task.unwrap().version,
                })
        }),
    decreases count,
{
    if count > 0 {
        lemma_callback_keys_notes_cover(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        crate::quick_n_dirty::lemma_drain_callback_keys_keeps_domain(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_drain_callback_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let id = keys[count as int - 1];
        let next = crate::node::spec_drain_settled_callbacks(
            prior, id, now, retry_timeout,
        );
        let prior_notes = spec_callback_keys_notes(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let one = spec_callback_object_notes(
            prior, id, now, retry_timeout,
        );
        if prior[id].promise.state != PromiseState::Pending {
            lemma_callback_fold_notes_cover(
                prior,
                id,
                prior[id].promise.callbacks.len(),
                now,
                retry_timeout,
            );
            lemma_drain_callbacks_preserves_task_versions(
                prior,
                id,
                prior[id].promise.callbacks.len(),
                now,
                retry_timeout,
            );
            crate::quick_n_dirty::lemma_drain_callbacks_preserves_record(
                prior,
                id,
                prior[id].promise.callbacks.len(),
                now,
                retry_timeout,
            );
            crate::quick_n_dirty::lemma_drain_callbacks_keeps_domain(
                prior,
                id,
                prior[id].promise.callbacks.len(),
                now,
                retry_timeout,
            );
        }
        reveal(crate::node::spec_drain_settled_callbacks);
        assert forall|target: Seq<char>|
            crate::document::offer_committed(
                map, next, target, now,
            ) implies (prior_notes + one).contains(
                NoteV::Execute {
                    id: target,
                    version: next[target].task.unwrap().version,
                },
            ) by {
            let note = NoteV::Execute {
                id: target,
                version: next[target].task.unwrap().version,
            };
            lemma_contains_add(prior_notes, one, note);
            if crate::document::offer_committed(
                map, prior, target, now,
            ) {
                assert(prior_notes.contains(NoteV::Execute {
                    id: target,
                    version: prior[target].task.unwrap().version,
                }));
                if target != id {
                    crate::quick_n_dirty::lemma_drain_callbacks_preserves_other_promises(
                        prior,
                        id,
                        prior[id].promise.callbacks.len(),
                        now,
                        retry_timeout,
                    );
                }
            } else {
                assert(prior.contains_key(target));
                assert(prior[target].promise.state
                    == next[target].promise.state) by {
                    if prior[id].promise.state
                        != PromiseState::Pending
                    {
                        if target != id {
                            crate::quick_n_dirty::lemma_drain_callbacks_preserves_other_promises(
                                prior,
                                id,
                                prior[id].promise.callbacks.len(),
                                now,
                                retry_timeout,
                            );
                            assert(next[target].promise
                                == prior[target].promise);
                        } else {
                            assert(spec_record(
                                c_string(id), next[id].promise,
                            ) == spec_record(
                                c_string(id), prior[id].promise,
                            ));
                        }
                    } else {
                        assert(next == prior);
                    }
                };
                lemma_offer_endpoint_decompose(
                    map, prior, next, target, now,
                );
                assert(crate::document::offer_committed(
                    prior, next, target, now,
                ));
                assert(one.contains(NoteV::Execute {
                    id: target,
                    version: next[target].task.unwrap().version,
                }));
            }
        };
    }
}

pub proof fn lemma_callback_keys_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    state: StateV,
    now: Time,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        count <= keys.len(),
        forall|i: int| 0 <= i < count ==>
            map.contains_key(#[trigger] keys[i]),
    ensures
        ({
            let next = crate::node::spec_drain_callback_keys(
                map,
                keys,
                count,
                now,
                config.retry_timeout,
            );
            let works = spec_callback_keys_work(
                map,
                keys,
                count,
                now,
                config.retry_timeout,
            );
            let trace =
                spec_timeout_trace(config, state, now, works);
            &&& timeout_trace_legal(
                config, state, now, works,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(spec_callback_keys_notes(
                map,
                keys,
                count,
                now,
                config.retry_timeout,
            ))
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
            &&& next.dom() == map.dom()
        }),
    decreases count,
{
    if count == 0 {
        assert(changed_within(
            state.store, state.store, origin_chars,
        ));
    } else {
        lemma_callback_keys_matches(
            config,
            origin_chars,
            map,
            keys,
            (count - 1) as nat,
            state,
            now,
        );
        let prior = crate::node::spec_drain_callback_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            config.retry_timeout,
        );
        let prior_work = spec_callback_keys_work(
            map,
            keys,
            (count - 1) as nat,
            now,
            config.retry_timeout,
        );
        let prior_trace = spec_timeout_trace(
            config, state, now, prior_work,
        );
        let id = keys[count as int - 1];
        assert(prior.contains_key(id));
        lemma_callback_object_matches(
            config,
            origin_chars,
            prior,
            prior_trace.state,
            now,
            id,
        );
        let one = spec_callback_object_work(
            prior, id, now, config.retry_timeout,
        );
        lemma_timeout_trace_add(
            config, state, now, prior_work, one,
        );
    }
}

pub open spec fn spec_listener_object_notes(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
) -> Seq<NoteV> {
    if !map.contains_key(id)
        || map[id].promise.state == PromiseState::Pending
    {
        Seq::empty()
    } else {
        spec_listener_fold_notes(
            map,
            id,
            map[id].promise.listeners,
            map[id].promise.listeners.len(),
        )
    }
}

pub proof fn lemma_listener_object_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        map.contains_key(id),
    ensures
        ({
            let next =
                crate::node::spec_clear_settled_listeners(
                    map, id,
                );
            let works = spec_listener_object_work(map, id);
            let trace =
                spec_timeout_trace(config, state, now, works);
            &&& timeout_trace_legal(
                config, state, now, works,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(
                spec_listener_object_notes(map, id),
            )
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
            &&& next.dom() == map.dom()
        }),
{
    if map[id].promise.state == PromiseState::Pending {
        assert(spec_listener_object_work(map, id).len() == 0);
        assert(crate::node::spec_clear_settled_listeners(
            map, id,
        ) == map);
        assert(changed_within(
            state.store, state.store, origin_chars,
        ));
    } else {
        let listeners = map[id].promise.listeners;
        lemma_listener_fold_matches(
            config,
            origin_chars,
            map,
            id,
            listeners,
            listeners.len(),
            state,
            now,
        );
        assert(listeners.skip(listeners.len() as int)
            =~= Seq::<Seq<char>>::empty());
        reveal(crate::node::spec_clear_settled_listeners);
    }
}

pub open spec fn spec_listener_keys_notes(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = crate::node::spec_clear_listener_keys(
            map, keys, (count - 1) as nat,
        );
        spec_listener_keys_notes(
            map, keys, (count - 1) as nat,
        ) + spec_listener_object_notes(
            prior, keys[count as int - 1],
        )
    }
}

pub proof fn lemma_listener_keys_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    state: StateV,
    now: Time,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        count <= keys.len(),
        forall|i: int| 0 <= i < count ==>
            map.contains_key(#[trigger] keys[i]),
    ensures
        ({
            let next = crate::node::spec_clear_listener_keys(
                map, keys, count,
            );
            let works =
                spec_listener_keys_work(map, keys, count);
            let trace =
                spec_timeout_trace(config, state, now, works);
            &&& timeout_trace_legal(
                config, state, now, works,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(
                spec_listener_keys_notes(map, keys, count),
            )
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
            &&& next.dom() == map.dom()
        }),
    decreases count,
{
    if count == 0 {
        assert(changed_within(
            state.store, state.store, origin_chars,
        ));
    } else {
        lemma_listener_keys_matches(
            config,
            origin_chars,
            map,
            keys,
            (count - 1) as nat,
            state,
            now,
        );
        let prior = crate::node::spec_clear_listener_keys(
            map, keys, (count - 1) as nat,
        );
        let prior_work = spec_listener_keys_work(
            map, keys, (count - 1) as nat,
        );
        let prior_trace = spec_timeout_trace(
            config, state, now, prior_work,
        );
        let id = keys[count as int - 1];
        assert(prior.contains_key(id));
        lemma_listener_object_matches(
            config,
            origin_chars,
            prior,
            prior_trace.state,
            now,
            id,
        );
        let one = spec_listener_object_work(prior, id);
        lemma_timeout_trace_add(
            config, state, now, prior_work, one,
        );
    }
}

pub open spec fn spec_phase2_notes(
    projected: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Seq<NoteV> {
    let resumed = crate::node::spec_drain_callback_keys(
        projected, keys, count, now, retry_timeout,
    );
    spec_callback_keys_notes(
        projected, keys, count, now, retry_timeout,
    ) + spec_listener_keys_notes(resumed, keys, count)
}

pub proof fn lemma_execute_notes_subset(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    now: Time,
    keys: Seq<Seq<char>>,
    count: nat,
    raw: Seq<NoteV>,
)
    requires
        count <= keys.len(),
        forall|id: Seq<char>|
            crate::document::offer_committed(
                before, after, id, now,
            ) ==> raw.contains(NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            }),
    ensures
        crate::node::spec_execute_notes(
            before, after, now, keys, count,
        ).to_set().subset_of(raw.to_set()),
    decreases count,
{
    if count > 0 {
        lemma_execute_notes_subset(
            before,
            after,
            now,
            keys,
            (count - 1) as nat,
            raw,
        );
        let prior = crate::node::spec_execute_notes(
            before, after, now, keys, (count - 1) as nat,
        );
        let id = keys[count as int - 1];
        if crate::document::offer_committed(
            before, after, id, now,
        ) {
            let note = NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            };
            assert(crate::node::spec_execute_notes(
                before, after, now, keys, count,
            ) == prior.push(note));
            assert forall|candidate: NoteV|
                crate::node::spec_execute_notes(
                    before, after, now, keys, count,
                ).to_set().contains(candidate) implies
                raw.to_set().contains(candidate) by {
                if candidate == note {
                    assert(raw.contains(note));
                } else {
                    assert(prior.to_set().contains(candidate));
                }
            };
        }
    }
}

pub proof fn lemma_unblock_notes_for_subset(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    promise: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
    raw: Seq<NoteV>,
)
    requires
        count <= listeners.len(),
        forall|address: Seq<char>|
            crate::document::listener_committed(
                before, after, promise, address,
            ) ==> raw.contains(NoteV::Unblock {
                address,
                promise: spec_record(
                    c_string(promise),
                    after[promise].promise,
                ),
            }),
    ensures
        crate::node::spec_unblock_notes_for(
            before, after, promise, listeners, count,
        ).to_set().subset_of(raw.to_set()),
    decreases count,
{
    if count > 0 {
        lemma_unblock_notes_for_subset(
            before,
            after,
            promise,
            listeners,
            (count - 1) as nat,
            raw,
        );
        let prior = crate::node::spec_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            (count - 1) as nat,
        );
        let address = listeners[count as int - 1];
        if crate::document::listener_committed(
            before, after, promise, address,
        ) {
            let note = NoteV::Unblock {
                address,
                promise: spec_record(
                    c_string(promise),
                    after[promise].promise,
                ),
            };
            assert(crate::node::spec_unblock_notes_for(
                before, after, promise, listeners, count,
            ) == prior.push(note));
            assert forall|candidate: NoteV|
                crate::node::spec_unblock_notes_for(
                    before, after, promise, listeners, count,
                ).to_set().contains(candidate) implies
                raw.to_set().contains(candidate) by {
                if candidate == note {
                    assert(raw.contains(note));
                } else {
                    assert(prior.to_set().contains(candidate));
                }
            };
        }
    }
}

pub proof fn lemma_unblock_notes_subset(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    raw: Seq<NoteV>,
)
    requires
        count <= keys.len(),
        forall|promise: Seq<char>, address: Seq<char>|
            crate::document::listener_committed(
                before, after, promise, address,
            ) ==> raw.contains(NoteV::Unblock {
                address,
                promise: spec_record(
                    c_string(promise),
                    after[promise].promise,
                ),
            }),
    ensures
        crate::node::spec_unblock_notes(
            before, after, keys, count,
        ).to_set().subset_of(raw.to_set()),
    decreases count,
{
    if count > 0 {
        lemma_unblock_notes_subset(
            before, after, keys, (count - 1) as nat, raw,
        );
        let prior = crate::node::spec_unblock_notes(
            before, after, keys, (count - 1) as nat,
        );
        let promise = keys[count as int - 1];
        lemma_unblock_notes_for_subset(
            before,
            after,
            promise,
            before[promise].promise.listeners,
            before[promise].promise.listeners.len(),
            raw,
        );
        let tail = crate::node::spec_unblock_notes_for(
            before,
            after,
            promise,
            before[promise].promise.listeners,
            before[promise].promise.listeners.len(),
        );
        assert forall|candidate: NoteV|
            (prior + tail).to_set().contains(candidate) implies
            raw.to_set().contains(candidate) by {
            if prior.to_set().contains(candidate) {
            } else {
                assert(tail.to_set().contains(candidate));
            }
        };
    }
}

pub proof fn lemma_committed_notes_subset(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    now: Time,
    raw: Seq<NoteV>,
)
    requires
        forall|id: Seq<char>|
            crate::document::offer_committed(
                before, after, id, now,
            ) ==> raw.contains(NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            }),
        forall|promise: Seq<char>, address: Seq<char>|
            crate::document::listener_committed(
                before, after, promise, address,
            ) ==> raw.contains(NoteV::Unblock {
                address,
                promise: spec_record(
                    c_string(promise),
                    after[promise].promise,
                ),
            }),
    ensures
        crate::node::spec_committed_notes(
            DocumentBodyV::Workflow(before),
            DocumentBodyV::Workflow(after),
            now,
        ).to_set().subset_of(raw.to_set()),
{
    let after_keys = spec_sorted_present(after);
    let before_keys = spec_sorted_present(before);
    lemma_execute_notes_subset(
        before, after, now, after_keys, after_keys.len(), raw,
    );
    lemma_unblock_notes_subset(
        before, after, before_keys, before_keys.len(), raw,
    );
    let executes = crate::node::spec_execute_notes(
        before, after, now, after_keys, after_keys.len(),
    );
    let unblocks = crate::node::spec_unblock_notes(
        before, after, before_keys, before_keys.len(),
    );
    assert forall|candidate: NoteV|
        (executes + unblocks).to_set().contains(candidate) implies
        raw.to_set().contains(candidate) by {
        if executes.to_set().contains(candidate) {
        } else {
            assert(unblocks.to_set().contains(candidate));
        }
    };
}

pub proof fn lemma_execute_notes_contains(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    now: Time,
    keys: Seq<Seq<char>>,
    count: nat,
    id: Seq<char>,
)
    requires
        count <= keys.len(),
        keys.take(count as int).contains(id),
        crate::document::offer_committed(
            before, after, id, now,
        ),
    ensures
        crate::node::spec_execute_notes(
            before, after, now, keys, count,
        ).contains(NoteV::Execute {
            id,
            version: after[id].task.unwrap().version,
        }),
    decreases count,
{
    reveal(crate::node::spec_execute_notes);
    if count > 0 {
        let prior_count = (count - 1) as nat;
        let last = keys[count as int - 1];
        let prior = crate::node::spec_execute_notes(
            before, after, now, keys, prior_count,
        );
        let current = crate::node::spec_execute_notes(
            before, after, now, keys, count,
        );
        if last == id {
            let note = NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            };
            assert(current == prior.push(note));
            assert(current[prior.len() as int] == note);
        } else {
            assert(keys.take(prior_count as int).contains(id));
            lemma_execute_notes_contains(
                before,
                after,
                now,
                keys,
                prior_count,
                id,
            );
            let note = NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            };
            let i = choose|i: int|
                0 <= i < prior.len() && prior[i] == note;
            if crate::document::offer_committed(
                before, after, last, now,
            ) {
                assert(current[i] == note);
            } else {
                assert(current == prior);
            }
        }
    }
}

pub proof fn lemma_unblock_notes_for_contains(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    promise: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
    address: Seq<char>,
)
    requires
        count <= listeners.len(),
        listeners.take(count as int).contains(address),
        crate::document::listener_committed(
            before, after, promise, address,
        ),
    ensures
        crate::node::spec_unblock_notes_for(
            before, after, promise, listeners, count,
        ).contains(NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(promise), after[promise].promise,
            ),
        }),
    decreases count,
{
    reveal(crate::node::spec_unblock_notes_for);
    if count > 0 {
        let prior_count = (count - 1) as nat;
        let last = listeners[count as int - 1];
        let prior = crate::node::spec_unblock_notes_for(
            before, after, promise, listeners, prior_count,
        );
        let current = crate::node::spec_unblock_notes_for(
            before, after, promise, listeners, count,
        );
        let note = NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(promise), after[promise].promise,
            ),
        };
        if last == address {
            assert(current == prior.push(note));
            assert(current[prior.len() as int] == note);
        } else {
            assert(listeners.take(prior_count as int)
                .contains(address));
            lemma_unblock_notes_for_contains(
                before,
                after,
                promise,
                listeners,
                prior_count,
                address,
            );
            let i = choose|i: int|
                0 <= i < prior.len() && prior[i] == note;
            if crate::document::listener_committed(
                before, after, promise, last,
            ) {
                assert(current[i] == note);
            } else {
                assert(current == prior);
            }
        }
    }
}

pub proof fn lemma_unblock_notes_contains(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    promise: Seq<char>,
    address: Seq<char>,
)
    requires
        count <= keys.len(),
        keys.take(count as int).contains(promise),
        crate::document::listener_committed(
            before, after, promise, address,
        ),
    ensures
        crate::node::spec_unblock_notes(
            before, after, keys, count,
        ).contains(NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(promise), after[promise].promise,
            ),
        }),
    decreases count,
{
    reveal(crate::node::spec_unblock_notes);
    if count > 0 {
        let prior_count = (count - 1) as nat;
        let last = keys[count as int - 1];
        let prior = crate::node::spec_unblock_notes(
            before, after, keys, prior_count,
        );
        let current = crate::node::spec_unblock_notes(
            before, after, keys, count,
        );
        let tail = crate::node::spec_unblock_notes_for(
            before,
            after,
            last,
            before[last].promise.listeners,
            before[last].promise.listeners.len(),
        );
        assert(current == prior + tail);
        if last == promise {
            assert(before[promise].promise.listeners
                .contains(address));
            assert(before[promise].promise.listeners.take(
                before[promise].promise.listeners.len() as int,
            ) == before[promise].promise.listeners);
            lemma_unblock_notes_for_contains(
                before,
                after,
                promise,
                before[promise].promise.listeners,
                before[promise].promise.listeners.len(),
                address,
            );
            lemma_contains_add(
                prior,
                tail,
                NoteV::Unblock {
                    address,
                    promise: spec_record(
                        c_string(promise),
                        after[promise].promise,
                    ),
                },
            );
        } else {
            assert(keys.take(prior_count as int)
                .contains(promise));
            lemma_unblock_notes_contains(
                before,
                after,
                keys,
                prior_count,
                promise,
                address,
            );
            let note = NoteV::Unblock {
                address,
                promise: spec_record(
                    c_string(promise), after[promise].promise,
                ),
            };
            lemma_contains_add(prior, tail, note);
        }
    }
}

pub proof fn lemma_committed_execute_contains(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    now: Time,
    id: Seq<char>,
)
    requires
        crate::document::offer_committed(
            before, after, id, now,
        ),
    ensures
        crate::node::spec_committed_notes(
            DocumentBodyV::Workflow(before),
            DocumentBodyV::Workflow(after),
            now,
        ).contains(NoteV::Execute {
            id,
            version: after[id].task.unwrap().version,
        }),
{
    let keys = spec_sorted_present(after);
    lemma_sorted(after.dom());
    assert(after.dom().contains(id));
    assert(keys.contains(id));
    assert(keys.take(keys.len() as int) == keys);
    lemma_execute_notes_contains(
        before, after, now, keys, keys.len(), id,
    );
    lemma_contains_add(
        crate::node::spec_execute_notes(
            before, after, now, keys, keys.len(),
        ),
        crate::node::spec_unblock_notes(
            before,
            after,
            spec_sorted_present(before),
            spec_sorted_present(before).len(),
        ),
        NoteV::Execute {
            id,
            version: after[id].task.unwrap().version,
        },
    );
}

pub proof fn lemma_committed_unblock_contains(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    now: Time,
    promise: Seq<char>,
    address: Seq<char>,
)
    requires
        crate::document::listener_committed(
            before, after, promise, address,
        ),
    ensures
        crate::node::spec_committed_notes(
            DocumentBodyV::Workflow(before),
            DocumentBodyV::Workflow(after),
            now,
        ).contains(NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(promise), after[promise].promise,
            ),
        }),
{
    let before_keys = spec_sorted_present(before);
    lemma_sorted(before.dom());
    assert(before.dom().contains(promise));
    assert(before_keys.contains(promise));
    assert(before_keys.take(before_keys.len() as int)
        == before_keys);
    lemma_unblock_notes_contains(
        before,
        after,
        before_keys,
        before_keys.len(),
        promise,
        address,
    );
    lemma_contains_add(
        crate::node::spec_execute_notes(
            before,
            after,
            now,
            spec_sorted_present(after),
            spec_sorted_present(after).len(),
        ),
        crate::node::spec_unblock_notes(
            before,
            after,
            before_keys,
            before_keys.len(),
        ),
        NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(promise), after[promise].promise,
            ),
        },
    );
}

pub proof fn lemma_note_sends_subset(
    notes: Seq<NoteV>,
    raw: Seq<NoteV>,
)
    requires
        notes.to_set().subset_of(raw.to_set()),
    ensures
        note_sends(notes).to_set()
            .subset_of(note_sends(raw).to_set()),
{
    assert forall|message: (echod_abstract::model::Pid, echod_abstract::protocol::Message)|
        note_sends(notes).to_set().contains(message) implies
        note_sends(raw).to_set().contains(message) by {
        let i = choose|i: int| 0 <= i < note_sends(notes).len()
            && #[trigger] note_sends(notes)[i] == message;
        let note = notes[i];
        assert(notes.to_set().contains(note));
        assert(raw.to_set().contains(note));
        let j = choose|j: int| 0 <= j < raw.len()
            && #[trigger] raw[j] == note;
        assert(note_sends(raw)[j] == message);
    };
}

pub proof fn lemma_sweep_listener_survives_or_committed(
    map: Map<Seq<char>, ObjV>,
    now: Time,
    retry_timeout: u64,
    id: Seq<char>,
    address: Seq<char>,
)
    requires
        map.contains_key(id),
        map[id].promise.listeners.contains(address),
    ensures
        ({
            let swept = spec_sweep(
                DocumentBodyV::Workflow(map),
                now,
                retry_timeout,
            ).0->Workflow_0;
            swept[id].promise.listeners.contains(address)
                || crate::document::listener_committed(
                    map, swept, id, address,
                )
        }),
{
    let keys = spec_sorted_present(map);
    let projected = crate::node::spec_project_keys(
        map, keys, keys.len(), now, retry_timeout,
    );
    let drain_keys = spec_sorted_present(projected);
    let resumed = crate::node::spec_drain_callback_keys(
        projected,
        drain_keys,
        drain_keys.len(),
        now,
        retry_timeout,
    );
    let closed = crate::node::spec_clear_listener_keys(
        resumed, drain_keys, drain_keys.len(),
    );
    crate::quick_n_dirty::lemma_project_keys_keeps_domain(
        map, keys, keys.len(), now, retry_timeout,
    );
    lemma_project_keys_preserves_listeners(
        map, keys, keys.len(), now, retry_timeout,
    );
    crate::quick_n_dirty::lemma_drain_callback_keys_keeps_domain(
        projected,
        drain_keys,
        drain_keys.len(),
        now,
        retry_timeout,
    );
    lemma_drain_callback_keys_preserves_listeners(
        projected,
        drain_keys,
        drain_keys.len(),
        now,
        retry_timeout,
    );
    crate::quick_n_dirty::lemma_clear_listener_keys_keeps_domain(
        resumed, drain_keys, drain_keys.len(),
    );
    crate::quick_n_dirty::lemma_clear_listener_keys_preserves_queue_source(
        resumed, drain_keys, drain_keys.len(),
    );
    if !closed[id].promise.listeners.contains(address) {
        if closed[id].promise.state == PromiseState::Pending {
            assert(resumed[id].promise.state
                == PromiseState::Pending);
            lemma_clear_listener_keys_preserves_pending_listener(
                resumed,
                drain_keys,
                drain_keys.len(),
                id,
                address,
            );
        }
        assert(crate::document::listener_committed(
            map, closed, id, address,
        )) by {
            reveal(crate::document::listener_committed);
        };
    }
    reveal(crate::node::spec_project_workflow);
    reveal(crate::node::spec_drain_workflow);
    reveal(spec_sweep);
}

#[verifier::spinoff_prover]
pub proof fn lemma_request_notes_covered(
    name: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    request: Request,
    now: Time,
    retry_timeout: u64,
)
    requires
        crate::node::spec_request_document(request)
            == Some(name),
        !matches!(request, Request::ScheduleGet(_)
            | Request::ScheduleCreate(_)
            | Request::ScheduleDelete(_)),
    ensures
        ({
            let original = DocumentBodyV::Workflow(map);
            let swept = spec_sweep(
                original, now, retry_timeout,
            ).0->Workflow_0;
            let handled = crate::node::spec_handle(
                DocumentBodyV::Workflow(swept),
                request,
                now,
            ).0->Workflow_0;
            let closed = spec_sweep(
                DocumentBodyV::Workflow(handled),
                now,
                retry_timeout,
            ).0->Workflow_0;
            let final_notes = crate::node::spec_committed_notes(
                original,
                DocumentBodyV::Workflow(closed),
                now,
            );
            let raw =
                crate::node::spec_committed_notes(
                    original,
                    DocumentBodyV::Workflow(swept),
                    now,
                ) + crate::node::spec_committed_notes(
                    DocumentBodyV::Workflow(handled),
                    DocumentBodyV::Workflow(closed),
                    now,
                );
            final_notes.to_set().subset_of(raw.to_set())
        }),
{
    let original = DocumentBodyV::Workflow(map);
    let swept_doc = spec_sweep(
        original, now, retry_timeout,
    ).0;
    let swept = swept_doc->Workflow_0;
    let handled_doc = crate::node::spec_handle(
        swept_doc, request, now,
    ).0;
    let handled = handled_doc->Workflow_0;
    let closed_doc = spec_sweep(
        handled_doc, now, retry_timeout,
    ).0;
    let closed = closed_doc->Workflow_0;
    let before_notes = crate::node::spec_committed_notes(
        original, swept_doc, now,
    );
    let after_notes = crate::node::spec_committed_notes(
        handled_doc, closed_doc, now,
    );
    let raw = before_notes + after_notes;
    crate::quick_n_dirty::lemma_sweep_keeps_domain(
        map, now, retry_timeout,
    );
    crate::quick_n_dirty::lemma_sweep_keeps_domain(
        handled, now, retry_timeout,
    );
    let handled_keys = spec_sorted_present(handled);
    let handled_projected = crate::node::spec_project_keys(
        handled,
        handled_keys,
        handled_keys.len(),
        now,
        retry_timeout,
    );
    let handled_drain_keys =
        spec_sorted_present(handled_projected);
    let handled_resumed = crate::node::spec_drain_callback_keys(
        handled_projected,
        handled_drain_keys,
        handled_drain_keys.len(),
        now,
        retry_timeout,
    );
    lemma_project_keys_preserves_task_versions(
        handled,
        handled_keys,
        handled_keys.len(),
        now,
        retry_timeout,
    );
    lemma_project_keys_pending_reflects(
        handled,
        handled_keys,
        handled_keys.len(),
        now,
        retry_timeout,
    );
    crate::quick_n_dirty::lemma_project_keys_keeps_domain(
        handled,
        handled_keys,
        handled_keys.len(),
        now,
        retry_timeout,
    );
    lemma_callback_keys_preserves_task_versions(
        handled_projected,
        handled_drain_keys,
        handled_drain_keys.len(),
        now,
        retry_timeout,
    );
    lemma_drain_callback_keys_preserves_listeners(
        handled_projected,
        handled_drain_keys,
        handled_drain_keys.len(),
        now,
        retry_timeout,
    );
    crate::quick_n_dirty::lemma_drain_callback_keys_keeps_domain(
        handled_projected,
        handled_drain_keys,
        handled_drain_keys.len(),
        now,
        retry_timeout,
    );
    lemma_clear_listener_keys_preserves_record(
        handled_resumed,
        handled_drain_keys,
        handled_drain_keys.len(),
    );
    crate::quick_n_dirty::lemma_clear_listener_keys_keeps_domain(
        handled_resumed,
        handled_drain_keys,
        handled_drain_keys.len(),
    );
    crate::quick_n_dirty::lemma_clear_listener_keys_preserves_queue_source(
        handled_resumed,
        handled_drain_keys,
        handled_drain_keys.len(),
    );
    reveal(crate::node::spec_project_workflow);
    reveal(crate::node::spec_drain_workflow);
    reveal(spec_sweep);
    assert(handled_projected
        == crate::node::spec_project_workflow(
            handled, now, retry_timeout,
        ));
    assert(closed
        == crate::node::spec_clear_listener_keys(
            handled_resumed,
            handled_drain_keys,
            handled_drain_keys.len(),
        ));
    assert forall|id: Seq<char>|
        #[trigger] closed.contains_key(id)
            && closed[id].task is Some implies
        {
            &&& handled.contains_key(id)
            &&& handled[id].task is Some
            &&& handled[id].task.unwrap().version
                == closed[id].task.unwrap().version
        } by {
        assert(closed[id].task == handled_resumed[id].task);
        assert(handled_resumed[id].task.unwrap().version
            == handled_projected[id].task.unwrap().version);
        assert(handled_projected[id].task.unwrap().version
            == handled[id].task.unwrap().version);
    };
    assert forall|id: Seq<char>|
        #[trigger] closed.contains_key(id)
            && closed[id].promise.state
                == PromiseState::Pending implies
        handled[id].promise.state
            == PromiseState::Pending by {
        assert(handled_resumed[id].promise.state
            == closed[id].promise.state);
        assert(spec_record(
            c_string(id), handled_resumed[id].promise,
        ) == spec_record(
            c_string(id), handled_projected[id].promise,
        ));
        reveal(spec_record);
    };
    assert forall|id: Seq<char>|
        crate::document::offer_committed(
            map, closed, id, now,
        ) implies raw.contains(NoteV::Execute {
            id,
            version: closed[id].task.unwrap().version,
        }) by {
        let note = NoteV::Execute {
            id,
            version: closed[id].task.unwrap().version,
        };
        if crate::document::offer_committed(
            map, swept, id, now,
        ) && swept[id].task.unwrap().version
            == closed[id].task.unwrap().version
        {
            lemma_committed_execute_contains(
                map, swept, now, id,
            );
        } else {
            crate::quick_n_dirty::lemma_handle_preserves_future_offer(
                swept, request, now, id,
            );
            assert(crate::document::offer_committed(
                handled, closed, id, now,
            )) by {
                reveal(crate::document::offer_committed);
                reveal(crate::quick_n_dirty::future_offer_preserved);
                match request {
                    Request::PromiseGet(_)
                    | Request::PromiseCreate(_)
                    | Request::PromiseSettle(_)
                    | Request::PromiseRegisterCallback(_)
                    | Request::PromiseRegisterListener(_)
                    | Request::TaskGet(_)
                    | Request::TaskCreate(_)
                    | Request::TaskAcquire(_)
                    | Request::TaskFulfill(_)
                    | Request::TaskRelease(_)
                    | Request::TaskHalt(_)
                    | Request::TaskContinue(_)
                    | Request::TaskHeartbeat(_)
                    | Request::TaskSuspend(_)
                    | Request::TaskFence(_)
                    | Request::TaskFenceCheck(_) => {},
                    _ => {},
                }
            };
            lemma_committed_execute_contains(
                handled, closed, now, id,
            );
        }
        lemma_contains_add(before_notes, after_notes, note);
    };
    assert forall|promise: Seq<char>, address: Seq<char>|
        crate::document::listener_committed(
            map, closed, promise, address,
        ) implies raw.contains(NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(promise), closed[promise].promise,
            ),
        }) by {
        let note = NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(promise), closed[promise].promise,
            ),
        };
        lemma_sweep_listener_survives_or_committed(
            map, now, retry_timeout, promise, address,
        );
        if crate::document::listener_committed(
            map, swept, promise, address,
        ) {
            crate::quick_n_dirty::lemma_handle_preserves_settled_record(
                swept, request, now, promise,
            );
            lemma_sweep_preserves_settled_record(
                handled, now, retry_timeout, promise,
            );
            assert(spec_record(
                c_string(promise), swept[promise].promise,
            ) == spec_record(
                c_string(promise), closed[promise].promise,
            ));
        }
        if crate::document::listener_committed(
            map, swept, promise, address,
        ) && spec_record(
            c_string(promise), swept[promise].promise,
        ) == spec_record(
            c_string(promise), closed[promise].promise,
        ) {
            lemma_committed_unblock_contains(
                map, swept, now, promise, address,
            );
        } else {
            assert(swept.contains_key(promise));
            assert(swept[promise].promise.listeners
                .contains(address));
            crate::quick_n_dirty::lemma_handle_preserves_listener(
                swept, request, now, promise, address,
            );
            assert(crate::document::listener_committed(
                handled, closed, promise, address,
            )) by {
                match request {
                    Request::PromiseGet(_)
                    | Request::PromiseCreate(_)
                    | Request::PromiseSettle(_)
                    | Request::PromiseRegisterCallback(_)
                    | Request::PromiseRegisterListener(_)
                    | Request::TaskGet(_)
                    | Request::TaskCreate(_)
                    | Request::TaskAcquire(_)
                    | Request::TaskFulfill(_)
                    | Request::TaskRelease(_)
                    | Request::TaskHalt(_)
                    | Request::TaskContinue(_)
                    | Request::TaskHeartbeat(_)
                    | Request::TaskSuspend(_)
                    | Request::TaskFence(_)
                    | Request::TaskFenceCheck(_) => {},
                    _ => {},
                }
            };
            lemma_committed_unblock_contains(
                handled, closed, now, promise, address,
            );
        }
        lemma_contains_add(before_notes, after_notes, note);
    };
    lemma_committed_notes_subset(map, closed, now, raw);
}

pub proof fn lemma_clear_listener_keys_preserves_unlisted(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    id: Seq<char>,
)
    requires
        count <= keys.len(),
        !keys.take(count as int).contains(id),
    ensures
        crate::node::spec_clear_listener_keys(
            map, keys, count,
        ).contains_key(id) == map.contains_key(id),
        map.contains_key(id) ==>
            crate::node::spec_clear_listener_keys(
                map, keys, count,
            )[id] == map[id],
    decreases count,
{
    if count > 0 {
        lemma_clear_listener_keys_preserves_unlisted(
            map, keys, (count - 1) as nat, id,
        );
        let last = keys[count as int - 1];
        assert(keys.take(count as int)
            == keys.take(count as int - 1).push(last));
        if last == id {
            lemma_singleton_contains(id);
            lemma_contains_add(
                keys.take(count as int - 1),
                seq![id],
                id,
            );
            assert(keys.take(count as int - 1).push(id)
                =~= keys.take(count as int - 1) + seq![id]);
            assert(keys.take(count as int).contains(id));
        }
        assert(last != id);
        reveal(crate::node::spec_clear_settled_listeners);
    }
}

pub proof fn lemma_drain_callback_keys_preserves_listeners(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
    ensures
        ({
            let next = crate::node::spec_drain_callback_keys(
                map, keys, count, now, retry_timeout,
            );
            forall|id: Seq<char>|
                #[trigger] next.contains_key(id) ==>
                {
                    &&& next[id].promise.listeners
                        == map[id].promise.listeners
                    &&& spec_record(
                        c_string(id), next[id].promise,
                    ) == spec_record(
                        c_string(id), map[id].promise,
                    )
                }
        }),
    decreases count,
{
    if count > 0 {
        lemma_drain_callback_keys_preserves_listeners(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        crate::quick_n_dirty::lemma_drain_callback_keys_keeps_domain(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_drain_callback_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let id = keys[count as int - 1];
        reveal(crate::node::spec_drain_settled_callbacks);
        if prior.contains_key(id)
            && prior[id].promise.state != PromiseState::Pending
        {
            let callback_count =
                prior[id].promise.callbacks.len();
            crate::quick_n_dirty::lemma_drain_callbacks_preserves_other_promises(
                prior,
                id,
                callback_count,
                now,
                retry_timeout,
            );
            lemma_callback_drain_length(
                prior,
                id,
                callback_count,
                now,
                retry_timeout,
            );
            crate::quick_n_dirty::lemma_drain_callbacks_keeps_domain(
                prior,
                id,
                callback_count,
                now,
                retry_timeout,
            );
            crate::quick_n_dirty::lemma_drain_callbacks_preserves_record(
                prior,
                id,
                callback_count,
                now,
                retry_timeout,
            );
        }
        let next = crate::node::spec_drain_settled_callbacks(
            prior, id, now, retry_timeout,
        );
        assert forall|other: Seq<char>|
            #[trigger] next.contains_key(other) implies
            {
                &&& next[other].promise.listeners
                    == map[other].promise.listeners
                &&& spec_record(
                    c_string(other), next[other].promise,
                ) == spec_record(
                    c_string(other), map[other].promise,
                )
            } by {
            if other == id {
            } else if prior.contains_key(id)
                && prior[id].promise.state
                    != PromiseState::Pending
            {
                assert(next[other].promise
                    == prior[other].promise);
            } else {
                assert(next == prior);
            }
        };
    }
}

pub proof fn lemma_project_keys_preserves_listeners(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
    ensures
        ({
            let next = crate::node::spec_project_keys(
                map, keys, count, now, retry_timeout,
            );
            forall|id: Seq<char>|
                #[trigger] next.contains_key(id) ==>
                next[id].promise.listeners
                    == map[id].promise.listeners
        }),
    decreases count,
{
    if count > 0 {
        lemma_project_keys_preserves_listeners(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        crate::quick_n_dirty::lemma_project_keys_keeps_domain(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = crate::node::spec_project_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let id = keys[count as int - 1];
        reveal(crate::node::spec_project_due_object);
        if prior.contains_key(id) {
            assert(crate::node::spec_project_prom(
                prior[id].promise, now,
            ).listeners == prior[id].promise.listeners);
        }
    }
}

pub proof fn lemma_clear_listener_keys_preserves_pending_listener(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    id: Seq<char>,
    address: Seq<char>,
)
    requires
        count <= keys.len(),
        map.contains_key(id),
        map[id].promise.state == PromiseState::Pending,
        map[id].promise.listeners.contains(address),
    ensures
        ({
            let next = crate::node::spec_clear_listener_keys(
                map, keys, count,
            );
            &&& next.contains_key(id)
            &&& next[id].promise.state == PromiseState::Pending
            &&& next[id].promise.listeners.contains(address)
        }),
    decreases count,
{
    if count > 0 {
        lemma_clear_listener_keys_preserves_pending_listener(
            map,
            keys,
            (count - 1) as nat,
            id,
            address,
        );
        let prior = crate::node::spec_clear_listener_keys(
            map, keys, (count - 1) as nat,
        );
        let last = keys[count as int - 1];
        reveal(crate::node::spec_clear_settled_listeners);
        if last != id {
            assert(crate::node::spec_clear_settled_listeners(
                prior, last,
            )[id] == prior[id]);
        } else {
            assert(crate::node::spec_clear_settled_listeners(
                prior, last,
            ) == prior);
        }
    }
}

pub proof fn lemma_project_keys_preserves_settled_record(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
    id: Seq<char>,
)
    requires
        count <= keys.len(),
        map.contains_key(id),
        map[id].promise.state != PromiseState::Pending,
    ensures
        ({
            let next = crate::node::spec_project_keys(
                map, keys, count, now, retry_timeout,
            );
            &&& next.contains_key(id)
            &&& next[id].promise.state
                == map[id].promise.state
            &&& spec_record(
                c_string(id), next[id].promise,
            ) == spec_record(
                c_string(id), map[id].promise,
            )
        }),
    decreases count,
{
    crate::quick_n_dirty::lemma_project_keys_keeps_domain(
        map, keys, count, now, retry_timeout,
    );
    if count > 0 {
        lemma_project_keys_preserves_settled_record(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
            id,
        );
        let prior = crate::node::spec_project_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let current = keys[count as int - 1];
        reveal(crate::node::spec_project_due_object);
        if current == id {
            assert(prior[id].promise.state
                != PromiseState::Pending);
        }
    }
}

pub proof fn lemma_clear_listener_keys_preserves_record(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= keys.len(),
    ensures
        ({
            let next = crate::node::spec_clear_listener_keys(
                map, keys, count,
            );
            forall|id: Seq<char>|
                #[trigger] next.contains_key(id) ==>
                {
                    &&& spec_record(c_string(id), next[id].promise)
                        == spec_record(c_string(id), map[id].promise)
                    &&& next[id].task == map[id].task
                }
        }),
    decreases count,
{
    if count > 0 {
        lemma_clear_listener_keys_preserves_record(
            map, keys, (count - 1) as nat,
        );
        let prior = crate::node::spec_clear_listener_keys(
            map, keys, (count - 1) as nat,
        );
        let id = keys[count as int - 1];
        reveal(crate::node::spec_clear_settled_listeners);
        assert forall|other: Seq<char>|
            #[trigger] crate::node::spec_clear_settled_listeners(
                prior, id,
            ).contains_key(other) implies
            {
                &&& spec_record(
                    c_string(other),
                    crate::node::spec_clear_settled_listeners(
                        prior, id,
                    )[other].promise,
                ) == spec_record(
                    c_string(other), map[other].promise,
                )
                &&& crate::node::spec_clear_settled_listeners(
                    prior, id,
                )[other].task == map[other].task
            } by {
            if other != id {
                assert(crate::node::spec_clear_settled_listeners(
                    prior, id,
                )[other] == prior[other]);
            }
        };
    }
}

pub proof fn lemma_sweep_preserves_settled_record(
    map: Map<Seq<char>, ObjV>,
    now: Time,
    retry_timeout: u64,
    id: Seq<char>,
)
    requires
        map.contains_key(id),
        map[id].promise.state != PromiseState::Pending,
    ensures
        ({
            let swept = spec_sweep(
                DocumentBodyV::Workflow(map),
                now,
                retry_timeout,
            ).0->Workflow_0;
            &&& swept.contains_key(id)
            &&& spec_record(
                c_string(id), swept[id].promise,
            ) == spec_record(
                c_string(id), map[id].promise,
            )
        }),
{
    let keys = spec_sorted_present(map);
    let projected = crate::node::spec_project_keys(
        map, keys, keys.len(), now, retry_timeout,
    );
    let resumed = crate::node::spec_drain_callback_keys(
        projected, keys, keys.len(), now, retry_timeout,
    );
    crate::quick_n_dirty::lemma_project_keys_keeps_domain(
        map, keys, keys.len(), now, retry_timeout,
    );
    lemma_project_keys_preserves_settled_record(
        map,
        keys,
        keys.len(),
        now,
        retry_timeout,
        id,
    );
    lemma_drain_callback_keys_preserves_listeners(
        projected,
        keys,
        keys.len(),
        now,
        retry_timeout,
    );
    crate::quick_n_dirty::lemma_drain_callback_keys_keeps_domain(
        projected,
        keys,
        keys.len(),
        now,
        retry_timeout,
    );
    lemma_clear_listener_keys_preserves_record(
        resumed, keys, keys.len(),
    );
    crate::quick_n_dirty::lemma_clear_listener_keys_keeps_domain(
        resumed, keys, keys.len(),
    );
    let closed = crate::node::spec_clear_listener_keys(
        resumed, keys, keys.len(),
    );
    assert(projected.contains_key(id));
    assert(resumed.contains_key(id));
    assert(spec_record(
        c_string(id), resumed[id].promise,
    ) == spec_record(
        c_string(id), projected[id].promise,
    ));
    assert(closed.contains_key(id));
    assert(spec_record(
        c_string(id), closed[id].promise,
    ) == spec_record(
        c_string(id), resumed[id].promise,
    ));
    reveal(crate::node::spec_project_workflow);
    reveal(crate::node::spec_drain_workflow);
    reveal(spec_sweep);
    assert(projected.dom() == map.dom());
    assert(spec_sorted_present(projected) == keys);
    assert(crate::node::spec_project_workflow(
        map, now, retry_timeout,
    ) == projected);
    assert(crate::node::spec_drain_workflow(
        projected, now, retry_timeout,
    ) == closed);
    assert(spec_sweep(
        DocumentBodyV::Workflow(map),
        now,
        retry_timeout,
    ).0 == DocumentBodyV::Workflow(
        closed,
    ));
}

pub proof fn lemma_listener_fold_notes_contains(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
    address: Seq<char>,
)
    requires
        count <= listeners.len(),
        listeners.take(count as int).contains(address),
    ensures
        spec_listener_fold_notes(
            map, id, listeners, count,
        ).contains(NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(id), map[id].promise,
            ),
        }),
{
    let i = choose|i: int|
        0 <= i < listeners.take(count as int).len()
            && listeners.take(count as int)[i] == address;
    assert(spec_listener_fold_notes(
        map, id, listeners, count,
    )[i] == NoteV::Unblock {
        address,
        promise: spec_record(
            c_string(id), map[id].promise,
        ),
    });
}

pub proof fn lemma_listener_keys_notes_cover(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    promise: Seq<char>,
    address: Seq<char>,
)
    requires
        count <= keys.len(),
        keys.take(count as int).no_duplicates(),
        keys.take(count as int).contains(promise),
        map.contains_key(promise),
        map[promise].promise.state != PromiseState::Pending,
        map[promise].promise.listeners.contains(address),
    ensures
        spec_listener_keys_notes(
            map, keys, count,
        ).contains(NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(promise), map[promise].promise,
            ),
        }),
    decreases count,
{
    if count > 0 {
        let last = keys[count as int - 1];
        let prior_keys = keys.take(count as int - 1);
        assert(keys.take(count as int)
            == prior_keys.push(last));
        crate::effects::lemma_nodup_last_not_in_prefix(
            keys, count,
        );
        if last == promise {
            assert(!prior_keys.contains(promise));
            lemma_clear_listener_keys_preserves_unlisted(
                map, keys, (count - 1) as nat, promise,
            );
            let prior = crate::node::spec_clear_listener_keys(
                map, keys, (count - 1) as nat,
            );
            assert(prior[promise] == map[promise]);
            assert(prior[promise].promise.listeners.take(
                prior[promise].promise.listeners.len() as int,
            ) == prior[promise].promise.listeners);
            lemma_listener_fold_notes_contains(
                prior,
                promise,
                prior[promise].promise.listeners,
                prior[promise].promise.listeners.len(),
                address,
            );
            let object_notes =
                spec_listener_object_notes(prior, promise);
            assert(object_notes.contains(NoteV::Unblock {
                address,
                promise: spec_record(
                    c_string(promise), map[promise].promise,
                ),
            }));
            lemma_contains_add(
                spec_listener_keys_notes(
                    map, keys, (count - 1) as nat,
                ),
                object_notes,
                NoteV::Unblock {
                    address,
                    promise: spec_record(
                        c_string(promise), map[promise].promise,
                    ),
                },
            );
        } else {
            assert(prior_keys.contains(promise));
            lemma_listener_keys_notes_cover(
                map,
                keys,
                (count - 1) as nat,
                promise,
                address,
            );
            lemma_contains_add(
                spec_listener_keys_notes(
                    map, keys, (count - 1) as nat,
                ),
                spec_listener_object_notes(
                    crate::node::spec_clear_listener_keys(
                        map, keys, (count - 1) as nat,
                    ),
                    last,
                ),
                NoteV::Unblock {
                    address,
                    promise: spec_record(
                        c_string(promise), map[promise].promise,
                    ),
                },
            );
        }
    }
}

pub proof fn lemma_phase2_fold_matches(
    config: ServerConfig,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    state: StateV,
    now: Time,
)
    requires
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
        count <= keys.len(),
        forall|i: int| 0 <= i < count ==>
            map.contains_key(#[trigger] keys[i]),
    ensures
        ({
            let resumed =
                crate::node::spec_drain_callback_keys(
                    map,
                    keys,
                    count,
                    now,
                    config.retry_timeout,
                );
            let next = crate::node::spec_clear_listener_keys(
                resumed, keys, count,
            );
            let works = spec_phase2_work(
                map,
                keys,
                count,
                now,
                config.retry_timeout,
            );
            let trace =
                spec_timeout_trace(config, state, now, works);
            &&& timeout_trace_legal(
                config, state, now, works,
            )
            &&& trace.state.pending == state.pending
            &&& trace.send == note_sends(spec_phase2_notes(
                map,
                keys,
                count,
                now,
                config.retry_timeout,
            ))
            &&& origin_rel(
                next, origin_chars, trace.state.store,
            )
            &&& changed_within(
                state.store, trace.state.store, origin_chars,
            )
            &&& finite_store(trace.state.store)
            &&& next.dom() == map.dom()
        }),
{
    lemma_callback_keys_matches(
        config,
        origin_chars,
        map,
        keys,
        count,
        state,
        now,
    );
    let callback_work = spec_callback_keys_work(
        map,
        keys,
        count,
        now,
        config.retry_timeout,
    );
    let callback_trace = spec_timeout_trace(
        config, state, now, callback_work,
    );
    let resumed = crate::node::spec_drain_callback_keys(
        map,
        keys,
        count,
        now,
        config.retry_timeout,
    );
    assert forall|i: int| 0 <= i < count implies
        resumed.contains_key(#[trigger] keys[i]) by {
    };
    lemma_listener_keys_matches(
        config,
        origin_chars,
        resumed,
        keys,
        count,
        callback_trace.state,
        now,
    );
    let listener_work =
        spec_listener_keys_work(resumed, keys, count);
    lemma_timeout_trace_add(
        config,
        state,
        now,
        callback_work,
        listener_work,
    );
}

// ---------------------------------------------------------------------------
// One atomic workflow sweep
// ---------------------------------------------------------------------------

pub proof fn lemma_origin_due(
    config: ServerConfig,
    key: Seq<char>,
    origin_chars: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
)
    requires
        key == spec_origin_key(origin_chars),
        origin_rel(map, origin_chars, state.store),
        finite_store(state.store),
    ensures
        due_agrees(
            config,
            key,
            DocumentBodyV::Workflow(map),
            state,
            now,
        ),
{
    let keys = spec_sorted_present(map);
    lemma_sorted(map.dom());
    assert forall|i: int| 0 <= i < keys.len() implies
        map.contains_key(#[trigger] keys[i]) by {
        assert(map.dom().contains(keys[i]));
    };
    lemma_phase1_fold_matches(
        config,
        origin_chars,
        map,
        keys,
        keys.len(),
        state,
        now,
    );
    let phase1_work = spec_phase1_work(keys, keys.len());
    let phase1 = spec_timeout_trace(
        config, state, now, phase1_work,
    );
    let projected = spec_project_keys(
        map,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    crate::quick_n_dirty::lemma_project_keys_keeps_domain(
        map,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    assert forall|i: int| 0 <= i < keys.len() implies
        projected.contains_key(#[trigger] keys[i]) by {
    };
    lemma_phase2_fold_matches(
        config,
        origin_chars,
        projected,
        keys,
        keys.len(),
        phase1.state,
        now,
    );
    let phase2_work = spec_phase2_work(
        projected,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    lemma_timeout_trace_add(
        config,
        state,
        now,
        phase1_work,
        phase2_work,
    );
    let work = phase1_work + phase2_work;
    let trace = spec_timeout_trace(config, state, now, work);
    lemma_phase1_work_is_workflow(keys, keys.len());
    lemma_callback_keys_work_is_workflow(
        projected,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    let resumed = crate::node::spec_drain_callback_keys(
        projected,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    crate::quick_n_dirty::lemma_drain_callback_keys_keeps_domain(
        projected,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    let drained = crate::node::spec_clear_listener_keys(
        resumed, keys, keys.len(),
    );
    assert forall|i: int| 0 <= i < keys.len() implies
        resumed.contains_key(#[trigger] keys[i]) by {
    };
    lemma_listener_keys_work_is_workflow(
        resumed, keys, keys.len(),
    );
    assert forall|i: int| 0 <= i < work.len() implies
        workflow_timeout_work(#[trigger] work[i]) by {
        if i < phase1_work.len() {
            assert(work[i] == phase1_work[i]);
        } else {
            assert(work[i]
                == phase2_work[i - phase1_work.len()]);
            let callback_work = spec_callback_keys_work(
                projected,
                keys,
                keys.len(),
                now,
                config.retry_timeout,
            );
            let listener_work = spec_listener_keys_work(
                resumed, keys, keys.len(),
            );
            if i - phase1_work.len() < callback_work.len() {
                assert(phase2_work[i - phase1_work.len()]
                    == callback_work[
                        i - phase1_work.len()
                    ]);
            } else {
                assert(phase2_work[i - phase1_work.len()]
                    == listener_work[
                        i - phase1_work.len()
                            - callback_work.len()
                    ]);
            }
        }
    };
    lemma_workflow_trace_keeps_schedules(
        config, state, now, work,
    );
    let before = DocumentBodyV::Workflow(map);
    let after = DocumentBodyV::Workflow(drained);
    let notes = crate::node::spec_committed_notes(
        before, after, now,
    );
    let raw_notes = spec_phase1_notes(
        map,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    ) + spec_phase2_notes(
        projected,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    crate::effects::lemma_sorted_no_duplicates(map.dom());
    lemma_phase1_notes_cover(
        map,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    lemma_callback_keys_notes_cover(
        projected,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    lemma_callback_keys_preserves_task_versions(
        projected,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    lemma_project_keys_preserves_listeners(
        map,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    lemma_drain_callback_keys_preserves_listeners(
        projected,
        keys,
        keys.len(),
        now,
        config.retry_timeout,
    );
    crate::quick_n_dirty::lemma_clear_listener_keys_preserves_queue_source(
        resumed, keys, keys.len(),
    );
    lemma_clear_listener_keys_preserves_record(
        resumed, keys, keys.len(),
    );
    assert forall|id: Seq<char>|
        crate::document::offer_committed(
            map, drained, id, now,
        ) implies raw_notes.contains(NoteV::Execute {
            id,
            version: drained[id].task.unwrap().version,
        }) by {
        assert(drained[id].task == resumed[id].task);
        let phase1_notes = spec_phase1_notes(
            map,
            keys,
            keys.len(),
            now,
            config.retry_timeout,
        );
        let callback_notes = spec_callback_keys_notes(
            projected,
            keys,
            keys.len(),
            now,
            config.retry_timeout,
        );
        let listener_notes = spec_listener_keys_notes(
            resumed, keys, keys.len(),
        );
        let note = NoteV::Execute {
            id,
            version: drained[id].task.unwrap().version,
        };
        if crate::document::offer_committed(
            map, projected, id, now,
        ) {
            assert(phase1_notes.contains(NoteV::Execute {
                id,
                version: projected[id].task.unwrap().version,
            }));
            assert(projected[id].task.unwrap().version
                == drained[id].task.unwrap().version);
        } else {
            assert(crate::document::offer_committed(
                projected, resumed, id, now,
            ));
            assert(callback_notes.contains(NoteV::Execute {
                id,
                version: resumed[id].task.unwrap().version,
            }));
        }
        lemma_contains_add(callback_notes, listener_notes, note);
        lemma_contains_add(
            phase1_notes,
            callback_notes + listener_notes,
            note,
        );
    };
    assert forall|promise: Seq<char>, address: Seq<char>|
        crate::document::listener_committed(
            map, drained, promise, address,
        ) implies raw_notes.contains(NoteV::Unblock {
            address,
            promise: spec_record(
                c_string(promise),
                drained[promise].promise,
            ),
        }) by {
        assert(map.contains_key(promise));
        assert(map.dom().contains(promise));
        assert(keys.contains(promise));
        assert(keys.take(keys.len() as int) == keys);
        assert(keys.take(keys.len() as int).contains(promise));
        assert(resumed.contains_key(promise));
        assert(resumed[promise].promise.state
            == drained[promise].promise.state);
        assert(resumed[promise].promise.listeners
            == map[promise].promise.listeners);
        lemma_listener_keys_notes_cover(
            resumed,
            keys,
            keys.len(),
            promise,
            address,
        );
        assert(spec_record(
            c_string(promise), drained[promise].promise,
        ) == spec_record(
            c_string(promise), resumed[promise].promise,
        ));
        let listener_notes =
            spec_listener_keys_notes(
                resumed, keys, keys.len(),
            );
        let phase2_notes = spec_phase2_notes(
            projected,
            keys,
            keys.len(),
            now,
            config.retry_timeout,
        );
        lemma_contains_add(
            spec_callback_keys_notes(
                projected,
                keys,
                keys.len(),
                now,
                config.retry_timeout,
            ),
            listener_notes,
            NoteV::Unblock {
                address,
                promise: spec_record(
                    c_string(promise),
                    drained[promise].promise,
                ),
            },
        );
        lemma_contains_add(
            spec_phase1_notes(
                map,
                keys,
                keys.len(),
                now,
                config.retry_timeout,
            ),
            phase2_notes,
            NoteV::Unblock {
                address,
                promise: spec_record(
                    c_string(promise),
                    drained[promise].promise,
                ),
            },
        );
    };
    lemma_committed_notes_subset(map, drained, now, raw_notes);
    lemma_note_sends_subset(notes, raw_notes);
    assert(trace.send == note_sends(raw_notes));
    assert(note_sends(notes).to_set()
        .subset_of(trace.send.to_set()));
    assert(trace.state.pending == state.pending);
    assert(doc_rel(key, after, trace.state.store)) by {
        lemma_origin_reads(
            key, origin_chars, drained, trace.state.store,
        );
    };
    assert(trace.state.store.schedules
        == state.store.schedules);
    lemma_others_kept_within(
        state.store, trace.state.store, origin_chars,
    );
    assert(spec_due_transition(
        before, now, config.retry_timeout,
    ) == (after, None::<Response>, Seq::<PendingV>::empty(), notes));
    assert(due_agrees(config, key, before, state, now));
}

// ---------------------------------------------------------------------------
// The due step of a schedule
// ---------------------------------------------------------------------------

/// A schedule whose run is due: both sides advance it and queue the
/// occurrence.
pub proof fn lemma_schedule_due(
    config: ServerConfig,
    key: Seq<char>,
    id: Seq<char>,
    sch: Schedule,
    state: StateV,
    now: Time,
)
    requires
        key == spec_schedule_key(id),
        slot_rel(Some(sch), id, state.store),
        finite_store(state.store),
        sch.next_run_at <= now,
        sch.next_run_at <= MAX_TIME,
        echod_types::spec_deadline_bounded(
            sch.next_run_at,
            sch.promise_timeout,
        ),
        ({
            let promise = echod_abstract::trusted::spec_expand(
                sch.promise_id@,
                sch.id@,
                sch.next_run_at,
            );
            &&& promise.len() <= usize::MAX as int
            &&& exists|carrier: String| carrier@ == promise
        }),
    ensures
        due_agrees(config, key, DocumentBodyV::Schedule(Some(sch)), state, now),
        schedule_due_exact(
            config,
            key,
            DocumentBodyV::Schedule(Some(sch)),
            state,
            now,
        ),
{
    let s = state.store;
    let doc = DocumentBodyV::Schedule(Some(sch));
    assert(s.schedules.contains_key(id));
    let c = s.schedules[id];
    assert(schedule_rel(sch, c));
    assert(sch.id@ == id);
    let at = sch.next_run_at;
    assert(c.next_run_at == at);
    let work = schedule_work(s, id);
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    let outcome = spec_process_work(config, work, s, now);
    assert(outcome == spec_schedule_step(s, id, now));
    let d = ScheduleV { last_run_at: Some(at), next_run_at: spec_next_cron(c.cron, at), ..c };
    let occ = Sched::Timer(
        at,
        InternalV::Occurrence {
            promise: spec_expand(c.promise_id, id, at),
            at,
            timeout: c.promise_timeout,
            param: c.promise_param,
            tags: c.promise_tags,
        },
    );
    let n = AStore { schedules: s.schedules.insert(id, d), ..s };
    assert(outcome == spec_did(n, seq![occ], Seq::empty()));
    let r = spec_due_result(state, outcome);
    let (next, _, born, notes) = spec_due_transition(doc, now, config.retry_timeout);
    let pending = PendingV {
        promise: spec_expand(sch.promise_id@, sch.id@, at),
        at,
        timeout: sch.promise_timeout,
        param: sch.promise_param,
        tags: sch.promise_tags,
    };
    let sch2 = Schedule { last_run_at: Some(at), next_run_at: spec_next_cron(sch.cron@, at), ..sch };
    assert(next == DocumentBodyV::Schedule(Some(sch2)));
    assert(born == seq![pending]);
    assert(notes.len() == 0);
    lemma_sends_none();
    lemma_sends_of(state, outcome);
    assert(r.send == sends_of(Seq::empty()));
    assert(r.send == note_sends(notes)) by {
        assert(notes =~= Seq::<NoteV>::empty());
    };
    assert(as_item(pending) == occ);
    assert(items(born) =~= seq![occ]);
    assert(r.state.pending == state.pending + items(born));
    assert(schedule_rel(sch2, d));
    assert(slot_rel(Some(sch2), id, n));
    lemma_schedule_key(id);
    assert(doc_rel(key, next, n));
    lemma_others_kept_schedule(s, n, id);
    assert(n.schedules.dom() == s.schedules.dom().insert(id));
    assert(finite_store(n));
    lemma_one_timeout_legal(config, state, now, work);
    lemma_one_timeout_result(config, state, now, work);
    let work_seq = seq![work];
    let trace =
        spec_timeout_trace(config, state, now, work_seq);
    assert(trace.state == r.state);
    assert(trace.send == r.send);
    assert(crate::interpret::others_kept(key, s, n));
    assert(exists|works: Seq<InternalV>|
        #[trigger] timeout_trace_legal(
            config, state, now, works,
        ) && {
        let matched =
            spec_timeout_trace(config, state, now, works);
        &&& matched.send == note_sends(notes)
        &&& matched.state.pending
            == state.pending + items(born)
        &&& doc_rel(key, next, matched.state.store)
        &&& crate::interpret::others_kept(
            key, state.store, matched.state.store,
        )
        &&& finite_store(matched.state.store)
    }) by {
        assert(timeout_trace_legal(
            config, state, now, work_seq,
        ));
    };
    assert(results.contains(r));
    let j = choose|j: int|
        0 <= j < results.len() && results[j] == r;
    assert(schedule_due_exact(
        config, key, doc, state, now,
    ));
}

/// A changing transition that creates one occurrence is necessarily a
/// schedule fire, and therefore has one exact abstract timeout result.
pub proof fn lemma_changing_schedule_due_exact(
    config: ServerConfig,
    key: Seq<char>,
    doc: DocumentBodyV,
    state: StateV,
    now: Time,
)
    requires
        doc_rel(key, doc, state.store),
        finite_store(state.store),
        ({
            let transition =
                spec_due_transition(
                    doc, now, config.retry_timeout,
                );
            &&& transition.0 != doc
            &&& transition.2.len() == 1
        }),
    ensures
        schedule_due_exact(config, key, doc, state, now),
{
    if spec_starts(key, schedule_prefix()) {
        let id = key.skip(2);
        lemma_starts_split(key, schedule_prefix());
        assert(key == spec_schedule_key(id));
        match doc {
            DocumentBodyV::Schedule(Some(schedule)) => {
                assert(slot_rel(
                    Some(schedule), id, state.store,
                ));
                assert(schedule.next_run_at <= now);
                assert(schedule.next_run_at <= MAX_TIME);
                assert(echod_types::spec_deadline_bounded(
                    schedule.next_run_at,
                    schedule.promise_timeout,
                )) by {
                    reveal(spec_due_transition);
                    reveal(crate::node::spec_fire_schedule);
                };
                assert(({
                    let promise =
                        echod_abstract::trusted::spec_expand(
                            schedule.promise_id@,
                            schedule.id@,
                            schedule.next_run_at,
                        );
                    &&& promise.len() <= usize::MAX as int
                    &&& exists|carrier: String| carrier@ == promise
                })) by {
                    reveal(spec_due_transition);
                    reveal(crate::node::spec_fire_schedule);
                };
                lemma_schedule_due(
                    config, key, id, schedule, state, now,
                );
            },
            _ => {
                assert(spec_due_transition(
                    doc, now, config.retry_timeout,
                ).2.len() == 0);
                assert(false);
            },
        }
    } else {
        match doc {
            DocumentBodyV::Workflow(_) => {
                reveal(spec_due_transition);
                assert(spec_due_transition(
                    doc, now, config.retry_timeout,
                ).2.len() == 0);
                assert(false);
            },
            DocumentBodyV::Schedule(_) => {
                assert(false);
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Every due step
// ---------------------------------------------------------------------------

pub proof fn lemma_due_agrees(config: ServerConfig, key: Seq<char>, doc: DocumentBodyV, state: StateV, now: Time)
    requires
        doc_rel(key, doc, state.store),
        finite_store(state.store),
    ensures
        due_agrees(config, key, doc, state, now),
{
    let s = state.store;
    if spec_starts(key, schedule_prefix()) {
        let id = key.skip(2);
        lemma_starts_split(key, schedule_prefix());
        assert(key == spec_schedule_key(id));
        match doc {
            DocumentBodyV::Schedule(Some(sch)) => {
                let promise = echod_abstract::trusted::spec_expand(
                    sch.promise_id@,
                    sch.id@,
                    sch.next_run_at,
                );
                if sch.next_run_at <= now
                    && sch.next_run_at <= MAX_TIME
                    && echod_types::spec_deadline_bounded(
                        sch.next_run_at,
                        sch.promise_timeout,
                    )
                    && promise.len() <= usize::MAX as int
                    && exists|carrier: String| carrier@ == promise
                {
                    lemma_schedule_due(config, key, id, sch, state, now);
                } else {
                    assert(spec_due_transition(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
                }
            },
            _ => {
                assert(spec_due_transition(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
            },
        }
    } else if spec_starts(key, origin_prefix()) {
        let o = key.skip(2);
        lemma_starts_split(key, origin_prefix());
        assert(key == spec_origin_key(o));
        match doc {
            DocumentBodyV::Workflow(map) => {
                lemma_origin_doc(key, o, doc, state.store);
                lemma_origin_due(config, key, o, map, state, now);
            },
            _ => {},
        }
    } else {
        match doc {
            DocumentBodyV::Workflow(map) => {
                assert(map.dom().len() == 0);
                assert(map.dom() =~= Set::<Seq<char>>::empty());
                lemma_sorted(map.dom());
                assert(c_sorted(map.dom()).len() == 0);
                assert(spec_due_transition(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
            },
            DocumentBodyV::Schedule(_) => {
                assert(spec_due_transition(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
            },
        }
    }
}

pub proof fn lemma_dues_agree(config: ServerConfig)
    ensures
        dues_agree(config),
{
    assert forall|key: Seq<char>, doc: DocumentBodyV, state: StateV, now: u64|
        doc_rel(key, doc, state.store) && finite_store(state.store) implies #[trigger] due_agrees(
        config,
        key,
        doc,
        state,
        now,
    ) by {
        lemma_due_agrees(config, key, doc, state, now);
    };
}

// ---------------------------------------------------------------------------
// The occurrence
// ---------------------------------------------------------------------------

/// Lean's `createPromiseAt`: the object born of an occurrence relates to the
/// abstract object born of it.
pub proof fn lemma_born(pending: PendingV, now: Time)
    requires
        now >= pending.at,
    ensures
        ({
            let timeout_at = spec_sat_add(pending.at, pending.timeout);
            let runnable = spec_targeted(pending.tags) && !spec_timer(pending.tags);
            let born = spec_new_obj(timeout_at, now, pending.param, pending.tags, runnable);
            let promise = if timeout_at > pending.at {
                PromV { created_at: pending.at, ..born.promise }
            } else {
                born.promise
            };
            let task = match born.task {
                Some(t) if t.state == TaskState::Pending => Some(TkV {
                    retry_timeout_at: Some(now),
                    ..t
                }),
                other => other,
            };
            let (p, t) = spec_new_object(
                sat_add(pending.at, pending.timeout),
                pending.at,
                now,
                pending.param,
                pending.tags,
                spec_has_target(pending.tags) && !spec_is_timer(pending.tags),
            );
            &&& object_rel(ObjV { promise, task }, p, t)
            &&& promise.callbacks.len() == 0
        }),
{
    let at = pending.at;
    let tags = pending.tags;
    lemma_sat_add(at, pending.timeout);
    lemma_targeted(tags);
    lemma_timer(tags);
    lemma_offer(tags, at);
    lemma_empty_to_set();
    let timeout_at = spec_sat_add(at, pending.timeout);
    let runnable = spec_targeted(tags) && !spec_timer(tags);
    let born = spec_new_obj(timeout_at, now, pending.param, tags, runnable);
    let promise = if timeout_at > at {
        PromV { created_at: at, ..born.promise }
    } else {
        born.promise
    };
    let task = match born.task {
        Some(t) if t.state == TaskState::Pending => Some(TkV {
            retry_timeout_at: Some(now),
            ..t
        }),
        other => other,
    };
    let (p, t) = spec_new_object(timeout_at, at, now, pending.param, tags, runnable);
    let live_now = timeout_at > now;
    assert(promise.state == p.state);
    assert(promise.created_at == p.created_at);
    assert(promise.settled_at == p.settled_at);
    assert(promise_rel(promise, p));
    match (task, t) {
        (Some(ct), Some(at_)) => {
            assert(task_rel(ct, at_));
        },
        (None, None) => {},
        _ => {
            assert(false);
        },
    }
    assert(object_rel(ObjV { promise, task }, p, t));
}

pub proof fn lemma_occurrence_agrees(pending: PendingV, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_origin_key(origin(pending.promise)), doc, s),
        finite_store(s),
    ensures
        occurrence_agrees(pending, doc, s, now),
{
    let x = pending.promise;
    let o = origin(x);
    let key = spec_origin_key(o);
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    assert(spec_opened(doc) == doc);
    let next = spec_occurrence(doc, pending, now);
    if map.contains_key(x) || now < pending.at {
        assert(next == doc);
    } else {
        assert(!s.promises.contains_key(x));
        assert(!s.tasks.contains_key(x));
        lemma_born(pending, now);
        let timeout_at = spec_sat_add(pending.at, pending.timeout);
        let runnable = spec_targeted(pending.tags) && !spec_timer(pending.tags);
        let born = spec_new_obj(timeout_at, now, pending.param, pending.tags, runnable);
        let promise = if timeout_at > pending.at {
            PromV { created_at: pending.at, ..born.promise }
        } else {
            born.promise
        };
        let task = match born.task {
            Some(t) if t.state == TaskState::Pending => Some(TkV {
                retry_timeout_at: Some(now),
                ..t
            }),
            other => other,
        };
        let obj = ObjV { promise, task };
        assert(next == DocumentBodyV::Workflow(map.insert(x, obj)));
        let (p, t) = spec_new_object(
            sat_add(pending.at, pending.timeout),
            pending.at,
            now,
            pending.param,
            pending.tags,
            spec_has_target(pending.tags) && !spec_is_timer(pending.tags),
        );
        assert(object_rel(obj, p, t));
        assert(callbacks_in(obj.promise.callbacks, o));
        let out = spec_create_if_absent(
            s,
            x,
            pending.at,
            pending.timeout,
            pending.param,
            pending.tags,
            now,
        );
        let tasks = match t {
            Some(task) => s.tasks.insert(x, task),
            None => s.tasks,
        };
        let n = AStore { promises: s.promises.insert(x, p), tasks, ..s };
        assert(out == spec_did(n, Seq::empty(), Seq::empty()));
        match t {
            Some(_) => {},
            None => {
                assert(s.tasks.remove(x) =~= s.tasks);
            },
        }
        lemma_one_changed(map, o, s, x, obj, p, t, n);
        lemma_origin_reads(key, o, map.insert(x, obj), n);
        lemma_others_kept_within(s, n, o);
    }
}

pub proof fn lemma_occurrences_agree()
    ensures
        occurrences_agree(),
{
    assert forall|pending: PendingV, doc: DocumentBodyV, s: AStore, now: u64|
        doc_rel(spec_origin_key(origin(pending.promise)), doc, s) && finite_store(s) implies #[trigger] occurrence_agrees(
        pending,
        doc,
        s,
        now,
    ) by {
        lemma_occurrence_agrees(pending, doc, s, now);
    };
}

// ---------------------------------------------------------------------------
// Agreement
// ---------------------------------------------------------------------------

/// Lean's `refinement_handlers`: at every configuration, every handler,
/// the due step, and the occurrence agree.
pub proof fn lemma_agreement(config: ServerConfig)
    ensures
        agreement(config),
{
    crate::handlers::lemma_requests_agree(config);
    lemma_dues_agree(config);
    lemma_occurrences_agree();
}

} // verus!
