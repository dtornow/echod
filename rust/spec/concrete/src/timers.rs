//! The due step and the occurrence agree.
//!
//! The concrete node walks one document and takes the first thing due in
//! it; the abstract service offers every timeout of every object. This
//! module finds the concrete choice among the abstract offers: the key
//! order ([`lemma_sorted`]), membership in the offers
//! ([`lemma_timeout_offered`]), and then each branch of
//! `spec_step_object` against its abstract counterpart. The occurrence is
//! Lean's `createPromiseAt` against `spec_create_if_absent`. The module ends
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
    lemma_sat_add, lemma_schedule_key, lemma_starts_split, lemma_string_view, lemma_targeted,
    lemma_timer, object_rel, origin_prefix, origin_rel, promise_rel, schedule_prefix, schedule_rel,
    slot_rel, task_rel,
};
#[cfg(verus_keep_ghost)]
use crate::model::{spec_string as c_string};
#[cfg(verus_keep_ghost)]
use crate::node::{
    DocV, NoteV, ObjV, PendingV, PromV, spec_due_id, spec_min_key as c_min_key, spec_new_obj,
    spec_obj_due, spec_occurrence, spec_offer_at, spec_opened, spec_origin_key, spec_origin_map,
    spec_project_obj, spec_record, spec_resume, spec_run_due, spec_schedule_key,
    spec_sorted as c_sorted, spec_step_object, spec_targeted, spec_timer, spec_unlease as c_unlease,
    TkV,
};
#[cfg(verus_keep_ghost)]
use crate::store::{spec_before as c_before, spec_sat_add, spec_starts};
#[cfg(verus_keep_ghost)]
use crate::relation::{
    agreement, as_item, due_agrees, dues_agree, items, note_sends, occurrence_agrees,
    occurrences_agree,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::machine::{
    spec_callback, spec_callback_apply, spec_create_if_absent, spec_did, spec_has_target,
    spec_is_timer, spec_lease, spec_lease_at, spec_listener, spec_new_object, spec_process_work,
    spec_project_promise, spec_project_task, spec_promise_record, spec_retry, spec_schedule_step,
    spec_string as a_string, spec_unlease as a_unlease,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::model::{
    Pid as APid, spec_derived, spec_due_result, spec_keep, spec_over_callbacks, spec_over_listeners,
    spec_over_promises, spec_over_schedules, spec_over_tasks, spec_queue, spec_run_timeout, StateV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::view::{
    DispatchV, InOutV, InternalV, least as a_least, lemma_least_exists as a_lemma_least_exists,
    lemma_lift_dispatch, lemma_min_key as a_lemma_min_key, lift_dispatch, PromiseV, sat_add,
    ScheduleV, spec_before as a_before, spec_keys, spec_min_key as a_min_key,
    spec_sorted as a_sorted, StoreV as AStore, TaskV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::protocol::Message as AMessage;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::trusted::{pset_seq, spec_expand, spec_next_cron};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::{Dispatch, Output, ServerConfig};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::RoverSpec::StepResultV;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::comm::{Sched, Time};
#[cfg(verus_keep_ghost)]
use echod_types::{origin, PromiseRecord, PromiseState, Response, Schedule, TaskState};

verus! {

broadcast use
    vstd::seq::group_seq_lemmas,
    vstd::set::group_set_lemmas,
    echod_abstract_spec::view::group_views;

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

/// The first due id is an id of the document.
pub proof fn lemma_due_id(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, now: Time)
    requires
        forall|i: int| 0 <= i < keys.len() ==> map.contains_key(#[trigger] keys[i]),
    ensures
        match spec_due_id(map, keys, now) {
            Some(id) => map.contains_key(id),
            None => true,
        },
    decreases keys.len(),
{
    if keys.len() == 0 {
    } else if spec_obj_due(map[keys[0]], now) is Some {
    } else {
        let rest = keys.drop_first();
        assert forall|i: int| 0 <= i < rest.len() implies map.contains_key(#[trigger] rest[i]) by {
            assert(rest[i] == keys[i + 1]);
        };
        lemma_due_id(map, rest, now);
    }
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
    awaiters: Seq<Seq<char>>,
    awaiter: Seq<char>,
)
    requires
        awaiters.contains(awaiter),
    ensures
        offered(
            config,
            state,
            now,
            InternalV::Callback { awaited, awaiter },
            spec_over_callbacks(config, state, now, awaited, awaiters),
        ),
    decreases awaiters.len(),
{
    let work = InternalV::Callback { awaited, awaiter };
    let head = spec_keep(
        config,
        state,
        now,
        InternalV::Callback { awaited, awaiter: awaiters[0] },
        Seq::empty(),
    );
    let tail = spec_over_callbacks(config, state, now, awaited, awaiters.drop_first());
    assert(spec_over_callbacks(config, state, now, awaited, awaiters) == head + tail);
    if awaiters[0] == awaiter {
        lemma_keep_offered(config, state, now, work);
        lemma_offered_left(config, state, now, work, head, tail);
    } else {
        let j = choose|j: int| 0 <= j < awaiters.len() && awaiters[j] == awaiter;
        assert(awaiters.drop_first()[j - 1] == awaiter);
        lemma_over_callbacks_offered(config, state, now, awaited, awaiters.drop_first(), awaiter);
        lemma_offered_right(config, state, now, work, head, tail);
    }
}

pub proof fn lemma_over_listeners_offered(
    config: ServerConfig,
    state: StateV,
    now: Time,
    awaited: Seq<char>,
    addresses: Seq<Seq<char>>,
    address: Seq<char>,
)
    requires
        addresses.contains(address),
    ensures
        offered(
            config,
            state,
            now,
            InternalV::Listener { awaited, address },
            spec_over_listeners(config, state, now, awaited, addresses),
        ),
    decreases addresses.len(),
{
    let work = InternalV::Listener { awaited, address };
    let head = spec_keep(
        config,
        state,
        now,
        InternalV::Listener { awaited, address: addresses[0] },
        Seq::empty(),
    );
    let tail = spec_over_listeners(config, state, now, awaited, addresses.drop_first());
    assert(spec_over_listeners(config, state, now, awaited, addresses) == head + tail);
    if addresses[0] == address {
        lemma_keep_offered(config, state, now, work);
        lemma_offered_left(config, state, now, work, head, tail);
    } else {
        let j = choose|j: int| 0 <= j < addresses.len() && addresses[j] == address;
        assert(addresses.drop_first()[j - 1] == address);
        lemma_over_listeners_offered(config, state, now, awaited, addresses.drop_first(), address);
        lemma_offered_right(config, state, now, work, head, tail);
    }
}

/// What the promises offer: every promise's timeout, every callback, every
/// listener.
pub open spec fn promise_offers(
    config: ServerConfig,
    state: StateV,
    now: Time,
    id: Seq<char>,
    results: Seq<AResult>,
) -> bool {
    let p = state.store.promises[id];
    &&& offered(config, state, now, InternalV::PromiseTimeout(id), results)
    &&& forall|awaiter: Seq<char>|
        #[trigger] p.callbacks.contains(awaiter) ==> offered(
            config,
            state,
            now,
            InternalV::Callback { awaited: id, awaiter },
            results,
        )
    &&& forall|address: Seq<char>|
        #[trigger] p.listeners.contains(address) ==> offered(
            config,
            state,
            now,
            InternalV::Listener { awaited: id, address },
            results,
        )
}

pub proof fn lemma_promise_offers_left(
    config: ServerConfig,
    state: StateV,
    now: Time,
    id: Seq<char>,
    a: Seq<AResult>,
    b: Seq<AResult>,
)
    requires
        promise_offers(config, state, now, id, a),
    ensures
        promise_offers(config, state, now, id, a + b),
{
    let p = state.store.promises[id];
    lemma_offered_left(config, state, now, InternalV::PromiseTimeout(id), a, b);
    assert forall|awaiter: Seq<char>| #[trigger] p.callbacks.contains(awaiter) implies offered(
        config,
        state,
        now,
        InternalV::Callback { awaited: id, awaiter },
        a + b,
    ) by {
        lemma_offered_left(config, state, now, InternalV::Callback { awaited: id, awaiter }, a, b);
    };
    assert forall|address: Seq<char>| #[trigger] p.listeners.contains(address) implies offered(
        config,
        state,
        now,
        InternalV::Listener { awaited: id, address },
        a + b,
    ) by {
        lemma_offered_left(config, state, now, InternalV::Listener { awaited: id, address }, a, b);
    };
}

pub proof fn lemma_promise_offers_right(
    config: ServerConfig,
    state: StateV,
    now: Time,
    id: Seq<char>,
    a: Seq<AResult>,
    b: Seq<AResult>,
)
    requires
        promise_offers(config, state, now, id, b),
    ensures
        promise_offers(config, state, now, id, a + b),
{
    let p = state.store.promises[id];
    lemma_offered_right(config, state, now, InternalV::PromiseTimeout(id), a, b);
    assert forall|awaiter: Seq<char>| #[trigger] p.callbacks.contains(awaiter) implies offered(
        config,
        state,
        now,
        InternalV::Callback { awaited: id, awaiter },
        a + b,
    ) by {
        lemma_offered_right(config, state, now, InternalV::Callback { awaited: id, awaiter }, a, b);
    };
    assert forall|address: Seq<char>| #[trigger] p.listeners.contains(address) implies offered(
        config,
        state,
        now,
        InternalV::Listener { awaited: id, address },
        a + b,
    ) by {
        lemma_offered_right(config, state, now, InternalV::Listener { awaited: id, address }, a, b);
    };
}

pub proof fn lemma_over_promises_offered(
    config: ServerConfig,
    state: StateV,
    now: Time,
    keys: Seq<Seq<char>>,
    id: Seq<char>,
)
    requires
        keys.contains(id),
    ensures
        promise_offers(config, state, now, id, spec_over_promises(config, state, now, keys)),
    decreases keys.len(),
{
    let head = keys[0];
    let p = state.store.promises[head];
    let a = spec_keep(config, state, now, InternalV::PromiseTimeout(head), Seq::empty());
    let b = spec_over_callbacks(config, state, now, head, pset_seq(p.callbacks));
    let c = spec_over_listeners(config, state, now, head, pset_seq(p.listeners));
    let d = spec_over_promises(config, state, now, keys.drop_first());
    assert(spec_over_promises(config, state, now, keys) == a + b + c + d);
    if head == id {
        lemma_keep_offered(config, state, now, InternalV::PromiseTimeout(id));
        lemma_offered_left(config, state, now, InternalV::PromiseTimeout(id), a, b);
        assert forall|awaiter: Seq<char>| #[trigger] p.callbacks.contains(awaiter) implies offered(
            config,
            state,
            now,
            InternalV::Callback { awaited: id, awaiter },
            a + b,
        ) by {
            assert(pset_seq(p.callbacks).to_set().contains(awaiter));
            lemma_contains_to_set(pset_seq(p.callbacks), awaiter);
            lemma_over_callbacks_offered(config, state, now, id, pset_seq(p.callbacks), awaiter);
            lemma_offered_right(config, state, now, InternalV::Callback { awaited: id, awaiter }, a, b);
        };
        assert forall|address: Seq<char>| #[trigger] p.listeners.contains(address) implies offered(
            config,
            state,
            now,
            InternalV::Listener { awaited: id, address },
            a + b + c,
        ) by {
            assert(pset_seq(p.listeners).to_set().contains(address));
            lemma_contains_to_set(pset_seq(p.listeners), address);
            lemma_over_listeners_offered(config, state, now, id, pset_seq(p.listeners), address);
            lemma_offered_right(config, state, now, InternalV::Listener { awaited: id, address }, a + b, c);
        };
        lemma_offered_left(config, state, now, InternalV::PromiseTimeout(id), a + b, c);
        assert forall|awaiter: Seq<char>| #[trigger] p.callbacks.contains(awaiter) implies offered(
            config,
            state,
            now,
            InternalV::Callback { awaited: id, awaiter },
            a + b + c,
        ) by {
            lemma_offered_left(config, state, now, InternalV::Callback { awaited: id, awaiter }, a + b, c);
        };
        assert(promise_offers(config, state, now, id, a + b + c));
        lemma_promise_offers_left(config, state, now, id, a + b + c, d);
    } else {
        let j = choose|j: int| 0 <= j < keys.len() && keys[j] == id;
        assert(keys.drop_first()[j - 1] == id);
        lemma_over_promises_offered(config, state, now, keys.drop_first(), id);
        lemma_promise_offers_right(config, state, now, id, a + b + c, d);
    }
}

/// What the tasks offer: every lease, and the retry of every task that has
/// one.
pub open spec fn task_offers(
    config: ServerConfig,
    state: StateV,
    now: Time,
    id: Seq<char>,
    results: Seq<AResult>,
) -> bool {
    &&& offered(config, state, now, InternalV::TaskLeaseTimeout(id), results)
    &&& state.store.tasks[id].retry_timeout_at is Some ==> offered(
        config,
        state,
        now,
        InternalV::TaskRetryTimeout(id),
        results,
    )
}

pub proof fn lemma_over_tasks_offered(
    config: ServerConfig,
    state: StateV,
    now: Time,
    keys: Seq<Seq<char>>,
    id: Seq<char>,
)
    requires
        keys.contains(id),
    ensures
        task_offers(config, state, now, id, spec_over_tasks(config, state, now, keys)),
    decreases keys.len(),
{
    let head = keys[0];
    let t = state.store.tasks[head];
    let lease = spec_keep(config, state, now, InternalV::TaskLeaseTimeout(head), Seq::empty());
    let retry = match t.retry_timeout_at {
        Some(_) => spec_keep(config, state, now, InternalV::TaskRetryTimeout(head), Seq::empty()),
        None => Seq::<AResult>::empty(),
    };
    let rest = spec_over_tasks(config, state, now, keys.drop_first());
    assert(spec_over_tasks(config, state, now, keys) == lease + retry + rest);
    if head == id {
        lemma_keep_offered(config, state, now, InternalV::TaskLeaseTimeout(id));
        lemma_offered_left(config, state, now, InternalV::TaskLeaseTimeout(id), lease, retry);
        lemma_offered_left(config, state, now, InternalV::TaskLeaseTimeout(id), lease + retry, rest);
        if t.retry_timeout_at is Some {
            lemma_keep_offered(config, state, now, InternalV::TaskRetryTimeout(id));
            lemma_offered_right(config, state, now, InternalV::TaskRetryTimeout(id), lease, retry);
            lemma_offered_left(config, state, now, InternalV::TaskRetryTimeout(id), lease + retry, rest);
        }
    } else {
        let j = choose|j: int| 0 <= j < keys.len() && keys[j] == id;
        assert(keys.drop_first()[j - 1] == id);
        lemma_over_tasks_offered(config, state, now, keys.drop_first(), id);
        lemma_offered_right(config, state, now, InternalV::TaskLeaseTimeout(id), lease + retry, rest);
        if state.store.tasks[id].retry_timeout_at is Some {
            lemma_offered_right(config, state, now, InternalV::TaskRetryTimeout(id), lease + retry, rest);
        }
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

/// Everything the abstract timeout step offers, by object.
pub proof fn lemma_timeout_offered(config: ServerConfig, state: StateV, now: Time)
    requires
        finite_store(state.store),
    ensures
        forall|id: Seq<char>|
            #[trigger] state.store.promises.contains_key(id) ==> promise_offers(
                config,
                state,
                now,
                id,
                spec_run_timeout(config, state, now),
            ),
        forall|id: Seq<char>|
            #[trigger] state.store.tasks.contains_key(id) ==> task_offers(
                config,
                state,
                now,
                id,
                spec_run_timeout(config, state, now),
            ),
        forall|id: Seq<char>|
            #[trigger] state.store.schedules.contains_key(id) ==> offered(
                config,
                state,
                now,
                schedule_work(state.store, id),
                spec_run_timeout(config, state, now),
            ),
{
    let s = state.store;
    let queued = spec_queue(config, state, now, 0);
    let op = spec_over_promises(config, state, now, spec_keys(s.promises));
    let ot = spec_over_tasks(config, state, now, spec_keys(s.tasks));
    let os = spec_over_schedules(config, state, now, spec_keys(s.schedules));
    let results = spec_run_timeout(config, state, now);
    assert(spec_derived(config, state, now) == op + ot + os);
    assert(results == queued + (op + ot + os));
    lemma_sorted(s.promises.dom());
    lemma_sorted(s.tasks.dom());
    lemma_sorted(s.schedules.dom());
    assert forall|id: Seq<char>| #[trigger] s.promises.contains_key(id) implies promise_offers(
        config,
        state,
        now,
        id,
        results,
    ) by {
        assert(s.promises.dom().contains(id));
        lemma_over_promises_offered(config, state, now, spec_keys(s.promises), id);
        lemma_promise_offers_left(config, state, now, id, op, ot);
        lemma_promise_offers_left(config, state, now, id, op + ot, os);
        lemma_promise_offers_right(config, state, now, id, queued, op + ot + os);
    };
    assert forall|id: Seq<char>| #[trigger] s.tasks.contains_key(id) implies task_offers(
        config,
        state,
        now,
        id,
        results,
    ) by {
        assert(s.tasks.dom().contains(id));
        lemma_over_tasks_offered(config, state, now, spec_keys(s.tasks), id);
        lemma_offered_right(config, state, now, InternalV::TaskLeaseTimeout(id), op, ot);
        lemma_offered_left(config, state, now, InternalV::TaskLeaseTimeout(id), op + ot, os);
        lemma_offered_right(config, state, now, InternalV::TaskLeaseTimeout(id), queued, op + ot + os);
        if s.tasks[id].retry_timeout_at is Some {
            lemma_offered_right(config, state, now, InternalV::TaskRetryTimeout(id), op, ot);
            lemma_offered_left(config, state, now, InternalV::TaskRetryTimeout(id), op + ot, os);
            lemma_offered_right(config, state, now, InternalV::TaskRetryTimeout(id), queued, op + ot + os);
        }
    };
    assert forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) implies offered(
        config,
        state,
        now,
        schedule_work(s, id),
        results,
    ) by {
        assert(s.schedules.dom().contains(id));
        lemma_over_schedules_offered(config, state, now, spec_keys(s.schedules), id);
        lemma_offered_right(config, state, now, schedule_work(s, id), op + ot, os);
        lemma_offered_right(config, state, now, schedule_work(s, id), queued, op + ot + os);
    };
}

/// `work` names objects the store holds, so the timeout step offers it.
pub open spec fn work_known(s: AStore, work: InternalV) -> bool {
    match work {
        InternalV::PromiseTimeout(id) => s.promises.contains_key(id),
        InternalV::Callback { awaited, awaiter } => s.promises.contains_key(awaited)
            && s.promises[awaited].callbacks.contains(awaiter),
        InternalV::Listener { awaited, address } => s.promises.contains_key(awaited)
            && s.promises[awaited].listeners.contains(address),
        InternalV::TaskLeaseTimeout(id) => s.tasks.contains_key(id),
        InternalV::TaskRetryTimeout(id) => s.tasks.contains_key(id)
            && s.tasks[id].retry_timeout_at is Some,
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
        work_known(state.store, work),
    ensures
        offered(config, state, now, work, spec_run_timeout(config, state, now)),
{
    lemma_timeout_offered(config, state, now);
    let results = spec_run_timeout(config, state, now);
    match work {
        InternalV::PromiseTimeout(id) => {
            assert(promise_offers(config, state, now, id, results));
        },
        InternalV::Callback { awaited, awaiter } => {
            assert(promise_offers(config, state, now, awaited, results));
        },
        InternalV::Listener { awaited, address } => {
            assert(promise_offers(config, state, now, awaited, results));
        },
        InternalV::TaskLeaseTimeout(id) => {
            assert(task_offers(config, state, now, id, results));
        },
        InternalV::TaskRetryTimeout(id) => {
            assert(task_offers(config, state, now, id, results));
        },
        InternalV::ScheduleTimeout { id, promise } => {
            assert(offered(config, state, now, schedule_work(state.store, id), results));
        },
        InternalV::Occurrence { .. } => {},
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
    let d = Dispatch::Execute { id: c_string(id), version };
    lemma_string_view(id);
    assert(d@ == DispatchV::Execute { id, version });
    lemma_lift_dispatch(d);
}

/// A lifted unblock is the unblock of the string.
pub proof fn lemma_lift_unblock(address: Seq<char>, promise: PromiseRecord)
    ensures
        lift_dispatch(DispatchV::Unblock { address, promise }) == (Dispatch::Unblock {
            address: c_string(address),
            promise,
        }),
{
    let d = Dispatch::Unblock { address: c_string(address), promise };
    lemma_string_view(address);
    assert(d@ == DispatchV::Unblock { address, promise });
    lemma_lift_dispatch(d);
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
// One matched result
// ---------------------------------------------------------------------------

/// `r` is an abstract timeout result that does what the due step did.
pub open spec fn due_matched(
    config: ServerConfig,
    key: Seq<char>,
    doc: DocV,
    state: StateV,
    now: Time,
    r: AResult,
) -> bool {
    let (next, _, born, notes) = spec_run_due(doc, now, config.retry_timeout);
    &&& spec_run_timeout(config, state, now).contains(r)
    &&& r.send == note_sends(notes)
    &&& r.state.pending == state.pending + items(born)
    &&& doc_rel(key, next, r.state.store)
    &&& crate::interpret::others_kept(key, state.store, r.state.store)
    &&& finite_store(r.state.store)
}

pub proof fn lemma_matched(
    config: ServerConfig,
    key: Seq<char>,
    doc: DocV,
    state: StateV,
    now: Time,
    r: AResult,
)
    requires
        due_matched(config, key, doc, state, now, r),
    ensures
        due_agrees(config, key, doc, state, now),
{
    let results = spec_run_timeout(config, state, now);
    let j = choose|j: int| 0 <= j < results.len() && results[j] == r;
    assert(results[j] == r);
}

/// An origin document whose due step changed the store within its origin.
pub proof fn lemma_origin_matched(
    config: ServerConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    work: InternalV,
    map2: Map<Seq<char>, ObjV>,
    notes: Seq<NoteV>,
)
    requires
        key == spec_origin_key(o),
        map.dom().finite(),
        map2.dom().finite(),
        finite_store(state.store),
        offered(config, state, now, work, spec_run_timeout(config, state, now)),
        ({
            let outcome = spec_process_work(config, work, state.store, now);
            &&& !outcome.not_due
            &&& outcome.work.len() == 0
            &&& outcome.next.schedules == state.store.schedules
            &&& origin_rel(map2, o, outcome.next)
            &&& changed_within(state.store, outcome.next, o)
            &&& finite_store(outcome.next)
            &&& sends_of(outcome.send) == note_sends(notes)
        }),
        spec_run_due(DocV::Origin(map), now, config.retry_timeout) == (DocV::Origin(map2), None::<Response>, Seq::<PendingV>::empty(), notes),
    ensures
        due_agrees(config, key, DocV::Origin(map), state, now),
{
    let s = state.store;
    let outcome = spec_process_work(config, work, s, now);
    let r = spec_due_result(state, outcome);
    let n = outcome.next;
    assert(r.state.pending == state.pending + outcome.work);
    assert(state.pending + outcome.work =~= state.pending);
    assert(items(Seq::<PendingV>::empty()) =~= Seq::<Sched<InternalV>>::empty());
    assert(state.pending + items(Seq::<PendingV>::empty()) =~= state.pending);
    lemma_sends_of(state, outcome);
    assert(r.send == sends_of(outcome.send));
    lemma_origin_reads(key, o, map2, n);
    lemma_others_kept_within(s, n, o);
    assert(due_matched(config, key, DocV::Origin(map), state, now, r));
    lemma_matched(config, key, DocV::Origin(map), state, now, r);
}

/// The store changed at one id of the origin: the next document reads as
/// the next store.
pub proof fn lemma_one_changed(
    map: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    id: Seq<char>,
    obj2: ObjV,
    p2: PromiseV,
    t2: Option<TaskV>,
    n: AStore,
)
    requires
        map.dom().finite(),
        origin_rel(map, o, s),
        finite_store(s),
        origin(id) == o,
        object_rel(obj2, p2, t2),
        callbacks_in(obj2.promise.callbacks, o),
        n.promises == s.promises.insert(id, p2),
        n.tasks == match t2 {
            Some(t) => s.tasks.insert(id, t),
            None => s.tasks.remove(id),
        },
        n.schedules == s.schedules,
    ensures
        map.insert(id, obj2).dom().finite(),
        origin_rel(map.insert(id, obj2), o, n),
        changed_within(s, n, o),
        finite_store(n),
{
    lemma_origin_update(map, o, s, id, obj2, p2, t2, n);
    assert(map.insert(id, obj2).dom() == map.dom().insert(id));
    lemma_within_one(s, n, id);
    assert(n.promises.dom() == s.promises.dom().insert(id));
    match t2 {
        Some(t) => {
            assert(n.tasks.dom() == s.tasks.dom().insert(id));
        },
        None => {
            assert(n.tasks.dom() == s.tasks.dom().remove(id));
        },
    }
}

/// The store changed at two ids of the origin.
pub proof fn lemma_within_two(s: AStore, n: AStore, id: Seq<char>, y: Seq<char>)
    requires
        origin(y) == origin(id),
        forall|other: Seq<char>|
            other != id && other != y ==> #[trigger] n.promises.contains_key(other) == s.promises.contains_key(other)
                && (s.promises.contains_key(other) ==> n.promises[other] == s.promises[other]),
        forall|other: Seq<char>|
            other != id && other != y ==> #[trigger] n.tasks.contains_key(other) == s.tasks.contains_key(other)
                && (s.tasks.contains_key(other) ==> n.tasks[other] == s.tasks[other]),
    ensures
        changed_within(s, n, origin(id)),
{
    assert forall|other: Seq<char>| #![trigger origin(other)] origin(other) != origin(id) implies {
        &&& s.promises.contains_key(other) == n.promises.contains_key(other)
        &&& (s.promises.contains_key(other) ==> s.promises[other] == n.promises[other])
        &&& s.tasks.contains_key(other) == n.tasks.contains_key(other)
        &&& (s.tasks.contains_key(other) ==> s.tasks[other] == n.tasks[other])
    } by {
        assert(other != id);
        assert(other != y);
    };
}

// ---------------------------------------------------------------------------
// The due branches of an origin document
// ---------------------------------------------------------------------------

/// The context of one due object: the document, its origin, the store, and
/// the object with its abstract promise and task.
pub open spec fn due_context(
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    s: AStore,
    id: Seq<char>,
) -> bool {
    &&& key == spec_origin_key(o)
    &&& map.dom().finite()
    &&& origin_rel(map, o, s)
    &&& finite_store(s)
    &&& map.contains_key(id)
}

/// A pending promise past its timeout: both sides project it.
pub proof fn lemma_promise_due(
    config: ServerConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state == PromiseState::Pending,
        map[id].promise.timeout_at <= now,
    ensures
        due_agrees(config, key, DocV::Origin(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    let work = InternalV::PromiseTimeout(id);
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    let q = spec_project_promise(p, now);
    assert(p.state == PromiseState::Pending);
    assert(q.state != PromiseState::Pending);
    let tasks = if s.tasks.contains_key(id) {
        s.tasks.insert(id, spec_project_task(s.tasks[id], q))
    } else {
        s.tasks
    };
    let n = AStore { promises: s.promises.insert(id, q), tasks, ..s };
    let outcome = spec_process_work(config, work, s, now);
    assert(outcome == spec_did(n, Seq::empty(), Seq::empty()));
    let obj2 = spec_project_obj(obj, now);
    lemma_project_object(obj, p, ta, now);
    let t2 = match ta {
        Some(task) => Some(spec_project_task(task, q)),
        None => None,
    };
    assert(object_rel(obj2, q, t2));
    assert(obj2.promise.callbacks == obj.promise.callbacks);
    match ta {
        Some(_) => {
            assert(s.tasks.contains_key(id));
        },
        None => {
            assert(!s.tasks.contains_key(id));
            assert(s.tasks.remove(id) =~= s.tasks);
        },
    }
    lemma_one_changed(map, o, s, id, obj2, q, t2, n);
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map.insert(id, obj2), Seq::<NoteV>::empty()));
    lemma_sends_none();
    lemma_origin_matched(config, key, o, map, state, now, work, map.insert(id, obj2), Seq::empty());
}

/// An acquired task whose lease ran out: both sides release it.
pub proof fn lemma_lease_due(
    config: ServerConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state == PromiseState::Pending,
        map[id].promise.timeout_at > now,
        map[id].task is Some,
        map[id].task.unwrap().state == TaskState::Acquired,
        map[id].task.unwrap().lease_timeout_at is Some,
        map[id].task.unwrap().lease_timeout_at.unwrap() <= now,
    ensures
        due_agrees(config, key, DocV::Origin(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let t = obj.task.unwrap();
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    assert(ta is Some);
    let t_a = ta.unwrap();
    assert(task_rel(t, t_a));
    assert(s.tasks.contains_key(id));
    assert(t_a == s.tasks[id]);
    let work = InternalV::TaskLeaseTimeout(id);
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    assert(spec_project_promise(p, now).state == PromiseState::Pending);
    assert(t_a.state == TaskState::Acquired);
    assert(t.ttl is Some);
    let at = t.lease_timeout_at.unwrap();
    assert(sat_add(t_a.acquired_at, t.ttl.unwrap()) == at);
    assert(spec_lease_at(t_a) == at);
    let u = a_unlease(t_a, TaskState::Pending, Some(now));
    let n = AStore { tasks: s.tasks.insert(id, u), ..s };
    let outcome = spec_process_work(config, work, s, now);
    assert(outcome == spec_lease(s, id, now));
    assert(outcome == spec_did(n, Seq::empty(), Seq::empty()));
    let t2 = c_unlease(t, TaskState::Pending, Some(now));
    let obj2 = ObjV { task: Some(t2), ..obj };
    assert(task_rel(t2, u));
    assert(object_rel(obj2, p, Some(u)));
    lemma_promises_kept(s, id);
    lemma_one_changed(map, o, s, id, obj2, p, Some(u), n);
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map.insert(id, obj2), Seq::<NoteV>::empty()));
    lemma_sends_none();
    lemma_origin_matched(config, key, o, map, state, now, work, map.insert(id, obj2), Seq::empty());
}

/// A pending task whose offer is due: both sides offer it again and tell
/// the outside to execute it.
pub proof fn lemma_retry_due(
    config: ServerConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state == PromiseState::Pending,
        map[id].promise.timeout_at > now,
        map[id].task is Some,
        map[id].task.unwrap().state == TaskState::Pending,
        map[id].task.unwrap().retry_timeout_at is Some,
        map[id].task.unwrap().retry_timeout_at.unwrap() <= now,
    ensures
        due_agrees(config, key, DocV::Origin(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let t = obj.task.unwrap();
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    assert(ta is Some);
    let t_a = ta.unwrap();
    assert(task_rel(t, t_a));
    assert(s.tasks.contains_key(id));
    assert(t_a == s.tasks[id]);
    assert(t_a.retry_timeout_at == t.retry_timeout_at);
    let work = InternalV::TaskRetryTimeout(id);
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    assert(spec_project_promise(p, now).state == PromiseState::Pending);
    lemma_sat_add(now, config.retry_timeout);
    let again = sat_add(now, config.retry_timeout);
    assert(again == spec_sat_add(now, config.retry_timeout));
    let u = TaskV { retry_timeout_at: Some(again), ..t_a };
    let n = AStore { tasks: s.tasks.insert(id, u), ..s };
    let outcome = spec_process_work(config, work, s, now);
    assert(outcome == spec_retry(config, s, id, now));
    assert(outcome == spec_did(n, Seq::empty(), seq![DispatchV::Execute { id, version: t_a.version }]));
    let t2 = TkV { retry_timeout_at: Some(spec_sat_add(now, config.retry_timeout)), ..t };
    let obj2 = ObjV { task: Some(t2), ..obj };
    assert(task_rel(t2, u));
    assert(object_rel(obj2, p, Some(u)));
    lemma_promises_kept(s, id);
    lemma_one_changed(map, o, s, id, obj2, p, Some(u), n);
    let notes = seq![NoteV::Execute { id, version: t.version }];
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map.insert(id, obj2), notes));
    assert(t.version == t_a.version);
    lemma_sends_execute(id, t.version);
    lemma_origin_matched(config, key, o, map, state, now, work, map.insert(id, obj2), notes);
}

/// A settled promise with a callback: both sides drop the callback and
/// resume the awaiter.
pub proof fn lemma_callback_due(
    config: ServerConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state != PromiseState::Pending,
        map[id].promise.callbacks.len() > 0,
    ensures
        due_agrees(config, key, DocV::Origin(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    assert(promise_rel(obj.promise, p));
    let callbacks = obj.promise.callbacks;
    let awaiter = callbacks[0];
    assert(callbacks.contains(awaiter));
    lemma_contains_to_set(callbacks, awaiter);
    assert(p.callbacks.contains(awaiter));
    assert(origin(awaiter) == o);
    let since = match obj.promise.settled_at {
        Some(at) => at,
        None => 0,
    };
    let work = InternalV::Callback { awaited: id, awaiter };
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    // The awaited side.
    assert(spec_project_promise(p, now) == p);
    let q = PromiseV { callbacks: p.callbacks.remove(awaiter), ..p };
    let outcome = spec_process_work(config, work, s, now);
    assert(outcome == spec_callback(s, id, awaiter, now));
    assert(outcome == spec_callback_apply(s, id, awaiter, q, since, now));
    let tasks0 = if s.tasks.contains_key(id) {
        s.tasks.insert(id, spec_project_task(s.tasks[id], q))
    } else {
        s.tasks
    };
    assert(tasks0 == s.tasks) by {
        if s.tasks.contains_key(id) {
            assert(ta is Some);
            assert(obj.task is Some);
            assert(obj.task.unwrap().state == TaskState::Fulfilled);
            assert(s.tasks[id].state == TaskState::Fulfilled);
            assert(spec_project_task(s.tasks[id], q) == s.tasks[id]);
            assert(s.tasks.insert(id, s.tasks[id]) =~= s.tasks);
        }
    };
    lemma_skip_no_duplicates(callbacks);
    let obj1 = ObjV { promise: PromV { callbacks: callbacks.skip(1), ..obj.promise }, ..obj };
    assert(promise_rel(obj1.promise, q));
    assert(object_rel(obj1, q, ta));
    assert forall|k: int| 0 <= k < callbacks.skip(1).len() implies origin(#[trigger] callbacks.skip(1)[k]) == o by {
        assert(callbacks.skip(1)[k] == callbacks[k + 1]);
    };
    assert(callbacks_in(obj1.promise.callbacks, o));
    let map1 = map.insert(id, obj1);
    let n1 = AStore { promises: s.promises.insert(id, q), tasks: s.tasks, ..s };
    lemma_tasks_kept(s, id);
    lemma_one_changed(map, o, s, id, obj1, q, ta, n1);
    let map2 = spec_resume(map1, awaiter, id, since, now);
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map2, Seq::<NoteV>::empty()));
    lemma_sends_none();
    // The awaiter side.
    let n = AStore { promises: s.promises.insert(id, q), tasks: outcome.next.tasks, ..s };
    assert(outcome.next == n);
    assert(outcome.send.len() == 0);
    assert(outcome.work.len() == 0);
    if !map.contains_key(awaiter) {
        assert(!s.tasks.contains_key(awaiter));
        assert(n.tasks == tasks0);
        assert(awaiter != id);
        assert(!map1.contains_key(awaiter));
        assert(map2 == map1);
        lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
    } else if awaiter == id {
        let proj = spec_project_obj(obj1, now);
        assert(proj.promise.state != PromiseState::Pending);
        match proj.task {
            None => {
                assert(map2 == map1);
            },
            Some(tp) => {
                assert(tp.state == TaskState::Fulfilled);
                assert(map2 == map1);
            },
        }
        if s.tasks.contains_key(id) {
            assert(s.tasks[id].state == TaskState::Fulfilled);
            let stored = s.tasks[id];
            let t = spec_project_task(stored, spec_project_promise(p, now));
            assert(t.state == TaskState::Fulfilled);
            assert(n.tasks == tasks0);
        } else {
            assert(n.tasks == tasks0);
        }
        lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
    } else {
        let objw = map[awaiter];
        let pw = s.promises[awaiter];
        let taw = abstract_task(s, awaiter);
        assert(object_rel(objw, pw, taw));
        assert(map1[awaiter] == objw);
        assert(s.promises.contains_key(awaiter));
        let proj = spec_project_obj(objw, now);
        let pwq = spec_project_promise(pw, now);
        lemma_project_object(objw, pw, taw, now);
        match proj.task {
            None => {
                assert(taw is None);
                assert(!s.tasks.contains_key(awaiter));
                assert(n.tasks == tasks0);
                assert(map2 == map1);
                lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
            },
            Some(tp) => {
                assert(taw is Some);
                assert(s.tasks.contains_key(awaiter));
                let tw = taw.unwrap();
                let t = spec_project_task(tw, pwq);
                assert(task_rel(tp, t));
                assert(callbacks_in(objw.promise.callbacks, o));
                match tp.state {
                    TaskState::Suspended => {
                        assert(objw.promise.state == PromiseState::Pending);
                        let u = TaskV {
                            state: TaskState::Pending,
                            resumes: seq![id],
                            retry_timeout_at: Some(since),
                            ..t
                        };
                        assert(n.tasks == tasks0.insert(awaiter, u));
                        let tc = TkV {
                            state: TaskState::Pending,
                            pid: None,
                            ttl: None,
                            lease_timeout_at: None,
                            retry_timeout_at: Some(since),
                            resumes: seq![id],
                            ..tp
                        };
                        let objw2 = ObjV { task: Some(tc), ..objw };
                        assert(map2 == map1.insert(awaiter, objw2));
                        assert(tp.pid is None);
                        assert(tp.ttl is None);
                        assert(task_rel(tc, u));
                        assert(object_rel(objw2, pw, Some(u)));
                        assert(n.promises == n1.promises.insert(awaiter, pw)) by {
                            assert(n1.promises[awaiter] == pw);
                            assert(n1.promises.insert(awaiter, pw) =~= n1.promises);
                        };
                        assert(n.tasks == n1.tasks.insert(awaiter, u));
                        lemma_origin_update(map1, o, n1, awaiter, objw2, pw, Some(u), n);
                        assert(map2.dom() == map1.dom().insert(awaiter));
                        lemma_within_two(s, n, id, awaiter);
                        assert(n.tasks.dom() == s.tasks.dom().insert(awaiter));
                        assert(finite_store(n));
                        lemma_origin_matched(config, key, o, map, state, now, work, map2, Seq::empty());
                    },
                    TaskState::Fulfilled => {
                        assert(n.tasks == tasks0);
                        assert(map2 == map1);
                        lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
                    },
                    _ => {
                        assert(objw.promise.state == PromiseState::Pending);
                        if tp.resumes.contains(id) {
                            assert(t.resumes.contains(id));
                            assert(n.tasks == tasks0);
                            assert(map2 == map1);
                            lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
                        } else {
                            assert(!t.resumes.contains(id));
                            let u = TaskV { resumes: t.resumes.push(id), ..t };
                            assert(n.tasks == tasks0.insert(awaiter, u));
                            let tc = TkV { resumes: tp.resumes.push(id), ..tp };
                            let objw2 = ObjV { task: Some(tc), ..objw };
                            assert(map2 == map1.insert(awaiter, objw2));
                            assert(task_rel(tc, u));
                            assert(object_rel(objw2, pw, Some(u)));
                            assert(n.promises == n1.promises.insert(awaiter, pw)) by {
                                assert(n1.promises[awaiter] == pw);
                                assert(n1.promises.insert(awaiter, pw) =~= n1.promises);
                            };
                            assert(n.tasks == n1.tasks.insert(awaiter, u));
                            lemma_origin_update(map1, o, n1, awaiter, objw2, pw, Some(u), n);
                            assert(map2.dom() == map1.dom().insert(awaiter));
                            lemma_within_two(s, n, id, awaiter);
                            assert(n.tasks.dom() == s.tasks.dom().insert(awaiter));
                            assert(finite_store(n));
                            lemma_origin_matched(config, key, o, map, state, now, work, map2, Seq::empty());
                        }
                    },
                }
            },
        }
    }
}

/// A settled promise with a listener: both sides drop the listener and tell
/// the address.
pub proof fn lemma_listener_due(
    config: ServerConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state != PromiseState::Pending,
        map[id].promise.callbacks.len() == 0,
        map[id].promise.listeners.len() > 0,
    ensures
        due_agrees(config, key, DocV::Origin(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    assert(promise_rel(obj.promise, p));
    let listeners = obj.promise.listeners;
    let address = listeners[0];
    assert(listeners.contains(address));
    lemma_contains_to_set(listeners, address);
    assert(p.listeners.contains(address));
    let work = InternalV::Listener { awaited: id, address };
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    assert(spec_project_promise(p, now) == p);
    lemma_string_view(id);
    assert(c_string(id) == a_string(id));
    lemma_record(c_string(id), obj.promise, p);
    let rec = spec_promise_record(a_string(id), p);
    assert(rec == spec_record(c_string(id), obj.promise));
    let q = PromiseV { listeners: p.listeners.remove(address), ..p };
    let tasks = if s.tasks.contains_key(id) {
        s.tasks.insert(id, spec_project_task(s.tasks[id], q))
    } else {
        s.tasks
    };
    assert(tasks == s.tasks) by {
        if s.tasks.contains_key(id) {
            assert(ta is Some);
            assert(obj.task is Some);
            assert(obj.task.unwrap().state == TaskState::Fulfilled);
            assert(s.tasks[id].state == TaskState::Fulfilled);
            assert(spec_project_task(s.tasks[id], q) == s.tasks[id]);
            assert(s.tasks.insert(id, s.tasks[id]) =~= s.tasks);
        }
    };
    let n = AStore { promises: s.promises.insert(id, q), tasks, ..s };
    let outcome = spec_process_work(config, work, s, now);
    assert(outcome == spec_listener(s, id, address, now));
    assert(outcome == spec_did(n, Seq::empty(), seq![DispatchV::Unblock { address, promise: rec }]));
    lemma_skip_no_duplicates(listeners);
    let obj2 = ObjV { promise: PromV { listeners: listeners.skip(1), ..obj.promise }, ..obj };
    assert(promise_rel(obj2.promise, q));
    assert(object_rel(obj2, q, ta));
    assert(callbacks_in(obj2.promise.callbacks, o));
    lemma_tasks_kept(s, id);
    lemma_one_changed(map, o, s, id, obj2, q, ta, n);
    let notes = seq![NoteV::Unblock { address, promise: rec }];
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map.insert(id, obj2), notes));
    lemma_sends_unblock(address, rec);
    lemma_origin_matched(config, key, o, map, state, now, work, map.insert(id, obj2), notes);
}

/// The due step of an origin document.
pub proof fn lemma_origin_due(
    config: ServerConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: StateV,
    now: Time,
)
    requires
        key == spec_origin_key(o),
        map.dom().finite(),
        origin_rel(map, o, state.store),
        finite_store(state.store),
    ensures
        due_agrees(config, key, DocV::Origin(map), state, now),
{
    let doc = DocV::Origin(map);
    let keys = c_sorted(map.dom());
    lemma_sorted(map.dom());
    assert forall|i: int| 0 <= i < keys.len() implies map.contains_key(#[trigger] keys[i]) by {
        assert(map.dom().contains(keys[i]));
    };
    lemma_due_id(map, keys, now);
    match spec_due_id(map, keys, now) {
        None => {
            assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
        },
        Some(id) => {
            assert(map.contains_key(id));
            assert(due_context(key, o, map, state.store, id));
            let obj = map[id];
            let (map2, notes) = spec_step_object(map, id, now, config.retry_timeout);
            assert(spec_run_due(doc, now, config.retry_timeout) == (DocV::Origin(map2), None::<Response>, Seq::<PendingV>::empty(), notes));
            if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
                lemma_promise_due(config, key, o, map, state, now, id);
            } else if obj.promise.state == PromiseState::Pending {
                match obj.task {
                    Some(t) if t.state == TaskState::Acquired && match t.lease_timeout_at {
                        Some(at) => at <= now,
                        None => false,
                    } => {
                        lemma_lease_due(config, key, o, map, state, now, id);
                    },
                    Some(t) if t.state == TaskState::Pending && match t.retry_timeout_at {
                        Some(at) => at <= now,
                        None => false,
                    } => {
                        lemma_retry_due(config, key, o, map, state, now, id);
                    },
                    _ => {
                        assert(map2 == map);
                        assert(notes.len() == 0);
                    },
                }
            } else if obj.promise.callbacks.len() > 0 {
                lemma_callback_due(config, key, o, map, state, now, id);
            } else if obj.promise.listeners.len() > 0 {
                lemma_listener_due(config, key, o, map, state, now, id);
            } else {
                assert(map2 == map);
                assert(notes.len() == 0);
            }
        },
    }
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
    ensures
        due_agrees(config, key, DocV::Schedule(Some(sch)), state, now),
{
    let s = state.store;
    let doc = DocV::Schedule(Some(sch));
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
    let (next, _, born, notes) = spec_run_due(doc, now, config.retry_timeout);
    let pending = PendingV {
        promise: spec_expand(sch.promise_id@, sch.id@, at),
        at,
        timeout: sch.promise_timeout,
        param: sch.promise_param,
        tags: sch.promise_tags,
    };
    let sch2 = Schedule { last_run_at: Some(at), next_run_at: spec_next_cron(sch.cron@, at), ..sch };
    assert(next == DocV::Schedule(Some(sch2)));
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
    assert(due_matched(config, key, doc, state, now, r));
    lemma_matched(config, key, doc, state, now, r);
}

// ---------------------------------------------------------------------------
// Every due step
// ---------------------------------------------------------------------------

pub proof fn lemma_due_agrees(config: ServerConfig, key: Seq<char>, doc: DocV, state: StateV, now: Time)
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
            DocV::Schedule(Some(sch)) => {
                if sch.next_run_at <= now {
                    lemma_schedule_due(config, key, id, sch, state, now);
                } else {
                    assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
                }
            },
            _ => {
                assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
            },
        }
    } else if spec_starts(key, origin_prefix()) {
        let o = key.skip(2);
        lemma_starts_split(key, origin_prefix());
        assert(key == spec_origin_key(o));
        match doc {
            DocV::Origin(map) => {
                lemma_origin_due(config, key, o, map, state, now);
            },
            _ => {},
        }
    } else {
        match doc {
            DocV::Origin(map) => {
                lemma_sorted(map.dom());
                assert(c_sorted(map.dom()).len() == 0);
                assert(spec_due_id(map, c_sorted(map.dom()), now) is None);
                assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
            },
            DocV::Schedule(_) => {
                assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
            },
        }
    }
}

pub proof fn lemma_dues_agree(config: ServerConfig)
    ensures
        dues_agree(config),
{
    assert forall|key: Seq<char>, doc: DocV, state: StateV, now: u64|
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
                    retry_timeout_at: Some(spec_offer_at(pending.tags, pending.at)),
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
            retry_timeout_at: Some(spec_offer_at(tags, at)),
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

pub proof fn lemma_occurrence_agrees(pending: PendingV, doc: DocV, s: AStore, now: Time)
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
    let map = spec_origin_map(doc);
    assert(doc == DocV::Origin(map));
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
                retry_timeout_at: Some(spec_offer_at(pending.tags, pending.at)),
                ..t
            }),
            other => other,
        };
        let obj = ObjV { promise, task };
        assert(next == DocV::Origin(map.insert(x, obj)));
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
    assert forall|pending: PendingV, doc: DocV, s: AStore, now: u64|
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
