//! The conformance catalogue, transcribed.
//!
//! `resonatehq/resonate`, `spec/02-abstract/properties.lean`, entry for
//! entry, same names. A `.state` entry is a predicate on `(now, s)`; a
//! `.trans` entry on `(now, a, b)` with `b` reached from `a` in one step.
//! Lean quantifies over lists of objects; here the state is the fold of the
//! rows, a map by id, and `all` over a list is `forall` over the map's keys.
//! The three `well_formed_store_*_unique` entries are the row-level
//! well-formedness `State::wf`, which is what makes the fold a bijection.
//!
//! `inv` collects the `.state` entries, `legal` the `.trans` entries, and
//! `internal_legal` the two sweeper entries that hold of internal steps only.

use vstd::prelude::*;

use crate::ident::same_origin_spec;
use crate::store::AState;
use crate::tags::{tags_get, timer_targeted, OType};
use crate::types::*;

verus! {

// ---------------------------------------------------------------------------
// Reading the state
// ---------------------------------------------------------------------------

impl AState {
    /// `s.promise? id`.
    pub open spec fn promise_of(self, id: Seq<char>) -> Option<APromise> {
        if self.objects.contains_key(id) { Some(self.objects[id]) } else { None }
    }

    /// `s.task? id`.
    pub open spec fn task_of(self, id: Seq<char>) -> Option<ATask> {
        if self.objects.contains_key(id) { self.objects[id].task } else { None }
    }

    pub open spec fn has_task(self, id: Seq<char>) -> bool {
        self.task_of(id) is Some
    }

    /// Every entry sits under its own key. True of any fold.
    pub open spec fn keyed(self) -> bool {
        &&& forall|id: Seq<char>| #[trigger] self.objects.contains_key(id) ==> self.objects[id].id == id
        &&& forall|id: Seq<char>| #[trigger] self.schedules.contains_key(id) ==> self.schedules[id].id == id
        &&& forall|k: OutboxKey| #[trigger] self.outbox.contains_key(k) ==> self.outbox[k].key() == k
    }
}

pub open spec fn no_dups<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && s[i] == s[j] ==> i == j
}

/// `xs ⊆ ys`.
pub open spec fn subset_of<T>(xs: Seq<T>, ys: Seq<T>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> ys.contains(#[trigger] xs[i])
}

pub open spec fn task_cleared(t: ATask) -> bool {
    t.pid is None && t.ttl is None && t.lease_timeout_at is None && t.retry_timeout_at is None
}

pub open spec fn opt_or_zero(o: Option<nat>) -> nat {
    match o { Some(x) => x, None => 0 }
}

// ---------------------------------------------------------------------------
// .state — one object
// ---------------------------------------------------------------------------

pub open spec fn well_formed_promise_created_at_lte_timeout_at(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        s.objects[id].created_at <= s.objects[id].timeout_at
}

pub open spec fn well_formed_promise_pending_created_before_deadline(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        (s.objects[id].state != PromiseState::Pending || s.objects[id].created_at < s.objects[id].timeout_at)
}

pub open spec fn well_formed_promise_settled_at_lte_timeout_at(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        match s.objects[id].settled_at { None => true, Some(x) => x <= s.objects[id].timeout_at }
}

pub open spec fn well_formed_promise_created_at_lte_settled_at(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        match s.objects[id].settled_at { None => true, Some(x) => s.objects[id].created_at <= x }
}

pub open spec fn well_formed_promise_settled_at_iff_not_pending(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        ((s.objects[id].state != PromiseState::Pending) == (s.objects[id].settled_at is Some))
}

pub open spec fn well_formed_promise_pending_has_no_value(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        (s.objects[id].state != PromiseState::Pending || s.objects[id].value.is_empty())
}

pub open spec fn deadline_verdict(p: APromise) -> PromiseState {
    if p.is_timer() { PromiseState::Resolved } else { PromiseState::RejectedTimedout }
}

pub open spec fn well_formed_promise_deadline_verdict_matches_timer_tag(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        (s.objects[id].settled_at != Some(s.objects[id].timeout_at)
            || s.objects[id].state == deadline_verdict(s.objects[id]))
}

pub open spec fn well_formed_promise_deadline_settlement_has_no_value(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        (s.objects[id].settled_at != Some(s.objects[id].timeout_at) || s.objects[id].value.is_empty())
}

pub open spec fn well_formed_promise_timer_not_targeted(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==> !timer_targeted(s.objects[id].tags)
}

pub open spec fn well_formed_promise_timedout_is_server_owned(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        (s.objects[id].state != PromiseState::RejectedTimedout
            || s.objects[id].settled_at == Some(s.objects[id].timeout_at))
}

pub open spec fn well_formed_promise_callbacks_unique(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==> no_dups(s.objects[id].callbacks)
}

pub open spec fn well_formed_promise_listeners_unique(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==> no_dups(s.objects[id].listeners)
}

pub open spec fn well_formed_promise_obligations_require_external(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        ((s.objects[id].callbacks.len() == 0 && s.objects[id].listeners.len() == 0)
            || s.objects[id].otype().awaitable())
}

pub open spec fn well_formed_promise_awaiter_is_not_self(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==> !s.objects[id].callbacks.contains(id)
}

pub open spec fn well_formed_promise_callbacks_same_origin(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>, i: int| #[trigger] s.objects.contains_key(id)
        && 0 <= i < s.objects[id].callbacks.len() ==>
            same_origin_spec(#[trigger] s.objects[id].callbacks[i], id)
}

pub open spec fn well_formed_promise_created_at_lte_now(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==> s.objects[id].created_at <= now
}

pub open spec fn well_formed_promise_settled_at_lte_now(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        match s.objects[id].settled_at { None => true, Some(x) => x <= now }
}

/// `s.tasks.all f`: every object's task, where it has one.
pub open spec fn all_tasks(s: AState, f: spec_fn(ATask) -> bool) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        match s.objects[id].task { Some(t) => f(t), None => true }
}

pub open spec fn well_formed_task_acquired_iff_has_pid(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| (t.state == TaskState::Acquired) == (t.pid is Some))
}

pub open spec fn well_formed_task_acquired_iff_has_ttl(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| (t.state == TaskState::Acquired) == (t.ttl is Some))
}

pub open spec fn well_formed_task_acquired_iff_has_lease_timeout_at(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| (t.state == TaskState::Acquired) == (t.lease_timeout_at is Some))
}

pub open spec fn well_formed_task_pending_iff_has_retry_timeout_at(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| (t.state == TaskState::Pending) == (t.retry_timeout_at is Some))
}

pub open spec fn well_formed_task_fulfilled_is_cleared(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| t.state != TaskState::Fulfilled || (task_cleared(t) && t.resumes.len() == 0))
}

pub open spec fn well_formed_task_suspended_is_cleared(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| t.state != TaskState::Suspended || task_cleared(t))
}

pub open spec fn well_formed_task_halted_is_cleared(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| t.state != TaskState::Halted || task_cleared(t))
}

pub open spec fn well_formed_task_suspended_has_no_resumes(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| t.state != TaskState::Suspended || t.resumes.len() == 0)
}

pub open spec fn well_formed_task_resumes_unique(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| no_dups(t.resumes))
}

pub open spec fn well_formed_task_acquired_version_positive(_now: nat, s: AState) -> bool {
    all_tasks(s, |t: ATask| t.state != TaskState::Acquired || 1 <= t.version)
}

pub open spec fn well_formed_schedule_promise_tags_not_timer_targeted(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==> !timer_targeted(s.schedules[id].promise_tags)
}

pub open spec fn well_formed_schedule_created_at_lte_next_run_at(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==>
        s.schedules[id].created_at <= s.schedules[id].next_run_at
}

pub open spec fn well_formed_schedule_created_at_lte_last_run_at(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==>
        match s.schedules[id].last_run_at { None => true, Some(l) => s.schedules[id].created_at <= l }
}

pub open spec fn well_formed_schedule_last_run_at_lt_next_run_at(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==>
        match s.schedules[id].last_run_at { None => true, Some(l) => l < s.schedules[id].next_run_at }
}

// The three uniqueness entries are stated on the rows, where ids can collide.

pub open spec fn well_formed_store_object_ids_unique(_now: nat, s: crate::store::State) -> bool {
    crate::store::distinct_by(s.objects@, crate::store::obj_key())
}

pub open spec fn well_formed_store_schedule_ids_unique(_now: nat, s: crate::store::State) -> bool {
    crate::store::distinct_by(s.schedules@, crate::store::sched_key())
}

pub open spec fn well_formed_store_outbox_keys_unique(_now: nat, s: crate::store::State) -> bool {
    crate::store::distinct_by(s.outbox@, crate::store::out_key())
}

// ---------------------------------------------------------------------------
// .state — several objects
// ---------------------------------------------------------------------------

pub open spec fn consistent_task_iff_kind_task(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        ((s.objects[id].task is Some) == (s.objects[id].otype() == OType::Runnable))
}

pub open spec fn consistent_settled_promise_has_fulfilled_task(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        (s.objects[id].state == PromiseState::Pending
            || match s.objects[id].task { Some(t) => t.state == TaskState::Fulfilled, None => true })
}

pub open spec fn consistent_callback_awaiter_is_targeted(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>, i: int| #[trigger] s.objects.contains_key(id)
        && 0 <= i < s.objects[id].callbacks.len() ==>
            s.objects.contains_key(#[trigger] s.objects[id].callbacks[i])
            && s.objects[s.objects[id].callbacks[i]].otype() == OType::Runnable
}

pub open spec fn consistent_outbox_execute_names_existing_task(_now: nat, s: AState) -> bool {
    forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) ==>
        match s.outbox[k].message {
            AMessage::Execute { task_id, .. } => s.has_task(task_id),
            AMessage::Unblock(_) => true,
        }
}

pub open spec fn consistent_outbox_never_ahead(_now: nat, s: AState) -> bool {
    forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) ==>
        match s.outbox[k].message {
            AMessage::Execute { task_id, version } =>
                match s.task_of(task_id) { Some(t) => version <= t.version, None => true },
            AMessage::Unblock(_) => true,
        }
}

pub open spec fn target_or_empty(p: APromise) -> Seq<char> {
    crate::tags::target_of(p.tags)
}

pub open spec fn consistent_outbox_execute_address_is_target_tag(_now: nat, s: AState) -> bool {
    forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) ==>
        match s.outbox[k].message {
            AMessage::Execute { task_id, .. } =>
                match s.promise_of(task_id) { Some(p) => s.outbox[k].address == target_or_empty(p), None => true },
            AMessage::Unblock(_) => true,
        }
}

pub open spec fn consistent_outbox_unblock_names_settled_promise(_now: nat, s: AState) -> bool {
    forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) ==>
        match s.outbox[k].message {
            AMessage::Unblock(r) =>
                r.state != PromiseState::Pending
                && s.objects.contains_key(r.id) && s.objects[r.id].state != PromiseState::Pending,
            AMessage::Execute { .. } => true,
        }
}

pub open spec fn some_callbacks_contain(s: AState, awaiter: Seq<char>) -> bool {
    exists|id: Seq<char>| #[trigger] s.objects.contains_key(id) && s.objects[id].callbacks.contains(awaiter)
}

pub open spec fn consistent_suspended_task_holds_rung(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        match s.objects[id].task {
            Some(t) => t.state != TaskState::Suspended
                || s.objects[id].project_promise(now).state != PromiseState::Pending
                || some_callbacks_contain(s, id),
            None => true,
        }
}

pub open spec fn consistent_settled_task_promise_settled(_now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        match s.objects[id].task {
            Some(t) => t.state != TaskState::Fulfilled || s.objects[id].state != PromiseState::Pending,
            None => true,
        }
}

// ---------------------------------------------------------------------------
// .trans — records and sets
// ---------------------------------------------------------------------------

pub open spec fn preserved_promise_birth_fields_immutable(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        match b.promise_of(id) {
            None => true,
            Some(q) => {
                let p = a.objects[id];
                q.param.data == p.param.data && q.param.headers == p.param.headers
                    && q.tags == p.tags && q.timeout_at == p.timeout_at && q.created_at == p.created_at
            },
        }
}

pub open spec fn preserved_settled_promise_record(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        (a.objects[id].state == PromiseState::Pending
            || match b.promise_of(id) {
                None => false,
                Some(q) => {
                    let p = a.objects[id];
                    q.state == p.state && q.settled_at == p.settled_at
                        && q.value.data == p.value.data && q.value.headers == p.value.headers
                },
            })
}

pub open spec fn monotone_promise_set_grows(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> b.objects.contains_key(id)
}

pub open spec fn monotone_task_set_grows(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        (a.objects[id].task is None || b.has_task(id))
}

/// `a.objects.all fun o => o.task.all fun t => match b.task? o.id with | none => <none_case> | some u => f t u`.
pub open spec fn all_task_pairs(a: AState, b: AState, none_case: bool, f: spec_fn(ATask, ATask) -> bool) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        match a.objects[id].task {
            None => true,
            Some(t) => match b.task_of(id) { None => none_case, Some(u) => f(t, u) },
        }
}

pub open spec fn monotone_task_version_increases_only_on_acquisition(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask|
        if t.state == TaskState::Pending && u.state == TaskState::Acquired {
            u.version == t.version + 1
        } else {
            u.version == t.version
        })
}

pub open spec fn preserved_fulfilled_task(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, false, |t: ATask, u: ATask|
        t.state != TaskState::Fulfilled
            || (u.state == TaskState::Fulfilled && u.version == t.version && u.resumes.len() == 0
                && task_cleared(u)))
}

pub open spec fn preserved_no_dead_dispatch(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        match b.objects[id].task {
            None => true,
            Some(u) => u.state != TaskState::Pending
                || (match a.task_of(id) { Some(t) => t.state == TaskState::Pending, None => false })
                || b.objects[id].project_promise(now).state == PromiseState::Pending,
        }
}

pub open spec fn has_execute(s: AState, id: Seq<char>, v: nat, address: Seq<char>) -> bool {
    exists|k: OutboxKey| #[trigger] s.outbox.contains_key(k)
        && s.outbox[k].address == address
        && match s.outbox[k].message {
            AMessage::Execute { task_id, version } => task_id == id && version == v,
            AMessage::Unblock(_) => false,
        }
}

pub open spec fn has_unblock(s: AState, id: Seq<char>, address: Seq<char>) -> bool {
    exists|k: OutboxKey| #[trigger] s.outbox.contains_key(k)
        && s.outbox[k].address == address
        && match s.outbox[k].message {
            AMessage::Unblock(r) => r.id == id,
            AMessage::Execute { .. } => false,
        }
}

pub open spec fn preserved_execute_only_for_live_task(now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) ==>
        match b.outbox[k].message {
            AMessage::Unblock(_) => true,
            AMessage::Execute { task_id, version } =>
                has_execute(a, task_id, version, b.outbox[k].address)
                || match b.promise_of(task_id) {
                    Some(p) => p.project_promise(now).state == PromiseState::Pending,
                    None => true,
                },
        }
}

// ---------------------------------------------------------------------------
// .trans — field-level evolution
// ---------------------------------------------------------------------------

pub open spec fn preserved_promise_state_frozen_once_settled(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        (a.objects[id].state == PromiseState::Pending
            || match b.promise_of(id) { None => false, Some(q) => q.state == a.objects[id].state })
}

pub open spec fn preserved_promise_settlement_is_one_way(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        (b.objects[id].state != PromiseState::Pending
            || match a.promise_of(id) { Some(p) => p.state == PromiseState::Pending, None => true })
}

pub open spec fn consistent_promise_settled_at_moves_with_state(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        match b.promise_of(id) {
            None => false,
            Some(q) => (q.settled_at != a.objects[id].settled_at) == (q.state != a.objects[id].state),
        }
}

pub open spec fn preserved_promise_value_until_settlement(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        match b.promise_of(id) {
            None => false,
            Some(q) => q.state != PromiseState::Pending
                || (q.value.data == a.objects[id].value.data && q.value.headers == a.objects[id].value.headers),
        }
}

pub open spec fn preserved_promise_no_duplicate_ids(_now: nat, _a: crate::store::State, b: crate::store::State) -> bool {
    crate::store::distinct_by(b.objects@, crate::store::obj_key())
}

pub open spec fn monotone_promise_callbacks_grow_while_pending(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        (b.objects[id].state != PromiseState::Pending
            || match a.promise_of(id) {
                None => b.objects[id].callbacks.len() == 0,
                Some(p) => subset_of(p.callbacks, b.objects[id].callbacks),
            })
}

pub open spec fn monotone_promise_callbacks_shrink_once_settled(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        (b.objects[id].state == PromiseState::Pending
            || match a.promise_of(id) {
                None => b.objects[id].callbacks.len() == 0,
                Some(p) => subset_of(b.objects[id].callbacks, p.callbacks),
            })
}

pub open spec fn monotone_promise_listeners_grow_while_pending(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        (b.objects[id].state != PromiseState::Pending
            || match a.promise_of(id) {
                None => b.objects[id].listeners.len() == 0,
                Some(p) => subset_of(p.listeners, b.objects[id].listeners),
            })
}

pub open spec fn monotone_promise_listeners_shrink_once_settled(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        (b.objects[id].state == PromiseState::Pending
            || match a.promise_of(id) {
                None => b.objects[id].listeners.len() == 0,
                Some(p) => subset_of(b.objects[id].listeners, p.listeners),
            })
}

// ---------------------------------------------------------------------------
// .trans — the state machine edges
// ---------------------------------------------------------------------------

pub open spec fn promise_edge_admissible(p: PromiseState, q: PromiseState) -> bool {
    p == q || p == PromiseState::Pending
}

pub open spec fn consistent_promise_state_edge_admissible(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        match b.promise_of(id) { None => true, Some(q) => promise_edge_admissible(a.objects[id].state, q.state) }
}

pub open spec fn task_edge_admissible(t: TaskState, u: TaskState) -> bool {
    ||| t == u
    ||| t == TaskState::Pending && (u == TaskState::Acquired || u == TaskState::Halted || u == TaskState::Fulfilled)
    ||| t == TaskState::Acquired && (u == TaskState::Pending || u == TaskState::Suspended
            || u == TaskState::Halted || u == TaskState::Fulfilled)
    ||| t == TaskState::Suspended && (u == TaskState::Pending || u == TaskState::Halted || u == TaskState::Fulfilled)
    ||| t == TaskState::Halted && (u == TaskState::Pending || u == TaskState::Fulfilled)
}

pub open spec fn consistent_task_state_edge_admissible(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask| task_edge_admissible(t.state, u.state))
}

pub open spec fn preserved_task_acquisition_only_from_pending(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        match b.objects[id].task {
            None => true,
            Some(u) => u.state != TaskState::Acquired
                || match a.task_of(id) {
                    Some(t) => t.state == TaskState::Pending || t.state == TaskState::Acquired,
                    None => true,
                },
        }
}

pub open spec fn preserved_task_suspension_only_from_acquired(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        match b.objects[id].task {
            None => true,
            Some(u) => u.state != TaskState::Suspended
                || match a.task_of(id) {
                    Some(t) => t.state == TaskState::Acquired || t.state == TaskState::Suspended,
                    None => false,
                },
        }
}

pub open spec fn preserved_task_halted_only_reenters_via_pending(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, false, |t: ATask, u: ATask|
        t.state != TaskState::Halted
            || u.state == TaskState::Halted || u.state == TaskState::Pending || u.state == TaskState::Fulfilled)
}

// ---------------------------------------------------------------------------
// .trans — cross-object coupling
// ---------------------------------------------------------------------------

pub open spec fn consistent_settlement_fulfils_task(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        (a.objects[id].state != PromiseState::Pending
            || match (b.promise_of(id), b.task_of(id)) {
                (Some(q), Some(u)) => q.state == PromiseState::Pending || u.state == TaskState::Fulfilled,
                _ => true,
            })
}

pub open spec fn consistent_task_fulfilment_needs_settlement(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        match b.objects[id].task {
            None => true,
            Some(u) => u.state != TaskState::Fulfilled
                || match a.task_of(id) {
                    None => true,
                    Some(t) => t.state == TaskState::Fulfilled
                        || match (a.promise_of(id), b.promise_of(id)) {
                            (Some(p), Some(q)) => p.state == PromiseState::Pending && q.state != PromiseState::Pending,
                            _ => false,
                        },
                },
        }
}

pub open spec fn consistent_obligation_discharge_requires_settled(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        match b.promise_of(id) {
            None => true,
            Some(q) => (subset_of(a.objects[id].callbacks, q.callbacks) && subset_of(a.objects[id].listeners, q.listeners))
                || q.state != PromiseState::Pending,
        }
}

pub open spec fn consistent_callback_consumption_resumes_awaiter(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>, i: int| #[trigger] a.objects.contains_key(id)
        && 0 <= i < a.objects[id].callbacks.len() ==> {
            let x = #[trigger] a.objects[id].callbacks[i];
            (match b.promise_of(id) { None => true, Some(q) => q.callbacks.contains(x) })
            || match b.task_of(x) {
                None => true,
                Some(u) => u.state == TaskState::Fulfilled || u.resumes.contains(id),
            }
        }
}

/// Exactly one `unblock` for `(id, addr)`, settled. In a map keyed by
/// `Notify(id, addr)` that is the entry at that key.
pub open spec fn one_unblock(s: AState, id: Seq<char>, addr: Seq<char>) -> bool {
    &&& s.outbox.contains_key(OutboxKey::Notify(id, addr))
    &&& s.outbox[OutboxKey::Notify(id, addr)].address == addr
    &&& match s.outbox[OutboxKey::Notify(id, addr)].message {
        AMessage::Unblock(r) => r.id == id && r.state != PromiseState::Pending,
        AMessage::Execute { .. } => false,
    }
    &&& forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) && s.outbox[k].address == addr
        && (match s.outbox[k].message { AMessage::Unblock(r) => r.id == id, AMessage::Execute { .. } => false })
        ==> k == OutboxKey::Notify(id, addr)
}

pub open spec fn consistent_listener_consumption_enqueues_unblock(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>, i: int| #[trigger] a.objects.contains_key(id)
        && 0 <= i < a.objects[id].listeners.len() ==> {
            let addr = #[trigger] a.objects[id].listeners[i];
            (match b.promise_of(id) { None => true, Some(q) => q.listeners.contains(addr) })
            || one_unblock(b, id, addr)
        }
}

pub open spec fn consistent_wake_follows_callback_consumption(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        match b.objects[id].task {
            None => true,
            Some(u) => match a.task_of(id) {
                None => true,
                Some(t) => !(t.state == TaskState::Suspended && u.state == TaskState::Pending)
                    || exists|pid: Seq<char>| #[trigger] a.objects.contains_key(pid)
                        && a.objects[pid].callbacks.contains(id)
                        && (match b.promise_of(pid) { None => false, Some(q) => !q.callbacks.contains(id) })
                        && u.resumes.contains(pid),
            },
        }
}

pub open spec fn consistent_suspension_registers_callback(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        match b.objects[id].task {
            None => true,
            Some(u) => u.state != TaskState::Suspended
                || (match a.task_of(id) { None => false, Some(t) => t.state == TaskState::Suspended })
                || exists|qid: Seq<char>| #[trigger] b.objects.contains_key(qid)
                    && b.objects[qid].callbacks.contains(id)
                    && (match a.promise_of(qid) { None => true, Some(p) => !p.callbacks.contains(id) })
                    && b.objects[qid].state == PromiseState::Pending,
        }
}

pub open spec fn consistent_task_birth_couples_promise_birth(_now: nat, a: AState, b: AState) -> bool {
    &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        match b.objects[id].task {
            None => true,
            Some(u) => a.has_task(id)
                || (!a.objects.contains_key(id)
                    && b.objects[id].otype() == OType::Runnable
                    && (if u.state == TaskState::Fulfilled {
                            b.objects[id].state != PromiseState::Pending
                        } else {
                            b.objects[id].state == PromiseState::Pending
                        })
                    && ((u.state == TaskState::Pending && u.version == 0)
                        || (u.state == TaskState::Acquired && 1 <= u.version)
                        || (u.state == TaskState::Fulfilled && u.version == 0))),
        }
    &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        a.objects.contains_key(id) || b.objects[id].otype() != OType::Runnable || b.objects[id].task is Some
}

// ---------------------------------------------------------------------------
// .trans — the outbox
// ---------------------------------------------------------------------------

pub open spec fn monotone_outbox_keys_never_disappear(_now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] a.outbox.contains_key(k) ==> b.outbox.contains_key(k)
}

pub open spec fn consistent_new_execute_matches_task_and_target(_now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) ==>
        match b.outbox[k].message {
            AMessage::Unblock(_) => true,
            AMessage::Execute { task_id, version } =>
                has_execute(a, task_id, version, b.outbox[k].address)
                || ((match b.task_of(task_id) { Some(t) => t.version == version, None => false })
                    && (match b.promise_of(task_id) {
                        Some(p) => b.outbox[k].address == target_or_empty(p),
                        None => false,
                    })),
        }
}

pub open spec fn consistent_new_unblock_carries_stored_record(_now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) ==>
        match b.outbox[k].message {
            AMessage::Execute { .. } => true,
            AMessage::Unblock(r) =>
                has_unblock(a, r.id, b.outbox[k].address)
                || (r.state != PromiseState::Pending
                    && match b.promise_of(r.id) {
                        Some(p) => p.state == r.state && p.settled_at == r.settled_at
                            && p.value.data == r.value.data && p.timeout_at == r.timeout_at
                            && p.created_at == r.created_at,
                        None => false,
                    }),
        }
}

pub open spec fn consistent_new_unblock_discharges_its_listener(_now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) ==>
        match b.outbox[k].message {
            AMessage::Execute { .. } => true,
            AMessage::Unblock(r) =>
                has_unblock(a, r.id, b.outbox[k].address)
                || (a.objects.contains_key(r.id) && a.objects[r.id].listeners.contains(b.outbox[k].address)
                    && (b.objects.contains_key(r.id) ==> !b.objects[r.id].listeners.contains(b.outbox[k].address))),
        }
}

// ---------------------------------------------------------------------------
// .trans — schedules and the task ledger
// ---------------------------------------------------------------------------

pub open spec fn preserved_schedule_birth_fields_immutable(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.schedules.contains_key(id) ==>
        (!b.schedules.contains_key(id) || {
            let c = a.schedules[id];
            let d = b.schedules[id];
            d.cron == c.cron && d.promise_id == c.promise_id && d.promise_timeout == c.promise_timeout
                && d.promise_param.data == c.promise_param.data
                && d.promise_param.headers == c.promise_param.headers
                && d.promise_tags == c.promise_tags && d.created_at == c.created_at
        })
}

pub open spec fn consistent_task_birth_state(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        match b.objects[id].task {
            None => true,
            Some(u) => a.has_task(id)
                || (u.state == TaskState::Pending && u.retry_timeout_at is Some
                    && u.pid is None && u.ttl is None && u.lease_timeout_at is None && u.resumes.len() == 0)
                || (u.state == TaskState::Fulfilled && task_cleared(u) && u.resumes.len() == 0)
                || (u.state == TaskState::Acquired && 1 <= u.version && u.retry_timeout_at is None
                    && u.pid is Some && u.ttl is Some && u.lease_timeout_at is Some && u.resumes.len() == 0),
        }
}

pub open spec fn consistent_task_lease_released_atomically(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask|
        !(t.state == TaskState::Acquired && u.state != TaskState::Acquired)
            || (u.pid is None && u.ttl is None && u.lease_timeout_at is None && u.version == t.version))
}

pub open spec fn preserved_task_lease_holder_stable(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask|
        !(t.state == TaskState::Acquired && u.state == TaskState::Acquired && u.version == t.version)
            || (u.pid == t.pid && u.ttl == t.ttl))
}

pub open spec fn consistent_task_lease_fields_move_together(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask| {
        ||| (u.pid == t.pid && u.ttl == t.ttl && u.lease_timeout_at == t.lease_timeout_at)
        ||| (t.state != TaskState::Acquired && u.state == TaskState::Acquired
                && u.pid is Some && u.ttl is Some && u.lease_timeout_at is Some)
        ||| (t.state == TaskState::Acquired && u.state != TaskState::Acquired
                && u.pid is None && u.ttl is None && u.lease_timeout_at is None)
        ||| (t.state == TaskState::Acquired && u.state == TaskState::Acquired && u.pid == t.pid && u.ttl == t.ttl)
    })
}

pub open spec fn monotone_task_resumes_grow_or_clear(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask| u.resumes.len() == 0 || subset_of(t.resumes, u.resumes))
}

pub open spec fn consistent_task_resumes_cleared_only_on_dispatch_or_park(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask|
        !(t.resumes.len() != 0 && u.resumes.len() == 0)
            || u.state == TaskState::Acquired || u.state == TaskState::Suspended || u.state == TaskState::Fulfilled)
}

pub open spec fn consistent_task_acquisition_is_atomic(now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask|
        !(t.state != TaskState::Acquired && u.state == TaskState::Acquired)
            || (t.state == TaskState::Pending && t.version < u.version
                && u.pid is Some && u.ttl is Some
                && u.lease_timeout_at == Some((now + opt_or_zero(u.ttl)) as nat)
                && u.retry_timeout_at is None && u.resumes.len() == 0))
}

pub open spec fn consistent_task_lease_deadline_is_now_plus_ttl(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        match b.objects[id].task {
            None => true,
            Some(u) => match u.lease_timeout_at {
                None => true,
                Some(d) => d == now + opt_or_zero(u.ttl)
                    || match a.task_of(id) {
                        Some(t) => t.lease_timeout_at == Some(d) && t.ttl == u.ttl && t.state == u.state,
                        None => false,
                    },
            },
        }
}

pub open spec fn consistent_task_pending_entry_arms_retry(now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask|
        !(t.state != TaskState::Pending && u.state == TaskState::Pending) || u.retry_timeout_at == Some(now))
}

pub open spec fn consistent_task_retry_rearm_only_when_due(now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask|
        !(t.state == TaskState::Pending && u.state == TaskState::Pending && u.retry_timeout_at != t.retry_timeout_at)
            || match t.retry_timeout_at { Some(due) => due <= now, None => false })
}

pub open spec fn monotone_task_retry_rearm_advances(now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask|
        t.state != TaskState::Pending
            || u.state != TaskState::Pending || u.retry_timeout_at == t.retry_timeout_at
            || match u.retry_timeout_at { Some(d) => now < d, None => false })
}

pub open spec fn consistent_task_wake_records_resume(now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask|
        !(t.state == TaskState::Suspended && u.state == TaskState::Pending)
            || (u.resumes.len() != 0 && u.retry_timeout_at == Some(now) && u.version == t.version))
}

// ---------------------------------------------------------------------------
// .trans — settlement
// ---------------------------------------------------------------------------

pub open spec fn consistent_promise_settlement_stamp(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        (a.objects[id].state != PromiseState::Pending
            || match b.promise_of(id) {
                None => false,
                Some(q) => {
                    let p = a.objects[id];
                    ||| q.state == PromiseState::Pending
                    ||| (q.settled_at == Some(now) && now < q.timeout_at && q.state != PromiseState::RejectedTimedout)
                    ||| (q.settled_at == Some(q.timeout_at) && q.timeout_at <= now
                            && q.state == deadline_verdict(q)
                            && q.value.data == p.value.data && q.value.headers == p.value.headers)
                },
            })
}

pub open spec fn preserved_timedout_is_server_owned(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        (a.objects[id].state != PromiseState::Pending
            || match b.promise_of(id) {
                None => true,
                Some(q) => q.state != PromiseState::RejectedTimedout
                    || (a.objects[id].timeout_at <= now && q.settled_at == Some(a.objects[id].timeout_at)),
            })
}

pub open spec fn consistent_new_promise_born_clean(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        (a.objects.contains_key(id) || {
            let q = b.objects[id];
            q.callbacks.len() == 0 && q.listeners.len() == 0 && q.value.is_empty()
                && q.created_at <= now
                && ((q.state == PromiseState::Pending && q.settled_at is None && q.created_at < q.timeout_at)
                    || (q.settled_at == Some(q.timeout_at) && q.created_at == q.timeout_at
                        && q.timeout_at <= now && q.state == deadline_verdict(q)))
        })
}

// ---------------------------------------------------------------------------
// The sweeper entries: internal steps only
// ---------------------------------------------------------------------------

pub open spec fn task_edge_internal_admissible(t: TaskState, u: TaskState) -> bool {
    ||| t == u
    ||| u == TaskState::Fulfilled
    ||| t == TaskState::Acquired && u == TaskState::Pending
    ||| t == TaskState::Suspended && u == TaskState::Pending
}

pub open spec fn consistent_task_state_edge_internal_admissible(_now: nat, a: AState, b: AState) -> bool {
    all_task_pairs(a, b, true, |t: ATask, u: ATask| task_edge_internal_admissible(t.state, u.state))
}

pub open spec fn consistent_promise_state_edge_internal_admissible(_now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        match b.promise_of(id) {
            None => true,
            Some(q) => {
                let p = a.objects[id];
                p.state == q.state
                    || (p.state == PromiseState::Pending
                        && (q.state == PromiseState::RejectedTimedout
                            || (q.state == PromiseState::Resolved && p.is_timer())))
            },
        }
}

// ---------------------------------------------------------------------------
// The catalogue, folded
// ---------------------------------------------------------------------------

/// Every `.state` entry stated on the abstract state.
pub open spec fn inv(now: nat, s: AState) -> bool {
    &&& s.keyed()
    &&& well_formed_promise_created_at_lte_timeout_at(now, s)
    &&& well_formed_promise_pending_created_before_deadline(now, s)
    &&& well_formed_promise_settled_at_lte_timeout_at(now, s)
    &&& well_formed_promise_created_at_lte_settled_at(now, s)
    &&& well_formed_promise_settled_at_iff_not_pending(now, s)
    &&& well_formed_promise_pending_has_no_value(now, s)
    &&& well_formed_promise_deadline_verdict_matches_timer_tag(now, s)
    &&& well_formed_promise_deadline_settlement_has_no_value(now, s)
    &&& well_formed_promise_timer_not_targeted(now, s)
    &&& well_formed_promise_timedout_is_server_owned(now, s)
    &&& well_formed_promise_callbacks_unique(now, s)
    &&& well_formed_promise_listeners_unique(now, s)
    &&& well_formed_promise_obligations_require_external(now, s)
    &&& well_formed_promise_awaiter_is_not_self(now, s)
    &&& well_formed_promise_callbacks_same_origin(now, s)
    &&& well_formed_promise_created_at_lte_now(now, s)
    &&& well_formed_promise_settled_at_lte_now(now, s)
    &&& well_formed_task_acquired_iff_has_pid(now, s)
    &&& well_formed_task_acquired_iff_has_ttl(now, s)
    &&& well_formed_task_acquired_iff_has_lease_timeout_at(now, s)
    &&& well_formed_task_pending_iff_has_retry_timeout_at(now, s)
    &&& well_formed_task_fulfilled_is_cleared(now, s)
    &&& well_formed_task_suspended_is_cleared(now, s)
    &&& well_formed_task_halted_is_cleared(now, s)
    &&& well_formed_task_suspended_has_no_resumes(now, s)
    &&& well_formed_task_resumes_unique(now, s)
    &&& well_formed_task_acquired_version_positive(now, s)
    &&& well_formed_schedule_promise_tags_not_timer_targeted(now, s)
    &&& well_formed_schedule_created_at_lte_next_run_at(now, s)
    &&& well_formed_schedule_created_at_lte_last_run_at(now, s)
    &&& well_formed_schedule_last_run_at_lt_next_run_at(now, s)
    &&& consistent_task_iff_kind_task(now, s)
    &&& consistent_settled_promise_has_fulfilled_task(now, s)
    &&& consistent_callback_awaiter_is_targeted(now, s)
    &&& consistent_outbox_execute_names_existing_task(now, s)
    &&& consistent_outbox_never_ahead(now, s)
    &&& consistent_outbox_execute_address_is_target_tag(now, s)
    &&& consistent_outbox_unblock_names_settled_promise(now, s)
    &&& consistent_settled_task_promise_settled(now, s)
    &&& consistent_suspended_task_holds_rung(now, s)
}

/// The three `.state` entries stated on the rows.
pub open spec fn inv_rows(now: nat, s: crate::store::State) -> bool {
    &&& well_formed_store_object_ids_unique(now, s)
    &&& well_formed_store_schedule_ids_unique(now, s)
    &&& well_formed_store_outbox_keys_unique(now, s)
}

/// Every `.trans` entry stated on the abstract states.
pub open spec fn legal(now: nat, a: AState, b: AState) -> bool {
    &&& preserved_promise_birth_fields_immutable(now, a, b)
    &&& preserved_settled_promise_record(now, a, b)
    &&& monotone_promise_set_grows(now, a, b)
    &&& monotone_task_set_grows(now, a, b)
    &&& monotone_task_version_increases_only_on_acquisition(now, a, b)
    &&& preserved_fulfilled_task(now, a, b)
    &&& preserved_promise_state_frozen_once_settled(now, a, b)
    &&& preserved_promise_settlement_is_one_way(now, a, b)
    &&& consistent_promise_settled_at_moves_with_state(now, a, b)
    &&& preserved_promise_value_until_settlement(now, a, b)
    &&& monotone_promise_callbacks_grow_while_pending(now, a, b)
    &&& monotone_promise_callbacks_shrink_once_settled(now, a, b)
    &&& monotone_promise_listeners_grow_while_pending(now, a, b)
    &&& monotone_promise_listeners_shrink_once_settled(now, a, b)
    &&& consistent_promise_state_edge_admissible(now, a, b)
    &&& consistent_task_state_edge_admissible(now, a, b)
    &&& preserved_task_acquisition_only_from_pending(now, a, b)
    &&& preserved_task_suspension_only_from_acquired(now, a, b)
    &&& preserved_task_halted_only_reenters_via_pending(now, a, b)
    &&& consistent_settlement_fulfils_task(now, a, b)
    &&& consistent_task_fulfilment_needs_settlement(now, a, b)
    &&& consistent_obligation_discharge_requires_settled(now, a, b)
    &&& consistent_callback_consumption_resumes_awaiter(now, a, b)
    &&& consistent_listener_consumption_enqueues_unblock(now, a, b)
    &&& consistent_wake_follows_callback_consumption(now, a, b)
    &&& consistent_suspension_registers_callback(now, a, b)
    &&& consistent_task_birth_couples_promise_birth(now, a, b)
    &&& monotone_outbox_keys_never_disappear(now, a, b)
    &&& consistent_new_execute_matches_task_and_target(now, a, b)
    &&& consistent_new_unblock_carries_stored_record(now, a, b)
    &&& consistent_new_unblock_discharges_its_listener(now, a, b)
    &&& preserved_schedule_birth_fields_immutable(now, a, b)
    &&& consistent_task_birth_state(now, a, b)
    &&& consistent_task_lease_released_atomically(now, a, b)
    &&& preserved_task_lease_holder_stable(now, a, b)
    &&& consistent_task_lease_fields_move_together(now, a, b)
    &&& monotone_task_resumes_grow_or_clear(now, a, b)
    &&& consistent_task_resumes_cleared_only_on_dispatch_or_park(now, a, b)
    &&& preserved_no_dead_dispatch(now, a, b)
    &&& preserved_execute_only_for_live_task(now, a, b)
    &&& consistent_promise_settlement_stamp(now, a, b)
    &&& preserved_timedout_is_server_owned(now, a, b)
    &&& consistent_new_promise_born_clean(now, a, b)
    &&& consistent_task_acquisition_is_atomic(now, a, b)
    &&& consistent_task_lease_deadline_is_now_plus_ttl(now, a, b)
    &&& consistent_task_pending_entry_arms_retry(now, a, b)
    &&& consistent_task_retry_rearm_only_when_due(now, a, b)
    &&& monotone_task_retry_rearm_advances(now, a, b)
    &&& consistent_task_wake_records_resume(now, a, b)
}

/// The `.trans` entry stated on the rows.
pub open spec fn legal_rows(now: nat, a: crate::store::State, b: crate::store::State) -> bool {
    preserved_promise_no_duplicate_ids(now, a, b)
}

/// The two sweeper entries.
pub open spec fn internal_legal(now: nat, a: AState, b: AState) -> bool {
    &&& consistent_task_state_edge_internal_admissible(now, a, b)
    &&& consistent_promise_state_edge_internal_admissible(now, a, b)
}

} // verus!
