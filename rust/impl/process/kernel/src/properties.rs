//! The conformance catalogue, transcribed.
//!
//! `resonatehq/resonate`, `spec/02-abstract/properties.lean`, entry for
//! entry, same names. A `.state` entry is a predicate on `(now, s)`; a
//! `.trans` entry on `(now, a, b)` with `b` reached from `a` in one step.
//! Lean quantifies over lists of objects; here the state is the fold of the
//! rows, a map by id, and `all` over a list is `forall` over the map's keys.
//! Every entry is written as that `forall` over a body `…_at`, stated at one
//! id (or one outbox key), so that a proof can work one object at a time.
//! The three `well_formed_store_*_unique` entries are the row-level
//! well-formedness `State::wf`, which is what makes the fold a bijection.
//!
//! `inv` collects the `.state` entries, `legal` the `.trans` entries, and
//! `internal_legal` the two sweeper entries that hold of internal steps only.
//! `inv_obj`, `inv_out`, `inv_sched` and `trans_obj`, `trans_out`,
//! `trans_sched` are the same entries folded the other way: everything the
//! catalogue says about one id. The pointwise lemmas at the end tie the two.

use vstd::prelude::*;

use crate::store::*;
use crate::tags::OType;
use crate::types::*;

verus! {

// ---------------------------------------------------------------------------
// Reading the state
// ---------------------------------------------------------------------------

#[cfg(verus_keep_ghost)]
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

pub open spec fn opt_or_zero(o: Option<u64>) -> nat {
    match o { Some(x) => x as nat, None => 0 }
}

pub open spec fn deadline_verdict(p: APromise) -> PromiseState {
    if p.is_timer() { PromiseState::Resolved } else { PromiseState::RejectedTimedout }
}

pub open spec fn target_or_empty(p: APromise) -> Seq<char> {
    crate::tags::target_of(p.tags)
}

pub open spec fn some_callbacks_contain(s: AState, awaiter: Seq<char>) -> bool {
    exists|id: Seq<char>| #[trigger] s.objects.contains_key(id) && s.objects[id].callbacks.contains(awaiter)
}

pub open spec fn has_execute(s: AState, id: Seq<char>, v: u64, address: Seq<char>) -> bool {
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

// ===========================================================================
// .state — one object
// ===========================================================================

pub open spec fn well_formed_promise_created_at_lte_timeout_at_at(_now: nat, p: APromise) -> bool {
    p.created_at <= p.timeout_at
}
pub open spec fn well_formed_promise_created_at_lte_timeout_at(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_created_at_lte_timeout_at_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_pending_created_before_deadline_at(_now: nat, p: APromise) -> bool {
    p.state != PromiseState::Pending || p.created_at < p.timeout_at
}
pub open spec fn well_formed_promise_pending_created_before_deadline(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_pending_created_before_deadline_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_settled_at_lte_timeout_at_at(_now: nat, p: APromise) -> bool {
    match p.settled_at { None => true, Some(x) => x <= p.timeout_at }
}
pub open spec fn well_formed_promise_settled_at_lte_timeout_at(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_settled_at_lte_timeout_at_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_created_at_lte_settled_at_at(_now: nat, p: APromise) -> bool {
    match p.settled_at { None => true, Some(x) => p.created_at <= x }
}
pub open spec fn well_formed_promise_created_at_lte_settled_at(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_created_at_lte_settled_at_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_settled_at_iff_not_pending_at(_now: nat, p: APromise) -> bool {
    (p.state != PromiseState::Pending) == (p.settled_at is Some)
}
pub open spec fn well_formed_promise_settled_at_iff_not_pending(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_settled_at_iff_not_pending_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_pending_has_no_value_at(_now: nat, p: APromise) -> bool {
    p.state != PromiseState::Pending || p.value.is_empty()
}
pub open spec fn well_formed_promise_pending_has_no_value(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_pending_has_no_value_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_deadline_verdict_matches_timer_tag_at(_now: nat, p: APromise) -> bool {
    p.settled_at != Some(p.timeout_at) || p.state == deadline_verdict(p)
}
pub open spec fn well_formed_promise_deadline_verdict_matches_timer_tag(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_deadline_verdict_matches_timer_tag_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_deadline_settlement_has_no_value_at(_now: nat, p: APromise) -> bool {
    p.settled_at != Some(p.timeout_at) || p.value.is_empty()
}
pub open spec fn well_formed_promise_deadline_settlement_has_no_value(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_deadline_settlement_has_no_value_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_timer_not_targeted_at(_now: nat, p: APromise) -> bool {
    !crate::tags::timer_targeted(p.tags)
}
pub open spec fn well_formed_promise_timer_not_targeted(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_timer_not_targeted_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_timedout_is_server_owned_at(_now: nat, p: APromise) -> bool {
    p.state != PromiseState::RejectedTimedout || p.settled_at == Some(p.timeout_at)
}
pub open spec fn well_formed_promise_timedout_is_server_owned(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_timedout_is_server_owned_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_callbacks_unique_at(_now: nat, p: APromise) -> bool {
    no_dups(p.callbacks)
}
pub open spec fn well_formed_promise_callbacks_unique(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_callbacks_unique_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_listeners_unique_at(_now: nat, p: APromise) -> bool {
    no_dups(p.listeners)
}
pub open spec fn well_formed_promise_listeners_unique(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_listeners_unique_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_obligations_require_external_at(_now: nat, p: APromise) -> bool {
    (p.callbacks.len() == 0 && p.listeners.len() == 0) || p.otype().awaitable()
}
pub open spec fn well_formed_promise_obligations_require_external(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_obligations_require_external_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_awaiter_is_not_self_at(_now: nat, p: APromise) -> bool {
    !p.callbacks.contains(p.id)
}
pub open spec fn well_formed_promise_awaiter_is_not_self(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_awaiter_is_not_self_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_callbacks_same_origin_at(_now: nat, p: APromise) -> bool {
    forall|i: int| 0 <= i < p.callbacks.len() ==> crate::types::same_origin_spec(#[trigger] p.callbacks[i], p.id)
}
pub open spec fn well_formed_promise_callbacks_same_origin(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_callbacks_same_origin_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_created_at_lte_now_at(now: nat, p: APromise) -> bool {
    p.created_at <= now
}
pub open spec fn well_formed_promise_created_at_lte_now(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_created_at_lte_now_at(now, s.objects[id])
}

pub open spec fn well_formed_promise_settled_at_lte_now_at(now: nat, p: APromise) -> bool {
    match p.settled_at { None => true, Some(x) => x <= now }
}
pub open spec fn well_formed_promise_settled_at_lte_now(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_promise_settled_at_lte_now_at(now, s.objects[id])
}

/// `s.tasks.all f`, at one object: its task where it has one.
pub open spec fn task_at(p: APromise, f: spec_fn(ATask) -> bool) -> bool {
    match p.task { Some(t) => f(t), None => true }
}

pub open spec fn well_formed_task_acquired_iff_has_pid_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| (t.state == TaskState::Acquired) == (t.pid is Some))
}
pub open spec fn well_formed_task_acquired_iff_has_pid(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_acquired_iff_has_pid_at(now, s.objects[id])
}

pub open spec fn well_formed_task_acquired_iff_has_ttl_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| (t.state == TaskState::Acquired) == (t.ttl is Some))
}
pub open spec fn well_formed_task_acquired_iff_has_ttl(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_acquired_iff_has_ttl_at(now, s.objects[id])
}

pub open spec fn well_formed_task_acquired_iff_has_lease_timeout_at_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| (t.state == TaskState::Acquired) == (t.lease_timeout_at is Some))
}
pub open spec fn well_formed_task_acquired_iff_has_lease_timeout_at(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_acquired_iff_has_lease_timeout_at_at(now, s.objects[id])
}

pub open spec fn well_formed_task_pending_iff_has_retry_timeout_at_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| (t.state == TaskState::Pending) == (t.retry_timeout_at is Some))
}
pub open spec fn well_formed_task_pending_iff_has_retry_timeout_at(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_pending_iff_has_retry_timeout_at_at(now, s.objects[id])
}

pub open spec fn well_formed_task_fulfilled_is_cleared_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| t.state != TaskState::Fulfilled || (task_cleared(t) && t.resumes.len() == 0))
}
pub open spec fn well_formed_task_fulfilled_is_cleared(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_fulfilled_is_cleared_at(now, s.objects[id])
}

pub open spec fn well_formed_task_suspended_is_cleared_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| t.state != TaskState::Suspended || task_cleared(t))
}
pub open spec fn well_formed_task_suspended_is_cleared(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_suspended_is_cleared_at(now, s.objects[id])
}

pub open spec fn well_formed_task_halted_is_cleared_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| t.state != TaskState::Halted || task_cleared(t))
}
pub open spec fn well_formed_task_halted_is_cleared(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_halted_is_cleared_at(now, s.objects[id])
}

pub open spec fn well_formed_task_suspended_has_no_resumes_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| t.state != TaskState::Suspended || t.resumes.len() == 0)
}
pub open spec fn well_formed_task_suspended_has_no_resumes(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_suspended_has_no_resumes_at(now, s.objects[id])
}

pub open spec fn well_formed_task_resumes_unique_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| no_dups(t.resumes))
}
pub open spec fn well_formed_task_resumes_unique(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_resumes_unique_at(now, s.objects[id])
}

pub open spec fn well_formed_task_acquired_version_positive_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| t.state != TaskState::Acquired || 1 <= t.version)
}
pub open spec fn well_formed_task_acquired_version_positive(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        well_formed_task_acquired_version_positive_at(now, s.objects[id])
}

// --- schedules ---

pub open spec fn well_formed_schedule_promise_tags_not_timer_targeted_at(_now: nat, c: ASchedule) -> bool {
    !crate::tags::timer_targeted(c.promise_tags)
}
pub open spec fn well_formed_schedule_promise_tags_not_timer_targeted(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==>
        well_formed_schedule_promise_tags_not_timer_targeted_at(now, s.schedules[id])
}

pub open spec fn well_formed_schedule_created_at_lte_next_run_at_at(_now: nat, c: ASchedule) -> bool {
    c.created_at <= c.next_run_at
}
pub open spec fn well_formed_schedule_created_at_lte_next_run_at(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==>
        well_formed_schedule_created_at_lte_next_run_at_at(now, s.schedules[id])
}

pub open spec fn well_formed_schedule_created_at_lte_last_run_at_at(_now: nat, c: ASchedule) -> bool {
    match c.last_run_at { None => true, Some(l) => c.created_at <= l }
}
pub open spec fn well_formed_schedule_created_at_lte_last_run_at(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==>
        well_formed_schedule_created_at_lte_last_run_at_at(now, s.schedules[id])
}

pub open spec fn well_formed_schedule_last_run_at_lt_next_run_at_at(_now: nat, c: ASchedule) -> bool {
    match c.last_run_at { None => true, Some(l) => l < c.next_run_at }
}
pub open spec fn well_formed_schedule_last_run_at_lt_next_run_at(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==>
        well_formed_schedule_last_run_at_lt_next_run_at_at(now, s.schedules[id])
}

// --- the three uniqueness entries, stated on the rows, where ids can collide ---

pub open spec fn well_formed_store_object_ids_unique(_now: nat, s: crate::store::State) -> bool {
    crate::store::distinct_by(s.objects@, crate::store::obj_key())
}

pub open spec fn well_formed_store_schedule_ids_unique(_now: nat, s: crate::store::State) -> bool {
    crate::store::distinct_by(s.schedules@, crate::store::sched_key())
}

pub open spec fn well_formed_store_outbox_keys_unique(_now: nat, s: crate::store::State) -> bool {
    crate::store::distinct_by(s.outbox@, crate::store::out_key())
}

// ===========================================================================
// .state — several objects
// ===========================================================================

pub open spec fn consistent_task_iff_kind_task_at(_now: nat, p: APromise) -> bool {
    (p.task is Some) == (p.otype() == OType::Runnable)
}
pub open spec fn consistent_task_iff_kind_task(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        consistent_task_iff_kind_task_at(now, s.objects[id])
}

pub open spec fn consistent_settled_promise_has_fulfilled_task_at(_now: nat, p: APromise) -> bool {
    p.state == PromiseState::Pending || task_at(p, |t: ATask| t.state == TaskState::Fulfilled)
}
pub open spec fn consistent_settled_promise_has_fulfilled_task(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        consistent_settled_promise_has_fulfilled_task_at(now, s.objects[id])
}

pub open spec fn consistent_callback_awaiter_is_targeted_at(_now: nat, s: AState, p: APromise) -> bool {
    forall|i: int| 0 <= i < p.callbacks.len() ==>
        s.objects.contains_key(#[trigger] p.callbacks[i]) && s.objects[p.callbacks[i]].otype() == OType::Runnable
}
pub open spec fn consistent_callback_awaiter_is_targeted(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        consistent_callback_awaiter_is_targeted_at(now, s, s.objects[id])
}

pub open spec fn consistent_suspended_task_holds_rung_at(now: nat, s: AState, id: Seq<char>) -> bool {
    task_at(s.objects[id], |t: ATask| t.state != TaskState::Suspended
        || s.objects[id].project_promise(now).state != PromiseState::Pending
        || some_callbacks_contain(s, id))
}
pub open spec fn consistent_suspended_task_holds_rung(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        consistent_suspended_task_holds_rung_at(now, s, id)
}

pub open spec fn consistent_settled_task_promise_settled_at(_now: nat, p: APromise) -> bool {
    task_at(p, |t: ATask| t.state != TaskState::Fulfilled || p.state != PromiseState::Pending)
}
pub open spec fn consistent_settled_task_promise_settled(now: nat, s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==>
        consistent_settled_task_promise_settled_at(now, s.objects[id])
}

// --- the outbox ---

pub open spec fn consistent_outbox_execute_names_existing_task_at(_now: nat, s: AState, e: AOutboxEntry) -> bool {
    match e.message {
        AMessage::Execute { task_id, .. } => s.has_task(task_id),
        AMessage::Unblock(_) => true,
    }
}
pub open spec fn consistent_outbox_execute_names_existing_task(now: nat, s: AState) -> bool {
    forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) ==>
        consistent_outbox_execute_names_existing_task_at(now, s, s.outbox[k])
}

pub open spec fn consistent_outbox_never_ahead_at(_now: nat, s: AState, e: AOutboxEntry) -> bool {
    match e.message {
        AMessage::Execute { task_id, version } =>
            match s.task_of(task_id) { Some(t) => version <= t.version, None => true },
        AMessage::Unblock(_) => true,
    }
}
pub open spec fn consistent_outbox_never_ahead(now: nat, s: AState) -> bool {
    forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) ==>
        consistent_outbox_never_ahead_at(now, s, s.outbox[k])
}

pub open spec fn consistent_outbox_execute_address_is_target_tag_at(_now: nat, s: AState, e: AOutboxEntry) -> bool {
    match e.message {
        AMessage::Execute { task_id, .. } =>
            match s.promise_of(task_id) { Some(p) => e.address == target_or_empty(p), None => true },
        AMessage::Unblock(_) => true,
    }
}
pub open spec fn consistent_outbox_execute_address_is_target_tag(now: nat, s: AState) -> bool {
    forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) ==>
        consistent_outbox_execute_address_is_target_tag_at(now, s, s.outbox[k])
}

pub open spec fn consistent_outbox_unblock_names_settled_promise_at(_now: nat, s: AState, e: AOutboxEntry) -> bool {
    match e.message {
        AMessage::Unblock(r) =>
            r.state != PromiseState::Pending
            && s.objects.contains_key(r.id) && s.objects[r.id].state != PromiseState::Pending,
        AMessage::Execute { .. } => true,
    }
}
pub open spec fn consistent_outbox_unblock_names_settled_promise(now: nat, s: AState) -> bool {
    forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) ==>
        consistent_outbox_unblock_names_settled_promise_at(now, s, s.outbox[k])
}

// ===========================================================================
// .trans — bodies at one id. `p` is the object in `a`, `q` the one in `b`.
// ===========================================================================

// --- entries quantified over `a` ---

pub open spec fn preserved_promise_birth_fields_immutable_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    match b.promise_of(id) {
        None => true,
        Some(q) => q.param.data == p.param.data && q.param.headers == p.param.headers
            && q.tags == p.tags && q.timeout_at == p.timeout_at && q.created_at == p.created_at,
    }
}
pub open spec fn preserved_promise_birth_fields_immutable(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        preserved_promise_birth_fields_immutable_at(now, b, id, a.objects[id])
}

pub open spec fn preserved_settled_promise_record_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    p.state == PromiseState::Pending
        || match b.promise_of(id) {
            None => false,
            Some(q) => q.state == p.state && q.settled_at == p.settled_at
                && q.value.data == p.value.data && q.value.headers == p.value.headers,
        }
}
pub open spec fn preserved_settled_promise_record(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        preserved_settled_promise_record_at(now, b, id, a.objects[id])
}

pub open spec fn monotone_promise_set_grows_at(_now: nat, b: AState, id: Seq<char>, _p: APromise) -> bool {
    b.objects.contains_key(id)
}
pub open spec fn monotone_promise_set_grows(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        monotone_promise_set_grows_at(now, b, id, a.objects[id])
}

pub open spec fn monotone_task_set_grows_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    p.task is None || b.has_task(id)
}
pub open spec fn monotone_task_set_grows(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        monotone_task_set_grows_at(now, b, id, a.objects[id])
}

/// `o.task.all fun t => match b.task? o.id with | none => none_case | some u => f t u`.
pub open spec fn task_pair_at(b: AState, id: Seq<char>, p: APromise, none_case: bool, f: spec_fn(ATask, ATask) -> bool) -> bool {
    match p.task {
        None => true,
        Some(t) => match b.task_of(id) { None => none_case, Some(u) => f(t, u) },
    }
}

/// Lean's `TaskObject.lapsed`: an acquired task whose lease has ended by
/// `now`. A read shows it pending, so one request may take it over: the
/// stored row goes from acquired to acquired, one version up, in one step.
pub open spec fn lapsed(t: ATask, now: nat) -> bool {
    t.state == TaskState::Acquired && match t.lease_timeout_at { Some(d) => d <= now, None => false }
}

pub open spec fn monotone_task_version_increases_only_on_acquisition_at(now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask|
        if t.state == TaskState::Pending && u.state == TaskState::Acquired {
            u.version == t.version + 1
        } else if lapsed(t, now) && u.state == TaskState::Acquired {
            u.version == t.version || u.version == t.version + 1
        } else {
            u.version == t.version
        })
}
pub open spec fn monotone_task_version_increases_only_on_acquisition(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        monotone_task_version_increases_only_on_acquisition_at(now, b, id, a.objects[id])
}

pub open spec fn preserved_fulfilled_task_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, false, |t: ATask, u: ATask|
        t.state != TaskState::Fulfilled
            || (u.state == TaskState::Fulfilled && u.version == t.version && u.resumes.len() == 0 && task_cleared(u)))
}
pub open spec fn preserved_fulfilled_task(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        preserved_fulfilled_task_at(now, b, id, a.objects[id])
}

pub open spec fn preserved_promise_state_frozen_once_settled_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    p.state == PromiseState::Pending
        || match b.promise_of(id) { None => false, Some(q) => q.state == p.state }
}
pub open spec fn preserved_promise_state_frozen_once_settled(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        preserved_promise_state_frozen_once_settled_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_promise_settled_at_moves_with_state_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    match b.promise_of(id) {
        None => false,
        Some(q) => (q.settled_at != p.settled_at) == (q.state != p.state),
    }
}
pub open spec fn consistent_promise_settled_at_moves_with_state(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_promise_settled_at_moves_with_state_at(now, b, id, a.objects[id])
}

pub open spec fn preserved_promise_value_until_settlement_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    match b.promise_of(id) {
        None => false,
        Some(q) => q.state != PromiseState::Pending
            || (q.value.data == p.value.data && q.value.headers == p.value.headers),
    }
}
pub open spec fn preserved_promise_value_until_settlement(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        preserved_promise_value_until_settlement_at(now, b, id, a.objects[id])
}

pub open spec fn preserved_promise_no_duplicate_ids(_now: nat, _a: crate::store::State, b: crate::store::State) -> bool {
    crate::store::distinct_by(b.objects@, crate::store::obj_key())
}

pub open spec fn consistent_promise_state_edge_admissible_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    match b.promise_of(id) { None => true, Some(q) => p.state == q.state || p.state == PromiseState::Pending }
}
pub open spec fn consistent_promise_state_edge_admissible(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_promise_state_edge_admissible_at(now, b, id, a.objects[id])
}

pub open spec fn task_edge_admissible(t: TaskState, u: TaskState) -> bool {
    ||| t == u
    ||| t == TaskState::Pending && (u == TaskState::Acquired || u == TaskState::Halted || u == TaskState::Fulfilled)
    ||| t == TaskState::Acquired && (u == TaskState::Pending || u == TaskState::Suspended
            || u == TaskState::Halted || u == TaskState::Fulfilled)
    ||| t == TaskState::Suspended && (u == TaskState::Pending || u == TaskState::Halted || u == TaskState::Fulfilled)
    ||| t == TaskState::Halted && (u == TaskState::Pending || u == TaskState::Fulfilled)
}
pub open spec fn consistent_task_state_edge_admissible_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask| task_edge_admissible(t.state, u.state))
}
pub open spec fn consistent_task_state_edge_admissible(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_task_state_edge_admissible_at(now, b, id, a.objects[id])
}

pub open spec fn preserved_task_halted_only_reenters_via_pending_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, false, |t: ATask, u: ATask|
        t.state != TaskState::Halted
            || u.state == TaskState::Halted || u.state == TaskState::Pending || u.state == TaskState::Fulfilled)
}
pub open spec fn preserved_task_halted_only_reenters_via_pending(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        preserved_task_halted_only_reenters_via_pending_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_settlement_fulfils_task_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    p.state != PromiseState::Pending
        || match (b.promise_of(id), b.task_of(id)) {
            (Some(q), Some(u)) => q.state == PromiseState::Pending || u.state == TaskState::Fulfilled,
            _ => true,
        }
}
pub open spec fn consistent_settlement_fulfils_task(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_settlement_fulfils_task_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_obligation_discharge_requires_settled_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    match b.promise_of(id) {
        None => true,
        Some(q) => (subset_of(p.callbacks, q.callbacks) && subset_of(p.listeners, q.listeners))
            || q.state != PromiseState::Pending,
    }
}
pub open spec fn consistent_obligation_discharge_requires_settled(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_obligation_discharge_requires_settled_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_callback_consumption_resumes_awaiter_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    forall|i: int| 0 <= i < p.callbacks.len() ==> {
        let x = #[trigger] p.callbacks[i];
        (match b.promise_of(id) { None => true, Some(q) => q.callbacks.contains(x) })
        || match b.task_of(x) {
            None => true,
            Some(u) => u.state == TaskState::Fulfilled || u.resumes.contains(id),
        }
    }
}
pub open spec fn consistent_callback_consumption_resumes_awaiter(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_callback_consumption_resumes_awaiter_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_listener_consumption_enqueues_unblock_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    forall|i: int| 0 <= i < p.listeners.len() ==> {
        let addr = #[trigger] p.listeners[i];
        (match b.promise_of(id) { None => true, Some(q) => q.listeners.contains(addr) })
        || one_unblock(b, id, addr)
    }
}
pub open spec fn consistent_listener_consumption_enqueues_unblock(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_listener_consumption_enqueues_unblock_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_task_lease_released_atomically_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask|
        !(t.state == TaskState::Acquired && u.state != TaskState::Acquired)
            || (u.pid is None && u.ttl is None && u.lease_timeout_at is None && u.version == t.version))
}
pub open spec fn consistent_task_lease_released_atomically(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_task_lease_released_atomically_at(now, b, id, a.objects[id])
}

pub open spec fn preserved_task_lease_holder_stable_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask|
        !(t.state == TaskState::Acquired && u.state == TaskState::Acquired && u.version == t.version)
            || (u.pid == t.pid && u.ttl == t.ttl))
}
pub open spec fn preserved_task_lease_holder_stable(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        preserved_task_lease_holder_stable_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_task_lease_fields_move_together_at(now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask| {
        ||| (u.pid == t.pid && u.ttl == t.ttl && u.lease_timeout_at == t.lease_timeout_at)
        ||| (t.state != TaskState::Acquired && u.state == TaskState::Acquired
                && u.pid is Some && u.ttl is Some && u.lease_timeout_at is Some)
        ||| (t.state == TaskState::Acquired && u.state != TaskState::Acquired
                && u.pid is None && u.ttl is None && u.lease_timeout_at is None)
        ||| (t.state == TaskState::Acquired && u.state == TaskState::Acquired && u.pid == t.pid && u.ttl == t.ttl)
        ||| (lapsed(t, now) && u.state == TaskState::Acquired && u.version == t.version + 1
                && u.pid is Some && u.ttl is Some && u.lease_timeout_at is Some)
    })
}
pub open spec fn consistent_task_lease_fields_move_together(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_task_lease_fields_move_together_at(now, b, id, a.objects[id])
}

pub open spec fn monotone_task_resumes_grow_or_clear_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask| u.resumes.len() == 0 || subset_of(t.resumes, u.resumes))
}
pub open spec fn monotone_task_resumes_grow_or_clear(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        monotone_task_resumes_grow_or_clear_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_task_resumes_cleared_only_on_dispatch_or_park_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask|
        !(t.resumes.len() != 0 && u.resumes.len() == 0)
            || u.state == TaskState::Acquired || u.state == TaskState::Suspended || u.state == TaskState::Fulfilled)
}
pub open spec fn consistent_task_resumes_cleared_only_on_dispatch_or_park(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_task_resumes_cleared_only_on_dispatch_or_park_at(now, b, id, a.objects[id])
}

pub open spec fn granted(now: nat, u: ATask) -> bool {
    u.pid is Some && u.ttl is Some
        && u.lease_timeout_at == Some((now + opt_or_zero(u.ttl)) as u64)
        && u.retry_timeout_at is None && u.resumes.len() == 0
}

pub open spec fn consistent_task_acquisition_is_atomic_at(now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask|
        (!(t.state != TaskState::Acquired && u.state == TaskState::Acquired)
            || (t.state == TaskState::Pending && t.version < u.version && granted(now, u)))
        // a lapsed lease taken over in one step: the same grant, from the lapsed row
        && (!(lapsed(t, now) && u.state == TaskState::Acquired && u.version != t.version)
            || (u.version == t.version + 1 && granted(now, u))))
}
pub open spec fn consistent_task_acquisition_is_atomic(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_task_acquisition_is_atomic_at(now, b, id, a.objects[id])
}

/// A task that comes to be pending is due for an offer at once: at `now` for
/// a release or a continue; at the lease's end, already passed, for a lease
/// that lapsed (or already offered by the same step and armed ahead); at the
/// awaited promise's settlement, already passed, for a resume.
pub open spec fn consistent_task_pending_entry_arms_retry_at(now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask|
        !(t.state != TaskState::Pending && u.state == TaskState::Pending)
            || match u.retry_timeout_at {
                Some(r) => {
                    ||| r == now
                    ||| (lapsed(t, now) && (t.lease_timeout_at == Some(r) || now < r))
                    ||| (t.state == TaskState::Suspended && r <= now)
                },
                None => false,
            })
}
pub open spec fn consistent_task_pending_entry_arms_retry(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_task_pending_entry_arms_retry_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_task_retry_rearm_only_when_due_at(now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask|
        !(t.state == TaskState::Pending && u.state == TaskState::Pending && u.retry_timeout_at != t.retry_timeout_at)
            || match t.retry_timeout_at { Some(due) => due <= now, None => false })
}
pub open spec fn consistent_task_retry_rearm_only_when_due(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_task_retry_rearm_only_when_due_at(now, b, id, a.objects[id])
}

pub open spec fn monotone_task_retry_rearm_advances_at(now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask|
        t.state != TaskState::Pending
            || u.state != TaskState::Pending || u.retry_timeout_at == t.retry_timeout_at
            || match u.retry_timeout_at { Some(d) => now < d, None => false })
}
pub open spec fn monotone_task_retry_rearm_advances(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        monotone_task_retry_rearm_advances_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_task_wake_records_resume_at(now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask|
        !(t.state == TaskState::Suspended && u.state == TaskState::Pending)
            || (u.resumes.len() != 0 && u.version == t.version
                && match u.retry_timeout_at { Some(r) => r <= now, None => false }))
}
pub open spec fn consistent_task_wake_records_resume(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_task_wake_records_resume_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_promise_settlement_stamp_at(now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    p.state != PromiseState::Pending
        || match b.promise_of(id) {
            None => false,
            Some(q) => {
                ||| q.state == PromiseState::Pending
                ||| (q.settled_at == Some(now as u64) && now < q.timeout_at && q.state != PromiseState::RejectedTimedout)
                ||| (q.settled_at == Some(q.timeout_at) && q.timeout_at <= now
                        && q.state == deadline_verdict(q)
                        && q.value.data == p.value.data && q.value.headers == p.value.headers)
            },
        }
}
pub open spec fn consistent_promise_settlement_stamp(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_promise_settlement_stamp_at(now, b, id, a.objects[id])
}

pub open spec fn preserved_timedout_is_server_owned_at(now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    p.state != PromiseState::Pending
        || match b.promise_of(id) {
            None => true,
            Some(q) => q.state != PromiseState::RejectedTimedout
                || (p.timeout_at <= now && q.settled_at == Some(p.timeout_at)),
        }
}
pub open spec fn preserved_timedout_is_server_owned(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        preserved_timedout_is_server_owned_at(now, b, id, a.objects[id])
}

// --- entries quantified over `b` ---

pub open spec fn preserved_no_dead_dispatch_at(now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    task_at(q, |u: ATask| u.state != TaskState::Pending
        || (match a.task_of(id) { Some(t) => t.state == TaskState::Pending, None => q.state == PromiseState::Pending })
        || q.project_promise(now).state == PromiseState::Pending)
}
pub open spec fn preserved_no_dead_dispatch(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        preserved_no_dead_dispatch_at(now, a, id, b.objects[id])
}

pub open spec fn preserved_promise_settlement_is_one_way_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    q.state != PromiseState::Pending
        || match a.promise_of(id) { Some(p) => p.state == PromiseState::Pending, None => true }
}
pub open spec fn preserved_promise_settlement_is_one_way(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        preserved_promise_settlement_is_one_way_at(now, a, id, b.objects[id])
}

pub open spec fn monotone_promise_callbacks_grow_while_pending_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    q.state != PromiseState::Pending
        || match a.promise_of(id) {
            None => q.callbacks.len() == 0,
            Some(p) => subset_of(p.callbacks, q.callbacks),
        }
}
pub open spec fn monotone_promise_callbacks_grow_while_pending(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        monotone_promise_callbacks_grow_while_pending_at(now, a, id, b.objects[id])
}

pub open spec fn monotone_promise_callbacks_shrink_once_settled_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    q.state == PromiseState::Pending
        || match a.promise_of(id) {
            None => q.callbacks.len() == 0,
            Some(p) => subset_of(q.callbacks, p.callbacks),
        }
}
pub open spec fn monotone_promise_callbacks_shrink_once_settled(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        monotone_promise_callbacks_shrink_once_settled_at(now, a, id, b.objects[id])
}

pub open spec fn monotone_promise_listeners_grow_while_pending_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    q.state != PromiseState::Pending
        || match a.promise_of(id) {
            None => q.listeners.len() == 0,
            Some(p) => subset_of(p.listeners, q.listeners),
        }
}
pub open spec fn monotone_promise_listeners_grow_while_pending(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        monotone_promise_listeners_grow_while_pending_at(now, a, id, b.objects[id])
}

pub open spec fn monotone_promise_listeners_shrink_once_settled_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    q.state == PromiseState::Pending
        || match a.promise_of(id) {
            None => q.listeners.len() == 0,
            Some(p) => subset_of(q.listeners, p.listeners),
        }
}
pub open spec fn monotone_promise_listeners_shrink_once_settled(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        monotone_promise_listeners_shrink_once_settled_at(now, a, id, b.objects[id])
}

pub open spec fn preserved_task_acquisition_only_from_pending_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    task_at(q, |u: ATask| u.state != TaskState::Acquired
        || match a.task_of(id) {
            Some(t) => t.state == TaskState::Pending || t.state == TaskState::Acquired,
            None => true,
        })
}
pub open spec fn preserved_task_acquisition_only_from_pending(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        preserved_task_acquisition_only_from_pending_at(now, a, id, b.objects[id])
}

pub open spec fn preserved_task_suspension_only_from_acquired_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    task_at(q, |u: ATask| u.state != TaskState::Suspended
        || match a.task_of(id) {
            Some(t) => t.state == TaskState::Acquired || t.state == TaskState::Suspended,
            None => false,
        })
}
pub open spec fn preserved_task_suspension_only_from_acquired(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        preserved_task_suspension_only_from_acquired_at(now, a, id, b.objects[id])
}

pub open spec fn consistent_task_fulfilment_needs_settlement_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    task_at(q, |u: ATask| u.state != TaskState::Fulfilled
        || match a.task_of(id) {
            None => true,
            Some(t) => t.state == TaskState::Fulfilled
                || match a.promise_of(id) {
                    Some(p) => p.state == PromiseState::Pending && q.state != PromiseState::Pending,
                    None => false,
                },
        })
}
pub open spec fn consistent_task_fulfilment_needs_settlement(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        consistent_task_fulfilment_needs_settlement_at(now, a, id, b.objects[id])
}

pub open spec fn consistent_wake_follows_callback_consumption_at(_now: nat, a: AState, b: AState, id: Seq<char>, q: APromise) -> bool {
    task_at(q, |u: ATask| match a.task_of(id) {
        None => true,
        Some(t) => !(t.state == TaskState::Suspended && u.state == TaskState::Pending)
            || exists|pid: Seq<char>| #[trigger] a.objects.contains_key(pid)
                && a.objects[pid].callbacks.contains(id)
                && (match b.promise_of(pid) { None => false, Some(w) => !w.callbacks.contains(id) })
                && u.resumes.contains(pid),
    })
}
pub open spec fn consistent_wake_follows_callback_consumption(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        consistent_wake_follows_callback_consumption_at(now, a, b, id, b.objects[id])
}

/// The entry as `properties.lean` states it. It is FALSE of the abstract
/// machine, so it is not in `legal`; the amended entry below is. Witness, in
/// the machine's own steps: a task `X` suspends on `P1` and `P2`; `P1`
/// settles and the callback drain consumes `P1`'s callback and wakes `X`;
/// `X` is acquired again and suspends on `P2` alone. `P2` already carried
/// `X` (the drain removed `X` from `P1` only), so `addCallback` is a no-op
/// and no promise gains a callback it did not have — yet `X` suspended
/// legitimately. The sweep did not reach it: the trace is seven steps long.
pub open spec fn consistent_suspension_registers_callback_lean_at(_now: nat, a: AState, b: AState, id: Seq<char>, q: APromise) -> bool {
    task_at(q, |u: ATask| u.state != TaskState::Suspended
        || (match a.task_of(id) { None => false, Some(t) => t.state == TaskState::Suspended })
        || exists|qid: Seq<char>| #[trigger] b.objects.contains_key(qid)
            && b.objects[qid].callbacks.contains(id)
            && (match a.promise_of(qid) { None => true, Some(p) => !p.callbacks.contains(id) })
            && b.objects[qid].state == PromiseState::Pending)
}

/// Amended: a task that became suspended in this step holds a callback on a
/// pending promise in `b`. (The original also demanded the callback be new.)
pub open spec fn consistent_suspension_registers_callback_at(_now: nat, a: AState, b: AState, id: Seq<char>, q: APromise) -> bool {
    task_at(q, |u: ATask| u.state != TaskState::Suspended
        || (match a.task_of(id) { None => false, Some(t) => t.state == TaskState::Suspended })
        || exists|qid: Seq<char>| #[trigger] b.objects.contains_key(qid)
            && b.objects[qid].callbacks.contains(id)
            && b.objects[qid].state == PromiseState::Pending)
}
pub open spec fn consistent_suspension_registers_callback(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        consistent_suspension_registers_callback_at(now, a, b, id, b.objects[id])
}

pub open spec fn consistent_task_birth_couples_promise_birth_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    &&& task_at(q, |u: ATask| a.has_task(id)
        || (!a.objects.contains_key(id)
            && q.otype() == OType::Runnable
            && (if u.state == TaskState::Fulfilled {
                    q.state != PromiseState::Pending
                } else {
                    q.state == PromiseState::Pending
                })
            && ((u.state == TaskState::Pending && u.version == 0)
                || (u.state == TaskState::Acquired && 1 <= u.version)
                || (u.state == TaskState::Fulfilled && u.version == 0))))
    &&& (a.objects.contains_key(id) || q.otype() != OType::Runnable || q.task is Some)
}
pub open spec fn consistent_task_birth_couples_promise_birth(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        consistent_task_birth_couples_promise_birth_at(now, a, id, b.objects[id])
}

pub open spec fn consistent_task_birth_state_at(_now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    task_at(q, |u: ATask| a.has_task(id)
        || (u.state == TaskState::Pending && u.retry_timeout_at is Some
            && u.pid is None && u.ttl is None && u.lease_timeout_at is None && u.resumes.len() == 0)
        || (u.state == TaskState::Fulfilled && task_cleared(u) && u.resumes.len() == 0)
        || (u.state == TaskState::Acquired && 1 <= u.version && u.retry_timeout_at is None
            && u.pid is Some && u.ttl is Some && u.lease_timeout_at is Some && u.resumes.len() == 0))
}
pub open spec fn consistent_task_birth_state(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        consistent_task_birth_state_at(now, a, id, b.objects[id])
}

pub open spec fn consistent_task_lease_deadline_is_now_plus_ttl_at(now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    task_at(q, |u: ATask| match u.lease_timeout_at {
        None => true,
        Some(d) => d == now + opt_or_zero(u.ttl)
            || match a.task_of(id) {
                Some(t) => t.lease_timeout_at == Some(d) && t.ttl == u.ttl && t.state == u.state,
                None => false,
            },
    })
}
pub open spec fn consistent_task_lease_deadline_is_now_plus_ttl(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        consistent_task_lease_deadline_is_now_plus_ttl_at(now, a, id, b.objects[id])
}

pub open spec fn consistent_new_promise_born_clean_at(now: nat, a: AState, id: Seq<char>, q: APromise) -> bool {
    a.objects.contains_key(id)
        || (q.callbacks.len() == 0 && q.listeners.len() == 0 && q.value.is_empty()
            && q.created_at <= now
            && ((q.state == PromiseState::Pending && q.settled_at is None && q.created_at < q.timeout_at)
                || (q.settled_at == Some(q.timeout_at) && q.created_at == q.timeout_at
                    && q.timeout_at <= now && q.state == deadline_verdict(q))))
}
pub open spec fn consistent_new_promise_born_clean(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==>
        consistent_new_promise_born_clean_at(now, a, id, b.objects[id])
}

// --- the outbox ---

pub open spec fn monotone_outbox_keys_never_disappear(_now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] a.outbox.contains_key(k) ==> b.outbox.contains_key(k)
}

pub open spec fn preserved_execute_only_for_live_task_at(now: nat, a: AState, b: AState, e: AOutboxEntry) -> bool {
    match e.message {
        AMessage::Unblock(_) => true,
        AMessage::Execute { task_id, version } =>
            has_execute(a, task_id, version, e.address)
            || match b.promise_of(task_id) {
                Some(p) => p.project_promise(now).state == PromiseState::Pending,
                None => true,
            },
    }
}
pub open spec fn preserved_execute_only_for_live_task(now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) ==>
        preserved_execute_only_for_live_task_at(now, a, b, b.outbox[k])
}

pub open spec fn consistent_new_execute_matches_task_and_target_at(_now: nat, a: AState, b: AState, e: AOutboxEntry) -> bool {
    match e.message {
        AMessage::Unblock(_) => true,
        AMessage::Execute { task_id, version } =>
            has_execute(a, task_id, version, e.address)
            || ((match b.task_of(task_id) { Some(t) => t.version == version, None => false })
                && (match b.promise_of(task_id) { Some(p) => e.address == target_or_empty(p), None => false })),
    }
}
pub open spec fn consistent_new_execute_matches_task_and_target(now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) ==>
        consistent_new_execute_matches_task_and_target_at(now, a, b, b.outbox[k])
}

pub open spec fn consistent_new_unblock_carries_stored_record_at(_now: nat, a: AState, b: AState, e: AOutboxEntry) -> bool {
    match e.message {
        AMessage::Execute { .. } => true,
        AMessage::Unblock(r) =>
            has_unblock(a, r.id, e.address)
            || (r.state != PromiseState::Pending
                && match b.promise_of(r.id) {
                    Some(p) => p.state == r.state && p.settled_at == r.settled_at
                        && p.value.data == r.value.data && p.timeout_at == r.timeout_at
                        && p.created_at == r.created_at,
                    None => false,
                }),
    }
}
pub open spec fn consistent_new_unblock_carries_stored_record(now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) ==>
        consistent_new_unblock_carries_stored_record_at(now, a, b, b.outbox[k])
}

pub open spec fn consistent_new_unblock_discharges_its_listener_at(_now: nat, a: AState, b: AState, e: AOutboxEntry) -> bool {
    match e.message {
        AMessage::Execute { .. } => true,
        AMessage::Unblock(r) =>
            has_unblock(a, r.id, e.address)
            || (a.objects.contains_key(r.id) && a.objects[r.id].listeners.contains(e.address)
                && (b.objects.contains_key(r.id) ==> !b.objects[r.id].listeners.contains(e.address))),
    }
}
pub open spec fn consistent_new_unblock_discharges_its_listener(now: nat, a: AState, b: AState) -> bool {
    forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) ==>
        consistent_new_unblock_discharges_its_listener_at(now, a, b, b.outbox[k])
}

// --- schedules ---

pub open spec fn preserved_schedule_birth_fields_immutable_at(_now: nat, b: AState, id: Seq<char>, c: ASchedule) -> bool {
    !b.schedules.contains_key(id) || {
        let d = b.schedules[id];
        d.cron == c.cron && d.promise_id == c.promise_id && d.promise_timeout == c.promise_timeout
            && d.promise_param.data == c.promise_param.data
            && d.promise_param.headers == c.promise_param.headers
            && d.promise_tags == c.promise_tags && d.created_at == c.created_at
    }
}
pub open spec fn preserved_schedule_birth_fields_immutable(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.schedules.contains_key(id) ==>
        preserved_schedule_birth_fields_immutable_at(now, b, id, a.schedules[id])
}

// ===========================================================================
// The sweeper entries: internal steps only
// ===========================================================================

pub open spec fn task_edge_internal_admissible(t: TaskState, u: TaskState) -> bool {
    ||| t == u
    ||| u == TaskState::Fulfilled
    ||| t == TaskState::Acquired && u == TaskState::Pending
    ||| t == TaskState::Suspended && u == TaskState::Pending
}
pub open spec fn consistent_task_state_edge_internal_admissible_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    task_pair_at(b, id, p, true, |t: ATask, u: ATask| task_edge_internal_admissible(t.state, u.state))
}
pub open spec fn consistent_task_state_edge_internal_admissible(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_task_state_edge_internal_admissible_at(now, b, id, a.objects[id])
}

pub open spec fn consistent_promise_state_edge_internal_admissible_at(_now: nat, b: AState, id: Seq<char>, p: APromise) -> bool {
    match b.promise_of(id) {
        None => true,
        Some(q) => p.state == q.state
            || (p.state == PromiseState::Pending
                && (q.state == PromiseState::RejectedTimedout
                    || (q.state == PromiseState::Resolved && p.is_timer()))),
    }
}
pub open spec fn consistent_promise_state_edge_internal_admissible(now: nat, a: AState, b: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==>
        consistent_promise_state_edge_internal_admissible_at(now, b, id, a.objects[id])
}


// ===========================================================================
// Kernel bounds — not catalogue entries
// ===========================================================================

/// What the kernel adds to the catalogue so that its `u64` arithmetic never
/// overflows: every duration and version it stores is at most `MAX_TIME`.
/// Versions grow by one per acquisition, so this is a bound no run reaches;
/// `task.create` and `task.acquire` refuse to cross it.
pub open spec fn kernel_bounds_at(p: APromise) -> bool {
    &&& p.timeout_at <= 2 * (MAX_TIME as nat)
    &&& task_at(p, |t: ATask| t.version <= MAX_TIME as nat && opt_or_zero(t.ttl) <= MAX_TIME as nat)
}

pub open spec fn kernel_bounds(s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==> kernel_bounds_at(s.objects[id])
}

pub open spec fn kernel_sched_bounds_at(c: ASchedule) -> bool {
    c.promise_timeout <= MAX_TIME as nat
}

pub open spec fn kernel_sched_bounds(s: AState) -> bool {
    forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==> kernel_sched_bounds_at(s.schedules[id])
}

// ===========================================================================
// The catalogue, folded by entry
// ===========================================================================

/// Every `.state` entry stated on the abstract state.
#[verifier::opaque]
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
    &&& kernel_bounds(s)
    &&& kernel_sched_bounds(s)
}

/// The three `.state` entries stated on the rows.
pub open spec fn inv_rows(now: nat, s: crate::store::State) -> bool {
    &&& well_formed_store_object_ids_unique(now, s)
    &&& well_formed_store_schedule_ids_unique(now, s)
    &&& well_formed_store_outbox_keys_unique(now, s)
}

/// Every `.trans` entry stated on the abstract states.
#[verifier::opaque]
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
#[verifier::opaque]
pub open spec fn internal_legal(now: nat, a: AState, b: AState) -> bool {
    &&& consistent_task_state_edge_internal_admissible(now, a, b)
    &&& consistent_promise_state_edge_internal_admissible(now, a, b)
}

// ===========================================================================
// The catalogue, folded by id
// ===========================================================================

/// Every `.state` entry about one object, `p = s.objects[id]`.
pub open spec fn inv_obj(now: nat, s: AState, id: Seq<char>) -> bool {
    let p = s.objects[id];
    &&& p.id == id
    &&& well_formed_promise_created_at_lte_timeout_at_at(now, p)
    &&& well_formed_promise_pending_created_before_deadline_at(now, p)
    &&& well_formed_promise_settled_at_lte_timeout_at_at(now, p)
    &&& well_formed_promise_created_at_lte_settled_at_at(now, p)
    &&& well_formed_promise_settled_at_iff_not_pending_at(now, p)
    &&& well_formed_promise_pending_has_no_value_at(now, p)
    &&& well_formed_promise_deadline_verdict_matches_timer_tag_at(now, p)
    &&& well_formed_promise_deadline_settlement_has_no_value_at(now, p)
    &&& well_formed_promise_timer_not_targeted_at(now, p)
    &&& well_formed_promise_timedout_is_server_owned_at(now, p)
    &&& well_formed_promise_callbacks_unique_at(now, p)
    &&& well_formed_promise_listeners_unique_at(now, p)
    &&& well_formed_promise_obligations_require_external_at(now, p)
    &&& well_formed_promise_awaiter_is_not_self_at(now, p)
    &&& well_formed_promise_callbacks_same_origin_at(now, p)
    &&& well_formed_promise_created_at_lte_now_at(now, p)
    &&& well_formed_promise_settled_at_lte_now_at(now, p)
    &&& well_formed_task_acquired_iff_has_pid_at(now, p)
    &&& well_formed_task_acquired_iff_has_ttl_at(now, p)
    &&& well_formed_task_acquired_iff_has_lease_timeout_at_at(now, p)
    &&& well_formed_task_pending_iff_has_retry_timeout_at_at(now, p)
    &&& well_formed_task_fulfilled_is_cleared_at(now, p)
    &&& well_formed_task_suspended_is_cleared_at(now, p)
    &&& well_formed_task_halted_is_cleared_at(now, p)
    &&& well_formed_task_suspended_has_no_resumes_at(now, p)
    &&& well_formed_task_resumes_unique_at(now, p)
    &&& well_formed_task_acquired_version_positive_at(now, p)
    &&& consistent_task_iff_kind_task_at(now, p)
    &&& consistent_settled_promise_has_fulfilled_task_at(now, p)
    &&& consistent_callback_awaiter_is_targeted_at(now, s, p)
    &&& consistent_settled_task_promise_settled_at(now, p)
    &&& consistent_suspended_task_holds_rung_at(now, s, id)
    &&& kernel_bounds_at(p)
}

/// Every `.state` entry about one outbox entry.
pub open spec fn inv_out(now: nat, s: AState, k: OutboxKey) -> bool {
    let e = s.outbox[k];
    &&& e.key() == k
    &&& consistent_outbox_execute_names_existing_task_at(now, s, e)
    &&& consistent_outbox_never_ahead_at(now, s, e)
    &&& consistent_outbox_execute_address_is_target_tag_at(now, s, e)
    &&& consistent_outbox_unblock_names_settled_promise_at(now, s, e)
}

/// Every `.state` entry about one schedule.
pub open spec fn inv_sched(now: nat, s: AState, id: Seq<char>) -> bool {
    let c = s.schedules[id];
    &&& c.id == id
    &&& well_formed_schedule_promise_tags_not_timer_targeted_at(now, c)
    &&& well_formed_schedule_created_at_lte_next_run_at_at(now, c)
    &&& well_formed_schedule_created_at_lte_last_run_at_at(now, c)
    &&& well_formed_schedule_last_run_at_lt_next_run_at_at(now, c)
    &&& kernel_sched_bounds_at(c)
}

/// Every `.trans` entry about one id.
pub open spec fn trans_obj(now: nat, a: AState, b: AState, id: Seq<char>) -> bool {
    &&& a.objects.contains_key(id) ==> {
        let p = a.objects[id];
        &&& preserved_promise_birth_fields_immutable_at(now, b, id, p)
        &&& preserved_settled_promise_record_at(now, b, id, p)
        &&& monotone_promise_set_grows_at(now, b, id, p)
        &&& monotone_task_set_grows_at(now, b, id, p)
        &&& monotone_task_version_increases_only_on_acquisition_at(now, b, id, p)
        &&& preserved_fulfilled_task_at(now, b, id, p)
        &&& preserved_promise_state_frozen_once_settled_at(now, b, id, p)
        &&& consistent_promise_settled_at_moves_with_state_at(now, b, id, p)
        &&& preserved_promise_value_until_settlement_at(now, b, id, p)
        &&& consistent_promise_state_edge_admissible_at(now, b, id, p)
        &&& consistent_task_state_edge_admissible_at(now, b, id, p)
        &&& preserved_task_halted_only_reenters_via_pending_at(now, b, id, p)
        &&& consistent_settlement_fulfils_task_at(now, b, id, p)
        &&& consistent_obligation_discharge_requires_settled_at(now, b, id, p)
        &&& consistent_callback_consumption_resumes_awaiter_at(now, b, id, p)
        &&& consistent_listener_consumption_enqueues_unblock_at(now, b, id, p)
        &&& consistent_task_lease_released_atomically_at(now, b, id, p)
        &&& preserved_task_lease_holder_stable_at(now, b, id, p)
        &&& consistent_task_lease_fields_move_together_at(now, b, id, p)
        &&& monotone_task_resumes_grow_or_clear_at(now, b, id, p)
        &&& consistent_task_resumes_cleared_only_on_dispatch_or_park_at(now, b, id, p)
        &&& consistent_task_acquisition_is_atomic_at(now, b, id, p)
        &&& consistent_task_pending_entry_arms_retry_at(now, b, id, p)
        &&& consistent_task_retry_rearm_only_when_due_at(now, b, id, p)
        &&& monotone_task_retry_rearm_advances_at(now, b, id, p)
        &&& consistent_task_wake_records_resume_at(now, b, id, p)
        &&& consistent_promise_settlement_stamp_at(now, b, id, p)
        &&& preserved_timedout_is_server_owned_at(now, b, id, p)
    }
    &&& b.objects.contains_key(id) ==> {
        let q = b.objects[id];
        &&& preserved_no_dead_dispatch_at(now, a, id, q)
        &&& preserved_promise_settlement_is_one_way_at(now, a, id, q)
        &&& monotone_promise_callbacks_grow_while_pending_at(now, a, id, q)
        &&& monotone_promise_callbacks_shrink_once_settled_at(now, a, id, q)
        &&& monotone_promise_listeners_grow_while_pending_at(now, a, id, q)
        &&& monotone_promise_listeners_shrink_once_settled_at(now, a, id, q)
        &&& preserved_task_acquisition_only_from_pending_at(now, a, id, q)
        &&& preserved_task_suspension_only_from_acquired_at(now, a, id, q)
        &&& consistent_task_fulfilment_needs_settlement_at(now, a, id, q)
        &&& consistent_wake_follows_callback_consumption_at(now, a, b, id, q)
        &&& consistent_suspension_registers_callback_at(now, a, b, id, q)
        &&& consistent_task_birth_couples_promise_birth_at(now, a, id, q)
        &&& consistent_task_birth_state_at(now, a, id, q)
        &&& consistent_task_lease_deadline_is_now_plus_ttl_at(now, a, id, q)
        &&& consistent_new_promise_born_clean_at(now, a, id, q)
    }
}

/// Every `.trans` entry about one outbox key.
pub open spec fn trans_out(now: nat, a: AState, b: AState, k: OutboxKey) -> bool {
    &&& a.outbox.contains_key(k) ==> b.outbox.contains_key(k)
    &&& b.outbox.contains_key(k) ==> {
        let e = b.outbox[k];
        &&& preserved_execute_only_for_live_task_at(now, a, b, e)
        &&& consistent_new_execute_matches_task_and_target_at(now, a, b, e)
        &&& consistent_new_unblock_carries_stored_record_at(now, a, b, e)
        &&& consistent_new_unblock_discharges_its_listener_at(now, a, b, e)
    }
}

/// Every `.trans` entry about one schedule id.
pub open spec fn trans_sched(now: nat, a: AState, b: AState, id: Seq<char>) -> bool {
    a.schedules.contains_key(id) ==> preserved_schedule_birth_fields_immutable_at(now, b, id, a.schedules[id])
}

/// The two sweeper entries about one id.
pub open spec fn internal_obj(now: nat, a: AState, b: AState, id: Seq<char>) -> bool {
    a.objects.contains_key(id) ==> {
        &&& consistent_task_state_edge_internal_admissible_at(now, b, id, a.objects[id])
        &&& consistent_promise_state_edge_internal_admissible_at(now, b, id, a.objects[id])
    }
}

} // verus!
