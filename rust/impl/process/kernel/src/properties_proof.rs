//! The catalogue's own theorems. First the frame, the theorem every step
//! ends with: a step that proves the entries at the ids it touched, and
//! touched nothing else, satisfies the whole catalogue. Then its pieces,
//! then the folds between the catalogue stated entry by entry and stated
//! id by id, and the frames an untouched id gets for free. Nothing here
//! is executed.
//!
//! A step changes a few objects, a few outbox entries, a few schedules. For
//! each one it touched it proves the catalogue's entries at that id, locally.
//! [`lemma_step`] does the rest: an untouched id satisfies every entry
//! because nothing about it moved, and the cross-object entries at an
//! untouched id survive because the touched ids obey the `.trans` entries.
//! Its conclusion is the whole catalogue, `inv` and `legal`.

use vstd::prelude::*;

use crate::properties::*;
use crate::store::*;
use crate::tags::OType;
use crate::types::*;

verus! {

/// What a step may do, stated per id, and what follows.
///
/// Each set is a predicate on ids.
/// - `changed`: the object ids the step wrote. Elsewhere `b` agrees with `a`.
/// - `lost`: the ids whose callbacks the step may have consumed, a subset of
///   `changed`. Every other registered callback survives into `b`.
/// - `new_out`: the outbox keys the step wrote. Elsewhere `b` agrees with `a`.
/// - `sched`: the schedule ids the step wrote. Elsewhere `b` agrees with `a`.
pub proof fn lemma_step(
    now: nat, a: AState, b: AState,
    changed: spec_fn(Seq<char>) -> bool, lost: spec_fn(Seq<char>) -> bool,
    new_out: spec_fn(OutboxKey) -> bool, sched: spec_fn(Seq<char>) -> bool,
)
    requires
        inv(now, a),
        // objects
        forall|x: Seq<char>| !changed(x) ==>
            (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
            && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]),
        forall|x: Seq<char>| #[trigger] changed(x) && b.objects.contains_key(x) ==> inv_obj(now, b, x),
        forall|x: Seq<char>| #[trigger] changed(x) ==> trans_obj(now, a, b, x),
        forall|z: Seq<char>| #[trigger] lost(z) ==> changed(z),
        forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
            && #[trigger] a.objects[w].callbacks.contains(z) && !lost(z)
            ==> b.objects.contains_key(w) && b.objects[w].callbacks.contains(z),
        // outbox
        forall|k: OutboxKey| !new_out(k) ==>
            (a.outbox.contains_key(k) <==> #[trigger] b.outbox.contains_key(k))
            && (a.outbox.contains_key(k) ==> a.outbox[k] == b.outbox[k]),
        forall|k: OutboxKey| #[trigger] new_out(k) && b.outbox.contains_key(k) ==> inv_out(now, b, k),
        forall|k: OutboxKey| #[trigger] new_out(k) ==> trans_out(now, a, b, k),
        // schedules
        forall|x: Seq<char>| !sched(x) ==>
            (a.schedules.contains_key(x) <==> #[trigger] b.schedules.contains_key(x))
            && (a.schedules.contains_key(x) ==> a.schedules[x] == b.schedules[x]),
        forall|x: Seq<char>| #[trigger] sched(x) && b.schedules.contains_key(x) ==> inv_sched(now, b, x),
        forall|x: Seq<char>| #[trigger] sched(x) ==> trans_sched(now, a, b, x),
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);

    // Every id obeys the .trans entries.
    assert forall|x: Seq<char>| #[trigger] trans_obj(now, a, b, x) by {
        if !changed(x) {
            assert(a.objects.contains_key(x) <==> b.objects.contains_key(x));
            lemma_trans_obj_unchanged(now, a, b, x);
        }
    }
    assert forall|k: OutboxKey| #[trigger] trans_out(now, a, b, k) by {
        if !new_out(k) {
            assert(a.outbox.contains_key(k) <==> b.outbox.contains_key(k));
            lemma_trans_out_frame(now, a, b, k);
        }
    }
    assert forall|x: Seq<char>| #[trigger] trans_sched(now, a, b, x) by {
        if !sched(x) {
            assert(a.schedules.contains_key(x) <==> b.schedules.contains_key(x));
            lemma_trans_sched_unchanged(now, a, b, x);
        }
    }
    lemma_legal_pointwise(now, a, b);

    // Every id obeys the .state entries.
    assert forall|x: Seq<char>| #[trigger] b.objects.contains_key(x) implies inv_obj(now, b, x) by {
        if !changed(x) {
            assert(a.objects.contains_key(x));
            lemma_inv_obj_frame(now, a, b, x, lost);
        }
    }
    assert forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) implies inv_out(now, b, k) by {
        if !new_out(k) {
            assert(a.outbox.contains_key(k));
            lemma_inv_out_frame(now, a, b, k);
        }
    }
    assert forall|x: Seq<char>| #[trigger] b.schedules.contains_key(x) implies inv_sched(now, b, x) by {
        if !sched(x) {
            assert(a.schedules.contains_key(x));
            assert(inv_sched(now, a, x));
        }
    }
    lemma_inv_pointwise(now, b);
}

/// A step that changed nothing is legal.
pub proof fn lemma_noop(now: nat, a: AState)
    requires
        inv(now, a),
    ensures
        legal(now, a, a),
{
    lemma_step(now, a, a, |x: Seq<char>| false, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// An outbox entry the step did not touch satisfies its `.trans` entries,
/// even when the step touched other entries.
pub proof fn lemma_trans_out_frame(now: nat, a: AState, b: AState, k: OutboxKey)
    requires
        a.outbox.contains_key(k) <==> b.outbox.contains_key(k),
        a.outbox.contains_key(k) ==> a.outbox[k] == b.outbox[k],
    ensures
        trans_out(now, a, b, k),
{
    if b.outbox.contains_key(k) {
        let e = b.outbox[k];
        match e.message {
            AMessage::Execute { task_id, version } => {
                assert(has_execute(a, task_id, version, e.address)) by {
                    assert(a.outbox.contains_key(k));
                }
            }
            AMessage::Unblock(r) => {
                assert(has_unblock(a, r.id, e.address)) by {
                    assert(a.outbox.contains_key(k));
                }
            }
        }
    }
}

/// An object the step did not touch still obeys the `.state` entries in `b`:
/// its own fields did not move, and the objects it points at obeyed the
/// `.trans` entries.
pub proof fn lemma_inv_obj_frame(now: nat, a: AState, b: AState, x: Seq<char>, lost: spec_fn(Seq<char>) -> bool)
    requires
        inv_obj(now, a, x),
        a.objects.contains_key(x),
        b.objects.contains_key(x),
        a.objects[x] == b.objects[x],
        !lost(x),
        forall|y: Seq<char>| #[trigger] trans_obj(now, a, b, y),
        forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
            && #[trigger] a.objects[w].callbacks.contains(z) && !lost(z)
            ==> b.objects.contains_key(w) && b.objects[w].callbacks.contains(z),
    ensures
        inv_obj(now, b, x),
{
    let p = a.objects[x];
    // callbacks point at runnable objects that are still there, unchanged in kind
    assert forall|i: int| 0 <= i < p.callbacks.len() implies
        b.objects.contains_key(#[trigger] p.callbacks[i]) && b.objects[p.callbacks[i]].otype() == OType::Runnable by {
        let t = p.callbacks[i];
        assert(a.objects.contains_key(t) && a.objects[t].otype() == OType::Runnable);
        assert(trans_obj(now, a, b, t));
        assert(monotone_promise_set_grows_at(now, b, t, a.objects[t]));
        assert(preserved_promise_birth_fields_immutable_at(now, b, t, a.objects[t]));
        assert(b.objects[t].tags == a.objects[t].tags);
    }
    // a suspended task's rung survives
    match p.task {
        Some(t) => {
            if t.state == TaskState::Suspended && p.project_promise(now).state == PromiseState::Pending {
                assert(some_callbacks_contain(a, x));
                let w = choose|w: Seq<char>| #[trigger] a.objects.contains_key(w) && a.objects[w].callbacks.contains(x);
                assert(b.objects.contains_key(w) && b.objects[w].callbacks.contains(x));
                assert(some_callbacks_contain(b, x));
            }
        }
        None => {}
    }
}

/// An unchanged object under a step that keeps every object, its tags and
/// its registered callbacks still obeys the `.state` entries.
pub proof fn lemma_inv_obj_frame_simple(now: nat, a: AState, b: AState, x: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(x),
        b.objects.contains_key(x),
        a.objects[x] == b.objects[x],
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
            && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z),
    ensures
        inv_obj(now, b, x),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, x));
    let p = a.objects[x];
    assert forall|i: int| 0 <= i < p.callbacks.len() implies
        b.objects.contains_key(#[trigger] p.callbacks[i]) && b.objects[p.callbacks[i]].otype() == OType::Runnable by {
        let t = p.callbacks[i];
        assert(a.objects.contains_key(t) && a.objects[t].otype() == OType::Runnable);
        assert(b.objects[t].tags == a.objects[t].tags);
    }
    match p.task {
        Some(t) => {
            if t.state == TaskState::Suspended && p.project_promise(now).state == PromiseState::Pending {
                assert(some_callbacks_contain(a, x));
                let w = choose|w: Seq<char>| #[trigger] a.objects.contains_key(w) && a.objects[w].callbacks.contains(x);
                assert(b.objects.contains_key(w) && b.objects[w].callbacks.contains(x));
                assert(some_callbacks_contain(b, x));
            }
        }
        None => {}
    }
}

/// An outbox entry the step did not touch still obeys the `.state` entries in
/// `b`: the task it names is still there with a version no smaller, the
/// promise it names kept its tags, and a settled promise stayed settled.
pub proof fn lemma_inv_out_frame(now: nat, a: AState, b: AState, k: OutboxKey)
    requires
        inv_out(now, a, k),
        a.outbox.contains_key(k),
        b.outbox.contains_key(k),
        a.outbox[k] == b.outbox[k],
        forall|y: Seq<char>| #[trigger] trans_obj(now, a, b, y),
    ensures
        inv_out(now, b, k),
{
    let e = a.outbox[k];
    match e.message {
        AMessage::Execute { task_id, version } => {
            assert(a.has_task(task_id));
            assert(a.objects.contains_key(task_id));
            let p = a.objects[task_id];
            assert(trans_obj(now, a, b, task_id));
            assert(monotone_promise_set_grows_at(now, b, task_id, p));
            assert(monotone_task_set_grows_at(now, b, task_id, p));
            assert(monotone_task_version_increases_only_on_acquisition_at(now, b, task_id, p));
            assert(preserved_promise_birth_fields_immutable_at(now, b, task_id, p));
            assert(b.objects.contains_key(task_id));
            assert(b.has_task(task_id));
            assert(b.objects[task_id].tags == p.tags);
        }
        AMessage::Unblock(r) => {
            assert(a.objects.contains_key(r.id));
            let p = a.objects[r.id];
            assert(trans_obj(now, a, b, r.id));
            assert(monotone_promise_set_grows_at(now, b, r.id, p));
            assert(preserved_promise_state_frozen_once_settled_at(now, b, r.id, p));
        }
    }
}

// ===========================================================================
// Folding one way and the other
// ===========================================================================

/// The `.state` entries hold iff they hold at every id.
pub proof fn lemma_inv_pointwise(now: nat, s: AState)
    ensures
        inv(now, s) <==> {
            &&& forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) ==> inv_obj(now, s, id)
            &&& forall|k: OutboxKey| #[trigger] s.outbox.contains_key(k) ==> inv_out(now, s, k)
            &&& forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) ==> inv_sched(now, s, id)
        },
{
    reveal(inv);
}

/// The `.trans` entries hold iff they hold at every id and key.
pub proof fn lemma_legal_pointwise(now: nat, a: AState, b: AState)
    ensures
        legal(now, a, b) <==> {
            &&& forall|id: Seq<char>| #[trigger] trans_obj(now, a, b, id)
            &&& forall|k: OutboxKey| #[trigger] trans_out(now, a, b, k)
            &&& forall|id: Seq<char>| #[trigger] trans_sched(now, a, b, id)
        },
{
    reveal(legal);
    if forall|id: Seq<char>| #[trigger] trans_obj(now, a, b, id) {
        assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies
            preserved_promise_birth_fields_immutable_at(now, b, id, a.objects[id])
            && preserved_settled_promise_record_at(now, b, id, a.objects[id])
            && monotone_promise_set_grows_at(now, b, id, a.objects[id])
            && monotone_task_set_grows_at(now, b, id, a.objects[id])
            && monotone_task_version_increases_only_on_acquisition_at(now, b, id, a.objects[id])
            && preserved_fulfilled_task_at(now, b, id, a.objects[id])
            && preserved_promise_state_frozen_once_settled_at(now, b, id, a.objects[id])
            && consistent_promise_settled_at_moves_with_state_at(now, b, id, a.objects[id])
            && preserved_promise_value_until_settlement_at(now, b, id, a.objects[id])
            && consistent_promise_state_edge_admissible_at(now, b, id, a.objects[id])
            && consistent_task_state_edge_admissible_at(now, b, id, a.objects[id])
            && preserved_task_halted_only_reenters_via_pending_at(now, b, id, a.objects[id])
            && consistent_settlement_fulfils_task_at(now, b, id, a.objects[id])
            && consistent_obligation_discharge_requires_settled_at(now, b, id, a.objects[id])
            && consistent_callback_consumption_resumes_awaiter_at(now, b, id, a.objects[id])
            && consistent_listener_consumption_enqueues_unblock_at(now, b, id, a.objects[id])
            && consistent_task_lease_released_atomically_at(now, b, id, a.objects[id])
            && preserved_task_lease_holder_stable_at(now, b, id, a.objects[id])
            && consistent_task_lease_fields_move_together_at(now, b, id, a.objects[id])
            && monotone_task_resumes_grow_or_clear_at(now, b, id, a.objects[id])
            && consistent_task_resumes_cleared_only_on_dispatch_or_park_at(now, b, id, a.objects[id])
            && consistent_task_acquisition_is_atomic_at(now, b, id, a.objects[id])
            && consistent_task_pending_entry_arms_retry_at(now, b, id, a.objects[id])
            && consistent_task_retry_rearm_only_when_due_at(now, b, id, a.objects[id])
            && monotone_task_retry_rearm_advances_at(now, b, id, a.objects[id])
            && consistent_task_wake_records_resume_at(now, b, id, a.objects[id])
            && consistent_promise_settlement_stamp_at(now, b, id, a.objects[id])
            && preserved_timedout_is_server_owned_at(now, b, id, a.objects[id]) by {
            assert(trans_obj(now, a, b, id));
        }
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies
            preserved_no_dead_dispatch_at(now, a, id, b.objects[id])
            && preserved_promise_settlement_is_one_way_at(now, a, id, b.objects[id])
            && monotone_promise_callbacks_grow_while_pending_at(now, a, id, b.objects[id])
            && monotone_promise_callbacks_shrink_once_settled_at(now, a, id, b.objects[id])
            && monotone_promise_listeners_grow_while_pending_at(now, a, id, b.objects[id])
            && monotone_promise_listeners_shrink_once_settled_at(now, a, id, b.objects[id])
            && preserved_task_acquisition_only_from_pending_at(now, a, id, b.objects[id])
            && preserved_task_suspension_only_from_acquired_at(now, a, id, b.objects[id])
            && consistent_task_fulfilment_needs_settlement_at(now, a, id, b.objects[id])
            && consistent_wake_follows_callback_consumption_at(now, a, b, id, b.objects[id])
            && consistent_suspension_registers_callback_at(now, a, b, id, b.objects[id])
            && consistent_task_birth_couples_promise_birth_at(now, a, id, b.objects[id])
            && consistent_task_birth_state_at(now, a, id, b.objects[id])
            && consistent_task_lease_deadline_is_now_plus_ttl_at(now, a, id, b.objects[id])
            && consistent_new_promise_born_clean_at(now, a, id, b.objects[id]) by {
            assert(trans_obj(now, a, b, id));
        }
    }
    if forall|k: OutboxKey| #[trigger] trans_out(now, a, b, k) {
        assert forall|k: OutboxKey| #[trigger] a.outbox.contains_key(k) implies b.outbox.contains_key(k) by {
            assert(trans_out(now, a, b, k));
        }
        assert forall|k: OutboxKey| #[trigger] b.outbox.contains_key(k) implies
            preserved_execute_only_for_live_task_at(now, a, b, b.outbox[k])
            && consistent_new_execute_matches_task_and_target_at(now, a, b, b.outbox[k])
            && consistent_new_unblock_carries_stored_record_at(now, a, b, b.outbox[k])
            && consistent_new_unblock_discharges_its_listener_at(now, a, b, b.outbox[k]) by {
            assert(trans_out(now, a, b, k));
        }
    }
    if forall|id: Seq<char>| #[trigger] trans_sched(now, a, b, id) {
        assert forall|id: Seq<char>| #[trigger] a.schedules.contains_key(id) implies
            preserved_schedule_birth_fields_immutable_at(now, b, id, a.schedules[id]) by {
            assert(trans_sched(now, a, b, id));
        }
    }
}

/// The sweeper entries hold iff they hold at every id.
pub proof fn lemma_internal_pointwise(now: nat, a: AState, b: AState)
    ensures
        internal_legal(now, a, b) <==> forall|id: Seq<char>| #[trigger] internal_obj(now, a, b, id),
{
    reveal(internal_legal);
    if forall|id: Seq<char>| #[trigger] internal_obj(now, a, b, id) {
        assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies
            consistent_task_state_edge_internal_admissible_at(now, b, id, a.objects[id])
            && consistent_promise_state_edge_internal_admissible_at(now, b, id, a.objects[id]) by {
            assert(internal_obj(now, a, b, id));
        }
    }
}

// ===========================================================================
// Frames: what an untouched id satisfies for free
// ===========================================================================

/// An object the step did not touch satisfies every `.trans` entry.
pub proof fn lemma_trans_obj_unchanged(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        a.objects.contains_key(id) ==> inv_obj(now, a, id),
        a.objects.contains_key(id) <==> b.objects.contains_key(id),
        a.objects.contains_key(id) ==> a.objects[id] == b.objects[id],
    ensures
        trans_obj(now, a, b, id),
{
    if a.objects.contains_key(id) {
        let p = a.objects[id];
        assert forall|i: int| 0 <= i < p.callbacks.len() implies p.callbacks.contains(#[trigger] p.callbacks[i]) by {}
        assert forall|i: int| 0 <= i < p.listeners.len() implies p.listeners.contains(#[trigger] p.listeners[i]) by {}
        assert(subset_of(p.callbacks, p.callbacks));
        assert(subset_of(p.listeners, p.listeners));
        match p.task {
            Some(t) => {
                assert forall|i: int| 0 <= i < t.resumes.len() implies t.resumes.contains(#[trigger] t.resumes[i]) by {}
                assert(subset_of(t.resumes, t.resumes));
            }
            None => {}
        }
    }
}

/// An outbox the step did not touch satisfies every `.trans` entry.
pub proof fn lemma_trans_out_unchanged(now: nat, a: AState, b: AState, k: OutboxKey)
    requires
        a.outbox == b.outbox,
    ensures
        trans_out(now, a, b, k),
{
    if b.outbox.contains_key(k) {
        let e = b.outbox[k];
        match e.message {
            AMessage::Execute { task_id, version } => {
                assert(has_execute(a, task_id, version, e.address)) by {
                    assert(a.outbox.contains_key(k));
                }
            }
            AMessage::Unblock(r) => {
                assert(has_unblock(a, r.id, e.address)) by {
                    assert(a.outbox.contains_key(k));
                }
            }
        }
    }
}

/// A schedule the step did not touch satisfies its `.trans` entry.
pub proof fn lemma_trans_sched_unchanged(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        a.schedules.contains_key(id) ==> b.schedules.contains_key(id) && a.schedules[id] == b.schedules[id],
    ensures
        trans_sched(now, a, b, id),
{
}

} // verus!
