//! The sweep, simulated: `executable_single_pass` is a run of Abstract
//! internal actions.
//!
//! The kernel's sweep is five phases over the stored row order: every
//! promise's deadline, every lease, every settled promise's callbacks, then
//! its listeners, then every due retry. Each phase is a fold of a per-object
//! step already simulated in `internal_sim`; the actions of the run are the
//! phases' steps in the kernel's order, with the one wrinkle that a callback
//! on a bare awaiter is two Abstract actions (`callback_actions`).

use vstd::prelude::*;

use echod_abstract::state::AState;
use echod_kernel::external as kext;
use echod_kernel::internal as kint;
use echod_kernel::steps as ksteps;
use echod_kernel::steps::AOwed;
use echod_kernel::store::AState as KState;
use echod_kernel::types as kernel;
use echod_kernel::types::APromise;

use crate::actions::*;
use crate::bridge::*;
use crate::internal_sim::*;
use crate::relation::*;
use crate::*;

verus! {

pub open spec fn canonical_ids(ids: Seq<Chars>) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> canonical(#[trigger] ids[i])
}

/// No promise lists itself as a callback: the kernel's
/// `well_formed_promise_awaiter_is_not_self`, stated on the document.
pub open spec fn not_self(k: KState) -> bool {
    forall|id: Chars| #[trigger] k.objects.contains_key(id) ==> !k.objects[id].callbacks.contains(id)
}

// ---------------------------------------------------------------------------
// Deadlines
// ---------------------------------------------------------------------------

pub open spec fn deadline_actions(ids: Seq<Chars>) -> Seq<AbsInternal>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else {
        deadline_actions(ids.drop_last()).push(AbsInternal::PromiseTimeout(promise_timeout_req(ids.last())))
    }
}

pub proof fn lemma_deadlines_sim(k: KState, a: AState, ids: Seq<Chars>, now: u64, rt: u64)
    requires doc_related(k, a), canonical_ids(ids),
    ensures ({
        let k2 = ksteps::executable_deadlines(k, ids, now as nat);
        &&& doc_related(k2, internal_run(a, deadline_actions(ids), now, rt))
        &&& k2.schedules == k.schedules
        &&& k2.objects.dom() == k.objects.dom()
        &&& forall|id: Chars| #[trigger] k.objects.contains_key(id) ==> k2.objects[id].callbacks == k.objects[id].callbacks
    }),
    decreases ids.len(),
{
    if ids.len() == 0 {
    } else {
        let rest = ids.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies canonical(#[trigger] rest[i]) by { assert(rest[i] == ids[i]); }
        lemma_deadlines_sim(k, a, rest, now, rt);
        let k1 = ksteps::executable_deadlines(k, rest, now as nat);
        let a1 = internal_run(a, deadline_actions(rest), now, rt);
        let id = ids.last();
        lemma_promise_timeout_sim(k1, a1, id, now);
        lemma_internal_run_push(a, deadline_actions(rest), AbsInternal::PromiseTimeout(promise_timeout_req(id)), now, rt);
        let k2 = ksteps::executable_deadlines(k, ids, now as nat);
        assert(k2.objects.dom() =~= k.objects.dom());
    }
}

// ---------------------------------------------------------------------------
// Leases
// ---------------------------------------------------------------------------

pub open spec fn lease_actions(ids: Seq<Chars>) -> Seq<AbsInternal>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else {
        lease_actions(ids.drop_last()).push(AbsInternal::TaskLeaseTimeout(lease_timeout_req(ids.last())))
    }
}

pub proof fn lemma_leases_sim(k: KState, a: AState, ids: Seq<Chars>, now: u64, rt: u64)
    requires doc_related(k, a), canonical_ids(ids),
    ensures ({
        let k2 = ksteps::executable_leases(k, ids, now as nat);
        &&& doc_related(k2, internal_run(a, lease_actions(ids), now, rt))
        &&& k2.schedules == k.schedules
        &&& k2.objects.dom() == k.objects.dom()
        &&& forall|id: Chars| #[trigger] k.objects.contains_key(id) ==> k2.objects[id].callbacks == k.objects[id].callbacks
    }),
    decreases ids.len(),
{
    if ids.len() == 0 {
    } else {
        let rest = ids.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies canonical(#[trigger] rest[i]) by { assert(rest[i] == ids[i]); }
        lemma_leases_sim(k, a, rest, now, rt);
        let k1 = ksteps::executable_leases(k, rest, now as nat);
        let a1 = internal_run(a, lease_actions(rest), now, rt);
        let id = ids.last();
        lemma_lease_timeout_sim(k1, a1, id, now);
        lemma_internal_run_push(a, lease_actions(rest), AbsInternal::TaskLeaseTimeout(lease_timeout_req(id)), now, rt);
        let k2 = ksteps::executable_leases(k, ids, now as nat);
        assert(k2.objects.dom() =~= k.objects.dom());
    }
}

// ---------------------------------------------------------------------------
// Callbacks
// ---------------------------------------------------------------------------

/// What the snapshot guarantees of each owed row: a canonical awaited id, and
/// canonical awaiters other than itself.
pub open spec fn owed_ok(owed: Seq<AOwed>) -> bool {
    forall|i: int| 0 <= i < owed.len() ==> {
        let item = #[trigger] owed[i];
        &&& canonical(item.awaited)
        &&& forall|j: int| 0 <= j < item.callbacks.len() ==> canonical(#[trigger] item.callbacks[j]) && item.callbacks[j] != item.awaited
    }
}

pub proof fn lemma_owed_snapshot_ok(k: KState, a: AState, ids: Seq<Chars>)
    requires doc_related(k, a), canonical_ids(ids), not_self(k),
    ensures owed_ok(ksteps::executable_owed_snapshot(k, ids)),
    decreases ids.len(),
{
    if ids.len() == 0 {
    } else {
        let rest = ids.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies canonical(#[trigger] rest[i]) by { assert(rest[i] == ids[i]); }
        lemma_owed_snapshot_ok(k, a, rest);
        let prior = ksteps::executable_owed_snapshot(k, rest);
        let x = ids.last();
        let out = ksteps::executable_owed_snapshot(k, ids);
        if out.len() > prior.len() {
            assert(k.objects.contains_key(x));
            let p = k.objects[x];
            assert(canonical_promise(p));
            assert forall|i: int| 0 <= i < out.len() implies ({
                let item = #[trigger] out[i];
                &&& canonical(item.awaited)
                &&& forall|j: int| 0 <= j < item.callbacks.len() ==> canonical(#[trigger] item.callbacks[j]) && item.callbacks[j] != item.awaited
            }) by {
                if i < prior.len() {
                    assert(out[i] == prior[i]);
                } else {
                    assert(out[i].awaited == x && out[i].callbacks == p.callbacks);
                    assert forall|j: int| 0 <= j < p.callbacks.len() implies canonical(#[trigger] p.callbacks[j]) && p.callbacks[j] != x by {
                        if p.callbacks[j] == x {
                            assert(p.callbacks.contains(x));
                        }
                    }
                }
            }
        }
    }
}

/// The actions one owed row's callbacks are, in stored order; each
/// callback's actions depend on the kernel state it finds.
pub open spec fn callbacks_actions(k: KState, x: Chars, cbs: Seq<Chars>, now: u64) -> Seq<AbsInternal>
    decreases cbs.len(),
{
    if cbs.len() == 0 {
        Seq::empty()
    } else {
        let before = ksteps::executable_callbacks(k, x, cbs.drop_last(), now as nat);
        callbacks_actions(k, x, cbs.drop_last(), now) + callback_actions(before, x, cbs.last(), now)
    }
}

pub proof fn lemma_callbacks_sim(k: KState, a: AState, x: Chars, cbs: Seq<Chars>, now: u64, rt: u64)
    requires
        doc_related(k, a),
        canonical(x),
        forall|j: int| 0 <= j < cbs.len() ==> canonical(#[trigger] cbs[j]) && cbs[j] != x,
    ensures doc_related(
        ksteps::executable_callbacks(k, x, cbs, now as nat),
        internal_run(a, callbacks_actions(k, x, cbs, now), now, rt)),
    decreases cbs.len(),
{
    if cbs.len() == 0 {
    } else {
        let rest = cbs.drop_last();
        assert forall|j: int| 0 <= j < rest.len() implies canonical(#[trigger] rest[j]) && rest[j] != x by { assert(rest[j] == cbs[j]); }
        lemma_callbacks_sim(k, a, x, rest, now, rt);
        let k1 = ksteps::executable_callbacks(k, x, rest, now as nat);
        let acts = callbacks_actions(k, x, rest, now);
        let a1 = internal_run(a, acts, now, rt);
        let y = cbs.last();
        lemma_callback_sim(k1, a1, x, y, now, rt);
        lemma_internal_run_app(a, acts, callback_actions(k1, x, y, now), now, rt);
    }
}

pub open spec fn owed_callbacks_actions(k: KState, owed: Seq<AOwed>, now: u64) -> Seq<AbsInternal>
    decreases owed.len(),
{
    if owed.len() == 0 {
        Seq::empty()
    } else {
        let before = ksteps::executable_owed_callbacks(k, owed.drop_last(), now as nat);
        let item = owed.last();
        owed_callbacks_actions(k, owed.drop_last(), now) + callbacks_actions(before, item.awaited, item.callbacks, now)
    }
}

pub proof fn lemma_owed_callbacks_sim(k: KState, a: AState, owed: Seq<AOwed>, now: u64, rt: u64)
    requires doc_related(k, a), owed_ok(owed),
    ensures doc_related(
        ksteps::executable_owed_callbacks(k, owed, now as nat),
        internal_run(a, owed_callbacks_actions(k, owed, now), now, rt)),
    decreases owed.len(),
{
    if owed.len() == 0 {
    } else {
        let rest = owed.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies ({
            let item = #[trigger] rest[i];
            &&& canonical(item.awaited)
            &&& forall|j: int| 0 <= j < item.callbacks.len() ==> canonical(#[trigger] item.callbacks[j]) && item.callbacks[j] != item.awaited
        }) by { assert(rest[i] == owed[i]); }
        lemma_owed_callbacks_sim(k, a, rest, now, rt);
        let k1 = ksteps::executable_owed_callbacks(k, rest, now as nat);
        let acts = owed_callbacks_actions(k, rest, now);
        let a1 = internal_run(a, acts, now, rt);
        let item = owed.last();
        assert(item == owed[owed.len() - 1]);
        lemma_callbacks_sim(k1, a1, item.awaited, item.callbacks, now, rt);
        lemma_internal_run_app(a, acts, callbacks_actions(k1, item.awaited, item.callbacks, now), now, rt);
    }
}

// ---------------------------------------------------------------------------
// Listeners
// ---------------------------------------------------------------------------

pub open spec fn listeners_actions(x: Chars, ls: Seq<Chars>) -> Seq<AbsInternal>
    decreases ls.len(),
{
    if ls.len() == 0 {
        Seq::empty()
    } else {
        listeners_actions(x, ls.drop_last()).push(AbsInternal::Listener(listener_req(x, ls.last())))
    }
}

pub proof fn lemma_listeners_sim(k: KState, a: AState, x: Chars, ls: Seq<Chars>, now: u64, rt: u64)
    requires doc_related(k, a), canonical(x),
    ensures doc_related(
        ksteps::executable_listeners(k, x, ls, now as nat),
        internal_run(a, listeners_actions(x, ls), now, rt)),
    decreases ls.len(),
{
    if ls.len() == 0 {
    } else {
        let rest = ls.drop_last();
        lemma_listeners_sim(k, a, x, rest, now, rt);
        let k1 = ksteps::executable_listeners(k, x, rest, now as nat);
        let a1 = internal_run(a, listeners_actions(x, rest), now, rt);
        let addr = ls.last();
        lemma_listener_sim(k1, a1, x, addr, now);
        lemma_internal_run_push(a, listeners_actions(x, rest), AbsInternal::Listener(listener_req(x, addr)), now, rt);
    }
}

pub open spec fn owed_listeners_actions(owed: Seq<AOwed>) -> Seq<AbsInternal>
    decreases owed.len(),
{
    if owed.len() == 0 {
        Seq::empty()
    } else {
        let item = owed.last();
        owed_listeners_actions(owed.drop_last()) + listeners_actions(item.awaited, item.listeners)
    }
}

pub proof fn lemma_owed_listeners_sim(k: KState, a: AState, owed: Seq<AOwed>, now: u64, rt: u64)
    requires doc_related(k, a), owed_ok(owed),
    ensures doc_related(
        ksteps::executable_owed_listeners(k, owed, now as nat),
        internal_run(a, owed_listeners_actions(owed), now, rt)),
    decreases owed.len(),
{
    if owed.len() == 0 {
    } else {
        let rest = owed.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies ({
            let item = #[trigger] rest[i];
            &&& canonical(item.awaited)
            &&& forall|j: int| 0 <= j < item.callbacks.len() ==> canonical(#[trigger] item.callbacks[j]) && item.callbacks[j] != item.awaited
        }) by { assert(rest[i] == owed[i]); }
        lemma_owed_listeners_sim(k, a, rest, now, rt);
        let k1 = ksteps::executable_owed_listeners(k, rest, now as nat);
        let acts = owed_listeners_actions(rest);
        let a1 = internal_run(a, acts, now, rt);
        let item = owed.last();
        assert(item == owed[owed.len() - 1]);
        lemma_listeners_sim(k1, a1, item.awaited, item.listeners, now, rt);
        lemma_internal_run_app(a, acts, listeners_actions(item.awaited, item.listeners), now, rt);
    }
}

// ---------------------------------------------------------------------------
// Retries
// ---------------------------------------------------------------------------

pub proof fn lemma_due_snapshot_canonical(k: KState, ids: Seq<Chars>, now: u64)
    requires canonical_ids(ids),
    ensures canonical_ids(ksteps::executable_due_snapshot(k, ids, now as nat)),
    decreases ids.len(),
{
    if ids.len() == 0 {
    } else {
        let rest = ids.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies canonical(#[trigger] rest[i]) by { assert(rest[i] == ids[i]); }
        lemma_due_snapshot_canonical(k, rest, now);
        let prior = ksteps::executable_due_snapshot(k, rest, now as nat);
        let out = ksteps::executable_due_snapshot(k, ids, now as nat);
        assert forall|i: int| 0 <= i < out.len() implies canonical(#[trigger] out[i]) by {
            if i < prior.len() {
                assert(out[i] == prior[i]);
            } else {
                assert(out[i] == ids.last());
            }
        }
    }
}

pub open spec fn due_actions(due: Seq<Chars>) -> Seq<AbsInternal>
    decreases due.len(),
{
    if due.len() == 0 {
        Seq::empty()
    } else {
        due_actions(due.drop_last()).push(AbsInternal::TaskRetryTimeout(retry_timeout_req(due.last())))
    }
}

pub proof fn lemma_due_sim(k: KState, a: AState, due: Seq<Chars>, now: u64, rt: u64)
    requires doc_related(k, a), canonical_ids(due), now <= kernel::MAX_TIME, rt <= kernel::MAX_TIME,
    ensures doc_related(
        ksteps::executable_due(k, due, now as nat, rt as nat),
        internal_run(a, due_actions(due), now, rt)),
    decreases due.len(),
{
    if due.len() == 0 {
    } else {
        let rest = due.drop_last();
        assert forall|i: int| 0 <= i < rest.len() implies canonical(#[trigger] rest[i]) by { assert(rest[i] == due[i]); }
        lemma_due_sim(k, a, rest, now, rt);
        let k1 = ksteps::executable_due(k, rest, now as nat, rt as nat);
        let a1 = internal_run(a, due_actions(rest), now, rt);
        let id = due.last();
        lemma_retry_timeout_sim(k1, a1, id, now, rt);
        lemma_internal_run_push(a, due_actions(rest), AbsInternal::TaskRetryTimeout(retry_timeout_req(id)), now, rt);
    }
}

// ---------------------------------------------------------------------------
// The pass
// ---------------------------------------------------------------------------

/// The Abstract run one sweep is.
pub open spec fn sweep_actions(k: KState, ids: Seq<Chars>, now: u64, rt: u64) -> Seq<AbsInternal> {
    let after_deadlines = ksteps::executable_deadlines(k, ids, now as nat);
    let after_leases = ksteps::executable_leases(after_deadlines, ids, now as nat);
    let owed = ksteps::executable_owed_snapshot(after_leases, ids);
    let after_callbacks = ksteps::executable_owed_callbacks(after_leases, owed, now as nat);
    let after_owed = ksteps::executable_owed_listeners(after_callbacks, owed, now as nat);
    let due = ksteps::executable_due_snapshot(after_owed, ids, now as nat);
    deadline_actions(ids)
        + lease_actions(ids)
        + owed_callbacks_actions(after_leases, owed, now)
        + owed_listeners_actions(owed)
        + due_actions(due)
}

pub proof fn lemma_sweep_sim(k: KState, a: AState, ids: Seq<Chars>, now: u64, rt: u64)
    requires
        doc_related(k, a),
        canonical_ids(ids),
        not_self(k),
        now <= kernel::MAX_TIME,
        rt <= kernel::MAX_TIME,
    ensures doc_related(
        ksteps::executable_single_pass(k, ids, now as nat, rt as nat),
        internal_run(a, sweep_actions(k, ids, now, rt), now, rt)),
{
    let k1 = ksteps::executable_deadlines(k, ids, now as nat);
    let s1 = deadline_actions(ids);
    lemma_deadlines_sim(k, a, ids, now, rt);
    let a1 = internal_run(a, s1, now, rt);

    let k2 = ksteps::executable_leases(k1, ids, now as nat);
    let s2 = lease_actions(ids);
    lemma_leases_sim(k1, a1, ids, now, rt);
    let a2 = internal_run(a1, s2, now, rt);
    assert(not_self(k2)) by {
        assert forall|id: Chars| #[trigger] k2.objects.contains_key(id) implies !k2.objects[id].callbacks.contains(id) by {
            assert(k.objects.contains_key(id));
            assert(k1.objects.contains_key(id));
        }
    }

    let owed = ksteps::executable_owed_snapshot(k2, ids);
    lemma_owed_snapshot_ok(k2, a2, ids);
    let k3 = ksteps::executable_owed_callbacks(k2, owed, now as nat);
    let s3 = owed_callbacks_actions(k2, owed, now);
    lemma_owed_callbacks_sim(k2, a2, owed, now, rt);
    let a3 = internal_run(a2, s3, now, rt);

    let k4 = ksteps::executable_owed_listeners(k3, owed, now as nat);
    let s4 = owed_listeners_actions(owed);
    lemma_owed_listeners_sim(k3, a3, owed, now, rt);
    let a4 = internal_run(a3, s4, now, rt);
    assert(k4 == ksteps::executable_owed(k2, owed, now as nat));

    let due = ksteps::executable_due_snapshot(k4, ids, now as nat);
    lemma_due_snapshot_canonical(k4, ids, now);
    let s5 = due_actions(due);
    lemma_due_sim(k4, a4, due, now, rt);

    lemma_internal_run_app(a, s1, s2, now, rt);
    lemma_internal_run_app(a, s1 + s2, s3, now, rt);
    lemma_internal_run_app(a, s1 + s2 + s3, s4, now, rt);
    lemma_internal_run_app(a, s1 + s2 + s3 + s4, s5, now, rt);
}

} // verus!
