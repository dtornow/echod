//! The model's `On(ids)` step as kernel steps, and absorbed by the sweep. The
//! model projects the ids, resumes every awaiter among them by every settled
//! promise among them, and then, id by id, reclaims a lease, tells the
//! listeners and re-arms an offer. Run on a state whose awaiters are resumed
//! in the objects' order, the step is absorbed by the sweep: the sweep
//! computes the same objects after it as before, and sends the same less what
//! the step sent.

use vstd::prelude::*;

use echod_kernel::external::with_objects;
use echod_kernel::internal::lease_timeout_objects;
use echod_kernel::properties::inv;
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::spec::DispatchV;

use crate::absorb::*;
use crate::canon::*;
use crate::sweep::*;
use crate::sweep_proof::*;

verus! {

// --------------------------------------------------------------- the step

/// Every awaiter among `all` resumed by every settled promise among `awaiteds`.
pub open spec fn k_resumes(b: AState, awaiteds: Seq<Seq<char>>, all: Seq<Seq<char>>, now: nat) -> AState
    decreases awaiteds.len(),
{
    if awaiteds.len() == 0 {
        b
    } else {
        callbacks_of(k_resumes(b, awaiteds.drop_last(), all, now), awaiteds.last(), all, now)
    }
}

/// The due work on one id: its lease, its listeners, its offer.
pub open spec fn k_due_one(b: AState, id: Seq<char>, now: nat, t: nat) -> AState {
    let b1 = with_objects(b, lease_timeout_objects(b, id, now));
    let b2 = if b1.objects.contains_key(id) { listeners_of(b1, id, b1.objects[id].listeners, now) } else { b1 };
    retry_fn(b2, id, now, t)
}

pub open spec fn k_due_one_sends(b: AState, id: Seq<char>, now: nat, t: nat) -> Seq<DispatchV> {
    let b1 = with_objects(b, lease_timeout_objects(b, id, now));
    let b2 = if b1.objects.contains_key(id) { listeners_of(b1, id, b1.objects[id].listeners, now) } else { b1 };
    (if b1.objects.contains_key(id) { listeners_sends(b1, id, b1.objects[id].listeners, now) } else { Seq::empty() }) + retry_send(b2, id, now, t)
}

pub open spec fn k_due(b: AState, ids: Seq<Seq<char>>, now: nat, t: nat) -> AState
    decreases ids.len(),
{
    if ids.len() == 0 { b } else { k_due_one(k_due(b, ids.drop_last(), now, t), ids.last(), now, t) }
}

pub open spec fn k_due_sends(b: AState, ids: Seq<Seq<char>>, now: nat, t: nat) -> Seq<DispatchV>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else {
        k_due_sends(b, ids.drop_last(), now, t) + k_due_one_sends(k_due(b, ids.drop_last(), now, t), ids.last(), now, t)
    }
}

/// `On(ids)` in kernel steps.
pub open spec fn k_on(b: AState, ids: Seq<Seq<char>>, now: nat, t: nat) -> AState {
    k_due(k_resumes(phase_deadlines(b, ids, now), ids, ids, now), ids, now, t)
}

pub open spec fn k_on_sends(b: AState, ids: Seq<Seq<char>>, now: nat, t: nat) -> Seq<DispatchV> {
    k_due_sends(k_resumes(phase_deadlines(b, ids, now), ids, ids, now), ids, now, t)
}

/// The resumes among `ids` run in the objects' order: an awaiter among them is
/// resumed by a settled promise among them only when that promise is the
/// first of its settled awaiteds, or the awaiter is done.
pub open spec fn resume_ok(b: AState, ids: Seq<Seq<char>>, now: nat) -> bool {
    forall|i: int, j: int| #![trigger ids[i], ids[j]] 0 <= i < ids.len() && 0 <= j < ids.len() && awaits(b, ids[i], ids[j], now)
        ==> first_awaited(b, ids[i], ids[j], ids_of(b), now) || done(b, ids[j], now)
}

// ------------------------------------------------------------ the absorbs

pub proof fn absorb_deadlines(b: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
    ensures
        ({
            let b2 = phase_deadlines(b, ids, now);
            &&& inv(now, b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b2, now, t) == sweep_sends(b, now, t)
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        absorb_deadlines(b, ids.drop_last(), now, t);
        let b1 = phase_deadlines(b, ids.drop_last(), now);
        let x = ids.last();
        lemma_project_inv(b1, x, now);
        absorb_project(b1, x, now, now, t);
        assert(phase_deadlines(b, ids, now) == with_objects(b1, echod_kernel::internal::promise_timeout_objects(b1, x, now)));
        assert(phase_deadlines(b, ids, now).objects.dom() =~= b1.objects.dom());
    }
}

/// The conditions a run of resumes keeps: awaits only go, done stays, the
/// bucket's keys stay.
pub proof fn absorb_callbacks_of(b: AState, x: Seq<char>, aw: Seq<Seq<char>>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
        forall|i: int| 0 <= i < aw.len() && awaits(b, x, #[trigger] aw[i], now) ==> first_awaited(b, x, aw[i], ids_of(b), now) || done(b, aw[i], now),
    ensures
        ({
            let b2 = callbacks_of(b, x, aw, now);
            &&& inv(now, b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& forall|y: Seq<char>, z: Seq<char>| #[trigger] awaits(b2, y, z, now) ==> awaits(b, y, z, now)
            &&& forall|z: Seq<char>| #[trigger] done(b2, z, now) == done(b, z, now)
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b2, now, t) == sweep_sends(b, now, t)
        }),
    decreases aw.len(),
{
    if aw.len() > 0 {
        let aw0 = aw.drop_last();
        let w = aw.last();
        assert forall|i: int| 0 <= i < aw0.len() && awaits(b, x, #[trigger] aw0[i], now) implies first_awaited(b, x, aw0[i], ids_of(b), now) || done(b, aw0[i], now) by {
            assert(aw0[i] == aw[i]);
        }
        absorb_callbacks_of(b, x, aw0, now, t);
        let b1 = callbacks_of(b, x, aw0, now);
        assert(ids_of(b1) == ids_of(b));
        // the last pair's condition, carried from b to b1
        assert(aw[aw.len() - 1] == w);
        if awaits(b1, x, w, now) {
            assert(awaits(b, x, w, now));
            if !done(b, w, now) {
                assert(first_awaited(b, x, w, ids_of(b), now));
                assert(first_awaited(b1, x, w, ids_of(b1), now)) by {
                    assert forall|i: int, j: int| #![trigger ids_of(b1)[i], ids_of(b1)[j]] 0 <= i < j < ids_of(b1).len() && ids_of(b1)[j] == x implies !awaits(b1, ids_of(b1)[i], w, now) by {
                        assert(!awaits(b, ids_of(b)[i], w, now));
                    }
                }
            }
        }
        absorb_callback_any(b1, x, w, now, t);
        lemma_callback_mono(b1, x, w, now);
    }
}

pub proof fn absorb_resumes(b: AState, awaiteds: Seq<Seq<char>>, all: Seq<Seq<char>>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
        forall|i: int, j: int| #![trigger awaiteds[i], all[j]] 0 <= i < awaiteds.len() && 0 <= j < all.len() && awaits(b, awaiteds[i], all[j], now)
            ==> first_awaited(b, awaiteds[i], all[j], ids_of(b), now) || done(b, all[j], now),
    ensures
        ({
            let b2 = k_resumes(b, awaiteds, all, now);
            &&& inv(now, b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& forall|y: Seq<char>, z: Seq<char>| #[trigger] awaits(b2, y, z, now) ==> awaits(b, y, z, now)
            &&& forall|z: Seq<char>| #[trigger] done(b2, z, now) == done(b, z, now)
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b2, now, t) == sweep_sends(b, now, t)
        }),
    decreases awaiteds.len(),
{
    if awaiteds.len() > 0 {
        let aw0 = awaiteds.drop_last();
        let x = awaiteds.last();
        assert forall|i: int, j: int| #![trigger aw0[i], all[j]] 0 <= i < aw0.len() && 0 <= j < all.len() && awaits(b, aw0[i], all[j], now)
            implies first_awaited(b, aw0[i], all[j], ids_of(b), now) || done(b, all[j], now) by {
            assert(aw0[i] == awaiteds[i]);
        }
        absorb_resumes(b, aw0, all, now, t);
        let b1 = k_resumes(b, aw0, all, now);
        assert(ids_of(b1) == ids_of(b));
        assert(awaiteds[awaiteds.len() - 1] == x);
        assert forall|j: int| 0 <= j < all.len() && awaits(b1, x, #[trigger] all[j], now) implies first_awaited(b1, x, all[j], ids_of(b1), now) || done(b1, all[j], now) by {
            assert(awaits(b, x, all[j], now));
            if !done(b, all[j], now) {
                assert(first_awaited(b, x, all[j], ids_of(b), now));
                assert forall|i: int, k: int| #![trigger ids_of(b1)[i], ids_of(b1)[k]] 0 <= i < k < ids_of(b1).len() && ids_of(b1)[k] == x implies !awaits(b1, ids_of(b1)[i], all[j], now) by {
                    assert(!awaits(b, ids_of(b)[i], all[j], now));
                }
            }
        }
        absorb_callbacks_of(b1, x, all, now, t);
    }
}

pub proof fn absorb_listeners_of(b: AState, x: Seq<char>, l: Seq<Seq<char>>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
    ensures
        ({
            let b2 = listeners_of(b, x, l, now);
            &&& inv(now, b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b, now, t).to_multiset() == (listeners_sends(b, x, l, now) + sweep_sends(b2, now, t)).to_multiset()
        }),
    decreases l.len(),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    if l.len() == 0 {
        assert((Seq::<DispatchV>::empty() + sweep_sends(b, now, t)) =~= sweep_sends(b, now, t));
    } else {
        absorb_listeners_of(b, x, l.drop_last(), now, t);
        let b1 = listeners_of(b, x, l.drop_last(), now);
        let y = l.last();
        absorb_listener(b1, x, y, now, t);
        let b2 = listener_fn(b1, x, y, now);
        assert(b2.objects.dom() =~= b.objects.dom());
        let s0 = listeners_sends(b, x, l.drop_last(), now);
        let s1 = listener_send(b1, x, y, now);
        assert(listeners_sends(b, x, l, now) == s0 + s1);
        assert(sweep_sends(b, now, t).to_multiset() == s0.to_multiset().add(sweep_sends(b1, now, t).to_multiset()));
        assert(sweep_sends(b1, now, t).to_multiset() == s1.to_multiset().add(sweep_sends(b2, now, t).to_multiset()));
        assert((s0 + s1 + sweep_sends(b2, now, t)).to_multiset() =~= s0.to_multiset().add(s1.to_multiset().add(sweep_sends(b2, now, t).to_multiset())));
    }
}

pub proof fn absorb_due_one(b: AState, id: Seq<char>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        now <= MAX_TIME,
        b.objects.dom().finite(),
    ensures
        ({
            let b2 = k_due_one(b, id, now, t);
            &&& inv(now, b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b, now, t).to_multiset() == (k_due_one_sends(b, id, now, t) + sweep_sends(b2, now, t)).to_multiset()
        }),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    absorb_lease(b, id, now, t);
    let b1 = with_objects(b, lease_timeout_objects(b, id, now));
    assert(b1.objects.dom() =~= b.objects.dom());
    let s1: Seq<DispatchV> = if b1.objects.contains_key(id) { listeners_sends(b1, id, b1.objects[id].listeners, now) } else { Seq::empty() };
    let b2 = if b1.objects.contains_key(id) { listeners_of(b1, id, b1.objects[id].listeners, now) } else { b1 };
    if b1.objects.contains_key(id) {
        absorb_listeners_of(b1, id, b1.objects[id].listeners, now, t);
    } else {
        assert((Seq::<DispatchV>::empty() + sweep_sends(b1, now, t)) =~= sweep_sends(b1, now, t));
    }
    absorb_retry(b2, id, now, t);
    let b3 = retry_fn(b2, id, now, t);
    let s2 = retry_send(b2, id, now, t);
    assert(k_due_one(b, id, now, t) == b3);
    assert(k_due_one_sends(b, id, now, t) == s1 + s2);
    assert(b3.objects.dom() =~= b.objects.dom());
    assert((s1 + s2 + sweep_sends(b3, now, t)).to_multiset() =~= s1.to_multiset().add(s2.to_multiset().add(sweep_sends(b3, now, t).to_multiset())));
}

pub proof fn absorb_due(b: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        now <= MAX_TIME,
        b.objects.dom().finite(),
    ensures
        ({
            let b2 = k_due(b, ids, now, t);
            &&& inv(now, b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b, now, t).to_multiset() == (k_due_sends(b, ids, now, t) + sweep_sends(b2, now, t)).to_multiset()
        }),
    decreases ids.len(),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    if ids.len() == 0 {
        assert((Seq::<DispatchV>::empty() + sweep_sends(b, now, t)) =~= sweep_sends(b, now, t));
    } else {
        absorb_due(b, ids.drop_last(), now, t);
        let b1 = k_due(b, ids.drop_last(), now, t);
        absorb_due_one(b1, ids.last(), now, t);
        let b2 = k_due_one(b1, ids.last(), now, t);
        let s0 = k_due_sends(b, ids.drop_last(), now, t);
        let s1 = k_due_one_sends(b1, ids.last(), now, t);
        assert((s0 + s1 + sweep_sends(b2, now, t)).to_multiset() =~= s0.to_multiset().add(s1.to_multiset().add(sweep_sends(b2, now, t).to_multiset())));
    }
}

/// The step is absorbed by the sweep.
pub proof fn absorb_on(b: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        now <= MAX_TIME,
        b.objects.dom().finite(),
        resume_ok(phase_deadlines(b, ids, now), ids, now),
    ensures
        ({
            let b2 = k_on(b, ids, now, t);
            &&& inv(now, b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b, now, t).to_multiset() == (k_on_sends(b, ids, now, t) + sweep_sends(b2, now, t)).to_multiset()
        }),
{
    absorb_deadlines(b, ids, now, t);
    let b1 = phase_deadlines(b, ids, now);
    absorb_resumes(b1, ids, ids, now, t);
    let b2 = k_resumes(b1, ids, ids, now);
    absorb_due(b2, ids, now, t);
}

} // verus!
