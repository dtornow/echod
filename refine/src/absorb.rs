//! The sweep absorbs any one of its own steps: taken first, a step changes
//! neither what the sweep computes nor, up to order, what is sent in all. The
//! model runs these steps in its own order (a timer's object at a time, a
//! callback's awaiter at a time); the kernel runs them phase by phase. Read
//! off the canonical form, each step is a local change the form does not see.
//!
//! The one step with a side condition is a callback's: resuming `w` by `x`
//! first is absorbed when `x` is the first, in the objects' order, of the
//! settled promises holding a callback for `w`; the model's resumes are run in
//! that order.

use vstd::prelude::*;

use echod_kernel::external::with_objects;
use echod_kernel::internal::{lease_due, lease_timeout_objects, promise_timeout_objects, retry_due};
use echod_kernel::object::{lemma_next_offer, next_offer, without};
use echod_kernel::object_proof::lemma_without_contains;
use echod_kernel::properties::{inv, inv_obj, no_dups, opt_or_zero};
use echod_kernel::properties_proof::lemma_inv_pointwise;
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::twins::DispatchV;

use crate::canon::*;
use crate::sweep::*;
use crate::sweep_proof::*;

verus! {

// ------------------------------------------------------------ small lemmas

/// A task viewed through a promise and then through one no less settled is
/// the task viewed through the second.
pub proof fn lemma_view_twice(t: ATask, p1: APromise, p2: APromise)
    requires
        p1.state != PromiseState::Pending ==> p2.state != PromiseState::Pending,
    ensures
        t.view_through(p1).view_through(p2) == t.view_through(p2),
{
}

/// Projecting earlier and then at `now` is projecting at `now`.
pub proof fn lemma_project_mono(p: APromise, t0: nat, now: nat)
    requires
        t0 <= now,
    ensures
        p.project(t0).project(now) == p.project(now),
{
    let pp0 = p.project_promise(t0);
    let q = p.project(t0);
    let ppq = q.project_promise(now);
    let pp = p.project_promise(now);
    assert(APromise { task: p.task, ..ppq } == pp);
    assert(pp0.state != PromiseState::Pending ==> ppq.state != PromiseState::Pending);
    match p.task {
        None => {
            assert(q.project(now) == p.project(now));
        },
        Some(t) => {
            lemma_view_twice(t, pp0, ppq);
            assert(t.view_through(ppq) == t.view_through(pp));
            assert(q.task == Some(t.view_through(pp0)));
            assert(q.project(now).task == Some(t.view_through(pp0).view_through(ppq)));
            assert(q.project(now) == p.project(now));
        },
    }
}

/// `without` of an absent element is the identity.
pub proof fn lemma_without_absent(s: Seq<Seq<char>>, x: Seq<char>)
    requires
        !s.contains(x),
    ensures
        without(s, x) == s,
    decreases s.len(),
{
    if s.len() > 0 {
        assert(!s.drop_last().contains(x)) by {
            if s.drop_last().contains(x) {
                let i = choose|i: int| 0 <= i < s.drop_last().len() && s.drop_last()[i] == x;
                assert(s[i] == x);
            }
        }
        lemma_without_absent(s.drop_last(), x);
        assert(s.last() != x) by {
            assert(s[s.len() - 1] == s.last());
        }
        assert(without(s, x) =~= s);
    }
}

pub proof fn lemma_map_push(l: Seq<Seq<char>>, f: spec_fn(Seq<char>) -> DispatchV)
    requires
        l.len() > 0,
    ensures
        l.map_values(f) == l.drop_last().map_values(f).push(f(l.last())),
{
    assert(l.map_values(f) =~= l.drop_last().map_values(f).push(f(l.last())));
}

/// Mapping a list less one element: the multiset less that element's image.
pub proof fn lemma_map_without(l: Seq<Seq<char>>, a: Seq<char>, f: spec_fn(Seq<char>) -> DispatchV)
    requires
        no_dups(l),
        l.contains(a),
    ensures
        l.map_values(f).to_multiset() == without(l, a).map_values(f).to_multiset().insert(f(a)),
    decreases l.len(),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_axioms;
    let l0 = l.drop_last();
    let y = l.last();
    assert(no_dups(l0)) by {
        assert forall|i: int, j: int| 0 <= i < l0.len() && 0 <= j < l0.len() && l0[i] == l0[j] implies i == j by {
            assert(l[i] == l[j]);
        }
    }
    lemma_map_push(l, f);
    if y == a {
        assert(!l0.contains(a)) by {
            if l0.contains(a) {
                let i = choose|i: int| 0 <= i < l0.len() && l0[i] == a;
                assert(l[i] == l[l.len() - 1]);
            }
        }
        lemma_without_absent(l0, a);
        assert(without(l, a) == l0);
    } else {
        assert(l0.contains(a)) by {
            let i = choose|i: int| 0 <= i < l.len() && l[i] == a;
            assert(i < l.len() - 1);
            assert(l0[i] == a);
        }
        lemma_map_without(l0, a, f);
        assert(without(l, a) == without(l0, a).push(y));
        lemma_map_push(without(l, a), f);
        assert(without(l, a).drop_last() == without(l0, a));
        assert(without(l, a).last() == y);
        let m = without(l0, a).map_values(f).to_multiset();
        assert(l.map_values(f).to_multiset() == m.insert(f(a)).insert(f(y)));
        assert(without(l, a).map_values(f).to_multiset().insert(f(a)) == m.insert(f(y)).insert(f(a)));
        assert(m.insert(f(a)).insert(f(y)) =~= m.insert(f(y)).insert(f(a)));
    }
}

/// A sum that differs in one summand by one element.
pub proof fn lemma_fold_sends_one(ids: Seq<Seq<char>>, f: spec_fn(Seq<char>) -> Seq<DispatchV>, g: spec_fn(Seq<char>) -> Seq<DispatchV>, x: Seq<char>, d: DispatchV)
    requires
        ids.no_duplicates(),
        ids.contains(x),
        forall|y: Seq<char>| ids.contains(y) && y != x ==> #[trigger] f(y) == g(y),
        f(x).to_multiset() == g(x).to_multiset().insert(d),
    ensures
        fold_sends(ids, f).to_multiset() == fold_sends(ids, g).to_multiset().insert(d),
    decreases ids.len(),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    lemma_no_dup_last(ids);
    let ids0 = ids.drop_last();
    let y = ids.last();
    assert forall|z: Seq<char>| ids0.contains(z) implies ids.contains(z) by {
        let i = choose|i: int| 0 <= i < ids0.len() && ids0[i] == z;
        assert(ids[i] == z);
    }
    if y == x {
        lemma_fold_sends_ext(ids0, f, g);
        let m = fold_sends(ids0, g).to_multiset();
        assert(fold_sends(ids, f).to_multiset() == m.add(f(x).to_multiset()));
        assert(fold_sends(ids, g).to_multiset() == m.add(g(x).to_multiset()));
        assert(m.add(g(x).to_multiset().insert(d)) =~= m.add(g(x).to_multiset()).insert(d));
    } else {
        assert(ids0.contains(x)) by {
            let i = choose|i: int| 0 <= i < ids.len() && ids[i] == x;
            assert(i < ids.len() - 1);
            assert(ids0[i] == x);
        }
        lemma_fold_sends_one(ids0, f, g, x, d);
        assert(ids.contains(y)) by {
            assert(ids[ids.len() - 1] == y);
        }
        assert(f(y) == g(y));
        let m = fold_sends(ids0, g).to_multiset();
        assert(fold_sends(ids, f).to_multiset() == m.insert(d).add(g(y).to_multiset()));
        assert(fold_sends(ids, g).to_multiset().insert(d) == m.add(g(y).to_multiset()).insert(d));
        assert(m.insert(d).add(g(y).to_multiset()) =~= m.add(g(y).to_multiset()).insert(d));
    }
}

// ------------------------------------------------------ resumes, rearranged

pub proof fn lemma_resumed_none(b: AState, w: Seq<char>, ids: Seq<Seq<char>>, t: ATask, now: nat)
    requires
        forall|i: int| 0 <= i < ids.len() ==> !awaits(b, #[trigger] ids[i], w, now),
    ensures
        resumed(b, w, ids, t, now) == t,
    decreases ids.len(),
{
    if ids.len() > 0 {
        assert forall|i: int| 0 <= i < ids.drop_last().len() implies !awaits(b, #[trigger] ids.drop_last()[i], w, now) by {
            assert(ids.drop_last()[i] == ids[i]);
        }
        lemma_resumed_none(b, w, ids.drop_last(), t, now);
        assert(!awaits(b, ids.last(), w, now)) by {
            assert(ids[ids.len() - 1] == ids.last());
        }
    }
}

/// A done task is not resumed.
pub proof fn lemma_resumed_fulfilled(b: AState, w: Seq<char>, ids: Seq<Seq<char>>, t: ATask, now: nat)
    requires
        t.state == TaskState::Fulfilled,
    ensures
        resumed(b, w, ids, t, now) == t,
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_resumed_fulfilled(b, w, ids.drop_last(), t, now);
    }
}

/// A pending task is only told: its state, offer, lease and version stay, and
/// re-arming it first or last is the same.
pub proof fn lemma_resumed_pending(b: AState, w: Seq<char>, ids: Seq<Seq<char>>, t: ATask, now: nat, rt: nat)
    requires
        t.state == TaskState::Pending,
    ensures
        ({
            let r = resumed(b, w, ids, t, now);
            &&& r.state == TaskState::Pending
            &&& r.retry_timeout_at == t.retry_timeout_at
            &&& r.lease_timeout_at == t.lease_timeout_at
            &&& r.version == t.version
            &&& resumed(b, w, ids, t.rearm(now, rt), now) == r.rearm(now, rt)
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_resumed_pending(b, w, ids.drop_last(), t, now, rt);
    }
}

/// Resuming `w` by `x` first, then by the rest in order, is resuming it in
/// order, when `x` is the first of its settled awaiteds.
pub open spec fn first_awaited(b: AState, x: Seq<char>, w: Seq<char>, ids: Seq<Seq<char>>, now: nat) -> bool {
    forall|i: int, j: int| #![trigger ids[i], ids[j]] 0 <= i < j < ids.len() && ids[j] == x ==> !awaits(b, ids[i], w, now)
}

/// `w` is done, or not a task: a resume leaves it as it is, whatever the order.
pub open spec fn done(b: AState, w: Seq<char>, now: nat) -> bool {
    ||| !b.objects.contains_key(w)
    ||| b.objects[w].project(now).task is None
    ||| b.objects[w].project(now).task.unwrap().state == TaskState::Fulfilled
}

pub proof fn lemma_resumed_first(b: AState, b2: AState, w: Seq<char>, x: Seq<char>, ids: Seq<Seq<char>>, t: ATask, now: nat)
    requires
        ids.no_duplicates(),
        ids.contains(x),
        awaits(b, x, w, now),
        !awaits(b2, x, w, now),
        forall|y: Seq<char>| y != x ==> #[trigger] awaits(b2, y, w, now) == awaits(b, y, w, now),
        forall|y: Seq<char>| y != x && #[trigger] awaits(b, y, w, now) ==> since(b2, y, now) == since(b, y, now),
        first_awaited(b, x, w, ids, now),
    ensures
        resumed(b2, w, ids, resume_step(t, x, since(b, x, now)), now) == resumed(b, w, ids, t, now),
    decreases ids.len(),
{
    lemma_no_dup_last(ids);
    let ids0 = ids.drop_last();
    let y = ids.last();
    let t2 = resume_step(t, x, since(b, x, now));
    let j = choose|j: int| 0 <= j < ids.len() && ids[j] == x;
    if y == x {
        assert forall|i: int| 0 <= i < ids0.len() implies !awaits(b, #[trigger] ids0[i], w, now) by {
            assert(ids0[i] == ids[i]);
            assert(ids[ids.len() - 1] == x);
        }
        assert forall|i: int| 0 <= i < ids0.len() implies !awaits(b2, #[trigger] ids0[i], w, now) by {
            assert(ids0[i] == ids[i]);
            assert(ids0[i] != x);
        }
        lemma_resumed_none(b, w, ids0, t, now);
        lemma_resumed_none(b2, w, ids0, t2, now);
    } else {
        assert(j < ids.len() - 1);
        assert(ids0[j] == x);
        assert(first_awaited(b, x, w, ids0, now)) by {
            assert forall|i: int, k: int| #![trigger ids0[i], ids0[k]] 0 <= i < k < ids0.len() && ids0[k] == x implies !awaits(b, ids0[i], w, now) by {
                assert(ids0[i] == ids[i] && ids0[k] == ids[k]);
            }
        }
        lemma_resumed_first(b, b2, w, x, ids0, t, now);
    }
}

// ------------------------------------------------------------- the absorbs

/// What the sweep reads of two states' forms, object by object: the objects
/// after phase 4, and the records a settled object's unblocks carry.
pub open spec fn forms_agree(b: AState, b2: AState, ids: Seq<Seq<char>>, now: nat) -> bool {
    &&& b2.objects.dom() == b.objects.dom()
    &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> c4(b2, id, ids, now) == c4(b, id, ids, now)
    &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> c12(b2.objects[id], now).to_record() == c12(b.objects[id], now).to_record()
}

/// On agreeing forms the sweep computes the same objects, sends the same
/// offers, and the unblocks of each object are those of its listeners.
pub proof fn lemma_agree_objects(b: AState, b2: AState, now: nat, t: nat)
    requires
        inv(now, b),
        inv(now, b2),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
        forms_agree(b, b2, ids_of(b), now),
    ensures
        sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects,
        sweep_fn(b2, now, t).schedules == b2.schedules,
        sweep_fn(b, now, t).schedules == b.schedules,
        sweep_sends(b2, now, t) == canon_sends(b2, now, t),
        sweep_sends(b, now, t) == canon_sends(b, now, t),
        ids_of(b2) == ids_of(b),
        fold_sends(ids_of(b), |id: Seq<char>| c_execute(b2, id, ids_of(b), now)) == fold_sends(ids_of(b), |id: Seq<char>| c_execute(b, id, ids_of(b), now)),
        forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> c12(b2.objects[id], now).state == c12(b.objects[id], now).state,
{
    let ids = ids_of(b);
    lemma_sweep_canon(b, now, t);
    lemma_sweep_canon(b2, now, t);
    assert(ids_of(b2) == ids);
    assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies c5(b2, id, ids, now, t) == c5(b, id, ids, now, t) && c12(b2.objects[id], now).state == c12(b.objects[id], now).state by {
        assert(c4(b2, id, ids, now) == c4(b, id, ids, now));
        assert(c4(b2, id, ids, now).state == c12(b2.objects[id], now).state);
    }
    assert(sweep_fn(b2, now, t).objects =~= sweep_fn(b, now, t).objects);
    assert forall|id: Seq<char>| ids.contains(id) implies #[trigger] c_execute(b2, id, ids, now) == c_execute(b, id, ids, now) by {
        if b.objects.contains_key(id) {
            assert(c4(b2, id, ids, now) == c4(b, id, ids, now));
        }
    }
    lemma_fold_sends_ext(ids, |id: Seq<char>| c_execute(b2, id, ids, now), |id: Seq<char>| c_execute(b, id, ids, now));
}

/// Agreeing forms with the same listeners: the same sends.
pub proof fn lemma_agree_sends(b: AState, b2: AState, now: nat, t: nat)
    requires
        inv(now, b),
        inv(now, b2),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
        forms_agree(b, b2, ids_of(b), now),
        forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> c12(b2.objects[id], now).listeners == c12(b.objects[id], now).listeners,
    ensures
        sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects,
        sweep_fn(b2, now, t).schedules == b2.schedules,
        sweep_fn(b, now, t).schedules == b.schedules,
        sweep_sends(b2, now, t) == sweep_sends(b, now, t),
{
    let ids = ids_of(b);
    lemma_agree_objects(b, b2, now, t);
    assert forall|id: Seq<char>| ids.contains(id) implies #[trigger] c_unblocks(b2, id, now) == c_unblocks(b, id, now) by {
        if b.objects.contains_key(id) {
            let c = c12(b.objects[id], now);
            let c2 = c12(b2.objects[id], now);
            if c.state != PromiseState::Pending {
                assert(c_unblocks(b2, id, now) =~= c_unblocks(b, id, now));
            }
        }
    }
    lemma_fold_sends_ext(ids, |y: Seq<char>| c_unblocks(b2, y, now), |y: Seq<char>| c_unblocks(b, y, now));
}

/// Agreeing forms, one settled object short of one listener: the same sends
/// less that listener's unblock.
pub proof fn lemma_agree_sends_but_unblock(b: AState, b2: AState, x: Seq<char>, address: Seq<char>, now: nat, t: nat)
    requires
        inv(now, b),
        inv(now, b2),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
        forms_agree(b, b2, ids_of(b), now),
        forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && id != x ==> c12(b2.objects[id], now).listeners == c12(b.objects[id], now).listeners,
        b.objects.contains_key(x),
        c12(b.objects[x], now).state != PromiseState::Pending,
        no_dups(c12(b.objects[x], now).listeners),
        c12(b.objects[x], now).listeners.contains(address),
        c12(b2.objects[x], now).listeners == without(c12(b.objects[x], now).listeners, address),
    ensures
        sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects,
        sweep_fn(b2, now, t).schedules == b2.schedules,
        sweep_fn(b, now, t).schedules == b.schedules,
        sweep_sends(b, now, t).to_multiset() == (seq![unblock_of(c12(b.objects[x], now), address)] + sweep_sends(b2, now, t)).to_multiset(),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_axioms;
    let ids = ids_of(b);
    lemma_ids_cover(b);
    b.objects.dom().lemma_to_seq_no_duplicates();
    lemma_agree_objects(b, b2, now, t);
    let p = c12(b.objects[x], now);
    let p2 = c12(b2.objects[x], now);
    let f = |ad: Seq<char>| unblock_of(p, ad);
    let d = unblock_of(p, address);
    assert(c_unblocks(b, x, now) == p.listeners.map_values(f));
    assert(c_unblocks(b2, x, now) =~= without(p.listeners, address).map_values(f)) by {
        assert(p2.state != PromiseState::Pending);
        assert(p2.to_record() == p.to_record());
        assert forall|i: int| 0 <= i < p2.listeners.len() implies unblock_of(p2, p2.listeners[i]) == f(p2.listeners[i]) by {}
    }
    lemma_map_without(p.listeners, address, f);
    assert forall|id: Seq<char>| ids.contains(id) && id != x implies #[trigger] c_unblocks(b, id, now) == c_unblocks(b2, id, now) by {
        if b.objects.contains_key(id) {
            let c = c12(b.objects[id], now);
            if c.state != PromiseState::Pending {
                assert(c_unblocks(b2, id, now) =~= c_unblocks(b, id, now));
            }
        }
    }
    lemma_fold_sends_one(ids, |y: Seq<char>| c_unblocks(b, y, now), |y: Seq<char>| c_unblocks(b2, y, now), x, d);
    let u = fold_sends(ids, |y: Seq<char>| c_unblocks(b, y, now));
    let u2 = fold_sends(ids, |y: Seq<char>| c_unblocks(b2, y, now));
    let e = fold_sends(ids, |id: Seq<char>| c_execute(b, id, ids, now));
    assert(canon_sends(b, now, t) == u + e);
    assert(canon_sends(b2, now, t) == u2 + e);
    assert((u + e).to_multiset() =~= (seq![d] + (u2 + e)).to_multiset());
}

/// Forms agreeing but at one object, whose offer is due in one and taken in
/// the other: the same objects after the sweep, the same sends less that offer.
pub proof fn lemma_agree_sends_but_execute(b: AState, b2: AState, x: Seq<char>, now: nat, t: nat)
    requires
        inv(now, b),
        inv(now, b2),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
        b2.objects.dom() == b.objects.dom(),
        forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && id != x ==> c4(b2, id, ids_of(b), now) == c4(b, id, ids_of(b), now),
        forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> c12(b2.objects[id], now).to_record() == c12(b.objects[id], now).to_record(),
        forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> c12(b2.objects[id], now).listeners == c12(b.objects[id], now).listeners && c12(b2.objects[id], now).state == c12(b.objects[id], now).state,
        b.objects.contains_key(x),
        c5(b2, x, ids_of(b), now, t) == c5(b, x, ids_of(b), now, t),
        retry_due(c4(b, x, ids_of(b), now), now),
        !retry_due(c4(b2, x, ids_of(b), now), now),
    ensures
        sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects,
        sweep_fn(b2, now, t).schedules == b2.schedules,
        sweep_fn(b, now, t).schedules == b.schedules,
        sweep_sends(b, now, t).to_multiset() == (seq![execute_of(x, c4(b, x, ids_of(b), now))] + sweep_sends(b2, now, t)).to_multiset(),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_axioms;
    let ids = ids_of(b);
    lemma_ids_cover(b);
    b.objects.dom().lemma_to_seq_no_duplicates();
    lemma_sweep_canon(b, now, t);
    lemma_sweep_canon(b2, now, t);
    assert(ids_of(b2) == ids);
    assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies c5(b2, id, ids, now, t) == c5(b, id, ids, now, t) by {
        if id != x {
            assert(c4(b2, id, ids, now) == c4(b, id, ids, now));
        }
    }
    assert(sweep_fn(b2, now, t).objects =~= sweep_fn(b, now, t).objects);
    // the unblocks: the same
    assert forall|id: Seq<char>| ids.contains(id) implies #[trigger] c_unblocks(b2, id, now) == c_unblocks(b, id, now) by {
        if b.objects.contains_key(id) {
            let c = c12(b.objects[id], now);
            if c.state != PromiseState::Pending {
                assert(c_unblocks(b2, id, now) =~= c_unblocks(b, id, now));
            }
        }
    }
    lemma_fold_sends_ext(ids, |y: Seq<char>| c_unblocks(b2, y, now), |y: Seq<char>| c_unblocks(b, y, now));
    // the offers: one short
    assert forall|id: Seq<char>| ids.contains(id) && id != x implies #[trigger] c_execute(b, id, ids, now) == c_execute(b2, id, ids, now) by {
        if b.objects.contains_key(id) {
            assert(c4(b2, id, ids, now) == c4(b, id, ids, now));
        }
    }
    let d = execute_of(x, c4(b, x, ids, now));
    assert(c_execute(b, x, ids, now) == seq![d]);
    assert(c_execute(b2, x, ids, now) == Seq::<DispatchV>::empty());
    assert(seq![d].to_multiset() == Seq::<DispatchV>::empty().to_multiset().insert(d)) by {
        assert(seq![d] == Seq::<DispatchV>::empty().push(d));
    }
    lemma_fold_sends_one(ids, |id: Seq<char>| c_execute(b, id, ids, now), |id: Seq<char>| c_execute(b2, id, ids, now), x, d);
    let u = fold_sends(ids, |y: Seq<char>| c_unblocks(b, y, now));
    let e = fold_sends(ids, |id: Seq<char>| c_execute(b, id, ids, now));
    let e2 = fold_sends(ids, |id: Seq<char>| c_execute(b2, id, ids, now));
    assert(canon_sends(b, now, t) == u + e);
    assert(canon_sends(b2, now, t) == u + e2);
    assert((u + e).to_multiset() =~= (seq![d] + (u + e2)).to_multiset());
}

// ---------------------------------------------------------------- the steps

/// Two states whose objects agree but at `x`, where they are read alike and
/// await alike: their forms agree.
pub proof fn lemma_forms_from_same_reads(b: AState, b2: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        b2.objects.dom() == b.objects.dom(),
        forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> c12(b2.objects[id], now) == c12(b.objects[id], now),
        forall|y: Seq<char>, w: Seq<char>| #[trigger] awaits(b2, y, w, now) == awaits(b, y, w, now),
        forall|y: Seq<char>, w: Seq<char>| #[trigger] awaits(b, y, w, now) ==> since(b2, y, now) == since(b, y, now),
    ensures
        forms_agree(b, b2, ids, now),
{
    assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies c4(b2, id, ids, now) == c4(b, id, ids, now) by {
        match c12(b.objects[id], now).task {
            None => {},
            Some(tk) => {
                lemma_resumed_same(b2, b, id, ids, tk, now);
            },
        }
    }
}

/// Projecting one object first, at any earlier instant, is absorbed.
pub proof fn absorb_project(b: AState, x: Seq<char>, t0: nat, now: nat, t: nat)
    requires
        inv(now, b),
        inv(now, with_objects(b, promise_timeout_objects(b, x, t0))),
        t0 <= now,
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
    ensures
        ({
            let b2 = with_objects(b, promise_timeout_objects(b, x, t0));
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b2, now, t) == sweep_sends(b, now, t)
        }),
{
    let b2 = with_objects(b, promise_timeout_objects(b, x, t0));
    let ids = ids_of(b);
    if b.objects.contains_key(x) {
        assert(b2.objects.dom() =~= b.objects.dom());
        lemma_project_mono(b.objects[x], t0, now);
        assert(b2.objects[x].project(now) == b.objects[x].project(now));
        assert(b2.objects[x].callbacks == b.objects[x].callbacks);
        assert forall|y: Seq<char>, w: Seq<char>| #[trigger] awaits(b2, y, w, now) == awaits(b, y, w, now) && since(b2, y, now) == since(b, y, now) by {}
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies c12(b2.objects[id], now) == c12(b.objects[id], now) by {}
        lemma_forms_from_same_reads(b, b2, ids, now);
        lemma_agree_sends(b, b2, now, t);
    } else {
        assert(b2 == b);
    }
}

/// Reclaiming one lease first is absorbed.
pub proof fn absorb_lease(b: AState, x: Seq<char>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
    ensures
        ({
            let b2 = with_objects(b, lease_timeout_objects(b, x, now));
            &&& inv(now, b2)
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b2, now, t) == sweep_sends(b, now, t)
        }),
{
    let b2 = with_objects(b, lease_timeout_objects(b, x, now));
    lemma_lease_inv(b, x, now);
    let ids = ids_of(b);
    if b.objects.contains_key(x) && lease_due(b.objects[x], now) {
        let p = b.objects[x];
        let tk = p.task.unwrap().release(p.task.unwrap().lease_timeout_at.unwrap() as nat);
        let p2 = p.with_task(tk);
        assert(b2.objects == b.objects.insert(x, p2));
        assert(b2.objects.dom() =~= b.objects.dom());
        assert(p.project(now) == p);
        lemma_project_pending_task(p, now, tk);
        assert(p2.project(now) == p2);
        assert(!lease_due(p2, now));
        assert(c12(p2, now) == p2);
        assert(c12(p, now) == p2);
        assert forall|y: Seq<char>, w: Seq<char>| #[trigger] awaits(b2, y, w, now) == awaits(b, y, w, now) && since(b2, y, now) == since(b, y, now) by {}
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies c12(b2.objects[id], now) == c12(b.objects[id], now) by {}
        lemma_forms_from_same_reads(b, b2, ids, now);
        lemma_agree_sends(b, b2, now, t);
    } else {
        assert(b2 == b);
    }
}

/// Re-arming one due offer first is absorbed: the offer it sends is the one
/// the sweep would have sent.
pub proof fn absorb_retry(b: AState, x: Seq<char>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        now <= MAX_TIME,
        b.objects.dom().finite(),
    ensures
        ({
            let b2 = retry_fn(b, x, now, t);
            &&& inv(now, b2)
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b, now, t).to_multiset() == (retry_send(b, x, now, t) + sweep_sends(b2, now, t)).to_multiset()
        }),
{
    let b2 = retry_fn(b, x, now, t);
    lemma_retry_inv(b, x, now, t);
    let ids = ids_of(b);
    if b.objects.contains_key(x) && retry_due(b.objects[x], now) {
        let p = b.objects[x];
        let t0 = p.task.unwrap();
        let p2 = p.with_task(t0.rearm(now, t));
        assert(b2.objects == b.objects.insert(x, p2));
        assert(b2.objects.dom() =~= b.objects.dom());
        assert(p.project(now) == p);
        lemma_project_pending_task(p, now, t0.rearm(now, t));
        assert(p2.project(now) == p2);
        assert(c12(p, now) == p);
        assert(c12(p2, now) == p2);
        assert forall|y: Seq<char>, w: Seq<char>| #[trigger] awaits(b2, y, w, now) == awaits(b, y, w, now) && since(b2, y, now) == since(b, y, now) by {}
        // the one object that differs: its task re-armed, before or after its resumes
        let due = opt_or_zero(t0.retry_timeout_at);
        lemma_next_offer(due, now, t);
        let n = next_offer(due, now, t);
        assert(now < n <= now + t);
        assert(n as u64 == n);
        lemma_resumed_pending(b, x, ids, t0, now, t);
        lemma_resumed_same(b2, b, x, ids, t0, now);
        lemma_resumed_same(b2, b, x, ids, t0.rearm(now, t), now);
        let r = resumed(b, x, ids, t0, now);
        assert(c4(b, x, ids, now) == p.with_task(r));
        assert(c4(b2, x, ids, now) == p.with_task(r.rearm(now, t)));
        assert(retry_due(c4(b, x, ids, now), now));
        assert(!retry_due(c4(b2, x, ids, now), now));
        assert(c5(b2, x, ids, now, t) == c5(b, x, ids, now, t));
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && id != x implies c4(b2, id, ids, now) == c4(b, id, ids, now) by {
            assert(c12(b2.objects[id], now) == c12(b.objects[id], now));
            match c12(b.objects[id], now).task {
                None => {},
                Some(tk2) => {
                    lemma_resumed_same(b2, b, id, ids, tk2, now);
                },
            }
        }
        lemma_agree_sends_but_execute(b, b2, x, now, t);
        assert(retry_send(b, x, now, t) == seq![execute_of(x, c4(b, x, ids, now))]);
    } else {
        assert(b2 == b);
        assert(retry_send(b, x, now, t) == Seq::<DispatchV>::empty());
        assert((Seq::<DispatchV>::empty() + sweep_sends(b, now, t)) =~= sweep_sends(b, now, t));
    }
}

/// Telling one listener first is absorbed: the unblock it sends is the one
/// the sweep would have sent.
pub proof fn absorb_listener(b: AState, x: Seq<char>, address: Seq<char>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
    ensures
        ({
            let b2 = listener_fn(b, x, address, now);
            &&& inv(now, b2)
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b, now, t).to_multiset() == (listener_send(b, x, address, now) + sweep_sends(b2, now, t)).to_multiset()
        }),
{
    let b2 = listener_fn(b, x, address, now);
    lemma_listener_inv(b, x, address, now);
    let ids = ids_of(b);
    if b.objects.contains_key(x) {
        let p = b.objects[x].project(now);
        lemma_insert_same(with_objects(b, b.objects.insert(x, p)), x);
        if p.state == PromiseState::Pending || !p.listeners.contains(address) {
            // the step projects x: absorbed as a projection
            let b1 = with_objects(b, b.objects.insert(x, p));
            assert(b2 == b1);
            assert(b1 == with_objects(b, promise_timeout_objects(b, x, now)));
            lemma_project_inv(b, x, now);
            absorb_project(b, x, now, now, t);
            assert(listener_send(b, x, address, now) == Seq::<DispatchV>::empty());
            assert((Seq::<DispatchV>::empty() + sweep_sends(b2, now, t)) =~= sweep_sends(b2, now, t));
        } else {
            let q = p.remove_listener(address);
            assert(b2.objects == b.objects.insert(x, q));
            assert(b2.objects.dom() =~= b.objects.dom());
            echod_kernel::external_proof::lemma_project_idem(b.objects[x], now);
            lemma_project_lists(p, now, p.callbacks, q.listeners);
            assert(q.project(now) == q);
            lemma_inv_pointwise(now, b);
            assert(inv_obj(now, b, x));
            assert(no_dups(b.objects[x].listeners));
            assert(p.listeners == b.objects[x].listeners);
            assert forall|y: Seq<char>, w: Seq<char>| #[trigger] awaits(b2, y, w, now) == awaits(b, y, w, now) && since(b2, y, now) == since(b, y, now) by {}
            assert(c12(b.objects[x], now) == p);
            assert(c12(q, now) == q);
            lemma_record_lists(p, q.callbacks, q.listeners, q.task);
            assert(q.to_record() == p.to_record());
            assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies c4(b2, id, ids, now) == c4(b, id, ids, now) && c12(b2.objects[id], now).to_record() == c12(b.objects[id], now).to_record() by {
                if id != x {
                    assert(c12(b2.objects[id], now) == c12(b.objects[id], now));
                }
                match c12(b.objects[id], now).task {
                    None => {},
                    Some(tk2) => {
                        lemma_resumed_same(b2, b, id, ids, tk2, now);
                    },
                }
            }
            assert(forms_agree(b, b2, ids, now));
            lemma_agree_sends_but_unblock(b, b2, x, address, now, t);
            assert(listener_send(b, x, address, now) == seq![unblock_of(p, address)]);
        }
    } else {
        assert(b2 == b);
        assert(listener_send(b, x, address, now) == Seq::<DispatchV>::empty());
        assert((Seq::<DispatchV>::empty() + sweep_sends(b, now, t)) =~= sweep_sends(b, now, t));
    }
}

/// What one callback step changes of who awaits whom: only that `x` no
/// longer holds `w`; and of what is read: only `x`'s callbacks and `w`'s task.
pub proof fn lemma_callback_reads(b: AState, x: Seq<char>, w: Seq<char>, now: nat)
    requires
        inv(now, b),
        b.objects.contains_key(x),
        b.objects[x].project(now).state != PromiseState::Pending,
        b.objects[x].callbacks.contains(w),
    ensures
        ({
            let b2 = callback_fn(b, x, w, now);
            let p = b.objects[x].project(now);
            &&& w != x
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.objects[x] == p.remove_callback(w)
            &&& b.objects.contains_key(w) ==> b2.objects[w] == (match b.objects[w].project(now).task {
                None => b.objects[w].project(now),
                Some(tk) => b.objects[w].project(now).with_task(resume_step(tk, x, since(b, x, now))),
            })
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && id != x && id != w ==> b2.objects[id] == b.objects[id]
            &&& forall|y: Seq<char>, z: Seq<char>| (z != w || y != x) ==> #[trigger] awaits(b2, y, z, now) == awaits(b, y, z, now)
            &&& !awaits(b2, x, w, now)
            &&& awaits(b, x, w, now)
            &&& forall|y: Seq<char>| #[trigger] b.objects.contains_key(y) ==> since(b2, y, now) == since(b, y, now)
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> c12(b2.objects[id], now).to_record() == c12(b.objects[id], now).to_record()
                && c12(b2.objects[id], now).listeners == c12(b.objects[id], now).listeners
                && c12(b2.objects[id], now).state == c12(b.objects[id], now).state
        }),
{
    let b2 = callback_fn(b, x, w, now);
    lemma_inv_pointwise(now, b);
    assert(inv_obj(now, b, x));
    assert(w != x);
    let p = b.objects[x].project(now);
    echod_kernel::external_proof::lemma_project_idem(b.objects[x], now);
    let p2 = p.remove_callback(w);
    lemma_project_lists(p, now, p2.callbacks, p.listeners);
    assert(p2.project(now) == p2);
    lemma_insert_same(with_objects(b, b.objects.insert(x, p)), x);
    let a2 = with_objects(b, b.objects.insert(x, p2));
    assert(a2.objects.dom() =~= b.objects.dom());
    lemma_without_contains(p.callbacks, w, w);
    assert(b2.objects.contains_key(x) && b2.objects[x] == p2);
    if b.objects.contains_key(w) {
        let q = b.objects[w].project(now);
        echod_kernel::external_proof::lemma_project_idem(b.objects[w], now);
        lemma_insert_same(with_objects(a2, a2.objects.insert(w, q)), w);
        match q.task {
            None => {},
            Some(tk) => {
                let tk2 = resume_step(tk, x, since(b, x, now));
                if tk.state == TaskState::Fulfilled {
                    assert(q.with_task(tk2) == q);
                }
                lemma_projected_obj(q, now);
                if tk.state != TaskState::Fulfilled {
                    lemma_project_pending_task(q, now, tk2);
                }
                assert(b2.objects[w] == q.with_task(tk2));
                assert(b2.objects[w].project(now) == b2.objects[w]);
            },
        }
    }
    assert(b2.objects.dom() =~= b.objects.dom());
    assert forall|y: Seq<char>, z: Seq<char>| (z != w || y != x) implies #[trigger] awaits(b2, y, z, now) == awaits(b, y, z, now) by {
        if y == x {
            lemma_without_contains(p.callbacks, w, z);
        } else if y == w && b.objects.contains_key(w) {
            assert(b2.objects[w].project(now).state == b.objects[w].project(now).state);
            assert(b2.objects[w].callbacks == b.objects[w].callbacks);
        }
    }
    assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies c12(b2.objects[id], now).to_record() == c12(b.objects[id], now).to_record()
        && c12(b2.objects[id], now).listeners == c12(b.objects[id], now).listeners
        && c12(b2.objects[id], now).state == c12(b.objects[id], now).state by {
        if id == x {
            assert(c12(b2.objects[x], now) == p2);
            assert(c12(b.objects[x], now) == p);
            lemma_record_lists(p, p2.callbacks, p2.listeners, p2.task);
        } else if id == w {
            let q = b.objects[w].project(now);
            let c = c12(b.objects[w], now);
            let c2 = c12(b2.objects[w], now);
            assert(c.to_record() == q.to_record()) by {
                lemma_record_lists(q, c.callbacks, c.listeners, c.task);
            }
            assert(c2.to_record() == q.to_record()) by {
                lemma_record_lists(q, c2.callbacks, c2.listeners, c2.task);
            }
        }
    }
}

/// The awaiter's form: resumed by `x` first and then the rest in order is
/// resumed in order, `x` being the first of its settled awaiteds.
pub proof fn lemma_callback_form_w(b: AState, x: Seq<char>, w: Seq<char>, ids: Seq<Seq<char>>, now: nat)
    requires
        inv(now, b),
        b.objects.contains_key(x),
        b.objects[x].project(now).state != PromiseState::Pending,
        b.objects[x].callbacks.contains(w),
        b.objects.contains_key(w),
        ids.no_duplicates(),
        ids.contains(x),
        first_awaited(b, x, w, ids, now) || done(b, w, now),
    ensures
        c4(callback_fn(b, x, w, now), w, ids, now) == c4(b, w, ids, now),
{
    let b2 = callback_fn(b, x, w, now);
    lemma_callback_reads(b, x, w, now);
    let q = b.objects[w].project(now);
    echod_kernel::external_proof::lemma_project_idem(b.objects[w], now);
    lemma_projected_obj(q, now);
    match q.task {
        None => {
            assert(b2.objects[w] == q);
        },
        Some(tk) => {
            let s = since(b, x, now);
            let tk2 = resume_step(tk, x, s);
            assert(b2.objects[w] == q.with_task(tk2));
            if tk.state == TaskState::Fulfilled {
                assert(tk2 == tk);
                assert(c12(b2.objects[w], now) == c12(q, now));
                lemma_resumed_fulfilled(b, w, ids, c12(q, now).task.unwrap(), now);
                lemma_resumed_fulfilled(b2, w, ids, c12(q, now).task.unwrap(), now);
            } else {
                assert(!done(b, w, now));
                assert(first_awaited(b, x, w, ids, now));
                assert(q.state == PromiseState::Pending);
                lemma_project_pending_task(q, now, tk2);
                let c = c12(q, now);
                let c2 = c12(q.with_task(tk2), now);
                if lease_due(q, now) {
                    assert(tk.state == TaskState::Acquired);
                    assert(tk2 == tk.buffer(x));
                    let end = tk.lease_timeout_at.unwrap() as nat;
                    assert(c == q.with_task(tk.release(end)));
                    assert(lease_due(q.with_task(tk2), now));
                    assert(c2 == q.with_task(tk2.release(end)));
                    assert(tk2.release(end) == resume_step(tk.release(end), x, s));
                    lemma_resumed_first(b, b2, w, x, ids, tk.release(end), now);
                } else {
                    assert(c == q);
                    assert(!lease_due(q.with_task(tk2), now));
                    assert(c2 == q.with_task(tk2));
                    lemma_resumed_first(b, b2, w, x, ids, tk, now);
                }
            }
        },
    }
}

/// Resuming one awaiter first is absorbed, when the promise resuming it is the
/// first of its settled awaiteds in the objects' order.
pub proof fn absorb_callback(b: AState, x: Seq<char>, w: Seq<char>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
        b.objects.contains_key(x),
        b.objects[x].project(now).state != PromiseState::Pending,
        b.objects[x].callbacks.contains(w),
        first_awaited(b, x, w, ids_of(b), now) || done(b, w, now),
    ensures
        ({
            let b2 = callback_fn(b, x, w, now);
            &&& inv(now, b2)
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b2, now, t) == sweep_sends(b, now, t)
        }),
{
    let b2 = callback_fn(b, x, w, now);
    lemma_callback_inv(b, x, w, now);
    lemma_callback_reads(b, x, w, now);
    let ids = ids_of(b);
    lemma_ids_cover(b);
    b.objects.dom().lemma_to_seq_no_duplicates();
    let p = b.objects[x].project(now);
    let p2 = p.remove_callback(w);
    // x: its callbacks emptied either way
    assert(c12(b2.objects[x], now) == p2);
    assert(c12(b.objects[x], now) == p);
    match p.task {
        None => {},
        Some(tk) => {
            assert forall|y: Seq<char>| #[trigger] awaits(b2, y, x, now) == awaits(b, y, x, now) by {}
            lemma_resumed_same(b2, b, x, ids, tk, now);
        },
    }
    assert(c4(b2, x, ids, now) == c4(b, x, ids, now));
    if b.objects.contains_key(w) {
        lemma_callback_form_w(b, x, w, ids, now);
    }
    assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies c4(b2, id, ids, now) == c4(b, id, ids, now) by {
        if id != x && id != w {
            assert(b2.objects[id] == b.objects[id]);
            assert forall|y: Seq<char>| #[trigger] awaits(b2, y, id, now) == awaits(b, y, id, now) by {}
            match c12(b.objects[id], now).task {
                None => {},
                Some(tk2) => {
                    lemma_resumed_same(b2, b, id, ids, tk2, now);
                },
            }
        }
    }
    assert(forms_agree(b, b2, ids, now));
    lemma_agree_sends(b, b2, now, t);
}


/// Any one callback step is absorbed, when the awaiter is resumed by the first
/// of its settled awaiteds or is done: a step not due is a projection of `x`.
pub proof fn absorb_callback_any(b: AState, x: Seq<char>, w: Seq<char>, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
        awaits(b, x, w, now) ==> first_awaited(b, x, w, ids_of(b), now) || done(b, w, now),
    ensures
        ({
            let b2 = callback_fn(b, x, w, now);
            &&& inv(now, b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& sweep_fn(b2, now, t).objects == sweep_fn(b, now, t).objects
            &&& sweep_fn(b2, now, t).schedules == sweep_fn(b, now, t).schedules
            &&& sweep_sends(b2, now, t) == sweep_sends(b, now, t)
        }),
{
    let b2 = callback_fn(b, x, w, now);
    lemma_callback_inv(b, x, w, now);
    if b.objects.contains_key(x) {
        let p = b.objects[x].project(now);
        lemma_insert_same(with_objects(b, b.objects.insert(x, p)), x);
        if p.state == PromiseState::Pending || !p.callbacks.contains(w) {
            let b1 = with_objects(b, b.objects.insert(x, p));
            assert(b2 == b1);
            assert(b1 == with_objects(b, promise_timeout_objects(b, x, now)));
            assert(b1.objects.dom() =~= b.objects.dom());
            lemma_project_inv(b, x, now);
            absorb_project(b, x, now, now, t);
            lemma_sweep_canon(b, now, t);
            lemma_sweep_canon(b1, now, t);
        } else {
            assert(awaits(b, x, w, now));
            absorb_callback(b, x, w, now, t);
            lemma_callback_reads(b, x, w, now);
            lemma_sweep_canon(b, now, t);
            lemma_sweep_canon(b2, now, t);
        }
    } else {
        assert(b2 == b);
    }
}

/// A callback step only takes awaits away and leaves who is done as it is.
pub proof fn lemma_callback_mono(b: AState, x: Seq<char>, w: Seq<char>, now: nat)
    requires
        inv(now, b),
    ensures
        ({
            let b2 = callback_fn(b, x, w, now);
            &&& b2.objects.dom() == b.objects.dom()
            &&& forall|y: Seq<char>, z: Seq<char>| #[trigger] awaits(b2, y, z, now) ==> awaits(b, y, z, now)
            &&& forall|z: Seq<char>| #[trigger] done(b2, z, now) == done(b, z, now)
            &&& forall|y: Seq<char>| #[trigger] b.objects.contains_key(y) && y != x && y != w ==> b2.objects[y] == b.objects[y]
            &&& forall|y: Seq<char>| #[trigger] b.objects.contains_key(y) ==> b2.objects[y].project(now).state == b.objects[y].project(now).state
        }),
{
    let b2 = callback_fn(b, x, w, now);
    if b.objects.contains_key(x) {
        let p = b.objects[x].project(now);
        echod_kernel::external_proof::lemma_project_idem(b.objects[x], now);
        lemma_insert_same(with_objects(b, b.objects.insert(x, p)), x);
        if p.state == PromiseState::Pending || !p.callbacks.contains(w) {
            let b1 = with_objects(b, b.objects.insert(x, p));
            assert(b2 == b1);
            assert(b1.objects.dom() =~= b.objects.dom());
            assert forall|y: Seq<char>, z: Seq<char>| #[trigger] awaits(b2, y, z, now) implies awaits(b, y, z, now) by {}
            assert forall|z: Seq<char>| #[trigger] done(b2, z, now) == done(b, z, now) by {}
        } else {
            lemma_callback_reads(b, x, w, now);
            assert forall|y: Seq<char>, z: Seq<char>| #[trigger] awaits(b2, y, z, now) implies awaits(b, y, z, now) by {
                if y == x && z == w {
                    assert(!awaits(b2, x, w, now));
                }
            }
            assert forall|z: Seq<char>| #[trigger] done(b2, z, now) == done(b, z, now) by {
                if z == w && b.objects.contains_key(w) {
                    let q = b.objects[w].project(now);
                    match q.task {
                        None => {},
                        Some(tk) => {
                            let tk2 = resume_step(tk, x, since(b, x, now));
                            assert(b2.objects[w] == q.with_task(tk2));
                            assert(b2.objects[w].project(now) == b2.objects[w]);
                            assert((tk2.state == TaskState::Fulfilled) == (tk.state == TaskState::Fulfilled));
                        },
                    }
                } else if z == x {
                    assert(b2.objects[x].project(now).task == b.objects[x].project(now).task);
                }
            }
        }
    } else {
        assert(b2 == b);
    }
}

} // verus!
