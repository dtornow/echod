//! The sweep's result, object by object: the canonical form. Phases 1 and 2
//! read each object alone; phase 3 resumes each task by the settled promises
//! that hold a callback for it, in the objects' order; phase 4 empties a
//! settled promise's listeners; phase 5 re-arms a due offer. `lemma_sweep_canon`
//! is the sweep computing this form; the absorb lemmas (`absorb.rs`) read it
//! to show the sweep's result does not change when one of its own steps is
//! taken first.

use vstd::prelude::*;

use echod_kernel::external::with_objects;
use echod_kernel::internal::{lease_due, retry_due};
use echod_kernel::object::without;
use echod_kernel::object_proof::lemma_without_contains;
use echod_kernel::properties::{inv, inv_obj, no_dups, opt_or_zero};
use echod_kernel::properties_proof::lemma_inv_pointwise;
use echod_kernel::store::AState;
use echod_kernel::tags::target_of;
use echod_kernel::types::*;
use resonate::twins::DispatchV;

use crate::sweep::*;
use crate::sweep_proof::*;
use crate::translate::message_out;

verus! {

// ------------------------------------------------------------------- the form

/// Phases 1 and 2 on one object: read at `now`, its lease reclaimed if past.
pub open spec fn c12(p: APromise, now: nat) -> APromise {
    let p1 = p.project(now);
    if lease_due(p1, now) {
        p1.with_task(p1.task.unwrap().release(p1.task.unwrap().lease_timeout_at.unwrap() as nat))
    } else {
        p1
    }
}

/// `x`, settled by `now`, holds a callback for `w`.
pub open spec fn awaits(b: AState, x: Seq<char>, w: Seq<char>, now: nat) -> bool {
    b.objects.contains_key(x) && b.objects[x].project(now).state != PromiseState::Pending && b.objects[x].callbacks.contains(w)
}

/// When `x` settled: what its awaiters are woken with.
pub open spec fn since(b: AState, x: Seq<char>, now: nat) -> nat {
    opt_or_zero(b.objects[x].project(now).settled_at)
}

/// One resume of a task: woken if suspended, told if running, left if done.
pub open spec fn resume_step(t: ATask, x: Seq<char>, since: nat) -> ATask {
    if t.state == TaskState::Suspended {
        t.wake(x, since)
    } else if t.state != TaskState::Fulfilled {
        t.buffer(x)
    } else {
        t
    }
}

/// The task of `w` after its settled awaiteds among `ids`, in order, resumed it.
pub open spec fn resumed(b: AState, w: Seq<char>, ids: Seq<Seq<char>>, t: ATask, now: nat) -> ATask
    decreases ids.len(),
{
    if ids.len() == 0 {
        t
    } else {
        let t1 = resumed(b, w, ids.drop_last(), t, now);
        let x = ids.last();
        if awaits(b, x, w, now) { resume_step(t1, x, since(b, x, now)) } else { t1 }
    }
}

/// The object after phases 1 to 4.
pub open spec fn c4(b: AState, id: Seq<char>, ids: Seq<Seq<char>>, now: nat) -> APromise {
    let p = c12(b.objects[id], now);
    let settled = p.state != PromiseState::Pending;
    APromise {
        callbacks: if settled { Seq::empty() } else { p.callbacks },
        listeners: if settled { Seq::empty() } else { p.listeners },
        task: match p.task {
            None => None,
            Some(t) => Some(resumed(b, id, ids, t, now)),
        },
        ..p
    }
}

/// The object after the sweep.
pub open spec fn c5(b: AState, id: Seq<char>, ids: Seq<Seq<char>>, now: nat, t: nat) -> APromise {
    let p = c4(b, id, ids, now);
    if retry_due(p, now) { p.with_task(p.task.unwrap().rearm(now, t)) } else { p }
}

/// The unblock a listener of `p` is sent.
pub open spec fn unblock_of(p: APromise, address: Seq<char>) -> DispatchV {
    message_out(AOutboxEntry { address, message: AMessage::Unblock(p.to_record()) })
}

/// The offer the task at `id` is sent.
pub open spec fn execute_of(id: Seq<char>, p: APromise) -> DispatchV {
    message_out(AOutboxEntry { address: target_of(p.tags), message: AMessage::Execute { task_id: id, version: p.task.unwrap().version } })
}

/// A sum of sends over ids.
pub open spec fn fold_sends(ids: Seq<Seq<char>>, f: spec_fn(Seq<char>) -> Seq<DispatchV>) -> Seq<DispatchV>
    decreases ids.len(),
{
    if ids.len() == 0 { Seq::empty() } else { fold_sends(ids.drop_last(), f) + f(ids.last()) }
}

/// The unblocks the settled `x` sends: one per listener.
pub open spec fn c_unblocks(b: AState, x: Seq<char>, now: nat) -> Seq<DispatchV> {
    if b.objects.contains_key(x) && c12(b.objects[x], now).state != PromiseState::Pending {
        let p = c12(b.objects[x], now);
        p.listeners.map_values(|address: Seq<char>| unblock_of(p, address))
    } else {
        Seq::empty()
    }
}

/// The offer `id` sends, if its task is due after phases 1 to 4.
pub open spec fn c_execute(b: AState, id: Seq<char>, ids: Seq<Seq<char>>, now: nat) -> Seq<DispatchV> {
    if b.objects.contains_key(id) && retry_due(c4(b, id, ids, now), now) {
        seq![execute_of(id, c4(b, id, ids, now))]
    } else {
        Seq::empty()
    }
}

pub open spec fn canon_sends(b: AState, now: nat, t: nat) -> Seq<DispatchV> {
    let ids = ids_of(b);
    fold_sends(ids, |x: Seq<char>| c_unblocks(b, x, now)) + fold_sends(ids, |id: Seq<char>| c_execute(b, id, ids, now))
}

// ----------------------------------------------------------------- utilities

/// Records read none of the lists nor the task.
pub proof fn lemma_record_lists(p: APromise, callbacks: Seq<Seq<char>>, listeners: Seq<Seq<char>>, task: Option<ATask>)
    ensures
        (APromise { callbacks, listeners, task, ..p }).to_record() == p.to_record(),
{
}

pub proof fn lemma_fold_sends_ext(ids: Seq<Seq<char>>, f: spec_fn(Seq<char>) -> Seq<DispatchV>, g: spec_fn(Seq<char>) -> Seq<DispatchV>)
    requires
        forall|x: Seq<char>| ids.contains(x) ==> #[trigger] f(x) == g(x),
    ensures
        fold_sends(ids, f) == fold_sends(ids, g),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_fold_sends_ext(ids.drop_last(), f, g);
        assert(ids.contains(ids.last())) by {
            assert(ids[ids.len() - 1] == ids.last());
        }
        assert forall|x: Seq<char>| ids.drop_last().contains(x) implies ids.contains(x) by {
            let i = choose|i: int| 0 <= i < ids.drop_last().len() && ids.drop_last()[i] == x;
            assert(ids[i] == x);
        }
    }
}

/// A sequence without duplicates: its last element is not among the rest.
pub proof fn lemma_no_dup_last(ids: Seq<Seq<char>>)
    requires
        ids.no_duplicates(),
        ids.len() > 0,
    ensures
        ids.drop_last().no_duplicates(),
        !ids.drop_last().contains(ids.last()),
{
    if ids.drop_last().contains(ids.last()) {
        let i = choose|i: int| 0 <= i < ids.drop_last().len() && ids.drop_last()[i] == ids.last();
        assert(ids[i] == ids[ids.len() - 1]);
        assert(false);
    }
}

/// `s` less every element of `aw`, element by element.
pub open spec fn spent(s: Seq<Seq<char>>, aw: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases aw.len(),
{
    if aw.len() == 0 { s } else { without(spent(s, aw.drop_last()), aw.last()) }
}

pub proof fn lemma_spent_contains(s: Seq<Seq<char>>, aw: Seq<Seq<char>>, c: Seq<char>)
    ensures
        spent(s, aw).contains(c) <==> (s.contains(c) && !aw.contains(c)),
    decreases aw.len(),
{
    if aw.len() > 0 {
        lemma_spent_contains(s, aw.drop_last(), c);
        lemma_without_contains(spent(s, aw.drop_last()), aw.last(), c);
        lemma_contains_split(aw, c);
    }
}

/// Spending a list on itself leaves nothing.
pub proof fn lemma_spent_all(s: Seq<Seq<char>>)
    ensures
        spent(s, s) == Seq::<Seq<char>>::empty(),
{
    if spent(s, s).len() > 0 {
        let c = spent(s, s)[0];
        assert(spent(s, s).contains(c));
        lemma_spent_contains(s, s, c);
        assert(false);
    }
    assert(spent(s, s) =~= Seq::<Seq<char>>::empty());
}

// ------------------------------------------------------------------ phase 1

pub proof fn lemma_deadlines_exact(a: AState, ids: Seq<Seq<char>>, now: nat)
    ensures
        ({
            let b = phase_deadlines(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& b.outbox == a.outbox
            &&& forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> b.objects[id] == (if ids.contains(id) { a.objects[id].project(now) } else { a.objects[id] })
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_deadlines_exact(a, ids.drop_last(), now);
        let a1 = phase_deadlines(a, ids.drop_last(), now);
        let x = ids.last();
        let b = phase_deadlines(a, ids, now);
        if a1.objects.contains_key(x) {
            assert(b.objects == a1.objects.insert(x, a1.objects[x].project(now)));
            assert(b.objects.dom() =~= a1.objects.dom());
            echod_kernel::external_proof::lemma_project_idem(a.objects[x], now);
        }
        assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies b.objects[id] == (if ids.contains(id) { a.objects[id].project(now) } else { a.objects[id] }) by {
            lemma_contains_split(ids, id);
            if id != x {
                assert(b.objects[id] == a1.objects[id]);
            }
        }
    }
}

// ------------------------------------------------------------------ phase 2

/// Phase 2 on one object.
pub open spec fn lease_step(p: APromise, now: nat) -> APromise {
    if lease_due(p, now) { p.with_task(p.task.unwrap().release(p.task.unwrap().lease_timeout_at.unwrap() as nat)) } else { p }
}

pub proof fn lemma_leases_exact(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        ids.no_duplicates(),
    ensures
        ({
            let b = phase_leases(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& b.outbox == a.outbox
            &&& forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> b.objects[id] == (if ids.contains(id) { lease_step(a.objects[id], now) } else { a.objects[id] })
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_no_dup_last(ids);
        lemma_leases_exact(a, ids.drop_last(), now);
        let a1 = phase_leases(a, ids.drop_last(), now);
        let x = ids.last();
        let b = phase_leases(a, ids, now);
        if a1.objects.contains_key(x) {
            assert(a1.objects[x] == a.objects[x]);
            if lease_due(a1.objects[x], now) {
                assert(b.objects == a1.objects.insert(x, lease_step(a.objects[x], now)));
                assert(b.objects.dom() =~= a1.objects.dom());
            } else {
                assert(b == a1);
            }
        } else {
            assert(b == a1);
        }
        assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies b.objects[id] == (if ids.contains(id) { lease_step(a.objects[id], now) } else { a.objects[id] }) by {
            lemma_contains_split(ids, id);
            if id != x {
                assert(b.objects[id] == a1.objects[id]);
            }
        }
    }
}

// ------------------------------------------------------------------ phase 3

/// The settled, projected `x` spends the callbacks `aw`, each held once: each
/// awaiter's task is resumed once, and `x` keeps the callbacks not in `aw`.
pub proof fn lemma_callbacks_of_exact(a: AState, x: Seq<char>, aw: Seq<Seq<char>>, now: nat)
    requires
        projected(a, now),
        a.objects.contains_key(x),
        a.objects[x].state != PromiseState::Pending,
        no_dups(aw),
        !aw.contains(x),
        forall|i: int| 0 <= i < aw.len() ==> a.objects[x].callbacks.contains(#[trigger] aw[i]),
    ensures
        ({
            let b = callbacks_of(a, x, aw, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& b.outbox == a.outbox
            &&& projected(b, now)
            &&& b.objects[x] == APromise { callbacks: spent(a.objects[x].callbacks, aw), ..a.objects[x] }
            &&& forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) && w != x ==> b.objects[w] == (
                if aw.contains(w) {
                    match a.objects[w].task {
                        None => a.objects[w],
                        Some(t) => a.objects[w].with_task(resume_step(t, x, since(a, x, now))),
                    }
                } else {
                    a.objects[w]
                })
        }),
    decreases aw.len(),
{
    if aw.len() > 0 {
        let aw0 = aw.drop_last();
        let y = aw.last();
        assert(no_dups(aw0) && !aw0.contains(y)) by {
            assert forall|i: int, j: int| 0 <= i < aw0.len() && 0 <= j < aw0.len() && aw0[i] == aw0[j] implies i == j by {
                assert(aw[i] == aw[j]);
            }
            if aw0.contains(y) {
                let i = choose|i: int| 0 <= i < aw0.len() && aw0[i] == y;
                assert(aw[i] == aw[aw.len() - 1]);
            }
        }
        assert(!aw0.contains(x)) by {
            if aw0.contains(x) {
                let i = choose|i: int| 0 <= i < aw0.len() && aw0[i] == x;
                assert(aw[i] == x);
            }
        }
        assert(forall|i: int| 0 <= i < aw0.len() ==> a.objects[x].callbacks.contains(#[trigger] aw0[i])) by {
            assert forall|i: int| 0 <= i < aw0.len() implies a.objects[x].callbacks.contains(#[trigger] aw0[i]) by {
                assert(aw0[i] == aw[i]);
            }
        }
        lemma_callbacks_of_exact(a, x, aw0, now);
        let b1 = callbacks_of(a, x, aw0, now);
        let b = callback_fn(b1, x, y, now);
        assert(b == callbacks_of(a, x, aw, now));
        assert(y != x);
        assert(a.objects[x].callbacks.contains(y)) by {
            assert(aw[aw.len() - 1] == y);
        }
        // x in b1: its callbacks still hold y
        let px = b1.objects[x];
        assert(px.callbacks == spent(a.objects[x].callbacks, aw0));
        lemma_spent_contains(a.objects[x].callbacks, aw0, y);
        assert(px.callbacks.contains(y));
        assert(px.state != PromiseState::Pending);
        assert(px.project(now) == px);
        lemma_insert_same(b1, x);
        let a1 = with_objects(b1, b1.objects.insert(x, px));
        assert(a1 == b1);
        let p2 = px.remove_callback(y);
        let a2 = with_objects(a1, a1.objects.insert(x, p2));
        assert(p2 == APromise { callbacks: spent(a.objects[x].callbacks, aw), ..a.objects[x] });
        assert(a2.objects.dom() =~= a.objects.dom());
        lemma_project_lists(px, now, p2.callbacks, px.listeners);
        assert(p2.project(now) == p2);
        assert(projected(a2, now));
        if !a2.objects.contains_key(y) {
            assert(b == a2);
            assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) && w != x implies b.objects[w] == (
                if aw.contains(w) {
                    match a.objects[w].task {
                        None => a.objects[w],
                        Some(t) => a.objects[w].with_task(resume_step(t, x, since(a, x, now))),
                    }
                } else {
                    a.objects[w]
                }) by {
                lemma_contains_split(aw, w);
                assert(w != y);
            }
        } else {
            // y: untouched so far, projected; its task takes one resume
            assert(b1.objects[y] == a.objects[y]);
            let q = a2.objects[y].project(now);
            assert(q == a.objects[y]);
            lemma_insert_same(a2, y);
            let a3 = with_objects(a2, a2.objects.insert(y, q));
            assert(a3 == a2);
            assert(since(a, x, now) == opt_or_zero(px.settled_at));
            match q.task {
                None => {
                    assert(b == a3);
                },
                Some(t) => {
                    let t2 = resume_step(t, x, since(a, x, now));
                    if t.state == TaskState::Suspended {
                        assert(b == with_objects(a3, a3.objects.insert(y, q.with_task(t2))));
                    } else if t.state != TaskState::Fulfilled {
                        assert(b == with_objects(a3, a3.objects.insert(y, q.with_task(t2))));
                    } else {
                        assert(b == a3);
                        assert(q.with_task(t2) == q);
                    }
                    assert(b.objects[y] == q.with_task(t2));
                    assert(b.objects.dom() =~= a.objects.dom());
                    lemma_projected_obj(q, now);
                    if t.state != TaskState::Fulfilled {
                        assert(q.state == PromiseState::Pending);
                        lemma_project_pending_task(q, now, t2);
                    }
                    assert(projected(b, now));
                },
            }
            assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) && w != x implies b.objects[w] == (
                if aw.contains(w) {
                    match a.objects[w].task {
                        None => a.objects[w],
                        Some(t) => a.objects[w].with_task(resume_step(t, x, since(a, x, now))),
                    }
                } else {
                    a.objects[w]
                }) by {
                lemma_contains_split(aw, w);
                if w != y {
                    assert(b.objects[w] == b1.objects[w]);
                }
            }
        }
    }
}

/// Spending callbacks of a pending, projected `x` does nothing.
pub proof fn lemma_callbacks_of_pending(a: AState, x: Seq<char>, aw: Seq<Seq<char>>, now: nat)
    requires
        a.objects.contains_key(x),
        a.objects[x].project(now) == a.objects[x],
        a.objects[x].state == PromiseState::Pending,
    ensures
        callbacks_of(a, x, aw, now) == a,
    decreases aw.len(),
{
    if aw.len() > 0 {
        lemma_callbacks_of_pending(a, x, aw.drop_last(), now);
        lemma_insert_same(a, x);
    }
}

/// Phase 3 on a projected state under the invariant: a settled object's
/// callbacks are spent; every task is resumed by the settled promises among
/// `ids` holding a callback for it, in order.
pub proof fn lemma_callbacks_exact(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        projected(a, now),
        inv(now, a),
        ids.no_duplicates(),
    ensures
        ({
            let b = phase_callbacks(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& b.outbox == a.outbox
            &&& projected(b, now)
            &&& forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> b.objects[id] == APromise {
                callbacks: if ids.contains(id) && a.objects[id].state != PromiseState::Pending { Seq::empty() } else { a.objects[id].callbacks },
                task: match a.objects[id].task {
                    None => None,
                    Some(t) => Some(resumed(a, id, ids, t, now)),
                },
                ..a.objects[id]
            }
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_no_dup_last(ids);
        let ids0 = ids.drop_last();
        lemma_callbacks_exact(a, ids0, now);
        let a1 = phase_callbacks(a, ids0, now);
        let x = ids.last();
        let b = phase_callbacks(a, ids, now);
        if a1.objects.contains_key(x) {
            let px = a.objects[x];
            let l = a1.objects[x].callbacks;
            assert(l == px.callbacks);
            if px.state != PromiseState::Pending {
                lemma_inv_pointwise(now, a);
                assert(inv_obj(now, a, x));
                assert(px.id == x);
                assert(no_dups(l));
                assert(!l.contains(x));
                assert(forall|i: int| 0 <= i < l.len() ==> a1.objects[x].callbacks.contains(#[trigger] l[i]));
                assert(a1.objects[x].state != PromiseState::Pending);
                lemma_callbacks_of_exact(a1, x, l, now);
                assert(b == callbacks_of(a1, x, l, now));
                lemma_spent_all(l);
                assert(since(a1, x, now) == since(a, x, now));
                assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies b.objects[id] == APromise {
                    callbacks: if ids.contains(id) && a.objects[id].state != PromiseState::Pending { Seq::empty() } else { a.objects[id].callbacks },
                    task: match a.objects[id].task {
                        None => None,
                        Some(t) => Some(resumed(a, id, ids, t, now)),
                    },
                    ..a.objects[id]
                } by {
                    lemma_contains_split(ids, id);
                    if id == x {
                        assert(!awaits(a, x, x, now));
                    } else {
                        assert(awaits(a, x, id, now) <==> l.contains(id));
                    }
                }
            } else {
                lemma_callbacks_of_pending(a1, x, l, now);
                assert(b == a1);
                assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies b.objects[id] == APromise {
                    callbacks: if ids.contains(id) && a.objects[id].state != PromiseState::Pending { Seq::empty() } else { a.objects[id].callbacks },
                    task: match a.objects[id].task {
                        None => None,
                        Some(t) => Some(resumed(a, id, ids, t, now)),
                    },
                    ..a.objects[id]
                } by {
                    lemma_contains_split(ids, id);
                    assert(!awaits(a, x, id, now));
                }
            }
        } else {
            assert(b == a1);
            assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies b.objects[id] == APromise {
                callbacks: if ids.contains(id) && a.objects[id].state != PromiseState::Pending { Seq::empty() } else { a.objects[id].callbacks },
                task: match a.objects[id].task {
                    None => None,
                    Some(t) => Some(resumed(a, id, ids, t, now)),
                },
                ..a.objects[id]
            } by {
                lemma_contains_split(ids, id);
                assert(!awaits(a, x, id, now));
            }
        }
    }
}


// ------------------------------------------------------------------ phase 4

/// The settled, projected `x` tells the listeners `l`, each held once: they
/// are sent their unblocks, and `x` keeps the listeners not in `l`.
pub proof fn lemma_listeners_of_exact(a: AState, x: Seq<char>, l: Seq<Seq<char>>, now: nat)
    requires
        projected(a, now),
        a.objects.contains_key(x),
        a.objects[x].state != PromiseState::Pending,
        no_dups(l),
        forall|i: int| 0 <= i < l.len() ==> a.objects[x].listeners.contains(#[trigger] l[i]),
    ensures
        ({
            let b = listeners_of(a, x, l, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& projected(b, now)
            &&& b.objects[x] == APromise { listeners: spent(a.objects[x].listeners, l), ..a.objects[x] }
            &&& forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) && w != x ==> b.objects[w] == a.objects[w]
            &&& listeners_sends(a, x, l, now) == l.map_values(|address: Seq<char>| unblock_of(a.objects[x], address))
        }),
    decreases l.len(),
{
    let f = |address: Seq<char>| unblock_of(a.objects[x], address);
    if l.len() == 0 {
        assert(l.map_values(f) =~= Seq::<DispatchV>::empty());
    } else {
        let l0 = l.drop_last();
        let y = l.last();
        assert(no_dups(l0) && !l0.contains(y)) by {
            assert forall|i: int, j: int| 0 <= i < l0.len() && 0 <= j < l0.len() && l0[i] == l0[j] implies i == j by {
                assert(l[i] == l[j]);
            }
            if l0.contains(y) {
                let i = choose|i: int| 0 <= i < l0.len() && l0[i] == y;
                assert(l[i] == l[l.len() - 1]);
            }
        }
        assert(forall|i: int| 0 <= i < l0.len() ==> a.objects[x].listeners.contains(#[trigger] l0[i])) by {
            assert forall|i: int| 0 <= i < l0.len() implies a.objects[x].listeners.contains(#[trigger] l0[i]) by {
                assert(l0[i] == l[i]);
            }
        }
        lemma_listeners_of_exact(a, x, l0, now);
        let b1 = listeners_of(a, x, l0, now);
        let b = listener_fn(b1, x, y, now);
        assert(b == listeners_of(a, x, l, now));
        assert(a.objects[x].listeners.contains(y)) by {
            assert(l[l.len() - 1] == y);
        }
        let px = b1.objects[x];
        assert(px.listeners == spent(a.objects[x].listeners, l0));
        lemma_spent_contains(a.objects[x].listeners, l0, y);
        assert(px.listeners.contains(y));
        assert(px.project(now) == px);
        lemma_insert_same(b1, x);
        let q = px.remove_listener(y);
        assert(q == APromise { listeners: spent(a.objects[x].listeners, l), ..a.objects[x] });
        assert(b.objects == b1.objects.insert(x, q));
        assert(b.objects.dom() =~= a.objects.dom());
        lemma_project_lists(px, now, px.callbacks, q.listeners);
        assert(q.project(now) == q);
        assert(projected(b, now));
        // the unblock carries x's record
        lemma_record_lists(a.objects[x], q.callbacks, q.listeners, q.task);
        assert(q.to_record() == a.objects[x].to_record());
        assert(listener_send(b1, x, y, now) == seq![unblock_of(a.objects[x], y)]);
        assert(listeners_sends(a, x, l, now) =~= l.map_values(f)) by {
            assert(listeners_sends(a, x, l, now) == l0.map_values(f) + seq![f(y)]);
        }
    }
}

/// Telling listeners of a pending, projected `x` does nothing and sends nothing.
pub proof fn lemma_listeners_of_pending(a: AState, x: Seq<char>, l: Seq<Seq<char>>, now: nat)
    requires
        a.objects.contains_key(x),
        a.objects[x].project(now) == a.objects[x],
        a.objects[x].state == PromiseState::Pending,
    ensures
        listeners_of(a, x, l, now) == a,
        listeners_sends(a, x, l, now) == Seq::<DispatchV>::empty(),
    decreases l.len(),
{
    if l.len() > 0 {
        lemma_listeners_of_pending(a, x, l.drop_last(), now);
        lemma_insert_same(a, x);
        assert(listeners_sends(a, x, l, now) =~= Seq::<DispatchV>::empty());
    }
}

/// What a settled object sends in phase 4, read off the state the phase runs on.
pub open spec fn unblocks_a(a: AState, x: Seq<char>) -> Seq<DispatchV> {
    if a.objects.contains_key(x) && a.objects[x].state != PromiseState::Pending {
        a.objects[x].listeners.map_values(|address: Seq<char>| unblock_of(a.objects[x], address))
    } else {
        Seq::empty()
    }
}

pub proof fn lemma_listeners_exact(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        projected(a, now),
        inv(now, a),
        ids.no_duplicates(),
    ensures
        ({
            let b = phase_listeners(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& projected(b, now)
            &&& forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> b.objects[id] == APromise {
                listeners: if ids.contains(id) && a.objects[id].state != PromiseState::Pending { Seq::empty() } else { a.objects[id].listeners },
                ..a.objects[id]
            }
            &&& phase_listeners_sends(a, ids, now) == fold_sends(ids, |x: Seq<char>| unblocks_a(a, x))
        }),
    decreases ids.len(),
{
    let f = |x: Seq<char>| unblocks_a(a, x);
    if ids.len() > 0 {
        lemma_no_dup_last(ids);
        let ids0 = ids.drop_last();
        lemma_listeners_exact(a, ids0, now);
        let a1 = phase_listeners(a, ids0, now);
        let x = ids.last();
        let b = phase_listeners(a, ids, now);
        if a1.objects.contains_key(x) {
            assert(a1.objects[x] == a.objects[x]);
            let l = a1.objects[x].listeners;
            if a.objects[x].state != PromiseState::Pending {
                lemma_inv_pointwise(now, a);
                assert(inv_obj(now, a, x));
                assert(no_dups(l));
                lemma_listeners_of_exact(a1, x, l, now);
                assert(b == listeners_of(a1, x, l, now));
                lemma_spent_all(l);
                assert(listeners_sends(a1, x, l, now) =~= f(x));
                assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies b.objects[id] == APromise {
                    listeners: if ids.contains(id) && a.objects[id].state != PromiseState::Pending { Seq::empty() } else { a.objects[id].listeners },
                    ..a.objects[id]
                } by {
                    lemma_contains_split(ids, id);
                }
            } else {
                lemma_listeners_of_pending(a1, x, l, now);
                assert(b == a1);
                assert(f(x) == Seq::<DispatchV>::empty());
                assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies b.objects[id] == APromise {
                    listeners: if ids.contains(id) && a.objects[id].state != PromiseState::Pending { Seq::empty() } else { a.objects[id].listeners },
                    ..a.objects[id]
                } by {
                    lemma_contains_split(ids, id);
                }
            }
        } else {
            assert(b == a1);
            assert(f(x) == Seq::<DispatchV>::empty());
            assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies b.objects[id] == APromise {
                listeners: if ids.contains(id) && a.objects[id].state != PromiseState::Pending { Seq::empty() } else { a.objects[id].listeners },
                ..a.objects[id]
            } by {
                lemma_contains_split(ids, id);
            }
        }
        assert(phase_listeners_sends(a, ids, now) == fold_sends(ids, f));
    }
}

// ------------------------------------------------------------------ phase 5

/// Phase 5 on one object.
pub open spec fn retry_step(p: APromise, now: nat, t: nat) -> APromise {
    if retry_due(p, now) { p.with_task(p.task.unwrap().rearm(now, t)) } else { p }
}

/// What an object sends in phase 5, read off the state the phase runs on.
pub open spec fn execute_a(a: AState, id: Seq<char>, now: nat) -> Seq<DispatchV> {
    if a.objects.contains_key(id) && retry_due(a.objects[id], now) { seq![execute_of(id, a.objects[id])] } else { Seq::empty() }
}

pub proof fn lemma_retries_exact(a: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    requires
        ids.no_duplicates(),
    ensures
        ({
            let b = phase_retries(a, ids, now, t);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> b.objects[id] == (if ids.contains(id) { retry_step(a.objects[id], now, t) } else { a.objects[id] })
            &&& phase_retries_sends(a, ids, now, t) == fold_sends(ids, |id: Seq<char>| execute_a(a, id, now))
        }),
    decreases ids.len(),
{
    let f = |id: Seq<char>| execute_a(a, id, now);
    if ids.len() > 0 {
        lemma_no_dup_last(ids);
        let ids0 = ids.drop_last();
        lemma_retries_exact(a, ids0, now, t);
        let a1 = phase_retries(a, ids0, now, t);
        let x = ids.last();
        let b = phase_retries(a, ids, now, t);
        assert(b == retry_fn(a1, x, now, t));
        if a1.objects.contains_key(x) {
            assert(a1.objects[x] == a.objects[x]);
            if retry_due(a1.objects[x], now) {
                assert(b.objects == a1.objects.insert(x, retry_step(a.objects[x], now, t)));
                assert(b.objects.dom() =~= a1.objects.dom());
            } else {
                assert(b == a1);
            }
        } else {
            assert(b == a1);
        }
        assert(retry_send(a1, x, now, t) == f(x));
        assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies b.objects[id] == (if ids.contains(id) { retry_step(a.objects[id], now, t) } else { a.objects[id] }) by {
            lemma_contains_split(ids, id);
            if id != x {
                assert(b.objects[id] == a1.objects[id]);
            }
        }
    }
}

// ----------------------------------------------------------------- assembly

/// The resumes read only who awaits whom and when it settled.
pub proof fn lemma_resumed_same(a: AState, b: AState, w: Seq<char>, ids: Seq<Seq<char>>, t: ATask, now: nat)
    requires
        forall|x: Seq<char>| #[trigger] awaits(a, x, w, now) == awaits(b, x, w, now),
        forall|x: Seq<char>| #[trigger] awaits(a, x, w, now) ==> since(a, x, now) == since(b, x, now),
    ensures
        resumed(a, w, ids, t, now) == resumed(b, w, ids, t, now),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_resumed_same(a, b, w, ids.drop_last(), t, now);
    }
}

/// The sweep computes the canonical form, object by object, and sends what
/// the form says.
pub proof fn lemma_sweep_canon(b: AState, now: nat, t: nat)
    requires
        inv(now, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
    ensures
        ({
            let s = sweep_fn(b, now, t);
            let ids = ids_of(b);
            &&& s.objects.dom() == b.objects.dom()
            &&& s.schedules == b.schedules
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> s.objects[id] == c5(b, id, ids, now, t)
            &&& sweep_sends(b, now, t) == canon_sends(b, now, t)
        }),
{
    let ids = ids_of(b);
    lemma_ids_cover(b);
    b.objects.dom().lemma_to_seq_no_duplicates();
    assert(ids.no_duplicates());
    // phase 1
    lemma_deadlines_exact(b, ids, now);
    lemma_deadlines_phase(b, ids, now);
    lemma_deadlines_inv(b, ids, now);
    let a1 = phase_deadlines(b, ids, now);
    assert(projected(a1, now));
    assert(forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> a1.objects[id] == b.objects[id].project(now));
    // phase 2
    lemma_leases_exact(a1, ids, now);
    lemma_leases_phase(a1, ids, now);
    lemma_leases_inv(a1, ids, now);
    let a2 = phase_leases(a1, ids, now);
    assert(projected(a2, now));
    assert(forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> a2.objects[id] == c12(b.objects[id], now));
    // phase 3
    lemma_callbacks_exact(a2, ids, now);
    lemma_callbacks_inv(a2, ids, now);
    let a3 = phase_callbacks(a2, ids, now);
    assert forall|x: Seq<char>, w: Seq<char>| #[trigger] awaits(a2, x, w, now) == awaits(b, x, w, now) && (awaits(a2, x, w, now) ==> since(a2, x, now) == since(b, x, now)) by {
        if b.objects.contains_key(x) {
            assert(a2.objects[x] == c12(b.objects[x], now));
            assert(a2.objects[x].project(now) == a2.objects[x]);
        }
    }
    assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies a3.objects[id] == APromise {
        callbacks: if c12(b.objects[id], now).state != PromiseState::Pending { Seq::empty() } else { c12(b.objects[id], now).callbacks },
        task: match c12(b.objects[id], now).task {
            None => None,
            Some(tk) => Some(resumed(b, id, ids, tk, now)),
        },
        ..c12(b.objects[id], now)
    } by {
        match c12(b.objects[id], now).task {
            None => {},
            Some(tk) => {
                lemma_resumed_same(a2, b, id, ids, tk, now);
            },
        }
    }
    // phase 4
    lemma_listeners_exact(a3, ids, now);
    lemma_listeners_inv(a3, ids, now);
    let a4 = phase_listeners(a3, ids, now);
    assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies a4.objects[id] == c4(b, id, ids, now) by {
        assert(a3.objects[id].state == c12(b.objects[id], now).state);
    }
    assert forall|x: Seq<char>| ids.contains(x) implies #[trigger] unblocks_a(a3, x) == c_unblocks(b, x, now) by {
        if b.objects.contains_key(x) {
            let p = c12(b.objects[x], now);
            assert(a3.objects[x].state == p.state && a3.objects[x].listeners == p.listeners);
            if p.state != PromiseState::Pending {
                lemma_record_lists(p, a3.objects[x].callbacks, a3.objects[x].listeners, a3.objects[x].task);
                assert(a3.objects[x].to_record() == p.to_record());
                assert(unblocks_a(a3, x) =~= c_unblocks(b, x, now));
            }
        }
    }
    lemma_fold_sends_ext(ids, |x: Seq<char>| unblocks_a(a3, x), |x: Seq<char>| c_unblocks(b, x, now));
    // phase 5
    lemma_retries_exact(a4, ids, now, t);
    let a5 = phase_retries(a4, ids, now, t);
    assert(a5 == sweep_fn(b, now, t));
    assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies a5.objects[id] == c5(b, id, ids, now, t) by {
        assert(a5.objects[id] == retry_step(a4.objects[id], now, t));
    }
    assert forall|id: Seq<char>| ids.contains(id) implies #[trigger] execute_a(a4, id, now) == c_execute(b, id, ids, now) by {
        if b.objects.contains_key(id) {
            assert(a4.objects[id] == c4(b, id, ids, now));
        }
    }
    lemma_fold_sends_ext(ids, |id: Seq<char>| execute_a(a4, id, now), |id: Seq<char>| c_execute(b, id, ids, now));
    assert(sweep_sends(b, now, t) == phase_listeners_sends(a3, ids, now) + phase_retries_sends(a4, ids, now, t));
}

} // verus!
