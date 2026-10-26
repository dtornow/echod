//! What the sweep leaves alone: every object's identity, tags and task
//! version. The relation reads two facts off these — no object carries the
//! `resonate:scope` tag the model has no word for, and no version exceeds the
//! wire's `u32` — and both survive a sweep because the sweep never writes
//! those fields.

use vstd::prelude::*;

use echod_kernel::external::with_objects;
use echod_kernel::internal::{lease_timeout_objects, promise_timeout_objects, retry_timeout_objects};
use echod_kernel::store::AState;
use echod_kernel::tags::tags_get;
use echod_kernel::types::*;

use crate::sweep::*;

verus! {

/// Same object: same id, same tags, a task or none, and the same version.
pub open spec fn same_shell(p: APromise, q: APromise) -> bool {
    &&& q.id == p.id
    &&& q.tags == p.tags
    &&& (q.task is Some) == (p.task is Some)
    &&& (p.task is Some ==> q.task.unwrap().version == p.task.unwrap().version)
}

/// Same objects, each with its shell.
pub open spec fn shell_kept(a: AState, b: AState) -> bool {
    &&& b.objects.dom() == a.objects.dom()
    &&& forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> same_shell(a.objects[id], b.objects[id])
}

/// No object is scoped global: the one tag that makes the kernel's awaitable
/// differ from the model's `external`. The wire never writes it.
pub open spec fn no_scope(a: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> tags_get(a.objects[id].tags, "resonate:scope"@) != Some("global"@)
}

/// Every version fits the wire's `u32`: the kernel refuses an acquire at
/// `MAX_VERSION`.
pub open spec fn versions_bounded(a: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> match a.objects[id].task {
        Some(t) => t.version <= MAX_VERSION,
        None => true,
    }
}

pub proof fn lemma_shell_refl(a: AState)
    ensures
        shell_kept(a, a),
{
}

pub proof fn lemma_shell_trans(a: AState, b: AState, c: AState)
    requires
        shell_kept(a, b),
        shell_kept(b, c),
    ensures
        shell_kept(a, c),
{
    assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies same_shell(a.objects[id], c.objects[id]) by {
        assert(b.objects.contains_key(id));
    }
}

/// What the shell carries across.
pub proof fn lemma_shell_keeps(a: AState, b: AState)
    requires
        shell_kept(a, b),
    ensures
        no_scope(a) ==> no_scope(b),
        versions_bounded(a) ==> versions_bounded(b),
{
    if no_scope(a) {
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies tags_get(b.objects[id].tags, "resonate:scope"@) != Some("global"@) by {
            assert(a.objects.contains_key(id));
        }
    }
    if versions_bounded(a) {
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies match b.objects[id].task {
            Some(t) => t.version <= MAX_VERSION,
            None => true,
        } by {
            assert(a.objects.contains_key(id));
        }
    }
}

/// Writing one object back with its shell keeps every shell.
pub proof fn lemma_insert_shell(a: AState, x: Seq<char>, q: APromise)
    requires
        a.objects.contains_key(x),
        same_shell(a.objects[x], q),
    ensures
        shell_kept(a, with_objects(a, a.objects.insert(x, q))),
{
    let b = with_objects(a, a.objects.insert(x, q));
    assert(b.objects.dom() =~= a.objects.dom());
}

/// A projection keeps the shell: it settles the promise and fulfills the task.
pub proof fn lemma_project_same_shell(p: APromise, now: nat)
    ensures
        same_shell(p, p.project(now)),
{
}

// ------------------------------------------------------------------ the steps

pub proof fn lemma_project_shell(a: AState, x: Seq<char>, now: nat)
    ensures
        shell_kept(a, with_objects(a, promise_timeout_objects(a, x, now))),
{
    if a.objects.contains_key(x) {
        lemma_project_same_shell(a.objects[x], now);
        lemma_insert_shell(a, x, a.objects[x].project(now));
    } else {
        assert(with_objects(a, promise_timeout_objects(a, x, now)) == a);
    }
}

pub proof fn lemma_lease_shell(a: AState, x: Seq<char>, now: nat)
    ensures
        shell_kept(a, with_objects(a, lease_timeout_objects(a, x, now))),
{
    if a.objects.contains_key(x) && echod_kernel::internal::lease_due(a.objects[x], now) {
        let p = a.objects[x];
        lemma_insert_shell(a, x, p.with_task(p.task.unwrap().release(p.task.unwrap().lease_timeout_at.unwrap() as nat)));
    } else {
        assert(with_objects(a, lease_timeout_objects(a, x, now)) == a);
    }
}

pub proof fn lemma_callback_shell(a: AState, x: Seq<char>, y: Seq<char>, now: nat)
    ensures
        shell_kept(a, callback_fn(a, x, y, now)),
{
    if !a.objects.contains_key(x) {
    } else {
        let p = a.objects[x].project(now);
        let a1 = with_objects(a, a.objects.insert(x, p));
        lemma_project_same_shell(a.objects[x], now);
        lemma_insert_shell(a, x, p);
        if p.state == PromiseState::Pending || !p.callbacks.contains(y) {
        } else {
            let a2 = with_objects(a1, a1.objects.insert(x, p.remove_callback(y)));
            lemma_insert_shell(a1, x, p.remove_callback(y));
            lemma_shell_trans(a, a1, a2);
            if !a2.objects.contains_key(y) {
            } else {
                let q = a2.objects[y].project(now);
                let a3 = with_objects(a2, a2.objects.insert(y, q));
                lemma_project_same_shell(a2.objects[y], now);
                lemma_insert_shell(a2, y, q);
                lemma_shell_trans(a, a2, a3);
                match q.task {
                    None => {},
                    Some(t) => {
                        if t.state == TaskState::Suspended {
                            lemma_insert_shell(a3, y, q.with_task(t.wake(x, echod_kernel::properties::opt_or_zero(p.settled_at))));
                            lemma_shell_trans(a, a3, callback_fn(a, x, y, now));
                        } else if t.state != TaskState::Fulfilled {
                            lemma_insert_shell(a3, y, q.with_task(t.buffer(x)));
                            lemma_shell_trans(a, a3, callback_fn(a, x, y, now));
                        }
                    },
                }
            }
        }
    }
}

pub proof fn lemma_listener_shell(a: AState, x: Seq<char>, address: Seq<char>, now: nat)
    ensures
        shell_kept(a, listener_fn(a, x, address, now)),
{
    if a.objects.contains_key(x) {
        let p = a.objects[x].project(now);
        let a1 = with_objects(a, a.objects.insert(x, p));
        lemma_project_same_shell(a.objects[x], now);
        lemma_insert_shell(a, x, p);
        if p.state == PromiseState::Pending || !p.listeners.contains(address) {
        } else {
            let b = listener_fn(a, x, address, now);
            assert(b.objects == a1.objects.insert(x, p.remove_listener(address)));
            lemma_insert_shell(a1, x, p.remove_listener(address));
            assert(shell_kept(a1, b)) by {
                assert(b.objects.dom() =~= a1.objects.dom());
            }
            lemma_shell_trans(a, a1, b);
        }
    }
}

pub proof fn lemma_retry_shell(a: AState, x: Seq<char>, now: nat, t: nat)
    ensures
        shell_kept(a, retry_fn(a, x, now, t)),
{
    if a.objects.contains_key(x) && echod_kernel::internal::retry_due(a.objects[x], now) {
        let p = a.objects[x];
        let b = retry_fn(a, x, now, t);
        assert(b.objects == a.objects.insert(x, p.with_task(p.task.unwrap().rearm(now, t))));
        lemma_insert_shell(a, x, p.with_task(p.task.unwrap().rearm(now, t)));
        assert(b.objects.dom() =~= a.objects.dom());
    }
}

// ----------------------------------------------------------------- the folds

pub proof fn lemma_deadlines_shell(a: AState, ids: Seq<Seq<char>>, now: nat)
    ensures
        shell_kept(a, phase_deadlines(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_deadlines_shell(a, ids.drop_last(), now);
        lemma_project_shell(phase_deadlines(a, ids.drop_last(), now), ids.last(), now);
        lemma_shell_trans(a, phase_deadlines(a, ids.drop_last(), now), phase_deadlines(a, ids, now));
    }
}

pub proof fn lemma_leases_shell(a: AState, ids: Seq<Seq<char>>, now: nat)
    ensures
        shell_kept(a, phase_leases(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_leases_shell(a, ids.drop_last(), now);
        lemma_lease_shell(phase_leases(a, ids.drop_last(), now), ids.last(), now);
        lemma_shell_trans(a, phase_leases(a, ids.drop_last(), now), phase_leases(a, ids, now));
    }
}

pub proof fn lemma_callbacks_of_shell(a: AState, x: Seq<char>, aw: Seq<Seq<char>>, now: nat)
    ensures
        shell_kept(a, callbacks_of(a, x, aw, now)),
    decreases aw.len(),
{
    if aw.len() > 0 {
        lemma_callbacks_of_shell(a, x, aw.drop_last(), now);
        lemma_callback_shell(callbacks_of(a, x, aw.drop_last(), now), x, aw.last(), now);
        lemma_shell_trans(a, callbacks_of(a, x, aw.drop_last(), now), callbacks_of(a, x, aw, now));
    }
}

pub proof fn lemma_phase_callbacks_shell(a: AState, ids: Seq<Seq<char>>, now: nat)
    ensures
        shell_kept(a, phase_callbacks(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_phase_callbacks_shell(a, ids.drop_last(), now);
        let a1 = phase_callbacks(a, ids.drop_last(), now);
        let x = ids.last();
        if a1.objects.contains_key(x) {
            lemma_callbacks_of_shell(a1, x, a1.objects[x].callbacks, now);
            lemma_shell_trans(a, a1, phase_callbacks(a, ids, now));
        }
    }
}

pub proof fn lemma_listeners_of_shell(a: AState, x: Seq<char>, l: Seq<Seq<char>>, now: nat)
    ensures
        shell_kept(a, listeners_of(a, x, l, now)),
    decreases l.len(),
{
    if l.len() > 0 {
        lemma_listeners_of_shell(a, x, l.drop_last(), now);
        lemma_listener_shell(listeners_of(a, x, l.drop_last(), now), x, l.last(), now);
        lemma_shell_trans(a, listeners_of(a, x, l.drop_last(), now), listeners_of(a, x, l, now));
    }
}

pub proof fn lemma_phase_listeners_shell(a: AState, ids: Seq<Seq<char>>, now: nat)
    ensures
        shell_kept(a, phase_listeners(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_phase_listeners_shell(a, ids.drop_last(), now);
        let a1 = phase_listeners(a, ids.drop_last(), now);
        let x = ids.last();
        if a1.objects.contains_key(x) {
            lemma_listeners_of_shell(a1, x, a1.objects[x].listeners, now);
            lemma_shell_trans(a, a1, phase_listeners(a, ids, now));
        }
    }
}

pub proof fn lemma_retries_shell(a: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    ensures
        shell_kept(a, phase_retries(a, ids, now, t)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_retries_shell(a, ids.drop_last(), now, t);
        lemma_retry_shell(phase_retries(a, ids.drop_last(), now, t), ids.last(), now, t);
        lemma_shell_trans(a, phase_retries(a, ids.drop_last(), now, t), phase_retries(a, ids, now, t));
    }
}

/// The sweep keeps every shell.
pub proof fn lemma_sweep_shell(a: AState, now: nat, t: nat)
    ensures
        shell_kept(a, sweep_fn(a, now, t)),
{
    let ids = ids_of(a);
    let a1 = phase_deadlines(a, ids, now);
    let a2 = phase_leases(a1, ids, now);
    let a3 = phase_callbacks(a2, ids, now);
    let a4 = phase_listeners(a3, ids, now);
    lemma_deadlines_shell(a, ids, now);
    lemma_leases_shell(a1, ids, now);
    lemma_shell_trans(a, a1, a2);
    lemma_phase_callbacks_shell(a2, ids, now);
    lemma_shell_trans(a, a2, a3);
    lemma_phase_listeners_shell(a3, ids, now);
    lemma_shell_trans(a, a3, a4);
    lemma_retries_shell(a4, ids, now, t);
    lemma_shell_trans(a, a4, sweep_fn(a, now, t));
}

} // verus!
