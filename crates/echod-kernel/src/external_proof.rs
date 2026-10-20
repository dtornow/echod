//! The proofs of the request handlers: one `lemma_*_legal` per handler, the
//! projection lemmas they share, and the frame lemmas for the handlers that
//! touch several objects. Each lemma takes the abstract states before and
//! after and concludes `post`. Nothing here is executed.

use vstd::prelude::*;

use crate::external::*;
use crate::object::*;
use crate::properties::*;
use crate::store::*;
use crate::tags::OType;
use crate::types::*;

verus! {

// ---------------------------------------------------------------------------
// Proofs
// ---------------------------------------------------------------------------

/// Projecting any set of objects at `now` is a legal step that keeps the invariant.
pub proof fn lemma_project_many(now: nat, a: AState, b: AState, ids: spec_fn(Seq<char>) -> bool)
    requires
        inv(now, a),
        forall|x: Seq<char>| #[trigger] ids(x) ==>
            a.objects.contains_key(x) && b.objects.contains_key(x) && b.objects[x] == a.objects[x].project(now),
        forall|x: Seq<char>| !ids(x) ==>
            (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
            && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].callbacks == a.objects[w].callbacks
        && b.objects[w].tags == a.objects[w].tags by {
        if ids(w) {
        } else {
            assert(b.objects.contains_key(w));
        }
    }
    assert forall|x: Seq<char>| #[trigger] ids(x) && b.objects.contains_key(x) implies inv_obj(now, b, x) by {
        lemma_project_inv_obj(now, a, b, x);
    }
    assert forall|x: Seq<char>| #[trigger] ids(x) implies trans_obj(now, a, b, x) by {
        lemma_project_trans_obj(now, a, b, x);
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, ids, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// A promise born at `t <= now` on a fresh id obeys the catalogue at its id,
/// provided it is either dead at birth or still live at `now`.
pub proof fn lemma_born_obj(now: nat, t: nat, a: AState, b: AState, req: APromiseCreateReq)
    requires
        inv(now, a),
        !a.objects.contains_key(req.id),
        !crate::tags::timer_targeted(req.tags),
        req.timeout_at <= 2 * (MAX_TIME as nat),
        t <= now,
        req.timeout_at <= t || req.timeout_at > now,
        b.objects.contains_key(req.id),
        b.objects[req.id] == spec_create(req, t),
    ensures
        inv_obj(now, b, req.id),
        trans_obj(now, a, b, req.id),
{
    lemma_inv_pointwise(now, a);
    let id = req.id;
    let q = spec_create(req, t);
    assert(q.callbacks.len() == 0);
    assert(!q.callbacks.contains(id));
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
}

/// `promise.create` on a fresh id.
pub proof fn lemma_create_legal(now: nat, a: AState, b: AState, req: APromiseCreateReq)
    requires
        inv(now, a),
        !a.objects.contains_key(req.id),
        !crate::tags::timer_targeted(req.tags),
        req.timeout_at <= MAX_TIME as nat,
        b.objects == a.objects.insert(req.id, spec_create(req, now)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    let id = req.id;
    lemma_born_obj(now, now, a, b, req);
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `promise.settle` on a pending promise.
pub proof fn lemma_settle_legal(now: nat, a: AState, b: AState, id: Seq<char>, state: PromiseState, value: AValue)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].project(now).state == PromiseState::Pending,
        state.spec_settable(),
        b.objects == a.objects.insert(id, a.objects[id].project(now).settle(state, value, now)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    assert(p.state == PromiseState::Pending && p.timeout_at > now);
    assert(p.project(now) == p);
    let q = p.settle(state, value, now);
    assert(b.objects[id] == q);
    assert(q.callbacks == p.callbacks && q.listeners == p.listeners && q.tags == p.tags);
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
    }
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// A rung in `a` is a rung in `b` when no registered callback was lost.
pub proof fn lemma_rung_transfer(a: AState, b: AState, id: Seq<char>)
    requires
        some_callbacks_contain(a, id),
        forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
            && #[trigger] a.objects[w].callbacks.contains(z)
            ==> b.objects.contains_key(w) && b.objects[w].callbacks.contains(z),
    ensures
        some_callbacks_contain(b, id),
{
    let w = choose|w: Seq<char>| #[trigger] a.objects.contains_key(w) && a.objects[w].callbacks.contains(id);
    assert(b.objects.contains_key(w) && b.objects[w].callbacks.contains(id));
}

/// `promise.callback`: `awaited` and `awaiter` both pending, both read at `now`.
pub proof fn lemma_add_callback_legal(now: nat, a: AState, b: AState, awaited: Seq<char>, awaiter: Seq<char>)
    requires
        inv(now, a),
        awaited != awaiter,
        crate::ident::same_origin_spec(awaited, awaiter),
        a.objects.contains_key(awaited),
        a.objects.contains_key(awaiter),
        a.objects[awaited].project(now).state == PromiseState::Pending,
        a.objects[awaiter].project(now).state == PromiseState::Pending,
        a.objects[awaiter].otype() == OType::Runnable,
        a.objects[awaited].otype().awaitable(),
        b.objects == a.objects.insert(awaited, a.objects[awaited].add_callback(awaiter)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, awaited));
    assert(inv_obj(now, a, awaiter));
    let p = a.objects[awaited];
    let q = p.add_callback(awaiter);
    assert(b.objects[awaited] == q);
    assert(p.state == PromiseState::Pending);
    assert(b.objects[awaiter] == a.objects[awaiter]);
    // the new callback list
    if p.callbacks.contains(awaiter) {
        assert(q == p);
    } else {
        assert(q.callbacks == p.callbacks.push(awaiter));
        assert(q.callbacks[q.callbacks.len() - 1] == awaiter);
        assert(no_dups(q.callbacks)) by {
            assert forall|i: int, j: int| 0 <= i < q.callbacks.len() && 0 <= j < q.callbacks.len()
                && q.callbacks[i] == q.callbacks[j] implies i == j by {
                if i < p.callbacks.len() && j < p.callbacks.len() {
                } else if i < p.callbacks.len() {
                    assert(p.callbacks[i] == awaiter);
                } else if j < p.callbacks.len() {
                    assert(p.callbacks[j] == awaiter);
                }
            }
        }
    }
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {
        if !p.callbacks.contains(awaiter) {
            assert(q.callbacks[i] == p.callbacks[i]);
        }
    }
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable
        && crate::ident::same_origin_spec(q.callbacks[i], awaited) && q.callbacks[i] != awaited by {
        if i < p.callbacks.len() {
            assert(q.callbacks[i] == p.callbacks[i]);
            assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        } else {
            assert(q.callbacks[i] == awaiter);
        }
    }
    assert(!q.callbacks.contains(awaited));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {
        if w == awaited {
            let i = choose|i: int| 0 <= i < p.callbacks.len() && p.callbacks[i] == z;
            assert(q.callbacks.contains(p.callbacks[i]));
        }
    }
    match q.task {
        Some(t) => {
            if t.state == TaskState::Suspended && q.project_promise(now).state == PromiseState::Pending {
                assert(some_callbacks_contain(a, awaited));
                lemma_rung_transfer(a, b, awaited);
            }
        }
        None => {}
    }
    assert(inv_obj(now, b, awaited));
    assert(trans_obj(now, a, b, awaited));
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == awaited, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `promise.listener`: `awaited` pending, read at `now`.
pub proof fn lemma_add_listener_legal(now: nat, a: AState, b: AState, awaited: Seq<char>, address: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(awaited),
        a.objects[awaited].project(now).state == PromiseState::Pending,
        a.objects[awaited].otype().awaitable(),
        b.objects == a.objects.insert(awaited, a.objects[awaited].add_listener(address)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, awaited));
    let p = a.objects[awaited];
    let q = p.add_listener(address);
    assert(b.objects[awaited] == q);
    assert(p.state == PromiseState::Pending);
    if p.listeners.contains(address) {
        assert(q == p);
    } else {
        assert(q.listeners == p.listeners.push(address));
        assert(no_dups(q.listeners)) by {
            assert forall|i: int, j: int| 0 <= i < q.listeners.len() && 0 <= j < q.listeners.len()
                && q.listeners[i] == q.listeners[j] implies i == j by {
                if i < p.listeners.len() && j < p.listeners.len() {
                } else if i < p.listeners.len() {
                    assert(p.listeners[i] == address);
                } else if j < p.listeners.len() {
                    assert(p.listeners[j] == address);
                }
            }
        }
    }
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {
        if !p.listeners.contains(address) {
            assert(q.listeners[i] == p.listeners[i]);
        }
    }
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    match q.task {
        Some(t) => {
            if t.state == TaskState::Suspended && q.project_promise(now).state == PromiseState::Pending {
                assert(some_callbacks_contain(a, awaited));
                lemma_rung_transfer(a, b, awaited);
            }
        }
        None => {}
    }
    assert(inv_obj(now, b, awaited));
    assert(trans_obj(now, a, b, awaited));
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == awaited, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// Projecting one object at `now` is a legal step that keeps the invariant.
pub proof fn lemma_project_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects == a.objects.insert(id, a.objects[id].project(now)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    let p = a.objects[id];
    let q = p.project(now);
    assert(b.objects[id] == q);
    assert(inv_obj(now, b, id)) by {
        lemma_project_inv_obj(now, a, b, id);
    }
    assert(trans_obj(now, a, b, id)) by {
        lemma_project_trans_obj(now, a, b, id);
    }
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// The projected object obeys every `.state` entry.
pub proof fn lemma_project_inv_obj(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].project(now),
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].callbacks == a.objects[w].callbacks
            && b.objects[w].tags == a.objects[w].tags,
    ensures
        inv_obj(now, b, id),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let q = b.objects[id];
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
    }
    match q.task {
        Some(u) => {
            if u.state == TaskState::Suspended && q.project_promise(now).state == PromiseState::Pending {
                assert(p.project_promise(now).state == PromiseState::Pending);
                assert(some_callbacks_contain(a, id));
                let w = choose|w: Seq<char>| #[trigger] a.objects.contains_key(w) && a.objects[w].callbacks.contains(id);
                assert(b.objects[w].callbacks.contains(id));
                assert(some_callbacks_contain(b, id));
            }
        }
        None => {}
    }
}

/// Projection is a legal transition at its own id.
pub proof fn lemma_project_trans_obj(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].project(now),
    ensures
        trans_obj(now, a, b, id),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let q = b.objects[id];
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    match p.task {
        Some(t) => {
            assert forall|i: int| 0 <= i < t.resumes.len() implies t.resumes.contains(#[trigger] t.resumes[i]) by {}
        }
        None => {}
    }
}

/// A schedule row written or removed, objects and outbox untouched.
pub proof fn lemma_schedule_create_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        !a.schedules.contains_key(id),
        b.schedules.contains_key(id),
        b.schedules[id].id == id,
        b.schedules[id].created_at == now,
        b.schedules[id].last_run_at is None,
        b.schedules[id].next_run_at >= now,
        !crate::tags::timer_targeted(b.schedules[id].promise_tags),
        b.schedules[id].promise_timeout <= MAX_TIME as nat,
        forall|x: Seq<char>| x != id ==>
            (a.schedules.contains_key(x) <==> #[trigger] b.schedules.contains_key(x))
            && (a.schedules.contains_key(x) ==> a.schedules[x] == b.schedules[x]),
        b.objects == a.objects,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_sched(now, b, id));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| false, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| x == id);
}

pub proof fn lemma_schedule_delete_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        !b.schedules.contains_key(id),
        forall|x: Seq<char>| x != id ==>
            (a.schedules.contains_key(x) <==> #[trigger] b.schedules.contains_key(x))
            && (a.schedules.contains_key(x) ==> a.schedules[x] == b.schedules[x]),
        b.objects == a.objects,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| false, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| x == id);
}

// ---------------------------------------------------------------------------
// Proofs
// ---------------------------------------------------------------------------

/// A projected object whose task is not fulfilled is the object itself: its
/// promise is pending and ahead of its deadline.
pub proof fn lemma_projected_task_identity(now: nat, a: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].project(now).task.unwrap().state != TaskState::Fulfilled,
    ensures
        a.objects[id].project(now) == a.objects[id],
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        a.objects[id].project(now).task.unwrap() == a.objects[id].task.unwrap(),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    if p.state != PromiseState::Pending {
        assert(consistent_settled_promise_has_fulfilled_task_at(now, p));
        assert(false);
    }
    if p.timeout_at <= now {
        assert(false);
    }
}

/// The common part of every single-task-edit step: the object keeps its
/// callbacks, listeners, tags and promise, so the pointers into and out of it
/// are what they were.
pub proof fn lemma_task_edit_frame(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        b.objects[id].callbacks == a.objects[id].callbacks,
        b.objects[id].listeners == a.objects[id].listeners,
        b.objects[id].tags == a.objects[id].tags,
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
            && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z),
    ensures
        forall|i: int| 0 <= i < a.objects[id].callbacks.len() ==>
            b.objects[id].callbacks.contains(#[trigger] a.objects[id].callbacks[i]),
        forall|i: int| 0 <= i < a.objects[id].listeners.len() ==>
            b.objects[id].listeners.contains(#[trigger] a.objects[id].listeners[i]),
        consistent_callback_awaiter_is_targeted_at(now, b, b.objects[id]),
        forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
            && #[trigger] a.objects[w].callbacks.contains(z)
            ==> b.objects.contains_key(w) && b.objects[w].callbacks.contains(z),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let q = b.objects[id];
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        assert(b.objects.contains_key(p.callbacks[i]));
        assert(b.objects[p.callbacks[i]].tags == a.objects[p.callbacks[i]].tags);
    }
}

/// `task.create` on a fresh id ahead of its deadline.
pub proof fn lemma_create_acquired_legal(now: nat, a: AState, b: AState, req: APromiseCreateReq, pid: Seq<char>, ttl: nat)
    requires
        inv(now, a),
        !a.objects.contains_key(req.id),
        crate::tags::otype(req.tags) == OType::Runnable,
        !crate::tags::timer_targeted(req.tags),
        req.timeout_at > now,
        req.timeout_at <= MAX_TIME as nat,
        ttl <= MAX_TIME as nat,
        b.objects == a.objects.insert(req.id, spec_create_acquired(req, pid, ttl, now)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    let id = req.id;
    let q = spec_create_acquired(req, pid, ttl, now);
    assert(b.objects[id] == q);
    assert(q.callbacks.len() == 0);
    assert(!q.callbacks.contains(id));
    assert(q.project_promise(now) == q);
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `task.acquire`, and `task.create` on an existing pending task.
pub proof fn lemma_acquire_legal(now: nat, a: AState, b: AState, id: Seq<char>, pid: Seq<char>, ttl: nat)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Pending,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        a.objects[id].task.unwrap().version < MAX_TIME as nat,
        ttl <= MAX_TIME as nat,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().acquire(pid, ttl, now))),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.acquire(pid, ttl, now);
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w != id {
            assert(b.objects.contains_key(w));
        }
    }
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert(u.resumes.len() == 0);
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `task.release`, and the lease timeout.
pub proof fn lemma_release_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Acquired,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().release(now))),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.release(now);
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w != id {
            assert(b.objects.contains_key(w));
        }
    }
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `task.halt` on a task that is neither fulfilled nor halted.
pub proof fn lemma_halt_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state != TaskState::Fulfilled,
        a.objects[id].task.unwrap().state != TaskState::Halted,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().halt())),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.halt();
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w != id {
            assert(b.objects.contains_key(w));
        }
    }
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `task.continue` on a halted task.
pub proof fn lemma_continue_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Halted,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().continue_(now))),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.continue_(now);
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w != id {
            assert(b.objects.contains_key(w));
        }
    }
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

// ---------------------------------------------------------------------------
// Proofs
// ---------------------------------------------------------------------------

/// Projection is idempotent.
pub proof fn lemma_project_idem(p: APromise, now: nat)
    ensures p.project(now).project(now) == p.project(now),
{
}

/// A heartbeat step from a state in heartbeat shape relative to `a` leaves a
/// state in heartbeat shape relative to `a`.
pub proof fn lemma_heartbeat_compose(now: nat, a: AState, s0: AState, b: AState, x: Seq<char>)
    requires
        heartbeat_shape(now, a, s0, x) || unchanged_at(a, s0, x),
        heartbeat_shape(now, s0, b, x) || unchanged_at(s0, b, x),
    ensures
        heartbeat_shape(now, a, b, x),
{
    if a.objects.contains_key(x) {
        let p = a.objects[x];
        assert(s0.objects.contains_key(x));
        let m = s0.objects[x];
        assert(b.objects.contains_key(x));
        if b.objects[x] == m {
        } else if b.objects[x] == m.project(now) {
            if m == p {
            } else if m == p.project(now) {
                lemma_project_idem(p, now);
            } else {
                let h = p.with_task(p.task.unwrap().heartbeat(now));
                assert(m == h);
                assert(h.project(now) == h);
            }
        } else {
            // m had an acquired task on a pending promise, and b[x] is m with its lease refreshed
            assert(m.task is Some && m.task.unwrap().state == TaskState::Acquired && m.state == PromiseState::Pending && m.timeout_at > now);
            if m == p {
            } else if m == p.project(now) {
                assert(p.project(now) == p);
            } else {
                let h = p.with_task(p.task.unwrap().heartbeat(now));
                assert(m == h);
                assert(h.with_task(h.task.unwrap().heartbeat(now)) == h);
            }
        }
    } else {
        assert(!s0.objects.contains_key(x));
        assert(!b.objects.contains_key(x));
    }
}

/// Any set of objects each untouched, projected or lease-refreshed is a legal step.
pub proof fn lemma_heartbeat_legal(now: nat, a: AState, b: AState, ids: spec_fn(Seq<char>) -> bool)
    requires
        inv(now, a),
        forall|x: Seq<char>| #[trigger] ids(x) ==> heartbeat_shape(now, a, b, x),
        forall|x: Seq<char>| !ids(x) ==> #[trigger] unchanged_at(a, b, x),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].callbacks == a.objects[w].callbacks
        && b.objects[w].tags == a.objects[w].tags by {
        if ids(w) {
            assert(heartbeat_shape(now, a, b, w));
            let p = a.objects[w];
            if b.objects[w] == p {
            } else if b.objects[w] == p.project(now) {
            } else {
                assert(b.objects[w] == p.with_task(p.task.unwrap().heartbeat(now)));
            }
        } else {
            assert(unchanged_at(a, b, w));
        }
    }
    assert(pointer_frame(a, b));
    // the changed ids
    assert forall|x: Seq<char>| #[trigger] ids(x) && b.objects.contains_key(x) implies inv_obj(now, b, x) && trans_obj(now, a, b, x) by {
        assert(heartbeat_shape(now, a, b, x));
        assert(a.objects.contains_key(x));
        assert(inv_obj(now, a, x));
        let p = a.objects[x];
        if b.objects[x] == p {
            assert(unchanged_at(a, b, x));
            lemma_trans_obj_unchanged(now, a, b, x);
            crate::frame::lemma_inv_obj_frame_simple(now, a, b, x);
        } else if b.objects[x] == p.project(now) {
            lemma_project_inv_obj(now, a, b, x);
            lemma_project_trans_obj(now, a, b, x);
        } else {
            let t = p.task.unwrap();
            let u = t.heartbeat(now);
            let q = p.with_task(u);
            assert(b.objects[x] == q);
            lemma_task_edit_frame(now, a, b, x);
            assert(q.project_promise(now) == q);
            assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
            assert(inv_obj(now, b, x));
            assert(trans_obj(now, a, b, x));
        }
    }
    assert forall|x: Seq<char>| #[trigger] ids(x) implies trans_obj(now, a, b, x) by {
        if !b.objects.contains_key(x) {
            assert(heartbeat_shape(now, a, b, x));
            assert(!a.objects.contains_key(x));
        }
    }
    assert forall|x: Seq<char>| !ids(x) implies
        (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]) by {
        assert(unchanged_at(a, b, x));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, ids, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `task.suspend`'s 300: the task keeps running with its ledger cleared, and
/// every awaited promise was read.
pub proof fn lemma_suspend_300_legal(now: nat, a: AState, b: AState, id: Seq<char>, acts: Seq<PromiseRegisterCallbackReq>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Acquired,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().clear_resumes()),
        forall|x: Seq<char>| #[trigger] awaited_of(acts, x) ==>
            a.objects.contains_key(x) && x != id
            && b.objects.contains_key(x) && b.objects[x] == a.objects[x].project(now),
        forall|x: Seq<char>| !awaited_of(acts, x) && x != id ==> #[trigger] unchanged_at(a, b, x),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    let changed = |x: Seq<char>| x == id || awaited_of(acts, x);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].callbacks == a.objects[w].callbacks
        && b.objects[w].tags == a.objects[w].tags by {
        if w == id {
        } else if awaited_of(acts, w) {
        } else {
            assert(unchanged_at(a, b, w));
        }
    }
    assert forall|x: Seq<char>| #[trigger] changed(x) && b.objects.contains_key(x) implies inv_obj(now, b, x) by {
        if x == id {
            assert(inv_obj(now, a, x));
            let p = a.objects[x];
            let t = p.task.unwrap();
            let u = t.clear_resumes();
            let q = p.with_task(u);
            assert(pointer_frame(a, b));
            lemma_task_edit_frame(now, a, b, x);
            assert(q.project_promise(now) == q);
            assert(inv_obj(now, b, x));
        } else {
            lemma_project_inv_obj(now, a, b, x);
        }
    }
    assert forall|x: Seq<char>| #[trigger] changed(x) implies trans_obj(now, a, b, x) by {
        if x == id {
            assert(inv_obj(now, a, x));
            let p = a.objects[x];
            let t = p.task.unwrap();
            let u = t.clear_resumes();
            let q = p.with_task(u);
            assert(pointer_frame(a, b));
            lemma_task_edit_frame(now, a, b, x);
            assert(q.project_promise(now) == q);
            assert(trans_obj(now, a, b, x));
        } else {
            lemma_project_trans_obj(now, a, b, x);
        }
    }
    assert forall|x: Seq<char>| !changed(x) implies
        (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]) by {
        assert(unchanged_at(a, b, x));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, changed, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `add_callback` registers `y`, and keeps what was registered.
pub proof fn lemma_add_callback_contains(p: APromise, y: Seq<char>)
    ensures
        p.add_callback(y).callbacks.contains(y),
        forall|z: Seq<char>| p.callbacks.contains(z) ==> #[trigger] p.add_callback(y).callbacks.contains(z),
        p.add_callback(y).tags == p.tags,
        p.add_callback(y).state == p.state,
{
    let q = p.add_callback(y);
    if p.callbacks.contains(y) {
    } else {
        assert(q.callbacks[q.callbacks.len() - 1] == y);
        assert forall|z: Seq<char>| p.callbacks.contains(z) implies #[trigger] q.callbacks.contains(z) by {
            let i = choose|i: int| 0 <= i < p.callbacks.len() && p.callbacks[i] == z;
            assert(q.callbacks[i] == z);
        }
    }
}

/// The parked task itself obeys the catalogue at its id, given a rung.
proof fn lemma_suspended_task_obj(now: nat, a: AState, b: AState, id: Seq<char>, w0: Seq<char>)
    requires
        suspend_base(now, a, id),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().suspend()),
        b.objects.contains_key(w0),
        b.objects[w0].callbacks.contains(id),
        b.objects[w0].state == PromiseState::Pending,
        pointer_frame(a, b),
    ensures
        inv_obj(now, b, id),
        trans_obj(now, a, b, id),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.suspend();
    let q = p.with_task(u);
    assert(some_callbacks_contain(b, id));
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert(u.resumes.len() == 0);
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
}

/// `task.suspend`'s 200: the task parked, registered on every awaited promise.
#[verifier::rlimit(400)]
pub proof fn lemma_suspend_legal(now: nat, a: AState, b: AState, id: Seq<char>, acts: Seq<PromiseRegisterCallbackReq>)
    requires
        suspend_base(now, a, id),
        acts.len() > 0,
        awaited_distinct(acts),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().suspend()),
        forall|x: Seq<char>| #[trigger] awaited_of(acts, x) ==>
            a.objects.contains_key(x) && a.objects[x].otype().awaitable()
            && a.objects[x].state == PromiseState::Pending && a.objects[x].timeout_at > now
            && x != id && crate::ident::same_origin_spec(x, id)
            && b.objects.contains_key(x) && b.objects[x] == a.objects[x].add_callback(id),
        forall|x: Seq<char>| !awaited_of(acts, x) && x != id ==> #[trigger] unchanged_at(a, b, x),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let changed = |x: Seq<char>| x == id || awaited_of(acts, x);
    assert(a.objects[id].otype() == OType::Runnable);
    // pointers survive
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w == id {
        } else if awaited_of(acts, w) {
            lemma_add_callback_contains(a.objects[w], id);
        } else {
            assert(unchanged_at(a, b, w));
        }
    }
    assert(pointer_frame(a, b));
    // the rung: the first awaited promise holds `id`
    let w0 = acts[0].awaited@;
    assert(awaited_touched(acts, acts.len() as int, w0));
    assert(awaited_of(acts, w0));
    lemma_add_callback_contains(a.objects[w0], id);
    assert(b.objects[w0].callbacks.contains(id));
    assert(b.objects[w0].state == PromiseState::Pending);
    assert(b.objects[id].otype() == OType::Runnable);
    // the task object
    lemma_suspended_task_obj(now, a, b, id, w0);
    // the awaited objects
    assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
        inv_obj(now, b, x) && trans_obj(now, a, b, x) by {
        lemma_added_callback_obj(now, a, b, x, id);
    }
    assert forall|x: Seq<char>| #[trigger] changed(x) && b.objects.contains_key(x) implies inv_obj(now, b, x) by {}
    assert forall|x: Seq<char>| #[trigger] changed(x) implies trans_obj(now, a, b, x) by {}
    assert forall|x: Seq<char>| !changed(x) implies
        (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]) by {
        assert(unchanged_at(a, b, x));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, changed, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// A pending, awaitable promise that gained a callback on a runnable, pending
/// awaiter of its origin obeys the catalogue at its id.
pub proof fn lemma_added_callback_obj(now: nat, a: AState, b: AState, w: Seq<char>, awaiter: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(w),
        w != awaiter,
        crate::ident::same_origin_spec(awaiter, w),
        a.objects[w].state == PromiseState::Pending,
        a.objects[w].otype().awaitable(),
        b.objects.contains_key(w),
        b.objects[w] == a.objects[w].add_callback(awaiter),
        b.objects.contains_key(awaiter),
        b.objects[awaiter].otype() == OType::Runnable,
        pointer_frame(a, b),
    ensures
        inv_obj(now, b, w),
        trans_obj(now, a, b, w),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, w));
    let p = a.objects[w];
    let q = p.add_callback(awaiter);
    lemma_add_callback_contains(p, awaiter);
    if p.callbacks.contains(awaiter) {
        assert(q == p);
    } else {
        assert(q.callbacks == p.callbacks.push(awaiter));
        assert(no_dups(q.callbacks)) by {
            assert forall|i: int, j: int| 0 <= i < q.callbacks.len() && 0 <= j < q.callbacks.len()
                && q.callbacks[i] == q.callbacks[j] implies i == j by {
                if i < p.callbacks.len() && j < p.callbacks.len() {
                } else if i < p.callbacks.len() {
                    assert(p.callbacks[i] == awaiter);
                } else if j < p.callbacks.len() {
                    assert(p.callbacks[j] == awaiter);
                }
            }
        }
    }
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable
        && crate::ident::same_origin_spec(q.callbacks[i], w) && q.callbacks[i] != w by {
        if i < p.callbacks.len() {
            assert(q.callbacks[i] == p.callbacks[i]);
            assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
            assert(b.objects[p.callbacks[i]].tags == a.objects[p.callbacks[i]].tags);
        } else {
            assert(q.callbacks[i] == awaiter);
        }
    }
    assert(!q.callbacks.contains(w));
    match q.task {
        Some(t) => {
            if t.state == TaskState::Suspended && q.project_promise(now).state == PromiseState::Pending {
                assert(some_callbacks_contain(a, w));
                let w2 = choose|w2: Seq<char>| #[trigger] a.objects.contains_key(w2) && a.objects[w2].callbacks.contains(w);
                assert(b.objects[w2].callbacks.contains(w));
                assert(some_callbacks_contain(b, w));
            }
        }
        None => {}
    }
    assert(inv_obj(now, b, w));
    assert(trans_obj(now, a, b, w));
}

/// One projected object makes every other id's `.trans` entries carry from
/// the intermediate state back to the start.
pub proof fn lemma_trans_obj_transfer(now: nat, a: AState, a1: AState, c: AState, y: Seq<char>)
    requires
        trans_obj(now, a1, c, y),
        a.objects.contains_key(y) <==> a1.objects.contains_key(y),
        a.objects.contains_key(y) ==> a.objects[y] == a1.objects[y],
        forall|w: Seq<char>| #[trigger] a1.objects.contains_key(w) ==>
            a.objects.contains_key(w) && a1.objects[w].callbacks == a.objects[w].callbacks,
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==> a1.objects.contains_key(w),
    ensures
        trans_obj(now, a, c, y),
{
    if c.objects.contains_key(y) {
        let q = c.objects[y];
        assert(a.task_of(y) == a1.task_of(y));
        assert(a.promise_of(y) == a1.promise_of(y));
        assert(a.has_task(y) == a1.has_task(y));
        match q.task {
            Some(u) => {
                match a1.task_of(y) {
                    Some(t) => {
                        if t.state == TaskState::Suspended && u.state == TaskState::Pending {
                            assert(consistent_wake_follows_callback_consumption_at(now, a1, c, y, q));
                            assert(exists|pid: Seq<char>| #[trigger] a1.objects.contains_key(pid)
                                && a1.objects[pid].callbacks.contains(y)
                                && (match c.promise_of(pid) { None => false, Some(w) => !w.callbacks.contains(y) })
                                && u.resumes.contains(pid));
                            let pid = choose|pid: Seq<char>| #[trigger] a1.objects.contains_key(pid)
                                && a1.objects[pid].callbacks.contains(y)
                                && (match c.promise_of(pid) { None => false, Some(w) => !w.callbacks.contains(y) })
                                && u.resumes.contains(pid);
                            assert(a1.objects.contains_key(pid));
                            assert(a.objects.contains_key(pid));
                            assert(a1.objects[pid].callbacks == a.objects[pid].callbacks);
                            assert(a.objects[pid].callbacks.contains(y));
                            assert(consistent_wake_follows_callback_consumption_at(now, a, c, y, q));
                        }
                    }
                    None => {}
                }
            }
            None => {}
        }
    }
}

/// `task.fence`: a projection of the fencing task's object, then a legal
/// promise step on another id, is one legal step.
pub proof fn lemma_fence_legal(now: nat, a: AState, a1: AState, c: AState, x: Seq<char>, y: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(x),
        a1.objects == a.objects.insert(x, a.objects[x].project(now)),
        a1.schedules == a.schedules,
        a1.outbox == a.outbox,
        legal(now, a1, c),
        touches_only(a1, c, |z: Seq<char>| z == y),
        x != y,
    ensures
        legal(now, a, c),
{
    lemma_inv_pointwise(now, a);
    lemma_legal_pointwise(now, a1, c);
    assert forall|w: Seq<char>| #[trigger] a1.objects.contains_key(w) implies
        a.objects.contains_key(w) && a1.objects[w].callbacks == a.objects[w].callbacks by {}
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies a1.objects.contains_key(w) by {}
    assert forall|id: Seq<char>| #[trigger] trans_obj(now, a, c, id) by {
        if id == x {
            assert(a1.objects.contains_key(x));
            assert(a1.objects[x] == a.objects[x].project(now));
            assert(c.objects.contains_key(x));
            assert(c.objects[x] == a1.objects[x]);
            lemma_project_trans_obj(now, a, c, x);
        } else if id == y {
            assert(trans_obj(now, a1, c, y));
            assert(a.objects.contains_key(y) <==> a1.objects.contains_key(y));
            lemma_trans_obj_transfer(now, a, a1, c, y);
        } else {
            assert(a1.objects.contains_key(id) <==> c.objects.contains_key(id));
            assert(a.objects.contains_key(id) <==> c.objects.contains_key(id));
            lemma_trans_obj_unchanged(now, a, c, id);
        }
    }
    assert forall|k: OutboxKey| #[trigger] trans_out(now, a, c, k) by {
        lemma_trans_out_unchanged(now, a, c, k);
    }
    assert forall|id: Seq<char>| #[trigger] trans_sched(now, a, c, id) by {
        lemma_trans_sched_unchanged(now, a, c, id);
    }
    lemma_legal_pointwise(now, a, c);
}

} // verus!
