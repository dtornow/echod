//! The sweep's two facts: on a state with nothing due it changes nothing
//! (`lemma_sweep_idem`), and it leaves nothing due (`lemma_sweep_swept`). The
//! second is what makes the relation's "abstract state is the sweep of the
//! concrete one" stable under the concrete machine's own sweeps.

use vstd::prelude::*;

use echod_kernel::external::with_objects;
use echod_kernel::external_proof::{lemma_project_idem, lemma_project_legal, lemma_release_legal};
use echod_kernel::internal::{lease_due, lease_timeout_objects, promise_timeout_objects, resumed_shape, retry_due, retry_timeout_objects};
use echod_kernel::internal_proof::{lemma_callback_legal, lemma_listener_legal, lemma_retry_legal};
use echod_kernel::object::{next_offer, lemma_next_offer, without};
use echod_kernel::object_proof::lemma_without_contains;
use echod_kernel::properties::{inv, inv_obj, opt_or_zero};
use echod_kernel::properties_proof::lemma_inv_pointwise;
use echod_kernel::steps::deadline_at;
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::spec::DispatchV;

use crate::sweep::*;

verus! {

/// Nothing is due on the object at `now`: its deadline is read, its lease
/// not past, its callbacks and listeners spent if it is settled, its offer
/// ahead.
pub open spec fn swept_obj(p: APromise, now: nat) -> bool {
    &&& p.project(now) == p
    &&& !lease_due(p, now)
    &&& p.state != PromiseState::Pending ==> p.callbacks.len() == 0 && p.listeners.len() == 0
    &&& !retry_due(p, now)
}

pub open spec fn swept(a: AState, now: nat) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> swept_obj(a.objects[id], now)
}

pub proof fn lemma_insert_same(a: AState, id: Seq<char>)
    requires
        a.objects.contains_key(id),
    ensures
        with_objects(a, a.objects.insert(id, a.objects[id])) == a,
{
    assert(a.objects.insert(id, a.objects[id]) =~= a.objects);
}

// ----------------------------------------------- identity on a swept state

pub proof fn lemma_deadlines_idem(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        swept(a, now),
    ensures
        phase_deadlines(a, ids, now) == a,
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_deadlines_idem(a, ids.drop_last(), now);
        let id = ids.last();
        if a.objects.contains_key(id) {
            lemma_insert_same(a, id);
        }
    }
}

pub proof fn lemma_leases_idem(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        swept(a, now),
    ensures
        phase_leases(a, ids, now) == a,
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_leases_idem(a, ids.drop_last(), now);
    }
}

pub proof fn lemma_callback_idem(a: AState, x: Seq<char>, y: Seq<char>, now: nat)
    requires
        swept(a, now),
    ensures
        callback_fn(a, x, y, now) == a,
{
    if a.objects.contains_key(x) {
        lemma_insert_same(a, x);
        let p = a.objects[x];
        if p.state != PromiseState::Pending {
            assert(p.callbacks.len() == 0);
            assert(!p.callbacks.contains(y));
        }
    }
}

pub proof fn lemma_callbacks_of_idem(a: AState, x: Seq<char>, awaiters: Seq<Seq<char>>, now: nat)
    requires
        swept(a, now),
    ensures
        callbacks_of(a, x, awaiters, now) == a,
    decreases awaiters.len(),
{
    if awaiters.len() > 0 {
        lemma_callbacks_of_idem(a, x, awaiters.drop_last(), now);
        lemma_callback_idem(a, x, awaiters.last(), now);
    }
}

pub proof fn lemma_callbacks_idem(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        swept(a, now),
    ensures
        phase_callbacks(a, ids, now) == a,
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_callbacks_idem(a, ids.drop_last(), now);
        let x = ids.last();
        if a.objects.contains_key(x) {
            lemma_callbacks_of_idem(a, x, a.objects[x].callbacks, now);
        }
    }
}

pub proof fn lemma_listener_idem(a: AState, x: Seq<char>, address: Seq<char>, now: nat)
    requires
        swept(a, now),
    ensures
        listener_fn(a, x, address, now) == a,
{
    if a.objects.contains_key(x) {
        lemma_insert_same(a, x);
        let p = a.objects[x];
        if p.state != PromiseState::Pending {
            assert(p.listeners.len() == 0);
            assert(!p.listeners.contains(address));
        }
    }
}

pub proof fn lemma_listeners_of_idem(a: AState, x: Seq<char>, addresses: Seq<Seq<char>>, now: nat)
    requires
        swept(a, now),
    ensures
        listeners_of(a, x, addresses, now) == a,
    decreases addresses.len(),
{
    if addresses.len() > 0 {
        lemma_listeners_of_idem(a, x, addresses.drop_last(), now);
        lemma_listener_idem(a, x, addresses.last(), now);
    }
}

pub proof fn lemma_listeners_idem(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        swept(a, now),
    ensures
        phase_listeners(a, ids, now) == a,
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_listeners_idem(a, ids.drop_last(), now);
        let x = ids.last();
        if a.objects.contains_key(x) {
            lemma_listeners_of_idem(a, x, a.objects[x].listeners, now);
        }
    }
}

pub proof fn lemma_retries_idem(a: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    requires
        swept(a, now),
    ensures
        phase_retries(a, ids, now, t) == a,
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_retries_idem(a, ids.drop_last(), now, t);
    }
}

/// On a state with nothing due, the sweep is the identity.
pub proof fn lemma_sweep_idem(a: AState, now: nat, t: nat)
    requires
        swept(a, now),
    ensures
        sweep_fn(a, now, t) == a,
{
    let ids = ids_of(a);
    lemma_deadlines_idem(a, ids, now);
    lemma_leases_idem(a, ids, now);
    lemma_callbacks_idem(a, ids, now);
    lemma_listeners_idem(a, ids, now);
    lemma_retries_idem(a, ids, now, t);
}

// ------------------------------------------------- the sweep leaves nothing due
//
// The five clauses of `swept`, one per phase. Each phase lemma establishes its
// clause on every object it is given and keeps the clauses of the phases
// before it; the per-object steps touch only the object named (the callback
// step also the awaiter's task), which is what keeps them.

/// Every object is projected at `now`.
pub open spec fn projected(a: AState, now: nat) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> a.objects[id].project(now) == a.objects[id]
}

/// No lease is due.
pub open spec fn leases_clear(a: AState, now: nat) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> !lease_due(a.objects[id], now)
}

/// A settled object has no callback left.
pub open spec fn callbacks_spent(a: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> (a.objects[id].state != PromiseState::Pending ==> a.objects[id].callbacks.len() == 0)
}

/// A settled object has no listener left.
pub open spec fn listeners_spent(a: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> (a.objects[id].state != PromiseState::Pending ==> a.objects[id].listeners.len() == 0)
}

/// No offer is due.
pub open spec fn retries_clear(a: AState, now: nat) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> !retry_due(a.objects[id], now)
}

/// Membership through the last element.
pub proof fn lemma_contains_split(s: Seq<Seq<char>>, y: Seq<char>)
    requires
        s.len() > 0,
    ensures
        s.contains(y) <==> (s.drop_last().contains(y) || s.last() == y),
{
    let init = s.drop_last();
    if s.contains(y) {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == y;
        if i < s.len() - 1 {
            assert(init[i] == y);
        }
    }
    if init.contains(y) {
        let i = choose|i: int| 0 <= i < init.len() && init[i] == y;
        assert(s[i] == y);
    }
    if s.last() == y {
        assert(s[s.len() - 1] == y);
    }
}

/// The objects' order covers the objects.
pub proof fn lemma_ids_cover(a: AState)
    requires
        a.objects.dom().finite(),
    ensures
        forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> ids_of(a).contains(id),
{
    broadcast use Seq::to_set_ensures;
    a.objects.dom().lemma_to_seq_to_set_id();
    assert forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) implies ids_of(a).contains(id) by {
        assert(a.objects.dom().to_seq().to_set().contains(id));
    }
}

/// What projection says of an object it leaves alone: pending means ahead of
/// its deadline, settled means its task, if any, is fulfilled.
pub proof fn lemma_projected_obj(p: APromise, now: nat)
    requires
        p.project(now) == p,
    ensures
        p.state == PromiseState::Pending ==> p.timeout_at > now,
        p.state != PromiseState::Pending && p.task is Some ==> p.task.unwrap().state == TaskState::Fulfilled,
{
    if p.state == PromiseState::Pending && p.timeout_at <= now {
        assert(p.project(now).state == p.project_promise(now).state);
        assert(p.project_promise(now).state != PromiseState::Pending);
        assert(false);
    }
    if p.state != PromiseState::Pending && p.task is Some {
        let t = p.task.unwrap();
        assert(p.project_promise(now) == p);
        assert(p.project(now).task == Some(t.view_through(p)));
        if t.state != TaskState::Fulfilled {
            assert(t.view_through(p).state == TaskState::Fulfilled);
            assert(false);
        }
    }
}

/// Projection reads the state, the deadline, the tags and the task: an edit of
/// the callbacks or the listeners keeps a projected object projected.
pub proof fn lemma_project_lists(p: APromise, now: nat, callbacks: Seq<Seq<char>>, listeners: Seq<Seq<char>>)
    requires
        p.project(now) == p,
    ensures
        (APromise { callbacks, listeners, ..p }).project(now) == (APromise { callbacks, listeners, ..p }),
{
    let q = APromise { callbacks, listeners, ..p };
    lemma_projected_obj(p, now);
    if p.state == PromiseState::Pending {
        assert(q.project_promise(now) == q);
        match q.task {
            None => {},
            Some(t) => {
                assert(t.view_through(q) == t);
            },
        }
    } else {
        assert(q.project_promise(now) == q);
        match q.task {
            None => {},
            Some(t) => {
                assert(t.state == TaskState::Fulfilled);
                assert(t.view_through(q) == t);
            },
        }
    }
}

/// A pending object ahead of its deadline is projected whatever its task.
pub proof fn lemma_project_pending_task(p: APromise, now: nat, t: ATask)
    requires
        p.state == PromiseState::Pending,
        p.timeout_at > now,
    ensures
        p.with_task(t).project(now) == p.with_task(t),
{
    let q = p.with_task(t);
    assert(q.project_promise(now) == q);
    assert(t.view_through(q) == t);
}

// --------------------------------------------------------------- deadlines

pub proof fn lemma_deadlines_phase(a: AState, ids: Seq<Seq<char>>, now: nat)
    ensures
        ({
            let b = phase_deadlines(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& b.outbox == a.outbox
            &&& forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) ==> b.objects[id].project(now) == b.objects[id]
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_deadlines_phase(a, ids.drop_last(), now);
        let a1 = phase_deadlines(a, ids.drop_last(), now);
        let x = ids.last();
        let b = phase_deadlines(a, ids, now);
        if a1.objects.contains_key(x) {
            assert(b.objects == a1.objects.insert(x, a1.objects[x].project(now)));
            assert(b.objects.dom() =~= a1.objects.dom());
            lemma_project_idem(a1.objects[x], now);
        }
        assert forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) implies b.objects[id].project(now) == b.objects[id] by {
            lemma_contains_split(ids, id);
            if id != x {
                assert(b.objects[id] == a1.objects[id]);
            }
        }
    }
}

// ------------------------------------------------------------------ leases

pub proof fn lemma_leases_phase(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        projected(a, now),
    ensures
        ({
            let b = phase_leases(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& b.outbox == a.outbox
            &&& projected(b, now)
            &&& forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) ==> !lease_due(b.objects[id], now)
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_leases_phase(a, ids.drop_last(), now);
        let a1 = phase_leases(a, ids.drop_last(), now);
        let x = ids.last();
        let b = phase_leases(a, ids, now);
        if a1.objects.contains_key(x) && lease_due(a1.objects[x], now) {
            let p = a1.objects[x];
            let t = p.task.unwrap().release(p.task.unwrap().lease_timeout_at.unwrap() as nat);
            assert(b.objects == a1.objects.insert(x, p.with_task(t)));
            assert(b.objects.dom() =~= a1.objects.dom());
            lemma_project_pending_task(p, now, t);
            assert(!lease_due(p.with_task(t), now));
        } else {
            assert(b == a1);
        }
        assert forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) implies !lease_due(b.objects[id], now) by {
            lemma_contains_split(ids, id);
            if id != x {
                assert(b.objects[id] == a1.objects[id]);
            }
        }
    }
}

// --------------------------------------------------------------- callbacks

/// One callback step on a state where every object is projected and no lease
/// is due: it keeps both, keeps every key, state and listener list, keeps
/// every other object's callbacks, and spends `y` on `x` if `x` is settled and
/// holds it.
pub proof fn lemma_callback_fn(a: AState, x: Seq<char>, y: Seq<char>, now: nat)
    requires
        projected(a, now),
        leases_clear(a, now),
    ensures
        ({
            let b = callback_fn(a, x, y, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& b.outbox == a.outbox
            &&& projected(b, now)
            &&& leases_clear(b, now)
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) ==> b.objects[z].state == a.objects[z].state && b.objects[z].listeners == a.objects[z].listeners
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) && z != x ==> b.objects[z].callbacks == a.objects[z].callbacks
            &&& a.objects.contains_key(x) ==> b.objects[x].callbacks == (if a.objects[x].state != PromiseState::Pending && a.objects[x].callbacks.contains(y) { without(a.objects[x].callbacks, y) } else { a.objects[x].callbacks })
        }),
{
    let b = callback_fn(a, x, y, now);
    if a.objects.contains_key(x) {
        let p = a.objects[x].project(now);
        assert(p == a.objects[x]);
        lemma_insert_same(a, x);
        let a1 = with_objects(a, a.objects.insert(x, p));
        assert(a1 == a);
        if p.state == PromiseState::Pending || !p.callbacks.contains(y) {
            assert(b == a);
        } else {
            let p2 = p.remove_callback(y);
            let a2 = with_objects(a1, a1.objects.insert(x, p2));
            assert(a2.objects.dom() =~= a.objects.dom());
            lemma_project_lists(p, now, without(p.callbacks, y), p.listeners);
            assert(p2 == APromise { callbacks: without(p.callbacks, y), listeners: p.listeners, ..p });
            assert(projected(a2, now));
            assert(leases_clear(a2, now));
            if !a2.objects.contains_key(y) {
                assert(b == a2);
            } else {
                let q = a2.objects[y].project(now);
                assert(q == a2.objects[y]);
                lemma_insert_same(a2, y);
                let a3 = with_objects(a2, a2.objects.insert(y, q));
                assert(a3 == a2);
                match q.task {
                    None => {
                        assert(b == a3);
                    },
                    Some(t) => {
                        lemma_projected_obj(q, now);
                        if t.state == TaskState::Suspended {
                            assert(q.state == PromiseState::Pending);
                            assert(y != x);
                            let t2 = t.wake(x, opt_or_zero(p.settled_at));
                            lemma_project_pending_task(q, now, t2);
                            assert(b == with_objects(a3, a3.objects.insert(y, q.with_task(t2))));
                            assert(b.objects.dom() =~= a.objects.dom());
                            assert(!lease_due(q.with_task(t2), now));
                        } else if t.state != TaskState::Fulfilled {
                            assert(q.state == PromiseState::Pending);
                            assert(y != x);
                            let t2 = t.buffer(x);
                            lemma_project_pending_task(q, now, t2);
                            assert(b == with_objects(a3, a3.objects.insert(y, q.with_task(t2))));
                            assert(b.objects.dom() =~= a.objects.dom());
                            assert(!lease_due(q.with_task(t2), now));
                        } else {
                            assert(b == a3);
                        }
                    },
                }
            }
        }
    } else {
        assert(b == a);
    }
}

pub proof fn lemma_callbacks_of(a: AState, x: Seq<char>, aw: Seq<Seq<char>>, now: nat)
    requires
        projected(a, now),
        leases_clear(a, now),
        a.objects.contains_key(x),
    ensures
        ({
            let b = callbacks_of(a, x, aw, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& b.outbox == a.outbox
            &&& projected(b, now)
            &&& leases_clear(b, now)
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) ==> b.objects[z].state == a.objects[z].state && b.objects[z].listeners == a.objects[z].listeners
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) && z != x ==> b.objects[z].callbacks == a.objects[z].callbacks
            &&& a.objects[x].state != PromiseState::Pending ==> forall|c: Seq<char>| #[trigger] b.objects[x].callbacks.contains(c) ==> a.objects[x].callbacks.contains(c) && !aw.contains(c)
        }),
    decreases aw.len(),
{
    if aw.len() > 0 {
        lemma_callbacks_of(a, x, aw.drop_last(), now);
        let b1 = callbacks_of(a, x, aw.drop_last(), now);
        let y = aw.last();
        lemma_callback_fn(b1, x, y, now);
        let b = callback_fn(b1, x, y, now);
        if a.objects[x].state != PromiseState::Pending {
            assert forall|c: Seq<char>| #[trigger] b.objects[x].callbacks.contains(c) implies a.objects[x].callbacks.contains(c) && !aw.contains(c) by {
                lemma_contains_split(aw, c);
                if b1.objects[x].callbacks.contains(y) {
                    lemma_without_contains(b1.objects[x].callbacks, y, c);
                }
            }
        }
    }
}

pub proof fn lemma_callbacks_phase(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        projected(a, now),
        leases_clear(a, now),
    ensures
        ({
            let b = phase_callbacks(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& b.outbox == a.outbox
            &&& projected(b, now)
            &&& leases_clear(b, now)
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) ==> b.objects[z].state == a.objects[z].state && b.objects[z].listeners == a.objects[z].listeners
            &&& forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) ==> (b.objects[id].state != PromiseState::Pending ==> b.objects[id].callbacks.len() == 0)
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_callbacks_phase(a, ids.drop_last(), now);
        let a1 = phase_callbacks(a, ids.drop_last(), now);
        let x = ids.last();
        let b = phase_callbacks(a, ids, now);
        if a1.objects.contains_key(x) {
            lemma_callbacks_of(a1, x, a1.objects[x].callbacks, now);
            assert(b == callbacks_of(a1, x, a1.objects[x].callbacks, now));
            if a1.objects[x].state != PromiseState::Pending && b.objects[x].callbacks.len() > 0 {
                let c = b.objects[x].callbacks[0];
                assert(b.objects[x].callbacks.contains(c));
                assert(false);
            }
        } else {
            assert(b == a1);
        }
        assert forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) implies (b.objects[id].state != PromiseState::Pending ==> b.objects[id].callbacks.len() == 0) by {
            lemma_contains_split(ids, id);
            if id != x {
                assert(b.objects[id].callbacks == a1.objects[id].callbacks);
                assert(b.objects[id].state == a1.objects[id].state);
            }
        }
    }
}

// --------------------------------------------------------------- listeners

pub proof fn lemma_listener_fn(a: AState, x: Seq<char>, address: Seq<char>, now: nat)
    requires
        projected(a, now),
        leases_clear(a, now),
    ensures
        ({
            let b = listener_fn(a, x, address, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& projected(b, now)
            &&& leases_clear(b, now)
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) ==> b.objects[z].state == a.objects[z].state && b.objects[z].callbacks == a.objects[z].callbacks && b.objects[z].task == a.objects[z].task
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) && z != x ==> b.objects[z].listeners == a.objects[z].listeners
            &&& a.objects.contains_key(x) ==> b.objects[x].listeners == (if a.objects[x].state != PromiseState::Pending && a.objects[x].listeners.contains(address) { without(a.objects[x].listeners, address) } else { a.objects[x].listeners })
        }),
{
    let b = listener_fn(a, x, address, now);
    if a.objects.contains_key(x) {
        let p = a.objects[x].project(now);
        assert(p == a.objects[x]);
        lemma_insert_same(a, x);
        let a1 = with_objects(a, a.objects.insert(x, p));
        assert(a1 == a);
        if p.state == PromiseState::Pending || !p.listeners.contains(address) {
            assert(b == a);
        } else {
            let q = p.remove_listener(address);
            assert(b.objects == a.objects.insert(x, q));
            assert(b.objects.dom() =~= a.objects.dom());
            lemma_project_lists(p, now, p.callbacks, without(p.listeners, address));
            assert(q == APromise { callbacks: p.callbacks, listeners: without(p.listeners, address), ..p });
        }
    } else {
        assert(b == a);
    }
}

pub proof fn lemma_listeners_of(a: AState, x: Seq<char>, addresses: Seq<Seq<char>>, now: nat)
    requires
        projected(a, now),
        leases_clear(a, now),
        a.objects.contains_key(x),
    ensures
        ({
            let b = listeners_of(a, x, addresses, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& projected(b, now)
            &&& leases_clear(b, now)
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) ==> b.objects[z].state == a.objects[z].state && b.objects[z].callbacks == a.objects[z].callbacks && b.objects[z].task == a.objects[z].task
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) && z != x ==> b.objects[z].listeners == a.objects[z].listeners
            &&& a.objects[x].state != PromiseState::Pending ==> forall|c: Seq<char>| #[trigger] b.objects[x].listeners.contains(c) ==> a.objects[x].listeners.contains(c) && !addresses.contains(c)
        }),
    decreases addresses.len(),
{
    if addresses.len() > 0 {
        lemma_listeners_of(a, x, addresses.drop_last(), now);
        let b1 = listeners_of(a, x, addresses.drop_last(), now);
        let y = addresses.last();
        lemma_listener_fn(b1, x, y, now);
        let b = listener_fn(b1, x, y, now);
        if a.objects[x].state != PromiseState::Pending {
            assert forall|c: Seq<char>| #[trigger] b.objects[x].listeners.contains(c) implies a.objects[x].listeners.contains(c) && !addresses.contains(c) by {
                lemma_contains_split(addresses, c);
                if b1.objects[x].listeners.contains(y) {
                    lemma_without_contains(b1.objects[x].listeners, y, c);
                }
            }
        }
    }
}

pub proof fn lemma_listeners_phase(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        projected(a, now),
        leases_clear(a, now),
    ensures
        ({
            let b = phase_listeners(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& projected(b, now)
            &&& leases_clear(b, now)
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) ==> b.objects[z].state == a.objects[z].state && b.objects[z].callbacks == a.objects[z].callbacks && b.objects[z].task == a.objects[z].task
            &&& forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) ==> (b.objects[id].state != PromiseState::Pending ==> b.objects[id].listeners.len() == 0)
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_listeners_phase(a, ids.drop_last(), now);
        let a1 = phase_listeners(a, ids.drop_last(), now);
        let x = ids.last();
        let b = phase_listeners(a, ids, now);
        if a1.objects.contains_key(x) {
            lemma_listeners_of(a1, x, a1.objects[x].listeners, now);
            assert(b == listeners_of(a1, x, a1.objects[x].listeners, now));
            if a1.objects[x].state != PromiseState::Pending && b.objects[x].listeners.len() > 0 {
                let c = b.objects[x].listeners[0];
                assert(b.objects[x].listeners.contains(c));
                assert(false);
            }
        } else {
            assert(b == a1);
        }
        assert forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) implies (b.objects[id].state != PromiseState::Pending ==> b.objects[id].listeners.len() == 0) by {
            lemma_contains_split(ids, id);
            if id != x {
                assert(b.objects[id].listeners == a1.objects[id].listeners);
                assert(b.objects[id].state == a1.objects[id].state);
            }
        }
    }
}

// ----------------------------------------------------------------- retries

pub proof fn lemma_retry_fn(a: AState, id: Seq<char>, now: nat, t: nat)
    requires
        projected(a, now),
        leases_clear(a, now),
        0 < t,
        now + t <= u64::MAX,
    ensures
        ({
            let b = retry_fn(a, id, now, t);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& projected(b, now)
            &&& leases_clear(b, now)
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) ==> b.objects[z].state == a.objects[z].state && b.objects[z].callbacks == a.objects[z].callbacks && b.objects[z].listeners == a.objects[z].listeners
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) && z != id ==> b.objects[z] == a.objects[z]
            &&& a.objects.contains_key(id) ==> !retry_due(b.objects[id], now)
        }),
{
    let b = retry_fn(a, id, now, t);
    if a.objects.contains_key(id) && retry_due(a.objects[id], now) {
        let p = a.objects[id];
        let t0 = p.task.unwrap();
        let due = opt_or_zero(t0.retry_timeout_at);
        assert(due == t0.retry_timeout_at.unwrap() as nat);
        assert(due <= now);
        lemma_next_offer(due, now, t);
        let n = next_offer(due, now, t);
        assert(now < n <= now + t);
        assert(n as u64 == n);
        let t2 = t0.rearm(now, t);
        assert(t2.retry_timeout_at == Some(n as u64));
        assert(b.objects == a.objects.insert(id, p.with_task(t2)));
        assert(b.objects.dom() =~= a.objects.dom());
        lemma_project_pending_task(p, now, t2);
        assert(!lease_due(p.with_task(t2), now));
        assert(!retry_due(p.with_task(t2), now));
    } else {
        assert(b == a);
    }
}

pub proof fn lemma_retries_phase(a: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    requires
        projected(a, now),
        leases_clear(a, now),
        0 < t,
        now + t <= u64::MAX,
    ensures
        ({
            let b = phase_retries(a, ids, now, t);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& projected(b, now)
            &&& leases_clear(b, now)
            &&& forall|z: Seq<char>| #[trigger] a.objects.contains_key(z) ==> b.objects[z].state == a.objects[z].state && b.objects[z].callbacks == a.objects[z].callbacks && b.objects[z].listeners == a.objects[z].listeners
            &&& forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) ==> !retry_due(b.objects[id], now)
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_retries_phase(a, ids.drop_last(), now, t);
        let a1 = phase_retries(a, ids.drop_last(), now, t);
        let x = ids.last();
        lemma_retry_fn(a1, x, now, t);
        let b = phase_retries(a, ids, now, t);
        assert(b == retry_fn(a1, x, now, t));
        assert forall|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) implies !retry_due(b.objects[id], now) by {
            lemma_contains_split(ids, id);
            if id != x {
                assert(b.objects[id] == a1.objects[id]);
            }
        }
    }
}

// ------------------------------------------------------------------ the sweep

/// On a finite bucket, within the kernel's doors (a positive interval, and the
/// next offer within the clock's type), the sweep leaves nothing due.
pub proof fn lemma_sweep_swept(a: AState, now: nat, t: nat)
    requires
        a.objects.dom().finite(),
        0 < t,
        now + t <= u64::MAX,
    ensures
        swept(sweep_fn(a, now, t), now),
        sweep_fn(a, now, t).objects.dom() == a.objects.dom(),
        sweep_fn(a, now, t).schedules == a.schedules,
{
    lemma_ids_cover(a);
    let ids = ids_of(a);
    let a1 = phase_deadlines(a, ids, now);
    let a2 = phase_leases(a1, ids, now);
    let a3 = phase_callbacks(a2, ids, now);
    let a4 = phase_listeners(a3, ids, now);
    let a5 = phase_retries(a4, ids, now, t);
    assert(a5 == sweep_fn(a, now, t));
    lemma_deadlines_phase(a, ids, now);
    assert(projected(a1, now));
    lemma_leases_phase(a1, ids, now);
    assert(leases_clear(a2, now));
    lemma_callbacks_phase(a2, ids, now);
    assert(callbacks_spent(a3));
    lemma_listeners_phase(a3, ids, now);
    assert(listeners_spent(a4));
    assert(callbacks_spent(a4));
    lemma_retries_phase(a4, ids, now, t);
    assert(retries_clear(a5, now));
    assert(callbacks_spent(a5));
    assert(listeners_spent(a5));
    assert forall|id: Seq<char>| #[trigger] a5.objects.contains_key(id) implies swept_obj(a5.objects[id], now) by {
        assert(a.objects.contains_key(id));
    }
}


// ------------------------------------------------------------ nothing sent

pub proof fn lemma_listener_send_idem(a: AState, x: Seq<char>, address: Seq<char>, now: nat)
    requires
        swept(a, now),
    ensures
        listener_send(a, x, address, now) == Seq::<DispatchV>::empty(),
{
    if a.objects.contains_key(x) {
        let p = a.objects[x];
        if p.state != PromiseState::Pending {
            assert(p.listeners.len() == 0);
            assert(!p.listeners.contains(address));
        }
    }
}

pub proof fn lemma_listeners_sends_idem(a: AState, x: Seq<char>, addresses: Seq<Seq<char>>, now: nat)
    requires
        swept(a, now),
    ensures
        listeners_sends(a, x, addresses, now) == Seq::<DispatchV>::empty(),
    decreases addresses.len(),
{
    if addresses.len() > 0 {
        lemma_listeners_sends_idem(a, x, addresses.drop_last(), now);
        lemma_listeners_of_idem(a, x, addresses.drop_last(), now);
        lemma_listener_send_idem(a, x, addresses.last(), now);
        assert(listeners_sends(a, x, addresses, now) =~= Seq::<DispatchV>::empty());
    }
}

pub proof fn lemma_phase_listeners_sends_idem(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        swept(a, now),
    ensures
        phase_listeners_sends(a, ids, now) == Seq::<DispatchV>::empty(),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_phase_listeners_sends_idem(a, ids.drop_last(), now);
        lemma_listeners_idem(a, ids.drop_last(), now);
        let x = ids.last();
        if a.objects.contains_key(x) {
            lemma_listeners_sends_idem(a, x, a.objects[x].listeners, now);
        }
        assert(phase_listeners_sends(a, ids, now) =~= Seq::<DispatchV>::empty());
    }
}

pub proof fn lemma_phase_retries_sends_idem(a: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    requires
        swept(a, now),
    ensures
        phase_retries_sends(a, ids, now, t) == Seq::<DispatchV>::empty(),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_phase_retries_sends_idem(a, ids.drop_last(), now, t);
        lemma_retries_idem(a, ids.drop_last(), now, t);
        assert(retry_send(a, ids.last(), now, t) == Seq::<DispatchV>::empty());
        assert(phase_retries_sends(a, ids, now, t) =~= Seq::<DispatchV>::empty());
    }
}

/// On a state with nothing due, the sweep sends nothing.
pub proof fn lemma_sends_idem(a: AState, now: nat, t: nat)
    requires
        swept(a, now),
    ensures
        sweep_sends(a, now, t) == Seq::<DispatchV>::empty(),
{
    let ids = ids_of(a);
    lemma_deadlines_idem(a, ids, now);
    lemma_leases_idem(a, ids, now);
    lemma_callbacks_idem(a, ids, now);
    lemma_listeners_idem(a, ids, now);
    lemma_phase_listeners_sends_idem(a, ids, now);
    lemma_phase_retries_sends_idem(a, ids, now, t);
    assert(sweep_sends(a, now, t) =~= Seq::<DispatchV>::empty());
}

// ------------------------------------------------ the kernel invariant kept

/// The kernel's invariant on the empty bucket.
pub proof fn lemma_inv_empty(now: nat)
    ensures
        inv(now, AState { objects: Map::empty(), schedules: Map::empty(), outbox: Map::empty() }),
{
    let s = AState { objects: Map::empty(), schedules: Map::empty(), outbox: Map::empty() };
    lemma_inv_pointwise(now, s);
}

/// Emptying the outbox keeps the invariant: nothing about an object reads it.
pub proof fn lemma_inv_fresh(now: nat, s: AState)
    requires
        inv(now, s),
    ensures
        inv(now, AState { outbox: Map::empty(), ..s }),
{
    let f = AState { outbox: Map::empty(), ..s };
    lemma_inv_pointwise(now, s);
    lemma_inv_pointwise(now, f);
    assert forall|id: Seq<char>| #[trigger] f.objects.contains_key(id) implies inv_obj(now, f, id) by {
        assert(inv_obj(now, s, id));
    }
}

/// The invariant at a later clock, on a state with nothing in its outbox:
/// its clauses read the clock only as a bound the state is under.
pub proof fn lemma_inv_later(now: nat, at: nat, s: AState)
    requires
        inv(now, s),
        now <= at,
        s.outbox == Map::<OutboxKey, AOutboxEntry>::empty(),
    ensures
        inv(at, s),
{
    lemma_inv_pointwise(now, s);
    lemma_inv_pointwise(at, s);
    assert forall|id: Seq<char>| #[trigger] s.objects.contains_key(id) implies inv_obj(at, s, id) by {
        assert(inv_obj(now, s, id));
        let p = s.objects[id];
        if p.project_promise(now).state != PromiseState::Pending {
            assert(p.project_promise(at).state != PromiseState::Pending);
        }
    }
}

pub proof fn lemma_project_inv(a: AState, x: Seq<char>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, with_objects(a, promise_timeout_objects(a, x, now))),
{
    if a.objects.contains_key(x) {
        lemma_project_legal(now, a, with_objects(a, promise_timeout_objects(a, x, now)), x);
    }
}

pub proof fn lemma_lease_inv(a: AState, x: Seq<char>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, with_objects(a, lease_timeout_objects(a, x, now))),
{
    if a.objects.contains_key(x) && lease_due(a.objects[x], now) {
        let p = a.objects[x];
        let at = p.task.unwrap().lease_timeout_at.unwrap() as nat;
        lemma_release_legal(now, a, with_objects(a, lease_timeout_objects(a, x, now)), x, at);
    }
}

pub proof fn lemma_callback_inv(a: AState, x: Seq<char>, y: Seq<char>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, callback_fn(a, x, y, now)),
{
    let b = callback_fn(a, x, y, now);
    if a.objects.contains_key(x) {
        let p = a.objects[x].project(now);
        let a1 = with_objects(a, a.objects.insert(x, p));
        lemma_project_inv(a, x, now);
        assert(a1 == with_objects(a, promise_timeout_objects(a, x, now)));
        if p.state == PromiseState::Pending || !p.callbacks.contains(y) {
            assert(b == a1);
        } else {
            lemma_inv_pointwise(now, a);
            assert(inv_obj(now, a, x));
            assert(a.objects[x].id == x);
            assert(!a.objects[x].callbacks.contains(a.objects[x].id));
            assert(p.callbacks == a.objects[x].callbacks);
            assert(y != x);
            let p2 = p.remove_callback(y);
            let a2 = with_objects(a1, a1.objects.insert(x, p2));
            assert(b.objects.contains_key(x) && b.objects[x] == p2);
            assert(b.schedules == a.schedules && b.outbox == a.outbox);
            assert forall|z: Seq<char>| z != x && z != y implies #[trigger] echod_kernel::external::unchanged_at(a, b, z) by {}
            assert(resumed_shape(now, a, b, x, y)) by {
                if a.objects.contains_key(y) {
                    let q = a2.objects[y].project(now);
                    assert(a2.objects[y] == a.objects[y]);
                    let m = a.objects[y].project(now);
                    assert(q == m);
                }
            }
            lemma_callback_legal(now, a, b, x, y, true);
        }
    } else {
        assert(b == a);
    }
}

pub proof fn lemma_callbacks_of_inv(a: AState, x: Seq<char>, aw: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, callbacks_of(a, x, aw, now)),
    decreases aw.len(),
{
    if aw.len() > 0 {
        lemma_callbacks_of_inv(a, x, aw.drop_last(), now);
        lemma_callback_inv(callbacks_of(a, x, aw.drop_last(), now), x, aw.last(), now);
    }
}

pub proof fn lemma_listener_inv(a: AState, x: Seq<char>, address: Seq<char>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, listener_fn(a, x, address, now)),
{
    let b = listener_fn(a, x, address, now);
    if a.objects.contains_key(x) {
        let p = a.objects[x].project(now);
        let a1 = with_objects(a, a.objects.insert(x, p));
        lemma_project_inv(a, x, now);
        assert(a1 == with_objects(a, promise_timeout_objects(a, x, now)));
        if p.state == PromiseState::Pending || !p.listeners.contains(address) {
            assert(b == a1);
        } else {
            assert(b.objects =~= a.objects.insert(x, p.remove_listener(address)));
            lemma_listener_legal(now, a, b, x, address);
        }
    } else {
        assert(b == a);
    }
}

pub proof fn lemma_listeners_of_inv(a: AState, x: Seq<char>, addresses: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, listeners_of(a, x, addresses, now)),
    decreases addresses.len(),
{
    if addresses.len() > 0 {
        lemma_listeners_of_inv(a, x, addresses.drop_last(), now);
        lemma_listener_inv(listeners_of(a, x, addresses.drop_last(), now), x, addresses.last(), now);
    }
}

pub proof fn lemma_retry_inv(a: AState, id: Seq<char>, now: nat, t: nat)
    requires
        inv(now, a),
        0 < t <= MAX_TIME,
    ensures
        inv(now, retry_fn(a, id, now, t)),
{
    if a.objects.contains_key(id) && retry_due(a.objects[id], now) {
        lemma_retry_legal(now, a, retry_fn(a, id, now, t), id, t);
    }
}

pub proof fn lemma_deadlines_inv(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, phase_deadlines(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_deadlines_inv(a, ids.drop_last(), now);
        lemma_project_inv(phase_deadlines(a, ids.drop_last(), now), ids.last(), now);
    }
}

pub proof fn lemma_leases_inv(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, phase_leases(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_leases_inv(a, ids.drop_last(), now);
        lemma_lease_inv(phase_leases(a, ids.drop_last(), now), ids.last(), now);
    }
}

pub proof fn lemma_callbacks_inv(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, phase_callbacks(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_callbacks_inv(a, ids.drop_last(), now);
        let a1 = phase_callbacks(a, ids.drop_last(), now);
        let x = ids.last();
        if a1.objects.contains_key(x) {
            lemma_callbacks_of_inv(a1, x, a1.objects[x].callbacks, now);
        }
    }
}

pub proof fn lemma_listeners_inv(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
    ensures
        inv(now, phase_listeners(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_listeners_inv(a, ids.drop_last(), now);
        let a1 = phase_listeners(a, ids.drop_last(), now);
        let x = ids.last();
        if a1.objects.contains_key(x) {
            lemma_listeners_of_inv(a1, x, a1.objects[x].listeners, now);
        }
    }
}

pub proof fn lemma_retries_inv(a: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    requires
        inv(now, a),
        0 < t <= MAX_TIME,
    ensures
        inv(now, phase_retries(a, ids, now, t)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_retries_inv(a, ids.drop_last(), now, t);
        lemma_retry_inv(phase_retries(a, ids.drop_last(), now, t), ids.last(), now, t);
    }
}

/// The sweep keeps the kernel's invariant: every step of it is a kernel step.
pub proof fn lemma_sweep_inv(a: AState, now: nat, t: nat)
    requires
        inv(now, a),
        0 < t <= MAX_TIME,
    ensures
        inv(now, sweep_fn(a, now, t)),
{
    let ids = ids_of(a);
    lemma_deadlines_inv(a, ids, now);
    let a1 = phase_deadlines(a, ids, now);
    lemma_leases_inv(a1, ids, now);
    let a2 = phase_leases(a1, ids, now);
    lemma_callbacks_inv(a2, ids, now);
    let a3 = phase_callbacks(a2, ids, now);
    lemma_listeners_inv(a3, ids, now);
    let a4 = phase_listeners(a3, ids, now);
    lemma_retries_inv(a4, ids, now, t);
}

// ------------------------------------------------- nothing due is nothing near

/// On a swept state under the invariant, every deadline, the kernel's or the
/// model's, is ahead of the clock.
pub proof fn lemma_swept_ahead(a: AState, now: nat)
    requires
        inv(now, a),
        swept(a, now),
    ensures
        forall|id: Seq<char>, t: nat| #[trigger] a.objects.contains_key(id) && #[trigger] deadline_at(a.objects[id], t) ==> t > now,
        forall|id: Seq<char>, t: nat| #[trigger] a.objects.contains_key(id) && #[trigger] mdeadline_at(a.objects[id], t) ==> t > now,
{
    lemma_inv_pointwise(now, a);
    assert forall|id: Seq<char>, t: nat| #![trigger a.objects.contains_key(id), deadline_at(a.objects[id], t)] #![trigger a.objects.contains_key(id), mdeadline_at(a.objects[id], t)] a.objects.contains_key(id) && (deadline_at(a.objects[id], t) || mdeadline_at(a.objects[id], t)) implies t > now by {
        assert(inv_obj(now, a, id));
        let p = a.objects[id];
        lemma_projected_obj(p, now);
        if p.state == PromiseState::Pending {
            assert(p.timeout_at > now);
            match p.task {
                None => {},
                Some(tk) => {
                    if tk.lease_timeout_at is Some {
                        assert(tk.state == TaskState::Acquired);
                        assert(!lease_due(p, now));
                        assert(tk.lease_timeout_at.unwrap() > now);
                    }
                    if tk.retry_timeout_at is Some {
                        assert(tk.state == TaskState::Pending);
                        assert(!retry_due(p, now));
                        assert(tk.retry_timeout_at.unwrap() > now);
                    }
                },
            }
        } else {
            match p.task {
                None => {},
                Some(tk) => {
                    assert(tk.state == TaskState::Fulfilled);
                    assert(tk.lease_timeout_at is None);
                    assert(tk.retry_timeout_at is None);
                },
            }
        }
    }
}

} // verus!
