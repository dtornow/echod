//! The sweep's two facts: on a state with nothing due it changes nothing
//! (`lemma_sweep_idem`), and it leaves nothing due (`lemma_sweep_swept`). The
//! second is what makes the relation's "abstract state is the sweep of the
//! concrete one" stable under the concrete machine's own sweeps.

use vstd::prelude::*;

use echod_kernel::external::with_objects;
use echod_kernel::internal::{lease_due, lease_timeout_objects, promise_timeout_objects, retry_due, retry_timeout_objects};
use echod_kernel::object::without;
use echod_kernel::store::AState;
use echod_kernel::types::*;

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

/// ADMITTED. On a finite bucket, within the kernel's doors, the sweep leaves
/// nothing due: each phase establishes its clause of `swept_obj` on every
/// object and keeps the clauses of the phases before it.
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
    admit();
}

} // verus!
