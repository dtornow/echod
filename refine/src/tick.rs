//! The clock moves. Nothing the kernel arms a timer for has been left behind
//! (a sweep is armed no later than the bucket's next deadline, and nothing is
//! overdue), so the sweep at the old instant only reads internal promises
//! past their deadline, which nothing hangs on; projecting those earlier is
//! absorbed by the sweep at the new instant. The model ticks, then drains to
//! that sweep.

use vstd::prelude::*;

use accordant::refinement::{end, lemma_end_add, lemma_legal_add, lemma_project_add, matches, shows};
use accordant::semantics::{before, is_overdue, legal, overdue, project, step, tick, Cfg, Config, Execution, Lab, Label};
use accordant::{Event, Model, Sched};
use echod_kernel::external::with_objects;
use echod_kernel::internal::{lease_due, promise_timeout_objects, retry_due};
use echod_kernel::properties::{inv, inv_obj};
use echod_kernel::properties_proof::lemma_inv_pointwise;
use echod_kernel::steps::{deadline_at, has_deadline, is_next, lease_deadline, objects_deadline, promise_deadline, retry_deadline, strip};
use echod_kernel::store::AState;
use echod_kernel::tags::OType;
use echod_kernel::types::*;
use resonate::spec::*;
use resonate::{Dispatch, Resonate};

use crate::absorb::*;
use crate::canon::*;
use crate::drain::*;
use crate::machine::*;
use crate::sweep::*;
use crate::sweep_proof::*;
use crate::theorem::*;
use crate::trans::*;

verus! {

// ------------------------------------------------------- the least deadline

/// The least of an object's deadlines.
pub open spec fn obj_min(p: APromise) -> Option<nat> {
    let a = promise_deadline(p);
    let b = lease_deadline(p);
    let c = retry_deadline(p);
    let ab: Option<nat> = match (a, b) {
        (None, x) => x,
        (x, None) => x,
        (Some(x), Some(y)) => Some(if x <= y { x } else { y }),
    };
    match (ab, c) {
        (None, x) => x,
        (x, None) => x,
        (Some(x), Some(y)) => Some(if x <= y { x } else { y }),
    }
}

pub proof fn lemma_obj_min(p: APromise)
    ensures
        obj_min(p) is Some ==> deadline_at(p, obj_min(p).unwrap()),
        forall|t: nat| #[trigger] deadline_at(p, t) ==> obj_min(p) is Some && obj_min(p).unwrap() <= t,
{
}

/// The least deadline among the objects named.
pub open spec fn min_dl(a: AState, ids: Seq<Seq<char>>) -> Option<nat>
    decreases ids.len(),
{
    if ids.len() == 0 {
        None
    } else {
        let m0 = min_dl(a, ids.drop_last());
        let x = ids.last();
        let m1: Option<nat> = if a.objects.contains_key(x) { obj_min(a.objects[x]) } else { None };
        match (m0, m1) {
            (None, y) => y,
            (y, None) => y,
            (Some(u), Some(v)) => Some(if u <= v { u } else { v }),
        }
    }
}

pub proof fn lemma_min_dl(a: AState, ids: Seq<Seq<char>>)
    ensures
        min_dl(a, ids) is Some ==> exists|id: Seq<char>| ids.contains(id) && #[trigger] a.objects.contains_key(id) && deadline_at(a.objects[id], min_dl(a, ids).unwrap()),
        forall|id: Seq<char>, t: nat| ids.contains(id) && #[trigger] a.objects.contains_key(id) && #[trigger] deadline_at(a.objects[id], t) ==> min_dl(a, ids) is Some && min_dl(a, ids).unwrap() <= t,
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_min_dl(a, ids.drop_last());
        let x = ids.last();
        if a.objects.contains_key(x) {
            lemma_obj_min(a.objects[x]);
        }
        assert(ids.contains(x)) by {
            assert(ids[ids.len() - 1] == x);
        }
        assert forall|z: Seq<char>| ids.drop_last().contains(z) implies ids.contains(z) by {
            let i = choose|i: int| 0 <= i < ids.drop_last().len() && ids.drop_last()[i] == z;
            assert(ids[i] == z);
        }
        assert forall|id: Seq<char>, t: nat| ids.contains(id) && #[trigger] a.objects.contains_key(id) && #[trigger] deadline_at(a.objects[id], t) implies min_dl(a, ids) is Some && min_dl(a, ids).unwrap() <= t by {
            lemma_contains_split(ids, id);
        }
    }
}

/// A bucket with a deadline has a least one.
pub proof fn lemma_least_deadline(a: AState)
    requires
        a.objects.dom().finite(),
        a.schedules == Map::<Seq<char>, ASchedule>::empty(),
        exists|t: nat| #[trigger] has_deadline(strip(a), t),
    ensures
        exists|d: nat| #[trigger] is_next(strip(a), d),
{
    lemma_ids_cover(a);
    lemma_min_dl(a, ids_of(a));
    let t0 = choose|t: nat| #[trigger] has_deadline(strip(a), t);
    assert(objects_deadline(a.objects, t0));
    let id0 = choose|id: Seq<char>| #[trigger] a.objects.contains_key(id) && deadline_at(a.objects[id], t0);
    assert(min_dl(a, ids_of(a)) is Some);
    let d = min_dl(a, ids_of(a)).unwrap();
    assert(has_deadline(strip(a), d));
    assert forall|u: nat| has_deadline(strip(a), u) implies d <= u by {
        assert(objects_deadline(a.objects, u));
        let id = choose|id: Seq<char>| #[trigger] a.objects.contains_key(id) && deadline_at(a.objects[id], u);
    }
    assert(is_next(strip(a), d));
}

/// With a sweep armed no later than the next deadline and nothing overdue,
/// no deadline has passed.
pub proof fn lemma_deadlines_ahead(cfg: Concrete, x: Cfg<Concrete>)
    requires
        raw_of(x).objects.dom().finite(),
        raw_of(x).schedules == Map::<Seq<char>, ASchedule>::empty(),
        sweep_armed(x),
        !overdue(cfg, x),
    ensures
        forall|id: Seq<char>, t: nat| #[trigger] raw_of(x).objects.contains_key(id) && #[trigger] deadline_at(raw_of(x).objects[id], t) ==> t > x.now,
{
    let raw = raw_of(x);
    assert forall|id: Seq<char>, t: nat| #[trigger] raw.objects.contains_key(id) && #[trigger] deadline_at(raw.objects[id], t) implies t > x.now by {
        assert(has_deadline(strip(raw), t));
        lemma_least_deadline(raw);
        let d = choose|d: nat| is_next(strip(raw), d);
        assert(next_deadline(raw) is Some);
        let d2 = next_deadline(raw).unwrap();
        assert(is_next(strip(raw), d2));
        assert(d2 <= t);
        assert(timer_by(x.internals, d2));
        let i = choose|i: int| 0 <= i < x.internals.len() && match #[trigger] x.internals[i] {
            Sched::Timer(u, _) => u as nat <= d2,
            Sched::Later(_) => false,
        };
        match x.internals[i] {
            Sched::Timer(u, req) => {
                assert(cfg.spec_internal(req, x.state, x.now).len() == 1);
                if u <= x.now {
                    assert(is_overdue(cfg, x, i));
                    assert(false);
                }
            },
            Sched::Later(_) => {},
        }
    }
}

// ---------------------------------------------------------- what the sweep keeps

/// The sweep keeps the lease rule.
pub proof fn lemma_sweep_leases(a: AState, now: nat, t: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
        0 < t <= MAX_TIME,
    ensures
        leases_from_ttl(sweep_fn(a, now, t)),
{
    let ids = ids_of(a);
    lemma_phase_deadlines_leases(a, ids, now);
    let a1 = phase_deadlines(a, ids, now);
    lemma_phase_leases_leases(a1, ids, now);
    let a2 = phase_leases(a1, ids, now);
    lemma_phase_callbacks_leases(a2, ids, now);
    let a3 = phase_callbacks(a2, ids, now);
    lemma_phase_listeners_leases(a3, ids, now);
    let a4 = phase_listeners(a3, ids, now);
    lemma_phase_retries_leases(a4, ids, now, t);
}

pub proof fn lemma_phase_deadlines_leases(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
    ensures
        inv(now, phase_deadlines(a, ids, now)),
        leases_from_ttl(phase_deadlines(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_phase_deadlines_leases(a, ids.drop_last(), now);
        lemma_project_keeps(phase_deadlines(a, ids.drop_last(), now), ids.last(), now);
    }
}

/// A lease step keeps the rule: a released task has no lease.
pub proof fn lemma_lease_keeps_leases(a: AState, x: Seq<char>, now: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
    ensures
        inv(now, with_objects(a, echod_kernel::internal::lease_timeout_objects(a, x, now))),
        leases_from_ttl(with_objects(a, echod_kernel::internal::lease_timeout_objects(a, x, now))),
{
    lemma_lease_inv(a, x, now);
    let b = with_objects(a, echod_kernel::internal::lease_timeout_objects(a, x, now));
    if a.objects.contains_key(x) && lease_due(a.objects[x], now) {
        assert(b.objects.dom() =~= a.objects.dom());
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies match b.objects[id].task {
            Some(t) => (t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap(),
            None => true,
        } by {
            if id != x {
                assert(b.objects[id] == a.objects[id]);
            }
        }
    }
}

pub proof fn lemma_phase_leases_leases(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
    ensures
        inv(now, phase_leases(a, ids, now)),
        leases_from_ttl(phase_leases(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_phase_leases_leases(a, ids.drop_last(), now);
        lemma_lease_keeps_leases(phase_leases(a, ids.drop_last(), now), ids.last(), now);
    }
}

pub proof fn lemma_callbacks_of_leases(a: AState, x: Seq<char>, aw: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
    ensures
        inv(now, callbacks_of(a, x, aw, now)),
        leases_from_ttl(callbacks_of(a, x, aw, now)),
    decreases aw.len(),
{
    if aw.len() > 0 {
        lemma_callbacks_of_leases(a, x, aw.drop_last(), now);
        lemma_callback_keeps(callbacks_of(a, x, aw.drop_last(), now), x, aw.last(), now);
    }
}

pub proof fn lemma_phase_callbacks_leases(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
    ensures
        inv(now, phase_callbacks(a, ids, now)),
        leases_from_ttl(phase_callbacks(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_phase_callbacks_leases(a, ids.drop_last(), now);
        let a1 = phase_callbacks(a, ids.drop_last(), now);
        let x = ids.last();
        if a1.objects.contains_key(x) {
            lemma_callbacks_of_leases(a1, x, a1.objects[x].callbacks, now);
        }
    }
}

/// A listener step keeps the rule: it reads the object and edits its listeners.
pub proof fn lemma_listener_keeps_leases(a: AState, x: Seq<char>, address: Seq<char>, now: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
    ensures
        inv(now, listener_fn(a, x, address, now)),
        leases_from_ttl(listener_fn(a, x, address, now)),
{
    lemma_listener_inv(a, x, address, now);
    let b = listener_fn(a, x, address, now);
    if a.objects.contains_key(x) {
        lemma_project_keeps(a, x, now);
        let p = a.objects[x].project(now);
        let a1 = with_objects(a, a.objects.insert(x, p));
        assert(a1 == with_objects(a, promise_timeout_objects(a, x, now)));
        assert(leases_from_ttl(a1));
        if p.state == PromiseState::Pending || !p.listeners.contains(address) {
            assert(b == a1);
        } else {
            assert(b.objects.dom() =~= a1.objects.dom());
            assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies match b.objects[id].task {
                Some(t) => (t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap(),
                None => true,
            } by {
                assert(b.objects[id].task == a1.objects[id].task);
            }
        }
    }
}

pub proof fn lemma_listeners_of_leases(a: AState, x: Seq<char>, l: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
    ensures
        inv(now, listeners_of(a, x, l, now)),
        leases_from_ttl(listeners_of(a, x, l, now)),
    decreases l.len(),
{
    if l.len() > 0 {
        lemma_listeners_of_leases(a, x, l.drop_last(), now);
        lemma_listener_keeps_leases(listeners_of(a, x, l.drop_last(), now), x, l.last(), now);
    }
}

pub proof fn lemma_phase_listeners_leases(a: AState, ids: Seq<Seq<char>>, now: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
    ensures
        inv(now, phase_listeners(a, ids, now)),
        leases_from_ttl(phase_listeners(a, ids, now)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_phase_listeners_leases(a, ids.drop_last(), now);
        let a1 = phase_listeners(a, ids.drop_last(), now);
        let x = ids.last();
        if a1.objects.contains_key(x) {
            lemma_listeners_of_leases(a1, x, a1.objects[x].listeners, now);
        }
    }
}

/// A retry step keeps the rule: it moves the offer only.
pub proof fn lemma_retry_keeps_leases(a: AState, x: Seq<char>, now: nat, t: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
        0 < t <= MAX_TIME,
    ensures
        inv(now, retry_fn(a, x, now, t)),
        leases_from_ttl(retry_fn(a, x, now, t)),
{
    lemma_retry_inv(a, x, now, t);
    let b = retry_fn(a, x, now, t);
    if a.objects.contains_key(x) && retry_due(a.objects[x], now) {
        assert(b.objects.dom() =~= a.objects.dom());
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) implies match b.objects[id].task {
            Some(tk) => (tk.lease_timeout_at is Some && tk.ttl is Some) ==> tk.lease_timeout_at.unwrap() >= tk.ttl.unwrap(),
            None => true,
        } by {
            if id != x {
                assert(b.objects[id] == a.objects[id]);
            } else {
                let tk = a.objects[x].task.unwrap();
                assert(b.objects[x].task == Some(tk.rearm(now, t)));
            }
        }
    }
}

pub proof fn lemma_phase_retries_leases(a: AState, ids: Seq<Seq<char>>, now: nat, t: nat)
    requires
        inv(now, a),
        leases_from_ttl(a),
        0 < t <= MAX_TIME,
    ensures
        inv(now, phase_retries(a, ids, now, t)),
        leases_from_ttl(phase_retries(a, ids, now, t)),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_phase_retries_leases(a, ids.drop_last(), now, t);
        lemma_retry_keeps_leases(phase_retries(a, ids.drop_last(), now, t), ids.last(), now, t);
    }
}

// ----------------------------------------------------------- the quiet sweep

pub proof fn lemma_fold_sends_empty(ids: Seq<Seq<char>>, f: spec_fn(Seq<char>) -> Seq<DispatchV>)
    requires
        forall|x: Seq<char>| ids.contains(x) ==> #[trigger] f(x) == Seq::<DispatchV>::empty(),
    ensures
        fold_sends(ids, f) == Seq::<DispatchV>::empty(),
    decreases ids.len(),
{
    if ids.len() > 0 {
        assert forall|x: Seq<char>| ids.drop_last().contains(x) implies ids.contains(x) by {
            let i = choose|i: int| 0 <= i < ids.drop_last().len() && ids.drop_last()[i] == x;
            assert(ids[i] == x);
        }
        lemma_fold_sends_empty(ids.drop_last(), f);
        assert(ids.contains(ids.last())) by {
            assert(ids[ids.len() - 1] == ids.last());
        }
        assert(fold_sends(ids, f) =~= Seq::<DispatchV>::empty());
    }
}

/// On a bucket with nothing the kernel times out owed, every callback and
/// listener spent, and no deadline passed, the sweep only reads the objects:
/// the internal promises past their deadlines settle, nothing else moves,
/// nothing is sent.
#[verifier::rlimit(200)]
pub proof fn lemma_quiet_sweep(raw: AState, now: nat, t: nat)
    requires
        inv(now, raw),
        raw.objects.dom().finite(),
        callbacks_spent(raw),
        listeners_spent(raw),
        0 < t <= MAX_TIME,
        forall|id: Seq<char>, u: nat| #[trigger] raw.objects.contains_key(id) && #[trigger] deadline_at(raw.objects[id], u) ==> u > now,
    ensures
        sweep_fn(raw, now, t).objects == phase_deadlines(raw, ids_of(raw), now).objects,
        sweep_fn(raw, now, t).schedules == phase_deadlines(raw, ids_of(raw), now).schedules,
        sweep_sends(raw, now, t) == Seq::<DispatchV>::empty(),
{
    let ids = ids_of(raw);
    lemma_ids_cover(raw);
    raw.objects.dom().lemma_to_seq_no_duplicates();
    lemma_inv_pointwise(now, raw);
    // phase 1: every object read
    lemma_deadlines_exact(raw, ids, now);
    lemma_deadlines_phase(raw, ids, now);
    lemma_deadlines_inv(raw, ids, now);
    let a1 = phase_deadlines(raw, ids, now);
    assert(projected(a1, now));
    assert forall|id: Seq<char>| #[trigger] raw.objects.contains_key(id) implies a1.objects[id] == raw.objects[id].project(now) by {}
    // what the read objects are: a pending one is ahead of its deadline, or
    // internal and alone; a settled one owes nothing
    assert forall|id: Seq<char>| #[trigger] raw.objects.contains_key(id) implies {
        let p = raw.objects[id];
        let q = a1.objects[id];
        &&& !lease_due(q, now)
        &&& !retry_due(q, now)
        &&& (q.state != PromiseState::Pending ==> q.callbacks.len() == 0 && q.listeners.len() == 0)
    } by {
        let p = raw.objects[id];
        let q = a1.objects[id];
        assert(inv_obj(now, raw, id));
        if p.state == PromiseState::Pending && p.timeout_at <= now {
            // past its deadline, unseen by the kernel: an internal promise
            assert(promise_deadline(p) is None) by {
                if promise_deadline(p) is Some {
                    assert(deadline_at(p, p.timeout_at as nat));
                }
            }
            assert(p.otype() == OType::Internal);
            assert(p.callbacks.len() == 0 && p.listeners.len() == 0);
            assert(q.state != PromiseState::Pending);
            assert(q.callbacks == p.callbacks && q.listeners == p.listeners);
            match q.task {
                None => {},
                Some(tk) => {
                    assert(tk.state == TaskState::Fulfilled);
                },
            }
        } else {
            assert(q == p) by {
                if p.state != PromiseState::Pending {
                    match p.task {
                        None => {},
                        Some(tk) => {
                            assert(tk.state == TaskState::Fulfilled);
                        },
                    }
                }
            }
            if lease_due(p, now) {
                let e = p.task.unwrap().lease_timeout_at.unwrap() as nat;
                assert(lease_deadline(p) == Some(e));
                assert(deadline_at(p, e));
                assert(false);
            }
            if retry_due(p, now) {
                let r = p.task.unwrap().retry_timeout_at.unwrap() as nat;
                assert(retry_deadline(p) == Some(r));
                assert(deadline_at(p, r));
                assert(false);
            }
        }
    }
    // phase 2: no lease due
    lemma_leases_exact(a1, ids, now);
    let a2 = phase_leases(a1, ids, now);
    assert(a2.objects =~= a1.objects);
    assert(a2 == a1);
    // phase 3: no settled object holds a callback
    lemma_callbacks_exact(a2, ids, now);
    let a3 = phase_callbacks(a2, ids, now);
    assert forall|id: Seq<char>| #[trigger] a2.objects.contains_key(id) implies a3.objects[id] == a2.objects[id] by {
        let q = a2.objects[id];
        assert forall|k: int| 0 <= k < ids.len() implies !awaits(a2, #[trigger] ids[k], id, now) by {
            let x = ids[k];
            if a2.objects.contains_key(x) && a2.objects[x].project(now).state != PromiseState::Pending {
                assert(a2.objects[x].callbacks.len() == 0);
            }
        }
        match q.task {
            None => {},
            Some(tk) => {
                lemma_resumed_none(a2, id, ids, tk, now);
                assert(resumed(a2, id, ids, tk, now) == tk);
            },
        }
        if q.state != PromiseState::Pending {
            assert(q.callbacks =~= Seq::<Seq<char>>::empty());
        }
        assert(a3.objects[id] == APromise {
            callbacks: if ids.contains(id) && q.state != PromiseState::Pending { Seq::empty() } else { q.callbacks },
            task: match q.task {
                None => None,
                Some(tk) => Some(resumed(a2, id, ids, tk, now)),
            },
            ..q
        });
    }
    assert(a3.objects =~= a2.objects);
    assert(a3 == a2);
    // phase 4: no settled object holds a listener; nothing sent
    lemma_listeners_exact(a3, ids, now);
    let a4 = phase_listeners(a3, ids, now);
    assert forall|id: Seq<char>| #[trigger] a3.objects.contains_key(id) implies a4.objects[id] == a3.objects[id] by {
        let q = a3.objects[id];
        if q.state != PromiseState::Pending {
            assert(q.listeners =~= Seq::<Seq<char>>::empty());
        }
        assert(a4.objects[id] == APromise {
            listeners: if ids.contains(id) && q.state != PromiseState::Pending { Seq::empty() } else { q.listeners },
            ..q
        });
    }
    assert(a4.objects =~= a3.objects);
    assert(a4.schedules == a3.schedules);
    assert forall|x: Seq<char>| ids.contains(x) implies #[trigger] unblocks_a(a3, x) == Seq::<DispatchV>::empty() by {
        if a3.objects.contains_key(x) && a3.objects[x].state != PromiseState::Pending {
            assert(a3.objects[x].listeners.len() == 0);
            assert(a3.objects[x].listeners.map_values(|address: Seq<char>| unblock_of(a3.objects[x], address)) =~= Seq::<DispatchV>::empty());
        }
    }
    lemma_fold_sends_empty(ids, |x: Seq<char>| unblocks_a(a3, x));
    // phase 5: no offer due; nothing sent
    lemma_retries_exact(a4, ids, now, t);
    let a5 = phase_retries(a4, ids, now, t);
    assert(a5.objects =~= a4.objects);
    assert forall|id: Seq<char>| ids.contains(id) implies #[trigger] execute_a(a4, id, now) == Seq::<DispatchV>::empty() by {}
    lemma_fold_sends_empty(ids, |id: Seq<char>| execute_a(a4, id, now));
    assert(sweep_sends(raw, now, t) =~= Seq::<DispatchV>::empty());
    assert(a5.objects == a1.objects);
    assert(a5.schedules == a1.schedules);
}


// ------------------------------------------ the early reads, absorbed later

/// Projecting objects at `now` is absorbed by the sweep at any `at >= now`.
pub proof fn lemma_project_absorb_all(raw: AState, ids: Seq<Seq<char>>, now: nat, at: nat, t: nat)
    requires
        inv(now, raw),
        raw.outbox == Map::<OutboxKey, AOutboxEntry>::empty(),
        raw.objects.dom().finite(),
        now <= at,
        0 < t <= MAX_TIME,
    ensures
        ({
            let b = phase_deadlines(raw, ids, now);
            &&& inv(now, b)
            &&& inv(at, b)
            &&& b.outbox == raw.outbox
            &&& b.objects.dom() == raw.objects.dom()
            &&& sweep_fn(b, at, t).objects == sweep_fn(raw, at, t).objects
            &&& sweep_fn(b, at, t).schedules == sweep_fn(raw, at, t).schedules
            &&& sweep_sends(b, at, t) == sweep_sends(raw, at, t)
        }),
    decreases ids.len(),
{
    lemma_inv_later(now, at, raw);
    if ids.len() > 0 {
        lemma_project_absorb_all(raw, ids.drop_last(), now, at, t);
        let b0 = phase_deadlines(raw, ids.drop_last(), now);
        let x = ids.last();
        let b1 = phase_deadlines(raw, ids, now);
        assert(b1 == with_objects(b0, promise_timeout_objects(b0, x, now)));
        lemma_project_inv(b0, x, now);
        assert(b1.outbox == raw.outbox);
        lemma_inv_later(now, at, b1);
        absorb_project(b0, x, now, at, t);
        if b0.objects.contains_key(x) {
            assert(b1.objects.dom() =~= b0.objects.dom());
        }
    }
}

// ------------------------------------------------------------------ the tick

/// The clock moves: the model ticks and drains to the sweep at the new instant.
#[verifier::rlimit(120)]
pub proof fn tick_matched(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        dial_ok(cfg),
        bounded(l),
        rel(cfg, x, s),
        tick(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    let a = abstract_of(cfg);
    let at = match l { Label::Obs(Event::Clock { at }) => at, _ => 0 };
    assert(l == Label::<resonate::Request, resonate::Response, Dispatch>::Obs(Event::Clock { at }));
    assert(x.now <= at && !overdue(cfg, x) && y == Config { now: at, ..x });
    assert(at <= MAX_TIME);
    let now = x.now;
    let n = now as nat;
    let m = at as nat;
    let rt = cfg.retry_timeout as nat;
    let raw = raw_of(x);
    let ids = ids_of(raw);
    // nothing the kernel times has passed
    lemma_deadlines_ahead(cfg, x);
    // so the sweep at `now` only reads: its result is the projections
    lemma_quiet_sweep(raw, n, rt);
    let a0 = sweep_fn(raw, n, rt);
    let pd = phase_deadlines(raw, ids, n);
    lemma_project_absorb_all(raw, ids, n, m, rt);
    assert(fresh(a0) == pd) by {
        assert(fresh(a0).objects == pd.objects);
        assert(fresh(a0).schedules == pd.schedules);
        assert(fresh(a0).outbox =~= pd.outbox);
    }
    // the model ticks
    let s1 = Config { now: at, ..s };
    no_overdue(cfg, x, s);
    assert(tick(a, s, l, s1));
    // and is in the drain's relation with the projections
    lemma_sweep_inv(raw, n, rt);
    lemma_inv_fresh(n, a0);
    lemma_inv_later(n, m, pd);
    lemma_sweep_leases(raw, n, rt);
    lemma_sweep_swept(raw, n, rt);
    assert(swept(a0, n));
    assert(swept(pd, n));
    lemma_swept_ahead(pd, n);
    assert(s1.state@ == translate(pd)) by {
        assert(translate(pd) == translate(a0));
    }
    assert(drain_inv(cfg, pd, s1)) by {
        assert(work_wf(pd, s1.internals)) by {
            assert forall|i: int| 0 <= i < s1.internals.len() implies {
                let wi = item_ids(#[trigger] s1.internals[i]);
                &&& is_on(accordant::semantics::req_of(s1.internals[i]))
                &&& wi.no_duplicates()
                &&& (s1.internals[i] is Timer ==> wi.len() == 1)
                &&& (s1.internals[i] is Later ==> 1 <= wi.len() <= 2 && pd.objects.contains_key(wi[0]) && pd.objects[wi[0]].state != PromiseState::Pending)
            } by {
                match s1.internals[i] {
                    Sched::Timer(tt, stp) => {
                        assert(item_ids(s1.internals[i]) == on_ids(stp));
                    },
                    Sched::Later(_) => {},
                }
            }
        }
        // what is due at `at` had its timer, now ready
        assert forall|id: Seq<char>| pending_due(pd, id, at) implies covered(s1.internals, at, id) by {
            let p = pd.objects[id];
            assert(mdeadline_at(p, p.timeout_at as nat));
            assert(p.timeout_at as nat > n);
            let i = choose|i: int| 0 <= i < s.internals.len() && #[trigger] s.internals[i] == Sched::Timer((p.timeout_at as nat) as u64, lift_internal(InternalV::On(seq![id])));
            axiom_realised(empty_server_v(), ResponseV::Status(0), InternalV::On(seq![id]), DispatchV::Execute { id: Seq::empty(), version: 0 });
            assert(item_ids(s.internals[i]) == seq![id]);
            assert(seq![id].contains(id)) by {
                assert(seq![id][0] == id);
            }
            assert(ready_item(s1.internals[i], at));
        }
        assert forall|id: Seq<char>| #[trigger] pd.objects.contains_key(id) && lease_due(pd.objects[id], m) implies covered(s1.internals, at, id) by {
            let p = pd.objects[id];
            let e = p.task.unwrap().lease_timeout_at.unwrap() as nat;
            assert(mdeadline_at(p, e));
            assert(e > n);
            let i = choose|i: int| 0 <= i < s.internals.len() && #[trigger] s.internals[i] == Sched::Timer(e as u64, lift_internal(InternalV::On(seq![id])));
            axiom_realised(empty_server_v(), ResponseV::Status(0), InternalV::On(seq![id]), DispatchV::Execute { id: Seq::empty(), version: 0 });
            assert(item_ids(s.internals[i]) == seq![id]);
            assert(seq![id].contains(id)) by {
                assert(seq![id][0] == id);
            }
            assert(ready_item(s1.internals[i], at));
        }
        assert forall|id: Seq<char>| #[trigger] pd.objects.contains_key(id) && retry_due(pd.objects[id], m) implies covered(s1.internals, at, id) by {
            let p = pd.objects[id];
            let r = p.task.unwrap().retry_timeout_at.unwrap() as nat;
            assert(mdeadline_at(p, r));
            assert(r > n);
            let i = choose|i: int| 0 <= i < s.internals.len() && #[trigger] s.internals[i] == Sched::Timer(r as u64, lift_internal(InternalV::On(seq![id])));
            axiom_realised(empty_server_v(), ResponseV::Status(0), InternalV::On(seq![id]), DispatchV::Execute { id: Seq::empty(), version: 0 });
            assert(item_ids(s.internals[i]) == seq![id]);
            assert(seq![id].contains(id)) by {
                assert(seq![id][0] == id);
            }
            assert(ready_item(s1.internals[i], at));
        }
        assert forall|xx: Seq<char>, w: Seq<char>| #[trigger] pd.objects.contains_key(xx) && pd.objects[xx].state != PromiseState::Pending && #[trigger] pd.objects[xx].callbacks.contains(w)
            implies covered2(s1.internals, at, xx, w) by {
            assert(pd.objects[xx].callbacks.len() == 0);
        }
        assert forall|xx: Seq<char>| #[trigger] pd.objects.contains_key(xx) && pd.objects[xx].state != PromiseState::Pending && pd.objects[xx].listeners.len() > 0 implies covered(s1.internals, at, xx) by {
            assert(pd.objects[xx].listeners.len() == 0);
        }
        assert forall|id: Seq<char>, tt: nat| #[trigger] pd.objects.contains_key(id) && #[trigger] mdeadline_at(pd.objects[id], tt) && tt > at implies mdeadline_at_timer(s1.internals, id, tt) by {
            assert(tt > n);
        }
    }
    // the model drains
    lemma_drain(cfg, pd, s1);
    let (mid2, t, bn) = choose|mid2: Execution<Resonate>, t: Cfg<Resonate>, bn: AState| #[trigger] drained(cfg, pd, s1, mid2, t, bn);
    // the tick, then the drain, shows the clock
    let first: Execution<Resonate> = seq![(l, s1)];
    assert(legal(a, s, first)) by {
        assert forall|k: int| 0 <= k < first.len() implies #[trigger] step(a, before::<Resonate>(s, first, k), first[k].0, first[k].1) by {
            assert(k == 0);
            assert(before::<Resonate>(s, first, 0) == s);
        }
    }
    assert(end::<Resonate>(s, first) == s1);
    assert(project::<Resonate>(first) =~= shows(l)) by {
        assert(first.len() == 1);
        assert(first.last() == (l, s1));
        assert(first.drop_last() =~= Seq::<(Lab<Resonate>, Cfg<Resonate>)>::empty());
        assert(project::<Resonate>(first.drop_last()) =~= Seq::<Event<resonate::Request, resonate::Response, Dispatch>>::empty());
    }
    let mid = first + mid2;
    lemma_legal_add(a, s, first, mid2);
    lemma_project_add::<Resonate>(first, mid2);
    lemma_end_add::<Resonate>(s, first, mid2);
    assert(project::<Resonate>(mid) =~= shows(l));
    assert(matches(a, s, l, t));
    // and the relation holds at the new instant
    let sw = sweep_fn(raw, m, rt);
    assert(bn.objects == sw.objects);
    lemma_sweep_swept(raw, m, rt);
    assert(pd.schedules == raw.schedules);
    assert(bn.schedules == sw.schedules);
    assert(translate(bn) == translate(sw));
    lemma_inv_later(n, m, raw);
    assert(sweep_sends(pd, m, rt) == sweep_sends(raw, m, rt));
    assert((y.sent + lift_dispatches(sweep_sends(raw, m, rt))).to_multiset().subset_of(t.sent.to_multiset())) by {
        assert(lift_dispatches(sweep_sends(raw, n, rt)) =~= Seq::<Dispatch>::empty());
        assert((x.sent + Seq::<Dispatch>::empty()) =~= x.sent);
        assert(x.sent.to_multiset().subset_of(s.sent.to_multiset()));
        let ld = lift_dispatches(sweep_sends(raw, m, rt)).to_multiset();
        assert((y.sent + lift_dispatches(sweep_sends(raw, m, rt))).to_multiset() == x.sent.to_multiset().add(ld));
        assert(t.sent.to_multiset() == s.sent.to_multiset().add(ld));
        assert forall|d: Dispatch| x.sent.to_multiset().add(ld).count(d) <= s.sent.to_multiset().add(ld).count(d) by {}
    }
    assert(timers_cover(t.internals, sw, at)) by {
        assert forall|id: Seq<char>, tt: nat| #[trigger] sw.objects.contains_key(id) && #[trigger] mdeadline_at(sw.objects[id], tt) implies mdeadline_at_timer(t.internals, id, tt) by {
            assert(bn.objects.contains_key(id) && mdeadline_at(bn.objects[id], tt));
        }
    }
    assert(rel(cfg, y, t));
}

} // verus!
