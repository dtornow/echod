//! The kernel's steps under translation: each is the model's corresponding
//! step on the translated state. A projection is the model's timeout; a
//! callback step its resume; a lease step its release; the listener steps
//! of an object its unblocks; a retry step its offer.

use vstd::prelude::*;

use echod_kernel::external::with_objects;
use echod_kernel::internal::{lease_due, lease_timeout_objects, promise_timeout_objects, retry_due};
use echod_kernel::object::{lemma_next_offer, next_offer, without};
use echod_kernel::object_proof::lemma_without_contains;
use echod_kernel::properties::{inv, inv_obj, no_dups, opt_or_zero};
use echod_kernel::properties_proof::lemma_inv_pointwise;
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::twins::*;
use resonate::{PState, Resonate, TState, Time};

use accordant::Sched;

use crate::canon::*;
use crate::onstep::*;
use crate::sweep::*;
use crate::sweep_proof::*;
use crate::theorem::{promise_v, task_v, translate};
use crate::translate::*;

verus! {

/// A lease ends no earlier than its length: what the model's lease start is
/// recovered from.
pub open spec fn leases_from_ttl(a: AState) -> bool {
    forall|id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> match a.objects[id].task {
        Some(t) => (t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap(),
        None => true,
    }
}

// ----------------------------------------------------------- reading maps

/// What the translation holds at a key.
pub proof fn lemma_translate_reads(a: AState, id: Seq<char>)
    ensures
        translate(a).promises.contains_key(id) == a.objects.contains_key(id),
        a.objects.contains_key(id) ==> translate(a).promises[id] == promise_v(a.objects[id]),
        translate(a).tasks.contains_key(id) == (a.objects.contains_key(id) && a.objects[id].task is Some),
        a.objects.contains_key(id) && a.objects[id].task is Some ==> translate(a).tasks[id] == task_v(a.objects[id].task.unwrap()),
{
}

/// Writing one object writes its promise and its task.
pub proof fn lemma_translate_insert(a: AState, id: Seq<char>, p: APromise)
    ensures
        ({
            let n = translate(a);
            let n2 = translate(with_objects(a, a.objects.insert(id, p)));
            &&& n2.promises == n.promises.insert(id, promise_v(p))
            &&& n2.tasks == (match p.task {
                Some(t) => n.tasks.insert(id, task_v(t)),
                None => n.tasks.remove(id),
            })
            &&& n2.schedules == n.schedules
        }),
{
    let a2 = with_objects(a, a.objects.insert(id, p));
    assert(translate(a2).promises =~= translate(a).promises.insert(id, promise_v(p)));
    match p.task {
        Some(t) => {
            assert(translate(a2).tasks =~= translate(a).tasks.insert(id, task_v(t)));
        },
        None => {
            assert(translate(a2).tasks =~= translate(a).tasks.remove(id));
        },
    }
}

/// A list less an element, as a set.
pub proof fn lemma_without_to_set(s: Seq<Seq<char>>, w: Seq<char>)
    ensures
        without(s, w).to_set() == s.to_set().remove(w),
{
    broadcast use Seq::to_set_ensures;
    assert forall|c: Seq<char>| without(s, w).to_set().contains(c) == s.to_set().remove(w).contains(c) by {
        lemma_without_contains(s, w, c);
    }
    assert(without(s, w).to_set() =~= s.to_set().remove(w));
}

/// Two lists without duplicates and with the same elements, mapped by an
/// injection, are the same multiset.
pub proof fn lemma_map_nodup_same_set(s1: Seq<Seq<char>>, s2: Seq<Seq<char>>, f: spec_fn(Seq<char>) -> DispatchV)
    requires
        s1.no_duplicates(),
        s2.no_duplicates(),
        s1.to_set() == s2.to_set(),
        vstd::relations::injective(f),
    ensures
        s1.map_values(f).to_multiset() == s2.map_values(f).to_multiset(),
{
    broadcast use Seq::to_set_ensures;
    broadcast use vstd::seq_lib::to_multiset_contains;
    broadcast use vstd::multiset::group_multiset_axioms;
    let m1 = s1.map_values(f);
    let m2 = s2.map_values(f);
    s1.lemma_no_duplicates_injective(f);
    s2.lemma_no_duplicates_injective(f);
    m1.lemma_multiset_has_no_duplicates();
    m2.lemma_multiset_has_no_duplicates();
    assert forall|d: DispatchV| m1.contains(d) == m2.contains(d) by {
        if m1.contains(d) {
            let i = choose|i: int| 0 <= i < m1.len() && m1[i] == d;
            assert(s1.contains(s1[i]));
            assert(s2.to_set().contains(s1[i]));
            let j = choose|j: int| 0 <= j < s2.len() && s2[j] == s1[i];
            assert(m2[j] == d);
        }
        if m2.contains(d) {
            let i = choose|i: int| 0 <= i < m2.len() && m2[i] == d;
            assert(s2.contains(s2[i]));
            assert(s1.to_set().contains(s2[i]));
            let j = choose|j: int| 0 <= j < s1.len() && s1[j] == s2[i];
            assert(m1[j] == d);
        }
    }
    assert forall|d: DispatchV| m1.to_multiset().count(d) == m2.to_multiset().count(d) by {
        if m1.contains(d) {
            assert(m1.to_multiset().count(d) == 1);
            assert(m2.to_multiset().count(d) == 1);
        } else {
            assert(m1.to_multiset().count(d) == 0);
            assert(m2.to_multiset().count(d) == 0);
        }
    }
    assert(m1.to_multiset() =~= m2.to_multiset());
}

/// A list's elements as a set has an element iff the list has one.
pub proof fn lemma_to_set_nonempty(s: Seq<Seq<char>>)
    ensures
        (s.to_set().len() > 0) == (s.len() > 0),
{
    broadcast use Seq::to_set_ensures;
    if s.len() == 0 {
        assert(s.to_set() =~= Set::<Seq<char>>::empty());
        vstd::set_lib::lemma_set_empty_equivalency_len::<Seq<char>>(s.to_set());
    } else {
        assert(s.to_set().contains(s[0]));
        if s.to_set().len() == 0 {
            vstd::set_lib::lemma_set_empty_equivalency_len::<Seq<char>>(s.to_set());
            assert(false);
        }
    }
}

/// The kernel's record of a promise is the model's.
pub proof fn lemma_prec(p: APromise)
    ensures
        prec_out(p.to_record()) == prec_v(p.id, promise_v(p)),
{
}

// --------------------------------------------------------------- the steps

/// A projection is the model's timeout: a live promise past its deadline is
/// settled by its kind, its task done; anything else is left.
pub proof fn tr_project(b: AState, x: Seq<char>, now: nat)
    requires
        inv(now, b),
        b.objects.contains_key(x),
    ensures
        ({
            let n = translate(b);
            let p = n.promises[x];
            translate(with_objects(b, promise_timeout_objects(b, x, now))) == (
                if live_v(p) && now >= p.timeout_at {
                    settle_v(n, x, if p.tags.timer { PState::Resolved } else { PState::TimedOut }, None, p.timeout_at)
                } else {
                    n
                })
        }),
{
    lemma_inv_pointwise(now, b);
    assert(inv_obj(now, b, x));
    lemma_translate_reads(b, x);
    let n = translate(b);
    let p0 = b.objects[x];
    let p = n.promises[x];
    let q = p0.project(now);
    let b2 = with_objects(b, promise_timeout_objects(b, x, now));
    lemma_translate_insert(b, x, q);
    if p0.state == PromiseState::Pending && p0.timeout_at <= now {
        let st = if p.tags.timer { PState::Resolved } else { PState::TimedOut };
        assert(p0.value.is_empty());
        assert(promise_v(q) == PromiseV { state: st, value: None, settled_at: Some(p0.timeout_at), ..p });
        let m = settle_v(n, x, st, None, p0.timeout_at);
        assert(translate(b2).promises == m.promises);
        match p0.task {
            None => {
                assert(!n.tasks.contains_key(x));
                assert(translate(b2).tasks =~= n.tasks);
                assert(m.tasks == n.tasks);
            },
            Some(t) => {
                let t2 = t.view_through(q.project_promise(now));
                assert(q.task == Some(t.view_through(p0.project_promise(now))));
                if t.state == TaskState::Fulfilled {
                    assert(q.task == Some(t));
                    assert(translate(b2).tasks =~= n.tasks);
                    assert(m.tasks == n.tasks);
                } else {
                    assert(q.task == Some(t.fulfill()));
                    assert(task_v(t.fulfill()) == fulfilled_v(task_v(t)));
                    assert(translate(b2).tasks == m.tasks);
                }
            },
        }
        assert(translate(b2) == m);
    } else {
        if p0.state != PromiseState::Pending {
            match p0.task {
                None => {},
                Some(t) => {
                    assert(t.state == TaskState::Fulfilled);
                },
            }
        }
        assert(q == p0);
        lemma_insert_same(b, x);
        assert(b2 == b);
    }
}

/// A callback step is the model's resume, when the callback is held by a
/// settled promise; else nothing. The two objects read must be projected.
pub proof fn tr_resume(b: AState, x: Seq<char>, w: Seq<char>, now: nat)
    requires
        inv(now, b),
        b.objects.contains_key(x) ==> b.objects[x].project(now) == b.objects[x],
        b.objects.contains_key(w) ==> b.objects[w].project(now) == b.objects[w],
    ensures
        ({
            let n = translate(b);
            let due = n.promises.contains_key(x) && !live_v(n.promises[x]) && n.promises[x].callbacks.contains(w);
            translate(callback_fn(b, x, w, now)) == (if due { resume_v(n, x, w, now as Time) } else { n })
        }),
{
    broadcast use Seq::to_set_ensures;
    let n = translate(b);
    lemma_translate_reads(b, x);
    lemma_translate_reads(b, w);
    let b2 = callback_fn(b, x, w, now);
    if b.objects.contains_key(x) {
        lemma_inv_pointwise(now, b);
        assert(inv_obj(now, b, x));
        let p = b.objects[x];
        assert(p.project(now) == p);
        lemma_insert_same(b, x);
        let due = !live_v(n.promises[x]) && n.promises[x].callbacks.contains(w);
        assert(n.promises[x].callbacks.contains(w) == p.callbacks.contains(w));
        if p.state == PromiseState::Pending || !p.callbacks.contains(w) {
            assert(b2 == b);
            assert(!due);
        } else {
            assert(due);
            assert(w != x);
            assert(p.settled_at is Some);
            let p2 = p.remove_callback(w);
            let a2 = with_objects(b, b.objects.insert(x, p2));
            lemma_translate_insert(b, x, p2);
            lemma_without_to_set(p.callbacks, w);
            assert(promise_v(p2) == PromiseV { callbacks: n.promises[x].callbacks.remove(w), ..n.promises[x] });
            let r = resume_v(n, x, w, now as Time);
            assert(r.promises == translate(a2).promises);
            let since = p.settled_at.unwrap();
            assert(opt_or_zero(p.settled_at) == since as nat);
            if !b.objects.contains_key(w) {
                assert(b2 == a2);
                assert(!n.tasks.contains_key(w));
                assert(r.tasks == n.tasks);
                assert(translate(a2).tasks =~= n.tasks);
                assert(translate(b2) == r);
            } else {
                let q = b.objects[w];
                assert(a2.objects[w] == q);
                assert(q.project(now) == q);
                lemma_insert_same(a2, w);
                let a3 = with_objects(a2, a2.objects.insert(w, q));
                assert(a3 == a2);
                match q.task {
                    None => {
                        assert(b2 == a2);
                        assert(!n.tasks.contains_key(w));
                        assert(r.tasks == n.tasks);
                        assert(translate(a2).tasks =~= n.tasks);
                        assert(translate(b2) == r);
                    },
                    Some(t) => {
                        assert(inv_obj(now, b, w));
                        assert(n.tasks[w] == task_v(t));
                        let tv = task_v(t);
                        if t.state == TaskState::Suspended {
                            let t2 = t.wake(x, since as nat);
                            assert(b2 == with_objects(a2, a2.objects.insert(w, q.with_task(t2))));
                            lemma_translate_insert(a2, w, q.with_task(t2));
                            assert(task_cleared_spec(t));
                            assert(task_v(t2) == TaskV { state: TState::Pending, resumes: seq![x], retry_at: Some(since), ..tv });
                            assert(translate(b2).promises =~= r.promises);
                            assert(translate(b2).tasks =~= r.tasks);
                            assert(translate(b2) == r);
                        } else if t.state != TaskState::Fulfilled {
                            let t2 = t.buffer(x);
                            assert(b2 == with_objects(a2, a2.objects.insert(w, q.with_task(t2))));
                            lemma_translate_insert(a2, w, q.with_task(t2));
                            if t.resumes.contains(x) {
                                assert(t2 == t);
                                assert(translate(b2).tasks =~= translate(a2).tasks);
                                assert(r.tasks == n.tasks);
                                assert(translate(a2).tasks =~= n.tasks);
                            } else {
                                assert(task_v(t2) == TaskV { resumes: tv.resumes.push(x), ..tv });
                            }
                            assert(translate(b2).promises =~= r.promises);
                            assert(translate(b2).tasks =~= r.tasks);
                            assert(translate(b2) == r);
                        } else {
                            assert(b2 == a2);
                            assert(r.tasks == n.tasks);
                            assert(translate(a2).tasks =~= n.tasks);
                            assert(translate(b2) == r);
                        }
                    },
                }
            }
        }
    } else {
        assert(b2 == b);
    }
}

/// A suspended task under the invariant holds no lease and no offer.
pub open spec fn task_cleared_spec(t: ATask) -> bool {
    t.pid is None && t.ttl is None && t.lease_timeout_at is None && t.retry_timeout_at is None
}

/// A lease step is the model's release of a held task past its lease.
pub proof fn tr_lease(b: AState, id: Seq<char>, now: nat)
    requires
        inv(now, b),
        leases_from_ttl(b),
        b.objects.contains_key(id) ==> b.objects[id].project(now) == b.objects[id],
    ensures
        ({
            let n = translate(b);
            let due = n.tasks.contains_key(id) && n.tasks[id].state == TState::Acquired && now >= lease_expires_v(n.tasks[id]);
            translate(with_objects(b, lease_timeout_objects(b, id, now))) == (
                if due { ServerV { tasks: n.tasks.insert(id, released_v(n.tasks[id], lease_expires_v(n.tasks[id]))), ..n } } else { n })
        }),
{
    let n = translate(b);
    lemma_translate_reads(b, id);
    let b2 = with_objects(b, lease_timeout_objects(b, id, now));
    if b.objects.contains_key(id) {
        lemma_inv_pointwise(now, b);
        assert(inv_obj(now, b, id));
        let p = b.objects[id];
        lemma_projected_obj(p, now);
        match p.task {
            None => {
                assert(b2 == b);
                assert(!n.tasks.contains_key(id));
            },
            Some(t) => {
                let tv = task_v(t);
                if t.state == TaskState::Acquired {
                    assert(t.lease_timeout_at is Some && t.ttl is Some);
                    let end = t.lease_timeout_at.unwrap();
                    assert(end >= t.ttl.unwrap());
                    assert(tv.acquired_at == end - t.ttl.unwrap());
                    assert(lease_expires_v(tv) == end);
                    assert(p.state == PromiseState::Pending);
                    assert(p.timeout_at > now);
                    if end <= now {
                        assert(lease_due(p, now));
                        let t2 = t.release(end as nat);
                        assert(b2 == with_objects(b, b.objects.insert(id, p.with_task(t2))));
                        lemma_translate_insert(b, id, p.with_task(t2));
                        assert(task_v(t2) == released_v(tv, end));
                        assert(translate(b2).promises =~= n.promises);
                        assert(translate(b2) == ServerV { tasks: n.tasks.insert(id, released_v(tv, end)), ..n });
                    } else {
                        assert(!lease_due(p, now));
                        assert(b2 == b);
                    }
                } else {
                    assert(!lease_due(p, now));
                    assert(b2 == b);
                    assert(tv.state != TState::Acquired);
                }
            },
        }
    } else {
        assert(b2 == b);
        assert(!n.tasks.contains_key(id));
    }
}

/// The listener steps of an object are the model's unblocks: a settled
/// promise's listeners are told, once each, and cleared.
pub proof fn tr_listeners(b: AState, id: Seq<char>, now: nat)
    requires
        inv(now, b),
        b.objects.contains_key(id),
        b.objects[id].project(now) == b.objects[id],
    ensures
        ({
            let n = translate(b);
            let p = n.promises[id];
            let told = !live_v(p) && p.listeners.len() > 0;
            let b2 = listeners_of(b, id, b.objects[id].listeners, now);
            &&& translate(b2) == (if told { ServerV { promises: n.promises.insert(id, PromiseV { listeners: Set::empty(), ..p }), ..n } } else { n })
            &&& listeners_sends(b, id, b.objects[id].listeners, now).to_multiset() == (
                if told { p.listeners.to_seq().map_values(|a: Chars| DispatchV::Unblock { address: a, promise: prec_v(id, p) }) } else { Seq::<DispatchV>::empty() }).to_multiset()
        }),
{
    broadcast use Seq::to_set_ensures;
    let n = translate(b);
    lemma_translate_reads(b, id);
    lemma_inv_pointwise(now, b);
    assert(inv_obj(now, b, id));
    let p0 = b.objects[id];
    let p = n.promises[id];
    let l = p0.listeners;
    assert(p0.id == id);
    assert(no_dups(l));
    assert(p.listeners == l.to_set());
    lemma_to_set_nonempty(l);
    let b2 = listeners_of(b, id, l, now);
    if p0.state != PromiseState::Pending {
        lemma_listeners_of_exact(b, id, l, now);
        lemma_spent_all(l);
        let q = APromise { listeners: Seq::empty(), ..p0 };
        assert(b2.objects[id] == q);
        assert(b2.objects =~= b.objects.insert(id, q));
        lemma_translate_insert(b, id, q);
        assert(Seq::<Seq<char>>::empty().to_set() =~= Set::<Seq<char>>::empty());
        assert(promise_v(q) == PromiseV { listeners: Set::empty(), ..p });
        let f = |a: Chars| DispatchV::Unblock { address: a, promise: prec_v(id, p) };
        lemma_prec(p0);
        assert forall|a: Seq<char>| #[trigger] unblock_of(p0, a) == f(a) by {}
        assert(l.map_values(|address: Seq<char>| unblock_of(p0, address)) =~= l.map_values(f));
        if l.len() > 0 {
            assert(translate(b2) == ServerV { promises: n.promises.insert(id, PromiseV { listeners: Set::empty(), ..p }), ..n }) by {
                assert(translate(b2).tasks =~= n.tasks);
            }
            assert(l.no_duplicates());
            l.to_set().lemma_to_seq_no_duplicates();
            l.to_set().lemma_to_seq_to_set_id();
            assert(vstd::relations::injective(f));
            lemma_map_nodup_same_set(l, l.to_set().to_seq(), f);
        } else {
            assert(l =~= Seq::<Seq<char>>::empty());
            assert(q == p0);
            lemma_insert_same(b, id);
            assert(b2 == b);
            assert(listeners_sends(b, id, l, now) == Seq::<DispatchV>::empty());
        }
    } else {
        lemma_listeners_of_pending(b, id, l, now);
    }
}

/// A retry step is the model's offer: a pending task past its offer, on a live
/// promise, is offered again and re-armed on its grid.
pub proof fn tr_retry(b: AState, id: Seq<char>, now: nat, rt: u64)
    requires
        inv(now, b),
        0 < rt,
        now + rt <= u64::MAX,
        b.objects.contains_key(id) ==> b.objects[id].project(now) == b.objects[id],
    ensures
        ({
            let n = translate(b);
            let live = n.promises.contains_key(id) && live_v(n.promises[id]);
            let retry = n.tasks.contains_key(id) && {
                let t = n.tasks[id];
                t.state == TState::Pending && t.retry_at is Some && t.retry_at.unwrap() <= now && live
            };
            let again = next_offer_v(n.tasks[id].retry_at.unwrap(), now as Time, rt);
            let b2 = retry_fn(b, id, now, rt as nat);
            &&& translate(b2) == (if retry { ServerV { tasks: n.tasks.insert(id, TaskV { retry_at: Some(again), ..n.tasks[id] }), ..n } } else { n })
            &&& retry_send(b, id, now, rt as nat) == (if retry { seq![DispatchV::Execute { id, version: n.tasks[id].version }] } else { Seq::<DispatchV>::empty() })
            &&& retry ==> b2.objects.contains_key(id) && b2.objects[id].task is Some && b2.objects[id].task.unwrap().retry_timeout_at == Some(again)
        }),
{
    let n = translate(b);
    lemma_translate_reads(b, id);
    let b2 = retry_fn(b, id, now, rt as nat);
    if b.objects.contains_key(id) {
        let p = b.objects[id];
        lemma_projected_obj(p, now);
        match p.task {
            None => {
                assert(!retry_due(p, now));
                assert(b2 == b);
            },
            Some(t) => {
                let tv = task_v(t);
                if t.state == TaskState::Pending && t.retry_timeout_at is Some && t.retry_timeout_at.unwrap() <= now && p.state == PromiseState::Pending {
                    assert(p.timeout_at > now);
                    assert(retry_due(p, now));
                    let due = t.retry_timeout_at.unwrap();
                    let nd = due as nat;
                    let tn = rt as nat;
                    lemma_next_offer(nd, now, tn);
                    let k = (now - nd) / (tn as int);
                    assert(next_offer(nd, now, tn) == nd + tn * (k + 1));
                    assert(nd + tn * (k + 1) <= now + tn);
                    assert(k <= now - nd) by {
                        vstd::arithmetic::div_mod::lemma_div_nonincreasing((now - nd) as int, tn as int);
                    }
                    assert(k + 1 <= u64::MAX);
                    assert(sat_add(k as u64, 1) == (k + 1) as u64);
                    assert(sat_mul(rt, (k + 1) as u64) == (tn * (k + 1)) as u64);
                    assert(sat_add(due, (tn * (k + 1)) as u64) == (nd + tn * (k + 1)) as u64);
                    let again = next_offer_v(due, now as Time, rt);
                    assert(again == next_offer(nd, now, tn) as u64);
                    let t2 = t.rearm(now, tn);
                    assert(t2.retry_timeout_at == Some(again));
                    assert(b2.objects == b.objects.insert(id, p.with_task(t2)));
                    lemma_translate_insert(b, id, p.with_task(t2));
                    assert(task_v(t2) == TaskV { retry_at: Some(again), ..tv });
                    assert(translate(b2).promises =~= n.promises);
                    assert(translate(b2) == ServerV { tasks: n.tasks.insert(id, TaskV { retry_at: Some(again), ..tv }), ..n });
                    assert(retry_send(b, id, now, tn) == seq![DispatchV::Execute { id, version: tv.version }]);
                } else {
                    assert(!retry_due(p, now));
                    assert(b2 == b);
                }
            },
        }
    } else {
        assert(b2 == b);
    }
}


// ------------------------------------------------------- what a step keeps

/// A projection keeps the lease rule and every other object.
pub proof fn lemma_project_keeps(b: AState, x: Seq<char>, now: nat)
    requires
        inv(now, b),
        leases_from_ttl(b),
    ensures
        ({
            let b2 = with_objects(b, promise_timeout_objects(b, x, now));
            &&& inv(now, b2)
            &&& leases_from_ttl(b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && id != x ==> b2.objects[id] == b.objects[id]
            &&& b.objects.contains_key(x) ==> b2.objects[x] == b.objects[x].project(now)
        }),
{
    lemma_project_inv(b, x, now);
    let b2 = with_objects(b, promise_timeout_objects(b, x, now));
    if b.objects.contains_key(x) {
        assert(b2.objects.dom() =~= b.objects.dom());
        let q = b.objects[x].project(now);
        match b.objects[x].task {
            None => {},
            Some(t) => {
                assert(q.task == Some(t.view_through(b.objects[x].project_promise(now))));
            },
        }
    }
}

/// What a callback step leaves: every object but the two it reads as it was;
/// `x` read and, if settled and holding `w`, less that callback; `w` read and,
/// if a task not done, resumed once. The lease rule is kept.
pub proof fn lemma_callback_keeps(b: AState, x: Seq<char>, w: Seq<char>, now: nat)
    requires
        inv(now, b),
        leases_from_ttl(b),
    ensures
        ({
            let b2 = callback_fn(b, x, w, now);
            &&& inv(now, b2)
            &&& leases_from_ttl(b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& !b.objects.contains_key(x) ==> b2 == b
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && id != x && id != w ==> b2.objects[id] == b.objects[id]
            &&& b.objects.contains_key(x) ==> {
                let p = b.objects[x].project(now);
                &&& (b2.objects[x] == p || b2.objects[x] == p.remove_callback(w))
                &&& b2.objects[x].project(now) == b2.objects[x]
                &&& !(b2.objects[x].state != PromiseState::Pending && b2.objects[x].callbacks.contains(w))
            }
            &&& b.objects.contains_key(x) && b.objects.contains_key(w) && w != x && b.objects[w].project(now) == b.objects[w] ==> {
                let q = b.objects[w].project(now);
                &&& (b2.objects[w] == q || (q.task is Some && b2.objects[w] == q.with_task(resume_step(q.task.unwrap(), x, since(b, x, now)))))
                &&& b2.objects[w].project(now) == b2.objects[w]
            }
            &&& b.objects.contains_key(x) ==> since(b, x, now) <= now
        }),
{
    lemma_callback_inv(b, x, w, now);
    let b2 = callback_fn(b, x, w, now);
    if b.objects.contains_key(x) {
        lemma_inv_pointwise(now, b);
        assert(inv_obj(now, b, x));
        let p = b.objects[x].project(now);
        echod_kernel::external_proof::lemma_project_idem(b.objects[x], now);
        lemma_insert_same(with_objects(b, b.objects.insert(x, p)), x);
        let b1 = with_objects(b, b.objects.insert(x, p));
        assert(b1.objects.dom() =~= b.objects.dom());
        lemma_project_keeps(b, x, now);
        assert(b1 == with_objects(b, promise_timeout_objects(b, x, now)));
        assert(since(b, x, now) <= now) by {
            if p.settled_at is Some {
                assert(p.settled_at.unwrap() <= now);
            }
        }
        if p.state == PromiseState::Pending || !p.callbacks.contains(w) {
            assert(b2 == b1);
            if b.objects.contains_key(w) && w != x {
                assert(b2.objects[w] == b.objects[w]);
            }
        } else {
            assert(w != x);
            let p2 = p.remove_callback(w);
            lemma_project_lists(p, now, p2.callbacks, p.listeners);
            lemma_without_contains(p.callbacks, w, w);
            let a2 = with_objects(b1, b1.objects.insert(x, p2));
            assert(a2.objects.dom() =~= b.objects.dom());
            assert(b2.objects[x] == p2);
            if !b.objects.contains_key(w) {
                assert(b2 == a2);
            } else {
                let q = b.objects[w].project(now);
                echod_kernel::external_proof::lemma_project_idem(b.objects[w], now);
                let a3 = with_objects(a2, a2.objects.insert(w, q));
                assert(a3.objects.dom() =~= b.objects.dom());
                lemma_projected_obj(q, now);
                match q.task {
                    None => {
                        assert(b2 == a3);
                    },
                    Some(t) => {
                        let s = since(b, x, now);
                        let t2 = resume_step(t, x, s);
                        if t.state == TaskState::Suspended {
                            assert(q.state == PromiseState::Pending);
                            lemma_project_pending_task(q, now, t2);
                            assert(b2 == with_objects(a3, a3.objects.insert(w, q.with_task(t2))));
                            assert(b2.objects.dom() =~= b.objects.dom());
                        } else if t.state != TaskState::Fulfilled {
                            assert(q.state == PromiseState::Pending);
                            lemma_project_pending_task(q, now, t2);
                            assert(b2 == with_objects(a3, a3.objects.insert(w, q.with_task(t2))));
                            assert(b2.objects.dom() =~= b.objects.dom());
                        } else {
                            assert(b2 == a3);
                        }
                    },
                }
            }
            // the lease rule: the awaiter's lease is as it was
            assert(leases_from_ttl(b2)) by {
                assert forall|id: Seq<char>| #[trigger] b2.objects.contains_key(id) implies match b2.objects[id].task {
                    Some(t) => (t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap(),
                    None => true,
                } by {
                    if id == x {
                        assert(b2.objects[x].task == p.task);
                        assert(leases_from_ttl(b1));
                    } else if id == w {
                        let q = b.objects[w].project(now);
                        assert(leases_from_ttl(b1));
                        assert(b1.objects[w] == b.objects[w]);
                        match q.task {
                            None => {},
                            Some(t) => {
                                let orig = b.objects[w].task.unwrap();
                                assert(t == orig.view_through(b.objects[w].project_promise(now)));
                            },
                        }
                    }
                }
            }
        }
    } else {
        assert(b2 == b);
    }
}


/// The due steps on an id keep the lease rule and every other object; the id
/// stays projected, its promise's state and callbacks stay; its task's lease
/// is kept or cleared, its offer kept or re-armed, nothing of it due.
pub proof fn lemma_due_one_keeps(b: AState, id: Seq<char>, now: nat, t: nat)
    requires
        inv(now, b),
        leases_from_ttl(b),
        0 < t <= MAX_TIME,
        now <= MAX_TIME,
        b.objects.contains_key(id) ==> b.objects[id].project(now) == b.objects[id],
    ensures
        ({
            let b2 = k_due_one(b, id, now, t);
            &&& inv(now, b2)
            &&& leases_from_ttl(b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& forall|z: Seq<char>| #[trigger] b.objects.contains_key(z) && z != id ==> b2.objects[z] == b.objects[z]
            &&& b.objects.contains_key(id) ==> {
                let p = b.objects[id];
                let q = b2.objects[id];
                &&& q.project(now) == q
                &&& q.state == p.state
                &&& q.timeout_at == p.timeout_at
                &&& q.callbacks == p.callbacks
                &&& q.state != PromiseState::Pending ==> q.listeners.len() == 0
                &&& !lease_due(q, now)
                &&& !retry_due(q, now)
                &&& q.task is Some == p.task is Some
                &&& q.task is Some ==> {
                    let t2 = q.task.unwrap();
                    let t1 = p.task.unwrap();
                    &&& t2.version == t1.version
                    &&& (t2.lease_timeout_at == t1.lease_timeout_at || t2.lease_timeout_at is None)
                    &&& (t2.lease_timeout_at is Some ==> t2.lease_timeout_at.unwrap() > now)
                    &&& (t2.retry_timeout_at is Some ==> t2.retry_timeout_at.unwrap() > now)
                }
            }
        }),
{
    let b1 = with_objects(b, lease_timeout_objects(b, id, now));
    lemma_lease_inv(b, id, now);
    assert(b1.objects.dom() =~= b.objects.dom());
    let b2 = if b1.objects.contains_key(id) { listeners_of(b1, id, b1.objects[id].listeners, now) } else { b1 };
    let b3 = retry_fn(b2, id, now, t);
    assert(k_due_one(b, id, now, t) == b3);
    if b.objects.contains_key(id) {
        let p = b.objects[id];
        lemma_inv_pointwise(now, b);
        assert(inv_obj(now, b, id));
        lemma_projected_obj(p, now);
        // the lease
        let p1 = b1.objects[id];
        if lease_due(p, now) {
            let tk = p.task.unwrap();
            let end = tk.lease_timeout_at.unwrap() as nat;
            assert(p1 == p.with_task(tk.release(end)));
            lemma_project_pending_task(p, now, tk.release(end));
        } else {
            assert(p1 == p);
        }
        assert(p1.project(now) == p1);
        assert(!lease_due(p1, now));
        assert(leases_from_ttl(b1));
        // the listeners
        lemma_inv_pointwise(now, b1);
        assert(inv_obj(now, b1, id));
        let l = p1.listeners;
        let p2 = b2.objects[id];
        if p1.state != PromiseState::Pending {
            lemma_listeners_of_exact(b1, id, l, now);
            lemma_spent_all(l);
            assert(p2 == APromise { listeners: Seq::empty(), ..p1 });
        } else {
            lemma_listeners_of_pending(b1, id, l, now);
            assert(p2 == p1);
        }
        lemma_listeners_of_inv(b1, id, l, now);
        assert(b2.objects.dom() =~= b.objects.dom());
        assert(p2.project(now) == p2) by {
            lemma_project_lists(p1, now, p1.callbacks, p2.listeners);
        }
        assert(leases_from_ttl(b2)) by {
            assert forall|z: Seq<char>| #[trigger] b2.objects.contains_key(z) implies match b2.objects[z].task {
                Some(tk) => (tk.lease_timeout_at is Some && tk.ttl is Some) ==> tk.lease_timeout_at.unwrap() >= tk.ttl.unwrap(),
                None => true,
            } by {
                assert(b2.objects[z].task == b1.objects[z].task);
            }
        }
        // the offer
        lemma_retry_inv(b2, id, now, t);
        let p3 = b3.objects[id];
        if retry_due(p2, now) {
            let tk = p2.task.unwrap();
            let due = opt_or_zero(tk.retry_timeout_at);
            lemma_next_offer(due, now, t);
            assert(next_offer(due, now, t) <= now + t);
            assert(now + t <= u64::MAX);
            assert(p3 == p2.with_task(tk.rearm(now, t)));
            lemma_project_pending_task(p2, now, tk.rearm(now, t));
            assert(p3.task.unwrap().retry_timeout_at == Some(next_offer(due, now, t) as u64));
        } else {
            assert(p3 == p2);
        }
        assert(b3.objects.dom() =~= b.objects.dom());
        assert(p3.project(now) == p3);
        assert(!retry_due(p3, now));
        assert(!lease_due(p3, now));
        // the fields the deadlines read
        lemma_inv_pointwise(now, b3);
        assert(inv_obj(now, b3, id));
        lemma_projected_obj(p3, now);
        match p3.task {
            None => {},
            Some(t3) => {
                if p3.state == PromiseState::Pending {
                    assert(p3.timeout_at > now);
                    if t3.lease_timeout_at is Some {
                        assert(t3.state == TaskState::Acquired);
                        assert(t3.lease_timeout_at.unwrap() > now);
                    }
                    if t3.retry_timeout_at is Some {
                        assert(t3.state == TaskState::Pending);
                        assert(t3.retry_timeout_at.unwrap() > now);
                    }
                } else {
                    assert(t3.state == TaskState::Fulfilled);
                    assert(t3.lease_timeout_at is None);
                    assert(t3.retry_timeout_at is None);
                }
            },
        }
        assert(leases_from_ttl(b3)) by {
            assert forall|z: Seq<char>| #[trigger] b3.objects.contains_key(z) implies match b3.objects[z].task {
                Some(tk) => (tk.lease_timeout_at is Some && tk.ttl is Some) ==> tk.lease_timeout_at.unwrap() >= tk.ttl.unwrap(),
                None => true,
            } by {
                if z != id {
                    assert(b3.objects[z] == b2.objects[z]);
                } else {
                    match p3.task {
                        None => {},
                        Some(t3) => {
                            assert(t3.lease_timeout_at == p2.task.unwrap().lease_timeout_at && t3.ttl == p2.task.unwrap().ttl);
                        },
                    }
                }
            }
        }
    } else {
        assert(b3 == b);
    }
}

// ------------------------------------------------------------- the folds

/// Work the deadlines phase starts: a resume per callback of a promise it
/// settles, and its listeners' unblocks.
pub open spec fn spawned(b: AState, ids: Seq<Seq<char>>, now: nat, item: Sched<InternalV>) -> bool {
    exists|x: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now && (
        item == Sched::Later(InternalV::On(seq![x])) || exists|w: Seq<char>| #[trigger] b.objects[x].callbacks.contains(w) && item == later2_v(x, w))
}

pub proof fn tr_deadlines(b: AState, ids: Seq<Seq<char>>, now: u64, work: Seq<Sched<InternalV>>)
    requires
        inv(now as nat, b),
        leases_from_ttl(b),
        ids.no_duplicates(),
    ensures
        ({
            let b1 = phase_deadlines(b, ids, now as nat);
            let (n1, work1) = deadlines_fold(ids, translate(b), work, now);
            &&& translate(b1) == n1
            &&& inv(now as nat, b1)
            &&& leases_from_ttl(b1)
            &&& b1.objects.dom() == b.objects.dom()
            &&& b1.schedules == b.schedules
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> b1.objects[id] == (if ids.contains(id) { b.objects[id].project(now as nat) } else { b.objects[id] })
            &&& work1.len() >= work.len()
            &&& forall|i: int| 0 <= i < work.len() ==> work1[i] == work[i]
            &&& forall|i: int| work.len() <= i < work1.len() ==> spawned(b, ids, now as nat, work1[i])
            &&& forall|x: Seq<char>, w: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now
                && #[trigger] b.objects[x].callbacks.contains(w) ==> work1.contains(later2_v(x, w))
            &&& forall|x: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now
                && b.objects[x].listeners.len() > 0 ==> work1.contains(Sched::Later(InternalV::On(seq![x])))
        }),
    decreases ids.len(),
{
    broadcast use Seq::to_set_ensures;
    let n = now as nat;
    if ids.len() > 0 {
        lemma_no_dup_last(ids);
        let ids0 = ids.drop_last();
        let x = ids.last();
        tr_deadlines(b, ids0, now, work);
        let b0 = phase_deadlines(b, ids0, n);
        let (n0, work0) = deadlines_fold(ids0, translate(b), work, now);
        let b1 = phase_deadlines(b, ids, n);
        let (n1, work1) = deadlines_fold(ids, translate(b), work, now);
        assert(b1 == with_objects(b0, promise_timeout_objects(b0, x, n)));
        lemma_project_keeps(b0, x, n);
        lemma_deadlines_exact(b, ids, n);
        assert forall|z: Seq<char>| ids0.contains(z) implies ids.contains(z) by {
            let i = choose|i: int| 0 <= i < ids0.len() && ids0[i] == z;
            assert(ids[i] == z);
        }
        assert(ids.contains(x)) by {
            assert(ids[ids.len() - 1] == x);
        }
        if b.objects.contains_key(x) {
            lemma_translate_reads(b0, x);
            assert(b0.objects[x] == b.objects[x]);
            tr_project(b0, x, n);
            let p = n0.promises[x];
            assert(p == promise_v(b.objects[x]));
            if live_v(p) && now >= p.timeout_at {
                let sw = settled_work_v(p, x);
                assert(work1 == work0 + sw);
                assert(b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now);
                let cbs = p.callbacks.to_seq();
                p.callbacks.lemma_to_seq_to_set_id();
                let resumes = cbs.map_values(|w: Chars| later2_v(x, w));
                assert forall|i: int| work0.len() <= i < work1.len() implies spawned(b, ids, n, work1[i]) by {
                    let j = i - work0.len();
                    assert(work1[i] == sw[j]);
                    if j < resumes.len() {
                        let w = cbs[j];
                        assert(sw[j] == later2_v(x, w));
                        assert(p.callbacks.contains(w));
                        assert(b.objects[x].callbacks.contains(w));
                    } else {
                        assert(sw[j] == Sched::Later(InternalV::On(seq![x])));
                    }
                }
                assert forall|w: Seq<char>| #[trigger] b.objects[x].callbacks.contains(w) implies work1.contains(later2_v(x, w)) by {
                    assert(p.callbacks.contains(w));
                    assert(cbs.contains(w));
                    let j = choose|j: int| 0 <= j < cbs.len() && cbs[j] == w;
                    assert(sw[j] == later2_v(x, w));
                    assert(work1[work0.len() + j] == later2_v(x, w));
                }
                if b.objects[x].listeners.len() > 0 {
                    lemma_to_set_nonempty(b.objects[x].listeners);
                    assert(p.listeners.len() > 0);
                    assert(sw.last() == Sched::Later(InternalV::On(seq![x])));
                    assert(work1[work1.len() - 1] == Sched::Later(InternalV::On(seq![x])));
                }
            } else {
                assert(work1 == work0);
                assert(!(b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now));
            }
        } else {
            assert(!n0.promises.contains_key(x));
            assert(work1 == work0);
            assert(b1 == b0);
        }
        assert forall|i: int| work.len() <= i < work1.len() implies spawned(b, ids, n, work1[i]) by {
            if i < work0.len() {
                assert(spawned(b, ids0, n, work0[i]));
                let y = choose|y: Seq<char>| ids0.contains(y) && #[trigger] b.objects.contains_key(y) && b.objects[y].state == PromiseState::Pending && b.objects[y].timeout_at <= n && (
                    work0[i] == Sched::Later(InternalV::On(seq![y])) || exists|w: Seq<char>| #[trigger] b.objects[y].callbacks.contains(w) && work0[i] == later2_v(y, w));
                assert(ids.contains(y));
            }
        }
        assert forall|y: Seq<char>, w: Seq<char>| ids.contains(y) && #[trigger] b.objects.contains_key(y) && b.objects[y].state == PromiseState::Pending && b.objects[y].timeout_at <= now
            && #[trigger] b.objects[y].callbacks.contains(w) implies work1.contains(later2_v(y, w)) by {
            lemma_contains_split(ids, y);
            if y != x {
                let i = choose|i: int| 0 <= i < work0.len() && work0[i] == later2_v(y, w);
                assert(work1[i] == later2_v(y, w));
            }
        }
        assert forall|y: Seq<char>| ids.contains(y) && #[trigger] b.objects.contains_key(y) && b.objects[y].state == PromiseState::Pending && b.objects[y].timeout_at <= now
            && b.objects[y].listeners.len() > 0 implies work1.contains(Sched::Later(InternalV::On(seq![y]))) by {
            lemma_contains_split(ids, y);
            if y != x {
                let i = choose|i: int| 0 <= i < work0.len() && work0[i] == Sched::Later(InternalV::On(seq![y]));
                assert(work1[i] == Sched::Later(InternalV::On(seq![y])));
            }
        }
    }
}

/// The resumes of `x` on `aw`, all of them projected: the model's inner fold.
pub proof fn tr_callbacks_of(b: AState, x: Seq<char>, aw: Seq<Seq<char>>, now: u64)
    requires
        inv(now as nat, b),
        leases_from_ttl(b),
        b.objects.contains_key(x) ==> b.objects[x].project(now as nat) == b.objects[x],
        forall|i: int| 0 <= i < aw.len() && b.objects.contains_key(#[trigger] aw[i]) ==> b.objects[aw[i]].project(now as nat) == b.objects[aw[i]],
    ensures
        ({
            let b2 = callbacks_of(b, x, aw, now as nat);
            &&& translate(b2) == resumes_inner(x, aw, translate(b), now)
            &&& inv(now as nat, b2)
            &&& leases_from_ttl(b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && id != x && !aw.contains(id) ==> b2.objects[id] == b.objects[id]
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && b.objects[id].project(now as nat) == b.objects[id] ==> b2.objects[id].project(now as nat) == b2.objects[id]
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> b2.objects[id].state == b.objects[id].state
                && b2.objects[id].timeout_at == b.objects[id].timeout_at && b2.objects[id].listeners == b.objects[id].listeners
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && id != x ==> b2.objects[id].callbacks == b.objects[id].callbacks
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> (b2.objects[id].task is Some == b.objects[id].task is Some) && (b2.objects[id].task is Some ==> {
                let t2 = b2.objects[id].task.unwrap();
                let t = b.objects[id].task.unwrap();
                &&& t2.lease_timeout_at == t.lease_timeout_at
                &&& t2.version == t.version
                &&& (t2.retry_timeout_at == t.retry_timeout_at || (t2.retry_timeout_at is Some && t2.retry_timeout_at.unwrap() <= now))
            })
            &&& forall|i: int| 0 <= i < aw.len() ==> !awaits(b2, x, #[trigger] aw[i], now as nat)
        }),
    decreases aw.len(),
{
    let n = now as nat;
    if aw.len() > 0 {
        let aw0 = aw.drop_last();
        let w = aw.last();
        assert forall|i: int| 0 <= i < aw0.len() && b.objects.contains_key(#[trigger] aw0[i]) implies b.objects[aw0[i]].project(n) == b.objects[aw0[i]] by {
            assert(aw0[i] == aw[i]);
        }
        tr_callbacks_of(b, x, aw0, now);
        let b1 = callbacks_of(b, x, aw0, n);
        assert(aw[aw.len() - 1] == w);
        assert(b.objects.contains_key(w) ==> b1.objects[w].project(n) == b1.objects[w]);
        tr_resume(b1, x, w, n);
        lemma_callback_keeps(b1, x, w, n);
        let b2 = callback_fn(b1, x, w, n);
        assert forall|id: Seq<char>| ids_contains_or(aw, aw0, id) implies true by {}
        if b.objects.contains_key(x) {
            let p = b1.objects[x];
            assert(p.project(n) == p);
            assert(b2.objects[x] == p || b2.objects[x] == p.remove_callback(w));
            assert(b2.objects[x].task == p.task);
            assert(b2.objects[x].state == p.state && b2.objects[x].listeners == p.listeners && b2.objects[x].timeout_at == p.timeout_at);
            if b.objects.contains_key(w) && w != x {
                let q = b1.objects[w];
                assert(q.project(n) == q);
                assert(b2.objects[w] == q || (q.task is Some && b2.objects[w] == q.with_task(resume_step(q.task.unwrap(), x, since(b1, x, n)))));
                assert(b2.objects[w].state == q.state && b2.objects[w].listeners == q.listeners && b2.objects[w].callbacks == q.callbacks && b2.objects[w].timeout_at == q.timeout_at);
                match q.task {
                    None => {},
                    Some(t) => {
                        let t2 = resume_step(t, x, since(b1, x, n));
                        assert(t2.lease_timeout_at == t.lease_timeout_at && t2.version == t.version);
                        assert(t2.retry_timeout_at == t.retry_timeout_at || (t2.retry_timeout_at is Some && t2.retry_timeout_at.unwrap() <= now));
                    },
                }
            }
        } else {
            assert(b2 == b1);
        }
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && id != x && !aw.contains(id) implies b2.objects[id] == b.objects[id] by {
            lemma_contains_split(aw, id);
            assert(!aw0.contains(id));
            assert(id != w);
        }
        assert forall|i: int| 0 <= i < aw.len() implies !awaits(b2, x, #[trigger] aw[i], n) by {
            if i < aw.len() - 1 {
                assert(aw0[i] == aw[i]);
                assert(!awaits(b1, x, aw[i], n));
                if b.objects.contains_key(x) {
                    let p = b1.objects[x];
                    if b2.objects[x] == p.remove_callback(w) {
                        lemma_without_contains(p.callbacks, w, aw[i]);
                    }
                }
            }
        }
    }
}

/// Just a hook for the triggers above.
pub open spec fn ids_contains_or(a: Seq<Seq<char>>, b: Seq<Seq<char>>, id: Seq<char>) -> bool {
    true
}

/// The resumes of every awaited among `awaiteds` on every awaiter among `all`,
/// all projected: the model's outer fold.
pub proof fn tr_resumes(b: AState, awaiteds: Seq<Seq<char>>, all: Seq<Seq<char>>, now: u64)
    requires
        inv(now as nat, b),
        leases_from_ttl(b),
        forall|i: int| 0 <= i < awaiteds.len() && b.objects.contains_key(#[trigger] awaiteds[i]) ==> b.objects[awaiteds[i]].project(now as nat) == b.objects[awaiteds[i]],
        forall|i: int| 0 <= i < all.len() && b.objects.contains_key(#[trigger] all[i]) ==> b.objects[all[i]].project(now as nat) == b.objects[all[i]],
    ensures
        ({
            let b2 = k_resumes(b, awaiteds, all, now as nat);
            &&& translate(b2) == resumes_fold(awaiteds, all, translate(b), now)
            &&& inv(now as nat, b2)
            &&& leases_from_ttl(b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && !awaiteds.contains(id) && !all.contains(id) ==> b2.objects[id] == b.objects[id]
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && b.objects[id].project(now as nat) == b.objects[id] ==> b2.objects[id].project(now as nat) == b2.objects[id]
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> b2.objects[id].state == b.objects[id].state
                && b2.objects[id].timeout_at == b.objects[id].timeout_at && b2.objects[id].listeners == b.objects[id].listeners
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && !awaiteds.contains(id) ==> b2.objects[id].callbacks == b.objects[id].callbacks
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) ==> (b2.objects[id].task is Some == b.objects[id].task is Some) && (b2.objects[id].task is Some ==> {
                let t2 = b2.objects[id].task.unwrap();
                let t = b.objects[id].task.unwrap();
                &&& t2.lease_timeout_at == t.lease_timeout_at
                &&& t2.version == t.version
                &&& (t2.retry_timeout_at == t.retry_timeout_at || (t2.retry_timeout_at is Some && t2.retry_timeout_at.unwrap() <= now))
            })
            &&& forall|i: int, j: int| 0 <= i < awaiteds.len() && 0 <= j < all.len() ==> !awaits(b2, #[trigger] awaiteds[i], #[trigger] all[j], now as nat)
        }),
    decreases awaiteds.len(),
{
    let n = now as nat;
    if awaiteds.len() > 0 {
        let aw0 = awaiteds.drop_last();
        let x = awaiteds.last();
        assert forall|i: int| 0 <= i < aw0.len() && b.objects.contains_key(#[trigger] aw0[i]) implies b.objects[aw0[i]].project(n) == b.objects[aw0[i]] by {
            assert(aw0[i] == awaiteds[i]);
        }
        tr_resumes(b, aw0, all, now);
        let b1 = k_resumes(b, aw0, all, n);
        assert(awaiteds[awaiteds.len() - 1] == x);
        assert forall|i: int| 0 <= i < all.len() && b1.objects.contains_key(#[trigger] all[i]) implies b1.objects[all[i]].project(n) == b1.objects[all[i]] by {}
        tr_callbacks_of(b1, x, all, now);
        let b2 = callbacks_of(b1, x, all, n);
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && !awaiteds.contains(id) && !all.contains(id) implies b2.objects[id] == b.objects[id] by {
            lemma_contains_split(awaiteds, id);
        }
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && !awaiteds.contains(id) implies b2.objects[id].callbacks == b.objects[id].callbacks by {
            lemma_contains_split(awaiteds, id);
        }
        assert forall|i: int, j: int| 0 <= i < awaiteds.len() && 0 <= j < all.len() implies !awaits(b2, #[trigger] awaiteds[i], #[trigger] all[j], n) by {
            if i < awaiteds.len() - 1 {
                assert(aw0[i] == awaiteds[i]);
                assert(!awaits(b1, awaiteds[i], all[j], n));
                // callbacks of an awaited other than x are as in b1; x's state is as in b1
                if awaiteds[i] != x {
                    assert(b2.objects[awaiteds[i]].callbacks == b1.objects[awaiteds[i]].callbacks || !b1.objects.contains_key(awaiteds[i]));
                    if b1.objects.contains_key(awaiteds[i]) {
                        assert(b2.objects[awaiteds[i]].state == b1.objects[awaiteds[i]].state);
                        assert(b2.objects[awaiteds[i]].project(n) == b2.objects[awaiteds[i]]);
                        assert(b1.objects[awaiteds[i]].project(n) == b1.objects[awaiteds[i]]);
                    }
                }
            }
        }
    }
}

/// One iteration of the model's `due_fold`.
pub open spec fn due_step(cfg: Resonate, id: Chars, n1: ServerV, work1: Seq<Sched<InternalV>>, send1: Seq<DispatchV>, now: Time) -> (ServerV, Seq<Sched<InternalV>>, Seq<DispatchV>) {
    let tasks2 = if n1.tasks.contains_key(id) && n1.tasks[id].state == TState::Acquired && now >= lease_expires_v(n1.tasks[id]) {
        n1.tasks.insert(id, released_v(n1.tasks[id], lease_expires_v(n1.tasks[id])))
    } else {
        n1.tasks
    };
    let n2 = ServerV { tasks: tasks2, ..n1 };
    let told = n2.promises.contains_key(id) && !live_v(n2.promises[id]) && n2.promises[id].listeners.len() > 0;
    let (n3, send3) = if told {
        let p = n2.promises[id];
        let rec = prec_v(id, p);
        let unblocks = p.listeners.to_seq().map_values(|a: Chars| DispatchV::Unblock { address: a, promise: rec });
        (ServerV { promises: n2.promises.insert(id, PromiseV { listeners: Set::empty(), ..p }), ..n2 }, send1 + unblocks)
    } else {
        (n2, send1)
    };
    let live = n3.promises.contains_key(id) && live_v(n3.promises[id]);
    let retry = n3.tasks.contains_key(id) && {
        let t = n3.tasks[id];
        t.state == TState::Pending && t.retry_at is Some && t.retry_at.unwrap() <= now && live
    };
    if retry {
        let t = n3.tasks[id];
        let again = next_offer_v(t.retry_at.unwrap(), now, cfg.retry_timeout);
        (
            ServerV { tasks: n3.tasks.insert(id, TaskV { retry_at: Some(again), ..t }), ..n3 },
            work1.push(at_v(again, id)),
            send3.push(DispatchV::Execute { id, version: t.version }),
        )
    } else {
        (n3, work1, send3)
    }
}

pub proof fn lemma_due_fold_step(cfg: Resonate, ids: Seq<Chars>, n: ServerV, work: Seq<Sched<InternalV>>, send: Seq<DispatchV>, now: Time)
    requires
        ids.len() > 0,
    ensures
        ({
            let (n1, w1, s1) = due_fold(cfg, ids.drop_last(), n, work, send, now);
            due_fold(cfg, ids, n, work, send, now) == due_step(cfg, ids.last(), n1, w1, s1, now)
        }),
{
}

/// The due steps on one id are the model's.
pub proof fn tr_due_one(b: AState, id: Seq<char>, now: u64, cfg: Resonate, work: Seq<Sched<InternalV>>, send: Seq<DispatchV>)
    requires
        inv(now as nat, b),
        leases_from_ttl(b),
        0 < cfg.retry_timeout <= MAX_TIME,
        now <= MAX_TIME,
        b.objects.contains_key(id) ==> b.objects[id].project(now as nat) == b.objects[id],
    ensures
        ({
            let rt = cfg.retry_timeout as nat;
            let b2 = k_due_one(b, id, now as nat, rt);
            let (n4, work4, send4) = due_step(cfg, id, translate(b), work, send, now);
            &&& translate(b2) == n4
            &&& send4.to_multiset() == (send + k_due_one_sends(b, id, now as nat, rt)).to_multiset()
            &&& work4.len() >= work.len()
            &&& forall|i: int| 0 <= i < work.len() ==> work4[i] == work[i]
            &&& work4.len() <= work.len() + 1
            &&& work4.len() == work.len() + 1 ==> b.objects.contains_key(id) && b2.objects[id].task is Some && b2.objects[id].task.unwrap().retry_timeout_at is Some
                && work4.last() == at_v(b2.objects[id].task.unwrap().retry_timeout_at.unwrap(), id)
            &&& b.objects.contains_key(id) && b2.objects[id].task is Some && b2.objects[id].task.unwrap().retry_timeout_at is Some
                && b2.objects[id].task.unwrap().retry_timeout_at != b.objects[id].task.unwrap().retry_timeout_at ==> work4.len() == work.len() + 1
        }),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_axioms;
    let n = now as nat;
    let rt = cfg.retry_timeout;
    let tn = rt as nat;
    let s0 = translate(b);
    lemma_translate_reads(b, id);
    // the lease
    tr_lease(b, id, n);
    lemma_lease_inv(b, id, n);
    let b1 = with_objects(b, lease_timeout_objects(b, id, n));
    assert(b1.objects.dom() =~= b.objects.dom());
    let tasks2 = if s0.tasks.contains_key(id) && s0.tasks[id].state == TState::Acquired && now >= lease_expires_v(s0.tasks[id]) {
        s0.tasks.insert(id, released_v(s0.tasks[id], lease_expires_v(s0.tasks[id])))
    } else {
        s0.tasks
    };
    let n2 = ServerV { tasks: tasks2, ..s0 };
    assert(translate(b1) == n2);
    assert(leases_from_ttl(b1));
    if b.objects.contains_key(id) {
        let p = b.objects[id];
        if lease_due(p, n) {
            let tk = p.task.unwrap();
            lemma_project_pending_task(p, n, tk.release(tk.lease_timeout_at.unwrap() as nat));
        }
        assert(b1.objects[id].project(n) == b1.objects[id]);
    }
    // the listeners
    let told = n2.promises.contains_key(id) && !live_v(n2.promises[id]) && n2.promises[id].listeners.len() > 0;
    let b2 = if b1.objects.contains_key(id) { listeners_of(b1, id, b1.objects[id].listeners, n) } else { b1 };
    let s1: Seq<DispatchV> = if b1.objects.contains_key(id) { listeners_sends(b1, id, b1.objects[id].listeners, n) } else { Seq::empty() };
    let (n3, send3) = if told {
        let p = n2.promises[id];
        let rec = prec_v(id, p);
        let unblocks = p.listeners.to_seq().map_values(|a: Chars| DispatchV::Unblock { address: a, promise: rec });
        (ServerV { promises: n2.promises.insert(id, PromiseV { listeners: Set::empty(), ..p }), ..n2 }, send + unblocks)
    } else {
        (n2, send)
    };
    if b1.objects.contains_key(id) {
        tr_listeners(b1, id, n);
        lemma_listeners_of_inv(b1, id, b1.objects[id].listeners, n);
        assert(translate(b2) == n3);
        assert(send3.to_multiset() == (send + s1).to_multiset());
        lemma_inv_pointwise(n, b1);
        assert(inv_obj(n, b1, id));
        if b1.objects[id].state != PromiseState::Pending {
            lemma_listeners_of_exact(b1, id, b1.objects[id].listeners, n);
        } else {
            lemma_listeners_of_pending(b1, id, b1.objects[id].listeners, n);
        }
        assert(b2.objects[id].project(n) == b2.objects[id]);
        assert(b2.objects.dom() =~= b.objects.dom());
        assert(leases_from_ttl(b2)) by {
            assert forall|z: Seq<char>| #[trigger] b2.objects.contains_key(z) implies match b2.objects[z].task {
                Some(t) => (t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap(),
                None => true,
            } by {
                assert(b2.objects[z].task == b1.objects[z].task);
            }
        }
    } else {
        assert(!told);
        assert(b2 == b1);
        assert(send3 == send);
        assert((send + Seq::<DispatchV>::empty()) =~= send);
    }
    // the offer
    assert(now + rt <= u64::MAX);
    tr_retry(b2, id, n, rt);
    let b3 = retry_fn(b2, id, n, tn);
    let s2 = retry_send(b2, id, n, tn);
    assert(k_due_one(b, id, n, tn) == b3);
    assert(k_due_one_sends(b, id, n, tn) == s1 + s2);
    let live = n3.promises.contains_key(id) && live_v(n3.promises[id]);
    let retry = n3.tasks.contains_key(id) && {
        let t = n3.tasks[id];
        t.state == TState::Pending && t.retry_at is Some && t.retry_at.unwrap() <= now && live
    };
    let (n4, work4, send4) = due_step(cfg, id, s0, work, send, now);
    if retry {
        let t = n3.tasks[id];
        let again = next_offer_v(t.retry_at.unwrap(), now, rt);
        assert(n4 == ServerV { tasks: n3.tasks.insert(id, TaskV { retry_at: Some(again), ..t }), ..n3 });
        assert(work4 == work.push(at_v(again, id)));
        assert(send4 == send3.push(DispatchV::Execute { id, version: t.version }));
        assert(translate(b3) == n4);
        assert(s2 == seq![DispatchV::Execute { id, version: t.version }]);
        assert(b3.objects[id].task.unwrap().retry_timeout_at == Some(again));
        assert(send4.to_multiset() =~= (send + (s1 + s2)).to_multiset());
    } else {
        assert(n4 == n3 && work4 == work && send4 == send3);
        assert(translate(b3) == n3);
        assert(s2 == Seq::<DispatchV>::empty());
        assert(send4.to_multiset() =~= (send + (s1 + s2)).to_multiset());
        // the offer, if any, is as it was
        if b.objects.contains_key(id) && b3.objects[id].task is Some && b3.objects[id].task.unwrap().retry_timeout_at is Some {
            assert(b3 == b2);
            assert(b2.objects[id].task == b1.objects[id].task);
            let p = b.objects[id];
            if lease_due(p, n) {
                // released: its first offer, the lease's end, is due now, so the retry would have fired
                let tk = p.task.unwrap();
                let end = tk.lease_timeout_at.unwrap();
                assert(b1.objects[id].task.unwrap().retry_timeout_at == Some(end));
                assert(end <= now);
                assert(b2.objects[id].state == PromiseState::Pending);
                assert(retry_due(b2.objects[id], n));
                assert(false);
            } else {
                assert(b1.objects[id] == p);
            }
        }
    }
}

/// The due steps on `ids` are the model's fold.
pub proof fn tr_due(b: AState, ids: Seq<Seq<char>>, now: u64, cfg: Resonate, work: Seq<Sched<InternalV>>, send: Seq<DispatchV>)
    requires
        inv(now as nat, b),
        leases_from_ttl(b),
        0 < cfg.retry_timeout <= MAX_TIME,
        now <= MAX_TIME,
        ids.no_duplicates(),
        forall|i: int| 0 <= i < ids.len() && b.objects.contains_key(#[trigger] ids[i]) ==> b.objects[ids[i]].project(now as nat) == b.objects[ids[i]],
    ensures
        ({
            let rt = cfg.retry_timeout as nat;
            let b2 = k_due(b, ids, now as nat, rt);
            let (n2, work2, send2) = due_fold(cfg, ids, translate(b), work, send, now);
            &&& translate(b2) == n2
            &&& inv(now as nat, b2)
            &&& leases_from_ttl(b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& send2.to_multiset() == (send + k_due_sends(b, ids, now as nat, rt)).to_multiset()
            &&& work2.len() >= work.len()
            &&& forall|i: int| 0 <= i < work.len() ==> work2[i] == work[i]
            &&& forall|i: int| work.len() <= i < work2.len() ==> exists|id: Seq<char>| ids.contains(id) && #[trigger] b.objects.contains_key(id) && b2.objects[id].task is Some
                && b2.objects[id].task.unwrap().retry_timeout_at is Some && #[trigger] work2[i] == at_v(b2.objects[id].task.unwrap().retry_timeout_at.unwrap(), id)
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && !ids.contains(id) ==> b2.objects[id] == b.objects[id]
            &&& forall|id: Seq<char>| ids.contains(id) && #[trigger] b.objects.contains_key(id) ==> {
                let p = b.objects[id];
                let q = b2.objects[id];
                &&& q.project(now as nat) == q
                &&& q.state == p.state
                &&& q.timeout_at == p.timeout_at
                &&& q.callbacks == p.callbacks
                &&& q.state != PromiseState::Pending ==> q.listeners.len() == 0
                &&& !lease_due(q, now as nat)
                &&& !retry_due(q, now as nat)
                &&& q.task is Some == p.task is Some
                &&& q.task is Some ==> {
                    let t2 = q.task.unwrap();
                    let t1 = p.task.unwrap();
                    &&& t2.version == t1.version
                    &&& (t2.lease_timeout_at == t1.lease_timeout_at || t2.lease_timeout_at is None)
                    &&& (t2.lease_timeout_at is Some ==> t2.lease_timeout_at.unwrap() > now)
                    &&& (t2.retry_timeout_at is Some ==> t2.retry_timeout_at.unwrap() > now)
                    &&& (t2.retry_timeout_at is Some && t2.retry_timeout_at != t1.retry_timeout_at ==> work2.contains(at_v(t2.retry_timeout_at.unwrap(), id)))
                }
            }
        }),
    decreases ids.len(),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    let n = now as nat;
    let rt = cfg.retry_timeout as nat;
    if ids.len() == 0 {
        assert((send + Seq::<DispatchV>::empty()) =~= send);
    } else {
        lemma_no_dup_last(ids);
        let ids0 = ids.drop_last();
        let x = ids.last();
        assert forall|i: int| 0 <= i < ids0.len() && b.objects.contains_key(#[trigger] ids0[i]) implies b.objects[ids0[i]].project(n) == b.objects[ids0[i]] by {
            assert(ids0[i] == ids[i]);
        }
        tr_due(b, ids0, now, cfg, work, send);
        let b1 = k_due(b, ids0, n, rt);
        let (n1, work1, send1) = due_fold(cfg, ids0, translate(b), work, send, now);
        assert(ids[ids.len() - 1] == x);
        assert(b.objects.contains_key(x) ==> b1.objects[x] == b.objects[x]);
        tr_due_one(b1, x, now, cfg, work1, send1);
        lemma_due_one_keeps(b1, x, n, rt);
        lemma_due_fold_step(cfg, ids, translate(b), work, send, now);
        let b2 = k_due_one(b1, x, n, rt);
        let (n2, work2, send2) = due_step(cfg, x, n1, work1, send1, now);
        assert(k_due(b, ids, n, rt) == b2);
        assert(b2.objects.dom() =~= b.objects.dom());
        let s0 = k_due_sends(b, ids0, n, rt);
        let s1 = k_due_one_sends(b1, x, n, rt);
        assert(k_due_sends(b, ids, n, rt) == s0 + s1);
        assert(send2.to_multiset() =~= (send + (s0 + s1)).to_multiset());
        assert forall|i: int| work.len() <= i < work2.len() implies exists|id: Seq<char>| ids.contains(id) && #[trigger] b.objects.contains_key(id) && b2.objects[id].task is Some
            && b2.objects[id].task.unwrap().retry_timeout_at is Some && #[trigger] work2[i] == at_v(b2.objects[id].task.unwrap().retry_timeout_at.unwrap(), id) by {
            if i < work1.len() {
                let id = choose|id: Seq<char>| ids0.contains(id) && #[trigger] b.objects.contains_key(id) && b1.objects[id].task is Some
                    && b1.objects[id].task.unwrap().retry_timeout_at is Some && work1[i] == at_v(b1.objects[id].task.unwrap().retry_timeout_at.unwrap(), id);
                assert(id != x);
                assert(b2.objects[id] == b1.objects[id]);
                let j = choose|j: int| 0 <= j < ids0.len() && ids0[j] == id;
                assert(ids[j] == id);
            } else {
                assert(b.objects.contains_key(x) && b2.objects[x].task is Some && b2.objects[x].task.unwrap().retry_timeout_at is Some);
                assert(work2[i] == work2.last());
            }
        }
        assert forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && !ids.contains(id) implies b2.objects[id] == b.objects[id] by {
            lemma_contains_split(ids, id);
        }
        assert forall|id: Seq<char>| ids.contains(id) && #[trigger] b.objects.contains_key(id) implies {
            let p = b.objects[id];
            let q = b2.objects[id];
            &&& q.project(n) == q
            &&& q.state == p.state
            &&& q.timeout_at == p.timeout_at
            &&& q.callbacks == p.callbacks
            &&& q.state != PromiseState::Pending ==> q.listeners.len() == 0
            &&& !lease_due(q, n)
            &&& !retry_due(q, n)
            &&& q.task is Some == p.task is Some
            &&& q.task is Some ==> {
                let t2 = q.task.unwrap();
                let t1 = p.task.unwrap();
                &&& t2.version == t1.version
                &&& (t2.lease_timeout_at == t1.lease_timeout_at || t2.lease_timeout_at is None)
                &&& (t2.lease_timeout_at is Some ==> t2.lease_timeout_at.unwrap() > now)
                &&& (t2.retry_timeout_at is Some ==> t2.retry_timeout_at.unwrap() > now)
                &&& (t2.retry_timeout_at is Some && t2.retry_timeout_at != t1.retry_timeout_at ==> work2.contains(at_v(t2.retry_timeout_at.unwrap(), id)))
            }
        } by {
            lemma_contains_split(ids, id);
            if id == x {
                assert(b1.objects[x] == b.objects[x]);
                if b2.objects[x].task is Some && b2.objects[x].task.unwrap().retry_timeout_at is Some && b2.objects[x].task.unwrap().retry_timeout_at != b.objects[x].task.unwrap().retry_timeout_at {
                    assert(work2.len() == work1.len() + 1);
                    assert(work2.last() == at_v(b2.objects[x].task.unwrap().retry_timeout_at.unwrap(), x));
                    assert(work2[work2.len() - 1] == work2.last());
                }
            } else {
                assert(b2.objects[id] == b1.objects[id]);
                if b1.objects[id].task is Some && b1.objects[id].task.unwrap().retry_timeout_at is Some && b1.objects[id].task.unwrap().retry_timeout_at != b.objects[id].task.unwrap().retry_timeout_at {
                    let j = choose|j: int| 0 <= j < work1.len() && work1[j] == at_v(b1.objects[id].task.unwrap().retry_timeout_at.unwrap(), id);
                    assert(work2[j] == work1[j]);
                }
            }
        }
    }
}


/// `On(ids)`: the kernel's steps compute the model's step on the translated
/// state, send the same up to order, and the work the model starts is read off
/// the objects: a resume per callback and an unblock note per settled
/// promise, a timer per offer re-armed, none of it due before now.
pub proof fn tr_on(b: AState, ids: Seq<Seq<char>>, now: u64, cfg: Resonate)
    requires
        inv(now as nat, b),
        leases_from_ttl(b),
        0 < cfg.retry_timeout <= MAX_TIME,
        now <= MAX_TIME,
        ids.no_duplicates(),
    ensures
        ({
            let n = now as nat;
            let rt = cfg.retry_timeout as nat;
            let b2 = k_on(b, ids, n, rt);
            let o = on_v(cfg, ids, translate(b), now);
            &&& translate(b2) == o.next
            &&& o.send.to_multiset() == k_on_sends(b, ids, n, rt).to_multiset()
            &&& inv(n, b2)
            &&& leases_from_ttl(b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            // the work
            &&& forall|i: int| 0 <= i < o.work.len() ==> match #[trigger] o.work[i] {
                Sched::Later(InternalV::On(_)) => true,
                Sched::Timer(t, InternalV::On(_)) => t > now,
                _ => false,
            }
            &&& forall|i: int| 0 <= i < o.work.len() && (#[trigger] o.work[i]) is Later ==> spawned(b, ids, n, o.work[i])
            &&& forall|x: Seq<char>, w: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now
                && #[trigger] b.objects[x].callbacks.contains(w) ==> o.work.contains(later2_v(x, w))
            &&& forall|x: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now
                && b.objects[x].listeners.len() > 0 ==> o.work.contains(Sched::Later(InternalV::On(seq![x])))
            // the objects
            &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && !ids.contains(id) ==> b2.objects[id] == b.objects[id]
            &&& forall|id: Seq<char>| ids.contains(id) && #[trigger] b.objects.contains_key(id) ==> {
                let p = b.objects[id];
                let q = b2.objects[id];
                &&& q.project(n) == q
                &&& q.state == p.project(n).state
                &&& q.timeout_at == p.timeout_at
                &&& (q.state == PromiseState::Pending ==> p.state == PromiseState::Pending && q.timeout_at > now)
                &&& (q.state != PromiseState::Pending ==> q.listeners.len() == 0)
                &&& !lease_due(q, n)
                &&& !retry_due(q, n)
                &&& (forall|w: Seq<char>| ids.contains(w) ==> !(q.state != PromiseState::Pending && #[trigger] q.callbacks.contains(w)))
                &&& (q.task is Some ==> {
                    let t2 = q.task.unwrap();
                    &&& (t2.lease_timeout_at is Some ==> p.task is Some && p.task.unwrap().lease_timeout_at == t2.lease_timeout_at && t2.lease_timeout_at.unwrap() > now)
                    &&& (t2.retry_timeout_at is Some ==> t2.retry_timeout_at.unwrap() > now
                        && (o.work.contains(at_v(t2.retry_timeout_at.unwrap(), id)) || (p.task is Some && p.task.unwrap().retry_timeout_at == t2.retry_timeout_at)))
                })
            }
        }),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    let n = now as nat;
    let rt = cfg.retry_timeout as nat;
    let s0 = translate(b);
    // phase 1
    tr_deadlines(b, ids, now, Seq::empty());
    let b1 = phase_deadlines(b, ids, n);
    let (n1, work1) = deadlines_fold(ids, s0, Seq::empty(), now);
    assert forall|i: int| 0 <= i < ids.len() && b1.objects.contains_key(#[trigger] ids[i]) implies b1.objects[ids[i]].project(n) == b1.objects[ids[i]] by {
        assert(ids.contains(ids[i]));
        echod_kernel::external_proof::lemma_project_idem(b.objects[ids[i]], n);
    }
    // phase 2
    tr_resumes(b1, ids, ids, now);
    let b1r = k_resumes(b1, ids, ids, n);
    let n2 = resumes_fold(ids, ids, n1, now);
    assert(translate(b1r) == n2);
    assert forall|i: int| 0 <= i < ids.len() && b1r.objects.contains_key(#[trigger] ids[i]) implies b1r.objects[ids[i]].project(n) == b1r.objects[ids[i]] by {
        assert(b1.objects[ids[i]].project(n) == b1.objects[ids[i]]);
    }
    // phase 3
    tr_due(b1r, ids, now, cfg, work1, Seq::empty());
    let b2 = k_due(b1r, ids, n, rt);
    let (n3, work3, send3) = due_fold(cfg, ids, n2, work1, Seq::empty(), now);
    assert(k_on(b, ids, n, rt) == b2);
    let o = on_v(cfg, ids, s0, now);
    assert(o.next == n3 && o.work == work3 && o.send == send3);
    assert(k_on_sends(b, ids, n, rt) == k_due_sends(b1r, ids, n, rt));
    assert((Seq::<DispatchV>::empty() + k_due_sends(b1r, ids, n, rt)) =~= k_due_sends(b1r, ids, n, rt));
    assert(b2.objects.dom() =~= b.objects.dom());
    // the work: the Laters from phase 1, the timers from phase 3
    assert forall|i: int| 0 <= i < work3.len() implies (match #[trigger] work3[i] {
        Sched::Later(InternalV::On(_)) => true,
        Sched::Timer(t, InternalV::On(_)) => t > now,
        _ => false,
    }) && (work3[i] is Later ==> spawned(b, ids, n, work3[i])) by {
        if i < work1.len() {
            assert(work3[i] == work1[i]);
            assert(spawned(b, ids, n, work1[i]));
            let x = choose|x: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= n && (
                work1[i] == Sched::Later(InternalV::On(seq![x])) || exists|w: Seq<char>| #[trigger] b.objects[x].callbacks.contains(w) && work1[i] == later2_v(x, w));
        } else {
            let id = choose|id: Seq<char>| ids.contains(id) && #[trigger] b1r.objects.contains_key(id) && b2.objects[id].task is Some
                && b2.objects[id].task.unwrap().retry_timeout_at is Some && #[trigger] work3[i] == at_v(b2.objects[id].task.unwrap().retry_timeout_at.unwrap(), id);
            assert(b2.objects[id].task.unwrap().retry_timeout_at.unwrap() > now);
        }
    }
    assert forall|x: Seq<char>, w: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now
        && #[trigger] b.objects[x].callbacks.contains(w) implies work3.contains(later2_v(x, w)) by {
        let i = choose|i: int| 0 <= i < work1.len() && work1[i] == later2_v(x, w);
        assert(work3[i] == later2_v(x, w));
    }
    assert forall|x: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now
        && b.objects[x].listeners.len() > 0 implies work3.contains(Sched::Later(InternalV::On(seq![x]))) by {
        let i = choose|i: int| 0 <= i < work1.len() && work1[i] == Sched::Later(InternalV::On(seq![x]));
        assert(work3[i] == Sched::Later(InternalV::On(seq![x])));
    }
    // the objects
    assert forall|id: Seq<char>| ids.contains(id) && #[trigger] b.objects.contains_key(id) implies {
        let p = b.objects[id];
        let q = b2.objects[id];
        &&& q.project(n) == q
        &&& q.state == p.project(n).state
        &&& q.timeout_at == p.timeout_at
        &&& (q.state == PromiseState::Pending ==> p.state == PromiseState::Pending && q.timeout_at > now)
        &&& (q.state != PromiseState::Pending ==> q.listeners.len() == 0)
        &&& !lease_due(q, n)
        &&& !retry_due(q, n)
        &&& (forall|w: Seq<char>| ids.contains(w) ==> !(q.state != PromiseState::Pending && #[trigger] q.callbacks.contains(w)))
        &&& (q.task is Some ==> {
            let t2 = q.task.unwrap();
            &&& (t2.lease_timeout_at is Some ==> p.task is Some && p.task.unwrap().lease_timeout_at == t2.lease_timeout_at && t2.lease_timeout_at.unwrap() > now)
            &&& (t2.retry_timeout_at is Some ==> t2.retry_timeout_at.unwrap() > now
                && (work3.contains(at_v(t2.retry_timeout_at.unwrap(), id)) || (p.task is Some && p.task.unwrap().retry_timeout_at == t2.retry_timeout_at)))
        })
    } by {
        let p = b.objects[id];
        let p1 = b1.objects[id];
        let pr = b1r.objects[id];
        let q = b2.objects[id];
        assert(p1 == p.project(n));
        lemma_projected_obj(p1, n);
        assert(pr.state == p1.state && pr.timeout_at == p1.timeout_at);
        assert(q.state == pr.state && q.timeout_at == pr.timeout_at && q.callbacks == pr.callbacks);
        if q.state == PromiseState::Pending {
            assert(p1.state == PromiseState::Pending);
            assert(p.state == PromiseState::Pending);
            assert(p1.timeout_at > now);
        }
        assert forall|w: Seq<char>| ids.contains(w) implies !(q.state != PromiseState::Pending && #[trigger] q.callbacks.contains(w)) by {
            let i = choose|i: int| 0 <= i < ids.len() && ids[i] == id;
            let j = choose|j: int| 0 <= j < ids.len() && ids[j] == w;
            assert(!awaits(b1r, ids[i], ids[j], n));
            assert(pr.project(n) == pr);
        }
        match q.task {
            None => {},
            Some(t2) => {
                assert(pr.task is Some);
                let tr = pr.task.unwrap();
                assert(p1.task is Some);
                let t1 = p1.task.unwrap();
                match p.task {
                    None => {
                        assert(p1.task is None);
                    },
                    Some(t0) => {
                        assert(t1 == t0.view_through(p.project_promise(n)));
                        if t2.lease_timeout_at is Some {
                            assert(t2.lease_timeout_at == tr.lease_timeout_at);
                            assert(tr.lease_timeout_at == t1.lease_timeout_at);
                            assert(t1 == t0);
                        }
                        if t2.retry_timeout_at is Some {
                            if t2.retry_timeout_at == tr.retry_timeout_at {
                                assert(tr.retry_timeout_at == t1.retry_timeout_at || (tr.retry_timeout_at is Some && tr.retry_timeout_at.unwrap() <= now));
                                assert(tr.retry_timeout_at == t1.retry_timeout_at);
                                assert(t1 == t0);
                            } else {
                                assert(work3.contains(at_v(t2.retry_timeout_at.unwrap(), id)));
                            }
                        }
                    },
                }
            },
        }
    }
}

} // verus!
