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
use resonate::{PState, TState, Time};

use crate::canon::*;
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

} // verus!
