//! The model drains to the kernel's sweep: from a configuration whose state is
//! the translation of a kernel state and whose pending work covers what is
//! due in it, a run of silent steps, each the model's `On` step, reaches the
//! translation of a swept state, the sweep's own result; it sends what the
//! sweep sends. The steps are run in an order the sweep absorbs: overdue
//! timers first by deadline (as the semantics demand), then the resumes
//! whose promise is the first of the awaiter's settled awaiteds.

use vstd::prelude::*;

use accordant::refinement::{end, lemma_end_add, lemma_legal_add, lemma_project_add, shows};
use accordant::semantics::{
    before, due_le, is_first, is_overdue, legal, overdue, project, ready, req_of, run, schedule, start_all, step, Cfg, Config, Execution, Lab, Label,
};
use accordant::{Model, Sched, Time};
use echod_kernel::internal::{lease_due, retry_due};
use echod_kernel::properties::{inv, inv_obj};
use echod_kernel::properties_proof::lemma_inv_pointwise;
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::twins::*;
use resonate::{Dispatch, Internal, Resonate, Server};

use crate::absorb::*;
use crate::canon::*;
use crate::machine::*;
use crate::onstep::*;
use crate::sweep::*;
use crate::sweep_proof::*;
use crate::theorem::{abstract_of, dial_ok, mdeadline_at_timer, timers_cover, translate};
use crate::trans::*;

verus! {

// ------------------------------------------------------------------ shapes

pub open spec fn on_ids(step: Internal) -> Seq<Seq<char>> {
    match step@ {
        InternalV::On(ids) => ids,
        _ => Seq::empty(),
    }
}

pub open spec fn is_on(step: Internal) -> bool {
    step@ matches InternalV::On(_)
}

pub open spec fn item_ids(it: Sched<Internal>) -> Seq<Seq<char>> {
    on_ids(req_of(it))
}

/// Ready to run: a `Later`, or a timer whose time has come.
pub open spec fn ready_item(it: Sched<Internal>, now: u64) -> bool {
    match it {
        Sched::Later(_) => true,
        Sched::Timer(t, _) => t <= now,
    }
}

/// The model's work along a drain: `On` steps without duplicate ids, timers on
/// one id, laters on one or two whose first is settled.
pub open spec fn work_wf(b: AState, s: Seq<Sched<Internal>>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> {
        let ids = item_ids(#[trigger] s[i]);
        &&& is_on(req_of(s[i]))
        &&& ids.no_duplicates()
        &&& (s[i] is Timer ==> ids.len() == 1)
        &&& (s[i] is Later ==> 1 <= ids.len() <= 2 && b.objects.contains_key(ids[0]) && b.objects[ids[0]].state != PromiseState::Pending)
    }
}

pub open spec fn covered(s: Seq<Sched<Internal>>, now: u64, id: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && ready_item(#[trigger] s[i], now) && item_ids(s[i]).contains(id)
}

pub open spec fn covered2(s: Seq<Sched<Internal>>, now: u64, x: Seq<char>, w: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && ready_item(#[trigger] s[i], now) && item_ids(s[i]).contains(x) && item_ids(s[i]).contains(w)
}

pub open spec fn pending_due(b: AState, id: Seq<char>, now: u64) -> bool {
    b.objects.contains_key(id) && b.objects[id].state == PromiseState::Pending && b.objects[id].timeout_at <= now
}

/// The relation a drain keeps: the model holds the kernel state, translated;
/// everything due in the kernel state is covered by ready work; every
/// deadline ahead has its timer.
pub open spec fn drain_inv(cfg: Concrete, b: AState, s: Cfg<Resonate>) -> bool {
    let now = s.now;
    let n = now as nat;
    &&& now <= MAX_TIME
    &&& dial_ok(cfg)
    &&& inv(n, b)
    &&& leases_from_ttl(b)
    &&& b.objects.dom().finite()
    &&& b.schedules == Map::<Seq<char>, ASchedule>::empty()
    &&& s.state@ == translate(b)
    &&& work_wf(b, s.internals)
    &&& forall|id: Seq<char>| pending_due(b, id, now) ==> covered(s.internals, now, id)
    &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && lease_due(b.objects[id], n) ==> covered(s.internals, now, id)
    &&& forall|id: Seq<char>| #[trigger] b.objects.contains_key(id) && retry_due(b.objects[id], n) ==> covered(s.internals, now, id)
    &&& forall|x: Seq<char>, w: Seq<char>| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && #[trigger] b.objects[x].callbacks.contains(w)
        ==> covered2(s.internals, now, x, w)
    &&& forall|x: Seq<char>| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && b.objects[x].listeners.len() > 0 ==> covered(s.internals, now, x)
    &&& forall|id: Seq<char>, t: nat| #[trigger] b.objects.contains_key(id) && #[trigger] mdeadline_at(b.objects[id], t) && t > now ==> mdeadline_at_timer(s.internals, id, t)
}

// ------------------------------------------------------------- the measure

pub open spec fn count_ready(s: Seq<Sched<Internal>>, now: u64) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { count_ready(s.drop_last(), now) + (if ready_item(s.last(), now) { 1nat } else { 0nat }) }
}

pub open spec fn due_set(b: AState, now: u64) -> Set<Seq<char>> {
    b.objects.dom().filter(|id: Seq<char>| pending_due(b, id, now))
}

pub proof fn lemma_count_ready_some(s: Seq<Sched<Internal>>, now: u64, i: int)
    requires
        0 <= i < s.len(),
        ready_item(s[i], now),
    ensures
        count_ready(s, now) > 0,
    decreases s.len(),
{
    if i < s.len() - 1 {
        lemma_count_ready_some(s.drop_last(), now, i);
    }
}

pub proof fn lemma_count_ready_none(s: Seq<Sched<Internal>>, now: u64)
    requires
        forall|i: int| 0 <= i < s.len() ==> !ready_item(#[trigger] s[i], now),
    ensures
        count_ready(s, now) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        assert forall|i: int| 0 <= i < s.drop_last().len() implies !ready_item(#[trigger] s.drop_last()[i], now) by {
            assert(s.drop_last()[i] == s[i]);
        }
        lemma_count_ready_none(s.drop_last(), now);
        assert(s[s.len() - 1] == s.last());
    }
}

pub proof fn lemma_count_ready_add(a: Seq<Sched<Internal>>, b: Seq<Sched<Internal>>, now: u64)
    ensures
        count_ready(a + b, now) == count_ready(a, now) + count_ready(b, now),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_count_ready_add(a, b.drop_last(), now);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

pub proof fn lemma_count_ready_remove(s: Seq<Sched<Internal>>, now: u64, i: int)
    requires
        0 <= i < s.len(),
        ready_item(s[i], now),
    ensures
        count_ready(s, now) == count_ready(s.remove(i), now) + 1,
{
    let a = s.subrange(0, i);
    let m = seq![s[i]];
    let c = s.subrange(i + 1, s.len() as int);
    assert(s =~= a + m + c);
    assert(s.remove(i) == a + c);
    lemma_count_ready_add(a + m, c, now);
    lemma_count_ready_add(a, m, now);
    lemma_count_ready_add(a, c, now);
    assert(count_ready(m, now) == 1) by {
        assert(m.len() == 1);
        assert(m.last() == s[i]);
        assert(m.drop_last() =~= Seq::<Sched<Internal>>::empty());
        assert(count_ready(Seq::<Sched<Internal>>::empty(), now) == 0);
    }
}

// ----------------------------------------------------- multisets under lift

pub proof fn lemma_count_map<A, B>(s: Seq<A>, f: spec_fn(A) -> B, v: A)
    requires
        vstd::relations::injective(f),
    ensures
        s.map_values(f).to_multiset().count(f(v)) == s.to_multiset().count(v),
    decreases s.len(),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_axioms;
    if s.len() == 0 {
        assert(s.map_values(f) =~= Seq::<B>::empty());
    } else {
        lemma_count_map(s.drop_last(), f, v);
        assert(s.map_values(f) =~= s.drop_last().map_values(f).push(f(s.last())));
        assert(s =~= s.drop_last().push(s.last()));
    }
}

pub proof fn lemma_count_map_out<A, B>(s: Seq<A>, f: spec_fn(A) -> B, y: B)
    requires
        forall|v: A| #[trigger] f(v) != y,
    ensures
        s.map_values(f).to_multiset().count(y) == 0,
    decreases s.len(),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_axioms;
    if s.len() == 0 {
        assert(s.map_values(f) =~= Seq::<B>::empty());
    } else {
        lemma_count_map_out(s.drop_last(), f, y);
        assert(s.map_values(f) =~= s.drop_last().map_values(f).push(f(s.last())));
    }
}

/// Equal multisets stay equal under an injective map.
pub proof fn lemma_map_multiset_injective<A, B>(s1: Seq<A>, s2: Seq<A>, f: spec_fn(A) -> B)
    requires
        vstd::relations::injective(f),
        s1.to_multiset() == s2.to_multiset(),
    ensures
        s1.map_values(f).to_multiset() == s2.map_values(f).to_multiset(),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    assert forall|y: B| s1.map_values(f).to_multiset().count(y) == s2.map_values(f).to_multiset().count(y) by {
        if exists|v: A| #[trigger] f(v) == y {
            let v = choose|v: A| #[trigger] f(v) == y;
            lemma_count_map(s1, f, v);
            lemma_count_map(s2, f, v);
        } else {
            lemma_count_map_out(s1, f, y);
            lemma_count_map_out(s2, f, y);
        }
    }
    assert(s1.map_values(f).to_multiset() =~= s2.map_values(f).to_multiset());
}

pub proof fn lemma_lift_dispatch_injective()
    ensures
        vstd::relations::injective(|d: DispatchV| lift_dispatch(d)),
{
    let f = |d: DispatchV| lift_dispatch(d);
    assert forall|d1: DispatchV, d2: DispatchV| #[trigger] f(d1) == #[trigger] f(d2) implies d1 == d2 by {
        axiom_realised(empty_server_v(), ResponseV::Status(0), InternalV::On(Seq::empty()), d1);
        axiom_realised(empty_server_v(), ResponseV::Status(0), InternalV::On(Seq::empty()), d2);
    }
}

pub open spec fn empty_server_v() -> ServerV {
    ServerV { promises: Map::empty(), tasks: Map::empty(), schedules: Map::empty() }
}

// ------------------------------------------------------- picking the next step

/// Among the indices below `k` satisfying `p`, one is first.
pub proof fn lemma_first_index(p: spec_fn(int) -> bool, k: int)
    requires
        0 <= k,
    ensures
        (exists|i: int| 0 <= i < k && #[trigger] p(i)) ==> exists|i: int| 0 <= i < k && #[trigger] p(i) && forall|j: int| 0 <= j < i ==> !#[trigger] p(j),
    decreases k,
{
    if k > 0 {
        lemma_first_index(p, k - 1);
        if exists|i: int| 0 <= i < k && #[trigger] p(i) {
            if exists|i: int| 0 <= i < k - 1 && #[trigger] p(i) {
            } else {
                assert(p(k - 1));
                assert forall|j: int| 0 <= j < k - 1 implies !#[trigger] p(j) by {}
            }
        }
    }
}

/// Among the indices below `k` satisfying `p`, one has the least key.
pub proof fn lemma_argmin(p: spec_fn(int) -> bool, d: spec_fn(int) -> int, k: int)
    requires
        0 <= k,
    ensures
        (exists|i: int| 0 <= i < k && #[trigger] p(i)) ==> exists|i: int| 0 <= i < k && #[trigger] p(i) && forall|j: int| 0 <= j < k && #[trigger] p(j) ==> d(i) <= d(j),
    decreases k,
{
    if k > 0 {
        lemma_argmin(p, d, k - 1);
        if exists|i: int| 0 <= i < k && #[trigger] p(i) {
            if exists|i: int| 0 <= i < k - 1 && #[trigger] p(i) {
                let i = choose|i: int| 0 <= i < k - 1 && #[trigger] p(i) && forall|j: int| 0 <= j < k - 1 && #[trigger] p(j) ==> d(i) <= d(j);
                if p(k - 1) && d(k - 1) < d(i) {
                    let m = k - 1;
                    assert forall|j: int| 0 <= j < k && #[trigger] p(j) implies d(m) <= d(j) by {
                        if j < k - 1 {
                            assert(d(i) <= d(j));
                        }
                    }
                } else {
                    assert forall|j: int| 0 <= j < k && #[trigger] p(j) implies d(i) <= d(j) by {}
                }
            } else {
                let m = k - 1;
                assert(p(m));
                assert forall|j: int| 0 <= j < k && #[trigger] p(j) implies d(m) <= d(j) by {
                    assert(j == m);
                }
            }
        }
    }
}

/// A timer's time, as a key.
pub open spec fn due_key(s: Cfg<Resonate>, i: int) -> int {
    match s.internals[i] {
        Sched::Timer(t, _) => t as int,
        Sched::Later(_) => 0,
    }
}

#[verifier::rlimit(200)]
pub proof fn lemma_first_overdue(a: Resonate, s: Cfg<Resonate>)
    requires
        overdue(a, s),
    ensures
        exists|i: int| 0 <= i < s.internals.len() && #[trigger] is_first(a, s, i),
{
    let p = |i: int| is_overdue(a, s, i);
    let d = |i: int| due_key(s, i);
    let k = s.internals.len() as int;
    let i0 = choose|i: int| #[trigger] is_overdue(a, s, i);
    assert(p(i0));
    lemma_argmin(p, d, k);
    let i = choose|i: int| 0 <= i < k && #[trigger] p(i) && forall|j: int| 0 <= j < k && #[trigger] p(j) ==> d(i) <= d(j);
    assert forall|j: int| #[trigger] is_overdue(a, s, j) implies due_le(s.internals[i], s.internals[j]) by {
        assert(p(j));
        assert(d(i) <= d(j));
    }
    assert(is_first(a, s, i));
}

/// Among the settled promises holding a callback for `w`, one comes first in
/// the objects' order.
#[verifier::rlimit(200)]
pub proof fn lemma_min_awaited(b: AState, w: Seq<char>, now: nat)
    requires
        exists|x: Seq<char>| #[trigger] awaits(b, x, w, now),
        b.objects.dom().finite(),
    ensures
        exists|i: int| 0 <= i < ids_of(b).len() && #[trigger] awaits(b, ids_of(b)[i], w, now) && forall|j: int| 0 <= j < i ==> !#[trigger] awaits(b, ids_of(b)[j], w, now),
{
    let ids = ids_of(b);
    let p = |i: int| 0 <= i < ids.len() && awaits(b, ids[i], w, now);
    let x = choose|x: Seq<char>| #[trigger] awaits(b, x, w, now);
    lemma_ids_cover(b);
    assert(ids.contains(x));
    let i0 = choose|i: int| 0 <= i < ids.len() && ids[i] == x;
    assert(p(i0));
    lemma_first_index(p, ids.len() as int);
    let i = choose|i: int| 0 <= i < ids.len() && #[trigger] p(i) && forall|j: int| 0 <= j < i ==> !#[trigger] p(j);
    assert forall|j: int| 0 <= j < i implies !#[trigger] awaits(b, ids[j], w, now) by {
        assert(!p(j));
    }
}

// --------------------------------------------------------------- one step

/// The model's one internal outcome on `On(ids)`.
pub proof fn lemma_resonate_internal(a: Resonate, step: Internal, st: Server, now: Time)
    requires
        is_on(step),
    ensures
        ({
            let o = on_v(a, on_ids(step), st@, now);
            &&& a.spec_internal(step, st, now).len() == 1
            &&& a.spec_internal(step, st, now)[0] == lift_inout(o)
        }),
{
    let o = resonate::twins::int(a, step@, st@, now);
    assert(o == on_v(a, on_ids(step), st@, now));
    assert(!o.pending);
}

/// The configuration after the ready item `i` runs.
pub open spec fn next_cfg(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int) -> Cfg<Resonate> {
    let o = on_v(abstract_of(cfg), item_ids(s.internals[i]), translate(b), s.now);
    Config {
        state: lift_server(o.next),
        internals: start_all(s.internals.remove(i), o.work.map_values(|w: Sched<InternalV>| lift_sched(w)), s.now),
        sent: s.sent + o.send.map_values(|d: DispatchV| lift_dispatch(d)),
        ..s
    }
}

/// The kernel state after it.
pub open spec fn next_state(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int) -> AState {
    k_on(b, item_ids(s.internals[i]), s.now as nat, cfg.retry_timeout as nat)
}

/// Running the item is a step of the model.
pub proof fn lemma_run_is_step(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int)
    requires
        s.state@ == translate(b),
        work_wf(b, s.internals),
        0 <= i < s.internals.len(),
        ready_item(s.internals[i], s.now),
        overdue(abstract_of(cfg), s) ==> is_first(abstract_of(cfg), s, i),
    ensures
        run(abstract_of(cfg), s, Label::Silent, next_cfg(cfg, b, s, i)),
{
    let a = abstract_of(cfg);
    let now = s.now;
    let it = s.internals[i];
    let ids = item_ids(it);
    let o = on_v(a, ids, translate(b), now);
    let s2 = next_cfg(cfg, b, s, i);
    assert(is_on(req_of(it)));
    lemma_resonate_internal(a, req_of(it), s.state, now);
    let outs = a.spec_internal(req_of(it), s.state, now);
    assert(outs.len() == 1 && outs[0] == lift_inout(o));
    assert(ready(now, it));
    assert(s2 == Config {
        state: outs[0].next,
        internals: start_all(s.internals.remove(i), outs[0].work, now),
        sent: s.sent + outs[0].send,
        ..s
    });
}

/// The state after the step is the kernel's, the sweep absorbs it, the sends
/// are accounted.
pub proof fn lemma_run_state(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int)
    requires
        drain_inv(cfg, b, s),
        0 <= i < s.internals.len(),
        resume_ok(phase_deadlines(b, item_ids(s.internals[i]), s.now as nat), item_ids(s.internals[i]), s.now as nat),
    ensures
        ({
            let n = s.now as nat;
            let t = cfg.retry_timeout as nat;
            let ids = item_ids(s.internals[i]);
            let b2 = next_state(cfg, b, s, i);
            let s2 = next_cfg(cfg, b, s, i);
            &&& s2.state@ == translate(b2)
            &&& inv(n, b2)
            &&& leases_from_ttl(b2)
            &&& b2.objects.dom() == b.objects.dom()
            &&& b2.schedules == b.schedules
            &&& sweep_fn(b2, n, t).objects == sweep_fn(b, n, t).objects
            &&& sweep_sends(b, n, t).to_multiset() == (k_on_sends(b, ids, n, t) + sweep_sends(b2, n, t)).to_multiset()
            &&& s2.sent.to_multiset() == s.sent.to_multiset().add(lift_dispatches(k_on_sends(b, ids, n, t)).to_multiset())
        }),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    let a = abstract_of(cfg);
    let now = s.now;
    let n = now as nat;
    let t = cfg.retry_timeout as nat;
    let ids = item_ids(s.internals[i]);
    let o = on_v(a, ids, translate(b), now);
    assert(ids.no_duplicates());
    tr_on(b, ids, now, a);
    absorb_on(b, ids, n, t);
    axiom_realised(o.next, ResponseV::Status(0), InternalV::On(Seq::empty()), DispatchV::Execute { id: Seq::empty(), version: 0 });
    lemma_lift_dispatch_injective();
    lemma_map_multiset_injective(o.send, k_on_sends(b, ids, n, t), |d: DispatchV| lift_dispatch(d));
}

/// The work after the step, as a sequence: what survives, then what the step
/// started, each timer at its own time (none is in the past).
pub open spec fn added_items(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int) -> Seq<Sched<Internal>> {
    let o = on_v(abstract_of(cfg), item_ids(s.internals[i]), translate(b), s.now);
    o.work.map_values(|w: Sched<InternalV>| lift_sched(w)).map_values(|w: Sched<Internal>| schedule(s.now, w))
}

/// `it` is among `s` at an index other than `i`.
pub open spec fn survives(s: Seq<Sched<Internal>>, i: int, it: Sched<Internal>) -> bool {
    exists|k: int| 0 <= k < s.len() && k != i && #[trigger] s[k] == it
}

/// `it` is among `rest`.
pub open spec fn kept(rest: Seq<Sched<Internal>>, it: Sched<Internal>) -> bool {
    exists|j: int| 0 <= j < rest.len() && #[trigger] rest[j] == it
}

/// What the work looks like after the step: every item but the one run
/// survives, at some index, and what the step started is appended.
pub proof fn lemma_run_work(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int)
    requires
        0 <= i < s.internals.len(),
    ensures
        next_cfg(cfg, b, s, i).internals == s.internals.remove(i) + added_items(cfg, b, s, i),
        added_items(cfg, b, s, i).len() == on_v(abstract_of(cfg), item_ids(s.internals[i]), translate(b), s.now).work.len(),
        forall|j: int| 0 <= j < s.internals.remove(i).len() ==> survives(s.internals, i, #[trigger] s.internals.remove(i)[j]),
        forall|k: int| 0 <= k < s.internals.len() && k != i ==> kept(s.internals.remove(i), #[trigger] s.internals[k]),
{
    let rest = s.internals.remove(i);
    let s2 = next_cfg(cfg, b, s, i);
    assert(s2.internals =~= rest + added_items(cfg, b, s, i));
    assert forall|j: int| 0 <= j < rest.len() implies survives(s.internals, i, #[trigger] rest[j]) by {
        if j < i {
            assert(s.internals[j] == rest[j]);
        } else {
            assert(s.internals[j + 1] == rest[j]);
        }
    }
    assert forall|k: int| 0 <= k < s.internals.len() && k != i implies kept(rest, #[trigger] s.internals[k]) by {
        if k < i {
            assert(rest[k] == s.internals[k]);
        } else {
            assert(rest[k - 1] == s.internals[k]);
        }
    }
}

/// What a later the deadlines phase spawns looks like: its first id a promise
/// among the ids pending and past its deadline, its ids one or two, distinct.
pub proof fn lemma_spawned_shape(b: AState, ids: Seq<Seq<char>>, now: nat, w: Sched<InternalV>)
    requires
        inv(now, b),
        spawned(b, ids, now, w),
    ensures
        w is Later,
        w->Later_0 is On,
        ({
            let wi = on_v_ids(w->Later_0);
            &&& 1 <= wi.len() <= 2
            &&& wi.no_duplicates()
            &&& ids.contains(wi[0])
            &&& b.objects.contains_key(wi[0])
            &&& b.objects[wi[0]].state == PromiseState::Pending
            &&& b.objects[wi[0]].timeout_at <= now
        }),
{
    lemma_inv_pointwise(now, b);
    let x = choose|x: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= now && (
        w == Sched::Later(InternalV::On(seq![x])) || exists|y: Seq<char>| #[trigger] b.objects[x].callbacks.contains(y) && w == later2_v(x, y));
    assert(inv_obj(now, b, x));
    assert(b.objects[x].id == x);
    if w == Sched::Later(InternalV::On(seq![x])) {
    } else {
        let y = choose|y: Seq<char>| #[trigger] b.objects[x].callbacks.contains(y) && w == later2_v(x, y);
        assert(y != x);
        assert(seq![x, y].no_duplicates());
    }
}

/// One item the step started: a later as the model spawned it, or a timer
/// ahead of now; an `On` step either way, its ids the model's.
pub proof fn lemma_added_item(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int, j: int)
    requires
        drain_inv(cfg, b, s),
        0 <= i < s.internals.len(),
        0 <= j < on_v(abstract_of(cfg), item_ids(s.internals[i]), translate(b), s.now).work.len(),
    ensures
        ({
            let now = s.now;
            let ids = item_ids(s.internals[i]);
            let o = on_v(abstract_of(cfg), ids, translate(b), now);
            let w = o.work[j];
            let it = added_items(cfg, b, s, i)[j];
            &&& is_on(req_of(it))
            &&& (w is Later || w is Timer)
            &&& (w is Later ==> w->Later_0 is On && it == Sched::Later(lift_internal(w->Later_0)) && item_ids(it) == on_v_ids(w->Later_0) && spawned(b, ids, now as nat, w))
            &&& (w is Timer ==> w->Timer_1 is On && w->Timer_0 > now && it == Sched::Timer(w->Timer_0, lift_internal(w->Timer_1)) && item_ids(it) == on_v_ids(w->Timer_1))
        }),
{
    let a = abstract_of(cfg);
    let now = s.now;
    let ids = item_ids(s.internals[i]);
    let o = on_v(a, ids, translate(b), now);
    tr_on(b, ids, now, a);
    let w = o.work[j];
    let newwork = o.work.map_values(|w: Sched<InternalV>| lift_sched(w));
    let added = added_items(cfg, b, s, i);
    assert(added[j] == schedule(now, newwork[j]));
    match w {
        Sched::Later(v) => {
            axiom_realised(empty_server_v(), ResponseV::Status(0), v, DispatchV::Execute { id: Seq::empty(), version: 0 });
            assert(newwork[j] == Sched::Later(lift_internal(v)));
            assert(added[j] == Sched::Later(lift_internal(v)));
        },
        Sched::Timer(tt, v) => {
            axiom_realised(empty_server_v(), ResponseV::Status(0), v, DispatchV::Execute { id: Seq::empty(), version: 0 });
            assert(newwork[j] == Sched::Timer(tt, lift_internal(v)));
            assert(tt > now);
            assert(added[j] == Sched::Timer(tt, lift_internal(v)));
        },
    }
}

/// The ids of an `On` view.
pub open spec fn on_v_ids(v: InternalV) -> Seq<Seq<char>> {
    match v {
        InternalV::On(ids) => ids,
        _ => Seq::empty(),
    }
}


/// One item's shape along a drain.
pub open spec fn item_wf(b: AState, it: Sched<Internal>) -> bool {
    let ids = item_ids(it);
    &&& is_on(req_of(it))
    &&& ids.no_duplicates()
    &&& (it is Timer ==> ids.len() == 1)
    &&& (it is Later ==> 1 <= ids.len() <= 2 && b.objects.contains_key(ids[0]) && b.objects[ids[0]].state != PromiseState::Pending)
}

pub proof fn lemma_work_wf_items(b: AState, s: Seq<Sched<Internal>>)
    ensures
        work_wf(b, s) == forall|j: int| 0 <= j < s.len() ==> item_wf(b, #[trigger] s[j]),
{
}

/// A surviving item keeps its shape: the settled stay settled.
pub proof fn lemma_item_wf_rest(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int, j: int)
    requires
        drain_inv(cfg, b, s),
        0 <= i < s.internals.len(),
        0 <= j < s.internals.remove(i).len(),
    ensures
        item_wf(next_state(cfg, b, s, i), s.internals.remove(i)[j]),
{
    let a = abstract_of(cfg);
    let now = s.now;
    let n = now as nat;
    let ids = item_ids(s.internals[i]);
    let b2 = next_state(cfg, b, s, i);
    tr_on(b, ids, now, a);
    lemma_run_work(cfg, b, s, i);
    let rest = s.internals.remove(i);
    let it = rest[j];
    assert(survives(s.internals, i, it));
    let k = choose|k: int| 0 <= k < s.internals.len() && k != i && #[trigger] s.internals[k] == it;
    lemma_work_wf_items(b, s.internals);
    assert(item_wf(b, it));
    let wi = item_ids(it);
    if it is Later {
        let x = wi[0];
        assert(b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending);
        if ids.contains(x) {
            assert(b2.objects[x].state == b.objects[x].project(n).state);
        } else {
            assert(b2.objects[x] == b.objects[x]);
        }
    }
}

/// An item the step started has the shape: its first id is settled now.
#[verifier::rlimit(100)]
pub proof fn lemma_item_wf_added(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int, jj: int)
    requires
        drain_inv(cfg, b, s),
        0 <= i < s.internals.len(),
        0 <= jj < on_v(abstract_of(cfg), item_ids(s.internals[i]), translate(b), s.now).work.len(),
    ensures
        item_wf(next_state(cfg, b, s, i), added_items(cfg, b, s, i)[jj]),
{
    let a = abstract_of(cfg);
    let now = s.now;
    let n = now as nat;
    let ids = item_ids(s.internals[i]);
    let o = on_v(a, ids, translate(b), now);
    let b2 = next_state(cfg, b, s, i);
    tr_on(b, ids, now, a);
    lemma_added_item(cfg, b, s, i, jj);
    let w = o.work[jj];
    let it = added_items(cfg, b, s, i)[jj];
    if w is Later {
        lemma_spawned_shape(b, ids, n, w);
        let wi = on_v_ids(w->Later_0);
        assert(item_ids(it) == wi);
        let x = wi[0];
        assert(ids.contains(x));
        assert(b2.objects[x].state == b.objects[x].project(n).state);
        assert(b.objects[x].project(n).state != PromiseState::Pending);
    } else {
        assert(item_ids(it).len() == 1);
    }
}

/// The work after the step keeps its shape.
pub proof fn lemma_run_wf(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int)
    requires
        drain_inv(cfg, b, s),
        0 <= i < s.internals.len(),
    ensures
        work_wf(next_state(cfg, b, s, i), next_cfg(cfg, b, s, i).internals),
{
    let b2 = next_state(cfg, b, s, i);
    let s2 = next_cfg(cfg, b, s, i);
    let rest = s.internals.remove(i);
    let added = added_items(cfg, b, s, i);
    lemma_run_work(cfg, b, s, i);
    assert forall|j: int| 0 <= j < s2.internals.len() implies item_wf(b2, #[trigger] s2.internals[j]) by {
        if j < rest.len() {
            lemma_item_wf_rest(cfg, b, s, i, j);
            assert(s2.internals[j] == rest[j]);
        } else {
            lemma_item_wf_added(cfg, b, s, i, j - rest.len());
            assert(s2.internals[j] == added[j - rest.len()]);
        }
    }
    lemma_work_wf_items(b2, s2.internals);
}

/// The measure falls: a step that settles a promise leaves fewer due; one that
/// settles none leaves the due as they were and one ready item fewer.
pub proof fn lemma_run_measure(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int)
    requires
        drain_inv(cfg, b, s),
        0 <= i < s.internals.len(),
        ready_item(s.internals[i], s.now),
    ensures
        ({
            let now = s.now;
            let ids = item_ids(s.internals[i]);
            let b2 = next_state(cfg, b, s, i);
            let s2 = next_cfg(cfg, b, s, i);
            &&& (exists|x: Seq<char>| ids.contains(x) && pending_due(b, x, now)) ==> due_set(b2, now).len() < due_set(b, now).len()
            &&& !(exists|x: Seq<char>| ids.contains(x) && pending_due(b, x, now)) ==> due_set(b2, now) == due_set(b, now) && count_ready(s2.internals, now) < count_ready(s.internals, now)
        }),
{
    broadcast use vstd::set::group_set_lemmas;
    let a = abstract_of(cfg);
    let now = s.now;
    let n = now as nat;
    let ids = item_ids(s.internals[i]);
    let o = on_v(a, ids, translate(b), now);
    let b2 = next_state(cfg, b, s, i);
    let s2 = next_cfg(cfg, b, s, i);
    tr_on(b, ids, now, a);
    lemma_run_work(cfg, b, s, i);
    let rest = s.internals.remove(i);
    let added = added_items(cfg, b, s, i);
    // what is due after is what was due before, outside the ids
    assert forall|id: Seq<char>| due_set(b2, now).contains(id) implies due_set(b, now).contains(id) && !ids.contains(id) by {
        assert(pending_due(b2, id, now));
        if ids.contains(id) {
            assert(b2.objects[id].state == PromiseState::Pending);
            assert(b2.objects[id].timeout_at > now);
        } else {
            assert(b2.objects[id] == b.objects[id]);
        }
    }
    if exists|x: Seq<char>| ids.contains(x) && pending_due(b, x, now) {
        let x = choose|x: Seq<char>| ids.contains(x) && pending_due(b, x, now);
        assert(due_set(b, now).contains(x));
        assert(due_set(b2, now).subset_of(due_set(b, now).remove(x)));
        vstd::set_lib::lemma_len_subset(due_set(b2, now), due_set(b, now).remove(x));
        vstd::set::lemma_set_remove_len(due_set(b, now), x);
    } else {
        assert forall|id: Seq<char>| due_set(b, now).contains(id) implies due_set(b2, now).contains(id) by {
            assert(pending_due(b, id, now));
            assert(!ids.contains(id));
            assert(b2.objects[id] == b.objects[id]);
        }
        assert(due_set(b2, now) =~= due_set(b, now));
        // no later was started, and timers are ahead: nothing added is ready
        assert forall|j: int| 0 <= j < added.len() implies !ready_item(#[trigger] added[j], now) by {
            lemma_added_item(cfg, b, s, i, j);
            let w = o.work[j];
            if w is Later {
                assert(spawned(b, ids, n, w));
                let x = choose|x: Seq<char>| ids.contains(x) && #[trigger] b.objects.contains_key(x) && b.objects[x].state == PromiseState::Pending && b.objects[x].timeout_at <= n && (
                    w == Sched::Later(InternalV::On(seq![x])) || exists|y: Seq<char>| #[trigger] b.objects[x].callbacks.contains(y) && w == later2_v(x, y));
                assert(pending_due(b, x, now));
                assert(false);
            }
        }
        lemma_count_ready_none(added, now);
        lemma_count_ready_add(rest, added, now);
        lemma_count_ready_remove(s.internals, now, i);
    }
}


// ------------------------------------------------- the relation after a step

/// Work the step started covers what it names.
pub proof fn lemma_added_covers(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int)
    requires
        drain_inv(cfg, b, s),
        0 <= i < s.internals.len(),
    ensures
        ({
            let now = s.now;
            let ids = item_ids(s.internals[i]);
            let o = on_v(abstract_of(cfg), ids, translate(b), now);
            let s2 = next_cfg(cfg, b, s, i);
            &&& forall|x: Seq<char>, w: Seq<char>| o.work.contains(later2_v(x, w)) ==> covered2(s2.internals, now, x, w)
            &&& forall|x: Seq<char>| o.work.contains(Sched::Later(InternalV::On(seq![x]))) ==> covered(s2.internals, now, x)
            &&& forall|id: Seq<char>, r: u64| o.work.contains(at_v(r, id)) ==> mdeadline_at_timer(s2.internals, id, r as nat)
        }),
{
    let now = s.now;
    let ids = item_ids(s.internals[i]);
    let o = on_v(abstract_of(cfg), ids, translate(b), now);
    let s2 = next_cfg(cfg, b, s, i);
    let rest = s.internals.remove(i);
    let added = added_items(cfg, b, s, i);
    lemma_run_work(cfg, b, s, i);
    assert forall|x: Seq<char>, w: Seq<char>| o.work.contains(later2_v(x, w)) implies covered2(s2.internals, now, x, w) by {
        let j = choose|j: int| 0 <= j < o.work.len() && o.work[j] == later2_v(x, w);
        lemma_added_item(cfg, b, s, i, j);
        let it = added[j];
        assert(s2.internals[rest.len() + j] == it);
        assert(item_ids(it) == seq![x, w]);
        assert(seq![x, w].contains(x) && seq![x, w].contains(w)) by {
            assert(seq![x, w][0] == x && seq![x, w][1] == w);
        }
        assert(ready_item(it, now));
    }
    assert forall|x: Seq<char>| o.work.contains(Sched::Later(InternalV::On(seq![x]))) implies covered(s2.internals, now, x) by {
        let j = choose|j: int| 0 <= j < o.work.len() && o.work[j] == Sched::Later(InternalV::On(seq![x]));
        lemma_added_item(cfg, b, s, i, j);
        let it = added[j];
        assert(s2.internals[rest.len() + j] == it);
        assert(item_ids(it) == seq![x]);
        assert(seq![x].contains(x)) by {
            assert(seq![x][0] == x);
        }
        assert(ready_item(it, now));
    }
    assert forall|id: Seq<char>, r: u64| o.work.contains(at_v(r, id)) implies mdeadline_at_timer(s2.internals, id, r as nat) by {
        let j = choose|j: int| 0 <= j < o.work.len() && o.work[j] == at_v(r, id);
        lemma_added_item(cfg, b, s, i, j);
        let it = added[j];
        assert(s2.internals[rest.len() + j] == it);
        assert(it == Sched::Timer(r, lift_internal(InternalV::On(seq![id]))));
        assert((r as nat) as u64 == r);
    }
}

/// The item is the timer on `id` at `t`.
pub open spec fn timer_at(it: Sched<Internal>, id: Seq<char>, t: nat) -> bool {
    it == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id])))
}

/// Coverage by an item other than the one run carries over.
pub proof fn lemma_cover_survives(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int)
    requires
        drain_inv(cfg, b, s),
        0 <= i < s.internals.len(),
    ensures
        ({
            let now = s.now;
            let s2 = next_cfg(cfg, b, s, i);
            &&& forall|k: int, id: Seq<char>| 0 <= k < s.internals.len() && k != i && ready_item(s.internals[k], now) && #[trigger] item_ids(s.internals[k]).contains(id) ==> covered(s2.internals, now, id)
            &&& forall|k: int, x: Seq<char>, w: Seq<char>| 0 <= k < s.internals.len() && k != i && ready_item(s.internals[k], now) && #[trigger] item_ids(s.internals[k]).contains(x) && #[trigger] item_ids(s.internals[k]).contains(w)
                ==> covered2(s2.internals, now, x, w)
            &&& forall|k: int, id: Seq<char>, t: nat| 0 <= k < s.internals.len() && k != i && #[trigger] timer_at(s.internals[k], id, t) ==> mdeadline_at_timer(s2.internals, id, t)
        }),
{
    let now = s.now;
    let s2 = next_cfg(cfg, b, s, i);
    let rest = s.internals.remove(i);
    lemma_run_work(cfg, b, s, i);
    assert forall|k: int| 0 <= k < s.internals.len() && k != i implies kept(s2.internals, #[trigger] s.internals[k]) by {
        assert(kept(rest, s.internals[k]));
        let j = choose|j: int| 0 <= j < rest.len() && #[trigger] rest[j] == s.internals[k];
        assert(s2.internals[j] == rest[j]);
    }
}

/// The relation after the step.
#[verifier::rlimit(200)]
pub proof fn lemma_run_inv(cfg: Concrete, b: AState, s: Cfg<Resonate>, i: int)
    requires
        drain_inv(cfg, b, s),
        0 <= i < s.internals.len(),
        ready_item(s.internals[i], s.now),
        resume_ok(phase_deadlines(b, item_ids(s.internals[i]), s.now as nat), item_ids(s.internals[i]), s.now as nat),
    ensures
        drain_inv(cfg, next_state(cfg, b, s, i), next_cfg(cfg, b, s, i)),
{
    let a = abstract_of(cfg);
    let now = s.now;
    let n = now as nat;
    let ids = item_ids(s.internals[i]);
    let o = on_v(a, ids, translate(b), now);
    let b2 = next_state(cfg, b, s, i);
    let s2 = next_cfg(cfg, b, s, i);
    tr_on(b, ids, now, a);
    lemma_run_state(cfg, b, s, i);
    lemma_run_wf(cfg, b, s, i);
    lemma_added_covers(cfg, b, s, i);
    lemma_cover_survives(cfg, b, s, i);
    assert(s2.now == now);
    // what is due, covered
    assert forall|id: Seq<char>| pending_due(b2, id, now) implies covered(s2.internals, now, id) by {
        if ids.contains(id) {
            assert(b2.objects[id].timeout_at > now);
        } else {
            assert(b2.objects[id] == b.objects[id]);
            assert(pending_due(b, id, now));
            let k = choose|k: int| 0 <= k < s.internals.len() && ready_item(#[trigger] s.internals[k], now) && item_ids(s.internals[k]).contains(id);
            assert(k != i);
        }
    }
    assert forall|id: Seq<char>| #[trigger] b2.objects.contains_key(id) && lease_due(b2.objects[id], n) implies covered(s2.internals, now, id) by {
        if ids.contains(id) {
            assert(!lease_due(b2.objects[id], n));
        } else {
            assert(b2.objects[id] == b.objects[id]);
            let k = choose|k: int| 0 <= k < s.internals.len() && ready_item(#[trigger] s.internals[k], now) && item_ids(s.internals[k]).contains(id);
            assert(k != i);
        }
    }
    assert forall|id: Seq<char>| #[trigger] b2.objects.contains_key(id) && retry_due(b2.objects[id], n) implies covered(s2.internals, now, id) by {
        if ids.contains(id) {
            assert(!retry_due(b2.objects[id], n));
        } else {
            assert(b2.objects[id] == b.objects[id]);
            let k = choose|k: int| 0 <= k < s.internals.len() && ready_item(#[trigger] s.internals[k], now) && item_ids(s.internals[k]).contains(id);
            assert(k != i);
        }
    }
    assert forall|x: Seq<char>, w: Seq<char>| #[trigger] b2.objects.contains_key(x) && b2.objects[x].state != PromiseState::Pending && #[trigger] b2.objects[x].callbacks.contains(w)
        implies covered2(s2.internals, now, x, w) by {
        if ids.contains(x) {
            assert(!ids.contains(w));
            assert(b.objects[x].callbacks.contains(w));
            if b.objects[x].state != PromiseState::Pending {
                let k = choose|k: int| 0 <= k < s.internals.len() && ready_item(#[trigger] s.internals[k], now) && item_ids(s.internals[k]).contains(x) && item_ids(s.internals[k]).contains(w);
                assert(k != i);
            } else {
                assert(b2.objects[x].state == b.objects[x].project(n).state);
                assert(b.objects[x].timeout_at <= now);
                assert(o.work.contains(later2_v(x, w)));
            }
        } else {
            assert(b2.objects[x] == b.objects[x]);
            let k = choose|k: int| 0 <= k < s.internals.len() && ready_item(#[trigger] s.internals[k], now) && item_ids(s.internals[k]).contains(x) && item_ids(s.internals[k]).contains(w);
            assert(k != i);
        }
    }
    assert forall|x: Seq<char>| #[trigger] b2.objects.contains_key(x) && b2.objects[x].state != PromiseState::Pending && b2.objects[x].listeners.len() > 0 implies covered(s2.internals, now, x) by {
        if ids.contains(x) {
            assert(b2.objects[x].listeners.len() == 0);
        } else {
            assert(b2.objects[x] == b.objects[x]);
            let k = choose|k: int| 0 <= k < s.internals.len() && ready_item(#[trigger] s.internals[k], now) && item_ids(s.internals[k]).contains(x);
            assert(k != i);
        }
    }
    // the deadlines ahead, with timers
    assert forall|id: Seq<char>, t: nat| #[trigger] b2.objects.contains_key(id) && #[trigger] mdeadline_at(b2.objects[id], t) && t > now implies mdeadline_at_timer(s2.internals, id, t) by {
        let q = b2.objects[id];
        let p = b.objects[id];
        if ids.contains(id) {
            if q.state == PromiseState::Pending && q.timeout_at as nat == t {
                assert(mdeadline_at(p, t));
                let k = choose|k: int| 0 <= k < s.internals.len() && #[trigger] s.internals[k] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id])));
                assert(k != i);
                assert(timer_at(s.internals[k], id, t));
            } else if echod_kernel::steps::lease_deadline(q) == Some(t) {
                let t2 = q.task.unwrap();
                assert(p.task.unwrap().lease_timeout_at == t2.lease_timeout_at);
                assert(mdeadline_at(p, t));
                let k = choose|k: int| 0 <= k < s.internals.len() && #[trigger] s.internals[k] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id])));
                assert(k != i);
                assert(timer_at(s.internals[k], id, t));
            } else {
                let t2 = q.task.unwrap();
                assert(t2.retry_timeout_at == Some(t as u64));
                if o.work.contains(at_v(t2.retry_timeout_at.unwrap(), id)) {
                } else {
                    assert(mdeadline_at(p, t));
                    let k = choose|k: int| 0 <= k < s.internals.len() && #[trigger] s.internals[k] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id])));
                    assert(k != i);
                    assert(timer_at(s.internals[k], id, t));
                }
            }
        } else {
            assert(q == p);
            let k = choose|k: int| 0 <= k < s.internals.len() && #[trigger] s.internals[k] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id])));
            assert(k != i);
            assert(timer_at(s.internals[k], id, t));
        }
    }
}

} // verus!
