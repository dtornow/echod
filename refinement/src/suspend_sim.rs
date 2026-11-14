//! `task.suspend`, simulated.
//!
//! The kernel reads the task, checks and reads the awaited promises one
//! after another, then registers the task on each; the Abstract checks and
//! registers against the pre-state, emitting each read's effects twice (once
//! in the check, once in the registration). The awaited promises are
//! distinct and none is the task's own, so every kernel read is of a row no
//! earlier step touched, and the second round of pre-state read effects
//! rewrites what the rows already hold.

use vstd::prelude::*;

use echod_abstract::state as abs_state;
use echod_abstract::state::{AEffect, AObject, AState, spec_apply_all, spec_apply_effect, spec_find_object};
use echod_abstract::task_spec as tspec;
use echod_abstract::types as abs;
use echod_kernel::external as kext;
use echod_kernel::store::AState as KState;
use echod_kernel::types as kernel;
use echod_kernel::types::{APromise, ATask};

use crate::bridge::*;
use crate::heartbeat_sim::{lemma_rewrite_promise, lemma_rewrite_task};
use crate::promise_sim::{lemma_add_callback, lemma_find_via_relation, promise_register_callback_req};
use crate::read_sim::*;
use crate::relation::*;
use crate::task_sim::lemma_after_task_read;
use crate::*;

verus! {

pub type KCb = kernel::APromiseRegisterCallbackReq;
pub type ACb = abs::APromiseRegisterCallbackReq;

pub open spec fn cb_reqs(s: Seq<KCb>) -> Seq<ACb>
    decreases s.len(),
{
    if s.len() == 0 { Seq::empty() } else { cb_reqs(s.drop_last()).push(promise_register_callback_req(s.last())) }
}

pub open spec fn task_suspend_req(r: kernel::ATaskSuspendReq) -> abs::ATaskSuspendReq {
    abs::ATaskSuspendReq { id: ident(r.id), version: r.version, actions: cb_reqs(r.actions) }
}

pub open spec fn canonical_actions(s: Seq<KCb>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> canonical(#[trigger] s[i].awaited)
}

pub proof fn lemma_cb_reqs_index(s: Seq<KCb>)
    ensures
        cb_reqs(s).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] cb_reqs(s)[i] == promise_register_callback_req(s[i]),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_cb_reqs_index(s.drop_last());
    }
}

// ---------------------------------------------------------------------------
// The doors
// ---------------------------------------------------------------------------

pub proof fn lemma_suspend_doors(acts: Seq<KCb>, id: Chars)
    requires canonical_actions(acts), canonical(id),
    ensures kext::suspend_doors(acts, id) == !tspec::spec_task_invalid_suspend_actions(cb_reqs(acts), ident(id)),
{
    lemma_cb_reqs_index(acts);
    let xs = cb_reqs(acts);
    let aid = ident(id);
    assert forall|j: int| 0 <= j < acts.len() implies
        ((#[trigger] acts[j].awaited != id && kernel::same_origin_spec(acts[j].awaited, id))
            == (xs[j].awaited != aid && xs[j].awaited.origin == aid.origin)) by {
        lemma_same_origin(acts[j].awaited, id);
        if ident(acts[j].awaited) == aid {
            lemma_ident_injective(acts[j].awaited, id);
        }
    }
    if kext::awaited_distinct(acts) {
        assert forall|j: int, i: int| 0 <= j < i < xs.len() implies xs[j].awaited != xs[i].awaited by {
            if xs[j].awaited == xs[i].awaited {
                lemma_ident_injective(acts[j].awaited, acts[i].awaited);
            }
        }
    } else {
        let (i, j) = choose|i: int, j: int| 0 <= i < acts.len() && 0 <= j < acts.len()
            && #[trigger] acts[i].awaited == #[trigger] acts[j].awaited && i != j;
        if i < j {
            assert(xs[i].awaited == xs[j].awaited);
        } else {
            assert(xs[j].awaited == xs[i].awaited);
        }
    }
}

// ---------------------------------------------------------------------------
// The kernel's folds, row by row
// ---------------------------------------------------------------------------

/// `first_failing` names the first failing action, if any.
pub proof fn lemma_first_failing(b: KState, acts: Seq<KCb>, m: int)
    requires 0 <= m <= acts.len(),
    ensures match kext::first_failing(b, acts, m) {
        None => forall|i: int| 0 <= i < m ==> !kext::awaited_fails(b, #[trigger] acts[i]),
        Some(j) => 0 <= j < m && kext::awaited_fails(b, acts[j])
            && forall|i: int| 0 <= i < j ==> !kext::awaited_fails(b, #[trigger] acts[i]),
    },
    decreases m,
{
    if m > 0 {
        lemma_first_failing(b, acts, m - 1);
    }
}

/// Reading the first `m` awaited promises leaves every other row alone.
pub proof fn lemma_awaited_read_untouched(b: KState, acts: Seq<KCb>, m: int, now: u64, w: Chars)
    requires 0 <= m <= acts.len(), !kext::awaited_touched(acts, m, w),
    ensures ({
        let c = kext::spec_awaited_read(b, acts, m, now as nat);
        &&& c.objects.contains_key(w) == b.objects.contains_key(w)
        &&& b.objects.contains_key(w) ==> c.objects[w] == b.objects[w]
        &&& c.schedules == b.schedules
    }),
    decreases m,
{
    if m > 0 {
        assert(!kext::awaited_touched(acts, m - 1, w));
        lemma_awaited_read_untouched(b, acts, m - 1, now, w);
        assert(acts[m - 1].awaited != w);
    }
}

/// Reading the first `m` awaited promises projects each one once.
pub proof fn lemma_awaited_read_at(b: KState, acts: Seq<KCb>, m: int, now: u64, j: int)
    requires
        0 <= j < m <= acts.len(),
        kext::awaited_distinct(acts),
        b.objects.contains_key(acts[j].awaited),
    ensures ({
        let c = kext::spec_awaited_read(b, acts, m, now as nat);
        &&& c.objects.contains_key(acts[j].awaited)
        &&& c.objects[acts[j].awaited] == b.objects[acts[j].awaited].project(now as nat)
    }),
    decreases m,
{
    let w = acts[j].awaited;
    if m - 1 == j {
        assert(!kext::awaited_touched(acts, j, w));
        lemma_awaited_read_untouched(b, acts, j, now, w);
    } else {
        lemma_awaited_read_at(b, acts, m - 1, now, j);
        assert(acts[m - 1].awaited != w);
    }
}

/// Registering on the first `m` awaited promises leaves every other row alone.
pub proof fn lemma_awaited_register_untouched(c: KState, acts: Seq<KCb>, m: int, id: Chars, w: Chars)
    requires 0 <= m <= acts.len(), !kext::awaited_touched(acts, m, w),
    ensures ({
        let d = kext::spec_awaited_register(c, acts, m, id);
        &&& d.objects.contains_key(w) == c.objects.contains_key(w)
        &&& c.objects.contains_key(w) ==> d.objects[w] == c.objects[w]
        &&& d.schedules == c.schedules
    }),
    decreases m,
{
    if m > 0 {
        assert(!kext::awaited_touched(acts, m - 1, w));
        lemma_awaited_register_untouched(c, acts, m - 1, id, w);
        assert(acts[m - 1].awaited != w);
    }
}

// ---------------------------------------------------------------------------
// One read, against a row no earlier step touched
// ---------------------------------------------------------------------------

/// The kernel reads `w` in `c`, where `c` still holds `k`'s row; the
/// Abstract's pre-state read effects commit on `c`'s partner.
pub proof fn lemma_untouched_read(k: KState, a0: AState, c: KState, a: AState, w: Chars, now: u64)
    requires
        doc_related(k, a0),
        doc_related(c, a),
        canonical(w),
        c.objects.contains_key(w) == k.objects.contains_key(w),
        k.objects.contains_key(w) ==> c.objects[w] == k.objects[w],
    ensures
        doc_related(kext::spec_read(c, w, now as nat), spec_apply_all(a, abs_state::spec_read_effects(a0, ident(w), now, true))),
        abs_state::spec_read_object(a0, ident(w), now)
            == if k.objects.contains_key(w) { Some(object(k.objects[w].project(now as nat))) } else { None },
{
    lemma_find_via_relation(k, a0, c, a, w);
    if k.objects.contains_key(w) {
        lemma_read_sim(c, a, w, now);
        lemma_read_sim(k, a0, w, now);
    } else {
        lemma_read_absent(c, a, w, now);
        lemma_read_absent(k, a0, w, now);
    }
}

// ---------------------------------------------------------------------------
// The check
// ---------------------------------------------------------------------------

/// Some awaited promise among the first `m` is settled at `now`.
pub open spec fn settled_before(b: KState, acts: Seq<KCb>, m: int, now: u64) -> bool {
    exists|j: int| 0 <= j < m && b.objects[#[trigger] acts[j].awaited].project(now as nat).state != kernel::PromiseState::Pending
}

/// The check over the first `m` actions, none of which fails: the Abstract
/// check is valid, its settledness is the kernel's, and the kernel's reads
/// relate to its effects.
pub proof fn lemma_suspend_check_prefix(k: KState, a0: AState, id: Chars, acts: Seq<KCb>, m: int, now: u64)
    requires
        doc_related(k, a0),
        canonical(id),
        k.has_task(id),
        canonical_actions(acts),
        kext::suspend_doors(acts, id),
        0 <= m <= acts.len(),
        kext::first_failing(kext::spec_read_task(k, id, now as nat), acts, m) is None,
    ensures ({
        let b = kext::spec_read_task(k, id, now as nat);
        let ab = after_read(a0, ident(id), now);
        let chk = tspec::spec_task_suspend_check(a0, cb_reqs(acts.take(m)), now, true);
        &&& chk.valid
        &&& chk.settled == settled_before(b, acts, m, now)
        &&& doc_related(kext::spec_awaited_read(b, acts, m, now as nat), spec_apply_all(ab, chk.effects))
    }),
    decreases m,
{
    let b = kext::spec_read_task(k, id, now as nat);
    let ab = after_read(a0, ident(id), now);
    lemma_after_task_read(k, a0, id, now);
    lemma_first_failing(b, acts, m);
    if m == 0 {
        assert(acts.take(0) =~= Seq::<KCb>::empty());
        assert(cb_reqs(Seq::<KCb>::empty()) =~= Seq::<ACb>::empty());
        lemma_apply_all_empty(ab);
        assert(!settled_before(b, acts, 0, now));
    } else {
        assert(kext::first_failing(b, acts, m - 1) is None) by {
            lemma_first_failing(b, acts, m - 1);
            match kext::first_failing(b, acts, m - 1) {
                Some(j) => { assert(kext::awaited_fails(b, acts[j])); assert(false); }
                None => {}
            }
        }
        lemma_suspend_check_prefix(k, a0, id, acts, m - 1, now);
        let c = kext::spec_awaited_read(b, acts, m - 1, now as nat);
        let prefix = cb_reqs(acts.take(m - 1));
        let prior = tspec::spec_task_suspend_check(a0, prefix, now, true);
        let a_c = spec_apply_all(ab, prior.effects);
        let act = acts[m - 1];
        let w = act.awaited;
        let aw = ident(w);
        assert(!kext::awaited_fails(b, act));
        assert(b.objects.contains_key(w) && b.objects[w].otype().awaitable());
        assert(w != id);
        assert(k.objects.contains_key(w) && b.objects[w] == k.objects[w]);
        assert(!kext::awaited_touched(acts, m - 1, w));
        lemma_awaited_read_untouched(b, acts, m - 1, now, w);
        lemma_untouched_read(k, a0, c, a_c, w, now);
        let q = k.objects[w].project(now as nat);
        lemma_otype(q.tags);
        let reads = abs_state::spec_read_effects(a0, aw, now, true);
        lemma_apply_all_app(ab, prior.effects, reads);
        // The Abstract check on the whole prefix.
        assert(acts.take(m).drop_last() =~= acts.take(m - 1));
        assert(acts.take(m).last() == act);
        let whole = cb_reqs(acts.take(m));
        assert(whole == prefix.push(promise_register_callback_req(act)));
        assert(whole.drop_last() =~= prefix);
        assert(whole.last() == promise_register_callback_req(act));
        let chk = tspec::spec_task_suspend_check(a0, whole, now, true);
        assert(chk.valid);
        assert(chk.effects == prior.effects + reads);
        assert(chk.settled == (prior.settled || promise(q).state != abs::PromiseState::Pending));
        assert(chk.settled == settled_before(b, acts, m, now)) by {
            if q.state != kernel::PromiseState::Pending {
                assert(b.objects[acts[m - 1].awaited].project(now as nat).state != kernel::PromiseState::Pending);
            } else if settled_before(b, acts, m, now) {
                let j = choose|j: int| 0 <= j < m && b.objects[#[trigger] acts[j].awaited].project(now as nat).state != kernel::PromiseState::Pending;
                assert(j < m - 1);
                assert(settled_before(b, acts, m - 1, now));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The registration
// ---------------------------------------------------------------------------

/// Registering on the first `m` awaited promises, all read: the kernel's
/// fold and the Abstract's pre-state effects agree.
pub proof fn lemma_suspend_register_prefix(k: KState, a0: AState, c: KState, a_c: AState, id: Chars, acts: Seq<KCb>, m: int, now: u64)
    requires
        doc_related(k, a0),
        doc_related(c, a_c),
        canonical(id),
        canonical_actions(acts),
        kext::suspend_doors(acts, id),
        0 <= m <= acts.len(),
        forall|j: int| 0 <= j < acts.len() ==> k.objects.contains_key(#[trigger] acts[j].awaited),
        forall|j: int| 0 <= j < acts.len() ==> c.objects.contains_key(#[trigger] acts[j].awaited)
            && c.objects[acts[j].awaited] == k.objects[acts[j].awaited].project(now as nat),
    ensures ({
        let reg = tspec::spec_task_suspend_register(a0, cb_reqs(acts.take(m)), ident(id), now, true);
        doc_related(kext::spec_awaited_register(c, acts, m, id), spec_apply_all(a_c, reg))
    }),
    decreases m,
{
    if m == 0 {
        assert(acts.take(0) =~= Seq::<KCb>::empty());
        assert(cb_reqs(Seq::<KCb>::empty()) =~= Seq::<ACb>::empty());
        lemma_apply_all_empty(a_c);
    } else {
        lemma_suspend_register_prefix(k, a0, c, a_c, id, acts, m - 1, now);
        let d = kext::spec_awaited_register(c, acts, m - 1, id);
        let prefix = cb_reqs(acts.take(m - 1));
        let prior = tspec::spec_task_suspend_register(a0, prefix, ident(id), now, true);
        let a_d = spec_apply_all(a_c, prior);
        let act = acts[m - 1];
        let w = act.awaited;
        let aw = ident(w);
        assert(!kext::awaited_touched(acts, m - 1, w));
        lemma_awaited_register_untouched(c, acts, m - 1, id, w);
        let q = k.objects[w].project(now as nat);
        assert(d.objects.contains_key(w) && d.objects[w] == q);
        assert(canonical_promise(q));
        // The pre-state read, again: a rewrite of what `d` holds at `w`.
        lemma_read_sim(k, a0, w, now);
        let reads = abs_state::spec_read_effects(a0, aw, now, true);
        let p0 = k.objects[w];
        let promise_part: Seq<AEffect> = if q.state != p0.state { seq![AEffect::SetPromise(aw, promise(q))] } else { Seq::empty() };
        let task_part: Seq<AEffect> = match (p0.task, q.task) {
            (Some(x), Some(y)) if x.state != y.state => seq![AEffect::SetTask(aw, task(y))],
            _ => Seq::empty(),
        };
        assert(reads == promise_part + task_part);
        lemma_apply_all_app(a_d, promise_part, task_part);
        let a_mid = spec_apply_all(a_d, promise_part);
        if q.state != p0.state {
            lemma_apply_all_one(a_d, AEffect::SetPromise(aw, promise(q)));
            lemma_rewrite_promise(d, a_d, w);
        }
        assert(doc_related(d, a_mid));
        match (p0.task, q.task) {
            (Some(x), Some(y)) if x.state != y.state => {
                lemma_apply_all_one(a_mid, AEffect::SetTask(aw, task(y)));
                lemma_rewrite_task(d, a_mid, w);
            }
            _ => {}
        }
        let a_read = spec_apply_all(a_d, reads);
        assert(doc_related(d, a_read));
        // The registration itself.
        let px = q.add_callback(id);
        lemma_add_callback(q, id);
        assert(canonical_promise(px));
        assert(task_opt(px.task) == object(q).task);
        lemma_set_promise(d.objects, a_read.objects, w, px);
        let write = seq![AEffect::SetPromise(aw, abs_state::spec_add_callback(promise(q), ident(id)))];
        lemma_apply_all_one(a_read, AEffect::SetPromise(aw, abs_state::spec_add_callback(promise(q), ident(id))));
        let one = tspec::spec_task_suspend_register_one(a0, promise_register_callback_req(act), ident(id), now, true);
        assert(one == reads + write);
        lemma_apply_all_app(a_d, reads, write);
        lemma_apply_all_app(a_c, prior, one);
        // The Abstract registration on the whole prefix.
        assert(acts.take(m).drop_last() =~= acts.take(m - 1));
        assert(acts.take(m).last() == act);
        let whole = cb_reqs(acts.take(m));
        assert(whole == prefix.push(promise_register_callback_req(act)));
        assert(whole.drop_last() =~= prefix);
        assert(whole.last() == promise_register_callback_req(act));
        assert(tspec::spec_task_suspend_register(a0, whole, ident(id), now, true) == prior + one);
        let out = kext::spec_awaited_register(c, acts, m, id);
        assert(out.objects == d.objects.insert(w, px));
        assert(out.schedules == d.schedules);
    }
}

// ---------------------------------------------------------------------------
// The handler, by outcome
// ---------------------------------------------------------------------------

/// The guard the three outcomes share: the task read, acquired at the
/// version named, its promise pending.
pub open spec fn suspend_open(k: KState, req: kernel::ATaskSuspendReq, now: u64) -> bool {
    &&& kext::suspend_doors(req.actions, req.id)
    &&& k.has_task(req.id)
    &&& {
        let q = k.objects[req.id].project(now as nat);
        let t = q.task.unwrap();
        t.state == kernel::TaskState::Acquired && q.state == kernel::PromiseState::Pending && t.version == req.version
    }
}

/// `first_failing` over all the actions names `j`: it is `None` over the
/// first `j`.
pub proof fn lemma_first_failing_before(b: KState, acts: Seq<KCb>, j: int)
    requires 0 <= j <= acts.len(), kext::first_failing(b, acts, acts.len() as int) == Some(j),
    ensures kext::first_failing(b, acts, j) is None,
{
    lemma_first_failing(b, acts, acts.len() as int);
    lemma_first_failing(b, acts, j);
    match kext::first_failing(b, acts, j) {
        Some(i) => { assert(kext::awaited_fails(b, acts[i])); assert(false); }
        None => {}
    }
}

/// Some awaited promise fails the check: 422, having read up to it.
pub proof fn lemma_suspend_422(k: KState, a: AState, req: kernel::ATaskSuspendReq, now: u64, j: int)
    requires
        doc_related(k, a),
        canonical(req.id),
        canonical_actions(req.actions),
        suspend_open(k, req, now),
        kext::first_failing(kext::spec_read_task(k, req.id, now as nat), req.actions, req.actions.len() as int) == Some(j),
    ensures ({
        let id = req.id;
        let acts = req.actions;
        let b = kext::spec_read_task(k, id, now as nat);
        let m = if b.objects.contains_key(acts[j].awaited) { j + 1 } else { j };
        let reads = abs_state::spec_read_effects(a, ident(id), now, true);
        let chk = tspec::spec_task_suspend_check(a, cb_reqs(acts), now, true);
        &&& !chk.valid
        &&& doc_related(kext::spec_awaited_read(b, acts, m, now as nat), spec_apply_all(a, reads + chk.effects))
    }),
{
    let id = req.id;
    let aid = ident(id);
    let acts = req.actions;
    let n = acts.len() as int;
    lemma_after_task_read(k, a, id, now);
    let b = kext::spec_read_task(k, id, now as nat);
    let ab = after_read(a, aid, now);
    let reads = abs_state::spec_read_effects(a, aid, now, true);
    lemma_first_failing(b, acts, n);
    lemma_first_failing_before(b, acts, j);
    lemma_suspend_check_prefix(k, a, id, acts, j, now);
    let c_j = kext::spec_awaited_read(b, acts, j, now as nat);
    let prefix = cb_reqs(acts.take(j));
    let prior = tspec::spec_task_suspend_check(a, prefix, now, true);
    let a_j = spec_apply_all(ab, prior.effects);
    let act = acts[j];
    let w = act.awaited;
    let aw = ident(w);
    assert(w != id);
    assert(b.objects.contains_key(w) == k.objects.contains_key(w));
    assert(k.objects.contains_key(w) ==> b.objects[w] == k.objects[w]);
    assert(!kext::awaited_touched(acts, j, w));
    lemma_awaited_read_untouched(b, acts, j, now, w);
    lemma_untouched_read(k, a, c_j, a_j, w, now);
    let reads_w = abs_state::spec_read_effects(a, aw, now, true);
    // The check on the first `j + 1`: invalid at `act`.
    assert(acts.take(j + 1).drop_last() =~= acts.take(j));
    assert(acts.take(j + 1).last() == act);
    let upto = cb_reqs(acts.take(j + 1));
    assert(upto == prefix.push(promise_register_callback_req(act)));
    assert(upto.drop_last() =~= prefix);
    assert(upto.last() == promise_register_callback_req(act));
    let chk1 = tspec::spec_task_suspend_check(a, upto, now, true);
    if k.objects.contains_key(w) {
        let qw = k.objects[w].project(now as nat);
        lemma_otype(qw.tags);
        assert(!qw.otype().awaitable());
    }
    assert(!chk1.valid);
    assert(chk1.effects == prior.effects + reads_w);
    lemma_apply_all_app(ab, prior.effects, reads_w);
    // Beyond `j + 1`, the check is unchanged.
    lemma_cb_reqs_index(acts);
    lemma_cb_reqs_index(acts.take(j + 1));
    lemma_cb_reqs_index(acts.subrange(j + 1, n));
    assert(cb_reqs(acts) =~= upto + cb_reqs(acts.subrange(j + 1, n)));
    tspec::lemma_task_suspend_check_invalid_extension(a, upto, cb_reqs(acts.subrange(j + 1, n)), now, true);
    let chk = tspec::spec_task_suspend_check(a, cb_reqs(acts), now, true);
    assert(chk == chk1);
    lemma_apply_all_app(a, reads, chk.effects);
    // The kernel stopped where the check did.
    if k.objects.contains_key(w) {
        assert(kext::spec_awaited_read(b, acts, j + 1, now as nat) == kext::spec_read(c_j, w, now as nat));
    } else {
        assert(reads_w =~= Seq::<AEffect>::empty());
        assert(prior.effects + reads_w =~= prior.effects);
    }
}

/// Every awaited promise passes the check: the reads, related.
pub proof fn lemma_suspend_pass(k: KState, a: AState, req: kernel::ATaskSuspendReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
        canonical_actions(req.actions),
        suspend_open(k, req, now),
        kext::first_failing(kext::spec_read_task(k, req.id, now as nat), req.actions, req.actions.len() as int) is None,
    ensures ({
        let id = req.id;
        let acts = req.actions;
        let n = acts.len() as int;
        let b = kext::spec_read_task(k, id, now as nat);
        let c = kext::spec_awaited_read(b, acts, n, now as nat);
        let reads = abs_state::spec_read_effects(a, ident(id), now, true);
        let chk = tspec::spec_task_suspend_check(a, cb_reqs(acts), now, true);
        &&& chk.valid
        &&& chk.settled == kext::any_settled(b, acts, now as nat)
        &&& doc_related(c, spec_apply_all(a, reads + chk.effects))
        &&& c.objects.contains_key(id) && c.objects[id] == k.objects[id].project(now as nat)
        &&& forall|j: int| 0 <= j < acts.len() ==> k.objects.contains_key(#[trigger] acts[j].awaited)
        &&& forall|j: int| 0 <= j < acts.len() ==> c.objects.contains_key(#[trigger] acts[j].awaited)
            && c.objects[acts[j].awaited] == k.objects[acts[j].awaited].project(now as nat)
    }),
{
    let id = req.id;
    let aid = ident(id);
    let acts = req.actions;
    let n = acts.len() as int;
    lemma_after_task_read(k, a, id, now);
    let b = kext::spec_read_task(k, id, now as nat);
    let ab = after_read(a, aid, now);
    let reads = abs_state::spec_read_effects(a, aid, now, true);
    assert(acts.take(n) =~= acts);
    lemma_first_failing(b, acts, n);
    lemma_suspend_check_prefix(k, a, id, acts, n, now);
    let c = kext::spec_awaited_read(b, acts, n, now as nat);
    let chk = tspec::spec_task_suspend_check(a, cb_reqs(acts), now, true);
    lemma_apply_all_app(a, reads, chk.effects);
    assert(!kext::awaited_touched(acts, n, id));
    lemma_awaited_read_untouched(b, acts, n, now, id);
    assert forall|j: int| 0 <= j < acts.len() implies k.objects.contains_key(#[trigger] acts[j].awaited)
        && c.objects.contains_key(acts[j].awaited)
        && c.objects[acts[j].awaited] == k.objects[acts[j].awaited].project(now as nat) by {
        assert(!kext::awaited_fails(b, acts[j]));
        assert(acts[j].awaited != id);
        lemma_awaited_read_at(b, acts, n, now, j);
    }
}

pub proof fn lemma_task_suspend_sim(k: KState, a: AState, req: kernel::ATaskSuspendReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
        canonical_actions(req.actions),
    ensures ({
        let (k2, res) = kext::spec_task_suspend(k, req, now as nat);
        let r = tspec::spec_task_suspend_action(a, task_suspend_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& task_suspend_res(res) == r.response
    }),
{
    let id = req.id;
    let aid = ident(id);
    let acts = req.actions;
    let n = acts.len() as int;
    lemma_suspend_doors(acts, id);
    if !kext::suspend_doors(acts, id) {
    } else {
        lemma_read_task_sim(k, a, id, now);
        if k.has_task(id) {
            lemma_after_task_read(k, a, id, now);
            let b = kext::spec_read_task(k, id, now as nat);
            let q = k.objects[id].project(now as nat);
            let t = q.task.unwrap();
            let reads = abs_state::spec_read_effects(a, aid, now, true);
            if t.state != kernel::TaskState::Acquired || q.state != kernel::PromiseState::Pending || t.version != req.version {
            } else {
                assert(suspend_open(k, req, now));
                let chk = tspec::spec_task_suspend_check(a, cb_reqs(acts), now, true);
                let checked_effects = reads + chk.effects;
                match kext::first_failing(b, acts, n) {
                    Some(j) => {
                        lemma_suspend_422(k, a, req, now, j);
                    }
                    None => {
                        lemma_suspend_pass(k, a, req, now);
                        let c = kext::spec_awaited_read(b, acts, n, now as nat);
                        let a_c = spec_apply_all(a, checked_effects);
                        assert(id_list(Seq::<Chars>::empty()) =~= Seq::<abs::AIdent>::empty());
                        if kext::any_settled(b, acts, now as nat) {
                            let t2 = t.clear_resumes();
                            assert(canonical_task(t2));
                            assert(task(t2) == abs_state::ATaskObject { resumes: Seq::empty(), ..task(t) });
                            lemma_set_task(c.objects, a_c.objects, id, t2);
                            lemma_apply_all_push(a, checked_effects, AEffect::SetTask(aid, task(t2)));
                        } else {
                            lemma_suspend_register_prefix(k, a, c, a_c, id, acts, n, now);
                            assert(acts.take(n) =~= acts);
                            let d = kext::spec_awaited_register(c, acts, n, id);
                            let reg = tspec::spec_task_suspend_register(a, cb_reqs(acts), aid, now, true);
                            let a_d = spec_apply_all(a_c, reg);
                            lemma_apply_all_app(a, checked_effects, reg);
                            assert(!kext::awaited_touched(acts, n, id));
                            lemma_awaited_register_untouched(c, acts, n, id, id);
                            assert(d.objects[id] == q);
                            let t2 = t.suspend();
                            assert(canonical_task(t2));
                            assert(task(t2) == abs_state::ATaskObject {
                                state: abs::TaskState::Suspended, pid: None, ttl: None, lease_timeout_at: None,
                                retry_timeout_at: None, resumes: Seq::empty(), ..task(t) });
                            lemma_set_task(d.objects, a_d.objects, id, t2);
                            lemma_apply_all_one(a_d, AEffect::SetTask(aid, task(t2)));
                            lemma_apply_all_app(a, checked_effects + reg, seq![AEffect::SetTask(aid, task(t2))]);
                        }
                    }
                }
            }
        }
    }
}

} // verus!
