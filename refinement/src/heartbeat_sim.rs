//! `task.heartbeat`, simulated.
//!
//! The kernel folds over the refs, each read against the state the previous
//! left; the Abstract reads every ref against the pre-state and commits the
//! effects in order. The two agree because a heartbeat changes nothing a
//! later heartbeat reads: the fold keeps every row in one of three shapes
//! (as it was, projected, projected and refreshed), and in each the
//! Abstract's pre-state effects are either the kernel's own write or a
//! rewrite of what the row already holds.

use vstd::prelude::*;

use echod_abstract::state as abs_state;
use echod_abstract::state::{AEffect, AObject, AState, spec_apply_all, spec_apply_effect, spec_find_object};
use echod_abstract::task_spec as tspec;
use echod_abstract::types as abs;
use echod_kernel::external as kext;
use echod_kernel::properties as kprops;
use echod_kernel::store::AState as KState;
use echod_kernel::types as kernel;
use echod_kernel::types::{APromise, ATask};

use crate::bridge::*;
use crate::promise_sim::lemma_find_via_relation;
use crate::read_sim::*;
use crate::relation::*;
use crate::*;

verus! {

pub open spec fn task_ref(r: kernel::ATaskRef) -> abs::ATaskRef {
    abs::ATaskRef { id: ident(r.id), version: r.version }
}

pub open spec fn task_refs(s: Seq<kernel::ATaskRef>) -> Seq<abs::ATaskRef>
    decreases s.len(),
{
    if s.len() == 0 { Seq::empty() } else { task_refs(s.drop_last()).push(task_ref(s.last())) }
}

pub open spec fn task_heartbeat_req(r: kernel::ATaskHeartbeatReq) -> abs::ATaskHeartbeatReq {
    abs::ATaskHeartbeatReq { pid: text(r.pid), tasks: task_refs(r.tasks) }
}

pub open spec fn canonical_refs(s: Seq<kernel::ATaskRef>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> canonical(#[trigger] s[i].id)
}

// ---------------------------------------------------------------------------
// Rewrites: an effect that writes what the row already holds
// ---------------------------------------------------------------------------

pub proof fn lemma_rewrite_promise(k: KState, a: AState, x: Chars)
    requires doc_related(k, a), k.objects.contains_key(x),
    ensures doc_related(k, spec_apply_effect(a, AEffect::SetPromise(ident(x), promise(k.objects[x])))),
{
    lemma_set_promise(k.objects, a.objects, x, k.objects[x]);
    assert(k.objects.insert(x, k.objects[x]) =~= k.objects);
}

pub proof fn lemma_rewrite_task(k: KState, a: AState, x: Chars)
    requires doc_related(k, a), k.objects.contains_key(x), k.objects[x].task is Some,
    ensures doc_related(k, spec_apply_effect(a, AEffect::SetTask(ident(x), task(k.objects[x].task.unwrap())))),
{
    let t = k.objects[x].task.unwrap();
    lemma_set_task(k.objects, a.objects, x, t);
    assert(k.objects[x].with_task(t) == k.objects[x]);
    assert(k.objects.insert(x, k.objects[x]) =~= k.objects);
}

/// A projected row whose promise is still pending stays put under
/// projection, whatever its task.
pub proof fn lemma_project_pending_with_task(q: APromise, t: ATask, now: u64)
    requires q.project(now as nat) == q, q.state == kernel::PromiseState::Pending,
    ensures q.with_task(t).project(now as nat) == q.with_task(t),
{
    assert(q.timeout_at > now);
}

// ---------------------------------------------------------------------------
// The shape the fold keeps
// ---------------------------------------------------------------------------

/// A row the fold has visited: as it was, projected, or projected and refreshed.
pub open spec fn hb_row(p0: APromise, p: APromise, now: u64) -> bool {
    let q = p0.project(now as nat);
    ||| p == p0
    ||| (p0.task is Some && p == q)
    ||| (p0.task is Some && q.state == kernel::PromiseState::Pending
        && p == q.with_task(q.task.unwrap().heartbeat(now as nat)))
}

pub open spec fn hb_shape(k0: KState, k: KState, now: u64) -> bool {
    &&& forall|id: Chars| k.objects.contains_key(id) == #[trigger] k0.objects.contains_key(id)
    &&& k.schedules == k0.schedules
    &&& forall|id: Chars| #[trigger] k0.objects.contains_key(id) ==> hb_row(k0.objects[id], k.objects[id], now)
}

/// One ref, on a state in shape: the kernel's step and the Abstract's
/// pre-state effects agree, and the shape is kept.
pub proof fn lemma_heartbeat_one_sim(k0: KState, a0: AState, k: KState, a: AState, pid: Chars, r: kernel::ATaskRef, now: u64)
    requires
        doc_related(k0, a0),
        doc_related(k, a),
        hb_shape(k0, k, now),
        kprops::kernel_bounds(k0),
        now <= kernel::MAX_TIME,
        canonical(r.id),
    ensures
        hb_shape(k0, kext::spec_heartbeat_one(k, pid, r, now as nat), now),
        doc_related(
            kext::spec_heartbeat_one(k, pid, r, now as nat),
            spec_apply_all(a, tspec::spec_task_heartbeat_one(a0, text(pid), task_ref(r), now, true))),
{
    let x = r.id;
    let ax = ident(x);
    let e = tspec::spec_task_heartbeat_one(a0, text(pid), task_ref(r), now, true);
    let out = kext::spec_heartbeat_one(k, pid, r, now as nat);
    lemma_read_task_sim(k0, a0, x, now);
    if !k0.has_task(x) {
        if k0.objects.contains_key(x) {
            assert(hb_row(k0.objects[x], k.objects[x], now));
            assert(k.objects[x] == k0.objects[x]);
        }
        assert(!k.has_task(x));
        assert(e =~= Seq::<AEffect>::empty());
        lemma_apply_all_empty(a);
    } else {
        let p0 = k0.objects[x];
        let t0 = p0.task.unwrap();
        let q = p0.project(now as nat);
        let t = q.task.unwrap();
        assert(hb_row(p0, k.objects[x], now));
        assert(k.has_task(x));
        assert(kprops::kernel_bounds_at(p0));
        lemma_project_canonical(p0, now);
        let kb = kext::spec_read_task(k, x, now as nat);
        let reads = abs_state::spec_read_effects(a0, ax, now, true);
        let ab = spec_apply_all(a, reads);
        assert(tspec::spec_task_read(a0, ax, now, true).object == Some(object(q)));
        assert(tspec::spec_task_read(a0, ax, now, true).effects == reads);

        // After the kernel's read, related to the reads committed on `a`.
        let p = k.objects[x];
        if p == p0 {
            lemma_find_via_relation(k0, a0, k, a, x);
            assert(abs_state::spec_read_effects(a, ax, now, true) == reads);
            lemma_read_sim(k, a, x, now);
            assert(kb.objects[x] == q);
        } else {
            if p == q {
                echod_kernel::external_proof::lemma_project_idem(p0, now as nat);
            } else {
                echod_kernel::external_proof::lemma_project_idem(p0, now as nat);
                lemma_project_pending_with_task(q, t.heartbeat(now as nat), now);
            }
            assert(p.project(now as nat) == p);
            assert(kb.objects =~= k.objects);
            assert(promise(p) == promise(q));
            let promise_part: Seq<AEffect> = if q.state != p0.state { seq![AEffect::SetPromise(ax, promise(q))] } else { Seq::empty() };
            let task_part: Seq<AEffect> = if t.state != t0.state { seq![AEffect::SetTask(ax, task(t))] } else { Seq::empty() };
            assert(reads == promise_part + task_part);
            lemma_apply_all_app(a, promise_part, task_part);
            let a_mid = spec_apply_all(a, promise_part);
            if q.state != p0.state {
                lemma_apply_all_one(a, AEffect::SetPromise(ax, promise(q)));
                lemma_rewrite_promise(k, a, x);
            }
            assert(doc_related(k, a_mid));
            if t.state != t0.state {
                assert(q.state != kernel::PromiseState::Pending);
                assert(p == q);
                lemma_apply_all_one(a_mid, AEffect::SetTask(ax, task(t)));
                lemma_rewrite_task(k, a_mid, x);
            }
            assert(doc_related(k, ab));
            assert(doc_related(kb, ab));
        }
        let p1 = kb.objects[x];
        let t1 = p1.task.unwrap();
        assert(p1 == q || p1 == q.with_task(t.heartbeat(now as nat)));
        assert(t1.state == t.state && t1.version == t.version && t1.pid == t.pid && t1.ttl == t.ttl && p1.state == q.state);
        assert(t1.resumes == t.resumes);
        let cond = t1.state == kernel::TaskState::Acquired && t1.version == r.version && t1.pid == Some(pid) && p1.state == kernel::PromiseState::Pending;
        let acond = task(t).state == abs::TaskState::Acquired && task(t).version == r.version
            && task(t).pid == Some(text(pid)) && promise(q).state == abs::PromiseState::Pending;
        assert(cond == acond);
        if cond {
            let t2 = t1.heartbeat(now as nat);
            assert(t2 == t.heartbeat(now as nat));
            assert(t.ttl == t0.ttl);
            assert(kprops::opt_or_zero(t.ttl) <= kernel::MAX_TIME);
            let attl: u64 = match task(t).ttl { Some(v) => v, None => 0 };
            assert(attl as nat == kprops::opt_or_zero(t.ttl));
            assert(task(t2) == abs_state::ATaskObject { lease_timeout_at: Some(tspec::spec_task_sat_add(now, attl)), ..task(t) });
            assert(e == reads.push(AEffect::SetTask(ax, task(t2))));
            assert(canonical_task(t2));
            lemma_set_task(kb.objects, ab.objects, x, t2);
            lemma_apply_all_push(a, reads, AEffect::SetTask(ax, task(t2)));
            assert(out.objects == kb.objects.insert(x, p1.with_task(t2)));
            assert(p1.with_task(t2) == q.with_task(t.heartbeat(now as nat)));
        } else {
            assert(e == reads);
            assert(out == kb);
        }
        // The shape: `x` moved into a visited shape, nothing else moved.
        assert forall|id: Chars| out.objects.contains_key(id) == #[trigger] k0.objects.contains_key(id) by {
            assert(k.objects.contains_key(id) == k0.objects.contains_key(id));
        }
        assert forall|id: Chars| #[trigger] k0.objects.contains_key(id) implies hb_row(k0.objects[id], out.objects[id], now) by {
            if id != x {
                assert(out.objects[id] == k.objects[id]);
            }
        }
    }
}

/// The first `j` refs, folded.
pub proof fn lemma_heartbeat_fold_sim(k0: KState, a0: AState, pid: Chars, refs: Seq<kernel::ATaskRef>, j: int, now: u64)
    requires
        doc_related(k0, a0),
        kprops::kernel_bounds(k0),
        now <= kernel::MAX_TIME,
        canonical_refs(refs),
        0 <= j <= refs.len(),
    ensures
        hb_shape(k0, kext::spec_heartbeat_fold(k0, pid, refs, j, now as nat), now),
        doc_related(
            kext::spec_heartbeat_fold(k0, pid, refs, j, now as nat),
            spec_apply_all(a0, tspec::spec_task_heartbeat_all(a0, text(pid), task_refs(refs.take(j)), now, true))),
    decreases j,
{
    if j == 0 {
        assert(refs.take(0) =~= Seq::<kernel::ATaskRef>::empty());
        assert(task_refs(Seq::<kernel::ATaskRef>::empty()) =~= Seq::<abs::ATaskRef>::empty());
        lemma_apply_all_empty(a0);
    } else {
        lemma_heartbeat_fold_sim(k0, a0, pid, refs, j - 1, now);
        let s = kext::spec_heartbeat_fold(k0, pid, refs, j - 1, now as nat);
        let prefix = task_refs(refs.take(j - 1));
        let all_prefix = tspec::spec_task_heartbeat_all(a0, text(pid), prefix, now, true);
        let a_s = spec_apply_all(a0, all_prefix);
        let r = refs[j - 1];
        lemma_heartbeat_one_sim(k0, a0, s, a_s, pid, r, now);
        let one = tspec::spec_task_heartbeat_one(a0, text(pid), task_ref(r), now, true);
        assert(refs.take(j).drop_last() =~= refs.take(j - 1));
        assert(refs.take(j).last() == r);
        let whole = task_refs(refs.take(j));
        assert(whole == prefix.push(task_ref(r)));
        assert(whole.drop_last() =~= prefix);
        assert(whole.last() == task_ref(r));
        assert(tspec::spec_task_heartbeat_all(a0, text(pid), whole, now, true) == all_prefix + one);
        lemma_apply_all_app(a0, all_prefix, one);
    }
}

pub proof fn lemma_task_heartbeat_sim(k: KState, a: AState, req: kernel::ATaskHeartbeatReq, now: u64)
    requires
        doc_related(k, a),
        kprops::kernel_bounds(k),
        now <= kernel::MAX_TIME,
        canonical_refs(req.tasks),
    ensures ({
        let (k2, res) = kext::spec_task_heartbeat(k, req, now as nat);
        let r = tspec::spec_task_heartbeat_action(a, task_heartbeat_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& status_res(res) == r.response
    }),
{
    let n = req.tasks.len() as int;
    lemma_heartbeat_fold_sim(k, a, req.pid, req.tasks, n, now);
    assert(req.tasks.take(n) =~= req.tasks);
}

} // verus!
