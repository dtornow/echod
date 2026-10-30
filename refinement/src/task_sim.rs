//! The Task handlers that touch one object (and the fence, which runs a
//! promise handler on behalf of a task), simulated.
//!
//! The kernel's domain, beyond canonical ids: `now` and every ttl are times
//! (`<= MAX_TIME`, so lease arithmetic does not saturate), and the task's
//! version has headroom (`< MAX_VERSION`): the kernel answers 409 where the
//! Lean text, on unbounded naturals, would acquire. `kernel_bounds` is part
//! of the kernel's own invariant.

use vstd::prelude::*;

use echod_abstract::promise_spec as pspec;
use echod_abstract::state as abs_state;
use echod_abstract::state::{AEffect, AObject, AState, spec_apply_all, spec_apply_effect, spec_find_object};
use echod_abstract::task_spec as tspec;
use echod_abstract::types as abs;
use echod_kernel::external as kext;
use echod_kernel::object as kobject;
use echod_kernel::properties as kprops;
use echod_kernel::store::AState as KState;
use echod_kernel::tags as ktags;
use echod_kernel::types as kernel;
use echod_kernel::types::{APromise, ATask};

use crate::bridge::*;
use crate::promise_sim::*;
use crate::read_sim::*;
use crate::relation::*;
use crate::*;

verus! {

// ---------------------------------------------------------------------------
// Requests under the mapping
// ---------------------------------------------------------------------------

pub open spec fn task_get_req(r: kernel::ATaskGetReq) -> abs::ATaskGetReq {
    abs::ATaskGetReq { id: ident(r.id) }
}

pub open spec fn task_create_req(r: kernel::ATaskCreateReq) -> abs::ATaskCreateReq {
    abs::ATaskCreateReq { pid: text(r.pid), ttl: r.ttl, action: promise_create_req(r.action) }
}

pub open spec fn task_acquire_req(r: kernel::ATaskAcquireReq) -> abs::ATaskAcquireReq {
    abs::ATaskAcquireReq { id: ident(r.id), version: r.version, pid: text(r.pid), ttl: r.ttl }
}

pub open spec fn task_fulfill_req(r: kernel::ATaskFulfillReq) -> abs::ATaskFulfillReq {
    abs::ATaskFulfillReq { id: ident(r.id), version: r.version, action: promise_settle_req(r.action) }
}

pub open spec fn task_release_req(r: kernel::ATaskReleaseReq) -> abs::ATaskReleaseReq {
    abs::ATaskReleaseReq { id: ident(r.id), version: r.version }
}

pub open spec fn task_halt_req(r: kernel::ATaskHaltReq) -> abs::ATaskHaltReq {
    abs::ATaskHaltReq { id: ident(r.id) }
}

pub open spec fn task_continue_req(r: kernel::ATaskContinueReq) -> abs::ATaskContinueReq {
    abs::ATaskContinueReq { id: ident(r.id) }
}

pub open spec fn task_fence_action(a: kernel::ATaskFenceAction) -> abs::ATaskFenceAction {
    match a {
        kernel::ATaskFenceAction::Create(c) => abs::ATaskFenceAction::Create(promise_create_req(c)),
        kernel::ATaskFenceAction::Settle(c) => abs::ATaskFenceAction::Settle(promise_settle_req(c)),
    }
}

pub open spec fn task_fence_req(r: kernel::ATaskFenceReq) -> abs::ATaskFenceReq {
    abs::ATaskFenceReq { id: ident(r.id), version: r.version, action: task_fence_action(r.action) }
}

pub open spec fn task_fence_check_req(r: kernel::ATaskFenceCheckReq) -> abs::ATaskFenceCheckReq {
    abs::ATaskFenceCheckReq { id: ident(r.id), version: r.version }
}

// ---------------------------------------------------------------------------
// Doors on the document
// ---------------------------------------------------------------------------

/// Every task's version has headroom, and every task's resume list has a
/// length. The first is where the kernel's `u32` counter and the Lean text's
/// naturals part; the second is true of any executable row.
pub open spec fn doc_headroom(k: KState) -> bool {
    forall|id: Chars| #[trigger] k.objects.contains_key(id) ==> match k.objects[id].task {
        Some(t) => t.version < kernel::MAX_VERSION && t.resumes.len() <= u64::MAX,
        None => true,
    }
}

pub open spec fn fence_in_domain(r: kernel::ATaskFenceReq) -> bool {
    &&& canonical(r.id)
    &&& match r.action {
        kernel::ATaskFenceAction::Create(c) => create_in_domain(c),
        kernel::ATaskFenceAction::Settle(c) => canonical(c.id),
    }
}

// ---------------------------------------------------------------------------
// Pieces
// ---------------------------------------------------------------------------

/// What `readTaskObject` left at `id`: the projected row, with a task.
pub proof fn lemma_after_task_read(k: KState, a: AState, id: Chars, now: u64)
    requires
        doc_related(k, a),
        canonical(id),
        k.has_task(id),
    ensures ({
        let kb = kext::spec_read_task(k, id, now as nat);
        let q = k.objects[id].project(now as nat);
        &&& kb.objects.contains_key(id)
        &&& kb.objects[id] == q
        &&& q.id == id
        &&& q.task is Some
        &&& canonical_promise(q)
        &&& kb.schedules == k.schedules
        &&& doc_related(kb, after_read(a, ident(id), now))
        &&& tspec::spec_task_read(a, ident(id), now, true).object == Some(object(q))
        &&& tspec::spec_task_read(a, ident(id), now, true).effects == abs_state::spec_read_effects(a, ident(id), now, true)
    }),
{
    lemma_read_task_sim(k, a, id, now);
    lemma_project_canonical(k.objects[id], now);
}

/// A `SetTask` on the row the read left, after the read's effects.
pub proof fn lemma_task_write(k: KState, a: AState, id: Chars, now: u64, t2: ATask)
    requires
        doc_related(k, a),
        canonical(id),
        k.has_task(id),
        canonical_task(t2),
    ensures ({
        let kb = kext::spec_read_task(k, id, now as nat);
        let reads = abs_state::spec_read_effects(a, ident(id), now, true);
        doc_related(
            KState { objects: kb.objects.insert(id, kb.objects[id].with_task(t2)), ..kb },
            spec_apply_all(a, reads.push(AEffect::SetTask(ident(id), task(t2)))))
    }),
{
    lemma_after_task_read(k, a, id, now);
    let kb = kext::spec_read_task(k, id, now as nat);
    let ab = after_read(a, ident(id), now);
    let reads = abs_state::spec_read_effects(a, ident(id), now, true);
    lemma_set_task(kb.objects, ab.objects, id, t2);
    lemma_apply_all_push(a, reads, AEffect::SetTask(ident(id), task(t2)));
}

/// The kernel's acquired task and the Abstract claimed task agree.
pub proof fn lemma_acquire_shape(t: ATask, pid: Chars, ttl: u64, now: u64)
    requires
        now <= kernel::MAX_TIME,
        ttl <= kernel::MAX_TIME,
        t.version < kernel::MAX_VERSION,
    ensures
        task(t.acquire(pid, ttl as nat, now as nat)) == tspec::spec_task_claimed(task(t), text(pid), ttl, now),
        canonical_task(t.acquire(pid, ttl as nat, now as nat)),
{
    assert(id_list(Seq::<Chars>::empty()) =~= Seq::<abs::AIdent>::empty());
}

/// The claim's response.
pub proof fn lemma_claim_of(p: APromise)
    requires
        p.task is Some,
        p.task.unwrap().resumes.len() <= u64::MAX,
    ensures
        task_claim_res(kext::claim_of(p)) == tspec::spec_task_claim_ok(object(p), task(p.task.unwrap())),
{
    lemma_promise_record(p);
    lemma_task_record(p.task.unwrap(), p.id);
}

// ---------------------------------------------------------------------------
// The handlers
// ---------------------------------------------------------------------------

pub proof fn lemma_task_get_sim(k: KState, a: AState, req: kernel::ATaskGetReq, now: u64)
    requires
        doc_related(k, a),
        doc_headroom(k),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_task_get(k, req, now as nat);
        let r = tspec::spec_task_get_action(a, task_get_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& task_get_res(res) == r.response
    }),
{
    let id = req.id;
    lemma_read_task_sim(k, a, id, now);
    if k.has_task(id) {
        lemma_after_task_read(k, a, id, now);
        let q = k.objects[id].project(now as nat);
        let t = q.task.unwrap();
        assert(t.resumes.len() <= u64::MAX) by {
            match k.objects[id].task {
                Some(t0) => { assert(t0.resumes.len() <= u64::MAX); }
                None => {}
            }
        }
        lemma_task_record(t, id);
    }
}

pub proof fn lemma_task_create_sim(k: KState, a: AState, req: kernel::ATaskCreateReq, now: u64)
    requires
        doc_related(k, a),
        doc_headroom(k),
        kprops::kernel_bounds(k),
        create_in_domain(req.action),
        req.ttl <= kernel::MAX_TIME,
        now <= kernel::MAX_TIME,
    ensures ({
        let (k2, res) = kext::spec_task_create(k, req, now as nat);
        let r = tspec::spec_task_create_action(a, task_create_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& task_claim_res(res) == r.response
    }),
{
    let act = req.action;
    let id = act.id;
    let aid = ident(id);
    let areq = task_create_req(req);
    lemma_strip_identity(act.tags);
    assert(pspec::spec_normalize_create(areq.action) == areq.action);
    lemma_timer_targeted(act.tags);
    lemma_otype(act.tags);
    if ktags::otype(act.tags) != ktags::OType::Runnable {
    } else if !k.objects.contains_key(id) {
        lemma_read_absent(k, a, id, now);
        lemma_is_timer(act.tags);
        let p = if act.timeout_at > now { kobject::spec_create_acquired(act, req.pid, req.ttl as nat, now as nat) } else { kobject::spec_create(act, now as nat) };
        let ap = tspec::spec_task_created_promise(areq.action, now);
        let at = tspec::spec_task_created_task(areq, ap, now);
        assert(tags(Seq::<(Chars, Chars)>::empty()) =~= Seq::<abs::ATag>::empty());
        assert(id_list(Seq::<Chars>::empty()) =~= Seq::<abs::AIdent>::empty());
        assert(text_list(Seq::<Chars>::empty()) =~= Seq::<abs::AText>::empty());
        assert(promise(p) == ap);
        assert(p.task is Some && task(p.task.unwrap()) == at);
        assert(p.id == id);
        let t = p.task.unwrap();
        let p0 = APromise { task: None, ..p };
        assert(canonical_promise(p0));
        assert(task_opt(p0.task) == None::<abs_state::ATaskObject>);
        lemma_set_promise(k.objects, a.objects, id, p0);
        let effects = Seq::<AEffect>::empty() + seq![AEffect::SetPromise(aid, ap)] + seq![AEffect::SetTask(aid, at)];
        assert(effects =~= seq![AEffect::SetPromise(aid, ap)].push(AEffect::SetTask(aid, at)));
        lemma_apply_all_one(a, AEffect::SetPromise(aid, ap));
        lemma_apply_all_push(a, seq![AEffect::SetPromise(aid, ap)], AEffect::SetTask(aid, at));
        let a1 = spec_apply_effect(a, AEffect::SetPromise(aid, ap));
        let k1 = k.objects.insert(id, p0);
        assert(canonical_task(t));
        lemma_set_task(k1, a1.objects, id, t);
        assert(k1[id].with_task(t) == p);
        assert(k1.insert(id, p) =~= k.objects.insert(id, p));
        lemma_claim_of(p);
    } else {
        lemma_read_sim(k, a, id, now);
        lemma_project_canonical(k.objects[id], now);
        let q = k.objects[id].project(now as nat);
        lemma_otype(q.tags);
        if ktags::otype(q.tags) != ktags::OType::Runnable {
        } else {
            match q.task {
                None => {}
                Some(t) => {
                    assert(t.resumes.len() <= u64::MAX && t.version < kernel::MAX_VERSION) by {
                        let t0 = k.objects[id].task.unwrap();
                        assert(t0.version < kernel::MAX_VERSION && t0.resumes.len() <= u64::MAX);
                    }
                    if t.state == kernel::TaskState::Fulfilled {
                        lemma_claim_of(q);
                    } else if t.state != kernel::TaskState::Pending {
                    } else {
                        assert(k.has_task(id));
                        lemma_acquire_shape(t, req.pid, req.ttl, now);
                        let t2 = t.acquire(req.pid, req.ttl as nat, now as nat);
                        assert(kext::spec_read_task(k, id, now as nat) == kext::spec_read(k, id, now as nat));
                        lemma_task_write(k, a, id, now, t2);
                        lemma_claim_of(q.with_task(t2));
                    }
                }
            }
        }
    }
}

pub proof fn lemma_task_acquire_sim(k: KState, a: AState, req: kernel::ATaskAcquireReq, now: u64)
    requires
        doc_related(k, a),
        doc_headroom(k),
        canonical(req.id),
        req.ttl <= kernel::MAX_TIME,
        now <= kernel::MAX_TIME,
    ensures ({
        let (k2, res) = kext::spec_task_acquire(k, req, now as nat);
        let r = tspec::spec_task_acquire_action(a, task_acquire_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& task_claim_res(res) == r.response
    }),
{
    let id = req.id;
    lemma_read_task_sim(k, a, id, now);
    if k.has_task(id) {
        lemma_after_task_read(k, a, id, now);
        let q = k.objects[id].project(now as nat);
        let t = q.task.unwrap();
        assert(t.resumes.len() <= u64::MAX && t.version < kernel::MAX_VERSION) by {
            let t0 = k.objects[id].task.unwrap();
            assert(t0.version < kernel::MAX_VERSION && t0.resumes.len() <= u64::MAX);
        }
        if t.state != kernel::TaskState::Pending || q.state != kernel::PromiseState::Pending || t.version != req.version {
        } else {
            lemma_acquire_shape(t, req.pid, req.ttl, now);
            let t2 = t.acquire(req.pid, req.ttl as nat, now as nat);
            lemma_task_write(k, a, id, now, t2);
            lemma_claim_of(q.with_task(t2));
        }
    }
}

pub proof fn lemma_task_fulfill_sim(k: KState, a: AState, req: kernel::ATaskFulfillReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_task_fulfill(k, req, now as nat);
        let r = tspec::spec_task_fulfill_action(a, task_fulfill_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& task_fulfill_res(res) == r.response
    }),
{
    let id = req.id;
    let aid = ident(id);
    assert(pspec::spec_settable(promise_state(req.action.state)) == req.action.state.spec_settable());
    if !req.action.state.spec_settable() {
    } else {
        lemma_read_task_sim(k, a, id, now);
        if k.has_task(id) {
            lemma_after_task_read(k, a, id, now);
            let kb = kext::spec_read_task(k, id, now as nat);
            let ab = after_read(a, aid, now);
            let q = k.objects[id].project(now as nat);
            let t = q.task.unwrap();
            if t.state != kernel::TaskState::Acquired || q.state != kernel::PromiseState::Pending || t.version != req.version {
            } else {
                lemma_settle_move(kb, ab, id, req.action.state, req.action.value, now);
                let promise2 = abs_state::APromiseObject { state: promise_state(req.action.state), value: value(req.action.value), settled_at: Some(now), ..promise(q) };
                let reads = abs_state::spec_read_effects(a, aid, now, true);
                lemma_apply_all_app(a, reads, abs_state::spec_set_settled_effects(object(q), promise2));
                lemma_promise_record(q.settle(req.action.state, req.action.value, now as nat));
            }
        }
    }
}

pub proof fn lemma_task_release_sim(k: KState, a: AState, req: kernel::ATaskReleaseReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_task_release(k, req, now as nat);
        let r = tspec::spec_task_release_action(a, task_release_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& status_res(res) == r.response
    }),
{
    let id = req.id;
    lemma_read_task_sim(k, a, id, now);
    if k.has_task(id) {
        lemma_after_task_read(k, a, id, now);
        let q = k.objects[id].project(now as nat);
        let t = q.task.unwrap();
        if t.state != kernel::TaskState::Acquired || q.state != kernel::PromiseState::Pending || t.version != req.version {
        } else {
            let t2 = t.release(now as nat);
            assert(canonical_task(t2));
            assert(task(t2) == abs_state::ATaskObject {
                state: abs::TaskState::Pending, pid: None, ttl: None, lease_timeout_at: None, retry_timeout_at: Some(now), ..task(t) });
            lemma_task_write(k, a, id, now, t2);
        }
    }
}

pub proof fn lemma_task_halt_sim(k: KState, a: AState, req: kernel::ATaskHaltReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_task_halt(k, req, now as nat);
        let r = tspec::spec_task_halt_action(a, task_halt_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& status_res(res) == r.response
    }),
{
    let id = req.id;
    lemma_read_task_sim(k, a, id, now);
    if k.has_task(id) {
        lemma_after_task_read(k, a, id, now);
        let q = k.objects[id].project(now as nat);
        let t = q.task.unwrap();
        if t.state == kernel::TaskState::Fulfilled || t.state == kernel::TaskState::Halted {
        } else {
            let t2 = t.halt();
            assert(canonical_task(t2));
            assert(task(t2) == abs_state::ATaskObject {
                state: abs::TaskState::Halted, pid: None, ttl: None, lease_timeout_at: None, retry_timeout_at: None, ..task(t) });
            lemma_task_write(k, a, id, now, t2);
        }
    }
}

pub proof fn lemma_task_continue_sim(k: KState, a: AState, req: kernel::ATaskContinueReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_task_continue(k, req, now as nat);
        let r = tspec::spec_task_continue_action(a, task_continue_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& status_res(res) == r.response
    }),
{
    let id = req.id;
    lemma_read_task_sim(k, a, id, now);
    if k.has_task(id) {
        lemma_after_task_read(k, a, id, now);
        let q = k.objects[id].project(now as nat);
        let t = q.task.unwrap();
        if t.state != kernel::TaskState::Halted || q.state != kernel::PromiseState::Pending {
        } else {
            let t2 = t.continue_(now as nat);
            assert(canonical_task(t2));
            assert(task(t2) == abs_state::ATaskObject { state: abs::TaskState::Pending, retry_timeout_at: Some(now), ..task(t) });
            lemma_task_write(k, a, id, now, t2);
        }
    }
}

pub proof fn lemma_task_fence_check_sim(k: KState, a: AState, req: kernel::ATaskFenceCheckReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_task_fence_check(k, req, now as nat);
        let r = tspec::spec_task_fence_check_action(a, task_fence_check_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& status_res(res) == r.response
    }),
{
    let id = req.id;
    lemma_read_task_sim(k, a, id, now);
    if k.has_task(id) {
        lemma_after_task_read(k, a, id, now);
    }
}

/// A promise create action reads one object; two states that find the same
/// object there give the same effects and response.
pub proof fn lemma_create_action_find(a: AState, a2: AState, req: abs::APromiseCreateReq, now: u64)
    requires
        spec_find_object(a.objects, pspec::spec_normalize_create(req).id) == spec_find_object(a2.objects, pspec::spec_normalize_create(req).id),
    ensures
        pspec::spec_promise_create_action(a, req, now, true).effects == pspec::spec_promise_create_action(a2, req, now, true).effects,
        pspec::spec_promise_create_action(a, req, now, true).response == pspec::spec_promise_create_action(a2, req, now, true).response,
{
    let id = pspec::spec_normalize_create(req).id;
    assert(abs_state::spec_read_object(a, id, now) == abs_state::spec_read_object(a2, id, now));
    assert(abs_state::spec_read_effects(a, id, now, true) == abs_state::spec_read_effects(a2, id, now, true));
}

pub proof fn lemma_settle_action_find(a: AState, a2: AState, req: abs::APromiseSettleReq, now: u64)
    requires
        spec_find_object(a.objects, req.id) == spec_find_object(a2.objects, req.id),
    ensures
        pspec::spec_promise_settle_action(a, req, now, true).effects == pspec::spec_promise_settle_action(a2, req, now, true).effects,
        pspec::spec_promise_settle_action(a, req, now, true).response == pspec::spec_promise_settle_action(a2, req, now, true).response,
{
    assert(abs_state::spec_read_object(a, req.id, now) == abs_state::spec_read_object(a2, req.id, now));
    assert(abs_state::spec_read_effects(a, req.id, now, true) == abs_state::spec_read_effects(a2, req.id, now, true));
}

pub proof fn lemma_task_fence_sim(k: KState, a: AState, req: kernel::ATaskFenceReq, now: u64)
    requires
        doc_related(k, a),
        fence_in_domain(req),
    ensures ({
        let (k2, res) = kext::spec_task_fence(k, req, now as nat);
        let r = tspec::spec_task_fence_action(a, task_fence_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& task_fence_res(res) == r.response
    }),
{
    let id = req.id;
    let aid = ident(id);
    let target = kext::fence_target(req.action);
    let areq = task_fence_req(req);
    assert(tspec::spec_task_fence_target(areq.action) == ident(target));
    lemma_same_origin(target, id);
    if ident(target) == aid {
        lemma_ident_injective(target, id);
    }
    if target == id || !kernel::same_origin_spec(target, id) {
    } else {
        lemma_read_task_sim(k, a, id, now);
        if k.has_task(id) {
            lemma_after_task_read(k, a, id, now);
            let kb = kext::spec_read_task(k, id, now as nat);
            let ab = after_read(a, aid, now);
            let q = k.objects[id].project(now as nat);
            let t = q.task.unwrap();
            let reads = abs_state::spec_read_effects(a, aid, now, true);
            if t.state != kernel::TaskState::Acquired || q.state != kernel::PromiseState::Pending || t.version != req.version {
            } else {
                // The target is another object: the read of the task left it alone.
                assert(kb.objects.contains_key(target) == k.objects.contains_key(target));
                assert(k.objects.contains_key(target) ==> kb.objects[target] == k.objects[target]);
                lemma_find_via_relation(k, a, kb, ab, target);
                match req.action {
                    kernel::ATaskFenceAction::Create(c) => {
                        let ac = promise_create_req(c);
                        lemma_strip_identity(c.tags);
                        assert(pspec::spec_normalize_create(ac) == ac);
                        lemma_create_action_find(a, ab, ac, now);
                        lemma_promise_create_sim(kb, ab, c, now);
                        let inner = pspec::spec_promise_create_action(a, ac, now, true);
                        lemma_apply_all_app(a, reads, inner.effects);
                    }
                    kernel::ATaskFenceAction::Settle(c) => {
                        let ac = promise_settle_req(c);
                        lemma_settle_action_find(a, ab, ac, now);
                        lemma_promise_settle_sim(kb, ab, c, now);
                        let inner = pspec::spec_promise_settle_action(a, ac, now, true);
                        lemma_apply_all_app(a, reads, inner.effects);
                    }
                }
            }
        }
    }
}

} // verus!
