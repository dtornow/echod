//! The internal steps on objects, simulated: the promise deadline, the lease
//! and retry timeouts, the callback and the listener.
//!
//! The kernel gives each as a function of the document (`internal.rs`); the
//! Abstract as effects of the pre-state (`internal.rs`). The messages the
//! retry and the listener emit go to the kernel's outbox and the Abstract's
//! `SetMessage`; neither is document state here, so they do not enter the
//! relation.
//!
//! One kernel step is not always one Abstract action. The kernel's callback
//! drain materializes the awaiter whether or not it carries a task; the
//! Abstract's `resumeOne` reads only task objects. When the awaiter is a bare
//! promise, the kernel step is the Abstract callback followed by the
//! Abstract promise timeout on the awaiter — two actions, both legal.

use vstd::prelude::*;

use echod_abstract::internal as aint;
use echod_abstract::state as abs_state;
use echod_abstract::state::{AEffect, AObject, AState, spec_apply_all, spec_apply_effect, spec_find_object};
use echod_abstract::types as abs;
use echod_kernel::external as kext;
use echod_kernel::internal as kint;
use echod_kernel::object as kobject;
use echod_kernel::properties as kprops;
use echod_kernel::store::AState as KState;
use echod_kernel::types as kernel;
use echod_kernel::types::{APromise, ATask};

use crate::actions::*;
use crate::bridge::*;
use crate::promise_sim::lemma_find_via_relation;
use crate::read_sim::*;
use crate::relation::*;
use crate::suspend_sim::lemma_untouched_read;
use crate::*;

verus! {

pub open spec fn promise_timeout_req(id: Chars) -> abs::APromiseTimeoutReq {
    abs::APromiseTimeoutReq { id: ident(id) }
}

pub open spec fn lease_timeout_req(id: Chars) -> abs::ATaskLeaseTimeoutReq {
    abs::ATaskLeaseTimeoutReq { id: ident(id) }
}

pub open spec fn retry_timeout_req(id: Chars) -> abs::ATaskRetryTimeoutReq {
    abs::ATaskRetryTimeoutReq { id: ident(id) }
}

pub open spec fn callback_req(x: Chars, y: Chars) -> abs::APromiseRegisterCallbackReq {
    abs::APromiseRegisterCallbackReq { awaited: ident(x), awaiter: ident(y) }
}

pub open spec fn listener_req(x: Chars, addr: Chars) -> abs::APromiseRegisterListenerReq {
    abs::APromiseRegisterListenerReq { awaited: ident(x), address: text(addr) }
}

/// A message effect leaves objects and schedules alone.
pub proof fn lemma_message_effect(k: KState, a: AState, addr: abs::AText, m: abs_state::AMessage)
    requires doc_related(k, a),
    ensures doc_related(k, spec_apply_effect(a, AEffect::SetMessage(addr, m))),
{
}

// ---------------------------------------------------------------------------
// The deadline
// ---------------------------------------------------------------------------

pub proof fn lemma_promise_timeout_sim(k: KState, a: AState, id: Chars, now: u64)
    requires doc_related(k, a), canonical(id),
    ensures doc_related(
        kext::with_objects(k, kint::promise_timeout_objects(k, id, now as nat)),
        spec_apply_all(a, aint::promise_timeout_semantics(a, promise_timeout_req(id), now))),
{
    if k.objects.contains_key(id) {
        lemma_read_sim(k, a, id, now);
    } else {
        lemma_read_absent(k, a, id, now);
        lemma_apply_all_empty(a);
    }
}

// ---------------------------------------------------------------------------
// The lease
// ---------------------------------------------------------------------------

/// A promise pending and ahead of its deadline projects to itself.
pub proof fn lemma_project_live(p: APromise, now: u64)
    requires p.state == kernel::PromiseState::Pending, p.timeout_at > now,
    ensures p.project(now as nat) == p,
{
    match p.task {
        Some(t) => { assert(t.view_through(p) == t); }
        None => {}
    }
}

pub proof fn lemma_lease_timeout_sim(k: KState, a: AState, id: Chars, now: u64)
    requires doc_related(k, a), canonical(id),
    ensures doc_related(
        kext::with_objects(k, kint::lease_timeout_objects(k, id, now as nat)),
        spec_apply_all(a, aint::lease_timeout_semantics(a, lease_timeout_req(id), now))),
{
    let aid = ident(id);
    lemma_related_contains(k.objects, a.objects, id);
    if k.objects.contains_key(id) {
        let p = k.objects[id];
        assert(spec_find_object(a.objects, aid) == Some(object(p)));
        let q = p.project(now as nat);
        lemma_project_object(p, now);
        // The lease view does not materialize: its only effect is the write.
        assert(abs_state::spec_read_task_effects(a, aid, now, false) =~= Seq::<AEffect>::empty());
        if kint::lease_due(p, now as nat) {
            let t = p.task.unwrap();
            lemma_project_live(p, now);
            assert(abs_state::spec_read_task_object(a, aid, now) == Some(object(p)));
            let end = t.lease_timeout_at.unwrap();
            let t2 = t.release(end as nat);
            assert(canonical_task(t2));
            let next = abs_state::ATaskObject {
                state: abs::TaskState::Pending, pid: None, ttl: None, lease_timeout_at: None,
                retry_timeout_at: Some(end), ..task(t) };
            assert(task(t2) == next);
            lemma_set_task(k.objects, a.objects, id, t2);
            assert(Seq::<AEffect>::empty() + seq![AEffect::SetTask(aid, next)] =~= seq![AEffect::SetTask(aid, next)]);
            lemma_apply_all_one(a, AEffect::SetTask(aid, next));
        } else {
            match p.task {
                Some(t) => {
                    assert(abs_state::spec_read_task_object(a, aid, now) == Some(object(q)));
                    let qt = q.task.unwrap();
                    if qt.state == kernel::TaskState::Acquired && qt.lease_timeout_at is Some
                        && qt.lease_timeout_at.unwrap() <= now && q.state == kernel::PromiseState::Pending {
                        assert(p.state == kernel::PromiseState::Pending && p.timeout_at > now);
                        lemma_project_live(p, now);
                        assert(kint::lease_due(p, now as nat));
                        assert(false);
                    }
                }
                None => {}
            }
            lemma_apply_all_empty(a);
        }
    } else {
        lemma_apply_all_empty(a);
    }
}

// ---------------------------------------------------------------------------
// The retry
// ---------------------------------------------------------------------------

/// Lean's `nextOffer` on both sides, from a due instant at or before `now`:
/// inside the time door the Abstract's saturation never fires.
pub proof fn lemma_next_offer(due: u64, now: u64, t: u64)
    requires due <= now, now <= kernel::MAX_TIME, t <= kernel::MAX_TIME,
    ensures
        kobject::next_offer(due as nat, now as nat, t as nat) == abs::spec_next_offer(due, now, t) as nat,
{
    if t == 0 {
    } else {
        let x = (now - due) as int;
        let q = x / (t as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, t as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(x, t as int);
        assert((t as int) * q <= x);
        assert((t as int) * (q + 1) == (t as int) * q + (t as int)) by (nonlinear_arith);
        assert(due + (t as int) * (q + 1) <= now + t);
        assert(now + t <= u64::MAX);
    }
}

pub proof fn lemma_retry_timeout_sim(k: KState, a: AState, id: Chars, now: u64, rt: u64)
    requires doc_related(k, a), canonical(id), now <= kernel::MAX_TIME, rt <= kernel::MAX_TIME,
    ensures doc_related(
        kint::retry_timeout_state(k, id, now as nat, rt as nat),
        spec_apply_all(a, aint::retry_timeout_semantics(a, retry_timeout_req(id), now, rt))),
{
    let aid = ident(id);
    lemma_related_contains(k.objects, a.objects, id);
    if k.objects.contains_key(id) {
        let p = k.objects[id];
        assert(spec_find_object(a.objects, aid) == Some(object(p)));
        let q = p.project(now as nat);
        lemma_project_object(p, now);
        assert(abs_state::spec_read_task_effects(a, aid, now, false) =~= Seq::<AEffect>::empty());
        if kint::retry_due(p, now as nat) {
            let t = p.task.unwrap();
            lemma_project_live(p, now);
            assert(abs_state::spec_read_task_object(a, aid, now) == Some(object(p)));
            let due = t.retry_timeout_at.unwrap();
            lemma_next_offer(due, now, rt);
            let t2 = t.rearm(now as nat, rt as nat);
            assert(kprops::opt_or_zero(t.retry_timeout_at) == due as nat);
            assert(canonical_task(t2));
            let next = abs_state::ATaskObject { retry_timeout_at: Some(abs::spec_next_offer(due, now, rt)), ..task(t) };
            assert(task(t2) == next);
            lemma_set_task(k.objects, a.objects, id, t2);
            let message = abs_state::AMessage {
                kind: abs_state::MessageKind::Execute, task_id: Some(aid), version: t.version, promise: None };
            let addr = aint::internal_target_or_empty(promise(p).tags);
            let one = seq![AEffect::SetTask(aid, next)];
            assert(Seq::<AEffect>::empty() + one =~= one);
            assert(one + seq![AEffect::SetMessage(addr, message)] =~= one.push(AEffect::SetMessage(addr, message)));
            lemma_apply_all_one(a, AEffect::SetTask(aid, next));
            lemma_apply_all_push(a, one, AEffect::SetMessage(addr, message));
            let k2 = kint::retry_timeout_state(k, id, now as nat, rt as nat);
            let k1 = KState { objects: k.objects.insert(id, p.with_task(t2)), ..k };
            assert(k2.objects == k1.objects);
            assert(k2.schedules == k1.schedules);
            assert(doc_related(k1, spec_apply_effect(a, AEffect::SetTask(aid, next))));
            lemma_message_effect(k1, spec_apply_effect(a, AEffect::SetTask(aid, next)), addr, message);
        } else {
            match p.task {
                Some(t) => {
                    assert(abs_state::spec_read_task_object(a, aid, now) == Some(object(q)));
                    let qt = q.task.unwrap();
                    if qt.state == kernel::TaskState::Pending && qt.retry_timeout_at is Some
                        && qt.retry_timeout_at.unwrap() <= now && q.state == kernel::PromiseState::Pending {
                        assert(p.state == kernel::PromiseState::Pending && p.timeout_at > now);
                        lemma_project_live(p, now);
                        assert(kint::retry_due(p, now as nat));
                        assert(false);
                    }
                }
                None => {}
            }
            lemma_apply_all_empty(a);
        }
    } else {
        lemma_apply_all_empty(a);
    }
}

// ---------------------------------------------------------------------------
// The callback
// ---------------------------------------------------------------------------

/// Removal keeps every remaining element from the list.
pub proof fn lemma_without_index(s: Seq<Chars>, x: Chars)
    ensures forall|i: int| 0 <= i < kobject::without(s, x).len() ==> s.contains(#[trigger] kobject::without(s, x)[i]),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_without_index(s.drop_last(), x);
        let out = kobject::without(s, x);
        let inner = kobject::without(s.drop_last(), x);
        assert forall|i: int| 0 <= i < out.len() implies s.contains(#[trigger] out[i]) by {
            if s.last() == x || i < inner.len() {
                assert(out[i] == inner[i]);
                assert(s.drop_last().contains(inner[i]));
                let j = choose|j: int| 0 <= j < s.drop_last().len() && s.drop_last()[j] == inner[i];
                assert(s[j] == out[i]);
            } else {
                assert(out[i] == s.last());
            }
        }
    }
}

/// The kernel's callback drain touches the awaiter even when it is a bare
/// promise; the Abstract's does not. The kernel step then owes the Abstract
/// a promise timeout on the awaiter after the callback.
pub open spec fn callback_touches_bare_awaiter(k: KState, x: Chars, y: Chars, now: u64) -> bool {
    &&& k.objects.contains_key(x)
    &&& {
        let p = k.objects[x].project(now as nat);
        p.state != kernel::PromiseState::Pending && p.callbacks.contains(y)
    }
    &&& k.objects.contains_key(y)
    &&& !k.has_task(y)
}

/// The Abstract actions one kernel callback step is: the callback, then, for
/// a bare awaiter, its promise timeout.
pub open spec fn callback_actions(k: KState, x: Chars, y: Chars, now: u64) -> Seq<AbsInternal> {
    if callback_touches_bare_awaiter(k, x, y, now) {
        seq![AbsInternal::Callback(callback_req(x, y)), AbsInternal::PromiseTimeout(promise_timeout_req(y))]
    } else {
        seq![AbsInternal::Callback(callback_req(x, y))]
    }
}

pub proof fn lemma_id_list_one(x: Chars)
    ensures id_list(seq![x]) == seq![ident(x)],
{
    assert(seq![x].drop_last() =~= Seq::<Chars>::empty());
    assert(seq![x].last() == x);
    assert(id_list(Seq::<Chars>::empty()) =~= Seq::<abs::AIdent>::empty());
    assert(Seq::<abs::AIdent>::empty().push(ident(x)) =~= seq![ident(x)]);
}

/// The kernel's `resumeOne` on an awaiter that carries a task, as the tail of
/// `callback_state`: the awaiter materialized, then woken or buffered.
pub open spec fn resume_state(k2: KState, x: Chars, y: Chars, now: nat, since: nat) -> KState {
    let q = k2.objects[y].project(now);
    let k3 = kext::with_objects(k2, k2.objects.insert(y, q));
    match q.task {
        None => k3,
        Some(t) => {
            if t.state == kernel::TaskState::Suspended {
                kext::with_objects(k3, k3.objects.insert(y, q.with_task(t.wake(x, since))))
            } else if t.state != kernel::TaskState::Fulfilled {
                kext::with_objects(k3, k3.objects.insert(y, q.with_task(t.buffer(x))))
            } else {
                k3
            }
        }
    }
}

/// `resumeOne` on an awaiter with a task: the kernel reads it after the
/// awaited promise's edit, the Abstract in the pre-state; `y` is untouched
/// between, so both see the same object.
pub proof fn lemma_resume_sim(k: KState, a: AState, k2: KState, a2: AState, x: Chars, y: Chars, now: u64, since: u64)
    requires
        doc_related(k, a),
        doc_related(k2, a2),
        canonical(x),
        canonical(y),
        k.has_task(y),
        k2.objects.contains_key(y),
        k2.objects[y] == k.objects[y],
    ensures doc_related(
        resume_state(k2, x, y, now as nat, since as nat),
        spec_apply_all(a2, aint::resume_one_semantics(a, ident(x), ident(y), now, since))),
{
    let ax = ident(x);
    let ay = ident(y);
    let reads_y = abs_state::spec_read_effects(a, ay, now, true);
    let resume = aint::resume_one_semantics(a, ax, ay, now, since);
    lemma_read_task_sim(k, a, y, now);
    lemma_untouched_read(k, a, k2, a2, y, now);
    let q = k.objects[y].project(now as nat);
    lemma_project_canonical(k.objects[y], now);
    let k3 = kext::spec_read(k2, y, now as nat);
    let a3 = spec_apply_all(a2, reads_y);
    assert(k3 == kext::with_objects(k2, k2.objects.insert(y, q)));
    assert(doc_related(k3, a3));
    assert(abs_state::spec_read_task_object(a, ay, now) == Some(object(q)));
    assert(abs_state::spec_read_task_effects(a, ay, now, true) == reads_y);
    let t = q.task.unwrap();
    lemma_id_list_one(x);
    lemma_id_list_contains(t.resumes, x);
    lemma_id_list_push(t.resumes, x);
    if t.state == kernel::TaskState::Suspended {
        let t2 = t.wake(x, since as nat);
        let next = abs_state::ATaskObject {
            state: abs::TaskState::Pending, resumes: seq![ax], retry_timeout_at: Some(since), ..task(t) };
        assert(task(t2) == next);
        assert(resume == reads_y + seq![AEffect::SetTask(ay, next)]);
        assert(resume =~= reads_y.push(AEffect::SetTask(ay, next)));
        lemma_apply_all_push(a2, reads_y, AEffect::SetTask(ay, next));
        assert(canonical_task(t2));
        lemma_set_task(k3.objects, a3.objects, y, t2);
    } else if t.state == kernel::TaskState::Fulfilled {
        assert(resume == reads_y);
    } else if t.resumes.contains(x) {
        assert(resume == reads_y);
        assert(t.buffer(x) == t);
        assert(q.with_task(t) == q);
        assert(k3.objects.insert(y, q) =~= k3.objects);
        assert(resume_state(k2, x, y, now as nat, since as nat) == k3);
    } else {
        let t2 = t.buffer(x);
        let next = abs_state::ATaskObject { resumes: task(t).resumes.push(ax), ..task(t) };
        assert(task(t2) == next);
        assert(resume == reads_y + seq![AEffect::SetTask(ay, next)]);
        assert(resume =~= reads_y.push(AEffect::SetTask(ay, next)));
        lemma_apply_all_push(a2, reads_y, AEffect::SetTask(ay, next));
        assert(canonical_task(t2));
        lemma_set_task(k3.objects, a3.objects, y, t2);
    }
}

pub proof fn lemma_callback_sim(k: KState, a: AState, x: Chars, y: Chars, now: u64, rt: u64)
    requires doc_related(k, a), canonical(x), canonical(y), x != y,
    ensures doc_related(
        kint::callback_state(k, x, y, now as nat),
        internal_run(a, callback_actions(k, x, y, now), now, rt)),
{
    let ax = ident(x);
    let ay = ident(y);
    let cb = aint::callback_semantics(a, callback_req(x, y), now);
    let one = AbsInternal::Callback(callback_req(x, y));
    let acts = callback_actions(k, x, y, now);
    let a_cb = spec_apply_all(a, cb);
    lemma_internal_run_one(a, one, now, rt);
    if callback_touches_bare_awaiter(k, x, y, now) {
        let two = AbsInternal::PromiseTimeout(promise_timeout_req(y));
        assert(acts =~= seq![one].push(two));
        lemma_internal_run_push(a, seq![one], two, now, rt);
        assert(internal_run(a, acts, now, rt) == internal_step(a_cb, two, now, rt));
    } else {
        assert(internal_run(a, acts, now, rt) == a_cb);
    }
    if !k.objects.contains_key(x) {
        lemma_read_absent(k, a, x, now);
        lemma_apply_all_empty(a);
    } else {
        lemma_read_sim(k, a, x, now);
        lemma_project_canonical(k.objects[x], now);
        let p = k.objects[x].project(now as nat);
        let k1 = kext::spec_read(k, x, now as nat);
        let reads = abs_state::spec_read_effects(a, ax, now, true);
        let a1 = after_read(a, ax, now);
        assert(k1 == kext::with_objects(k, k.objects.insert(x, p)));
        lemma_id_list_contains(p.callbacks, y);
        if p.state == kernel::PromiseState::Pending || !p.callbacks.contains(y) {
            assert(cb == reads);
        } else {
            // The callback comes off the awaited promise.
            let px = p.remove_callback(y);
            lemma_without_ident(p.callbacks, y);
            let promise2 = abs_state::APromiseObject {
                callbacks: abs_state::spec_without_ident(promise(p).callbacks, ay), ..promise(p) };
            assert(promise(px) == promise2);
            lemma_without_index(p.callbacks, y);
            assert(canonical_promise(px));
            assert(k1.objects.contains_key(x) && k1.objects[x] == p);
            assert(spec_find_object(a1.objects, ax) == Some(object(p)));
            assert(task_opt(px.task) == object(p).task);
            lemma_set_promise(k1.objects, a1.objects, x, px);
            let k2 = kext::with_objects(k1, k1.objects.insert(x, px));
            let a2 = spec_apply_effect(a1, AEffect::SetPromise(ax, promise2));
            lemma_apply_all_push(a, reads, AEffect::SetPromise(ax, promise2));
            let head = reads + seq![AEffect::SetPromise(ax, promise2)];
            assert(head =~= reads.push(AEffect::SetPromise(ax, promise2)));
            assert(a2 == spec_apply_all(a, head));
            assert(doc_related(k2, a2));
            // The awaiter resumes; the Abstract reads it in the pre-state.
            let since = aint::settled_since(promise(p));
            assert(since as nat == kprops::opt_or_zero(p.settled_at));
            let resume = aint::resume_one_semantics(a, ax, ay, now, since);
            assert(cb == head + resume);
            lemma_apply_all_app(a, head, resume);
            assert(k2.objects.contains_key(y) == k.objects.contains_key(y));
            assert(k.objects.contains_key(y) ==> k2.objects[y] == k.objects[y]);
            if !k.objects.contains_key(y) {
                lemma_read_task_sim(k, a, y, now);
                assert(resume =~= Seq::<AEffect>::empty());
                assert(cb =~= head);
                assert(kint::callback_state(k, x, y, now as nat) == k2);
            } else if !k.has_task(y) {
                // A bare promise: the Abstract callback leaves it; the
                // Abstract timeout on it is the kernel's projection.
                lemma_read_task_sim(k, a, y, now);
                let reads_y = abs_state::spec_read_effects(a, ay, now, true);
                lemma_untouched_read(k, a, k2, a2, y, now);
                let q = k.objects[y].project(now as nat);
                let k3 = kext::spec_read(k2, y, now as nat);
                assert(k3 == kext::with_objects(k2, k2.objects.insert(y, q)));
                assert(resume =~= Seq::<AEffect>::empty());
                assert(cb =~= head);
                assert(a_cb == a2);
                lemma_find_via_relation(k, a, k2, a2, y);
                assert(abs_state::spec_read_effects(a2, ay, now, true) == reads_y);
                assert(q.task is None);
                assert(kint::callback_state(k, x, y, now as nat) == k3);
            } else {
                lemma_resume_sim(k, a, k2, a2, x, y, now, since);
                assert(kint::callback_state(k, x, y, now as nat) == resume_state(k2, x, y, now as nat, since as nat));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The listener
// ---------------------------------------------------------------------------

pub proof fn lemma_listener_sim(k: KState, a: AState, x: Chars, addr: Chars, now: u64)
    requires doc_related(k, a), canonical(x),
    ensures doc_related(
        kint::listener_state(k, x, addr, now as nat),
        spec_apply_all(a, aint::listener_semantics(a, listener_req(x, addr), now))),
{
    let ax = ident(x);
    if !k.objects.contains_key(x) {
        lemma_read_absent(k, a, x, now);
        lemma_apply_all_empty(a);
    } else {
        lemma_read_sim(k, a, x, now);
        lemma_project_canonical(k.objects[x], now);
        let p = k.objects[x].project(now as nat);
        let k1 = kext::spec_read(k, x, now as nat);
        let reads = abs_state::spec_read_effects(a, ax, now, true);
        let a1 = after_read(a, ax, now);
        lemma_text_list_contains(p.listeners, addr);
        if p.state == kernel::PromiseState::Pending || !p.listeners.contains(addr) {
        } else {
            let q = p.remove_listener(addr);
            lemma_without_text(p.listeners, addr);
            let promise2 = abs_state::APromiseObject {
                listeners: abs_state::spec_without_text(promise(p).listeners, text(addr)), ..promise(p) };
            assert(promise(q) == promise2);
            assert(canonical_promise(q));
            assert(k1.objects.contains_key(x) && k1.objects[x] == p);
            assert(spec_find_object(a1.objects, ax) == Some(object(p)));
            assert(task_opt(q.task) == object(p).task);
            lemma_set_promise(k1.objects, a1.objects, x, q);
            let a2 = spec_apply_effect(a1, AEffect::SetPromise(ax, promise2));
            lemma_apply_all_push(a, reads, AEffect::SetPromise(ax, promise2));
            let head = reads + seq![AEffect::SetPromise(ax, promise2)];
            assert(head =~= reads.push(AEffect::SetPromise(ax, promise2)));
            let message = abs_state::AMessage {
                kind: abs_state::MessageKind::Unblock, task_id: None, version: 0,
                promise: Some(aint::internal_promise_record(promise(p), ax)) };
            assert(head + seq![AEffect::SetMessage(text(addr), message)] =~= head.push(AEffect::SetMessage(text(addr), message)));
            lemma_apply_all_push(a, head, AEffect::SetMessage(text(addr), message));
            let k2 = kint::listener_state(k, x, addr, now as nat);
            let k1b = KState { objects: k1.objects.insert(x, q), ..k1 };
            assert(k2.objects == k1b.objects);
            assert(k2.schedules == k1b.schedules);
            assert(doc_related(k1b, a2));
            lemma_message_effect(k1b, a2, text(addr), message);
        }
    }
}

} // verus!
