//! The five Promise handlers, simulated.
//!
//! For each kernel handler `kext::spec_promise_*` and the Abstract action
//! `spec_promise_*_action` with `materialize = true`: from related states and
//! a request within the kernel's domain, the handler and the action give the
//! same response under the mapping, and leave related states.
//!
//! The domain is the kernel's: ids are canonical, a create is not a targeted
//! timer (the wire strips the target before the kernel sees it) and its
//! deadline is within `MAX_TIME`.

use vstd::prelude::*;

use echod_abstract::promise_spec as pspec;
use echod_abstract::state as abs_state;
use echod_abstract::state::{AEffect, AObject, AState, spec_apply_all, spec_apply_effect, spec_find_object};
use echod_abstract::types as abs;
use echod_kernel::external as kext;
use echod_kernel::object as kobject;
use echod_kernel::store::AState as KState;
use echod_kernel::tags as ktags;
use echod_kernel::types as kernel;
use echod_kernel::types::{APromise, ATask};

use crate::bridge::*;
use crate::read_sim::*;
use crate::relation::*;
use crate::*;

verus! {

// ---------------------------------------------------------------------------
// Requests under the mapping
// ---------------------------------------------------------------------------

pub open spec fn promise_get_req(r: kernel::APromiseGetReq) -> abs::APromiseGetReq {
    abs::APromiseGetReq { id: ident(r.id) }
}

pub open spec fn promise_create_req(r: kernel::APromiseCreateReq) -> abs::APromiseCreateReq {
    abs::APromiseCreateReq { id: ident(r.id), timeout_at: r.timeout_at, param: value(r.param), tags: tags(r.tags) }
}

pub open spec fn promise_settle_req(r: kernel::APromiseSettleReq) -> abs::APromiseSettleReq {
    abs::APromiseSettleReq { id: ident(r.id), state: promise_state(r.state), value: value(r.value) }
}

pub open spec fn promise_register_callback_req(r: kernel::APromiseRegisterCallbackReq) -> abs::APromiseRegisterCallbackReq {
    abs::APromiseRegisterCallbackReq { awaited: ident(r.awaited), awaiter: ident(r.awaiter) }
}

pub open spec fn promise_register_listener_req(r: kernel::APromiseRegisterListenerReq) -> abs::APromiseRegisterListenerReq {
    abs::APromiseRegisterListenerReq { awaited: ident(r.awaited), address: text(r.address) }
}

/// What the kernel accepts of a create: the wire has stripped a timer's
/// target, and the deadline is a time.
pub open spec fn create_in_domain(r: kernel::APromiseCreateReq) -> bool {
    &&& canonical(r.id)
    &&& !ktags::timer_targeted(r.tags)
    &&& r.timeout_at <= kernel::MAX_TIME
}

// ---------------------------------------------------------------------------
// Pieces
// ---------------------------------------------------------------------------

/// First match in a related state is determined by the kernel map; two
/// related pairs that agree at `y` find the same object at `ident(y)`.
pub proof fn lemma_find_via_relation(k: KState, a: AState, k2: KState, a2: AState, y: Chars)
    requires
        doc_related(k, a),
        doc_related(k2, a2),
        canonical(y),
        k.objects.contains_key(y) == k2.objects.contains_key(y),
        k.objects.contains_key(y) ==> k.objects[y] == k2.objects[y],
    ensures
        spec_find_object(a2.objects, ident(y)) == spec_find_object(a.objects, ident(y)),
{
    lemma_related_contains(k.objects, a.objects, y);
    lemma_related_contains(k2.objects, a2.objects, y);
}

/// Reading `y` after reading `x != y` reads what reading `y` first would.
pub proof fn lemma_read_other(k: KState, a: AState, x: Chars, y: Chars, now: u64)
    requires
        doc_related(k, a),
        k.objects.contains_key(x),
        canonical(y),
        x != y,
    ensures
        abs_state::spec_read_object(after_read(a, ident(x), now), ident(y), now) == abs_state::spec_read_object(a, ident(y), now),
        abs_state::spec_read_effects(after_read(a, ident(x), now), ident(y), now, true) == abs_state::spec_read_effects(a, ident(y), now, true),
{
    lemma_read_sim(k, a, x, now);
    let k1 = kext::spec_read(k, x, now as nat);
    let a1 = after_read(a, ident(x), now);
    lemma_find_via_relation(k, a, k1, a1, y);
}

/// The kernel's born object and the Abstract's agree, face and task.
pub proof fn lemma_create_shape(req: kernel::APromiseCreateReq, now: u64)
    ensures
        promise(kobject::spec_create(req, now as nat)) == abs_state::spec_created_promise(promise_create_req(req), now),
        task_opt(kobject::spec_create(req, now as nat).task)
            == abs_state::spec_created_task(abs_state::spec_created_promise(promise_create_req(req), now), now),
        kobject::spec_create(req, now as nat).id == req.id,
{
    let p = kobject::spec_create(req, now as nat);
    let areq = promise_create_req(req);
    let ap = abs_state::spec_created_promise(areq, now);
    lemma_is_timer(req.tags);
    lemma_otype(req.tags);
    assert(tags(Seq::<(Chars, Chars)>::empty()) =~= Seq::<abs::ATag>::empty());
    assert(value(kernel::AValue::empty()) == abs::AValue { headers: Seq::empty(), data: None });
    assert(promise(p) == ap);
    assert(id_list(Seq::<Chars>::empty()) =~= Seq::<abs::AIdent>::empty());
    if ktags::otype(req.tags) == ktags::OType::Runnable && req.timeout_at > now {
        lemma_first_dispatch(req.tags, now);
    }
}

/// Adding a callback commutes with the mapping.
pub proof fn lemma_add_callback(p: APromise, y: Chars)
    requires canonical_promise(p), canonical(y),
    ensures promise(p.add_callback(y)) == abs_state::spec_add_callback(promise(p), ident(y)),
{
    lemma_id_list_contains(p.callbacks, y);
    lemma_id_list_push(p.callbacks, y);
}

/// Adding a listener commutes with the mapping.
pub proof fn lemma_add_listener(p: APromise, addr: Chars)
    ensures promise(p.add_listener(addr)) == abs_state::spec_add_listener(promise(p), text(addr)),
{
    lemma_text_list_contains(p.listeners, addr);
    lemma_text_list_push(p.listeners, addr);
}

/// The kernel's `settle` of a projected row, and the Abstract settled effects
/// committed on a related state.
pub proof fn lemma_settle_move(k: KState, a: AState, id: Chars, state: kernel::PromiseState, v: kernel::AValue, now: u64)
    requires
        doc_related(k, a),
        k.objects.contains_key(id),
        state.spec_settable(),
    ensures ({
        let q = k.objects[id];
        let promise2 = abs_state::APromiseObject { state: promise_state(state), value: value(v), settled_at: Some(now), ..promise(q) };
        let effects = abs_state::spec_set_settled_effects(object(q), promise2);
        &&& doc_related(
            KState { objects: k.objects.insert(id, q.settle(state, v, now as nat)), ..k },
            spec_apply_all(a, effects))
        &&& promise(q.settle(state, v, now as nat)) == promise2
    }),
{
    let aid = ident(id);
    let q = k.objects[id];
    let promise2 = abs_state::APromiseObject { state: promise_state(state), value: value(v), settled_at: Some(now), ..promise(q) };
    let effects = abs_state::spec_set_settled_effects(object(q), promise2);
    let settled = q.settle(state, v, now as nat);
    assert(spec_find_object(a.objects, aid) == Some(object(q)));

    let p1 = APromise { state, value: v, settled_at: Some(now), task: q.task, ..q };
    assert(promise(p1) == promise2);
    assert(canonical_promise(p1));
    assert(task_opt(p1.task) == object(q).task);
    lemma_set_promise(k.objects, a.objects, id, p1);
    let a1 = spec_apply_effect(a, AEffect::SetPromise(aid, promise2));
    let k1 = k.objects.insert(id, p1);
    assert(objects_related(k1, a1.objects));
    let first = seq![AEffect::SetPromise(aid, promise2)];
    lemma_apply_all_one(a, AEffect::SetPromise(aid, promise2));

    assert(promise2.state != abs::PromiseState::Pending);
    match q.task {
        Some(t) if t.state != kernel::TaskState::Fulfilled => {
            assert(object(q).task == Some(task(t)));
            assert(task(t).state != abs::TaskState::Fulfilled);
            assert(effects == first.push(AEffect::SetTask(aid, abs_state::spec_fulfill_task(task(t)))));
            lemma_apply_all_push(a, first, AEffect::SetTask(aid, abs_state::spec_fulfill_task(task(t))));
            lemma_fulfill_task(t);
            assert(canonical_task(t.fulfill()));
            lemma_set_task(k1, a1.objects, id, t.fulfill());
            assert(k1[id].with_task(t.fulfill()) == settled);
            assert(k1.insert(id, settled) =~= k.objects.insert(id, settled));
        }
        _ => {
            assert(effects == first);
            assert(p1 == settled);
        }
    }
}

// ---------------------------------------------------------------------------
// The handlers
// ---------------------------------------------------------------------------

pub proof fn lemma_promise_get_sim(k: KState, a: AState, req: kernel::APromiseGetReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_promise_get(k, req, now as nat);
        let r = pspec::spec_promise_get_action(a, promise_get_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& promise_res(res) == r.response
    }),
{
    let id = req.id;
    if k.objects.contains_key(id) {
        lemma_read_sim(k, a, id, now);
        let q = k.objects[id].project(now as nat);
        lemma_project_canonical(k.objects[id], now);
        lemma_promise_record(q);
    } else {
        lemma_read_absent(k, a, id, now);
    }
}

pub proof fn lemma_promise_create_sim(k: KState, a: AState, req: kernel::APromiseCreateReq, now: u64)
    requires
        doc_related(k, a),
        create_in_domain(req),
    ensures ({
        let (k2, res) = kext::spec_promise_create(k, req, now as nat);
        let r = pspec::spec_promise_create_action(a, promise_create_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& promise_res(res) == r.response
    }),
{
    let id = req.id;
    let aid = ident(id);
    let areq = promise_create_req(req);
    lemma_strip_identity(req.tags);
    assert(pspec::spec_normalize_create(areq) == areq);
    lemma_timer_targeted(req.tags);
    assert(!pspec::spec_tags_timer_targeted(areq.tags));
    if k.objects.contains_key(id) {
        lemma_read_sim(k, a, id, now);
        let q = k.objects[id].project(now as nat);
        lemma_project_canonical(k.objects[id], now);
        lemma_promise_record(q);
    } else {
        lemma_read_absent(k, a, id, now);
        let made = abs_state::spec_create_promise_effects(areq, now);
        assert(Seq::<AEffect>::empty() + made =~= made);
        lemma_create_absent(k, a, req, now);
        lemma_create_shape(req, now);
        lemma_promise_record(kobject::spec_create(req, now as nat));
    }
}

/// A promise born at a fresh id: the kernel inserts `spec_create`, the
/// Abstract commits `spec_create_promise_effects`.
pub proof fn lemma_create_absent(k: KState, a: AState, req: kernel::APromiseCreateReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
        !k.objects.contains_key(req.id),
    ensures
        doc_related(
            KState { objects: k.objects.insert(req.id, kobject::spec_create(req, now as nat)), ..k },
            spec_apply_all(a, abs_state::spec_create_promise_effects(promise_create_req(req), now))),
{
    let id = req.id;
    let aid = ident(id);
    let areq = promise_create_req(req);
    let p = kobject::spec_create(req, now as nat);
    lemma_create_shape(req, now);
    let ap = abs_state::spec_created_promise(areq, now);
    let made = abs_state::spec_create_promise_effects(areq, now);
    let base = seq![AEffect::SetPromise(aid, ap)];
    lemma_apply_all_one(a, AEffect::SetPromise(aid, ap));
    assert(id_list(Seq::<Chars>::empty()) =~= Seq::<abs::AIdent>::empty());
    assert(canonical_list(Seq::<Chars>::empty()));
    lemma_related_contains(k.objects, a.objects, id);
    let p0 = APromise { task: None, ..p };
    assert(canonical_promise(p0));
    assert(promise(p0) == ap);
    assert(task_opt(p0.task) == None::<abs_state::ATaskObject>);
    lemma_set_promise(k.objects, a.objects, id, p0);
    let a1 = spec_apply_effect(a, AEffect::SetPromise(aid, ap));
    let k1 = k.objects.insert(id, p0);
    assert(objects_related(k1, a1.objects));
    match p.task {
        Some(t) => {
            assert(abs_state::spec_created_task(ap, now) == Some(task(t)));
            assert(made == base.push(AEffect::SetTask(aid, task(t))));
            lemma_apply_all_push(a, base, AEffect::SetTask(aid, task(t)));
            assert(canonical_task(t));
            lemma_set_task(k1, a1.objects, id, t);
            assert(k1[id].with_task(t) == p);
            assert(k1.insert(id, p) =~= k.objects.insert(id, p));
        }
        None => {
            assert(abs_state::spec_created_task(ap, now) is None);
            assert(made == base);
            assert(p0 == p);
        }
    }
}

pub proof fn lemma_promise_settle_sim(k: KState, a: AState, req: kernel::APromiseSettleReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_promise_settle(k, req, now as nat);
        let r = pspec::spec_promise_settle_action(a, promise_settle_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& promise_res(res) == r.response
    }),
{
    let id = req.id;
    let aid = ident(id);
    assert(pspec::spec_settable(promise_state(req.state)) == req.state.spec_settable());
    if !req.state.spec_settable() {
    } else if !k.objects.contains_key(id) {
        lemma_read_absent(k, a, id, now);
    } else {
        lemma_read_sim(k, a, id, now);
        let kb = kext::spec_read(k, id, now as nat);
        let ab = after_read(a, aid, now);
        let q = k.objects[id].project(now as nat);
        lemma_project_canonical(k.objects[id], now);
        assert(kb.objects[id] == q);
        if q.state == kernel::PromiseState::Pending {
            lemma_settle_move(kb, ab, id, req.state, req.value, now);
            let promise2 = abs_state::APromiseObject { state: promise_state(req.state), value: value(req.value), settled_at: Some(now), ..promise(q) };
            let reads = abs_state::spec_read_effects(a, aid, now, true);
            let effects = abs_state::spec_set_settled_effects(object(q), promise2);
            lemma_apply_all_app(a, reads, effects);
            let settled = q.settle(req.state, req.value, now as nat);
            lemma_promise_record(settled);
        } else {
            lemma_promise_record(q);
        }
    }
}

pub proof fn lemma_promise_register_callback_sim(k: KState, a: AState, req: kernel::APromiseRegisterCallbackReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.awaited),
        canonical(req.awaiter),
    ensures ({
        let (k2, res) = kext::spec_promise_register_callback(k, req, now as nat);
        let r = pspec::spec_promise_register_callback_action(a, promise_register_callback_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& promise_res(res) == r.response
    }),
{
    let x = req.awaited;
    let y = req.awaiter;
    let ax = ident(x);
    let ay = ident(y);
    lemma_same_origin(x, y);
    if ax == ay {
        lemma_ident_injective(x, y);
    }
    if x == y || !kernel::same_origin_spec(x, y) {
    } else if !k.objects.contains_key(x) {
        lemma_read_absent(k, a, x, now);
    } else {
        lemma_read_sim(k, a, x, now);
        let k1 = kext::spec_read(k, x, now as nat);
        let a1 = after_read(a, ax, now);
        let qx = k.objects[x].project(now as nat);
        lemma_project_canonical(k.objects[x], now);
        assert(k1.objects[x] == qx);
        let reads_x = abs_state::spec_read_effects(a, ax, now, true);
        lemma_read_other(k, a, x, y, now);
        if !k1.objects.contains_key(y) {
            lemma_read_absent(k, a, y, now);
            assert(reads_x + Seq::<AEffect>::empty() =~= reads_x);
        } else {
            lemma_read_sim(k1, a1, y, now);
            let k2 = kext::spec_read(k1, y, now as nat);
            let a2 = after_read(a1, ay, now);
            let qy = k1.objects[y].project(now as nat);
            lemma_project_canonical(k1.objects[y], now);
            assert(k2.objects[y] == qy);
            assert(k2.objects[x] == qx);
            let reads_y = abs_state::spec_read_effects(a, ay, now, true);
            let reads = reads_x + reads_y;
            lemma_apply_all_app(a, reads_x, reads_y);
            assert(a2 == spec_apply_all(a, reads));
            lemma_otype(qx.tags);
            lemma_otype(qy.tags);
            if ktags::otype(qy.tags) != ktags::OType::Runnable || !ktags::otype(qx.tags).awaitable() {
            } else {
                lemma_promise_record(qx);
                if qx.state == kernel::PromiseState::Pending && qy.state == kernel::PromiseState::Pending {
                    let px = qx.add_callback(y);
                    lemma_add_callback(qx, y);
                    assert(canonical_promise(px));
                    assert(task_opt(px.task) == object(qx).task);
                    lemma_set_promise(k2.objects, a2.objects, x, px);
                    lemma_apply_all_push(a, reads, AEffect::SetPromise(ax, abs_state::spec_add_callback(promise(qx), ay)));
                    assert(px.to_record() == qx.to_record());
                }
            }
        }
    }
}

pub proof fn lemma_promise_register_listener_sim(k: KState, a: AState, req: kernel::APromiseRegisterListenerReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.awaited),
    ensures ({
        let (k2, res) = kext::spec_promise_register_listener(k, req, now as nat);
        let r = pspec::spec_promise_register_listener_action(a, promise_register_listener_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& promise_res(res) == r.response
    }),
{
    let x = req.awaited;
    let ax = ident(x);
    if !k.objects.contains_key(x) {
        lemma_read_absent(k, a, x, now);
    } else {
        lemma_read_sim(k, a, x, now);
        let kb = kext::spec_read(k, x, now as nat);
        let ab = after_read(a, ax, now);
        let q = k.objects[x].project(now as nat);
        lemma_project_canonical(k.objects[x], now);
        assert(kb.objects[x] == q);
        let reads = abs_state::spec_read_effects(a, ax, now, true);
        lemma_otype(q.tags);
        if !ktags::otype(q.tags).awaitable() {
        } else {
            lemma_promise_record(q);
            if q.state == kernel::PromiseState::Pending {
                let px = q.add_listener(req.address);
                lemma_add_listener(q, req.address);
                assert(canonical_promise(px));
                assert(task_opt(px.task) == object(q).task);
                lemma_set_promise(kb.objects, ab.objects, x, px);
                lemma_apply_all_push(a, reads, AEffect::SetPromise(ax, abs_state::spec_add_listener(promise(q), text(req.address))));
                assert(px.to_record() == q.to_record());
            }
        }
    }
}

} // verus!
