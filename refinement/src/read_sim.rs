//! Projection and the materialized read, simulated.
//!
//! The kernel's `spec_read` projects an object at `now` and stores the
//! projection. The Abstract read with `materialize = true` emits the writes
//! the projection moved (`spec_read_effects`). Committing those writes to a
//! related Abstract state leaves it related to the kernel's stored
//! projection, and the object both return is the same.

use vstd::prelude::*;

use echod_abstract::state as abs_state;
use echod_abstract::state::{AEffect, AObject, AState, spec_apply_all, spec_apply_effect, spec_find_object};
use echod_abstract::types as abs;
use echod_kernel::external as kext;
use echod_kernel::store::AState as KState;
use echod_kernel::types as kernel;
use echod_kernel::types::{APromise, ATask};

use crate::bridge::*;
use crate::relation::*;
use crate::*;

verus! {

// ---------------------------------------------------------------------------
// Committing effects, in pieces
// ---------------------------------------------------------------------------

pub proof fn lemma_apply_all_app(a: AState, s: Seq<AEffect>, t: Seq<AEffect>)
    ensures spec_apply_all(a, s + t) == spec_apply_all(spec_apply_all(a, s), t),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s + t =~= t);
    } else {
        assert((s + t)[0] == s[0]);
        assert((s + t).drop_first() =~= s.drop_first() + t);
        lemma_apply_all_app(spec_apply_effect(a, s[0]), s.drop_first(), t);
    }
}

pub proof fn lemma_apply_all_one(a: AState, e: AEffect)
    ensures spec_apply_all(a, seq![e]) == spec_apply_effect(a, e),
{
    let s = seq![e];
    assert(s.len() == 1 && s[0] == e);
    assert(s.drop_first() =~= Seq::<AEffect>::empty());
    assert(spec_apply_all(a, s) == spec_apply_all(spec_apply_effect(a, e), s.drop_first()));
    lemma_apply_all_empty(spec_apply_effect(a, e));
}

pub proof fn lemma_apply_all_push(a: AState, s: Seq<AEffect>, e: AEffect)
    ensures spec_apply_all(a, s.push(e)) == spec_apply_effect(spec_apply_all(a, s), e),
{
    assert(s.push(e) =~= s + seq![e]);
    lemma_apply_all_app(a, s, seq![e]);
    lemma_apply_all_one(spec_apply_all(a, s), e);
}

pub proof fn lemma_apply_all_empty(a: AState)
    ensures spec_apply_all(a, Seq::<AEffect>::empty()) == a,
{
}

// ---------------------------------------------------------------------------
// Projection commutes with the mapping
// ---------------------------------------------------------------------------

pub proof fn lemma_project_promise(p: APromise, now: u64)
    ensures promise(p.project_promise(now as nat)) == abs_state::spec_project_promise(promise(p), now),
{
    lemma_is_timer(p.tags);
}

pub proof fn lemma_fulfill_task(t: ATask)
    ensures task(t.fulfill()) == abs_state::spec_fulfill_task(task(t)),
{
    assert(id_list(Seq::<Chars>::empty()) =~= Seq::<abs::AIdent>::empty());
}

pub proof fn lemma_project_object(p: APromise, now: u64)
    ensures object(p.project(now as nat)) == abs_state::spec_project_object(object(p), now),
{
    lemma_project_promise(p, now);
    match p.task {
        Some(t) => { lemma_fulfill_task(t); }
        None => {}
    }
}

/// Projection keeps the id and the doors.
pub proof fn lemma_project_canonical(p: APromise, now: u64)
    requires canonical_promise(p),
    ensures canonical_promise(p.project(now as nat)), p.project(now as nat).id == p.id,
{
    match p.task {
        Some(t) => {
            assert(canonical_list(t.fulfill().resumes));
        }
        None => {}
    }
}

// ---------------------------------------------------------------------------
// Records and responses
// ---------------------------------------------------------------------------

pub open spec fn promise_record(r: kernel::APromiseRecord) -> abs::APromiseRecord {
    abs::APromiseRecord {
        id: ident(r.id),
        state: promise_state(r.state),
        param: value(r.param),
        value: value(r.value),
        tags: tags(r.tags),
        timeout_at: r.timeout_at,
        created_at: r.created_at,
        settled_at: r.settled_at,
    }
}

pub open spec fn opt_promise_record(r: Option<kernel::APromiseRecord>) -> Option<abs::APromiseRecord> {
    match r {
        Some(x) => Some(promise_record(x)),
        None => None,
    }
}

pub open spec fn promise_res(r: kernel::APromiseRes) -> abs::APromiseRes {
    abs::APromiseRes { status: r.status, promise: opt_promise_record(r.promise) }
}

pub open spec fn task_record(r: kernel::ATaskRecord) -> abs::ATaskRecord {
    abs::ATaskRecord {
        id: ident(r.id),
        state: task_state(r.state),
        version: r.version,
        resumes: r.resumes,
        ttl: r.ttl,
        pid: match r.pid { Some(x) => Some(text(x)), None => None },
    }
}

pub open spec fn opt_task_record(r: Option<kernel::ATaskRecord>) -> Option<abs::ATaskRecord> {
    match r {
        Some(x) => Some(task_record(x)),
        None => None,
    }
}

pub open spec fn status_res(r: kernel::AStatusRes) -> abs::AStatusRes {
    abs::AStatusRes { status: r.status }
}

pub open spec fn schedule_res(r: kernel::AScheduleRes) -> abs::AScheduleRes {
    abs::AScheduleRes {
        status: r.status,
        schedule: match r.schedule { Some(c) => Some(schedule(c)), None => None },
    }
}

pub open spec fn schedule_delete_res(r: kernel::AStatusRes) -> abs::AScheduleDeleteRes {
    abs::AScheduleDeleteRes { status: r.status }
}

pub open spec fn task_get_res(r: kernel::ATaskGetRes) -> abs::ATaskGetRes {
    abs::ATaskGetRes { status: r.status, task: opt_task_record(r.task) }
}

pub open spec fn task_claim_res(r: kernel::ATaskClaimRes) -> abs::ATaskClaimRes {
    abs::ATaskClaimRes {
        status: r.status,
        task: opt_task_record(r.task),
        promise: opt_promise_record(r.promise),
        preload: Seq::empty(),
    }
}

pub open spec fn task_fulfill_res(r: kernel::APromiseRes) -> abs::ATaskFulfillRes {
    abs::ATaskFulfillRes { status: r.status, promise: opt_promise_record(r.promise) }
}

pub open spec fn task_suspend_res(r: kernel::AStatusRes) -> abs::ATaskSuspendRes {
    abs::ATaskSuspendRes { status: r.status, preload: Seq::empty() }
}

pub open spec fn task_fence_res(r: kernel::ATaskFenceRes) -> abs::ATaskFenceRes {
    abs::ATaskFenceRes {
        status: r.status,
        action: match r.action {
            Some(kernel::ATaskFenceInnerRes::Create(x)) => Some(abs::ATaskFenceInnerRes::Create(promise_res(x))),
            Some(kernel::ATaskFenceInnerRes::Settle(x)) => Some(abs::ATaskFenceInnerRes::Settle(promise_res(x))),
            None => None,
        },
        preload: Seq::empty(),
    }
}

pub proof fn lemma_promise_record(p: APromise)
    ensures echod_abstract::promise_spec::spec_promise_record(promise(p), ident(p.id)) == promise_record(p.to_record()),
{
}

pub proof fn lemma_task_record(t: ATask, id: Chars)
    requires t.resumes.len() <= u64::MAX,
    ensures echod_abstract::task_spec::spec_task_record(task(t), ident(id)) == task_record(t.to_record(id)),
{
    lemma_id_list_index(t.resumes);
    assert(id_list(t.resumes).len() == t.resumes.len());
}

// ---------------------------------------------------------------------------
// The materialized read
// ---------------------------------------------------------------------------

/// The Abstract state after the read's effects on `id`.
pub open spec fn after_read(a: AState, aid: abs::AIdent, now: u64) -> AState {
    spec_apply_all(a, abs_state::spec_read_effects(a, aid, now, true))
}

/// Reading an object the kernel has: the Abstract read finds the same
/// projection, and committing its materialized effects keeps the relation
/// with the kernel's stored projection.
pub proof fn lemma_read_sim(k: KState, a: AState, id: Chars, now: u64)
    requires
        doc_related(k, a),
        k.objects.contains_key(id),
    ensures
        abs_state::spec_read_object(a, ident(id), now) == Some(object(k.objects[id].project(now as nat))),
        doc_related(kext::spec_read(k, id, now as nat), after_read(a, ident(id), now)),
{
    let aid = ident(id);
    let p = k.objects[id];
    let old = object(p);
    assert(spec_find_object(a.objects, aid) == Some(old));
    lemma_project_object(p, now);
    lemma_project_canonical(p, now);
    let q = p.project(now as nat);
    let projected = object(q);
    assert(abs_state::spec_project_object(old, now) == projected);
    let k2 = kext::spec_read(k, id, now as nat);
    assert(k2.objects == k.objects.insert(id, q));
    assert(k2.schedules == k.schedules);

    let promise_effects: Seq<AEffect> = if projected.promise.state != old.promise.state {
        seq![AEffect::SetPromise(aid, projected.promise)]
    } else {
        Seq::empty()
    };
    let task_effects: Seq<AEffect> = match (old.task, projected.task) {
        (Some(x), Some(y)) if x.state != y.state => seq![AEffect::SetTask(aid, y)],
        _ => Seq::empty(),
    };
    assert(abs_state::spec_read_effects(a, aid, now, true) == promise_effects + task_effects);
    lemma_apply_all_app(a, promise_effects, task_effects);
    let mid = spec_apply_all(a, promise_effects);

    // The promise face moved exactly when its state did; the task likewise.
    let promise_moved = projected.promise.state != old.promise.state;
    let task_moved = match (old.task, projected.task) {
        (Some(x), Some(y)) => x.state != y.state,
        _ => false,
    };
    if !promise_moved {
        assert(q.state == p.state);
        assert(q.settled_at == p.settled_at);
    }
    if !task_moved {
        assert(q.task == p.task);
    }

    // The kernel row with the promise face projected and the task as it was.
    let p_mid = APromise { task: p.task, ..q };
    assert(p_mid.id == id);
    assert(canonical_promise(p_mid));

    if promise_moved {
        lemma_apply_all_one(a, AEffect::SetPromise(aid, projected.promise));
        assert(mid == spec_apply_effect(a, AEffect::SetPromise(aid, projected.promise)));
        assert(task_opt(p_mid.task) == old.task);
        assert(promise(p_mid) == projected.promise);
        lemma_set_promise(k.objects, a.objects, id, p_mid);
        assert(mid.objects == seq![AObject { id: aid, promise: projected.promise, task: old.task }]
            + abs_state::spec_without_object(a.objects, aid));
        assert(objects_related(k.objects.insert(id, p_mid), mid.objects));
        assert(mid.schedules == a.schedules);
    } else {
        assert(mid == a);
        assert(p_mid == p);
        assert(k.objects.insert(id, p_mid) =~= k.objects);
        assert(objects_related(k.objects.insert(id, p_mid), mid.objects));
    }
    let k_mid = k.objects.insert(id, p_mid);
    assert(k_mid.contains_key(id) && k_mid[id] == p_mid);

    if task_moved {
        let t2 = q.task.unwrap();
        assert(projected.task == Some(task(t2)));
        assert(canonical_task(t2));
        lemma_apply_all_one(mid, AEffect::SetTask(aid, task(t2)));
        lemma_set_task(k_mid, mid.objects, id, t2);
        assert(p_mid.with_task(t2) == q);
        assert(k_mid.insert(id, q) =~= k.objects.insert(id, q));
        assert(objects_related(k.objects.insert(id, q), after_read(a, aid, now).objects));
    } else {
        assert(after_read(a, aid, now) == mid);
        assert(k_mid =~= k.objects.insert(id, q));
    }
}

/// Reading an object the kernel lacks: nothing is found, nothing is written.
pub proof fn lemma_read_absent(k: KState, a: AState, id: Chars, now: u64)
    requires
        doc_related(k, a),
        canonical(id),
        !k.objects.contains_key(id),
    ensures
        abs_state::spec_read_object(a, ident(id), now) is None,
        abs_state::spec_read_effects(a, ident(id), now, true) == Seq::<AEffect>::empty(),
        after_read(a, ident(id), now) == a,
{
    lemma_related_contains(k.objects, a.objects, id);
}

/// `readTaskObject`: as the read, for an object with a task.
pub proof fn lemma_read_task_sim(k: KState, a: AState, id: Chars, now: u64)
    requires
        doc_related(k, a),
        canonical(id),
    ensures
        k.has_task(id) ==> (
            abs_state::spec_read_task_object(a, ident(id), now) == Some(object(k.objects[id].project(now as nat)))
            && abs_state::spec_read_task_effects(a, ident(id), now, true) == abs_state::spec_read_effects(a, ident(id), now, true)
            && doc_related(kext::spec_read_task(k, id, now as nat), after_read(a, ident(id), now))
        ),
        !k.has_task(id) ==> (
            abs_state::spec_read_task_object(a, ident(id), now) is None
            && abs_state::spec_read_task_effects(a, ident(id), now, true) == Seq::<AEffect>::empty()
            && kext::spec_read_task(k, id, now as nat) == k
        ),
{
    let aid = ident(id);
    if k.objects.contains_key(id) {
        assert(spec_find_object(a.objects, aid) == Some(object(k.objects[id])));
        if k.has_task(id) {
            lemma_read_sim(k, a, id, now);
        } else {
            assert(k.objects[id].task is None);
        }
    } else {
        lemma_read_absent(k, a, id, now);
    }
}

} // verus!
