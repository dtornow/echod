//! Locality: a kernel step on one document is the same step on the bucket.
//!
//! The bucket holds many documents; the Abstract is one state. To run the
//! Abstract beside the bucket, a kernel step on a document has to be a step
//! on the union of the documents. It is, because every kernel function reads
//! and writes only the ids its request names and the ids those objects name
//! (callbacks), all of one origin: a request's ids are validated to one
//! origin, and the catalogue keeps every callback in its promise's origin.
//!
//! `gobj(k, r, c)` is the document `k`'s objects beside the rest of the
//! bucket's objects `r`, over schedules `c`; `glue(k, r)` is the same with
//! the schedules joined too. `inside_obj`/`outside_obj` say which ids each
//! side may hold. Each lemma says a kernel function on the glue is the
//! function on `k`, glued back — an equality, outbox included, since the
//! glue carries `k`'s outbox and every outbox entry a step writes is read
//! off objects the two sides share — and that it keeps `k` inside its ids.

use vstd::prelude::*;

use echod_kernel::external as kext;
use echod_kernel::internal as kint;
use echod_kernel::steps as ksteps;
use echod_kernel::store::AState as KState;
use echod_kernel::types as kernel;
use echod_kernel::types::{AOccurrence, APromise, ARequest, ASchedule, ATaskRef, APromiseRegisterCallbackReq};

use crate::sweep_sim::not_self;
use crate::*;

verus! {

pub type Ids = spec_fn(Chars) -> bool;

/// A document's objects beside the rest of the bucket's, over schedules `c`.
pub open spec fn gobj(k: KState, r: KState, c: Map<Chars, ASchedule>) -> KState {
    KState {
        objects: k.objects.union_prefer_right(r.objects),
        schedules: c,
        outbox: k.outbox,
    }
}

/// A document beside the rest of the bucket.
pub open spec fn glue(k: KState, r: KState) -> KState {
    gobj(k, r, k.schedules.union_prefer_right(r.schedules))
}

/// Every object id of `k` is in `f`.
pub open spec fn inside_obj(k: KState, f: Ids) -> bool {
    forall|id: Chars| #[trigger] k.objects.contains_key(id) ==> f(id)
}

/// No object id of `r` is in `f`.
pub open spec fn outside_obj(r: KState, f: Ids) -> bool {
    forall|id: Chars| #[trigger] r.objects.contains_key(id) ==> !f(id)
}

/// Every schedule id of `k` is in `g`.
pub open spec fn inside_sch(k: KState, g: Ids) -> bool {
    forall|sid: Chars| #[trigger] k.schedules.contains_key(sid) ==> g(sid)
}

/// No schedule id of `r` is in `g`.
pub open spec fn outside_sch(r: KState, g: Ids) -> bool {
    forall|sid: Chars| #[trigger] r.schedules.contains_key(sid) ==> !g(sid)
}

/// Every callback of every object of `k` is in `f`: what the catalogue's
/// `well_formed_promise_callbacks_same_origin` says of a document whose
/// objects are all of one origin.
pub open spec fn callbacks_inside(k: KState, f: Ids) -> bool {
    forall|id: Chars, y: Chars| #[trigger] k.objects.contains_key(id) && #[trigger] k.objects[id].callbacks.contains(y) ==> f(y)
}

/// `f` is closed under the kernel's `same_origin`: what the ids of one
/// origin are.
pub open spec fn origin_closed(f: Ids) -> bool {
    forall|x: Chars, y: Chars| #[trigger] f(x) && #[trigger] kernel::same_origin_spec(x, y) ==> f(y)
}

/// The ids of one origin.
pub open spec fn in_origin(o: Chars) -> Ids {
    |id: Chars| kernel::origin(id) == o
}

pub proof fn lemma_in_origin_closed(o: Chars)
    ensures origin_closed(in_origin(o)),
{
    assert forall|x: Chars, y: Chars| #[trigger] in_origin(o)(x) && #[trigger] kernel::same_origin_spec(x, y) implies in_origin(o)(y) by {
        assert(kernel::origin(x) == o);
        assert(kernel::origin(y) == kernel::origin(x));
    }
}

// ---------------------------------------------------------------------------
// Glue
// ---------------------------------------------------------------------------

pub proof fn lemma_gobj_has(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, id: Chars)
    requires inside_obj(k, f), outside_obj(r, f), f(id),
    ensures
        gobj(k, r, c).objects.contains_key(id) == k.objects.contains_key(id),
        k.objects.contains_key(id) ==> gobj(k, r, c).objects[id] == k.objects[id],
        gobj(k, r, c).has_task(id) == k.has_task(id),
{
}

/// Inserting an id of `f` on the glue is inserting it on the document.
pub proof fn lemma_gobj_insert(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, id: Chars, p: APromise)
    requires inside_obj(k, f), outside_obj(r, f), f(id),
    ensures
        gobj(k, r, c).objects.insert(id, p) == gobj(kext::with_objects(k, k.objects.insert(id, p)), r, c).objects,
        kext::with_objects(gobj(k, r, c), gobj(k, r, c).objects.insert(id, p)) == gobj(kext::with_objects(k, k.objects.insert(id, p)), r, c),
        inside_obj(kext::with_objects(k, k.objects.insert(id, p)), f),
{
    assert(gobj(k, r, c).objects.insert(id, p) =~= gobj(kext::with_objects(k, k.objects.insert(id, p)), r, c).objects);
}

pub proof fn lemma_glue_has_sched(k: KState, r: KState, g: Ids, sid: Chars)
    requires inside_sch(k, g), outside_sch(r, g), g(sid),
    ensures
        glue(k, r).schedules.contains_key(sid) == k.schedules.contains_key(sid),
        k.schedules.contains_key(sid) ==> glue(k, r).schedules[sid] == k.schedules[sid],
{
}

pub proof fn lemma_glue_insert_sched(k: KState, r: KState, g: Ids, sid: Chars, c: ASchedule)
    requires inside_sch(k, g), outside_sch(r, g), g(sid),
    ensures
        (KState { schedules: glue(k, r).schedules.insert(sid, c), ..glue(k, r) }) == glue(KState { schedules: k.schedules.insert(sid, c), ..k }, r),
        inside_sch(KState { schedules: k.schedules.insert(sid, c), ..k }, g),
{
    assert(glue(k, r).schedules.insert(sid, c) =~= glue(KState { schedules: k.schedules.insert(sid, c), ..k }, r).schedules);
}

pub proof fn lemma_glue_remove_sched(k: KState, r: KState, g: Ids, sid: Chars)
    requires inside_sch(k, g), outside_sch(r, g), g(sid),
    ensures
        (KState { schedules: glue(k, r).schedules.remove(sid), ..glue(k, r) }) == glue(KState { schedules: k.schedules.remove(sid), ..k }, r),
        inside_sch(KState { schedules: k.schedules.remove(sid), ..k }, g),
{
    assert(glue(k, r).schedules.remove(sid) =~= glue(KState { schedules: k.schedules.remove(sid), ..k }, r).schedules);
}

/// A step that leaves the schedules alone: its glue over the joined
/// schedules is its `gobj` over them.
pub proof fn lemma_glue_is_gobj(k: KState, k2: KState, r: KState)
    requires k2.schedules == k.schedules,
    ensures glue(k2, r) == gobj(k2, r, k.schedules.union_prefer_right(r.schedules)),
{
}

// ---------------------------------------------------------------------------
// Reads
// ---------------------------------------------------------------------------

pub proof fn lemma_read_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, id: Chars, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(id),
    ensures
        kext::spec_read(gobj(k, r, c), id, now) == gobj(kext::spec_read(k, id, now), r, c),
        inside_obj(kext::spec_read(k, id, now), f),
        kext::spec_read(k, id, now).objects.contains_key(id) == k.objects.contains_key(id),
        kext::spec_read(k, id, now).schedules == k.schedules,
        kext::spec_read(k, id, now).has_task(id) == k.has_task(id),
{
    lemma_gobj_has(k, r, c, f, id);
    if k.objects.contains_key(id) {
        lemma_gobj_insert(k, r, c, f, id, k.objects[id].project(now));
    }
}

pub proof fn lemma_read_task_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, id: Chars, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(id),
    ensures
        kext::spec_read_task(gobj(k, r, c), id, now) == gobj(kext::spec_read_task(k, id, now), r, c),
        inside_obj(kext::spec_read_task(k, id, now), f),
        kext::spec_read_task(k, id, now).objects.contains_key(id) == k.objects.contains_key(id),
        kext::spec_read_task(k, id, now).schedules == k.schedules,
        kext::spec_read_task(k, id, now).has_task(id) == k.has_task(id),
{
    lemma_gobj_has(k, r, c, f, id);
    if k.has_task(id) {
        lemma_read_local(k, r, c, f, id, now);
    }
}

// ---------------------------------------------------------------------------
// The promise handlers
// ---------------------------------------------------------------------------

pub proof fn lemma_promise_get_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::APromiseGetReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_promise_get(k, q, now);
        &&& kext::spec_promise_get(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_gobj_has(k, r, c, f, q.id);
    if k.objects.contains_key(q.id) {
        lemma_read_local(k, r, c, f, q.id, now);
        lemma_gobj_has(kext::spec_read(k, q.id, now), r, c, f, q.id);
    }
}

pub proof fn lemma_promise_create_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::APromiseCreateReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_promise_create(k, q, now);
        &&& kext::spec_promise_create(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_gobj_has(k, r, c, f, q.id);
    if echod_kernel::tags::timer_targeted(q.tags) || q.timeout_at > kernel::MAX_TIME {
    } else if k.objects.contains_key(q.id) {
        lemma_read_local(k, r, c, f, q.id, now);
        lemma_gobj_has(kext::spec_read(k, q.id, now), r, c, f, q.id);
    } else {
        lemma_gobj_insert(k, r, c, f, q.id, echod_kernel::object::spec_create(q, now));
    }
}

pub proof fn lemma_promise_settle_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::APromiseSettleReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_promise_settle(k, q, now);
        &&& kext::spec_promise_settle(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_gobj_has(k, r, c, f, q.id);
    if q.state.spec_settable() && k.objects.contains_key(q.id) {
        lemma_read_local(k, r, c, f, q.id, now);
        let kb = kext::spec_read(k, q.id, now);
        lemma_gobj_has(kb, r, c, f, q.id);
        if kb.objects[q.id].state == kernel::PromiseState::Pending {
            lemma_gobj_insert(kb, r, c, f, q.id, kb.objects[q.id].settle(q.state, q.value, now));
            let kc = kext::with_objects(kb, kb.objects.insert(q.id, kb.objects[q.id].settle(q.state, q.value, now)));
            lemma_gobj_has(kc, r, c, f, q.id);
        }
    }
}

pub proof fn lemma_promise_register_callback_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::APromiseRegisterCallbackReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), origin_closed(f), f(q.awaited),
    ensures ({
        let (k2, res) = kext::spec_promise_register_callback(k, q, now);
        &&& kext::spec_promise_register_callback(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    let x = q.awaited;
    let y = q.awaiter;
    lemma_gobj_has(k, r, c, f, x);
    if x == y || !kernel::same_origin_spec(x, y) {
    } else if !k.objects.contains_key(x) {
    } else {
        assert(f(y));
        lemma_read_local(k, r, c, f, x, now);
        let k1 = kext::spec_read(k, x, now);
        lemma_gobj_has(k1, r, c, f, y);
        if k1.objects.contains_key(y) {
            lemma_read_local(k1, r, c, f, y, now);
            let k2 = kext::spec_read(k1, y, now);
            lemma_gobj_has(k2, r, c, f, x);
            lemma_gobj_has(k2, r, c, f, y);
            if k2.objects[y].otype() != echod_kernel::tags::OType::Runnable || !k2.objects[x].otype().awaitable() {
            } else if k2.objects[x].state == kernel::PromiseState::Pending && k2.objects[y].state == kernel::PromiseState::Pending {
                lemma_gobj_insert(k2, r, c, f, x, k2.objects[x].add_callback(y));
                let k3 = kext::with_objects(k2, k2.objects.insert(x, k2.objects[x].add_callback(y)));
                lemma_gobj_has(k3, r, c, f, x);
            }
        }
    }
}

pub proof fn lemma_promise_register_listener_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::APromiseRegisterListenerReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.awaited),
    ensures ({
        let (k2, res) = kext::spec_promise_register_listener(k, q, now);
        &&& kext::spec_promise_register_listener(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    let x = q.awaited;
    lemma_gobj_has(k, r, c, f, x);
    if k.objects.contains_key(x) {
        lemma_read_local(k, r, c, f, x, now);
        let kb = kext::spec_read(k, x, now);
        lemma_gobj_has(kb, r, c, f, x);
        if !kb.objects[x].otype().awaitable() {
        } else if kb.objects[x].state == kernel::PromiseState::Pending {
            lemma_gobj_insert(kb, r, c, f, x, kb.objects[x].add_listener(q.address));
            let kc = kext::with_objects(kb, kb.objects.insert(x, kb.objects[x].add_listener(q.address)));
            lemma_gobj_has(kc, r, c, f, x);
        }
    }
}

// ---------------------------------------------------------------------------
// The schedule handlers
// ---------------------------------------------------------------------------

pub proof fn lemma_schedule_get_local(k: KState, r: KState, g: Ids, q: kernel::AScheduleGetReq, now: nat)
    requires inside_sch(k, g), outside_sch(r, g), g(q.id),
    ensures ({
        let (k2, res) = kext::spec_schedule_get(k, q, now);
        &&& kext::spec_schedule_get(glue(k, r), q, now) == (glue(k2, r), res)
        &&& inside_sch(k2, g)
        &&& k2.objects == k.objects
    }),
{
    lemma_glue_has_sched(k, r, g, q.id);
}

pub proof fn lemma_schedule_create_local(k: KState, r: KState, g: Ids, q: kernel::AScheduleCreateReq, now: nat)
    requires inside_sch(k, g), outside_sch(r, g), g(q.id),
    ensures ({
        let (k2, res) = kext::spec_schedule_create(k, q, now);
        &&& kext::spec_schedule_create(glue(k, r), q, now) == (glue(k2, r), res)
        &&& inside_sch(k2, g)
        &&& k2.objects == k.objects
    }),
{
    lemma_glue_has_sched(k, r, g, q.id);
    if echod_kernel::tags::timer_targeted(q.promise_tags) || q.promise_timeout > kernel::MAX_TIME || q.next_run_at < now {
    } else if k.schedules.contains_key(q.id) {
    } else {
        lemma_glue_insert_sched(k, r, g, q.id, kext::spec_new_schedule(q, now));
    }
}

pub proof fn lemma_schedule_delete_local(k: KState, r: KState, g: Ids, q: kernel::AScheduleDeleteReq, now: nat)
    requires inside_sch(k, g), outside_sch(r, g), g(q.id),
    ensures ({
        let (k2, res) = kext::spec_schedule_delete(k, q, now);
        &&& kext::spec_schedule_delete(glue(k, r), q, now) == (glue(k2, r), res)
        &&& inside_sch(k2, g)
        &&& k2.objects == k.objects
    }),
{
    lemma_glue_has_sched(k, r, g, q.id);
    if k.schedules.contains_key(q.id) {
        lemma_glue_remove_sched(k, r, g, q.id);
    }
}

// ---------------------------------------------------------------------------
// The task handlers on one object
// ---------------------------------------------------------------------------

/// The task handlers all begin the same way: the object read if it has a
/// task. The facts the rest of each handler needs about that read.
proof fn lemma_task_read(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, id: Chars, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(id),
    ensures ({
        let kb = kext::spec_read_task(k, id, now);
        &&& gobj(k, r, c).has_task(id) == k.has_task(id)
        &&& kext::spec_read_task(gobj(k, r, c), id, now) == gobj(kb, r, c)
        &&& inside_obj(kb, f)
        &&& kb.schedules == k.schedules
        &&& gobj(kb, r, c).objects.contains_key(id) == kb.objects.contains_key(id)
        &&& kb.objects.contains_key(id) ==> gobj(kb, r, c).objects[id] == kb.objects[id]
    }),
{
    lemma_gobj_has(k, r, c, f, id);
    lemma_read_task_local(k, r, c, f, id, now);
    lemma_gobj_has(kext::spec_read_task(k, id, now), r, c, f, id);
}

/// The object written back, and read again for the answer.
proof fn lemma_task_write(kb: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, id: Chars, p: APromise)
    requires inside_obj(kb, f), outside_obj(r, f), f(id),
    ensures ({
        let kc = kext::with_objects(kb, kb.objects.insert(id, p));
        &&& kext::with_objects(gobj(kb, r, c), gobj(kb, r, c).objects.insert(id, p)) == gobj(kc, r, c)
        &&& inside_obj(kc, f)
        &&& kc.schedules == kb.schedules
        &&& gobj(kc, r, c).objects.contains_key(id) && kc.objects.contains_key(id)
        &&& gobj(kc, r, c).objects[id] == kc.objects[id]
    }),
{
    lemma_gobj_insert(kb, r, c, f, id, p);
    lemma_gobj_has(kext::with_objects(kb, kb.objects.insert(id, p)), r, c, f, id);
}

pub proof fn lemma_task_get_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskGetReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_task_get(k, q, now);
        &&& kext::spec_task_get(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_task_read(k, r, c, f, q.id, now);
}

pub proof fn lemma_task_create_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskCreateReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.action.id),
    ensures ({
        let (k2, res) = kext::spec_task_create(k, q, now);
        &&& kext::spec_task_create(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    let act = q.action;
    let id = act.id;
    lemma_gobj_has(k, r, c, f, id);
    if echod_kernel::tags::otype(act.tags) != echod_kernel::tags::OType::Runnable || echod_kernel::tags::timer_targeted(act.tags)
        || act.timeout_at > kernel::MAX_TIME || q.ttl > kernel::MAX_TIME {
    } else if !k.objects.contains_key(id) {
        let p = if act.timeout_at > now { echod_kernel::object::spec_create_acquired(act, q.pid, q.ttl as nat, now) } else { echod_kernel::object::spec_create(act, now) };
        lemma_gobj_insert(k, r, c, f, id, p);
    } else {
        lemma_read_local(k, r, c, f, id, now);
        let kb = kext::spec_read(k, id, now);
        lemma_gobj_has(kb, r, c, f, id);
        let p = kb.objects[id];
        match p.task {
            None => {}
            Some(t) => {
                if t.state == kernel::TaskState::Fulfilled {
                } else if t.state != kernel::TaskState::Pending || t.version >= kernel::MAX_VERSION {
                } else {
                    lemma_task_write(kb, r, c, f, id, p.with_task(t.acquire(q.pid, q.ttl as nat, now)));
                }
            }
        }
    }
}

pub proof fn lemma_task_acquire_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskAcquireReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_task_acquire(k, q, now);
        &&& kext::spec_task_acquire(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_task_read(k, r, c, f, q.id, now);
    let kb = kext::spec_read_task(k, q.id, now);
    if q.ttl > kernel::MAX_TIME || !k.has_task(q.id) {
    } else {
        let p = kb.objects[q.id];
        match p.task {
            None => {}
            Some(t) => {
                if t.state != kernel::TaskState::Pending || p.state != kernel::PromiseState::Pending || t.version != q.version || t.version >= kernel::MAX_VERSION {
                } else {
                    lemma_task_write(kb, r, c, f, q.id, p.with_task(t.acquire(q.pid, q.ttl as nat, now)));
                }
            }
        }
    }
}

pub proof fn lemma_task_fulfill_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskFulfillReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_task_fulfill(k, q, now);
        &&& kext::spec_task_fulfill(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_task_read(k, r, c, f, q.id, now);
    let kb = kext::spec_read_task(k, q.id, now);
    if !q.action.state.spec_settable() || !k.has_task(q.id) {
    } else {
        let p = kb.objects[q.id];
        match p.task {
            None => {}
            Some(t) => {
                if t.state != kernel::TaskState::Acquired || p.state != kernel::PromiseState::Pending || t.version != q.version {
                } else {
                    lemma_task_write(kb, r, c, f, q.id, p.settle(q.action.state, q.action.value, now));
                }
            }
        }
    }
}

pub proof fn lemma_task_release_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskReleaseReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_task_release(k, q, now);
        &&& kext::spec_task_release(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_task_read(k, r, c, f, q.id, now);
    let kb = kext::spec_read_task(k, q.id, now);
    if k.has_task(q.id) {
        let p = kb.objects[q.id];
        match p.task {
            None => {}
            Some(t) => {
                if t.state != kernel::TaskState::Acquired || p.state != kernel::PromiseState::Pending || t.version != q.version {
                } else {
                    lemma_task_write(kb, r, c, f, q.id, p.with_task(t.release(now)));
                }
            }
        }
    }
}

pub proof fn lemma_task_halt_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskHaltReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_task_halt(k, q, now);
        &&& kext::spec_task_halt(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_task_read(k, r, c, f, q.id, now);
    let kb = kext::spec_read_task(k, q.id, now);
    if k.has_task(q.id) {
        let p = kb.objects[q.id];
        match p.task {
            None => {}
            Some(t) => {
                if t.state == kernel::TaskState::Fulfilled || t.state == kernel::TaskState::Halted {
                } else {
                    lemma_task_write(kb, r, c, f, q.id, p.with_task(t.halt()));
                }
            }
        }
    }
}

pub proof fn lemma_task_continue_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskContinueReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_task_continue(k, q, now);
        &&& kext::spec_task_continue(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_task_read(k, r, c, f, q.id, now);
    let kb = kext::spec_read_task(k, q.id, now);
    if k.has_task(q.id) {
        let p = kb.objects[q.id];
        match p.task {
            None => {}
            Some(t) => {
                if t.state != kernel::TaskState::Halted || p.state != kernel::PromiseState::Pending {
                } else {
                    lemma_task_write(kb, r, c, f, q.id, p.with_task(t.continue_(now)));
                }
            }
        }
    }
}

pub proof fn lemma_task_fence_check_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskFenceCheckReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_task_fence_check(k, q, now);
        &&& kext::spec_task_fence_check(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_task_read(k, r, c, f, q.id, now);
}

pub proof fn lemma_task_fence_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskFenceReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), origin_closed(f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_task_fence(k, q, now);
        &&& kext::spec_task_fence(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    let target = kext::fence_target(q.action);
    lemma_task_read(k, r, c, f, q.id, now);
    let kb = kext::spec_read_task(k, q.id, now);
    if target == q.id || !kernel::same_origin_spec(target, q.id) {
    } else if !k.has_task(q.id) {
    } else {
        assert(kernel::same_origin_spec(q.id, target));
        assert(f(target));
        let p = kb.objects[q.id];
        match p.task {
            None => {}
            Some(t) => {
                if t.state != kernel::TaskState::Acquired || p.state != kernel::PromiseState::Pending || t.version != q.version {
                } else {
                    match q.action {
                        kernel::ATaskFenceAction::Create(cq) => lemma_promise_create_local(kb, r, c, f, cq, now),
                        kernel::ATaskFenceAction::Settle(cq) => lemma_promise_settle_local(kb, r, c, f, cq, now),
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// task.heartbeat: the fold over the refs
// ---------------------------------------------------------------------------

/// Every ref's id is in `f`.
pub open spec fn refs_inside(refs: Seq<ATaskRef>, f: Ids) -> bool {
    forall|j: int| 0 <= j < refs.len() ==> f(#[trigger] refs[j].id)
}

pub proof fn lemma_heartbeat_one_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, pid: Chars, x: ATaskRef, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), f(x.id),
    ensures ({
        let k2 = kext::spec_heartbeat_one(k, pid, x, now);
        &&& kext::spec_heartbeat_one(gobj(k, r, c), pid, x, now) == gobj(k2, r, c)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_task_read(k, r, c, f, x.id, now);
    let kb = kext::spec_read_task(k, x.id, now);
    if k.has_task(x.id) {
        let p = kb.objects[x.id];
        match p.task {
            Some(t) => {
                if t.state == kernel::TaskState::Acquired && t.version == x.version && t.pid == Some(pid) && p.state == kernel::PromiseState::Pending {
                    lemma_task_write(kb, r, c, f, x.id, p.with_task(t.heartbeat(now)));
                }
            }
            None => {}
        }
    }
}

pub proof fn lemma_heartbeat_fold_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, pid: Chars, refs: Seq<ATaskRef>, j: int, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), refs_inside(refs, f), 0 <= j <= refs.len(),
    ensures ({
        let k2 = kext::spec_heartbeat_fold(k, pid, refs, j, now);
        &&& kext::spec_heartbeat_fold(gobj(k, r, c), pid, refs, j, now) == gobj(k2, r, c)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
    decreases j,
{
    if j <= 0 {
    } else {
        lemma_heartbeat_fold_local(k, r, c, f, pid, refs, j - 1, now);
        let kj = kext::spec_heartbeat_fold(k, pid, refs, j - 1, now);
        lemma_heartbeat_one_local(kj, r, c, f, pid, refs[j - 1], now);
    }
}

pub proof fn lemma_task_heartbeat_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskHeartbeatReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), refs_inside(q.tasks, f),
    ensures ({
        let (k2, res) = kext::spec_task_heartbeat(k, q, now);
        &&& kext::spec_task_heartbeat(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_heartbeat_fold_local(k, r, c, f, q.pid, q.tasks, q.tasks.len() as int, now);
}

// ---------------------------------------------------------------------------
// task.suspend: the folds over the actions
// ---------------------------------------------------------------------------

/// Every action's awaited promise is in `f`.
pub open spec fn awaited_inside(acts: Seq<APromiseRegisterCallbackReq>, f: Ids) -> bool {
    forall|j: int| 0 <= j < acts.len() ==> f(#[trigger] acts[j].awaited)
}

/// The doors passed: every awaited promise shares the task's origin.
pub proof fn lemma_doors_inside(acts: Seq<APromiseRegisterCallbackReq>, id: Chars, f: Ids)
    requires origin_closed(f), f(id), kext::suspend_doors(acts, id),
    ensures awaited_inside(acts, f),
{
    assert forall|j: int| 0 <= j < acts.len() implies f(#[trigger] acts[j].awaited) by {
        assert(kernel::same_origin_spec(acts[j].awaited, id));
        assert(kernel::same_origin_spec(id, acts[j].awaited));
    }
}

pub proof fn lemma_awaited_read_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, acts: Seq<APromiseRegisterCallbackReq>, j: int, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), awaited_inside(acts, f), 0 <= j <= acts.len(),
    ensures ({
        let k2 = kext::spec_awaited_read(k, acts, j, now);
        &&& kext::spec_awaited_read(gobj(k, r, c), acts, j, now) == gobj(k2, r, c)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
    decreases j,
{
    if j <= 0 {
    } else {
        lemma_awaited_read_local(k, r, c, f, acts, j - 1, now);
        let kj = kext::spec_awaited_read(k, acts, j - 1, now);
        lemma_read_local(kj, r, c, f, acts[j - 1].awaited, now);
    }
}

pub proof fn lemma_first_failing_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, acts: Seq<APromiseRegisterCallbackReq>, j: int)
    requires inside_obj(k, f), outside_obj(r, f), awaited_inside(acts, f), 0 <= j <= acts.len(),
    ensures kext::first_failing(gobj(k, r, c), acts, j) == kext::first_failing(k, acts, j),
    decreases j,
{
    if j <= 0 {
    } else {
        lemma_first_failing_local(k, r, c, f, acts, j - 1);
        lemma_gobj_has(k, r, c, f, acts[j - 1].awaited);
    }
}

/// With every awaited promise present, `any_settled` reads the same
/// objects on both sides.
pub proof fn lemma_any_settled_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, acts: Seq<APromiseRegisterCallbackReq>, now: nat)
    requires
        inside_obj(k, f), outside_obj(r, f), awaited_inside(acts, f),
        forall|j: int| 0 <= j < acts.len() ==> k.objects.contains_key(#[trigger] acts[j].awaited),
    ensures kext::any_settled(gobj(k, r, c), acts, now) == kext::any_settled(k, acts, now),
{
    assert forall|j: int| 0 <= j < acts.len() implies gobj(k, r, c).objects[#[trigger] acts[j].awaited] == k.objects[acts[j].awaited] by {
        lemma_gobj_has(k, r, c, f, acts[j].awaited);
    }
}

pub proof fn lemma_awaited_register_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, acts: Seq<APromiseRegisterCallbackReq>, j: int, id: Chars)
    requires inside_obj(k, f), outside_obj(r, f), awaited_inside(acts, f), 0 <= j <= acts.len(),
        forall|i: int| 0 <= i < acts.len() ==> k.objects.contains_key(#[trigger] acts[i].awaited),
    ensures ({
        let k2 = kext::spec_awaited_register(k, acts, j, id);
        &&& kext::spec_awaited_register(gobj(k, r, c), acts, j, id) == gobj(k2, r, c)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
        &&& forall|i: int| 0 <= i < acts.len() ==> k2.objects.contains_key(#[trigger] acts[i].awaited)
        &&& forall|x: Chars| k.objects.contains_key(x) ==> k2.objects.contains_key(x)
    }),
    decreases j,
{
    if j <= 0 {
    } else {
        lemma_awaited_register_local(k, r, c, f, acts, j - 1, id);
        let kj = kext::spec_awaited_register(k, acts, j - 1, id);
        let w = acts[j - 1].awaited;
        lemma_gobj_has(kj, r, c, f, w);
        lemma_gobj_insert(kj, r, c, f, w, kj.objects[w].add_callback(id));
    }
}

/// No action among the first `j` fails: each awaited promise is there.
proof fn lemma_none_failing_present(k: KState, acts: Seq<APromiseRegisterCallbackReq>, j: int)
    requires 0 <= j <= acts.len(), kext::first_failing(k, acts, j) is None,
    ensures forall|i: int| 0 <= i < j ==> k.objects.contains_key(#[trigger] acts[i].awaited),
    decreases j,
{
    if j <= 0 {
    } else {
        lemma_none_failing_present(k, acts, j - 1);
    }
}

/// Reading the awaited promises keeps every object there.
proof fn lemma_awaited_read_keeps(k: KState, acts: Seq<APromiseRegisterCallbackReq>, j: int, now: nat)
    requires 0 <= j <= acts.len(),
    ensures kext::spec_awaited_read(k, acts, j, now).objects.dom() == k.objects.dom(),
    decreases j,
{
    if j <= 0 {
    } else {
        lemma_awaited_read_keeps(k, acts, j - 1, now);
        let kj = kext::spec_awaited_read(k, acts, j - 1, now);
        assert(kext::spec_read(kj, acts[j - 1].awaited, now).objects.dom() =~= kj.objects.dom());
    }
}

/// The first failing action is one of the first `j`.
proof fn lemma_first_failing_range(k: KState, acts: Seq<APromiseRegisterCallbackReq>, j: int)
    requires 0 <= j <= acts.len(),
    ensures match kext::first_failing(k, acts, j) { Some(i) => 0 <= i < j, None => true },
    decreases j,
{
    if j <= 0 {
    } else {
        lemma_first_failing_range(k, acts, j - 1);
    }
}

pub proof fn lemma_task_suspend_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, q: kernel::ATaskSuspendReq, now: nat)
    requires inside_obj(k, f), outside_obj(r, f), origin_closed(f), f(q.id),
    ensures ({
        let (k2, res) = kext::spec_task_suspend(k, q, now);
        &&& kext::spec_task_suspend(gobj(k, r, c), q, now) == (gobj(k2, r, c), res)
        &&& inside_obj(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    let id = q.id;
    let acts = q.actions;
    let n = acts.len() as int;
    if !kext::suspend_doors(acts, id) {
    } else {
        lemma_doors_inside(acts, id, f);
        lemma_task_read(k, r, c, f, id, now);
        let kb = kext::spec_read_task(k, id, now);
        if !k.has_task(id) {
        } else {
            let p = kb.objects[id];
            match p.task {
                None => {}
                Some(t) => {
                    if t.state != kernel::TaskState::Acquired || p.state != kernel::PromiseState::Pending || t.version != q.version {
                    } else {
                        lemma_first_failing_local(kb, r, c, f, acts, n);
                        match kext::first_failing(kb, acts, n) {
                            Some(j) => {
                                lemma_first_failing_range(kb, acts, n);
                                lemma_gobj_has(kb, r, c, f, acts[j].awaited);
                                let m = if kb.objects.contains_key(acts[j].awaited) { j + 1 } else { j };
                                lemma_awaited_read_local(kb, r, c, f, acts, m, now);
                            }
                            None => {
                                lemma_none_failing_present(kb, acts, n);
                                lemma_awaited_read_local(kb, r, c, f, acts, n, now);
                                let kc = kext::spec_awaited_read(kb, acts, n, now);
                                lemma_awaited_read_keeps(kb, acts, n, now);
                                lemma_any_settled_local(kb, r, c, f, acts, now);
                                lemma_gobj_has(kc, r, c, f, id);
                                if kext::any_settled(kb, acts, now) {
                                    lemma_task_write(kc, r, c, f, id, kc.objects[id].with_task(t.clear_resumes()));
                                } else {
                                    lemma_awaited_register_local(kc, r, c, f, acts, n, id);
                                    let kd = kext::spec_awaited_register(kc, acts, n, id);
                                    lemma_gobj_has(kd, r, c, f, id);
                                    lemma_task_write(kd, r, c, f, id, kd.objects[id].with_task(t.suspend()));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Any request
// ---------------------------------------------------------------------------

/// The ids a request names that its handler reads or writes before any
/// door check relates them to the first: all of them in `f` (objects) or
/// `g` (schedules). The handlers check the rest against these.
pub open spec fn request_inside(req: ARequest, f: Ids, g: Ids) -> bool {
    match req {
        ARequest::PromiseGet(q) => f(q.id),
        ARequest::PromiseCreate(q) => f(q.id),
        ARequest::PromiseSettle(q) => f(q.id),
        ARequest::PromiseRegisterCallback(q) => f(q.awaited),
        ARequest::PromiseRegisterListener(q) => f(q.awaited),
        ARequest::ScheduleGet(q) => g(q.id),
        ARequest::ScheduleCreate(q) => g(q.id),
        ARequest::ScheduleDelete(q) => g(q.id),
        ARequest::TaskGet(q) => f(q.id),
        ARequest::TaskCreate(q) => f(q.action.id),
        ARequest::TaskAcquire(q) => f(q.id),
        ARequest::TaskFulfill(q) => f(q.id),
        ARequest::TaskRelease(q) => f(q.id),
        ARequest::TaskHalt(q) => f(q.id),
        ARequest::TaskContinue(q) => f(q.id),
        ARequest::TaskFence(q) => f(q.id),
        ARequest::TaskFenceCheck(q) => f(q.id),
        ARequest::TaskHeartbeat(q) => refs_inside(q.tasks, f),
        ARequest::TaskSuspend(q) => f(q.id),
    }
}

/// What `lemma_handle_local` says: the handler on the glue is the handler
/// on the document, glued back, with the same answer, and the document
/// stays inside its ids.
pub open spec fn handle_local(k: KState, r: KState, f: Ids, g: Ids, req: ARequest, now: nat) -> bool {
    let (k2, res) = kext::spec_handle(k, req, now);
    &&& kext::spec_handle(glue(k, r), req, now) == (glue(k2, r), res)
    &&& inside_obj(k2, f)
    &&& inside_sch(k2, g)
}

proof fn lemma_handle_local_objects(k: KState, r: KState, f: Ids, g: Ids, req: ARequest, now: nat)
    requires
        inside_obj(k, f), outside_obj(r, f), inside_sch(k, g), origin_closed(f),
        request_inside(req, f, g),
        !kext::is_schedule_request(req),
    ensures handle_local(k, r, f, g, req, now),
{
    let c = k.schedules.union_prefer_right(r.schedules);
    let k2 = kext::spec_handle(k, req, now).0;
    match req {
        ARequest::PromiseGet(q) => lemma_promise_get_local(k, r, c, f, q, now),
        ARequest::PromiseCreate(q) => lemma_promise_create_local(k, r, c, f, q, now),
        ARequest::PromiseSettle(q) => lemma_promise_settle_local(k, r, c, f, q, now),
        ARequest::PromiseRegisterCallback(q) => lemma_promise_register_callback_local(k, r, c, f, q, now),
        ARequest::PromiseRegisterListener(q) => lemma_promise_register_listener_local(k, r, c, f, q, now),
        ARequest::TaskGet(q) => lemma_task_get_local(k, r, c, f, q, now),
        ARequest::TaskCreate(q) => lemma_task_create_local(k, r, c, f, q, now),
        ARequest::TaskAcquire(q) => lemma_task_acquire_local(k, r, c, f, q, now),
        ARequest::TaskFulfill(q) => lemma_task_fulfill_local(k, r, c, f, q, now),
        ARequest::TaskRelease(q) => lemma_task_release_local(k, r, c, f, q, now),
        ARequest::TaskHalt(q) => lemma_task_halt_local(k, r, c, f, q, now),
        ARequest::TaskContinue(q) => lemma_task_continue_local(k, r, c, f, q, now),
        ARequest::TaskFence(q) => lemma_task_fence_local(k, r, c, f, q, now),
        ARequest::TaskFenceCheck(q) => lemma_task_fence_check_local(k, r, c, f, q, now),
        ARequest::TaskHeartbeat(q) => lemma_task_heartbeat_local(k, r, c, f, q, now),
        ARequest::TaskSuspend(q) => lemma_task_suspend_local(k, r, c, f, q, now),
        _ => {}
    }
    lemma_glue_is_gobj(k, k2, r);
}

/// Every handler is local.
pub proof fn lemma_handle_local(k: KState, r: KState, f: Ids, g: Ids, req: ARequest, now: nat)
    requires
        inside_obj(k, f), outside_obj(r, f), inside_sch(k, g), outside_sch(r, g), origin_closed(f),
        request_inside(req, f, g),
    ensures handle_local(k, r, f, g, req, now),
{
    match req {
        ARequest::ScheduleGet(q) => lemma_schedule_get_local(k, r, g, q, now),
        ARequest::ScheduleCreate(q) => lemma_schedule_create_local(k, r, g, q, now),
        ARequest::ScheduleDelete(q) => lemma_schedule_delete_local(k, r, g, q, now),
        _ => lemma_handle_local_objects(k, r, f, g, req, now),
    }
}

// ---------------------------------------------------------------------------
// The sweep's steps on one object
// ---------------------------------------------------------------------------
//
// Each is `gobj`-local and keeps the document inside its ids and its
// callbacks inside them: the sweep never adds a callback, so `callbacks_inside`
// is kept by every step, and `not_self` too.

/// Every id in `f`.
pub open spec fn ids_inside(ids: Seq<Chars>, f: Ids) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> f(#[trigger] ids[i])
}

pub proof fn lemma_ids_inside_drop_last(ids: Seq<Chars>, f: Ids)
    requires ids_inside(ids, f), ids.len() > 0,
    ensures ids_inside(ids.drop_last(), f), f(ids.last()),
{
    assert forall|i: int| 0 <= i < ids.drop_last().len() implies f(#[trigger] ids.drop_last()[i]) by {
        assert(ids.drop_last()[i] == ids[i]);
    }
}

/// What a sweep step keeps of a document: inside its ids, its callbacks
/// inside them, no promise its own callback.
pub open spec fn sweep_shape(k: KState, f: Ids) -> bool {
    &&& inside_obj(k, f)
    &&& callbacks_inside(k, f)
    &&& not_self(k)
}

/// Writing `p` at `id` with no new callback keeps the shape.
proof fn lemma_shape_write(k: KState, f: Ids, id: Chars, p: APromise)
    requires
        sweep_shape(k, f), f(id), p.id == id || k.objects.contains_key(id) && p.id == k.objects[id].id,
        forall|y: Chars| #[trigger] p.callbacks.contains(y) ==> k.objects.contains_key(id) && k.objects[id].callbacks.contains(y),
    ensures sweep_shape(kext::with_objects(k, k.objects.insert(id, p)), f),
{
    let k2 = kext::with_objects(k, k.objects.insert(id, p));
    assert forall|x: Chars, y: Chars| #[trigger] k2.objects.contains_key(x) && #[trigger] k2.objects[x].callbacks.contains(y) implies f(y) by {
        if x != id {
            assert(k.objects.contains_key(x) && k.objects[x].callbacks.contains(y));
        }
    }
}

/// The three object edits the sweep makes keep the callbacks: a projection,
/// a task written, a settlement.
proof fn lemma_project_callbacks(p: APromise, now: nat)
    ensures p.project(now).callbacks == p.callbacks, p.project(now).id == p.id,
{
}

pub proof fn lemma_promise_timeout_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, id: Chars, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), f(id),
    ensures ({
        let k2 = kext::with_objects(k, kint::promise_timeout_objects(k, id, now));
        &&& kext::with_objects(gobj(k, r, c), kint::promise_timeout_objects(gobj(k, r, c), id, now)) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_gobj_has(k, r, c, f, id);
    if k.objects.contains_key(id) {
        let p = k.objects[id].project(now);
        lemma_gobj_insert(k, r, c, f, id, p);
        lemma_project_callbacks(k.objects[id], now);
        lemma_shape_write(k, f, id, p);
    }
}

pub proof fn lemma_lease_timeout_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, id: Chars, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), f(id),
    ensures ({
        let k2 = kext::with_objects(k, kint::lease_timeout_objects(k, id, now));
        &&& kext::with_objects(gobj(k, r, c), kint::lease_timeout_objects(gobj(k, r, c), id, now)) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_gobj_has(k, r, c, f, id);
    if k.objects.contains_key(id) && kint::lease_due(k.objects[id], now) {
        let q = k.objects[id];
        let p = q.with_task(q.task.unwrap().release(q.task.unwrap().lease_timeout_at.unwrap() as nat));
        lemma_gobj_insert(k, r, c, f, id, p);
        lemma_shape_write(k, f, id, p);
    }
}

pub proof fn lemma_retry_timeout_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, id: Chars, now: nat, rt: nat)
    requires sweep_shape(k, f), outside_obj(r, f), f(id),
    ensures ({
        let k2 = kint::retry_timeout_state(k, id, now, rt);
        &&& kint::retry_timeout_state(gobj(k, r, c), id, now, rt) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_gobj_has(k, r, c, f, id);
    if k.objects.contains_key(id) && kint::retry_due(k.objects[id], now) {
        let q = k.objects[id];
        let p = q.with_task(q.task.unwrap().rearm(now, rt));
        lemma_gobj_insert(k, r, c, f, id, p);
        lemma_shape_write(k, f, id, p);
        assert(kint::retry_timeout_state(k, id, now, rt).objects == kext::with_objects(k, k.objects.insert(id, p)).objects);
    }
}

pub proof fn lemma_listener_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, x: Chars, address: Chars, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), f(x),
    ensures ({
        let k2 = kint::listener_state(k, x, address, now);
        &&& kint::listener_state(gobj(k, r, c), x, address, now) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_gobj_has(k, r, c, f, x);
    if k.objects.contains_key(x) {
        let p = k.objects[x].project(now);
        lemma_project_callbacks(k.objects[x], now);
        lemma_gobj_insert(k, r, c, f, x, p);
        lemma_shape_write(k, f, x, p);
        let k1 = kext::with_objects(k, k.objects.insert(x, p));
        if p.state == kernel::PromiseState::Pending || !p.listeners.contains(address) {
        } else {
            let q = p.remove_listener(address);
            lemma_gobj_insert(k1, r, c, f, x, q);
            lemma_shape_write(k1, f, x, q);
            assert(kint::listener_state(k, x, address, now).objects == kext::with_objects(k1, k1.objects.insert(x, q)).objects);
        }
    }
}

pub proof fn lemma_callback_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, x: Chars, y: Chars, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), f(x), f(y),
    ensures ({
        let k2 = kint::callback_state(k, x, y, now);
        &&& kint::callback_state(gobj(k, r, c), x, y, now) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_gobj_has(k, r, c, f, x);
    if k.objects.contains_key(x) {
        let p = k.objects[x].project(now);
        lemma_project_callbacks(k.objects[x], now);
        lemma_gobj_insert(k, r, c, f, x, p);
        lemma_shape_write(k, f, x, p);
        let k1 = kext::with_objects(k, k.objects.insert(x, p));
        if p.state == kernel::PromiseState::Pending || !p.callbacks.contains(y) {
        } else {
            let p2 = p.remove_callback(y);
            assert forall|z: Chars| #[trigger] p2.callbacks.contains(z) implies p.callbacks.contains(z) by {
                echod_kernel::object_proof::lemma_without_contains(p.callbacks, y, z);
            }
            lemma_gobj_insert(k1, r, c, f, x, p2);
            lemma_shape_write(k1, f, x, p2);
            let k2 = kext::with_objects(k1, k1.objects.insert(x, p2));
            lemma_gobj_has(k2, r, c, f, y);
            if k2.objects.contains_key(y) {
                let q = k2.objects[y].project(now);
                lemma_project_callbacks(k2.objects[y], now);
                lemma_gobj_insert(k2, r, c, f, y, q);
                lemma_shape_write(k2, f, y, q);
                let k3 = kext::with_objects(k2, k2.objects.insert(y, q));
                match q.task {
                    None => {}
                    Some(t) => {
                        if t.state == kernel::TaskState::Suspended {
                            let q2 = q.with_task(t.wake(x, echod_kernel::properties::opt_or_zero(p.settled_at)));
                            lemma_gobj_insert(k3, r, c, f, y, q2);
                            lemma_shape_write(k3, f, y, q2);
                        } else if t.state != kernel::TaskState::Fulfilled {
                            let q2 = q.with_task(t.buffer(x));
                            lemma_gobj_insert(k3, r, c, f, y, q2);
                            lemma_shape_write(k3, f, y, q2);
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The sweep's phases
// ---------------------------------------------------------------------------

pub proof fn lemma_deadlines_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, ids: Seq<Chars>, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), ids_inside(ids, f),
    ensures ({
        let k2 = ksteps::executable_deadlines(k, ids, now);
        &&& ksteps::executable_deadlines(gobj(k, r, c), ids, now) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
    decreases ids.len(),
{
    if ids.len() == 0 {
    } else {
        lemma_ids_inside_drop_last(ids, f);
        lemma_deadlines_local(k, r, c, f, ids.drop_last(), now);
        let k1 = ksteps::executable_deadlines(k, ids.drop_last(), now);
        lemma_promise_timeout_local(k1, r, c, f, ids.last(), now);
    }
}

pub proof fn lemma_leases_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, ids: Seq<Chars>, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), ids_inside(ids, f),
    ensures ({
        let k2 = ksteps::executable_leases(k, ids, now);
        &&& ksteps::executable_leases(gobj(k, r, c), ids, now) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
    decreases ids.len(),
{
    if ids.len() == 0 {
    } else {
        lemma_ids_inside_drop_last(ids, f);
        lemma_leases_local(k, r, c, f, ids.drop_last(), now);
        let k1 = ksteps::executable_leases(k, ids.drop_last(), now);
        lemma_lease_timeout_local(k1, r, c, f, ids.last(), now);
    }
}

/// Every owed row is in `f`, and so is every callback it lists.
pub open spec fn owed_inside(owed: Seq<ksteps::AOwed>, f: Ids) -> bool {
    forall|i: int| 0 <= i < owed.len() ==> f(#[trigger] owed[i].awaited) && ids_inside(owed[i].callbacks, f)
}

pub proof fn lemma_owed_snapshot_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, ids: Seq<Chars>)
    requires sweep_shape(k, f), outside_obj(r, f), ids_inside(ids, f),
    ensures
        ksteps::executable_owed_snapshot(gobj(k, r, c), ids) == ksteps::executable_owed_snapshot(k, ids),
        owed_inside(ksteps::executable_owed_snapshot(k, ids), f),
    decreases ids.len(),
{
    if ids.len() == 0 {
    } else {
        lemma_ids_inside_drop_last(ids, f);
        lemma_owed_snapshot_local(k, r, c, f, ids.drop_last());
        let x = ids.last();
        lemma_gobj_has(k, r, c, f, x);
        let prior = ksteps::executable_owed_snapshot(k, ids.drop_last());
        let owed = ksteps::executable_owed_snapshot(k, ids);
        if k.objects.contains_key(x) && k.objects[x].state != kernel::PromiseState::Pending
            && (k.objects[x].callbacks.len() > 0 || k.objects[x].listeners.len() > 0) {
            let item = ksteps::AOwed { awaited: x, callbacks: k.objects[x].callbacks, listeners: k.objects[x].listeners };
            assert(owed == prior.push(item));
            assert(ids_inside(item.callbacks, f)) by {
                assert forall|i: int| 0 <= i < item.callbacks.len() implies f(#[trigger] item.callbacks[i]) by {
                    assert(k.objects[x].callbacks.contains(item.callbacks[i]));
                }
            }
            assert forall|i: int| 0 <= i < owed.len() implies f(#[trigger] owed[i].awaited) && ids_inside(owed[i].callbacks, f) by {
                if i < prior.len() {
                    assert(owed[i] == prior[i]);
                } else {
                    assert(owed[i] == item);
                }
            }
        }
    }
}

pub proof fn lemma_callbacks_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, x: Chars, cbs: Seq<Chars>, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), f(x), ids_inside(cbs, f),
    ensures ({
        let k2 = ksteps::executable_callbacks(k, x, cbs, now);
        &&& ksteps::executable_callbacks(gobj(k, r, c), x, cbs, now) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
    decreases cbs.len(),
{
    if cbs.len() == 0 {
    } else {
        lemma_ids_inside_drop_last(cbs, f);
        lemma_callbacks_local(k, r, c, f, x, cbs.drop_last(), now);
        let k1 = ksteps::executable_callbacks(k, x, cbs.drop_last(), now);
        lemma_callback_local(k1, r, c, f, x, cbs.last(), now);
    }
}

pub proof fn lemma_owed_inside_drop_last(owed: Seq<ksteps::AOwed>, f: Ids)
    requires owed_inside(owed, f), owed.len() > 0,
    ensures owed_inside(owed.drop_last(), f), f(owed.last().awaited), ids_inside(owed.last().callbacks, f),
{
    assert forall|i: int| 0 <= i < owed.drop_last().len() implies f(#[trigger] owed.drop_last()[i].awaited) && ids_inside(owed.drop_last()[i].callbacks, f) by {
        assert(owed.drop_last()[i] == owed[i]);
        assert(f(owed[i].awaited) && ids_inside(owed[i].callbacks, f));
    }
    assert(f(owed[owed.len() - 1].awaited) && ids_inside(owed[owed.len() - 1].callbacks, f));
}

pub proof fn lemma_owed_callbacks_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, owed: Seq<ksteps::AOwed>, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), owed_inside(owed, f),
    ensures ({
        let k2 = ksteps::executable_owed_callbacks(k, owed, now);
        &&& ksteps::executable_owed_callbacks(gobj(k, r, c), owed, now) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
    decreases owed.len(),
{
    if owed.len() == 0 {
    } else {
        lemma_owed_inside_drop_last(owed, f);
        lemma_owed_callbacks_local(k, r, c, f, owed.drop_last(), now);
        let k1 = ksteps::executable_owed_callbacks(k, owed.drop_last(), now);
        lemma_callbacks_local(k1, r, c, f, owed.last().awaited, owed.last().callbacks, now);
    }
}

pub proof fn lemma_listeners_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, x: Chars, ls: Seq<Chars>, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), f(x),
    ensures ({
        let k2 = ksteps::executable_listeners(k, x, ls, now);
        &&& ksteps::executable_listeners(gobj(k, r, c), x, ls, now) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
    decreases ls.len(),
{
    if ls.len() == 0 {
    } else {
        lemma_listeners_local(k, r, c, f, x, ls.drop_last(), now);
        let k1 = ksteps::executable_listeners(k, x, ls.drop_last(), now);
        lemma_listener_local(k1, r, c, f, x, ls.last(), now);
    }
}

pub proof fn lemma_owed_listeners_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, owed: Seq<ksteps::AOwed>, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), owed_inside(owed, f),
    ensures ({
        let k2 = ksteps::executable_owed_listeners(k, owed, now);
        &&& ksteps::executable_owed_listeners(gobj(k, r, c), owed, now) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
    decreases owed.len(),
{
    if owed.len() == 0 {
    } else {
        lemma_owed_inside_drop_last(owed, f);
        lemma_owed_listeners_local(k, r, c, f, owed.drop_last(), now);
        let k1 = ksteps::executable_owed_listeners(k, owed.drop_last(), now);
        lemma_listeners_local(k1, r, c, f, owed.last().awaited, owed.last().listeners, now);
    }
}

pub proof fn lemma_due_snapshot_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, ids: Seq<Chars>, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), ids_inside(ids, f),
    ensures
        ksteps::executable_due_snapshot(gobj(k, r, c), ids, now) == ksteps::executable_due_snapshot(k, ids, now),
        ids_inside(ksteps::executable_due_snapshot(k, ids, now), f),
    decreases ids.len(),
{
    if ids.len() == 0 {
    } else {
        lemma_ids_inside_drop_last(ids, f);
        lemma_due_snapshot_local(k, r, c, f, ids.drop_last(), now);
        let x = ids.last();
        lemma_gobj_has(k, r, c, f, x);
        let prior = ksteps::executable_due_snapshot(k, ids.drop_last(), now);
        let due = ksteps::executable_due_snapshot(k, ids, now);
        if k.objects.contains_key(x) && kint::retry_due(k.objects[x], now) {
            assert(due == prior.push(x));
            assert forall|i: int| 0 <= i < due.len() implies f(#[trigger] due[i]) by {
                if i < prior.len() {
                    assert(due[i] == prior[i]);
                } else {
                    assert(due[i] == x);
                }
            }
        }
    }
}

pub proof fn lemma_due_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, due: Seq<Chars>, now: nat, rt: nat)
    requires sweep_shape(k, f), outside_obj(r, f), ids_inside(due, f),
    ensures ({
        let k2 = ksteps::executable_due(k, due, now, rt);
        &&& ksteps::executable_due(gobj(k, r, c), due, now, rt) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
    decreases due.len(),
{
    if due.len() == 0 {
    } else {
        lemma_ids_inside_drop_last(due, f);
        lemma_due_local(k, r, c, f, due.drop_last(), now, rt);
        let k1 = ksteps::executable_due(k, due.drop_last(), now, rt);
        lemma_retry_timeout_local(k1, r, c, f, due.last(), now, rt);
    }
}

/// The whole sweep is local: on the glue it is the sweep of the document,
/// glued back, and the document keeps its shape and its schedules.
pub proof fn lemma_single_pass_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, ids: Seq<Chars>, now: nat, rt: nat)
    requires sweep_shape(k, f), outside_obj(r, f), ids_inside(ids, f),
    ensures ({
        let k2 = ksteps::executable_single_pass(k, ids, now, rt);
        &&& ksteps::executable_single_pass(gobj(k, r, c), ids, now, rt) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    lemma_deadlines_local(k, r, c, f, ids, now);
    let k1 = ksteps::executable_deadlines(k, ids, now);
    lemma_leases_local(k1, r, c, f, ids, now);
    let k2 = ksteps::executable_leases(k1, ids, now);
    lemma_owed_snapshot_local(k2, r, c, f, ids);
    let owed = ksteps::executable_owed_snapshot(k2, ids);
    lemma_owed_callbacks_local(k2, r, c, f, owed, now);
    let k3 = ksteps::executable_owed_callbacks(k2, owed, now);
    lemma_owed_listeners_local(k3, r, c, f, owed, now);
    let k4 = ksteps::executable_owed_listeners(k3, owed, now);
    lemma_due_snapshot_local(k4, r, c, f, ids, now);
    let due = ksteps::executable_due_snapshot(k4, ids, now);
    lemma_due_local(k4, r, c, f, due, now, rt);
}

// ---------------------------------------------------------------------------
// The fire
// ---------------------------------------------------------------------------

/// Every occurrence's promise is in `f`.
pub open spec fn occs_inside(occs: Seq<AOccurrence>, f: Ids) -> bool {
    forall|j: int| 0 <= j < occs.len() ==> f(#[trigger] occs[j].promise_id)
}

pub proof fn lemma_fire_step_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, sch: ASchedule, o: AOccurrence, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), f(o.promise_id),
    ensures ({
        let k2 = kint::fire_step(now, k, sch, o);
        &&& kint::fire_step(now, gobj(k, r, c), sch, o) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
        &&& k2.outbox == k.outbox
    }),
{
    let x = o.promise_id;
    lemma_gobj_has(k, r, c, f, x);
    if !k.objects.contains_key(x) {
        let p = kint::born_occurrence(sch, o);
        assert(p.callbacks == Seq::<Chars>::empty());
        lemma_gobj_insert(k, r, c, f, x, p);
        let k2 = kext::with_objects(k, k.objects.insert(x, p));
        assert forall|z: Chars, y: Chars| #[trigger] k2.objects.contains_key(z) && #[trigger] k2.objects[z].callbacks.contains(y) implies f(y) by {
            if z != x {
                assert(k.objects.contains_key(z) && k.objects[z].callbacks.contains(y));
            }
        }
    }
}

pub proof fn lemma_fire_fold_local(k: KState, r: KState, c: Map<Chars, ASchedule>, f: Ids, sch: ASchedule, occs: Seq<AOccurrence>, j: int, now: nat)
    requires sweep_shape(k, f), outside_obj(r, f), occs_inside(occs, f), 0 <= j <= occs.len(),
    ensures ({
        let k2 = kint::fire_fold(now, k, sch, occs, j);
        &&& kint::fire_fold(now, gobj(k, r, c), sch, occs, j) == gobj(k2, r, c)
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
        &&& k2.outbox == k.outbox
    }),
    decreases j,
{
    if j <= 0 {
    } else {
        lemma_fire_fold_local(k, r, c, f, sch, occs, j - 1, now);
        let k1 = kint::fire_fold(now, k, sch, occs, j - 1);
        lemma_fire_step_local(k1, r, c, f, sch, occs[j - 1], now);
    }
}

} // verus!
