//! Each request handler of the process's document agrees with the model's:
//! on related documents, both leave related documents and answer the same
//! response. `lemma_handle_agrees` gathers the eighteen.

use vstd::prelude::*;

use echod_types::spec::*;
use echod_types::{
    PromiseCreateReq, PromiseGetReq, PromiseRegisterCallbackReq, PromiseRegisterListenerReq,
    PromiseSettleReq, PromiseState, Request, Response, Tags, TaskAcquireReq, TaskContinueReq,
    TaskCreateReq, TaskFenceAction, TaskFenceCheckReq, TaskFenceReq, TaskFulfillReq, TaskGetReq,
    TaskHaltReq, TaskHeartbeatReq, TaskRef, TaskReleaseReq, TaskState, TaskSuspendReq, Value,
    ScheduleCreateReq, ScheduleDeleteReq, ScheduleGetReq, Schedule,
};

use echod_document::spec as p;
use echod_document::state::AState;
use echod_document::tags::{is_timer, otype, tags_get, tags_has, timer_targeted, OType};
use echod_document::types::{APromise, ATask, MAX_TIME, MAX_VERSION};

use echod_concrete::node as c;
use echod_concrete::node::{DocV, ObjV, PromV, TkV};

use crate::relation::*;

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::map::group_map_lemmas};

// ---------------------------------------------------------------------------
// Trusted: any tag pairs are some vector's pairs, so the empty value exists.
// ---------------------------------------------------------------------------

/// Any tag pairs are some vector's pairs.
pub axiom fn axiom_tags_realised(tags: ATags)
    ensures
        exists|t: Tags| t.deep_view() == tags,
;

/// The model's empty value reads as the process's.
pub proof fn lemma_empty_value()
    ensures
        c::spec_empty_value()@ == AValue::empty(),
{
    axiom_tags_realised(Seq::empty());
    let t = choose|t: Tags| t.deep_view() == Seq::<(Seq<char>, Seq<char>)>::empty();
    let v = Value { headers: t, data: None };
    assert(v@ == AValue::empty());
    assert(exists|v: Value| v@ == AValue::empty());
}

// ---------------------------------------------------------------------------
// Reads and writes
// ---------------------------------------------------------------------------

/// What a handler leaves: the model's document is an origin's, related to
/// the process's state, whose schedules are as they were.
pub open spec fn out_rel(a: AState, b: AState, doc: DocV, now: u64) -> bool {
    &&& doc is Origin
    &&& objs_rel(b.objects, c::spec_origin_map(doc), now as nat)
    &&& b.schedules == a.schedules
}

/// Both sides read the same object: the process persists what the model
/// projects, and the relation survives the persisting.
pub proof fn lemma_read(a: AState, map: Map<Seq<char>, ObjV>, id: Seq<char>, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
        map.contains_key(id),
    ensures
        a.objects.contains_key(id),
        a.objects[id].task is Some <==> map[id].task is Some,
        p::spec_read(a, id, now as nat).objects[id] == to_prom(id, c::spec_project_obj(map[id], now)),
        p::spec_read(a, id, now as nat).objects.contains_key(id),
        objs_rel(p::spec_read(a, id, now as nat).objects, map, now as nat),
        p::spec_read(a, id, now as nat).schedules == a.schedules,
        p::spec_read(a, id, now as nat).outbox == a.outbox,
        p::spec_read_task(a, id, now as nat) == if map[id].task is Some { p::spec_read(a, id, now as nat) } else { a },
        a.has_task(id) <==> map[id].task is Some,
{
    lemma_project(id, map[id], now);
    let b = p::spec_read(a, id, now as nat);
    lemma_project_twice(a.objects[id], now as nat);
    assert(b.objects.dom() =~= map.dom());
}

/// Both sides write at `x`: what they write reads the same once projected.
pub proof fn lemma_write(objs: Map<Seq<char>, APromise>, map: Map<Seq<char>, ObjV>, now: u64, x: Seq<char>, q: APromise, o: ObjV)
    requires
        objs_rel(objs, map, now as nat),
        q.project(now as nat) == to_prom(x, o).project(now as nat),
    ensures
        objs_rel(objs.insert(x, q), map.insert(x, o), now as nat),
{
    assert(objs.insert(x, q).dom() =~= map.insert(x, o).dom());
}

/// The process writes at `x` what the model already holds there.
pub proof fn lemma_write_left(objs: Map<Seq<char>, APromise>, map: Map<Seq<char>, ObjV>, now: u64, x: Seq<char>, q: APromise)
    requires
        objs_rel(objs, map, now as nat),
        map.contains_key(x),
        q.project(now as nat) == to_prom(x, map[x]).project(now as nat),
    ensures
        objs_rel(objs.insert(x, q), map, now as nat),
{
    assert(objs.insert(x, q).dom() =~= map.dom());
}

/// An object both sides edit from its projection: the edit keeps the
/// promise settled or ahead of its deadline, so projecting again is nothing.
pub proof fn lemma_edit_projected(x: Seq<char>, o: ObjV, now: u64, q: APromise, e: ObjV)
    requires
        q == to_prom(x, e),
        e.promise.state == PromiseState::Pending ==> e.promise.timeout_at > now,
        e.promise.state != PromiseState::Pending ==> match e.task {
            Some(t) => t.state == TaskState::Fulfilled,
            None => true,
        },
    ensures
        q.project(now as nat) == to_prom(x, e).project(now as nat),
        q.project(now as nat) == q,
        to_prom(x, c::spec_project_obj(e, now)) == q,
{
    lemma_project(x, e, now);
}

// ---------------------------------------------------------------------------
// Birth
// ---------------------------------------------------------------------------

/// The object `promise.create` writes, on both sides.
pub proof fn lemma_new_obj(req: PromiseCreateReq, now: u64)
    requires
        delay_ok(req.tags),
    ensures
        to_prom(req.id@, c::spec_new_obj(req.timeout_at, now, req.param, req.tags, c::spec_targeted(req.tags)))
            == echod_document::object::spec_create(req@, now as nat),
{
    lemma_tags(req.tags);
    lemma_empty_value();
    let v = req.tags.deep_view();
    assert(v.skip(0) =~= v);
    lemma_delay(req.tags, 0);
    reveal_strlit("resonate:delay");
}

// ---------------------------------------------------------------------------
// Promise handlers
// ---------------------------------------------------------------------------

pub proof fn lemma_promise_get(a: AState, map: Map<Seq<char>, ObjV>, q: PromiseGetReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_promise_get(a, q@, now as nat);
            let (doc, s) = c::spec_promise_get(DocV::Origin(map), q.id, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Promise(r)
        }),
{
    let id = q.id@;
    if map.contains_key(id) {
        lemma_read(a, map, id, now);
        lemma_record(q.id, c::spec_project_obj(map[id], now));
    }
}

pub proof fn lemma_promise_create(a: AState, map: Map<Seq<char>, ObjV>, q: PromiseCreateReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
        create_ok(q),
    ensures
        ({
            let (b, r) = p::spec_promise_create(a, q@, now as nat);
            let (doc, s) = c::spec_promise_create(DocV::Origin(map), q, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Promise(r)
        }),
{
    let id = q.id@;
    lemma_tags(q.tags);
    if c::spec_timer(q.tags) && c::spec_targeted(q.tags) {
    } else if map.contains_key(id) {
        lemma_read(a, map, id, now);
        lemma_record(q.id, c::spec_project_obj(map[id], now));
    } else {
        let o = c::spec_new_obj(q.timeout_at, now, q.param, q.tags, c::spec_targeted(q.tags));
        lemma_new_obj(q, now);
        let w = echod_document::object::spec_create(q@, now as nat);
        lemma_write(a.objects, map, now, id, w, o);
        lemma_record(q.id, o);
    }
}

pub proof fn lemma_promise_settle(a: AState, map: Map<Seq<char>, ObjV>, q: PromiseSettleReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_promise_settle(a, q@, now as nat);
            let (doc, s) = c::spec_promise_settle(DocV::Origin(map), q, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Promise(r)
        }),
{
    let id = q.id@;
    if !q.state.spec_settable() {
    } else if !map.contains_key(id) {
    } else {
        lemma_read(a, map, id, now);
        let b = p::spec_read(a, id, now as nat);
        let seen = c::spec_project_obj(map[id], now);
        if seen.promise.state == PromiseState::Pending {
            let promise = PromV { state: q.state, value: q.value, settled_at: Some(now), ..seen.promise };
            let task = match seen.task {
                Some(t) if t.state != TaskState::Fulfilled => Some(c::spec_fulfill_task(t)),
                other => other,
            };
            let e = ObjV { promise, task };
            let w = b.objects[id].settle(q.state, q.value@, now as nat);
            assert(w == to_prom(id, e));
            lemma_edit_projected(id, seen, now, w, e);
            lemma_write(b.objects, map, now, id, w, e);
            lemma_record(q.id, e);
        } else {
            lemma_record(q.id, seen);
        }
    }
}

pub proof fn lemma_register_callback(a: AState, map: Map<Seq<char>, ObjV>, q: PromiseRegisterCallbackReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_promise_register_callback(a, q@, now as nat);
            let (doc, s) = c::spec_register_callback(DocV::Origin(map), q.awaited, q.awaiter, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Promise(r)
        }),
{
    let x = q.awaited@;
    let y = q.awaiter@;
    if x == y || !echod_types::same_origin_spec(x, y) {
    } else if !map.contains_key(x) {
    } else {
        lemma_read(a, map, x, now);
        let a1 = p::spec_read(a, x, now as nat);
        if !map.contains_key(y) {
        } else {
            lemma_read(a1, map, y, now);
            let a2 = p::spec_read(a1, y, now as nat);
            let ox = c::spec_project_obj(map[x], now);
            let oy = c::spec_project_obj(map[y], now);
            assert(a2.objects[x] == to_prom(x, ox));
            assert(a2.objects[y] == to_prom(y, oy));
            lemma_tags(ox.promise.tags);
            lemma_tags(oy.promise.tags);
            if !c::spec_targeted(oy.promise.tags) || !c::spec_awaitable(ox.promise.tags) {
            } else {
                lemma_record(q.awaited, ox);
                if ox.promise.state == PromiseState::Pending && oy.promise.state == PromiseState::Pending {
                    let callbacks = if ox.promise.callbacks.contains(y) { ox.promise.callbacks } else { ox.promise.callbacks.push(y) };
                    let e = ObjV { promise: PromV { callbacks, ..ox.promise }, ..ox };
                    let w = a2.objects[x].add_callback(y);
                    assert(w == to_prom(x, e));
                    lemma_edit_projected(x, ox, now, w, e);
                    lemma_write(a2.objects, map, now, x, w, e);
                }
            }
        }
    }
}

pub proof fn lemma_register_listener(a: AState, map: Map<Seq<char>, ObjV>, q: PromiseRegisterListenerReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_promise_register_listener(a, q@, now as nat);
            let (doc, s) = c::spec_register_listener(DocV::Origin(map), q.awaited, q.address, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Promise(r)
        }),
{
    let x = q.awaited@;
    if !map.contains_key(x) {
    } else {
        lemma_read(a, map, x, now);
        let b = p::spec_read(a, x, now as nat);
        let ox = c::spec_project_obj(map[x], now);
        lemma_tags(ox.promise.tags);
        if !c::spec_awaitable(ox.promise.tags) {
        } else {
            lemma_record(q.awaited, ox);
            if ox.promise.state == PromiseState::Pending {
                let address = q.address@;
                let listeners = if ox.promise.listeners.contains(address) { ox.promise.listeners } else { ox.promise.listeners.push(address) };
                let e = ObjV { promise: PromV { listeners, ..ox.promise }, ..ox };
                let w = b.objects[x].add_listener(address);
                assert(w == to_prom(x, e));
                lemma_edit_projected(x, ox, now, w, e);
                lemma_write(b.objects, map, now, x, w, e);
            }
        }
    }
}

pub proof fn lemma_task_get(a: AState, map: Map<Seq<char>, ObjV>, q: TaskGetReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_task_get(a, q@, now as nat);
            let (doc, s) = c::spec_task_get(DocV::Origin(map), q.id, now);
            out_rel(a, b, doc, now) && s@ == AResponse::TaskGet(r)
        }),
{
    let id = q.id@;
    if map.contains_key(id) {
        lemma_read(a, map, id, now);
        let o = c::spec_project_obj(map[id], now);
        if o.task is Some {
            lemma_task_record(q.id, o.task.unwrap());
        }
    }
}

// ---------------------------------------------------------------------------
// Task handlers
// ---------------------------------------------------------------------------

/// `task.acquire`'s edit, on both sides, within the bounds.
pub proof fn lemma_acquire(t: TkV, pid: Seq<char>, ttl: u64, now: u64)
    requires
        t.version < MAX_VERSION,
        ttl <= MAX_TIME,
        now <= MAX_TIME,
    ensures
        to_task(c::spec_acquire(t, pid, ttl, now)) == to_task(t).acquire(pid, ttl as nat, now as nat),
{
}

/// The model's `spec_held` against the process's reading of a task.
pub proof fn lemma_held(a: AState, map: Map<Seq<char>, ObjV>, id: Seq<char>, version: u64, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (m, held) = c::spec_held(map, id, version, now);
            let b = p::spec_read_task(a, id, now as nat);
            &&& m == map
            &&& objs_rel(b.objects, map, now as nat)
            &&& b.schedules == a.schedules
            &&& match held {
                c::Held::Missing => !a.has_task(id),
                c::Held::Stale => a.has_task(id) && {
                    let q = b.objects[id];
                    &&& q.task is Some
                    &&& q == to_prom(id, c::spec_project_obj(map[id], now))
                    &&& (q.task.unwrap().state != TaskState::Acquired || q.state != PromiseState::Pending
                        || q.task.unwrap().version != version)
                },
                c::Held::Ok(o) => a.has_task(id) && {
                    let q = b.objects[id];
                    &&& o == c::spec_project_obj(map[id], now)
                    &&& q == to_prom(id, o)
                    &&& o.task is Some
                    &&& o.task.unwrap().state == TaskState::Acquired
                    &&& o.task.unwrap().version == version
                    &&& o.promise.state == PromiseState::Pending
                    &&& o.promise.timeout_at > now
                    &&& q.task is Some
                    &&& q.task.unwrap().state == TaskState::Acquired
                    &&& q.task.unwrap().version == version
                    &&& q.state == PromiseState::Pending
                },
            }
        }),
{
    if map.contains_key(id) {
        lemma_read(a, map, id, now);
    }
}

pub proof fn lemma_task_create(a: AState, map: Map<Seq<char>, ObjV>, q: TaskCreateReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
        doc_ok(DocV::Origin(map)),
        create_ok(q.action),
        q.ttl <= MAX_TIME,
        now <= MAX_TIME,
    ensures
        ({
            let (b, r) = p::spec_task_create(a, q@, now as nat);
            let (doc, s) = c::spec_task_create(DocV::Origin(map), q.pid, q.ttl, q.action, now);
            out_rel(a, b, doc, now) && s@ == AResponse::TaskClaim(r)
        }),
{
    let act = q.action;
    let id = act.id@;
    lemma_tags(act.tags);
    if !c::spec_targeted(act.tags) || c::spec_timer(act.tags) {
    } else if !map.contains_key(id) {
        let o = c::spec_new_obj(act.timeout_at, now, act.param, act.tags, c::spec_targeted(act.tags));
        lemma_new_obj(act, now);
        let w = echod_document::object::spec_create(act@, now as nat);
        let map1 = map.insert(id, o);
        lemma_project(id, o, now);
        let seen = c::spec_project_obj(o, now);
        if act.timeout_at > now {
            assert(seen == o);
            let t = o.task.unwrap();
            let u = c::spec_acquire(t, q.pid@, q.ttl, now);
            lemma_acquire(t, q.pid@, q.ttl, now);
            let e = ObjV { task: Some(u), ..seen };
            let wa = echod_document::object::spec_create_acquired(act@, q.pid@, q.ttl as nat, now as nat);
            assert(wa == to_prom(id, e));
            lemma_edit_projected(id, seen, now, wa, e);
            assert(map1.insert(id, e) =~= map.insert(id, e));
            lemma_write(a.objects, map, now, id, wa, e);
            lemma_task_record(act.id, u);
            lemma_record(act.id, e);
        } else {
            assert(seen == o);
            lemma_write(a.objects, map, now, id, w, o);
            lemma_task_record(act.id, o.task.unwrap());
            lemma_record(act.id, o);
        }
    } else {
        lemma_read(a, map, id, now);
        let b = p::spec_read(a, id, now as nat);
        let seen = c::spec_project_obj(map[id], now);
        lemma_tags(seen.promise.tags);
        if !c::spec_targeted(seen.promise.tags) {
        } else {
            match seen.task {
                None => {},
                Some(t) => {
                    if t.state == TaskState::Fulfilled {
                        lemma_task_record(act.id, t);
                        lemma_record(act.id, seen);
                    } else if t.state == TaskState::Pending {
                        let u = c::spec_acquire(t, q.pid@, q.ttl, now);
                        lemma_acquire(t, q.pid@, q.ttl, now);
                        let e = ObjV { task: Some(u), ..seen };
                        let w = b.objects[id].with_task(b.objects[id].task.unwrap().acquire(q.pid@, q.ttl as nat, now as nat));
                        assert(w == to_prom(id, e));
                        lemma_edit_projected(id, seen, now, w, e);
                        lemma_write(b.objects, map, now, id, w, e);
                        lemma_task_record(act.id, u);
                        lemma_record(act.id, e);
                    }
                },
            }
        }
    }
}

pub proof fn lemma_task_acquire(a: AState, map: Map<Seq<char>, ObjV>, q: TaskAcquireReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
        doc_ok(DocV::Origin(map)),
        q.ttl <= MAX_TIME,
        now <= MAX_TIME,
    ensures
        ({
            let (b, r) = p::spec_task_acquire(a, q@, now as nat);
            let (doc, s) = c::spec_task_acquire(DocV::Origin(map), q.id, q.version, q.pid, q.ttl, now);
            out_rel(a, b, doc, now) && s@ == AResponse::TaskClaim(r)
        }),
{
    let id = q.id@;
    if map.contains_key(id) {
        lemma_read(a, map, id, now);
        let b = p::spec_read(a, id, now as nat);
        let seen = c::spec_project_obj(map[id], now);
        match seen.task {
            None => {},
            Some(t) => {
                if t.state == TaskState::Pending && t.version == q.version && seen.promise.state == PromiseState::Pending {
                    let u = c::spec_acquire(t, q.pid@, q.ttl, now);
                    lemma_acquire(t, q.pid@, q.ttl, now);
                    let e = ObjV { task: Some(u), ..seen };
                    let w = b.objects[id].with_task(b.objects[id].task.unwrap().acquire(q.pid@, q.ttl as nat, now as nat));
                    assert(w == to_prom(id, e));
                    lemma_edit_projected(id, seen, now, w, e);
                    lemma_write(b.objects, map, now, id, w, e);
                    lemma_task_record(q.id, u);
                    lemma_record(q.id, e);
                }
            },
        }
    }
}

pub proof fn lemma_task_fulfill(a: AState, map: Map<Seq<char>, ObjV>, q: TaskFulfillReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_task_fulfill(a, q@, now as nat);
            let (doc, s) = c::spec_task_fulfill(DocV::Origin(map), q.id, q.version, q.action, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Promise(r)
        }),
{
    let id = q.id@;
    if !q.action.state.spec_settable() {
    } else {
        lemma_held(a, map, id, q.version, now);
        let (_, held) = c::spec_held(map, id, q.version, now);
        let b = p::spec_read_task(a, id, now as nat);
        match held {
            c::Held::Ok(obj) => {
                let promise = PromV { state: q.action.state, value: q.action.value, settled_at: Some(now), ..obj.promise };
                let task = match obj.task {
                    Some(t) if t.state != TaskState::Fulfilled => Some(c::spec_fulfill_task(t)),
                    other => other,
                };
                let e = ObjV { promise, task };
                let w = b.objects[id].settle(q.action.state, q.action.value@, now as nat);
                assert(w == to_prom(id, e));
                lemma_edit_projected(id, obj, now, w, e);
                lemma_write(b.objects, map, now, id, w, e);
                lemma_record(q.id, e);
            },
            _ => {},
        }
    }
}

pub proof fn lemma_task_release(a: AState, map: Map<Seq<char>, ObjV>, q: TaskReleaseReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_task_release(a, q@, now as nat);
            let (doc, s) = c::spec_task_release(DocV::Origin(map), q.id, q.version, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Status(r)
        }),
{
    let id = q.id@;
    lemma_held(a, map, id, q.version, now);
    let (_, held) = c::spec_held(map, id, q.version, now);
    let b = p::spec_read_task(a, id, now as nat);
    match held {
        c::Held::Ok(obj) => {
            let t = obj.task.unwrap();
            let e = ObjV { task: Some(c::spec_unlease(t, TaskState::Pending, Some(now))), ..obj };
            let w = b.objects[id].with_task(b.objects[id].task.unwrap().release(now as nat));
            assert(w == to_prom(id, e));
            lemma_edit_projected(id, obj, now, w, e);
            lemma_write(b.objects, map, now, id, w, e);
        },
        _ => {},
    }
}

pub proof fn lemma_task_halt(a: AState, map: Map<Seq<char>, ObjV>, q: TaskHaltReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_task_halt(a, q@, now as nat);
            let (doc, s) = c::spec_task_halt(DocV::Origin(map), q.id, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Status(r)
        }),
{
    let id = q.id@;
    if map.contains_key(id) {
        lemma_read(a, map, id, now);
        let b = p::spec_read(a, id, now as nat);
        let obj = c::spec_project_obj(map[id], now);
        match obj.task {
            None => {},
            Some(t) => {
                if t.state == TaskState::Fulfilled || t.state == TaskState::Halted {
                } else {
                    let e = ObjV { task: Some(c::spec_unlease(t, TaskState::Halted, None)), ..obj };
                    let w = b.objects[id].with_task(b.objects[id].task.unwrap().halt());
                    assert(w == to_prom(id, e));
                    lemma_edit_projected(id, obj, now, w, e);
                    lemma_write(b.objects, map, now, id, w, e);
                }
            },
        }
    }
}

pub proof fn lemma_task_continue(a: AState, map: Map<Seq<char>, ObjV>, q: TaskContinueReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_task_continue(a, q@, now as nat);
            let (doc, s) = c::spec_task_continue(DocV::Origin(map), q.id, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Status(r)
        }),
{
    let id = q.id@;
    if map.contains_key(id) {
        lemma_read(a, map, id, now);
        let b = p::spec_read(a, id, now as nat);
        let obj = c::spec_project_obj(map[id], now);
        match obj.task {
            None => {},
            Some(t) => {
                if t.state == TaskState::Halted && obj.promise.state == PromiseState::Pending {
                    let e = ObjV { task: Some(TkV { state: TaskState::Pending, retry_timeout_at: Some(now), ..t }), ..obj };
                    let w = b.objects[id].with_task(b.objects[id].task.unwrap().continue_(now as nat));
                    assert(w == to_prom(id, e));
                    lemma_edit_projected(id, obj, now, w, e);
                    lemma_write(b.objects, map, now, id, w, e);
                }
            },
        }
    }
}

pub proof fn lemma_fence(a: AState, map: Map<Seq<char>, ObjV>, q: TaskFenceReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
        match q.action {
            TaskFenceAction::Create(cr) => create_ok(cr),
            TaskFenceAction::Settle(_) => true,
        },
    ensures
        ({
            let (b, r) = p::spec_task_fence(a, q@, now as nat);
            let (doc, s) = c::spec_fence(DocV::Origin(map), q.id, q.version, q.action, now);
            out_rel(a, b, doc, now) && s@ == AResponse::TaskFence(r)
        }),
{
    let id = q.id@;
    let target = match q.action {
        TaskFenceAction::Create(cr) => cr.id,
        TaskFenceAction::Settle(st) => st.id,
    };
    if target@ == id || !echod_types::same_origin_spec(target@, id) {
    } else {
        lemma_held(a, map, id, q.version, now);
        let (_, held) = c::spec_held(map, id, q.version, now);
        let b = p::spec_read_task(a, id, now as nat);
        match held {
            c::Held::Ok(_) => {
                match q.action {
                    TaskFenceAction::Create(cr) => {
                        lemma_promise_create(b, map, cr, now);
                    },
                    TaskFenceAction::Settle(st) => {
                        lemma_promise_settle(b, map, st, now);
                    },
                }
            },
            _ => {},
        }
    }
}

pub proof fn lemma_fence_check(a: AState, map: Map<Seq<char>, ObjV>, q: TaskFenceCheckReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_task_fence_check(a, q@, now as nat);
            let (doc, s) = c::spec_fence_check(DocV::Origin(map), q.id, q.version, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Status(r)
        }),
{
    lemma_held(a, map, q.id@, q.version, now);
}

// ---------------------------------------------------------------------------
// task.heartbeat: a fold over the refs on both sides
// ---------------------------------------------------------------------------

/// The refs, as the process's handler sees them.
pub open spec fn refs_v(tasks: Seq<TaskRef>) -> Seq<ATaskRef> {
    tasks.map_values(|t: TaskRef| t@)
}

pub proof fn lemma_refs_v(tasks: Vec<TaskRef>)
    ensures
        tasks.deep_view() == refs_v(tasks@),
{
    assert(tasks.deep_view() =~= refs_v(tasks@));
}

/// One ref of the model's heartbeat.
pub open spec fn ext_step(map: Map<Seq<char>, ObjV>, pid: Seq<char>, r: TaskRef, now: u64) -> Map<Seq<char>, ObjV> {
    if !map.contains_key(r.id@) {
        map
    } else {
        let obj = c::spec_project_obj(map[r.id@], now);
        match obj.task {
            Some(t) if t.state == TaskState::Acquired && t.version == r.version && t.pid == Some(pid) => {
                let ttl = match t.ttl { Some(n) => n, None => 0 };
                map.insert(r.id@, ObjV { task: Some(TkV { lease_timeout_at: Some(echod_concrete::store::spec_sat_add(now, ttl)), ..t }), ..obj })
            },
            _ => map,
        }
    }
}

pub proof fn lemma_extend_unfold(map: Map<Seq<char>, ObjV>, pid: Seq<char>, tasks: Seq<TaskRef>, now: u64, i: int)
    requires
        0 <= i < tasks.len(),
    ensures
        c::spec_extend(map, pid, tasks, now, i) == c::spec_extend(ext_step(map, pid, tasks[i], now), pid, tasks, now, i + 1),
{
}

pub proof fn lemma_extend_shift(map: Map<Seq<char>, ObjV>, pid: Seq<char>, tasks: Seq<TaskRef>, now: u64, i: int)
    requires
        0 <= i,
        tasks.len() >= 1,
    ensures
        c::spec_extend(map, pid, tasks, now, i + 1) == c::spec_extend(map, pid, tasks.drop_first(), now, i),
    decreases tasks.len() - i,
{
    if i + 1 < tasks.len() {
        assert(tasks.drop_first()[i] == tasks[i + 1]);
        lemma_extend_unfold(map, pid, tasks, now, i + 1);
        lemma_extend_unfold(map, pid, tasks.drop_first(), now, i);
        lemma_extend_shift(ext_step(map, pid, tasks[i + 1], now), pid, tasks, now, i + 1);
    }
}

pub proof fn lemma_fold_shift(a: AState, pid: Seq<char>, refs: Seq<ATaskRef>, k: int, now: nat)
    requires
        1 <= k <= refs.len(),
    ensures
        p::spec_heartbeat_fold(a, pid, refs, k, now)
            == p::spec_heartbeat_fold(p::spec_heartbeat_one(a, pid, refs[0], now), pid, refs.drop_first(), k - 1, now),
    decreases k,
{
    let a1 = p::spec_heartbeat_one(a, pid, refs[0], now);
    if k == 1 {
        assert(p::spec_heartbeat_fold(a, pid, refs, 0, now) == a);
        assert(p::spec_heartbeat_fold(a, pid, refs, 1, now) == a1);
        assert(p::spec_heartbeat_fold(a1, pid, refs.drop_first(), 0, now) == a1);
    } else {
        lemma_fold_shift(a, pid, refs, k - 1, now);
        assert(refs.drop_first()[k - 2] == refs[k - 1]);
        assert(p::spec_heartbeat_fold(a, pid, refs, k, now)
            == p::spec_heartbeat_one(p::spec_heartbeat_fold(a, pid, refs, k - 1, now), pid, refs[k - 1], now));
        assert(p::spec_heartbeat_fold(a1, pid, refs.drop_first(), k - 1, now)
            == p::spec_heartbeat_one(p::spec_heartbeat_fold(a1, pid, refs.drop_first(), k - 2, now), pid, refs.drop_first()[k - 2], now));
    }
}

/// A heartbeat keeps every task's version and ttl.
pub proof fn lemma_ext_step_ok(map: Map<Seq<char>, ObjV>, pid: Seq<char>, r: TaskRef, now: u64)
    requires
        doc_ok(DocV::Origin(map)),
    ensures
        doc_ok(DocV::Origin(ext_step(map, pid, r, now))),
{
    let m = ext_step(map, pid, r, now);
    assert forall|id: Seq<char>| #[trigger] m.contains_key(id) implies match m[id].task {
        Some(t) => t.version < MAX_VERSION && (t.ttl is Some ==> t.ttl.unwrap() <= MAX_TIME),
        None => true,
    } by {
        assert(map.contains_key(id));
    }
}

pub proof fn lemma_heartbeat_one(a: AState, map: Map<Seq<char>, ObjV>, pid: Seq<char>, r: TaskRef, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
        doc_ok(DocV::Origin(map)),
        now <= MAX_TIME,
    ensures
        ({
            let b = p::spec_heartbeat_one(a, pid, r@, now as nat);
            objs_rel(b.objects, ext_step(map, pid, r, now), now as nat) && b.schedules == a.schedules
        }),
{
    let id = r.id@;
    if map.contains_key(id) {
        lemma_read(a, map, id, now);
        let b = p::spec_read(a, id, now as nat);
        let obj = c::spec_project_obj(map[id], now);
        match obj.task {
            Some(t) if t.state == TaskState::Acquired && t.version == r.version && t.pid == Some(pid) => {
                let ttl = match t.ttl { Some(n) => n, None => 0 };
                let e = ObjV { task: Some(TkV { lease_timeout_at: Some(echod_concrete::store::spec_sat_add(now, ttl)), ..t }), ..obj };
                let w = b.objects[id].with_task(b.objects[id].task.unwrap().heartbeat(now as nat));
                assert(w == to_prom(id, e));
                lemma_edit_projected(id, obj, now, w, e);
                lemma_write(b.objects, map, now, id, w, e);
            },
            _ => {},
        }
    }
}

pub proof fn lemma_heartbeat_fold(a: AState, map: Map<Seq<char>, ObjV>, pid: Seq<char>, tasks: Seq<TaskRef>, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
        doc_ok(DocV::Origin(map)),
        now <= MAX_TIME,
    ensures
        ({
            let b = p::spec_heartbeat_fold(a, pid, refs_v(tasks), tasks.len() as int, now as nat);
            objs_rel(b.objects, c::spec_extend(map, pid, tasks, now, 0), now as nat) && b.schedules == a.schedules
        }),
    decreases tasks.len(),
{
    if tasks.len() == 0 {
    } else {
        let refs = refs_v(tasks);
        assert(refs[0] == tasks[0]@);
        assert(refs.drop_first() =~= refs_v(tasks.drop_first()));
        lemma_fold_shift(a, pid, refs, tasks.len() as int, now as nat);
        lemma_extend_unfold(map, pid, tasks, now, 0);
        let map1 = ext_step(map, pid, tasks[0], now);
        lemma_extend_shift(map1, pid, tasks, now, 0);
        lemma_heartbeat_one(a, map, pid, tasks[0], now);
        lemma_ext_step_ok(map, pid, tasks[0], now);
        let a1 = p::spec_heartbeat_one(a, pid, refs[0], now as nat);
        lemma_heartbeat_fold(a1, map1, pid, tasks.drop_first(), now);
    }
}

pub proof fn lemma_heartbeat(a: AState, map: Map<Seq<char>, ObjV>, q: TaskHeartbeatReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
        doc_ok(DocV::Origin(map)),
        now <= MAX_TIME,
        q.tasks@.len() > 0 ==> c::spec_one_origin(q.tasks@, echod_types::origin(q.tasks@[0].id@), 0),
    ensures
        ({
            let (b, r) = p::spec_task_heartbeat(a, q@, now as nat);
            let (doc, s) = c::spec_heartbeat(DocV::Origin(map), q.pid, q.tasks@, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Status(r)
        }),
{
    lemma_refs_v(q.tasks);
    lemma_heartbeat_fold(a, map, q.pid@, q.tasks@, now);
}

// ---------------------------------------------------------------------------
// task.suspend
// ---------------------------------------------------------------------------

/// The actions, as the process's handler sees them.
pub open spec fn acts_v(actions: Seq<PromiseRegisterCallbackReq>) -> Seq<APromiseRegisterCallbackReq> {
    actions.map_values(|x: PromiseRegisterCallbackReq| x@)
}

pub proof fn lemma_acts_v(actions: Vec<PromiseRegisterCallbackReq>)
    ensures
        actions.deep_view() == acts_v(actions@),
{
    assert(actions.deep_view() =~= acts_v(actions@));
}

pub proof fn lemma_bad_suspend(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, i: int)
    requires
        0 <= i <= actions.len(),
    ensures
        c::spec_bad_suspend(actions, id, i) == exists|j: int| i <= j < actions.len()
            && (#[trigger] actions[j].awaited@ == id || !echod_types::same_origin_spec(actions[j].awaited@, id)),
    decreases actions.len() - i,
{
    if i < actions.len() {
        lemma_bad_suspend(actions, id, i + 1);
        if actions[i].awaited@ == id || !echod_types::same_origin_spec(actions[i].awaited@, id) {
            assert(actions[i].awaited@ == id || !echod_types::same_origin_spec(actions[i].awaited@, id));
        }
    }
}

pub proof fn lemma_seen(actions: Seq<PromiseRegisterCallbackReq>, x: Seq<char>, j: int, stop: int)
    requires
        0 <= j,
        stop <= actions.len(),
    ensures
        c::spec_seen(actions, x, j, stop) == exists|k: int| j <= k < stop && #[trigger] actions[k].awaited@ == x,
    decreases stop - j,
{
    if j < stop {
        lemma_seen(actions, x, j + 1, stop);
        if actions[j].awaited@ == x {
            assert(actions[j].awaited@ == x);
        }
    }
}

pub proof fn lemma_distinct_awaited(actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        0 <= i <= actions.len(),
    ensures
        c::spec_distinct_awaited(actions, i) == forall|j: int, k: int|
            i <= j < actions.len() && 0 <= k < j ==> #[trigger] actions[k].awaited@ != #[trigger] actions[j].awaited@,
    decreases actions.len() - i,
{
    if i < actions.len() {
        lemma_distinct_awaited(actions, i + 1);
        lemma_seen(actions, actions[i].awaited@, 0, i);
    }
}

/// The door checks of both sides agree.
pub proof fn lemma_doors(q: TaskSuspendReq)
    ensures
        p::suspend_doors(acts_v(q.actions@), q.id@)
            == (q.actions@.len() > 0 && !c::spec_bad_suspend(q.actions@, q.id@, 0) && c::spec_distinct_awaited(q.actions@, 0)),
{
    let actions = q.actions@;
    let acts = acts_v(actions);
    let id = q.id@;
    lemma_bad_suspend(actions, id, 0);
    lemma_distinct_awaited(actions, 0);
    assert(acts.len() == actions.len());
    if p::suspend_doors(acts, id) {
        if c::spec_bad_suspend(actions, id, 0) {
            let j = choose|j: int| 0 <= j < actions.len()
                && (#[trigger] actions[j].awaited@ == id || !echod_types::same_origin_spec(actions[j].awaited@, id));
            assert(acts[j].awaited == actions[j].awaited@);
            assert(false);
        }
        assert forall|j: int, k: int| 0 <= j < actions.len() && 0 <= k < j implies
            #[trigger] actions[k].awaited@ != #[trigger] actions[j].awaited@ by {
            assert(acts[k].awaited == actions[k].awaited@);
            assert(acts[j].awaited == actions[j].awaited@);
        }
    } else if actions.len() > 0 {
        if p::awaited_distinct(acts) {
            let j = choose|j: int| 0 <= j < acts.len()
                && !(#[trigger] acts[j].awaited != id && echod_types::same_origin_spec(acts[j].awaited, id));
            assert(acts[j].awaited == actions[j].awaited@);
            assert(actions[j].awaited@ == id || !echod_types::same_origin_spec(actions[j].awaited@, id));
            assert(c::spec_bad_suspend(actions, id, 0));
        } else {
            let (i, j) = choose|i: int, j: int| 0 <= i < acts.len() && 0 <= j < acts.len()
                && #[trigger] acts[i].awaited == #[trigger] acts[j].awaited && i != j;
            assert(acts[i].awaited == actions[i].awaited@);
            assert(acts[j].awaited == actions[j].awaited@);
            if i < j {
                assert(actions[i].awaited@ == actions[j].awaited@);
            } else {
                assert(actions[j].awaited@ == actions[i].awaited@);
            }
            assert(!c::spec_distinct_awaited(actions, 0));
        }
    }
}

/// `first_failing` finds a failing action iff the model finds one missing or
/// unawaitable. The two sides read tags alike through the relation.
pub proof fn lemma_failing(b: AState, map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, now: u64, k: int)
    requires
        objs_rel(b.objects, map, now as nat),
        0 <= k <= actions.len(),
    ensures
        (p::first_failing(b, acts_v(actions), k) is Some)
            == exists|j: int| 0 <= j < k && #[trigger] p::awaited_fails(b, acts_v(actions)[j]),
        match p::first_failing(b, acts_v(actions), k) {
            Some(j) => 0 <= j < k && p::awaited_fails(b, acts_v(actions)[j]),
            None => true,
        },
        forall|j: int| 0 <= j < actions.len() ==> #[trigger] p::awaited_fails(b, acts_v(actions)[j])
            == (!map.contains_key(actions[j].awaited@)
                || !c::spec_awaitable(map[actions[j].awaited@].promise.tags)),
    decreases k,
{
    let acts = acts_v(actions);
    assert forall|j: int| 0 <= j < actions.len() implies #[trigger] p::awaited_fails(b, acts[j])
        == (!map.contains_key(actions[j].awaited@) || !c::spec_awaitable(map[actions[j].awaited@].promise.tags)) by {
        let w = actions[j].awaited@;
        assert(acts[j].awaited == w);
        if map.contains_key(w) {
            lemma_tags(map[w].promise.tags);
            assert(b.objects[w].project(now as nat).tags == b.objects[w].tags);
            assert(to_prom(w, map[w]).project(now as nat).tags == map[w].promise.tags.deep_view());
        }
    }
    if k > 0 {
        lemma_failing(b, map, actions, now, k - 1);
        if p::first_failing(b, acts, k - 1) is None && p::awaited_fails(b, acts[k - 1]) {
            assert(p::awaited_fails(b, acts[k - 1]));
        }
    }
}

pub proof fn lemma_missing(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        0 <= i <= actions.len(),
    ensures
        c::spec_missing_awaited(map, actions, i) == exists|j: int| i <= j < actions.len() && !map.contains_key(#[trigger] actions[j].awaited@),
        c::spec_unawaitable(map, actions, i) == exists|j: int| i <= j < actions.len()
            && map.contains_key(#[trigger] actions[j].awaited@) && !c::spec_awaitable(map[actions[j].awaited@].promise.tags),
    decreases actions.len() - i,
{
    if i < actions.len() {
        lemma_missing(map, actions, i + 1);
        if !map.contains_key(actions[i].awaited@) {
            assert(!map.contains_key(actions[i].awaited@));
        }
        if map.contains_key(actions[i].awaited@) && !c::spec_awaitable(map[actions[i].awaited@].promise.tags) {
            assert(map.contains_key(actions[i].awaited@) && !c::spec_awaitable(map[actions[i].awaited@].promise.tags));
        }
    }
}

pub proof fn lemma_any_settled(b: AState, map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, now: u64, i: int)
    requires
        objs_rel(b.objects, map, now as nat),
        0 <= i <= actions.len(),
    ensures
        c::spec_any_settled(map, actions, now, i) == exists|j: int| i <= j < actions.len()
            && map.contains_key(#[trigger] actions[j].awaited@)
            && b.objects[actions[j].awaited@].project(now as nat).state != PromiseState::Pending,
    decreases actions.len() - i,
{
    if i < actions.len() {
        lemma_any_settled(b, map, actions, now, i + 1);
        let w = actions[i].awaited@;
        if map.contains_key(w) {
            lemma_project(w, map[w], now);
            if c::spec_project_obj(map[w], now).promise.state != PromiseState::Pending {
                assert(map.contains_key(actions[i].awaited@)
                    && b.objects[actions[i].awaited@].project(now as nat).state != PromiseState::Pending);
            }
        }
    }
}

/// No action among the first `k` awaits `x`.
pub open spec fn untouched(actions: Seq<PromiseRegisterCallbackReq>, k: int, x: Seq<char>) -> bool {
    forall|j: int| 0 <= j < k ==> #[trigger] actions[j].awaited@ != x
}

pub proof fn lemma_untouched_shift(actions: Seq<PromiseRegisterCallbackReq>, k: int, x: Seq<char>)
    requires
        1 <= k <= actions.len(),
        untouched(actions, k, x),
    ensures
        untouched(actions.drop_first(), k - 1, x),
        actions[0].awaited@ != x,
{
    assert forall|j: int| 0 <= j < k - 1 implies #[trigger] actions.drop_first()[j].awaited@ != x by {
        assert(actions.drop_first()[j] == actions[j + 1]);
    }
}

/// The process's reads of the awaited promises keep the relation and touch
/// nothing else.
pub proof fn lemma_awaited_read(b: AState, map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, now: u64, k: int)
    requires
        objs_rel(b.objects, map, now as nat),
        0 <= k <= actions.len(),
    ensures
        ({
            let d = p::spec_awaited_read(b, acts_v(actions), k, now as nat);
            &&& objs_rel(d.objects, map, now as nat)
            &&& d.schedules == b.schedules
            &&& forall|x: Seq<char>| #[trigger] untouched(actions, k, x) ==> p::unchanged_at(b, d, x)
        }),
    decreases k,
{
    let acts = acts_v(actions);
    if k > 0 {
        lemma_awaited_read(b, map, actions, now, k - 1);
        let d0 = p::spec_awaited_read(b, acts, k - 1, now as nat);
        let d = p::spec_awaited_read(b, acts, k, now as nat);
        let w = actions[k - 1].awaited@;
        assert(acts[k - 1].awaited == w);
        if map.contains_key(w) {
            lemma_read(d0, map, w, now);
        }
        assert forall|x: Seq<char>| #[trigger] untouched(actions, k, x) implies p::unchanged_at(b, d, x) by {
            assert(untouched(actions, k - 1, x));
            assert(actions[k - 1].awaited@ != x);
        }
    }
}

/// One awaited promise registered, on both sides.
pub open spec fn reg_step(map: Map<Seq<char>, ObjV>, id: Seq<char>, w: Seq<char>) -> Map<Seq<char>, ObjV> {
    if !map.contains_key(w) {
        map
    } else {
        let obj = map[w];
        let callbacks = if obj.promise.callbacks.contains(id) { obj.promise.callbacks } else { obj.promise.callbacks.push(id) };
        map.insert(w, ObjV { promise: PromV { callbacks, ..obj.promise }, ..obj })
    }
}

pub proof fn lemma_add_callbacks_unfold(map: Map<Seq<char>, ObjV>, id: Seq<char>, actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        0 <= i < actions.len(),
    ensures
        c::spec_add_callbacks(map, id, actions, i) == c::spec_add_callbacks(reg_step(map, id, actions[i].awaited@), id, actions, i + 1),
{
}

pub proof fn lemma_add_callbacks_shift(map: Map<Seq<char>, ObjV>, id: Seq<char>, actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        0 <= i,
        actions.len() >= 1,
    ensures
        c::spec_add_callbacks(map, id, actions, i + 1) == c::spec_add_callbacks(map, id, actions.drop_first(), i),
    decreases actions.len() - i,
{
    if i + 1 < actions.len() {
        assert(actions.drop_first()[i] == actions[i + 1]);
        lemma_add_callbacks_unfold(map, id, actions, i + 1);
        lemma_add_callbacks_unfold(map, id, actions.drop_first(), i);
        lemma_add_callbacks_shift(reg_step(map, id, actions[i + 1].awaited@), id, actions, i + 1);
    }
}

pub proof fn lemma_register_shift(a: AState, acts: Seq<APromiseRegisterCallbackReq>, k: int, id: Seq<char>)
    requires
        1 <= k <= acts.len(),
    ensures
        ({
            let w = acts[0].awaited;
            let a1 = p::with_objects(a, a.objects.insert(w, a.objects[w].add_callback(id)));
            p::spec_awaited_register(a, acts, k, id) == p::spec_awaited_register(a1, acts.drop_first(), k - 1, id)
        }),
    decreases k,
{
    let w = acts[0].awaited;
    let a1 = p::with_objects(a, a.objects.insert(w, a.objects[w].add_callback(id)));
    if k == 1 {
        assert(p::spec_awaited_register(a, acts, 0, id) == a);
        assert(p::spec_awaited_register(a, acts, 1, id) == a1);
        assert(p::spec_awaited_register(a1, acts.drop_first(), 0, id) == a1);
    } else {
        lemma_register_shift(a, acts, k - 1, id);
        assert(acts.drop_first()[k - 2] == acts[k - 1]);
        let s = p::spec_awaited_register(a, acts, k - 1, id);
        assert(p::spec_awaited_register(a, acts, k, id)
            == p::with_objects(s, s.objects.insert(acts[k - 1].awaited, s.objects[acts[k - 1].awaited].add_callback(id))));
        let s1 = p::spec_awaited_register(a1, acts.drop_first(), k - 2, id);
        assert(p::spec_awaited_register(a1, acts.drop_first(), k - 1, id)
            == p::with_objects(s1, s1.objects.insert(acts.drop_first()[k - 2].awaited, s1.objects[acts.drop_first()[k - 2].awaited].add_callback(id))));
    }
}

/// Adding a callback commutes with the projection.
pub proof fn lemma_project_callback(q: APromise, id: Seq<char>, now: nat)
    ensures
        q.add_callback(id).project(now) == q.project(now).add_callback(id),
{
}

pub proof fn lemma_register(s: AState, map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, now: u64)
    requires
        objs_rel(s.objects, map, now as nat),
        forall|j: int| 0 <= j < actions.len() ==> map.contains_key(#[trigger] actions[j].awaited@),
    ensures
        ({
            let d = p::spec_awaited_register(s, acts_v(actions), actions.len() as int, id);
            let m = c::spec_add_callbacks(map, id, actions, 0);
            &&& objs_rel(d.objects, m, now as nat)
            &&& d.schedules == s.schedules
            &&& forall|x: Seq<char>| #[trigger] untouched(actions, actions.len() as int, x)
                ==> p::unchanged_at(s, d, x) && (map.contains_key(x) ==> m.contains_key(x) && m[x] == map[x])
        }),
    decreases actions.len(),
{
    let acts = acts_v(actions);
    if actions.len() > 0 {
        let w = actions[0].awaited@;
        assert(acts[0].awaited == w);
        lemma_register_shift(s, acts, actions.len() as int, id);
        lemma_add_callbacks_unfold(map, id, actions, 0);
        let map1 = reg_step(map, id, w);
        lemma_add_callbacks_shift(map1, id, actions, 0);
        assert(acts.drop_first() =~= acts_v(actions.drop_first()));
        let s1 = p::with_objects(s, s.objects.insert(w, s.objects[w].add_callback(id)));
        let obj = map[w];
        let callbacks = if obj.promise.callbacks.contains(id) { obj.promise.callbacks } else { obj.promise.callbacks.push(id) };
        let e = ObjV { promise: PromV { callbacks, ..obj.promise }, ..obj };
        assert(to_prom(w, e) == to_prom(w, obj).add_callback(id));
        lemma_project_callback(s.objects[w], id, now as nat);
        lemma_project_callback(to_prom(w, obj), id, now as nat);
        lemma_write(s.objects, map, now, w, s.objects[w].add_callback(id), e);
        assert forall|j: int| 0 <= j < actions.drop_first().len() implies map1.contains_key(#[trigger] actions.drop_first()[j].awaited@) by {
            assert(actions.drop_first()[j] == actions[j + 1]);
        }
        lemma_register(s1, map1, actions.drop_first(), id, now);
        let d = p::spec_awaited_register(s, acts, actions.len() as int, id);
        let m = c::spec_add_callbacks(map, id, actions, 0);
        assert forall|x: Seq<char>| #[trigger] untouched(actions, actions.len() as int, x)
            implies p::unchanged_at(s, d, x) && (map.contains_key(x) ==> m.contains_key(x) && m[x] == map[x]) by {
            lemma_untouched_shift(actions, actions.len() as int, x);
            assert(untouched(actions.drop_first(), actions.drop_first().len() as int, x));
        }
    }
}

pub proof fn lemma_suspend(a: AState, map: Map<Seq<char>, ObjV>, q: TaskSuspendReq, now: u64)
    requires
        objs_rel(a.objects, map, now as nat),
    ensures
        ({
            let (b, r) = p::spec_task_suspend(a, q@, now as nat);
            let (doc, s) = c::spec_suspend(DocV::Origin(map), q.id, q.version, q.actions@, now);
            out_rel(a, b, doc, now) && s@ == AResponse::Status(r)
        }),
{
    let id = q.id@;
    let actions = q.actions@;
    let acts = acts_v(actions);
    let n = actions.len() as int;
    lemma_acts_v(q.actions);
    lemma_doors(q);
    if actions.len() == 0 || c::spec_bad_suspend(actions, id, 0) || !c::spec_distinct_awaited(actions, 0) {
    } else {
        lemma_bad_suspend(actions, id, 0);
        lemma_held(a, map, id, q.version, now);
        let (_, held) = c::spec_held(map, id, q.version, now);
        let b = p::spec_read_task(a, id, now as nat);
        match held {
            c::Held::Ok(obj) => {
                let t = obj.task.unwrap();
                lemma_failing(b, map, actions, now, n);
                lemma_missing(map, actions, 0);
                assert(untouched(actions, n, id));
                match p::first_failing(b, acts, n) {
                    Some(j) => {
                        assert(p::awaited_fails(b, acts[j]));
                        assert(acts[j].awaited == actions[j].awaited@);
                        if !map.contains_key(actions[j].awaited@) {
                            assert(c::spec_missing_awaited(map, actions, 0));
                        } else {
                            assert(c::spec_unawaitable(map, actions, 0));
                        }
                        let m = if b.objects.contains_key(acts[j].awaited) { j + 1 } else { j };
                        lemma_awaited_read(b, map, actions, now, m);
                    },
                    None => {
                        if c::spec_missing_awaited(map, actions, 0) {
                            let j = choose|j: int| 0 <= j < n && !map.contains_key(#[trigger] actions[j].awaited@);
                            assert(p::awaited_fails(b, acts[j]));
                            assert(false);
                        }
                        if c::spec_unawaitable(map, actions, 0) {
                            let j = choose|j: int| 0 <= j < n && map.contains_key(#[trigger] actions[j].awaited@)
                                && !c::spec_awaitable(map[actions[j].awaited@].promise.tags);
                            assert(p::awaited_fails(b, acts[j]));
                            assert(false);
                        }
                        assert forall|j: int| 0 <= j < n implies map.contains_key(#[trigger] actions[j].awaited@) by {
                            assert(!p::awaited_fails(b, acts[j]));
                        }
                        lemma_awaited_read(b, map, actions, now, n);
                        let cc = p::spec_awaited_read(b, acts, n, now as nat);
                        assert(p::unchanged_at(b, cc, id));
                        lemma_any_settled(b, map, actions, now, 0);
                        if p::any_settled(b, acts, now as nat) {
                            assert(c::spec_any_settled(map, actions, now, 0));
                            let e = ObjV { task: Some(TkV { resumes: Seq::empty(), ..t }), ..obj };
                            let w = cc.objects[id].with_task(t_of(b, id).clear_resumes());
                            assert(w == to_prom(id, e));
                            lemma_edit_projected(id, obj, now, w, e);
                            lemma_write(cc.objects, map, now, id, w, e);
                        } else {
                            if c::spec_any_settled(map, actions, now, 0) {
                                let j = choose|j: int| 0 <= j < n && map.contains_key(#[trigger] actions[j].awaited@)
                                    && b.objects[actions[j].awaited@].project(now as nat).state != PromiseState::Pending;
                                assert(acts[j].awaited == actions[j].awaited@);
                                assert(p::any_settled(b, acts, now as nat));
                                assert(false);
                            }
                            lemma_register(cc, map, actions, id, now);
                            let d = p::spec_awaited_register(cc, acts, n, id);
                            let m = c::spec_add_callbacks(map, id, actions, 0);
                            assert(p::unchanged_at(cc, d, id));
                            assert(m[id] == map[id]);
                            assert(c::spec_project_obj(map[id], now) == map[id]);
                            let e = ObjV {
                                task: Some(TkV { resumes: Seq::empty(), ..c::spec_unlease(t, TaskState::Suspended, None) }),
                                ..m[id]
                            };
                            let w = d.objects[id].with_task(t_of(b, id).suspend());
                            assert(w == to_prom(id, e));
                            lemma_edit_projected(id, obj, now, w, e);
                            lemma_write(d.objects, m, now, id, w, e);
                        }
                    },
                }
            },
            _ => {},
        }
    }
}

/// The task the process's suspend read.
pub open spec fn t_of(b: AState, id: Seq<char>) -> ATask {
    b.objects[id].task.unwrap()
}

// ---------------------------------------------------------------------------
// Schedules
// ---------------------------------------------------------------------------

pub proof fn lemma_schedule_get(a: AState, slot: Option<Schedule>, q: ScheduleGetReq, now: u64)
    requires
        doc_rel(a, DocV::Schedule(slot), now as nat),
        slot_of(DocV::Schedule(slot), q.id@),
    ensures
        ({
            let (b, r) = p::spec_schedule_get(a, q@, now as nat);
            let (doc, s) = c::spec_schedule_get(DocV::Schedule(slot), q.id);
            doc_rel(b, doc, now as nat) && s@ == AResponse::Schedule(r)
        }),
{
    match slot {
        Some(sch) => {
            assert(a.schedules.contains_key(sch.id@));
            assert(a.schedules[sch.id@] == sch@);
            if sch.id@ == q.id@ {
                echod_abstract::trusted::axiom_string_ext(sch.id, q.id);
            } else {
                assert(!a.schedules.contains_key(q.id@));
            }
        },
        None => {
            assert(!a.schedules.contains_key(q.id@));
        },
    }
}

pub proof fn lemma_schedule_create(a: AState, slot: Option<Schedule>, q: ScheduleCreateReq, now: u64)
    requires
        doc_rel(a, DocV::Schedule(slot), now as nat),
        slot_of(DocV::Schedule(slot), q.id@),
        q.promise_timeout <= MAX_TIME,
        q.next_run_at == echod_abstract::trusted::spec_next_cron(q.cron@, now),
    ensures
        ({
            let (b, r) = p::spec_schedule_create(a, q@, now as nat);
            let (doc, s) = c::spec_schedule_create(DocV::Schedule(slot), q, now);
            doc_rel(b, doc, now as nat) && s@ == AResponse::Schedule(r)
        }),
{
    lemma_tags(q.promise_tags);
    echod_abstract::trusted::axiom_next_cron_after(q.cron@, now);
    if c::spec_targeted(q.promise_tags) && c::spec_timer(q.promise_tags) {
    } else {
        match slot {
            Some(sch) => {
                assert(a.schedules.contains_key(sch.id@));
                assert(a.schedules[sch.id@] == sch@);
            },
            None => {
                assert(!a.schedules.contains_key(q.id@));
                let schedule = Schedule {
                    id: q.id,
                    cron: q.cron,
                    promise_id: q.promise_id,
                    promise_timeout: q.promise_timeout,
                    promise_param: q.promise_param,
                    promise_tags: q.promise_tags,
                    next_run_at: echod_abstract::trusted::spec_next_cron(q.cron@, now),
                    last_run_at: None,
                    created_at: now,
                };
                assert(schedule@ == p::spec_new_schedule(q@, now as nat));
                assert(a.schedules.insert(q.id@, schedule@) =~= sched_map(Some(schedule)));
            },
        }
    }
}

pub proof fn lemma_schedule_delete(a: AState, slot: Option<Schedule>, q: ScheduleDeleteReq, now: u64)
    requires
        doc_rel(a, DocV::Schedule(slot), now as nat),
        slot_of(DocV::Schedule(slot), q.id@),
    ensures
        ({
            let (b, r) = p::spec_schedule_delete(a, q@, now as nat);
            let (doc, s) = c::spec_schedule_delete(DocV::Schedule(slot), q.id);
            doc_rel(b, doc, now as nat) && s@ == AResponse::Status(r)
        }),
{
    match slot {
        Some(sch) => {
            assert(a.schedules.contains_key(sch.id@));
            assert(a.schedules.remove(sch.id@) =~= Map::<Seq<char>, ASchedule>::empty());
            if sch.id@ == q.id@ {
                echod_abstract::trusted::axiom_string_ext(sch.id, q.id);
            } else {
                assert(!a.schedules.contains_key(q.id@));
            }
        },
        None => {
            assert(!a.schedules.contains_key(q.id@));
        },
    }
}

// ---------------------------------------------------------------------------
// Any request
// ---------------------------------------------------------------------------

/// What the two handlers agree on for one request.
pub open spec fn agrees(a: AState, doc: DocV, req: Request, now: u64) -> bool {
    let (b, r) = p::spec_handle(a, req@, now as nat);
    let (next, s) = c::spec_handle(doc, req, now);
    doc_rel(b, next, now as nat) && s@ == r
}

#[verifier::spinoff_prover]
pub proof fn lemma_handle_promise(a: AState, map: Map<Seq<char>, ObjV>, req: Request, now: u64)
    requires
        doc_rel(a, DocV::Origin(map), now as nat),
        req_ok(req, now),
        req is PromiseGet || req is PromiseCreate || req is PromiseSettle
            || req is PromiseRegisterCallback || req is PromiseRegisterListener,
    ensures
        agrees(a, DocV::Origin(map), req, now),
{
    match req {
        Request::PromiseGet(q) => lemma_promise_get(a, map, q, now),
        Request::PromiseCreate(q) => lemma_promise_create(a, map, q, now),
        Request::PromiseSettle(q) => lemma_promise_settle(a, map, q, now),
        Request::PromiseRegisterCallback(q) => lemma_register_callback(a, map, q, now),
        Request::PromiseRegisterListener(q) => lemma_register_listener(a, map, q, now),
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_handle_claim(a: AState, map: Map<Seq<char>, ObjV>, req: Request, now: u64)
    requires
        doc_rel(a, DocV::Origin(map), now as nat),
        req_ok(req, now),
        doc_ok(DocV::Origin(map)),
        now <= MAX_TIME,
        req is TaskGet || req is TaskCreate || req is TaskAcquire || req is TaskFulfill,
    ensures
        agrees(a, DocV::Origin(map), req, now),
{
    match req {
        Request::TaskGet(q) => lemma_task_get(a, map, q, now),
        Request::TaskCreate(q) => lemma_task_create(a, map, q, now),
        Request::TaskAcquire(q) => lemma_task_acquire(a, map, q, now),
        Request::TaskFulfill(q) => lemma_task_fulfill(a, map, q, now),
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_handle_lease(a: AState, map: Map<Seq<char>, ObjV>, req: Request, now: u64)
    requires
        doc_rel(a, DocV::Origin(map), now as nat),
        req_ok(req, now),
        doc_ok(DocV::Origin(map)),
        now <= MAX_TIME,
        req is TaskRelease || req is TaskHalt || req is TaskContinue || req is TaskHeartbeat,
    ensures
        agrees(a, DocV::Origin(map), req, now),
{
    match req {
        Request::TaskRelease(q) => lemma_task_release(a, map, q, now),
        Request::TaskHalt(q) => lemma_task_halt(a, map, q, now),
        Request::TaskContinue(q) => lemma_task_continue(a, map, q, now),
        Request::TaskHeartbeat(q) => lemma_heartbeat(a, map, q, now),
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_handle_fence(a: AState, map: Map<Seq<char>, ObjV>, req: Request, now: u64)
    requires
        doc_rel(a, DocV::Origin(map), now as nat),
        req_ok(req, now),
        req is TaskFence || req is TaskFenceCheck || req is TaskSuspend,
    ensures
        agrees(a, DocV::Origin(map), req, now),
{
    match req {
        Request::TaskFence(q) => lemma_fence(a, map, q, now),
        Request::TaskFenceCheck(q) => lemma_fence_check(a, map, q, now),
        Request::TaskSuspend(q) => lemma_suspend(a, map, q, now),
        _ => {},
    }
}

/// Origin documents: every request the model answers from an origin.
#[verifier::spinoff_prover]
pub proof fn lemma_handle_origin(a: AState, map: Map<Seq<char>, ObjV>, req: Request, now: u64)
    requires
        doc_rel(a, DocV::Origin(map), now as nat),
        kind_ok(DocV::Origin(map), req),
        req_ok(req, now),
        doc_ok(DocV::Origin(map)),
        now <= MAX_TIME,
    ensures
        agrees(a, DocV::Origin(map), req, now),
{
    match req {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => lemma_handle_promise(a, map, req, now),
        Request::TaskGet(_) | Request::TaskCreate(_) | Request::TaskAcquire(_) | Request::TaskFulfill(_) => lemma_handle_claim(a, map, req, now),
        Request::TaskRelease(_) | Request::TaskHalt(_) | Request::TaskContinue(_) | Request::TaskHeartbeat(_) => lemma_handle_lease(a, map, req, now),
        Request::TaskFence(_) | Request::TaskFenceCheck(_) | Request::TaskSuspend(_) => lemma_handle_fence(a, map, req, now),
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) | Request::ScheduleDelete(_) => {},
    }
}

/// Schedule documents: the schedule requests.
#[verifier::spinoff_prover]
pub proof fn lemma_handle_schedule(a: AState, slot: Option<Schedule>, req: Request, now: u64)
    requires
        doc_rel(a, DocV::Schedule(slot), now as nat),
        kind_ok(DocV::Schedule(slot), req),
        req_ok(req, now),
    ensures
        agrees(a, DocV::Schedule(slot), req, now),
{
    match req {
        Request::ScheduleGet(q) => lemma_schedule_get(a, slot, q, now),
        Request::ScheduleCreate(q) => lemma_schedule_create(a, slot, q, now),
        Request::ScheduleDelete(q) => lemma_schedule_delete(a, slot, q, now),
        _ => {},
    }
}

/// On related documents, the process's handler and the model's leave
/// related documents and answer the same response.
pub proof fn lemma_handle_agrees(a: AState, doc: DocV, req: Request, now: u64)
    requires
        doc_rel(a, doc, now as nat),
        kind_ok(doc, req),
        req_ok(req, now),
        doc_ok(doc),
        now <= MAX_TIME,
    ensures
        agrees(a, doc, req, now),
{
    match doc {
        DocV::Origin(map) => lemma_handle_origin(a, map, req, now),
        DocV::Schedule(slot) => lemma_handle_schedule(a, slot, req, now),
    }
}

} // verus!
