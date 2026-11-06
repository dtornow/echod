//! The remaining request handlers agree, each on the document it names.
//!
//! `interpret` proves promise get, create, and settle. This module proves
//! the callbacks and listeners, the task handlers, the heartbeat, the
//! suspend, the fence, and the schedule handlers, and gathers them into
//! [`lemma_requests_agree`]: every request with a key agrees on every
//! related, finite store. Cargo erases these bodies; a Verus run is what
//! checks them.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::interpret::{
    abstract_task, callbacks_in, changed_within, doc_rel, finite_store, lemma_awaitable,
    lemma_contains_to_set, lemma_empty_to_set, lemma_held, lemma_origin_doc, lemma_origin_reads,
    lemma_origin_update, lemma_others_kept_schedule, lemma_others_kept_within, lemma_others_same,
    lemma_project_object, lemma_promise_create_agrees, lemma_promise_handlers_agree,
    lemma_promise_settle_agrees, lemma_push_to_set, lemma_record, lemma_sat_add, lemma_schedule_doc,
    lemma_schedule_key, lemma_string_of, lemma_targeted, lemma_task_record, lemma_timer, object_rel,
    origin_rel, promise_rel, request_agrees, schedule_rel, slot_rel, task_rel,
};
#[cfg(verus_keep_ghost)]
use crate::node::{
    DocumentBodyV, Held, ObjV, PromV, spec_acquire as c_acquire, spec_add_callbacks,
    spec_any_settled as c_any_settled, spec_awaitable, spec_bad_suspend, spec_distinct_awaited,
    spec_extend as c_extend, spec_fence as c_fence, spec_fence_check as c_fence_check,
    spec_fulfill_task, spec_handle, spec_heartbeat as c_heartbeat, spec_held, spec_key,
    spec_missing_awaited, spec_new_obj, spec_one_origin, spec_opened, spec_origin_key,
    spec_workflow_map, spec_project_obj, spec_promise_create as c_promise_create,
    spec_promise_res as c_promise_res, spec_promise_settle as c_promise_settle,
    spec_register_callback as c_register_callback, spec_register_listener as c_register_listener,
    spec_schedule_create as c_schedule_create, spec_schedule_delete as c_schedule_delete,
    spec_schedule_get as c_schedule_get, spec_schedule_key, spec_seen, spec_suspend as c_suspend,
    spec_targeted, spec_task_acquire as c_task_acquire, spec_task_continue as c_task_continue,
    spec_task_create as c_task_create, spec_task_fulfill as c_task_fulfill,
    spec_task_get as c_task_get, spec_task_halt as c_task_halt, spec_task_release as c_task_release,
    spec_timer, spec_unawaitable, spec_unlease as c_unlease, spec_with_workflow, TkV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::machine::{
    spec_acquire as a_acquire, spec_any_settled as a_any_settled, spec_awaited,
    spec_callbacks as a_callbacks, spec_claim_res, spec_extend as a_extend, spec_external,
    spec_fence as a_fence, spec_fence_res, spec_fulfill, spec_handler, spec_has_target,
    spec_heartbeat as a_heartbeat, spec_held as a_held, spec_is_timer, spec_out,
    spec_project_promise, spec_project_task, spec_promise_create as a_promise_create,
    spec_promise_record, spec_promise_res as a_promise_res, spec_promise_settle as a_promise_settle,
    spec_refs_one_origin, spec_register_callback as a_register_callback,
    spec_register_listener as a_register_listener, spec_schedule_create as a_schedule_create,
    spec_schedule_res, spec_schedule_value, spec_settle, spec_status_res, spec_suspend as a_suspend,
    spec_task_acquire as a_task_acquire, spec_task_continue as a_task_continue,
    spec_task_create as a_task_create, spec_task_fulfill as a_task_fulfill, spec_task_get_res,
    spec_task_halt as a_task_halt, spec_task_record as a_task_record,
    spec_task_release as a_task_release, spec_unlease as a_unlease, spec_wrap_fence, SpecHeld,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::trusted::axiom_string_ext;
#[cfg(verus_keep_ghost)]
use echod_abstract::view::{
    all_in_origin, distinct, OutV, PromiseV, sat_add, ScheduleV, StoreV as AStore, TaskV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::ServerConfig;
#[cfg(verus_keep_ghost)]
use echod_rover::Time;
#[cfg(verus_keep_ghost)]
use echod_types::{
    origin, PromiseRegisterCallbackReq, PromiseRes, PromiseState, Request, Response,
    same_origin_spec, Schedule, ScheduleCreateReq, ScheduleRes, StatusRes, TaskClaimRes,
    TaskFenceAction, TaskFenceInnerRes, TaskFenceRes, TaskGetRes, TaskRef, TaskState,
};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

// ---------------------------------------------------------------------------
// Sequences
// ---------------------------------------------------------------------------

/// Pushing an absent element keeps a sequence free of duplicates.
pub proof fn lemma_push_no_duplicates(s: Seq<Seq<char>>, x: Seq<char>)
    requires
        s.no_duplicates(),
        !s.contains(x),
    ensures
        s.push(x).no_duplicates(),
{
    let pushed = s.push(x);
    assert forall|i: int, j: int| 0 <= i < pushed.len() && 0 <= j < pushed.len() && i != j implies pushed[i]
        != pushed[j] by {
        if i < s.len() && j < s.len() {
            assert(pushed[i] == s[i]);
            assert(pushed[j] == s[j]);
        } else if i < s.len() {
            assert(pushed[j] == x);
            assert(pushed[i] == s[i]);
            assert(s.contains(s[i]));
        } else {
            assert(pushed[i] == x);
            assert(pushed[j] == s[j]);
            assert(s.contains(s[j]));
        }
    };
}

/// Dropping the head keeps a sequence free of duplicates.
pub proof fn lemma_skip_no_duplicates(s: Seq<Seq<char>>)
    requires
        s.no_duplicates(),
        s.len() > 0,
    ensures
        s.skip(1).no_duplicates(),
        s.skip(1).to_set() == s.to_set().remove(s[0]),
        !s.skip(1).contains(s[0]),
{
    let rest = s.skip(1);
    assert forall|i: int, j: int| 0 <= i < rest.len() && 0 <= j < rest.len() && i != j implies rest[i]
        != rest[j] by {
        assert(rest[i] == s[i + 1]);
        assert(rest[j] == s[j + 1]);
    };
    assert forall|y: Seq<char>| rest.to_set().contains(y) == s.to_set().remove(s[0]).contains(y) by {
        if rest.contains(y) {
            let i = choose|i: int| 0 <= i < rest.len() && rest[i] == y;
            assert(s[i + 1] == y);
            assert(s.contains(y));
            assert(y != s[0]);
        }
        if s.contains(y) && y != s[0] {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == y;
            assert(i != 0);
            assert(rest[i - 1] == y);
            assert(rest.contains(y));
        }
    };
    assert(rest.to_set() =~= s.to_set().remove(s[0]));
    if rest.contains(s[0]) {
        let i = choose|i: int| 0 <= i < rest.len() && rest[i] == s[0];
        assert(s[i + 1] == s[0]);
        assert(false);
    }
}

/// Adding a callback on both sides: a push when absent, a set insert.
pub proof fn lemma_add_callback(callbacks: Seq<Seq<char>>, set: Set<Seq<char>>, x: Seq<char>)
    requires
        callbacks.no_duplicates(),
        set == callbacks.to_set(),
    ensures
        ({
            let added = if callbacks.contains(x) { callbacks } else { callbacks.push(x) };
            &&& added.to_set() == set.insert(x)
            &&& added.no_duplicates()
        }),
{
    lemma_contains_to_set(callbacks, x);
    if callbacks.contains(x) {
        assert(set.insert(x) =~= set);
    } else {
        lemma_push_to_set(callbacks, x);
        lemma_push_no_duplicates(callbacks, x);
    }
}

// ---------------------------------------------------------------------------
// Stores kept at an id
// ---------------------------------------------------------------------------

/// Re-inserting what is stored changes nothing.
pub proof fn lemma_tasks_kept(s: AStore, id: Seq<char>)
    ensures
        s.tasks == match abstract_task(s, id) {
            Some(task) => s.tasks.insert(id, task),
            None => s.tasks.remove(id),
        },
{
    match abstract_task(s, id) {
        Some(task) => {
            assert(s.tasks.insert(id, task) =~= s.tasks);
        },
        None => {
            assert(s.tasks.remove(id) =~= s.tasks);
        },
    }
}

pub proof fn lemma_promises_kept(s: AStore, id: Seq<char>)
    requires
        s.promises.contains_key(id),
    ensures
        s.promises.insert(id, s.promises[id]) == s.promises,
{
    assert(s.promises.insert(id, s.promises[id]) =~= s.promises);
}

/// A store changed at one id of the origin is changed within the origin.
pub proof fn lemma_within_one(s: AStore, next: AStore, id: Seq<char>)
    requires
        forall|other: Seq<char>|
            other != id ==> #[trigger] next.promises.contains_key(other) == s.promises.contains_key(other)
                && (s.promises.contains_key(other) ==> next.promises[other] == s.promises[other]),
        forall|other: Seq<char>|
            other != id ==> #[trigger] next.tasks.contains_key(other) == s.tasks.contains_key(other)
                && (s.tasks.contains_key(other) ==> next.tasks[other] == s.tasks[other]),
    ensures
        changed_within(s, next, origin(id)),
{
    assert forall|other: Seq<char>| #![trigger origin(other)] origin(other) != origin(id) implies {
        &&& s.promises.contains_key(other) == next.promises.contains_key(other)
        &&& (s.promises.contains_key(other) ==> s.promises[other] == next.promises[other])
        &&& s.tasks.contains_key(other) == next.tasks.contains_key(other)
        &&& (s.tasks.contains_key(other) ==> s.tasks[other] == next.tasks[other])
    } by {
        assert(other != id);
    };
}

/// The finiteness of a store changed at one id.
pub proof fn lemma_finite_at(s: AStore, next: AStore, id: Seq<char>)
    requires
        finite_store(s),
        next.schedules == s.schedules,
        next.promises == s.promises || next.promises.dom() == s.promises.dom().insert(id),
        next.tasks == s.tasks || next.tasks.dom() == s.tasks.dom().insert(id),
    ensures
        finite_store(next),
{
}

// ---------------------------------------------------------------------------
// Callbacks and listeners
// ---------------------------------------------------------------------------

pub proof fn lemma_register_callback_agrees(
    config: ServerConfig,
    req: PromiseRegisterCallbackReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.awaited@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::PromiseRegisterCallback(req),
            spec_origin_key(origin(req.awaited@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::PromiseRegisterCallback(req);
    let awaited = req.awaited;
    let awaiter = req.awaiter;
    let o = origin(awaited@);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_register_callback(doc, awaited, awaiter, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_register_callback(awaited, awaiter, s, now));
    if awaited@ == awaiter@ || !same_origin_spec(awaited@, awaiter@) {
        assert(outs == spec_out(a_promise_res(400, None), s));
        assert(c_register_callback(doc, awaited, awaiter, now) == (doc, c_promise_res(400, None)));
        lemma_others_same(key, s);
    } else {
        assert(origin(awaiter@) == o);
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        if !map.contains_key(awaited@) {
            assert(!s.promises.contains_key(awaited@));
            assert(outs == spec_out(a_promise_res(404, None), s));
            lemma_others_same(key, s);
        } else if !map.contains_key(awaiter@) {
            assert(s.promises.contains_key(awaited@));
            assert(!s.promises.contains_key(awaiter@));
            assert(outs == spec_out(a_promise_res(422, None), s));
            lemma_others_same(key, s);
        } else {
            let p0 = s.promises[awaited@];
            let w0 = s.promises[awaiter@];
            let ta = abstract_task(s, awaited@);
            lemma_project_object(map[awaited@], p0, ta, now);
            lemma_project_object(map[awaiter@], w0, abstract_task(s, awaiter@), now);
            let ao = spec_project_obj(map[awaited@], now);
            let wo = spec_project_obj(map[awaiter@], now);
            let p = spec_project_promise(p0, now);
            let w = spec_project_promise(w0, now);
            assert(promise_rel(ao.promise, p));
            assert(promise_rel(wo.promise, w));
            lemma_targeted(wo.promise.tags);
            lemma_awaitable(ao.promise, p);
            if !spec_targeted(wo.promise.tags) || !spec_awaitable(ao.promise.tags) {
                assert(outs == spec_out(a_promise_res(422, None), s));
                lemma_others_same(key, s);
            } else {
                lemma_record(awaited, ao.promise, p);
                let res = a_promise_res(200, Some(spec_promise_record(awaited, p)));
                assert(c_promise_res(200, Some(crate::node::spec_record(awaited, ao.promise))) == res);
                if ao.promise.state == PromiseState::Pending && wo.promise.state == PromiseState::Pending {
                    assert(ao == map[awaited@]);
                    assert(p == p0);
                    let callbacks = if ao.promise.callbacks.contains(awaiter@) {
                        ao.promise.callbacks
                    } else {
                        ao.promise.callbacks.push(awaiter@)
                    };
                    lemma_add_callback(ao.promise.callbacks, p.callbacks, awaiter@);
                    let obj2 = ObjV { promise: PromV { callbacks, ..ao.promise }, ..ao };
                    let q = PromiseV { callbacks: p.callbacks.insert(awaiter@), ..p };
                    assert(promise_rel(obj2.promise, q));
                    assert(object_rel(obj2, q, ta));
                    assert forall|k: int| 0 <= k < callbacks.len() implies origin(#[trigger] callbacks[k]) == o by {
                        if k < ao.promise.callbacks.len() {
                            assert(callbacks[k] == ao.promise.callbacks[k]);
                        } else {
                            assert(callbacks[k] == awaiter@);
                        }
                    };
                    let next = AStore { promises: s.promises.insert(awaited@, q), ..s };
                    assert(outs == spec_out(res, next));
                    lemma_tasks_kept(s, awaited@);
                    lemma_origin_update(map, o, s, awaited@, obj2, q, ta, next);
                    assert(map.insert(awaited@, obj2).dom() == map.dom().insert(awaited@));
                    lemma_origin_reads(key, o, map.insert(awaited@, obj2), next);
                    assert(c_register_callback(doc, awaited, awaiter, now).0 == DocumentBodyV::Workflow(map.insert(awaited@, obj2)));
                    lemma_within_one(s, next, awaited@);
                    lemma_others_kept_within(s, next, o);
                    assert(next.promises.dom() == s.promises.dom().insert(awaited@));
                    lemma_finite_at(s, next, awaited@);
                } else {
                    assert(outs == spec_out(res, s));
                    lemma_others_same(key, s);
                }
            }
        }
    }
}

pub proof fn lemma_register_listener_agrees(
    config: ServerConfig,
    req: echod_types::PromiseRegisterListenerReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.awaited@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::PromiseRegisterListener(req),
            spec_origin_key(origin(req.awaited@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::PromiseRegisterListener(req);
    let awaited = req.awaited;
    let address = req.address;
    let o = origin(awaited@);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_register_listener(doc, awaited, address, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_register_listener(awaited, address, s, now));
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(awaited@) {
        assert(!s.promises.contains_key(awaited@));
        assert(outs == spec_out(a_promise_res(404, None), s));
        lemma_others_same(key, s);
    } else {
        let p0 = s.promises[awaited@];
        let ta = abstract_task(s, awaited@);
        lemma_project_object(map[awaited@], p0, ta, now);
        let ao = spec_project_obj(map[awaited@], now);
        let p = spec_project_promise(p0, now);
        assert(promise_rel(ao.promise, p));
        lemma_awaitable(ao.promise, p);
        if !spec_awaitable(ao.promise.tags) {
            assert(outs == spec_out(a_promise_res(422, None), s));
            lemma_others_same(key, s);
        } else {
            lemma_record(awaited, ao.promise, p);
            let res = a_promise_res(200, Some(spec_promise_record(awaited, p)));
            if ao.promise.state == PromiseState::Pending {
                assert(ao == map[awaited@]);
                assert(p == p0);
                let listeners = if ao.promise.listeners.contains(address@) {
                    ao.promise.listeners
                } else {
                    ao.promise.listeners.push(address@)
                };
                lemma_add_callback(ao.promise.listeners, p.listeners, address@);
                let obj2 = ObjV { promise: PromV { listeners, ..ao.promise }, ..ao };
                let q = PromiseV { listeners: p.listeners.insert(address@), ..p };
                assert(promise_rel(obj2.promise, q));
                assert(object_rel(obj2, q, ta));
                assert(obj2.promise.callbacks == map[awaited@].promise.callbacks);
                let next = AStore { promises: s.promises.insert(awaited@, q), ..s };
                assert(outs == spec_out(res, next));
                lemma_tasks_kept(s, awaited@);
                lemma_origin_update(map, o, s, awaited@, obj2, q, ta, next);
                assert(map.insert(awaited@, obj2).dom() == map.dom().insert(awaited@));
                lemma_origin_reads(key, o, map.insert(awaited@, obj2), next);
                assert(c_register_listener(doc, awaited, address, now).0 == DocumentBodyV::Workflow(map.insert(awaited@, obj2)));
                lemma_within_one(s, next, awaited@);
                lemma_others_kept_within(s, next, o);
                assert(next.promises.dom() == s.promises.dom().insert(awaited@));
                lemma_finite_at(s, next, awaited@);
            } else {
                assert(outs == spec_out(res, s));
                lemma_others_same(key, s);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tasks
// ---------------------------------------------------------------------------

/// A projected object whose task is not fulfilled is the stored object: its
/// promise is pending, and so is the abstract projection.
pub proof fn lemma_unfulfilled_is_stored(obj: ObjV, p: PromiseV, t: Option<TaskV>, now: Time)
    requires
        object_rel(obj, p, t),
        obj.task is Some,
        spec_project_obj(obj, now).task.unwrap().state != TaskState::Fulfilled,
    ensures
        spec_project_obj(obj, now) == obj,
        obj.promise.state == PromiseState::Pending,
        spec_project_promise(p, now) == p,
        t is Some,
        spec_project_task(t.unwrap(), spec_project_promise(p, now)) == t.unwrap(),
{
    let seen = spec_project_obj(obj, now);
    let ct = obj.task.unwrap();
    if seen.promise.state != PromiseState::Pending {
        if ct.state != TaskState::Fulfilled {
            assert(seen.task == Some(spec_fulfill_task(ct)));
            assert(false);
        } else {
            assert(seen.task == obj.task);
            assert(false);
        }
    }
    assert(seen.promise.state == PromiseState::Pending);
    assert(obj.promise.state == PromiseState::Pending);
    assert(seen.promise == obj.promise);
    assert(seen.task == obj.task);
}

/// Acquiring on both sides relates.
pub proof fn lemma_acquire_rel(ct: TkV, at: TaskV, pid: Seq<char>, ttl: u64, now: Time)
    requires
        task_rel(ct, at),
    ensures
        task_rel(c_acquire(ct, pid, ttl, now), a_acquire(at, sat_add(at.version, 1), pid, ttl, now)),
{
    lemma_sat_add(ct.version, 1);
    lemma_sat_add(now, ttl);
}

pub proof fn lemma_task_get_agrees(config: ServerConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_origin_key(origin(id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskGet(echod_types::TaskGetReq { id }),
            spec_origin_key(origin(id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskGet(echod_types::TaskGetReq { id });
    let o = origin(id@);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_get(doc, id, now));
    let outs = spec_handler(config, request, s, now);
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(id@) {
        assert(!s.promises.contains_key(id@));
        assert(!s.tasks.contains_key(id@));
        assert(outs == spec_out(spec_task_get_res(404, None), s));
    } else {
        let p = s.promises[id@];
        let ta = abstract_task(s, id@);
        lemma_project_object(map[id@], p, ta, now);
        let seen = spec_project_obj(map[id@], now);
        match (map[id@].task, ta) {
            (None, None) => {
                assert(!s.tasks.contains_key(id@));
                assert(outs == spec_out(spec_task_get_res(404, None), s));
            },
            (Some(ct), Some(at)) => {
                assert(s.tasks.contains_key(id@));
                let seen_c = seen.task.unwrap();
                let seen_a = spec_project_task(at, spec_project_promise(p, now));
                assert(task_rel(seen_c, seen_a));
                lemma_task_record(id, seen_c, seen_a);
                assert(outs == spec_out(spec_task_get_res(200, Some(a_task_record(id, seen_a))), s));
            },
            _ => {
                assert(false);
            },
        }
    }
    assert(outs[0].next == s);
    lemma_others_same(key, s);
}

pub proof fn lemma_task_create_agrees(
    config: ServerConfig,
    req: echod_types::TaskCreateReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.action.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskCreate(req),
            spec_origin_key(origin(req.action.id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskCreate(req);
    let action = req.action;
    let x = action.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    let pid = req.pid;
    let ttl = req.ttl;
    assert(spec_handle(doc, request, now) == c_task_create(doc, pid, ttl, action, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_create(pid, ttl, action, s, now));
    lemma_targeted(action.tags);
    lemma_timer(action.tags);
    if !spec_targeted(action.tags) || spec_timer(action.tags) {
        assert(outs == spec_out(spec_claim_res(400, None, None), s));
        assert(c_task_create(doc, pid, ttl, action, now) == (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None })));
        lemma_others_same(key, s);
    } else {
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        let (doc1, created) = c_promise_create(doc, action, now);
        if map.contains_key(x) {
            assert(doc1 == doc);
            assert(s.promises.contains_key(x));
            let p = s.promises[x];
            let ta = abstract_task(s, x);
            lemma_project_object(map[x], p, ta, now);
            let seen = spec_project_obj(map[x], now);
            let seen_p = spec_project_promise(p, now);
            assert(promise_rel(seen.promise, seen_p));
            assert(seen.promise.tags == p.tags);
            lemma_targeted(seen.promise.tags);
            if !spec_targeted(seen.promise.tags) {
                assert(outs == spec_out(spec_claim_res(422, None, None), s));
                lemma_others_same(key, s);
            } else {
                match (map[x].task, ta) {
                    (None, None) => {
                        assert(!s.tasks.contains_key(x));
                        assert(seen.task is None);
                        assert(outs == spec_out(spec_claim_res(409, None, None), s));
                        lemma_others_same(key, s);
                    },
                    (Some(ct), Some(stored)) => {
                        assert(s.tasks.contains_key(x));
                        assert(s.tasks[x] == stored);
                        let t = seen.task.unwrap();
                        let seen_t = spec_project_task(stored, seen_p);
                        assert(task_rel(t, seen_t));
                        if t.state == TaskState::Fulfilled {
                            lemma_task_record(action.id, t, seen_t);
                            lemma_record(action.id, seen.promise, seen_p);
                            assert(outs[0].next == s);
                            lemma_others_same(key, s);
                        } else if t.state == TaskState::Pending {
                            lemma_unfulfilled_is_stored(map[x], p, ta, now);
                            assert(seen == map[x]);
                            assert(seen_p == p);
                            assert(seen_t == stored);
                            let u_c = c_acquire(t, pid@, ttl, now);
                            let u_a = a_acquire(stored, sat_add(stored.version, 1), pid@, ttl, now);
                            lemma_acquire_rel(t, stored, pid@, ttl, now);
                            let obj2 = ObjV { task: Some(u_c), ..seen };
                            let n = AStore { tasks: s.tasks.insert(x, u_a), ..s };
                            assert(object_rel(obj2, p, Some(u_a)));
                            assert(obj2.promise.callbacks == map[x].promise.callbacks);
                            lemma_promises_kept(s, x);
                            lemma_origin_update(map, o, s, x, obj2, p, Some(u_a), n);
                            assert(map.insert(x, obj2).dom() == map.dom().insert(x));
                            lemma_origin_reads(key, o, map.insert(x, obj2), n);
                            lemma_task_record(action.id, u_c, u_a);
                            lemma_record(action.id, obj2.promise, seen_p);
                            assert(outs == spec_out(
                                spec_claim_res(200, Some(a_task_record(action.id, u_a)), Some(spec_promise_record(action.id, seen_p))),
                                n,
                            ));
                            assert(c_task_create(doc, pid, ttl, action, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                            lemma_within_one(s, n, x);
                            lemma_others_kept_within(s, n, o);
                            assert(n.tasks.dom() == s.tasks.dom().insert(x));
                            lemma_finite_at(s, n, x);
                        } else {
                            assert(outs == spec_out(spec_claim_res(409, None, None), s));
                            lemma_others_same(key, s);
                        }
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        } else {
            assert(!s.promises.contains_key(x));
            assert(!s.tasks.contains_key(x));
            let obj = spec_new_obj(action.timeout_at, now, action.param, action.tags, true);
            assert(spec_targeted(action.tags));
            assert(doc1 == spec_with_workflow(doc, map.insert(x, obj)));
            assert(doc1 == DocumentBodyV::Workflow(map.insert(x, obj)));
            let map1 = map.insert(x, obj);
            assert(map1.contains_key(x));
            assert(map1[x] == obj);
            let seen = spec_project_obj(obj, now);
            assert(seen.promise.tags == action.tags);
            lemma_targeted(seen.promise.tags);
            assert(obj.task is Some);
            lemma_empty_to_set();
            let live = action.timeout_at > now;
            let p_a = PromiseV {
                state: if live { PromiseState::Pending } else { PromiseState::RejectedTimedout },
                value: echod_abstract::machine::spec_empty_value(),
                param: action.param,
                timeout_at: action.timeout_at,
                created_at: if live { now } else { action.timeout_at },
                settled_at: if live { None } else { Some(action.timeout_at) },
                tags: action.tags,
                callbacks: Set::empty(),
                listeners: Set::empty(),
            };
            let born = TaskV {
                state: TaskState::Fulfilled,
                version: 0,
                pid: None,
                ttl: None,
                acquired_at: 0,
                retry_timeout_at: None,
                resumes: Seq::empty(),
            };
            assert(promise_rel(obj.promise, p_a));
            assert forall|k: int| 0 <= k < obj.promise.callbacks.len() implies origin(#[trigger] obj.promise.callbacks[k]) == o by {};
            if live {
                let t = obj.task.unwrap();
                assert(t.state == TaskState::Pending);
                assert(seen == obj);
                assert(seen.task.unwrap() == t);
                let u_c = c_acquire(t, pid@, ttl, now);
                let t_a = a_acquire(born, 1, pid@, ttl, now);
                lemma_sat_add(0, 1);
                lemma_sat_add(now, ttl);
                assert(task_rel(u_c, t_a));
                let obj2 = ObjV { task: Some(u_c), ..seen };
                assert(object_rel(obj2, p_a, Some(t_a)));
                let n = AStore { promises: s.promises.insert(x, p_a), tasks: s.tasks.insert(x, t_a), ..s };
                assert(outs == spec_out(
                    spec_claim_res(200, Some(a_task_record(action.id, t_a)), Some(spec_promise_record(action.id, p_a))),
                    n,
                ));
                lemma_task_record(action.id, u_c, t_a);
                lemma_record(action.id, obj2.promise, p_a);
                lemma_origin_update(map, o, s, x, obj2, p_a, Some(t_a), n);
                assert(map1.insert(x, obj2) =~= map.insert(x, obj2));
                assert(c_task_create(doc, pid, ttl, action, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                assert(map.insert(x, obj2).dom() == map.dom().insert(x));
                lemma_origin_reads(key, o, map.insert(x, obj2), n);
                lemma_within_one(s, n, x);
                lemma_others_kept_within(s, n, o);
                assert(n.promises.dom() == s.promises.dom().insert(x));
                assert(n.tasks.dom() == s.tasks.dom().insert(x));
                lemma_finite_at(s, n, x);
            } else {
                let t = obj.task.unwrap();
                assert(t.state == TaskState::Fulfilled);
                assert(obj.promise.state == PromiseState::RejectedTimedout);
                assert(seen == obj);
                assert(task_rel(t, born));
                assert(object_rel(obj, p_a, Some(born)));
                let n = AStore { promises: s.promises.insert(x, p_a), tasks: s.tasks.insert(x, born), ..s };
                assert(outs == spec_out(
                    spec_claim_res(200, Some(a_task_record(action.id, born)), Some(spec_promise_record(action.id, p_a))),
                    n,
                ));
                lemma_task_record(action.id, t, born);
                lemma_record(action.id, obj.promise, p_a);
                lemma_origin_update(map, o, s, x, obj, p_a, Some(born), n);
                assert(c_task_create(doc, pid, ttl, action, now).0 == doc1);
                assert(map1.dom() == map.dom().insert(x));
                lemma_origin_reads(key, o, map1, n);
                lemma_within_one(s, n, x);
                lemma_others_kept_within(s, n, o);
                assert(n.promises.dom() == s.promises.dom().insert(x));
                assert(n.tasks.dom() == s.tasks.dom().insert(x));
                lemma_finite_at(s, n, x);
            }
        }
    }
}

pub proof fn lemma_task_acquire_agrees(
    config: ServerConfig,
    req: echod_types::TaskAcquireReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskAcquire(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskAcquire(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_acquire(doc, req.id, req.version, req.pid, req.ttl, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_acquire(req.id, req.version, req.pid, req.ttl, s, now));
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(x) {
        assert(!s.promises.contains_key(x));
        assert(!s.tasks.contains_key(x));
        assert(outs == spec_out(spec_claim_res(404, None, None), s));
        lemma_others_same(key, s);
    } else {
        let p = s.promises[x];
        let ta = abstract_task(s, x);
        lemma_project_object(map[x], p, ta, now);
        let seen = spec_project_obj(map[x], now);
        let seen_p = spec_project_promise(p, now);
        match (map[x].task, ta) {
            (None, None) => {
                assert(!s.tasks.contains_key(x));
                assert(outs == spec_out(spec_claim_res(404, None, None), s));
                lemma_others_same(key, s);
            },
            (Some(ct), Some(stored)) => {
                assert(s.tasks.contains_key(x));
                let t = seen.task.unwrap();
                let seen_t = spec_project_task(stored, seen_p);
                assert(task_rel(t, seen_t));
                assert(seen_t.version == stored.version);
                if t.state != TaskState::Pending || t.version != req.version || seen.promise.state != PromiseState::Pending {
                    assert(outs == spec_out(spec_claim_res(409, None, None), s));
                    lemma_others_same(key, s);
                } else {
                    lemma_unfulfilled_is_stored(map[x], p, ta, now);
                    assert(seen == map[x]);
                    assert(seen_p == p);
                    assert(seen_t == stored);
                    let u_c = c_acquire(t, req.pid@, req.ttl, now);
                    let u_a = a_acquire(stored, sat_add(stored.version, 1), req.pid@, req.ttl, now);
                    lemma_acquire_rel(t, stored, req.pid@, req.ttl, now);
                    let obj2 = ObjV { task: Some(u_c), ..seen };
                    let n = AStore { tasks: s.tasks.insert(x, u_a), ..s };
                    assert(object_rel(obj2, p, Some(u_a)));
                    assert(obj2.promise.callbacks == map[x].promise.callbacks);
                    lemma_promises_kept(s, x);
                    lemma_origin_update(map, o, s, x, obj2, p, Some(u_a), n);
                    assert(map.insert(x, obj2).dom() == map.dom().insert(x));
                    lemma_origin_reads(key, o, map.insert(x, obj2), n);
                    lemma_task_record(req.id, u_c, u_a);
                    lemma_record(req.id, obj2.promise, p);
                    assert(outs == spec_out(
                        spec_claim_res(200, Some(a_task_record(req.id, u_a)), Some(spec_promise_record(req.id, p))),
                        n,
                    ));
                    assert(c_task_acquire(doc, req.id, req.version, req.pid, req.ttl, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                    lemma_within_one(s, n, x);
                    lemma_others_kept_within(s, n, o);
                    assert(n.tasks.dom() == s.tasks.dom().insert(x));
                    lemma_finite_at(s, n, x);
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

/// The held object, released, fulfilled, or kept: one object replaced.
pub proof fn lemma_held_update(
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    s: AStore,
    x: Seq<char>,
    obj2: ObjV,
    q: PromiseV,
    u: TaskV,
)
    requires
        key == spec_origin_key(o),
        map.dom().finite(),
        finite_store(s),
        origin_rel(map, o, s),
        origin(x) == o,
        map.contains_key(x),
        s.promises.contains_key(x),
        s.tasks.contains_key(x),
        object_rel(obj2, q, Some(u)),
        callbacks_in(obj2.promise.callbacks, o),
    ensures
        ({
            let n = AStore { promises: s.promises.insert(x, q), tasks: s.tasks.insert(x, u), ..s };
            &&& doc_rel(key, DocumentBodyV::Workflow(map.insert(x, obj2)), n)
            &&& crate::interpret::others_kept(key, s, n)
            &&& finite_store(n)
        }),
{
    let n = AStore { promises: s.promises.insert(x, q), tasks: s.tasks.insert(x, u), ..s };
    lemma_origin_update(map, o, s, x, obj2, q, Some(u), n);
    assert(map.insert(x, obj2).dom() == map.dom().insert(x));
    lemma_origin_reads(key, o, map.insert(x, obj2), n);
    lemma_within_one(s, n, x);
    lemma_others_kept_within(s, n, o);
    assert(n.promises.dom() == s.promises.dom().insert(x));
    assert(n.tasks.dom() == s.tasks.dom().insert(x));
    lemma_finite_at(s, n, x);
}

pub proof fn lemma_task_release_agrees(
    config: ServerConfig,
    req: echod_types::TaskReleaseReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskRelease(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskRelease(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_release(doc, req.id, req.version, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_release(req.id, req.version, s, now));
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    lemma_held(map, o, s, x, req.version, now);
    let (_, held) = spec_held(map, x, req.version, now);
    assert(spec_with_workflow(doc, map) == doc);
    match held {
        Held::Missing => {
            assert(outs == spec_out(spec_status_res(404), s));
            lemma_others_same(key, s);
        },
        Held::Stale => {
            assert(outs == spec_out(spec_status_res(409), s));
            lemma_others_same(key, s);
        },
        Held::Ok(obj) => {
            let t = obj.task.unwrap();
            let t_a = s.tasks[x];
            let u_c = c_unlease(t, TaskState::Pending, Some(now));
            let u_a = a_unlease(t_a, TaskState::Pending, Some(now));
            assert(task_rel(u_c, u_a));
            let obj2 = ObjV { task: Some(u_c), ..obj };
            let p = s.promises[x];
            assert(object_rel(obj2, p, Some(u_a)));
            lemma_promises_kept(s, x);
            let n = AStore { promises: s.promises.insert(x, p), tasks: s.tasks.insert(x, u_a), ..s };
            assert(n == AStore { tasks: s.tasks.insert(x, u_a), ..s });
            assert(outs == spec_out(spec_status_res(200), n));
            lemma_held_update(key, o, map, s, x, obj2, p, u_a);
            assert(c_task_release(doc, req.id, req.version, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
        },
    }
}

pub proof fn lemma_task_fulfill_agrees(
    config: ServerConfig,
    req: echod_types::TaskFulfillReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskFulfill(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskFulfill(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    let action = req.action;
    assert(spec_handle(doc, request, now) == c_task_fulfill(doc, req.id, req.version, action, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_fulfill(req.id, req.version, action, s, now));
    if !action.state.spec_settable() {
        assert(outs == spec_out(a_promise_res(400, None), s));
        lemma_others_same(key, s);
    } else {
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        lemma_held(map, o, s, x, req.version, now);
        let (_, held) = spec_held(map, x, req.version, now);
        assert(spec_with_workflow(doc, map) == doc);
        match held {
            Held::Missing => {
                assert(outs == spec_out(a_promise_res(404, None), s));
                lemma_others_same(key, s);
            },
            Held::Stale => {
                assert(outs == spec_out(a_promise_res(409, None), s));
                lemma_others_same(key, s);
            },
            Held::Ok(obj) => {
                let t = obj.task.unwrap();
                let t_a = s.tasks[x];
                let p = s.promises[x];
                let promise = PromV { state: action.state, value: action.value, settled_at: Some(now), ..obj.promise };
                let task = Some(spec_fulfill_task(t));
                let obj2 = ObjV { promise, task };
                let q = PromiseV { state: action.state, value: action.value, settled_at: Some(now), ..p };
                let u = spec_fulfill(t_a);
                assert(promise_rel(promise, q));
                assert(task_rel(spec_fulfill_task(t), u));
                assert(object_rel(obj2, q, Some(u)));
                let n = spec_settle(s, x, action.state, action.value, now);
                assert(t_a.state == TaskState::Acquired);
                assert(n == AStore { promises: s.promises.insert(x, q), tasks: s.tasks.insert(x, u), ..s });
                assert(n.promises.contains_key(x));
                assert(n.promises[x] == q);
                lemma_record(req.id, promise, q);
                assert(outs == spec_out(a_promise_res(200, Some(spec_promise_record(req.id, q))), n));
                assert(c_task_fulfill(doc, req.id, req.version, action, now).1 == c_promise_res(200, Some(crate::node::spec_record(req.id, promise))));
                lemma_held_update(key, o, map, s, x, obj2, q, u);
                assert(c_task_fulfill(doc, req.id, req.version, action, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
            },
        }
    }
}

pub proof fn lemma_task_halt_agrees(config: ServerConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_origin_key(origin(id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskHalt(echod_types::TaskHaltReq { id }),
            spec_origin_key(origin(id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskHalt(echod_types::TaskHaltReq { id });
    let x = id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_halt(doc, id, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_halt(id, s, now));
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(x) {
        assert(!s.tasks.contains_key(x));
        assert(outs == spec_out(spec_status_res(404), s));
        lemma_others_same(key, s);
    } else {
        let p = s.promises[x];
        let ta = abstract_task(s, x);
        lemma_project_object(map[x], p, ta, now);
        let seen = spec_project_obj(map[x], now);
        let seen_p = spec_project_promise(p, now);
        match (map[x].task, ta) {
            (None, None) => {
                assert(!s.tasks.contains_key(x));
                assert(outs == spec_out(spec_status_res(404), s));
                lemma_others_same(key, s);
            },
            (Some(ct), Some(stored)) => {
                assert(s.tasks.contains_key(x));
                let t = seen.task.unwrap();
                let seen_t = spec_project_task(stored, seen_p);
                assert(task_rel(t, seen_t));
                if t.state == TaskState::Fulfilled {
                    assert(outs == spec_out(spec_status_res(409), s));
                    lemma_others_same(key, s);
                } else if t.state == TaskState::Halted {
                    assert(outs == spec_out(spec_status_res(200), s));
                    lemma_others_same(key, s);
                } else {
                    lemma_unfulfilled_is_stored(map[x], p, ta, now);
                    assert(seen == map[x]);
                    assert(seen_t == stored);
                    let u_c = c_unlease(t, TaskState::Halted, None);
                    let u_a = a_unlease(stored, TaskState::Halted, None);
                    assert(task_rel(u_c, u_a));
                    let obj2 = ObjV { task: Some(u_c), ..seen };
                    assert(object_rel(obj2, p, Some(u_a)));
                    assert(obj2.promise.callbacks == map[x].promise.callbacks);
                    lemma_promises_kept(s, x);
                    let n = AStore { promises: s.promises.insert(x, p), tasks: s.tasks.insert(x, u_a), ..s };
                    assert(n == AStore { tasks: s.tasks.insert(x, u_a), ..s });
                    assert(outs == spec_out(spec_status_res(200), n));
                    lemma_held_update(key, o, map, s, x, obj2, p, u_a);
                    assert(c_task_halt(doc, id, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn lemma_task_continue_agrees(config: ServerConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_origin_key(origin(id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskContinue(echod_types::TaskContinueReq { id }),
            spec_origin_key(origin(id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskContinue(echod_types::TaskContinueReq { id });
    let x = id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_continue(doc, id, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_continue(id, s, now));
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(x) {
        assert(!s.tasks.contains_key(x));
        assert(outs == spec_out(spec_status_res(404), s));
        lemma_others_same(key, s);
    } else {
        let p = s.promises[x];
        let ta = abstract_task(s, x);
        lemma_project_object(map[x], p, ta, now);
        let seen = spec_project_obj(map[x], now);
        let seen_p = spec_project_promise(p, now);
        match (map[x].task, ta) {
            (None, None) => {
                assert(!s.tasks.contains_key(x));
                assert(outs == spec_out(spec_status_res(404), s));
                lemma_others_same(key, s);
            },
            (Some(ct), Some(stored)) => {
                assert(s.tasks.contains_key(x));
                let t = seen.task.unwrap();
                let seen_t = spec_project_task(stored, seen_p);
                assert(task_rel(t, seen_t));
                let live = seen_p.state == PromiseState::Pending;
                assert(live == (seen.promise.state == PromiseState::Pending));
                if t.state != TaskState::Halted || seen.promise.state != PromiseState::Pending {
                    if live {
                        assert(seen_t == stored);
                        assert(t.state == stored.state);
                    }
                    assert(stored.state != TaskState::Halted || !live);
                    assert(outs == spec_out(spec_status_res(409), s));
                    lemma_others_same(key, s);
                } else {
                    lemma_unfulfilled_is_stored(map[x], p, ta, now);
                    assert(seen == map[x]);
                    assert(seen_t == stored);
                    assert(stored.state == TaskState::Halted);
                    let u_c = TkV { state: TaskState::Pending, retry_timeout_at: Some(now), ..t };
                    let u_a = TaskV { state: TaskState::Pending, retry_timeout_at: Some(now), ..stored };
                    assert(task_rel(u_c, u_a));
                    let obj2 = ObjV { task: Some(u_c), ..seen };
                    assert(object_rel(obj2, p, Some(u_a)));
                    assert(obj2.promise.callbacks == map[x].promise.callbacks);
                    lemma_promises_kept(s, x);
                    let n = AStore { promises: s.promises.insert(x, p), tasks: s.tasks.insert(x, u_a), ..s };
                    assert(n == AStore { tasks: s.tasks.insert(x, u_a), ..s });
                    assert(outs == spec_out(spec_status_res(200), n));
                    lemma_held_update(key, o, map, s, x, obj2, p, u_a);
                    assert(c_task_continue(doc, id, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}


// ---------------------------------------------------------------------------
// The heartbeat
// ---------------------------------------------------------------------------

pub proof fn lemma_one_origin_from(refs: Seq<TaskRef>, o: Seq<char>, i: int)
    requires
        0 <= i,
    ensures
        spec_one_origin(refs, o, i) == forall|k: int| i <= k < refs.len() ==> origin(#[trigger] refs[k].id@) == o,
    decreases refs.len() - i,
{
    if i >= refs.len() {
    } else {
        lemma_one_origin_from(refs, o, i + 1);
    }
}

pub proof fn lemma_refs_one_origin_from(refs: Seq<TaskRef>, j: int)
    requires
        j >= 1,
    ensures
        spec_refs_one_origin(refs, j) == forall|k: int|
            j <= k < refs.len() ==> origin(#[trigger] refs[k].id@) == origin(refs[0].id@),
    decreases refs.len() - j,
{
    if j >= refs.len() {
    } else {
        lemma_refs_one_origin_from(refs, j + 1);
    }
}

/// The running document and the running task map, `i` refs in: related,
/// with the same keys as at the start, the tasks differing from the start
/// in their leases alone, and other origins untouched.
pub open spec fn extending(
    map0: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    map_i: Map<Seq<char>, ObjV>,
    tasks_i: Map<Seq<char>, TaskV>,
) -> bool {
    &&& origin_rel(map_i, o, AStore { tasks: tasks_i, ..s })
    &&& forall|id: Seq<char>| #[trigger] map_i.contains_key(id) == map0.contains_key(id)
    &&& forall|id: Seq<char>|
        #[trigger] map0.contains_key(id) ==> {
            let a = map0[id];
            let b = map_i[id];
            &&& b.promise == a.promise
            &&& (b.task is Some) == (a.task is Some)
            &&& b.task is Some ==> b.task.unwrap() == (TkV {
                lease_timeout_at: b.task.unwrap().lease_timeout_at,
                ..a.task.unwrap()
            })
        }
    &&& forall|id: Seq<char>| #[trigger] tasks_i.contains_key(id) == s.tasks.contains_key(id)
    &&& forall|id: Seq<char>|
        #![trigger origin(id)]
        origin(id) != o ==> (s.tasks.contains_key(id) ==> tasks_i[id] == s.tasks[id])
}

pub proof fn lemma_extend(
    map0: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    pid: Seq<char>,
    refs: Seq<TaskRef>,
    now: Time,
    i: int,
    map_i: Map<Seq<char>, ObjV>,
    tasks_i: Map<Seq<char>, TaskV>,
)
    requires
        origin_rel(map0, o, s),
        extending(map0, o, s, map_i, tasks_i),
        0 <= i <= refs.len(),
        forall|k: int| 0 <= k < refs.len() ==> origin(#[trigger] refs[k].id@) == o,
    ensures
        extending(map0, o, s, c_extend(map_i, pid, refs, now, i), a_extend(s, pid, refs, now, i, tasks_i)),
    decreases refs.len() - i,
{
    if i >= refs.len() {
    } else {
        let id = refs[i].id@;
        let version = refs[i].version;
        let s_i = AStore { tasks: tasks_i, ..s };
        lemma_held(map0, o, s, id, version, now);
        let (_, held0) = spec_held(map0, id, version, now);
        let a = a_held(s, id, version, now);
        let a_cond = a is Ok && a->Ok_0.pid == Some(pid);
        let c_cond = map_i.contains_key(id) && {
            let obj = spec_project_obj(map_i[id], now);
            match obj.task {
                Some(t) => t.state == TaskState::Acquired && t.version == version && t.pid == Some(pid),
                None => false,
            }
        };
        if map_i.contains_key(id) {
            assert(map0.contains_key(id));
            let a0 = map0[id];
            let b = map_i[id];
            assert(b.promise == a0.promise);
            let seen0 = spec_project_obj(a0, now);
            let seen = spec_project_obj(b, now);
            assert(seen.promise == seen0.promise);
            match (a0.task, b.task) {
                (Some(ta0), Some(tb)) => {
                    assert(tb == TkV { lease_timeout_at: tb.lease_timeout_at, ..ta0 });
                    let p = s.promises[id];
                    assert(object_rel(a0, p, abstract_task(s, id)));
                    let t_c = seen.task.unwrap();
                    let t_c0 = seen0.task.unwrap();
                    assert(t_c.state == t_c0.state);
                    assert(t_c.version == t_c0.version);
                    assert(t_c.pid == t_c0.pid);
                    if t_c.state == TaskState::Acquired {
                        assert(seen0.promise.state == PromiseState::Pending);
                    }
                    assert(c_cond == (held0 is Ok && t_c0.pid == Some(pid)));
                    if held0 is Ok {
                        assert(t_c0 == a0.task.unwrap());
                        assert(task_rel(a0.task.unwrap(), s.tasks[id]));
                        assert(t_c0.pid == s.tasks[id].pid);
                    }
                    assert(c_cond == a_cond);
                },
                (None, None) => {
                    assert(!s.tasks.contains_key(id));
                    assert(a is Missing);
                    assert(!c_cond);
                },
                _ => {
                    assert(false);
                },
            }
        } else {
            assert(!map0.contains_key(id));
            assert(!s.tasks.contains_key(id));
            assert(a is Missing);
        }
        if c_cond {
            let obj = spec_project_obj(map_i[id], now);
            let p = s.promises[id];
            let ta = abstract_task(s_i, id);
            assert(object_rel(map_i[id], p, ta));
            lemma_unfulfilled_is_stored(map_i[id], p, ta, now);
            assert(obj == map_i[id]);
            let t = obj.task.unwrap();
            assert(t.state == TaskState::Acquired);
            assert(t.ttl is Some);
            let ttl = match t.ttl {
                Some(n) => n,
                None => 0,
            };
            let at = crate::store::spec_sat_add(now, ttl);
            let t2 = TkV { lease_timeout_at: Some(at), ..t };
            let obj2 = ObjV { task: Some(t2), ..obj };
            let t_a = a->Ok_0;
            assert(t_a == s.tasks[id]);
            let u_a = TaskV { acquired_at: now, ..t_a };
            assert(task_rel(map0[id].task.unwrap(), t_a));
            lemma_sat_add(now, ttl);
            assert(task_rel(t2, u_a));
            assert(object_rel(obj2, p, Some(u_a)));
            let map_next = map_i.insert(id, obj2);
            let tasks_next = tasks_i.insert(id, u_a);
            let s_next = AStore { tasks: tasks_next, ..s };
            assert(s_next.promises == s_i.promises.insert(id, p)) by {
                assert(s.promises.insert(id, p) =~= s.promises);
            };
            lemma_origin_update(map_i, o, s_i, id, obj2, p, Some(u_a), s_next);
            assert(extending(map0, o, s, map_next, tasks_next));
            assert(c_extend(map_i, pid, refs, now, i) == c_extend(map_next, pid, refs, now, i + 1));
            assert(a_extend(s, pid, refs, now, i, tasks_i) == a_extend(s, pid, refs, now, i + 1, tasks_next));
            lemma_extend(map0, o, s, pid, refs, now, i + 1, map_next, tasks_next);
        } else {
            assert(c_extend(map_i, pid, refs, now, i) == c_extend(map_i, pid, refs, now, i + 1));
            assert(a_extend(s, pid, refs, now, i, tasks_i) == a_extend(s, pid, refs, now, i + 1, tasks_i));
            lemma_extend(map0, o, s, pid, refs, now, i + 1, map_i, tasks_i);
        }
    }
}

pub proof fn lemma_heartbeat_agrees(
    config: ServerConfig,
    req: echod_types::TaskHeartbeatReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        req.tasks@.len() > 0,
        doc_rel(spec_origin_key(origin(req.tasks@[0].id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskHeartbeat(req),
            spec_origin_key(origin(req.tasks@[0].id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskHeartbeat(req);
    let refs = req.tasks@;
    let pid = req.pid;
    let o = origin(refs[0].id@);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_heartbeat(doc, pid, refs, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_heartbeat(pid, refs, s, now));
    lemma_one_origin_from(refs, o, 0);
    lemma_refs_one_origin_from(refs, 1);
    assert(spec_one_origin(refs, o, 0) == spec_refs_one_origin(refs, 1));
    if !spec_one_origin(refs, o, 0) {
        assert(outs == spec_out(spec_status_res(400), s));
        lemma_others_same(key, s);
    } else {
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        assert(extending(map, o, s, map, s.tasks));
        lemma_extend(map, o, s, pid@, refs, now, 0, map, s.tasks);
        let map2 = c_extend(map, pid@, refs, now, 0);
        let tasks2 = a_extend(s, pid@, refs, now, 0, s.tasks);
        let n = AStore { tasks: tasks2, ..s };
        assert(outs == spec_out(spec_status_res(200), n));
        assert(c_heartbeat(doc, pid, refs, now) == (DocumentBodyV::Workflow(map2), Response::Status(StatusRes { status: 200 })));
        assert(map2.dom() =~= map.dom());
        lemma_origin_reads(key, o, map2, n);
        assert(changed_within(s, n, o));
        lemma_others_kept_within(s, n, o);
        assert(tasks2.dom() =~= s.tasks.dom());
        assert(finite_store(n));
    }
}

// ---------------------------------------------------------------------------
// The suspend
// ---------------------------------------------------------------------------

pub proof fn lemma_bad_suspend_from(actions: Seq<PromiseRegisterCallbackReq>, x: Seq<char>, i: int)
    requires
        0 <= i,
    ensures
        spec_bad_suspend(actions, x, i) == exists|j: int|
            i <= j < actions.len() && ((#[trigger] actions[j]).awaited@ == x || origin(actions[j].awaited@) != origin(x)),
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_bad_suspend_from(actions, x, i + 1);
    }
}

pub proof fn lemma_seen_from(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, j: int, stop: int)
    requires
        0 <= j,
    ensures
        spec_seen(actions, id, j, stop) == exists|k: int|
            j <= k < stop && k < actions.len() && (#[trigger] actions[k]).awaited@ == id,
    decreases stop - j,
{
    if j >= stop || j >= actions.len() {
    } else {
        lemma_seen_from(actions, id, j + 1, stop);
    }
}

pub proof fn lemma_distinct_from(actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        i >= 0,
    ensures
        spec_distinct_awaited(actions, i) == forall|a: int, b: int|
            #![trigger actions[a], actions[b]]
            i <= a < actions.len() && 0 <= b < a ==> actions[a].awaited@ != actions[b].awaited@,
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_seen_from(actions, actions[i].awaited@, 0, i);
        lemma_distinct_from(actions, i + 1);
    }
}

pub proof fn lemma_missing_from(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        0 <= i,
    ensures
        spec_missing_awaited(map, actions, i) == exists|j: int|
            i <= j < actions.len() && !map.contains_key((#[trigger] actions[j]).awaited@),
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_missing_from(map, actions, i + 1);
    }
}

pub proof fn lemma_unawaitable_from(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        0 <= i,
    ensures
        spec_unawaitable(map, actions, i) == exists|j: int|
            i <= j < actions.len() && map.contains_key((#[trigger] actions[j]).awaited@)
                && !spec_awaitable(map[actions[j].awaited@].promise.tags),
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_unawaitable_from(map, actions, i + 1);
    }
}

pub proof fn lemma_c_any_settled_from(
    map: Map<Seq<char>, ObjV>,
    actions: Seq<PromiseRegisterCallbackReq>,
    now: Time,
    i: int,
)
    requires
        0 <= i,
    ensures
        c_any_settled(map, actions, now, i) == exists|j: int|
            i <= j < actions.len() && map.contains_key((#[trigger] actions[j]).awaited@)
                && spec_project_obj(map[actions[j].awaited@], now).promise.state != PromiseState::Pending,
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_c_any_settled_from(map, actions, now, i + 1);
    }
}

pub proof fn lemma_a_any_settled_from(s: AStore, ids: Seq<Seq<char>>, now: Time, i: int)
    requires
        0 <= i,
        forall|k: int| 0 <= k < ids.len() ==> s.promises.contains_key(#[trigger] ids[k]),
    ensures
        a_any_settled(s, ids, now, i) == exists|j: int|
            i <= j < ids.len() && spec_project_promise(s.promises[#[trigger] ids[j]], now).state != PromiseState::Pending,
    decreases ids.len() - i,
{
    if i >= ids.len() {
    } else {
        lemma_a_any_settled_from(s, ids, now, i + 1);
    }
}

/// The running document and the running promises, `i` callbacks in.
pub open spec fn adding(
    map0: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    x: Seq<char>,
    map_i: Map<Seq<char>, ObjV>,
    promises_i: Map<Seq<char>, PromiseV>,
) -> bool {
    &&& origin_rel(map_i, o, AStore { promises: promises_i, ..s })
    &&& forall|id: Seq<char>| #[trigger] map_i.contains_key(id) == map0.contains_key(id)
    &&& forall|id: Seq<char>| #[trigger] promises_i.contains_key(id) == s.promises.contains_key(id)
    &&& map0.contains_key(x) ==> map_i[x] == map0[x]
    &&& s.promises.contains_key(x) ==> promises_i[x] == s.promises[x]
    &&& forall|id: Seq<char>|
        #![trigger origin(id)]
        origin(id) != o ==> (s.promises.contains_key(id) ==> promises_i[id] == s.promises[id])
}

pub proof fn lemma_add_callbacks(
    map0: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    x: Seq<char>,
    actions: Seq<PromiseRegisterCallbackReq>,
    i: int,
    map_i: Map<Seq<char>, ObjV>,
    promises_i: Map<Seq<char>, PromiseV>,
)
    requires
        adding(map0, o, s, x, map_i, promises_i),
        0 <= i <= actions.len(),
        origin(x) == o,
        forall|k: int|
            i <= k < actions.len() ==> map0.contains_key((#[trigger] actions[k]).awaited@) && actions[k].awaited@ != x
                && origin(actions[k].awaited@) == o,
    ensures
        adding(
            map0,
            o,
            s,
            x,
            spec_add_callbacks(map_i, x, actions, i),
            a_callbacks(promises_i, spec_awaited(actions), x, i),
        ),
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        let a = actions[i].awaited@;
        let ids = spec_awaited(actions);
        assert(ids[i] == a);
        assert(map_i.contains_key(a));
        assert(promises_i.contains_key(a));
        let s_i = AStore { promises: promises_i, ..s };
        let obj = map_i[a];
        let p = promises_i[a];
        let ta = abstract_task(s_i, a);
        assert(object_rel(obj, p, ta));
        let callbacks = if obj.promise.callbacks.contains(x) {
            obj.promise.callbacks
        } else {
            obj.promise.callbacks.push(x)
        };
        lemma_add_callback(obj.promise.callbacks, p.callbacks, x);
        let obj2 = ObjV { promise: PromV { callbacks, ..obj.promise }, ..obj };
        let q = PromiseV { callbacks: p.callbacks.insert(x), ..p };
        assert(promise_rel(obj2.promise, q));
        assert(object_rel(obj2, q, ta));
        assert forall|k: int| 0 <= k < callbacks.len() implies origin(#[trigger] callbacks[k]) == o by {
            if k < obj.promise.callbacks.len() {
                assert(callbacks[k] == obj.promise.callbacks[k]);
            } else {
                assert(callbacks[k] == x);
            }
        };
        let map_next = map_i.insert(a, obj2);
        let promises_next = promises_i.insert(a, q);
        let s_next = AStore { promises: promises_next, ..s };
        lemma_tasks_kept(s_i, a);
        lemma_origin_update(map_i, o, s_i, a, obj2, q, ta, s_next);
        assert(adding(map0, o, s, x, map_next, promises_next));
        assert(spec_add_callbacks(map_i, x, actions, i) == spec_add_callbacks(map_next, x, actions, i + 1));
        assert(a_callbacks(promises_i, ids, x, i) == a_callbacks(promises_next, ids, x, i + 1));
        lemma_add_callbacks(map0, o, s, x, actions, i + 1, map_next, promises_next);
    }
}

pub proof fn lemma_suspend_agrees(
    config: ServerConfig,
    req: echod_types::TaskSuspendReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskSuspend(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskSuspend(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    let actions = req.actions@;
    let ids = spec_awaited(actions);
    assert(ids.len() == actions.len());
    assert forall|j: int| 0 <= j < actions.len() implies #[trigger] ids[j] == actions[j].awaited@ by {};
    assert(spec_handle(doc, request, now) == c_suspend(doc, req.id, req.version, actions, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_suspend(req.id, req.version, actions, s, now));
    lemma_bad_suspend_from(actions, x, 0);
    lemma_distinct_from(actions, 0);
    assert(spec_bad_suspend(actions, x, 0) == (ids.contains(x) || !all_in_origin(ids, x))) by {
        if spec_bad_suspend(actions, x, 0) {
            let j = choose|j: int|
                0 <= j < actions.len() && ((#[trigger] actions[j]).awaited@ == x || origin(actions[j].awaited@) != origin(x));
            if actions[j].awaited@ == x {
                assert(ids[j] == x);
                assert(ids.contains(x));
            } else {
                assert(origin(ids[j]) != origin(x));
                assert(!all_in_origin(ids, x));
            }
        }
        if ids.contains(x) {
            let j = choose|j: int| 0 <= j < ids.len() && ids[j] == x;
            assert(actions[j].awaited@ == x);
            assert(spec_bad_suspend(actions, x, 0));
        }
        if !all_in_origin(ids, x) {
            let j = choose|j: int| 0 <= j < ids.len() && origin(#[trigger] ids[j]) != origin(x);
            assert(origin(actions[j].awaited@) != origin(x));
            assert(spec_bad_suspend(actions, x, 0));
        }
    };
    assert(spec_distinct_awaited(actions, 0) == distinct(ids)) by {
        if spec_distinct_awaited(actions, 0) {
            assert forall|a: int, b: int| 0 <= a < b < ids.len() implies ids[a] != ids[b] by {
                assert(actions[b].awaited@ != actions[a].awaited@);
            };
        }
        if distinct(ids) {
            assert forall|a: int, b: int|
                #![trigger actions[a], actions[b]]
                0 <= a < actions.len() && 0 <= b < a implies actions[a].awaited@ != actions[b].awaited@ by {
                assert(ids[b] != ids[a]);
            };
        }
    };
    if actions.len() == 0 || spec_bad_suspend(actions, x, 0) || !spec_distinct_awaited(actions, 0) {
        assert(outs == spec_out(spec_status_res(400), s));
        assert(c_suspend(doc, req.id, req.version, actions, now) == (doc, Response::Status(StatusRes { status: 400 })));
        lemma_others_same(key, s);
    } else {
        assert(all_in_origin(ids, x));
        assert forall|k: int| 0 <= k < actions.len() implies origin((#[trigger] actions[k]).awaited@) == o
            && actions[k].awaited@ != x by {
            assert(origin(ids[k]) == origin(x));
            if actions[k].awaited@ == x {
                assert(ids.contains(x));
            }
        };
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        lemma_held(map, o, s, x, req.version, now);
        let (_, held) = spec_held(map, x, req.version, now);
        assert(spec_with_workflow(doc, map) == doc);
        match held {
            Held::Missing => {
                assert(outs == spec_out(spec_status_res(404), s));
                lemma_others_same(key, s);
            },
            Held::Stale => {
                assert(outs == spec_out(spec_status_res(409), s));
                lemma_others_same(key, s);
            },
            Held::Ok(obj) => {
                let t = obj.task.unwrap();
                let t_a = s.tasks[x];
                let p = s.promises[x];
                lemma_missing_from(map, actions, 0);
                lemma_unawaitable_from(map, actions, 0);
                let missing = exists|j: int| 0 <= j < ids.len() && !s.promises.contains_key(#[trigger] ids[j]);
                assert(spec_missing_awaited(map, actions, 0) == missing) by {
                    if spec_missing_awaited(map, actions, 0) {
                        let j = choose|j: int| 0 <= j < actions.len() && !map.contains_key((#[trigger] actions[j]).awaited@);
                        assert(!s.promises.contains_key(ids[j]));
                    }
                    if missing {
                        let j = choose|j: int| 0 <= j < ids.len() && !s.promises.contains_key(#[trigger] ids[j]);
                        assert(!map.contains_key(actions[j].awaited@));
                    }
                };
                if missing {
                    assert(outs == spec_out(spec_status_res(422), s));
                    assert(c_suspend(doc, req.id, req.version, actions, now).1 == Response::Status(StatusRes { status: 422 }));
                    lemma_others_same(key, s);
                } else {
                    assert forall|k: int| 0 <= k < ids.len() implies s.promises.contains_key(#[trigger] ids[k]) by {};
                    assert forall|k: int| 0 <= k < actions.len() implies map.contains_key((#[trigger] actions[k]).awaited@) by {
                        assert(s.promises.contains_key(ids[k]));
                    };
                    let unawaitable = exists|j: int| 0 <= j < ids.len() && !spec_external(s.promises[#[trigger] ids[j]]);
                    assert(spec_unawaitable(map, actions, 0) == unawaitable) by {
                        if spec_unawaitable(map, actions, 0) {
                            let j = choose|j: int|
                                0 <= j < actions.len() && map.contains_key((#[trigger] actions[j]).awaited@)
                                    && !spec_awaitable(map[actions[j].awaited@].promise.tags);
                            let a = actions[j].awaited@;
                            assert(object_rel(map[a], s.promises[a], abstract_task(s, a)));
                            lemma_awaitable(map[a].promise, s.promises[a]);
                            assert(!spec_external(s.promises[ids[j]]));
                        }
                        if unawaitable {
                            let j = choose|j: int| 0 <= j < ids.len() && !spec_external(s.promises[#[trigger] ids[j]]);
                            let a = actions[j].awaited@;
                            assert(object_rel(map[a], s.promises[a], abstract_task(s, a)));
                            lemma_awaitable(map[a].promise, s.promises[a]);
                            assert(!spec_awaitable(map[a].promise.tags));
                        }
                    };
                    if unawaitable {
                        assert(outs == spec_out(spec_status_res(422), s));
                        assert(c_suspend(doc, req.id, req.version, actions, now).1 == Response::Status(StatusRes { status: 422 }));
                        lemma_others_same(key, s);
                    } else {
                        lemma_c_any_settled_from(map, actions, now, 0);
                        lemma_a_any_settled_from(s, ids, now, 0);
                        assert(c_any_settled(map, actions, now, 0) == a_any_settled(s, ids, now, 0)) by {
                            assert forall|j: int| 0 <= j < actions.len() implies spec_project_obj(
                                map[(#[trigger] actions[j]).awaited@],
                                now,
                            ).promise.state == spec_project_promise(s.promises[ids[j]], now).state by {
                                let a = actions[j].awaited@;
                                lemma_project_object(map[a], s.promises[a], abstract_task(s, a), now);
                            };
                        };
                        if c_any_settled(map, actions, now, 0) {
                            let task = Some(TkV { resumes: Seq::empty(), ..t });
                            let u = TaskV { resumes: Seq::empty(), ..t_a };
                            assert(task_rel(task.unwrap(), u));
                            let obj2 = ObjV { task, ..obj };
                            assert(object_rel(obj2, p, Some(u)));
                            lemma_promises_kept(s, x);
                            let n = AStore { promises: s.promises.insert(x, p), tasks: s.tasks.insert(x, u), ..s };
                            assert(n == AStore { tasks: s.tasks.insert(x, u), ..s });
                            assert(outs == spec_out(spec_status_res(300), n));
                            lemma_held_update(key, o, map, s, x, obj2, p, u);
                            assert(c_suspend(doc, req.id, req.version, actions, now) == (DocumentBodyV::Workflow(map.insert(x, obj2)), Response::Status(StatusRes { status: 300 })));
                        } else {
                            assert(adding(map, o, s, x, map, s.promises));
                            lemma_add_callbacks(map, o, s, x, actions, 0, map, s.promises);
                            let map2 = spec_add_callbacks(map, x, actions, 0);
                            let promises2 = a_callbacks(s.promises, ids, x, 0);
                            assert(adding(map, o, s, x, map2, promises2));
                            let s2 = AStore { promises: promises2, ..s };
                            assert(map2[x] == obj);
                            assert(promises2[x] == p);
                            let task = Some(TkV { resumes: Seq::empty(), ..c_unlease(t, TaskState::Suspended, None) });
                            let u = TaskV {
                                state: TaskState::Suspended,
                                pid: None,
                                ttl: None,
                                acquired_at: 0,
                                retry_timeout_at: None,
                                resumes: Seq::empty(),
                                ..t_a
                            };
                            assert(task_rel(task.unwrap(), u));
                            let obj3 = ObjV { task, ..obj };
                            assert(object_rel(obj3, p, Some(u)));
                            let n = AStore { promises: promises2, tasks: s.tasks.insert(x, u), ..s };
                            assert(outs == spec_out(spec_status_res(200), n));
                            assert(n.promises == s2.promises.insert(x, p)) by {
                                assert(promises2.insert(x, p) =~= promises2);
                            };
                            lemma_origin_update(map2, o, s2, x, obj3, p, Some(u), n);
                            assert(map2.dom() =~= map.dom());
                            assert(map2.insert(x, obj3).dom() == map2.dom().insert(x));
                            lemma_origin_reads(key, o, map2.insert(x, obj3), n);
                            assert(c_suspend(doc, req.id, req.version, actions, now) == (DocumentBodyV::Workflow(map2.insert(x, obj3)), Response::Status(StatusRes { status: 200 })));
                            assert(changed_within(s, n, o)) by {
                                assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) != o implies {
                                    &&& s.promises.contains_key(id) == n.promises.contains_key(id)
                                    &&& (s.promises.contains_key(id) ==> s.promises[id] == n.promises[id])
                                    &&& s.tasks.contains_key(id) == n.tasks.contains_key(id)
                                    &&& (s.tasks.contains_key(id) ==> s.tasks[id] == n.tasks[id])
                                } by {
                                    assert(id != x);
                                };
                            };
                            lemma_others_kept_within(s, n, o);
                            assert(promises2.dom() =~= s.promises.dom());
                            assert(n.tasks.dom() == s.tasks.dom().insert(x));
                            assert(finite_store(n));
                        }
                    }
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The fence
// ---------------------------------------------------------------------------

/// The promise handlers answer a promise response.
pub proof fn lemma_promise_answers(doc: DocumentBodyV, action: TaskFenceAction, now: Time)
    ensures
        match action {
            TaskFenceAction::Create(c) => c_promise_create(doc, c, now).1 is Promise,
            TaskFenceAction::Settle(st) => c_promise_settle(doc, st, now).1 is Promise,
        },
{
}

pub proof fn lemma_fence_agrees(
    config: ServerConfig,
    req: echod_types::TaskFenceReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskFence(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskFence(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    let action = req.action;
    let target = match action {
        TaskFenceAction::Create(c) => c.id,
        TaskFenceAction::Settle(st) => st.id,
    };
    assert(spec_handle(doc, request, now) == c_fence(doc, req.id, req.version, action, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_fence(req, s, now));
    if target@ == x || !same_origin_spec(target@, x) {
        assert(outs == spec_out(spec_fence_res(400, None), s));
        assert(c_fence(doc, req.id, req.version, action, now) == (doc, Response::TaskFence(TaskFenceRes { status: 400, action: None })));
        lemma_others_same(key, s);
    } else {
        assert(origin(target@) == o);
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        lemma_held(map, o, s, x, req.version, now);
        let (_, held) = spec_held(map, x, req.version, now);
        assert(spec_with_workflow(doc, map) == doc);
        match held {
            Held::Missing => {
                assert(outs == spec_out(spec_fence_res(404, None), s));
                lemma_others_same(key, s);
            },
            Held::Stale => {
                assert(outs == spec_out(spec_fence_res(409, None), s));
                lemma_others_same(key, s);
            },
            Held::Ok(_) => {
                lemma_promise_answers(doc, action, now);
                match action {
                    TaskFenceAction::Create(c) => {
                        assert(spec_origin_key(origin(c.id@)) == key);
                        lemma_promise_create_agrees(config, c, doc, s, now);
                        let inner_outs = spec_handler(config, Request::PromiseCreate(c), s, now);
                        assert(inner_outs == a_promise_create(c, s, now));
                        let (doc2, response) = c_promise_create(doc, c, now);
                        assert(spec_handle(doc, Request::PromiseCreate(c), now) == (doc2, response));
                        assert(inner_outs.len() == 1);
                        assert(inner_outs[0].resp == response);
                        let inner = response->Promise_0;
                        assert(outs == spec_wrap_fence(inner_outs, true));
                        assert(outs == seq![OutV { resp: spec_fence_res(200, Some(TaskFenceInnerRes::Create(inner))), ..inner_outs[0] }]);
                        assert(c_fence(doc, req.id, req.version, action, now) == (doc2, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Create(inner)) })));
                    },
                    TaskFenceAction::Settle(st) => {
                        assert(spec_origin_key(origin(st.id@)) == key);
                        lemma_promise_settle_agrees(config, st, doc, s, now);
                        let inner_outs = spec_handler(config, Request::PromiseSettle(st), s, now);
                        assert(inner_outs == a_promise_settle(st, s, now));
                        let (doc2, response) = c_promise_settle(doc, st, now);
                        assert(spec_handle(doc, Request::PromiseSettle(st), now) == (doc2, response));
                        assert(inner_outs.len() == 1);
                        assert(inner_outs[0].resp == response);
                        let inner = response->Promise_0;
                        assert(outs == spec_wrap_fence(inner_outs, false));
                        assert(outs == seq![OutV { resp: spec_fence_res(200, Some(TaskFenceInnerRes::Settle(inner))), ..inner_outs[0] }]);
                        assert(c_fence(doc, req.id, req.version, action, now) == (doc2, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Settle(inner)) })));
                    },
                }
            },
        }
    }
}

pub proof fn lemma_fence_check_agrees(
    config: ServerConfig,
    req: echod_types::TaskFenceCheckReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskFenceCheck(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskFenceCheck(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_fence_check(doc, req.id, req.version, now));
    let outs = spec_handler(config, request, s, now);
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    lemma_held(map, o, s, x, req.version, now);
    assert(spec_with_workflow(doc, map) == doc);
    assert(outs[0].next == s);
    lemma_others_same(key, s);
}

// ---------------------------------------------------------------------------
// Schedules
// ---------------------------------------------------------------------------

/// A related schedule is the value of the abstract schedule.
pub proof fn lemma_schedule_value(c: Schedule, a: ScheduleV)
    requires
        schedule_rel(c, a),
    ensures
        c == spec_schedule_value(a),
{
    lemma_string_of(c.id);
    lemma_string_of(c.cron);
    lemma_string_of(c.promise_id);
}

pub proof fn lemma_schedule_get_agrees(config: ServerConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_schedule_key(id@), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::ScheduleGet(echod_types::ScheduleGetReq { id }),
            spec_schedule_key(id@),
            doc,
            s,
            now,
        ),
{
    let request = Request::ScheduleGet(echod_types::ScheduleGetReq { id });
    let key = spec_schedule_key(id@);
    assert(spec_handle(doc, request, now) == c_schedule_get(doc, id));
    let outs = spec_handler(config, request, s, now);
    lemma_schedule_doc(key, id@, doc, s);
    let slot = doc->Schedule_0;
    match slot {
        Some(sch) => {
            assert(sch.id@ == id@);
            axiom_string_ext(sch.id, id);
            assert(s.schedules.contains_key(id@));
            lemma_schedule_value(sch, s.schedules[id@]);
            assert(outs == spec_out(spec_schedule_res(200, Some(sch)), s));
            assert(c_schedule_get(doc, id) == (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(sch) })));
        },
        None => {
            assert(!s.schedules.contains_key(id@));
            assert(outs == spec_out(spec_schedule_res(404, None), s));
        },
    }
    lemma_others_same(key, s);
}

pub proof fn lemma_schedule_create_agrees(
    config: ServerConfig,
    req: ScheduleCreateReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_schedule_key(req.id@), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::ScheduleCreate(req), spec_schedule_key(req.id@), doc, s, now),
{
    let request = Request::ScheduleCreate(req);
    let key = spec_schedule_key(req.id@);
    assert(spec_handle(doc, request, now) == c_schedule_create(doc, req, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_schedule_create(req, s, now));
    lemma_timer(req.promise_tags);
    lemma_targeted(req.promise_tags);
    lemma_schedule_doc(key, req.id@, doc, s);
    lemma_schedule_key(req.id@);
    let slot = doc->Schedule_0;
    if spec_targeted(req.promise_tags) && spec_timer(req.promise_tags) {
        assert(outs == spec_out(spec_schedule_res(400, None), s));
        lemma_others_same(key, s);
    } else {
        match slot {
            Some(sch) => {
                assert(s.schedules.contains_key(req.id@));
                lemma_schedule_value(sch, s.schedules[req.id@]);
                assert(outs == spec_out(spec_schedule_res(200, Some(sch)), s));
                assert(c_schedule_create(doc, req, now) == (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(sch) })));
                lemma_others_same(key, s);
            },
            None => {
                assert(!s.schedules.contains_key(req.id@));
                let next_run_at = echod_abstract::trusted::spec_next_cron(req.cron@, now);
                let schedule = Schedule {
                    id: req.id,
                    cron: req.cron,
                    promise_id: req.promise_id,
                    promise_timeout: req.promise_timeout,
                    promise_param: req.promise_param,
                    promise_tags: req.promise_tags,
                    next_run_at,
                    last_run_at: None,
                    created_at: now,
                };
                let c = ScheduleV {
                    id: req.id@,
                    cron: req.cron@,
                    promise_id: req.promise_id@,
                    promise_timeout: req.promise_timeout,
                    promise_param: req.promise_param,
                    promise_tags: req.promise_tags,
                    created_at: now,
                    next_run_at,
                    last_run_at: None,
                };
                let next = AStore { schedules: s.schedules.insert(req.id@, c), ..s };
                assert(outs == spec_out(spec_schedule_res(200, Some(schedule)), next));
                assert(c_schedule_create(doc, req, now) == (DocumentBodyV::Schedule(Some(schedule)), Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })));
                assert(schedule_rel(schedule, c));
                assert(slot_rel(Some(schedule), req.id@, next));
                assert(doc_rel(key, DocumentBodyV::Schedule(Some(schedule)), next));
                lemma_others_kept_schedule(s, next, req.id@);
                assert(next.schedules.dom() == s.schedules.dom().insert(req.id@));
                assert(finite_store(next));
            },
        }
    }
}

pub proof fn lemma_schedule_delete_agrees(config: ServerConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_schedule_key(id@), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::ScheduleDelete(echod_types::ScheduleDeleteReq { id }),
            spec_schedule_key(id@),
            doc,
            s,
            now,
        ),
{
    let request = Request::ScheduleDelete(echod_types::ScheduleDeleteReq { id });
    let key = spec_schedule_key(id@);
    assert(spec_handle(doc, request, now) == c_schedule_delete(doc, id));
    let outs = spec_handler(config, request, s, now);
    lemma_schedule_doc(key, id@, doc, s);
    lemma_schedule_key(id@);
    let slot = doc->Schedule_0;
    match slot {
        Some(sch) => {
            assert(sch.id@ == id@);
            axiom_string_ext(sch.id, id);
            assert(s.schedules.contains_key(id@));
            let next = AStore { schedules: s.schedules.remove(id@), ..s };
            assert(outs == spec_out(spec_status_res(200), next));
            assert(c_schedule_delete(doc, id) == (DocumentBodyV::Schedule(None), Response::Status(StatusRes { status: 200 })));
            assert(!next.schedules.contains_key(id@));
            assert(slot_rel(None, id@, next));
            assert(doc_rel(key, DocumentBodyV::Schedule(None), next));
            lemma_others_kept_schedule(s, next, id@);
            assert(next.schedules.dom() == s.schedules.dom().remove(id@));
            assert(finite_store(next));
        },
        None => {
            assert(!s.schedules.contains_key(id@));
            assert(outs == spec_out(spec_status_res(404), s));
            lemma_others_same(key, s);
        },
    }
}

// ---------------------------------------------------------------------------
// Every request
// ---------------------------------------------------------------------------

/// One request with a key agrees on the document under that key.
pub proof fn lemma_request_agrees(
    config: ServerConfig,
    request: Request,
    key: Seq<char>,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        spec_key(request) == Some(key),
        doc_rel(key, doc, s),
        finite_store(s),
    ensures
        request_agrees(config, request, key, doc, s, now),
{
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_) => {
            lemma_promise_handlers_agree(config, request, doc, s, now);
        },
        Request::PromiseRegisterCallback(q) => lemma_register_callback_agrees(config, q, doc, s, now),
        Request::PromiseRegisterListener(q) => lemma_register_listener_agrees(config, q, doc, s, now),
        Request::TaskGet(q) => lemma_task_get_agrees(config, q.id, doc, s, now),
        Request::TaskCreate(q) => lemma_task_create_agrees(config, q, doc, s, now),
        Request::TaskAcquire(q) => lemma_task_acquire_agrees(config, q, doc, s, now),
        Request::TaskFulfill(q) => lemma_task_fulfill_agrees(config, q, doc, s, now),
        Request::TaskRelease(q) => lemma_task_release_agrees(config, q, doc, s, now),
        Request::TaskHalt(q) => lemma_task_halt_agrees(config, q.id, doc, s, now),
        Request::TaskContinue(q) => lemma_task_continue_agrees(config, q.id, doc, s, now),
        Request::TaskFence(q) => lemma_fence_agrees(config, q, doc, s, now),
        Request::TaskFenceCheck(q) => lemma_fence_check_agrees(config, q, doc, s, now),
        Request::TaskSuspend(q) => lemma_suspend_agrees(config, q, doc, s, now),
        Request::TaskHeartbeat(q) => {
            assert(q.tasks@.len() > 0);
            lemma_heartbeat_agrees(config, q, doc, s, now);
        },
        Request::ScheduleGet(q) => lemma_schedule_get_agrees(config, q.id, doc, s, now),
        Request::ScheduleDelete(q) => lemma_schedule_delete_agrees(config, q.id, doc, s, now),
        Request::ScheduleCreate(q) => lemma_schedule_create_agrees(config, q, doc, s, now),
    }
}

/// Lean's `refinement_handlers`, for the requests.
pub proof fn lemma_requests_agree(config: ServerConfig)
    ensures
        crate::relation::requests_agree(config),
{
    assert forall|request: Request, key: Seq<char>, doc: DocumentBodyV, s: AStore, now: u64|
        spec_key(request) == Some(key) && doc_rel(key, doc, s) && finite_store(s) implies #[trigger] request_agrees(
        config,
        request,
        key,
        doc,
        s,
        now,
    ) by {
        lemma_request_agrees(config, request, key, doc, s, now);
    };
}

} // verus!
