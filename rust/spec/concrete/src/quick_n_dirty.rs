//! One deliberately small document theorem, independent of Rover.

use vstd::prelude::*;

use echod_types::{
    PromiseCreateReq, PromiseRegisterCallbackReq, PromiseRegisterListenerReq, PromiseSettleReq,
    PromiseState, Request, TaskAcquireReq, TaskCreateReq, TaskFenceAction, TaskFenceReq,
    TaskContinueReq, TaskFulfillReq, TaskHaltReq, TaskHeartbeatReq, TaskRef, TaskReleaseReq,
    TaskState, TaskSuspendReq, MAX_TIME, MAX_VERSION,
};

#[cfg(verus_keep_ghost)]
use echod_types::origin;
#[cfg(verus_keep_ghost)]
use crate::store::spec_sat_add;
#[cfg(verus_keep_ghost)]
use crate::document::{
    callback_targets_well_formed, promise_well_formed, suspended_rung_well_formed,
    task_cleared, task_well_formed, unique, value_empty, well_formed, ObjV, PromV,
    StoredDocumentV, TkV, WorkflowDocumentV,
};
#[cfg(verus_keep_ghost)]
use crate::node::{
    spec_advance_stored, spec_awaitable, spec_body_deadline, spec_earliest_in,
    spec_due_id, spec_handle, spec_key, spec_obj_due, spec_project_obj, spec_request_document, spec_request_transition,
    spec_resume, spec_run_due, spec_sorted, spec_sorted_present, spec_stored_body, spec_sweep,
    spec_stored_committed_at, spec_stored_name, spec_targeted, spec_unavailable,
    spec_unlease, DocumentBodyV, REQUEST_SWEEP_STEPS,
};
#[cfg(verus_keep_ghost)]
use crate::interpret::{lemma_origin_key, lemma_schedule_key};

verus! {

/// The clauses that every intermediate request/sweep state preserves.
/// Deadline closure and drained settlement queues are deliberately omitted:
/// those are exactly what a successful post-sweep establishes.
pub open spec fn promise_relaxed(id: Seq<char>, object: ObjV, now: u64) -> bool {
    let promise = object.promise;
    &&& promise.timeout_at <= MAX_TIME
    &&& promise.created_at <= promise.timeout_at
    &&& promise.created_at <= now
    &&& (promise.state == PromiseState::Pending) == (promise.settled_at is None)
    &&& match promise.settled_at {
        Some(at) => promise.created_at <= at <= promise.timeout_at && at <= now,
        None => true,
    }
    &&& promise.state == PromiseState::Pending ==> value_empty(promise.value)
    &&& promise.state == PromiseState::RejectedTimedout ==>
        promise.settled_at == Some(promise.timeout_at)
    &&& promise.settled_at == Some(promise.timeout_at) ==> value_empty(promise.value)
    &&& unique(promise.callbacks)
    &&& unique(promise.listeners)
    &&& !promise.callbacks.contains(id)
    &&& forall|i: int| 0 <= i < promise.callbacks.len() ==>
        origin(promise.callbacks[i]) == origin(id)
    &&& (promise.callbacks.len() > 0 || promise.listeners.len() > 0) ==>
        spec_awaitable(promise.tags)
}

pub open spec fn task_relaxed(object: ObjV) -> bool {
    (object.task is Some) == spec_targeted(object.promise.tags)
        && match object.task {
            None => true,
            Some(task) => {
                &&& (task.state == TaskState::Acquired) == (task.pid is Some)
                &&& (task.state == TaskState::Acquired) == (task.ttl is Some)
                &&& (task.state == TaskState::Acquired) == (task.lease_timeout_at is Some)
                &&& (task.state == TaskState::Pending) == (task.retry_timeout_at is Some)
                &&& match task.ttl { Some(ttl) => 0 < ttl <= MAX_TIME, None => true }
                &&& task.state == TaskState::Acquired ==> task.version > 0
                &&& task.state == TaskState::Fulfilled ==> {
                    &&& task_cleared(task)
                    &&& task.resumes.len() == 0
                    &&& object.promise.state != PromiseState::Pending
                }
                &&& task.state == TaskState::Suspended ==> {
                    &&& task_cleared(task)
                    &&& task.resumes.len() == 0
                }
                &&& task.state == TaskState::Halted ==> task_cleared(task)
                &&& object.promise.state != PromiseState::Pending ==>
                    task.state == TaskState::Fulfilled
                &&& unique(task.resumes)
                &&& task.version <= MAX_VERSION
            },
        }
}

pub open spec fn suspended_rung_relaxed(
    objects: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    object: ObjV,
    now: u64,
) -> bool {
    match object.task {
        Some(task) if task.state == TaskState::Suspended
            && object.promise.state == PromiseState::Pending =>
                object.promise.timeout_at <= now
                    || exists|awaited: Seq<char>|
                        objects.contains_key(awaited)
                            && objects[awaited].promise.callbacks.contains(id),
        _ => true,
    }
}

pub open spec fn workflow_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    now: u64,
) -> bool {
    &&& now <= MAX_TIME
    &&& forall|id: Seq<char>| #[trigger] objects.contains_key(id) ==> {
        &&& origin(id) == name
        &&& promise_relaxed(id, objects[id], now)
        &&& task_relaxed(objects[id])
        &&& callback_targets_well_formed(objects, objects[id])
        &&& suspended_rung_relaxed(objects, id, objects[id], now)
    }
}

pub proof fn lemma_full_implies_relaxed(workflow: WorkflowDocumentV, now: u64)
    requires
        crate::document::workflow_well_formed(workflow),
        workflow.committed_at <= now,
        now <= MAX_TIME,
    ensures
        workflow_relaxed(workflow.document, workflow.objects, now),
{
    reveal(crate::document::workflow_well_formed);
    reveal(workflow_relaxed);
    reveal(promise_well_formed);
    reveal(task_well_formed);
    assert(crate::document::workflow_well_formed(workflow));
    assert forall|id: Seq<char>| workflow.objects.contains_key(id) implies {
        &&& origin(id) == workflow.document
        &&& promise_relaxed(id, workflow.objects[id], now)
        &&& task_relaxed(workflow.objects[id])
        &&& callback_targets_well_formed(workflow.objects, workflow.objects[id])
        &&& suspended_rung_relaxed(workflow.objects, id, workflow.objects[id], now)
    } by {
        assert(workflow.objects.contains_key(id));
        let object = workflow.objects[id];
        assert(origin(id) == workflow.document);
        assert(promise_well_formed(id, object, workflow.committed_at));
        assert(task_well_formed(object, workflow.committed_at));
        assert(callback_targets_well_formed(workflow.objects, object));
        assert(suspended_rung_well_formed(workflow.objects, id, object));
        assert(suspended_rung_relaxed(workflow.objects, id, object, now));
    };
}

proof fn lemma_map_due_none(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    now: u64,
)
    requires
        crate::node::spec_map_due(map, keys, now) is None,
        forall|i: int| 0 <= i < keys.len() ==>
            map.contains_key(#[trigger] keys[i]),
    ensures
        forall|id: Seq<char>| keys.contains(id) && map.contains_key(id) ==>
            spec_obj_due(map[id], now) is None,
    decreases keys.len(),
{
    if keys.len() > 0 {
        let first = keys[0];
        assert(spec_obj_due(map[first], now) is None);
        assert forall|i: int| 0 <= i < keys.drop_first().len() implies
            map.contains_key(#[trigger] keys.drop_first()[i]) by {
            assert(keys.drop_first()[i] == keys[i + 1]);
        };
        lemma_map_due_none(map, keys.drop_first(), now);
        assert forall|id: Seq<char>| keys.contains(id) && map.contains_key(id) implies
            spec_obj_due(map[id], now) is None by {
            if id != first {
                let j = choose|j: int| 0 <= j < keys.len() && keys[j] == id;
                assert(j != 0);
                assert(keys.drop_first()[j - 1] == id);
                assert(keys.drop_first().contains(id));
            }
        };
    }
}

pub proof fn lemma_relaxed_closed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        forall|id: Seq<char>| objects.contains_key(id) ==> {
            &&& origin(id) == name
            &&& promise_well_formed(id, objects[id], now)
            &&& task_well_formed(objects[id], now)
            &&& callback_targets_well_formed(objects, objects[id])
            &&& suspended_rung_well_formed(objects, id, objects[id])
            &&& spec_project_obj(objects[id], now) == objects[id]
        },
{
    reveal(workflow_relaxed);
    reveal(promise_relaxed);
    reveal(task_relaxed);
    reveal(value_empty);
    reveal(unique);
    crate::timers::lemma_sorted(objects.dom());
    let keys = spec_sorted(objects.dom());
    assert forall|i: int| 0 <= i < keys.len() implies
        objects.contains_key(#[trigger] keys[i]) by {
        assert(objects.dom().contains(keys[i]));
    };
    lemma_map_due_none(objects, keys, now);
    assert forall|id: Seq<char>| objects.contains_key(id) implies
        spec_obj_due(objects[id], now) is None by {
        assert(keys.contains(id));
    };
    assert forall|id: Seq<char>| objects.contains_key(id) implies {
        &&& origin(id) == name
        &&& promise_well_formed(id, objects[id], now)
        &&& task_well_formed(objects[id], now)
        &&& callback_targets_well_formed(objects, objects[id])
        &&& suspended_rung_well_formed(objects, id, objects[id])
        &&& spec_project_obj(objects[id], now) == objects[id]
    } by {
        let obj = objects[id];
        assert(origin(id) == name
            && promise_relaxed(id, obj, now)
            && task_relaxed(obj)
            && callback_targets_well_formed(objects, obj)
            && suspended_rung_relaxed(objects, id, obj, now));
        assert(spec_obj_due(obj, now) is None);
        if obj.promise.state == PromiseState::Pending {
            assert(obj.promise.timeout_at > now);
            assert(suspended_rung_well_formed(objects, id, obj));
        } else {
            assert(obj.promise.callbacks.len() == 0);
            assert(obj.promise.listeners.len() == 0);
        }
        match obj.task {
            Some(task) => {
                if task.state == TaskState::Acquired {
                    assert(task.lease_timeout_at.unwrap() > now);
                }
                if task.state == TaskState::Pending {
                    assert(task.retry_timeout_at.unwrap() > now);
                }
            },
            None => {},
        }
        assert(spec_project_obj(obj, now) == obj);
    };
}

pub proof fn lemma_replace_same_callbacks(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    next: ObjV,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        objects.contains_key(id),
        origin(id) == name,
        promise_relaxed(id, next, now),
        task_relaxed(next),
        next.promise.timeout_at == objects[id].promise.timeout_at,
        next.promise.callbacks == objects[id].promise.callbacks,
        spec_targeted(next.promise.tags) == spec_targeted(objects[id].promise.tags),
        (next.task is Some) == (objects[id].task is Some),
        suspended_rung_relaxed(objects.insert(id, next), id, next, now),
    ensures
        workflow_relaxed(name, objects.insert(id, next), now),
{
    reveal(workflow_relaxed);
    let updated = objects.insert(id, next);
    assert forall|x: Seq<char>| #[trigger] updated.contains_key(x) implies {
        &&& origin(x) == name
        &&& promise_relaxed(x, updated[x], now)
        &&& task_relaxed(updated[x])
        &&& callback_targets_well_formed(updated, updated[x])
        &&& suspended_rung_relaxed(updated, x, updated[x], now)
    } by {
        if x == id {
            assert(updated[x] == next);
        } else {
            assert(updated[x] == objects[x]);
            assert(objects.contains_key(x));
        }
        assert(callback_targets_well_formed(updated, updated[x])) by {
            assert forall|i: int| 0 <= i < updated[x].promise.callbacks.len() implies {
                let awaiter = #[trigger] updated[x].promise.callbacks[i];
                updated.contains_key(awaiter)
                    && updated[awaiter].task is Some
                    && spec_targeted(updated[awaiter].promise.tags)
            } by {
                let awaiter = updated[x].promise.callbacks[i];
                assert(objects.contains_key(awaiter));
                if awaiter == id {
                    assert(next.task is Some);
                    assert(spec_targeted(next.promise.tags));
                } else {
                    assert(updated[awaiter] == objects[awaiter]);
                }
            };
        };
        assert(suspended_rung_relaxed(updated, x, updated[x], now)) by {
            if x != id {
                match updated[x].task {
                    Some(task) if task.state == TaskState::Suspended
                        && updated[x].promise.state == PromiseState::Pending => {
                            assert(objects[x].task is Some);
                            assert(objects[x].task.unwrap().state == TaskState::Suspended);
                            assert(objects[x].promise.state == PromiseState::Pending);
                            if objects[x].promise.timeout_at <= now {
                                assert(updated[x].promise.timeout_at <= now);
                            } else {
                                let awaited = choose|awaited: Seq<char>|
                                    objects.contains_key(awaited)
                                        && objects[awaited].promise.callbacks.contains(x);
                                assert(objects.contains_key(awaited));
                                assert(objects[awaited].promise.callbacks.contains(x));
                                if awaited == id {
                                    assert(next.promise.callbacks.contains(x));
                                } else {
                                    assert(updated[awaited] == objects[awaited]);
                                }
                                assert(updated.contains_key(awaited));
                                assert(updated[awaited].promise.callbacks.contains(x));
                            }
                        },
                    _ => {},
                }
            }
        };
    };
}

proof fn lemma_insert_fresh(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    object: ObjV,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        !objects.contains_key(id),
        origin(id) == name,
        promise_relaxed(id, object, now),
        task_relaxed(object),
        callback_targets_well_formed(objects.insert(id, object), object),
        suspended_rung_relaxed(objects.insert(id, object), id, object, now),
    ensures
        workflow_relaxed(name, objects.insert(id, object), now),
{
    reveal(workflow_relaxed);
    let updated = objects.insert(id, object);
    assert forall|x: Seq<char>| #[trigger] updated.contains_key(x) implies {
        &&& origin(x) == name
        &&& promise_relaxed(x, updated[x], now)
        &&& task_relaxed(updated[x])
        &&& callback_targets_well_formed(updated, updated[x])
        &&& suspended_rung_relaxed(updated, x, updated[x], now)
    } by {
        if x == id {
            assert(updated[x] == object);
        } else {
            assert(objects.contains_key(x));
            assert(updated[x] == objects[x]);
            assert(callback_targets_well_formed(updated, updated[x])) by {
                assert forall|i: int| 0 <= i < updated[x].promise.callbacks.len() implies {
                    let target = #[trigger] updated[x].promise.callbacks[i];
                    updated.contains_key(target)
                        && updated[target].task is Some
                        && spec_targeted(updated[target].promise.tags)
                } by {
                    let target = updated[x].promise.callbacks[i];
                    assert(objects.contains_key(target));
                    assert(target != id);
                    assert(updated[target] == objects[target]);
                };
            };
            assert(suspended_rung_relaxed(updated, x, updated[x], now)) by {
                match updated[x].task {
                    Some(task) if task.state == TaskState::Suspended
                        && updated[x].promise.state == PromiseState::Pending
                        && updated[x].promise.timeout_at > now => {
                            let awaited = choose|awaited: Seq<char>|
                                objects.contains_key(awaited)
                                    && objects[awaited].promise.callbacks.contains(x);
                            assert(awaited != id);
                            assert(updated.contains_key(awaited));
                            assert(updated[awaited] == objects[awaited]);
                        },
                    _ => {},
                }
            };
        }
    };
}

proof fn lemma_add_one_callback(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    awaited: Seq<char>,
    awaiter: Seq<char>,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        objects.contains_key(awaited),
        objects.contains_key(awaiter),
        awaited != awaiter,
        objects[awaited].promise.state == PromiseState::Pending,
        spec_awaitable(objects[awaited].promise.tags),
        spec_targeted(objects[awaiter].promise.tags),
    ensures
        ({
            let old = objects[awaited];
            let callbacks = if old.promise.callbacks.contains(awaiter) {
                old.promise.callbacks
            } else {
                old.promise.callbacks.push(awaiter)
            };
            let next = ObjV {
                promise: PromV { callbacks, ..old.promise },
                ..old
            };
            workflow_relaxed(name, objects.insert(awaited, next), now)
        }),
{
    reveal(workflow_relaxed);
    reveal(promise_relaxed);
    let old = objects[awaited];
    let callbacks = if old.promise.callbacks.contains(awaiter) {
        old.promise.callbacks
    } else {
        crate::handlers::lemma_push_no_duplicates(old.promise.callbacks, awaiter);
        old.promise.callbacks.push(awaiter)
    };
    let next = ObjV {
        promise: PromV { callbacks, ..old.promise },
        ..old
    };
    let updated = objects.insert(awaited, next);
    assert(promise_relaxed(awaited, next, now));
    assert forall|x: Seq<char>| #[trigger] updated.contains_key(x) implies {
        &&& origin(x) == name
        &&& promise_relaxed(x, updated[x], now)
        &&& task_relaxed(updated[x])
        &&& callback_targets_well_formed(updated, updated[x])
        &&& suspended_rung_relaxed(updated, x, updated[x], now)
    } by {
        if x == awaited {
            assert(updated[x] == next);
        } else {
            assert(objects.contains_key(x));
            assert(updated[x] == objects[x]);
        }
        assert(callback_targets_well_formed(updated, updated[x])) by {
            assert forall|i: int| 0 <= i < updated[x].promise.callbacks.len() implies {
                let target = #[trigger] updated[x].promise.callbacks[i];
                updated.contains_key(target)
                    && updated[target].task is Some
                    && spec_targeted(updated[target].promise.tags)
            } by {
                let target = updated[x].promise.callbacks[i];
                if x == awaited {
                    if i >= old.promise.callbacks.len() {
                        assert(target == awaiter);
                        assert(awaiter != awaited);
                        assert(updated[awaiter] == objects[awaiter]);
                    } else {
                        assert(target == old.promise.callbacks[i]);
                        assert(objects.contains_key(target));
                        if target == awaited {
                            assert(updated[target].task == objects[target].task);
                            assert(updated[target].promise.tags == objects[target].promise.tags);
                        } else {
                            assert(updated[target] == objects[target]);
                        }
                    }
                } else {
                    assert(objects.contains_key(target));
                    if target == awaited {
                        assert(updated[target].task == objects[target].task);
                        assert(updated[target].promise.tags == objects[target].promise.tags);
                    } else {
                        assert(updated[target] == objects[target]);
                    }
                }
            };
        };
        assert(suspended_rung_relaxed(updated, x, updated[x], now)) by {
            match updated[x].task {
                Some(task) if task.state == TaskState::Suspended
                    && updated[x].promise.state == PromiseState::Pending
                    && updated[x].promise.timeout_at > now => {
                        if x != awaited {
                            let witness = choose|witness: Seq<char>|
                                objects.contains_key(witness)
                                    && objects[witness].promise.callbacks.contains(x);
                            if witness == awaited {
                                if old.promise.callbacks.contains(awaiter) {
                                    assert(updated[witness].promise.callbacks
                                        == old.promise.callbacks);
                                } else {
                                    let j = choose|j: int|
                                        0 <= j < old.promise.callbacks.len()
                                            && old.promise.callbacks[j] == x;
                                    assert(updated[witness].promise.callbacks[j] == x);
                                }
                                assert(updated[witness].promise.callbacks.contains(x));
                            } else {
                                assert(updated[witness] == objects[witness]);
                            }
                            assert(updated.contains_key(witness));
                        } else {
                            let witness = choose|witness: Seq<char>|
                                objects.contains_key(witness)
                                    && objects[witness].promise.callbacks.contains(x);
                            assert(witness != awaited);
                            assert(updated[witness] == objects[witness]);
                            assert(updated.contains_key(witness));
                        }
                    },
                _ => {},
            }
        };
    };
}

proof fn lemma_add_callbacks_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    awaiter: Seq<char>,
    actions: Seq<PromiseRegisterCallbackReq>,
    index: int,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        objects.contains_key(awaiter),
        spec_targeted(objects[awaiter].promise.tags),
        0 <= index <= actions.len(),
        forall|i: int| index <= i < actions.len() ==> {
            let awaited = (#[trigger] actions[i]).awaited@;
            &&& objects.contains_key(awaited)
            &&& awaited != awaiter
            &&& objects[awaited].promise.state == PromiseState::Pending
            &&& spec_awaitable(objects[awaited].promise.tags)
        },
        forall|i: int, j: int| index <= i < j < actions.len() ==>
            (#[trigger] actions[i]).awaited@ != (#[trigger] actions[j]).awaited@,
    ensures
        ({
            let updated = crate::node::spec_add_callbacks(
                objects,
                awaiter,
                actions,
                index,
            );
            &&& workflow_relaxed(name, updated, now)
            &&& forall|id: Seq<char>| #[trigger] updated.contains_key(id)
                == objects.contains_key(id)
            &&& updated[awaiter] == objects[awaiter]
            &&& forall|i: int| index <= i < actions.len() ==>
                updated[(#[trigger] actions[i]).awaited@]
                    .promise.callbacks.contains(awaiter)
            &&& forall|id: Seq<char>|
                objects.contains_key(id)
                && (forall|i: int| index <= i < actions.len() ==>
                    (#[trigger] actions[i]).awaited@ != id) ==>
                updated[id] == objects[id]
        }),
    decreases actions.len() - index,
{
    if index < actions.len() {
        let awaited = actions[index].awaited@;
        let old = objects[awaited];
        let callbacks = if old.promise.callbacks.contains(awaiter) {
            old.promise.callbacks
        } else {
            old.promise.callbacks.push(awaiter)
        };
        let next = ObjV {
            promise: PromV { callbacks, ..old.promise },
            ..old
        };
        let updated = objects.insert(awaited, next);
        if old.promise.callbacks.contains(awaiter) {
            assert(callbacks == old.promise.callbacks);
        } else {
            assert(callbacks[old.promise.callbacks.len() as int] == awaiter);
        }
        assert(callbacks.contains(awaiter));
        lemma_add_one_callback(name, objects, awaited, awaiter, now);
        assert(updated[awaited] == next);
        assert(updated[awaited].promise.callbacks.contains(awaiter));
        assert forall|i: int| index + 1 <= i < actions.len() implies {
            let id = (#[trigger] actions[i]).awaited@;
            &&& updated.contains_key(id)
            &&& id != awaiter
            &&& updated[id].promise.state == PromiseState::Pending
            &&& spec_awaitable(updated[id].promise.tags)
        } by {
            let id = actions[i].awaited@;
            if id == awaited {
                assert(updated[id] == next);
            } else {
                assert(updated[id] == objects[id]);
            }
        };
        assert(updated.contains_key(awaiter));
        assert(spec_targeted(updated[awaiter].promise.tags));
        assert forall|i: int, j: int| index + 1 <= i < j < actions.len() implies
            (#[trigger] actions[i]).awaited@ != (#[trigger] actions[j]).awaited@ by {};
        lemma_add_callbacks_preserves_relaxed(
            name,
            updated,
            awaiter,
            actions,
            index + 1,
            now,
        );
        let final_map = crate::node::spec_add_callbacks(
            updated,
            awaiter,
            actions,
            index + 1,
        );
        assert forall|id: Seq<char>| #[trigger] final_map.contains_key(id)
            == objects.contains_key(id) by {};
        assert(final_map[awaiter] == objects[awaiter]);
        assert forall|id: Seq<char>|
            objects.contains_key(id)
            && (forall|i: int| index <= i < actions.len() ==>
                (#[trigger] actions[i]).awaited@ != id) implies
            final_map[id] == objects[id] by {
            assert(id != awaited);
            assert(final_map[id] == updated[id]);
            assert(updated[id] == objects[id]);
        };
        assert forall|i: int| index <= i < actions.len() implies
            final_map[(#[trigger] actions[i]).awaited@]
                .promise.callbacks.contains(awaiter) by {
            if i == index {
                assert forall|j: int| index + 1 <= j < actions.len() implies
                    (#[trigger] actions[j]).awaited@ != awaited by {};
                assert(updated.contains_key(awaited));
                assert(final_map[awaited] == updated[awaited]);
                assert(final_map[awaited].promise.callbacks.contains(awaiter));
            }
        };
    }
}

pub proof fn lemma_pop_callback_and_resume(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        objects.contains_key(id),
        objects[id].promise.state != PromiseState::Pending,
        objects[id].promise.callbacks.len() > 0,
    ensures
        ({
            let object = objects[id];
            let awaiter = object.promise.callbacks[0];
            let since = object.promise.settled_at.unwrap();
            let popped = objects.insert(id, ObjV {
                promise: PromV {
                    callbacks: object.promise.callbacks.skip(1),
                    ..object.promise
                },
                ..object
            });
            workflow_relaxed(
                name,
                spec_resume(popped, awaiter, id, since, now),
                now,
            )
        }),
{
    reveal(workflow_relaxed);
    let object = objects[id];
    let awaiter = object.promise.callbacks[0];
    let since = object.promise.settled_at.unwrap();
    let popped_object = ObjV {
        promise: PromV {
            callbacks: object.promise.callbacks.skip(1),
            ..object.promise
        },
        ..object
    };
    let popped = objects.insert(id, popped_object);
    let resumed = spec_resume(popped, awaiter, id, since, now);
    crate::handlers::lemma_skip_no_duplicates(object.promise.callbacks);
    assert(promise_relaxed(id, popped_object, now));
    assert(task_relaxed(popped_object));
    assert(awaiter != id);
    assert(objects.contains_key(awaiter));
    assert(objects[awaiter].task is Some);
    assert(spec_targeted(objects[awaiter].promise.tags));
    assert(popped[awaiter] == objects[awaiter]);
    let projected = spec_project_obj(objects[awaiter], now);
    assert(projected.task is Some);
    match projected.task.unwrap().state {
        TaskState::Suspended => {},
        TaskState::Fulfilled => {},
        _ => {
            let task = projected.task.unwrap();
            if !task.resumes.contains(id) {
                crate::handlers::lemma_push_no_duplicates(task.resumes, id);
            }
        },
    }
    assert forall|x: Seq<char>| #[trigger] resumed.contains_key(x) implies {
        &&& origin(x) == name
        &&& promise_relaxed(x, resumed[x], now)
        &&& task_relaxed(resumed[x])
        &&& callback_targets_well_formed(resumed, resumed[x])
        &&& suspended_rung_relaxed(resumed, x, resumed[x], now)
    } by {
        assert(objects.contains_key(x));
        if x == id {
            assert(resumed[x] == popped_object);
        } else if x == awaiter {
            match projected.task.unwrap().state {
                TaskState::Suspended => {},
                TaskState::Fulfilled => {
                    assert(objects[x].promise.timeout_at <= now
                        || objects[x].task.unwrap().state != TaskState::Suspended);
                },
                _ => {},
            }
        } else {
            assert(resumed[x] == objects[x]);
        }
        assert(callback_targets_well_formed(resumed, resumed[x])) by {
            assert forall|i: int| 0 <= i < resumed[x].promise.callbacks.len() implies {
                let target = #[trigger] resumed[x].promise.callbacks[i];
                resumed.contains_key(target)
                    && resumed[target].task is Some
                    && spec_targeted(resumed[target].promise.tags)
            } by {
                let target = resumed[x].promise.callbacks[i];
                assert(objects.contains_key(target));
                if target == awaiter {
                    assert(resumed[target].task is Some);
                    assert(spec_targeted(resumed[target].promise.tags));
                } else if target == id {
                    assert(resumed[target] == popped_object);
                    assert(popped_object.task == objects[target].task);
                    assert(popped_object.promise.tags == objects[target].promise.tags);
                } else {
                    assert(resumed[target] == objects[target]);
                }
            };
        };
        assert(suspended_rung_relaxed(resumed, x, resumed[x], now)) by {
            match resumed[x].task {
                Some(task) if task.state == TaskState::Suspended
                    && resumed[x].promise.state == PromiseState::Pending => {
                        if resumed[x].promise.timeout_at <= now {
                        } else {
                            assert(x != awaiter);
                            let awaited = choose|awaited: Seq<char>|
                                objects.contains_key(awaited)
                                    && objects[awaited].promise.callbacks.contains(x);
                            assert(objects.contains_key(awaited));
                            assert(objects[awaited].promise.callbacks.contains(x));
                            if awaited == id {
                                assert(x != awaiter);
                                let j = choose|j: int|
                                    0 <= j < object.promise.callbacks.len()
                                        && object.promise.callbacks[j] == x;
                                assert(j != 0);
                                assert(object.promise.callbacks.skip(1)[j - 1] == x);
                                assert(object.promise.callbacks.skip(1).contains(x));
                            } else {
                                assert(resumed[awaited].promise.callbacks.contains(x));
                            }
                            assert(resumed.contains_key(awaited));
                        }
                    },
                _ => {},
            }
        };
    };
}

pub proof fn lemma_run_due_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    now: u64,
    retry_timeout: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        0 < retry_timeout <= MAX_TIME,
    ensures
        ({
            let next = spec_run_due(
                DocumentBodyV::Workflow(objects),
                now,
                retry_timeout,
            ).0;
            next is Workflow
                && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    crate::timers::lemma_sorted(objects.dom());
    let keys = spec_sorted_present(objects);
    assert forall|i: int| 0 <= i < keys.len() implies
        objects.contains_key(#[trigger] keys[i]) by {
        assert(objects.dom().contains(keys[i]));
    };
    crate::timers::lemma_due_id(objects, keys, now);
    match spec_due_id(objects, keys, now) {
        Some(id) => {
            assert(objects.contains_key(id));
            let object = objects[id];
            let next = spec_run_due(
                DocumentBodyV::Workflow(objects),
                now,
                retry_timeout,
            ).0;
            if object.promise.state == PromiseState::Pending
                && object.promise.timeout_at <= now
            {
                let projected = spec_project_obj(object, now);
                assert(promise_relaxed(id, projected, now));
                assert(task_relaxed(projected));
                lemma_replace_same_callbacks(name, objects, id, projected, now);
                assert(next is Workflow
                    && workflow_relaxed(name, next->Workflow_0, now));
            } else if object.promise.state == PromiseState::Pending {
                match object.task {
                    Some(task) if task.state == TaskState::Acquired
                        && match task.lease_timeout_at {
                            Some(at) => at <= now,
                            None => false,
                        } => {
                            let replaced = ObjV {
                                task: Some(spec_unlease(task, TaskState::Pending, Some(now))),
                                ..object
                            };
                            assert(promise_relaxed(id, replaced, now));
                            assert(task_relaxed(replaced));
                            lemma_replace_same_callbacks(name, objects, id, replaced, now);
                            assert(next is Workflow
                                && workflow_relaxed(name, next->Workflow_0, now));
                        },
                    Some(task) if task.state == TaskState::Pending
                        && match task.retry_timeout_at {
                            Some(at) => at <= now,
                            None => false,
                        } => {
                            let replaced = ObjV {
                                task: Some(TkV {
                                    retry_timeout_at: Some(spec_sat_add(now, retry_timeout)),
                                    ..task
                                }),
                                ..object
                            };
                            assert(spec_sat_add(now, retry_timeout) >= now);
                            assert(promise_relaxed(id, replaced, now));
                            assert(task_relaxed(replaced));
                            lemma_replace_same_callbacks(name, objects, id, replaced, now);
                            assert(next is Workflow
                                && workflow_relaxed(name, next->Workflow_0, now));
                        },
                    _ => {},
                }
            } else if object.promise.callbacks.len() > 0 {
                lemma_pop_callback_and_resume(name, objects, id, now);
                assert(next is Workflow
                    && workflow_relaxed(name, next->Workflow_0, now));
            } else if object.promise.listeners.len() > 0 {
                let replaced = ObjV {
                    promise: PromV {
                        listeners: object.promise.listeners.skip(1),
                        ..object.promise
                    },
                    ..object
                };
                crate::handlers::lemma_skip_no_duplicates(object.promise.listeners);
                assert(promise_relaxed(id, replaced, now));
                assert(task_relaxed(replaced));
                lemma_replace_same_callbacks(name, objects, id, replaced, now);
                assert(next is Workflow
                    && workflow_relaxed(name, next->Workflow_0, now));
            }
        },
        None => {},
    }
}

pub proof fn lemma_sweep_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    now: u64,
    retry_timeout: u64,
    limit: nat,
)
    requires
        workflow_relaxed(name, objects, now),
        0 < retry_timeout <= MAX_TIME,
    ensures
        ({
            let next = spec_sweep(
                DocumentBodyV::Workflow(objects),
                now,
                retry_timeout,
                limit,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
    decreases limit,
{
    if limit > 0 {
        lemma_run_due_preserves_relaxed(name, objects, now, retry_timeout);
        let next = spec_run_due(
            DocumentBodyV::Workflow(objects),
            now,
            retry_timeout,
        ).0;
        if next != DocumentBodyV::Workflow(objects) {
            lemma_sweep_preserves_relaxed(
                name,
                next->Workflow_0,
                now,
                retry_timeout,
                (limit - 1) as nat,
            );
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(10)]
proof fn lemma_promise_create_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: PromiseCreateReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::PromiseCreate(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    reveal(promise_relaxed);
    reveal(task_relaxed);
    reveal(value_empty);
    reveal(unique);
    if request.timeout_at > MAX_TIME
        || (crate::node::spec_timer(request.tags)
            && spec_targeted(request.tags))
        || objects.contains_key(request.id@)
    {
    } else {
        let object = crate::node::spec_new_obj(
            request.timeout_at,
            now,
            request.param,
            request.tags,
            spec_targeted(request.tags),
        );
        let updated = objects.insert(request.id@, object);
        assert(object.promise.callbacks =~= Seq::<Seq<char>>::empty());
        assert(object.promise.listeners =~= Seq::<Seq<char>>::empty());
        echod_abstract::trusted::axiom_empty_value_realised();
        assert(exists|v: echod_types::Value|
            v@ == echod_types::AValue::empty());
        assert(crate::node::spec_empty_value()@
            == echod_types::AValue::empty());
        assert(value_empty(object.promise.value));
        assert(promise_relaxed(request.id@, object, now));
        assert(task_relaxed(object));
        assert(callback_targets_well_formed(updated, object));
        assert(suspended_rung_relaxed(updated, request.id@, object, now));
        lemma_insert_fresh(name, objects, request.id@, object, now);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(10)]
proof fn lemma_register_callback_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: PromiseRegisterCallbackReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.awaited@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::PromiseRegisterCallback(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    lemma_relaxed_closed(name, objects, now);
    if request.awaited@ != request.awaiter@
        && echod_types::same_origin_spec(
            request.awaited@,
            request.awaiter@,
        )
        && objects.contains_key(request.awaited@)
        && objects.contains_key(request.awaiter@)
    {
        let awaited = spec_project_obj(objects[request.awaited@], now);
        let awaiter = spec_project_obj(objects[request.awaiter@], now);
        assert(awaited == objects[request.awaited@]);
        assert(awaiter == objects[request.awaiter@]);
        if spec_targeted(awaiter.promise.tags)
            && spec_awaitable(awaited.promise.tags)
            && awaited.promise.state == PromiseState::Pending
            && awaiter.promise.state == PromiseState::Pending
        {
            lemma_add_one_callback(
                name,
                objects,
                request.awaited@,
                request.awaiter@,
                now,
            );
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(10)]
proof fn lemma_add_listener_to_object(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    address: Seq<char>,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        objects.contains_key(id),
        objects[id].promise.state == PromiseState::Pending,
        spec_awaitable(objects[id].promise.tags),
    ensures
        ({
            let old = objects[id];
            let listeners = if old.promise.listeners.contains(address) {
                old.promise.listeners
            } else {
                old.promise.listeners.push(address)
            };
            let next = ObjV {
                promise: PromV { listeners, ..old.promise },
                ..old
            };
            workflow_relaxed(name, objects.insert(id, next), now)
        }),
{
    reveal(promise_relaxed);
    let old = objects[id];
    let listeners = if old.promise.listeners.contains(address) {
        old.promise.listeners
    } else {
        crate::handlers::lemma_push_no_duplicates(
            old.promise.listeners,
            address,
        );
        old.promise.listeners.push(address)
    };
    let next = ObjV {
        promise: PromV { listeners, ..old.promise },
        ..old
    };
    let updated = objects.insert(id, next);
    assert(promise_relaxed(id, next, now));
    assert(task_relaxed(next));
    assert(next.promise.timeout_at == objects[id].promise.timeout_at);
    assert(next.promise.callbacks == objects[id].promise.callbacks);
    assert(spec_targeted(next.promise.tags)
        == spec_targeted(objects[id].promise.tags));
    assert((next.task is Some) == (objects[id].task is Some));
    reveal(suspended_rung_relaxed);
    match next.task {
        Some(task) if task.state == TaskState::Suspended
            && next.promise.state == PromiseState::Pending
            && next.promise.timeout_at > now => {
                let awaited = choose|awaited: Seq<char>|
                    objects.contains_key(awaited)
                        && objects[awaited].promise.callbacks.contains(id);
                assert(objects.contains_key(awaited));
                if awaited == id {
                    assert(next.promise.callbacks
                        == objects[id].promise.callbacks);
                } else {
                    assert(updated[awaited] == objects[awaited]);
                }
                assert(updated.contains_key(awaited));
                assert(updated[awaited].promise.callbacks.contains(id));
            },
        _ => {},
    }
    assert(suspended_rung_relaxed(updated, id, next, now));
    lemma_replace_same_callbacks(name, objects, id, next, now);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(5)]
proof fn lemma_register_listener_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: PromiseRegisterListenerReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.awaited@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::PromiseRegisterListener(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    lemma_relaxed_closed(name, objects, now);
    if objects.contains_key(request.awaited@) {
        let old = spec_project_obj(objects[request.awaited@], now);
        assert(old == objects[request.awaited@]);
        if spec_awaitable(old.promise.tags)
            && old.promise.state == PromiseState::Pending
        {
            lemma_add_listener_to_object(
                name,
                objects,
                request.awaited@,
                request.address@,
                now,
            );
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(10)]
proof fn lemma_promise_settle_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: PromiseSettleReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::PromiseSettle(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    reveal(promise_relaxed);
    reveal(task_relaxed);
    lemma_relaxed_closed(name, objects, now);
    if request.state.spec_settable() && objects.contains_key(request.id@) {
        let seen = spec_project_obj(objects[request.id@], now);
        assert(seen == objects[request.id@]);
        if seen.promise.state == PromiseState::Pending {
            let promise = PromV {
                state: request.state,
                value: request.value,
                settled_at: Some(now),
                ..seen.promise
            };
            let task = match seen.task {
                Some(t) if t.state != TaskState::Fulfilled =>
                    Some(crate::node::spec_fulfill_task(t)),
                other => other,
            };
            let object = ObjV { promise, task };
            assert(promise_relaxed(request.id@, object, now));
            assert(task_relaxed(object));
            lemma_replace_same_callbacks(
                name,
                objects,
                request.id@,
                object,
                now,
            );
        }
    }
}

proof fn lemma_extend_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    pid: Seq<char>,
    tasks: Seq<TaskRef>,
    index: int,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        0 <= index <= tasks.len(),
        forall|id: Seq<char>| objects.contains_key(id) ==>
            spec_project_obj(objects[id], now) == objects[id],
    ensures
        ({
            let updated = crate::node::spec_extend(
                objects,
                pid,
                tasks,
                now,
                index,
            );
            &&& workflow_relaxed(name, updated, now)
            &&& forall|id: Seq<char>| updated.contains_key(id) ==>
                spec_project_obj(updated[id], now) == updated[id]
        }),
    decreases tasks.len() - index,
{
    if index < tasks.len() {
        let id = tasks[index].id@;
        if !objects.contains_key(id) {
            lemma_extend_preserves_relaxed(
                name,
                objects,
                pid,
                tasks,
                index + 1,
                now,
            );
        } else {
            let object = spec_project_obj(objects[id], now);
            assert(object == objects[id]);
            match object.task {
                Some(task) if task.state == TaskState::Acquired
                    && task.version == tasks[index].version
                    && task.pid == Some(pid) => {
                        let ttl = task.ttl.unwrap();
                        let at = spec_sat_add(now, ttl);
                        let next = ObjV {
                            task: Some(TkV {
                                lease_timeout_at: Some(at),
                                ..task
                            }),
                            ..object
                        };
                        let updated = objects.insert(id, next);
                        assert(0 < ttl <= MAX_TIME);
                        assert(at > now);
                        assert(promise_relaxed(id, next, now));
                        assert(task_relaxed(next));
                        assert(suspended_rung_relaxed(
                            updated,
                            id,
                            next,
                            now,
                        ));
                        lemma_replace_same_callbacks(
                            name,
                            objects,
                            id,
                            next,
                            now,
                        );
                        assert forall|x: Seq<char>|
                            updated.contains_key(x) implies
                            spec_project_obj(updated[x], now) == updated[x] by {
                            if x == id {
                                assert(updated[x] == next);
                            } else {
                                assert(updated[x] == objects[x]);
                            }
                        };
                        lemma_extend_preserves_relaxed(
                            name,
                            updated,
                            pid,
                            tasks,
                            index + 1,
                            now,
                        );
                    },
                _ => {
                    lemma_extend_preserves_relaxed(
                        name,
                        objects,
                        pid,
                        tasks,
                        index + 1,
                        now,
                    );
                },
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(5)]
proof fn lemma_task_halt_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: TaskHaltReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::TaskHalt(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    lemma_relaxed_closed(name, objects, now);
    if objects.contains_key(request.id@) {
        let object = spec_project_obj(objects[request.id@], now);
        assert(object == objects[request.id@]);
        match object.task {
            Some(task) if task.state != TaskState::Fulfilled
                && task.state != TaskState::Halted => {
                    let next = ObjV {
                        task: Some(spec_unlease(
                            task,
                            TaskState::Halted,
                            None,
                        )),
                        ..object
                    };
                    let updated = objects.insert(request.id@, next);
                    assert(promise_relaxed(request.id@, next, now));
                    assert(task_relaxed(next));
                    assert(suspended_rung_relaxed(
                        updated,
                        request.id@,
                        next,
                        now,
                    ));
                    lemma_replace_same_callbacks(
                        name,
                        objects,
                        request.id@,
                        next,
                        now,
                    );
                },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(5)]
proof fn lemma_task_continue_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: TaskContinueReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::TaskContinue(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    lemma_relaxed_closed(name, objects, now);
    if objects.contains_key(request.id@) {
        let object = spec_project_obj(objects[request.id@], now);
        assert(object == objects[request.id@]);
        match object.task {
            Some(task) if task.state == TaskState::Halted
                && object.promise.state == PromiseState::Pending => {
                    let next = ObjV {
                        task: Some(TkV {
                            state: TaskState::Pending,
                            retry_timeout_at: Some(now),
                            ..task
                        }),
                        ..object
                    };
                    let updated = objects.insert(request.id@, next);
                    assert(promise_relaxed(request.id@, next, now));
                    assert(task_relaxed(next));
                    assert(suspended_rung_relaxed(
                        updated,
                        request.id@,
                        next,
                        now,
                    ));
                    lemma_replace_same_callbacks(
                        name,
                        objects,
                        request.id@,
                        next,
                        now,
                    );
                },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(5)]
proof fn lemma_task_release_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: TaskReleaseReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::TaskRelease(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    lemma_relaxed_closed(name, objects, now);
    if objects.contains_key(request.id@) {
        let object = spec_project_obj(objects[request.id@], now);
        assert(object == objects[request.id@]);
        match object.task {
            Some(task) if task.state == TaskState::Acquired
                && task.version == request.version
                && object.promise.state == PromiseState::Pending => {
                    let next = ObjV {
                        task: Some(spec_unlease(
                            task,
                            TaskState::Pending,
                            Some(now),
                        )),
                        ..object
                    };
                    let updated = objects.insert(request.id@, next);
                    assert(promise_relaxed(request.id@, next, now));
                    assert(task_relaxed(next));
                    assert(suspended_rung_relaxed(
                        updated,
                        request.id@,
                        next,
                        now,
                    ));
                    lemma_replace_same_callbacks(
                        name,
                        objects,
                        request.id@,
                        next,
                        now,
                    );
                },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(5)]
proof fn lemma_task_fence_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: TaskFenceReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::TaskFence(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    lemma_relaxed_closed(name, objects, now);
    let target = match request.action {
        TaskFenceAction::Create(action) => action.id@,
        TaskFenceAction::Settle(action) => action.id@,
    };
    if target != request.id@
        && echod_types::same_origin_spec(target, request.id@)
        && objects.contains_key(request.id@)
    {
        let object = spec_project_obj(objects[request.id@], now);
        assert(object == objects[request.id@]);
        match object.task {
            Some(task) if task.state == TaskState::Acquired
                && task.version == request.version
                && object.promise.state == PromiseState::Pending => {
                    assert(origin(target) == name);
                    match request.action {
                        TaskFenceAction::Create(action) => {
                            lemma_promise_create_preserves_relaxed(
                                name,
                                objects,
                                action,
                                now,
                            );
                        },
                        TaskFenceAction::Settle(action) => {
                            lemma_promise_settle_preserves_relaxed(
                                name,
                                objects,
                                action,
                                now,
                            );
                        },
                    }
                },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(5)]
proof fn lemma_task_acquire_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: TaskAcquireReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::TaskAcquire(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    lemma_relaxed_closed(name, objects, now);
    if 0 < request.ttl <= MAX_TIME && objects.contains_key(request.id@) {
        let object = spec_project_obj(objects[request.id@], now);
        assert(object == objects[request.id@]);
        match object.task {
            Some(task) if task.state == TaskState::Pending
                && task.version == request.version
                && object.promise.state == PromiseState::Pending
                && task.version < MAX_VERSION => {
                    let acquired = crate::node::spec_acquire(
                        task,
                        request.pid@,
                        request.ttl,
                        now,
                    );
                    let next = ObjV { task: Some(acquired), ..object };
                    let updated = objects.insert(request.id@, next);
                    assert(spec_sat_add(now, request.ttl) > now);
                    assert(promise_relaxed(request.id@, next, now));
                    assert(task_relaxed(next));
                    assert(suspended_rung_relaxed(
                        updated,
                        request.id@,
                        next,
                        now,
                    ));
                    lemma_replace_same_callbacks(
                        name,
                        objects,
                        request.id@,
                        next,
                        now,
                    );
                },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(5)]
proof fn lemma_task_fulfill_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: TaskFulfillReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::TaskFulfill(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    lemma_relaxed_closed(name, objects, now);
    if request.action.state.spec_settable()
        && objects.contains_key(request.id@)
    {
        let object = spec_project_obj(objects[request.id@], now);
        assert(object == objects[request.id@]);
        match object.task {
            Some(task) if task.state == TaskState::Acquired
                && task.version == request.version
                && object.promise.state == PromiseState::Pending => {
                    let promise = PromV {
                        state: request.action.state,
                        value: request.action.value,
                        settled_at: Some(now),
                        ..object.promise
                    };
                    let next = ObjV {
                        promise,
                        task: Some(crate::node::spec_fulfill_task(task)),
                    };
                    let updated = objects.insert(request.id@, next);
                    assert(promise_relaxed(request.id@, next, now));
                    assert(task_relaxed(next));
                    assert(suspended_rung_relaxed(
                        updated,
                        request.id@,
                        next,
                        now,
                    ));
                    lemma_replace_same_callbacks(
                        name,
                        objects,
                        request.id@,
                        next,
                        now,
                    );
                },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(5)]
proof fn lemma_task_create_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: TaskCreateReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.action.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::TaskCreate(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    lemma_relaxed_closed(name, objects, now);
    if request.ttl == 0
        || request.ttl > MAX_TIME
        || request.action.timeout_at > MAX_TIME
        || !spec_targeted(request.action.tags)
        || crate::node::spec_timer(request.action.tags)
    {
        return;
    }
    lemma_promise_create_preserves_relaxed(
        name,
        objects,
        request.action,
        now,
    );
    let created_doc = crate::node::spec_promise_create(
        DocumentBodyV::Workflow(objects),
        request.action,
        now,
    ).0;
    assert(created_doc is Workflow);
    let created = created_doc->Workflow_0;
    assert(workflow_relaxed(name, created, now));
    assert(created.contains_key(request.action.id@));
    let seen = spec_project_obj(created[request.action.id@], now);
    assert(seen == created[request.action.id@]);
    if spec_targeted(seen.promise.tags) {
        match seen.task {
            Some(task) if task.state == TaskState::Pending
                && task.version < MAX_VERSION => {
                    let acquired = crate::node::spec_acquire(
                        task,
                        request.pid@,
                        request.ttl,
                        now,
                    );
                    let next = ObjV { task: Some(acquired), ..seen };
                    let updated = created.insert(request.action.id@, next);
                    assert(spec_sat_add(now, request.ttl) > now);
                    assert(promise_relaxed(request.action.id@, next, now));
                    assert(task_relaxed(next));
                    assert(suspended_rung_relaxed(
                        updated,
                        request.action.id@,
                        next,
                        now,
                    ));
                    lemma_replace_same_callbacks(
                        name,
                        created,
                        request.action.id@,
                        next,
                        now,
                    );
                },
            _ => {},
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(10)]
proof fn lemma_heartbeat_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: TaskHeartbeatReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        request.tasks@.len() > 0,
        origin(request.tasks@[0].id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::TaskHeartbeat(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    lemma_relaxed_closed(name, objects, now);
    lemma_extend_preserves_relaxed(
        name,
        objects,
        request.pid@,
        request.tasks@,
        0,
        now,
    );
}

#[verifier::spinoff_prover]
#[verifier::rlimit(10)]
proof fn lemma_task_suspend_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: TaskSuspendReq,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        origin(request.id@) == name,
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
    ensures
        ({
            let next = spec_handle(
                DocumentBodyV::Workflow(objects),
                Request::TaskSuspend(request),
                now,
            ).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    reveal(workflow_relaxed);
    lemma_relaxed_closed(name, objects, now);
    let actions = request.actions@;
    if actions.len() == 0
        || crate::node::spec_bad_suspend(actions, request.id@, 0)
        || !crate::node::spec_distinct_awaited(actions, 0)
    {
        return;
    }
    let held = crate::node::spec_held(
        objects,
        request.id@,
        request.version,
        now,
    ).1;
    match held {
        crate::node::Held::Missing | crate::node::Held::Stale => {},
        crate::node::Held::Ok(object) => {
            assert(object == objects[request.id@]);
            if crate::node::spec_missing_awaited(objects, actions, 0)
                || crate::node::spec_unawaitable(objects, actions, 0)
            {
                return;
            }
            if crate::node::spec_any_settled(objects, actions, now, 0) {
                let task = match object.task {
                    Some(t) => Some(TkV { resumes: Seq::empty(), ..t }),
                    None => None,
                };
                let next = ObjV { task, ..object };
                assert(promise_relaxed(request.id@, next, now));
                assert(task_relaxed(next));
                assert(suspended_rung_relaxed(
                    objects.insert(request.id@, next),
                    request.id@,
                    next,
                    now,
                ));
                lemma_replace_same_callbacks(
                    name,
                    objects,
                    request.id@,
                    next,
                    now,
                );
            } else {
                crate::handlers::lemma_bad_suspend_from(
                    actions,
                    request.id@,
                    0,
                );
                crate::handlers::lemma_distinct_from(actions, 0);
                crate::handlers::lemma_missing_from(objects, actions, 0);
                crate::handlers::lemma_unawaitable_from(objects, actions, 0);
                crate::handlers::lemma_c_any_settled_from(
                    objects,
                    actions,
                    now,
                    0,
                );
                assert forall|i: int| 0 <= i < actions.len() implies {
                    let awaited = (#[trigger] actions[i]).awaited@;
                    &&& objects.contains_key(awaited)
                    &&& awaited != request.id@
                    &&& objects[awaited].promise.state == PromiseState::Pending
                    &&& spec_awaitable(objects[awaited].promise.tags)
                } by {
                    let awaited = actions[i].awaited@;
                    assert(spec_project_obj(objects[awaited], now)
                        == objects[awaited]);
                };
                assert(spec_targeted(objects[request.id@].promise.tags));
                assert forall|i: int, j: int| 0 <= i < j < actions.len() implies
                    (#[trigger] actions[i]).awaited@
                        != (#[trigger] actions[j]).awaited@ by {};
                lemma_add_callbacks_preserves_relaxed(
                    name,
                    objects,
                    request.id@,
                    actions,
                    0,
                    now,
                );
                let with_callbacks = crate::node::spec_add_callbacks(
                    objects,
                    request.id@,
                    actions,
                    0,
                );
                let current = with_callbacks[request.id@];
                assert(current == objects[request.id@]);
                let task = match current.task {
                    Some(t) => Some(TkV {
                        resumes: Seq::empty(),
                        ..spec_unlease(t, TaskState::Suspended, None)
                    }),
                    None => None,
                };
                let next = ObjV { task, ..current };
                let updated = with_callbacks.insert(request.id@, next);
                assert(promise_relaxed(request.id@, next, now));
                assert(task_relaxed(next));
                assert(with_callbacks[actions[0].awaited@]
                    .promise.callbacks.contains(request.id@));
                assert(actions[0].awaited@ != request.id@);
                assert(updated.contains_key(actions[0].awaited@));
                assert(updated[actions[0].awaited@]
                    == with_callbacks[actions[0].awaited@]);
                assert(updated[actions[0].awaited@]
                    .promise.callbacks.contains(request.id@));
                reveal(suspended_rung_relaxed);
                assert(suspended_rung_relaxed(
                    updated,
                    request.id@,
                    next,
                    now,
                ));
                lemma_replace_same_callbacks(
                    name,
                    with_callbacks,
                    request.id@,
                    next,
                    now,
                );
            }
        },
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(1)]
pub proof fn lemma_handle_preserves_relaxed(
    name: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    request: Request,
    now: u64,
)
    requires
        workflow_relaxed(name, objects, now),
        request_document(request) == Some(name),
        spec_earliest_in(DocumentBodyV::Workflow(objects), now) is None,
        !matches!(request, Request::ScheduleGet(_)
            | Request::ScheduleCreate(_) | Request::ScheduleDelete(_)),
    ensures
        ({
            let next = spec_handle(DocumentBodyV::Workflow(objects), request, now).0;
            next is Workflow && workflow_relaxed(name, next->Workflow_0, now)
        }),
{
    let next = spec_handle(DocumentBodyV::Workflow(objects), request, now).0;
    match request {
        Request::PromiseGet(_) => {
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::PromiseCreate(q) => {
            lemma_promise_create_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::PromiseSettle(q) => {
            lemma_promise_settle_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::PromiseRegisterCallback(q) => {
            lemma_register_callback_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::PromiseRegisterListener(q) => {
            lemma_register_listener_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskGet(_) => {
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskCreate(q) => {
            lemma_task_create_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskAcquire(q) => {
            lemma_task_acquire_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskFulfill(q) => {
            lemma_task_fulfill_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskRelease(q) => {
            lemma_task_release_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskHalt(q) => {
            lemma_task_halt_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskContinue(q) => {
            lemma_task_continue_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskFence(q) => {
            lemma_task_fence_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskFenceCheck(_) => {
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskSuspend(q) => {
            lemma_task_suspend_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        Request::TaskHeartbeat(q) => {
            lemma_heartbeat_preserves_relaxed(name, objects, q, now);
            assert(next is Workflow && workflow_relaxed(name, next->Workflow_0, now)) by {};
        },
        _ => {},
    }
}

/// Apply an existing request handler's update to the stored document.
pub open spec fn on_request(
    document: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
    limit: nat,
) -> StoredDocumentV {
    let (body, response, _, _) = spec_request_transition(
        spec_stored_body(document),
        request,
        now,
        retry_timeout,
        limit,
    );
    if response == spec_unavailable(request) {
        document
    } else if body == spec_stored_body(document) {
        document
    } else {
        spec_advance_stored(document, body, now)
    }
}

pub open spec fn request_document(request: Request) -> Option<Seq<char>> {
    match request {
        Request::PromiseGet(q) => Some(origin(q.id@)),
        Request::PromiseCreate(q) => Some(origin(q.id@)),
        Request::PromiseSettle(q) => Some(origin(q.id@)),
        Request::PromiseRegisterCallback(q) => Some(origin(q.awaited@)),
        Request::PromiseRegisterListener(q) => Some(origin(q.awaited@)),
        Request::TaskGet(q) => Some(origin(q.id@)),
        Request::TaskCreate(q) => Some(origin(q.action.id@)),
        Request::TaskAcquire(q) => Some(origin(q.id@)),
        Request::TaskFulfill(q) => Some(origin(q.id@)),
        Request::TaskRelease(q) => Some(origin(q.id@)),
        Request::TaskHalt(q) => Some(origin(q.id@)),
        Request::TaskContinue(q) => Some(origin(q.id@)),
        Request::TaskFence(q) => Some(origin(q.id@)),
        Request::TaskFenceCheck(q) => Some(origin(q.id@)),
        Request::TaskSuspend(q) => Some(origin(q.id@)),
        Request::TaskHeartbeat(q) =>
            if q.tasks@.len() == 0 { None } else { Some(origin(q.tasks@[0].id@)) },
        Request::ScheduleGet(q) => Some(q.id@),
        Request::ScheduleCreate(q) => Some(q.id@),
        Request::ScheduleDelete(q) => Some(q.id@),
    }
}

pub open spec fn request_matches(document: StoredDocumentV, request: Request) -> bool {
    &&& request_document(request) == Some(spec_stored_name(document))
    &&& match (document, request) {
        (StoredDocumentV::Schedule(_), Request::ScheduleGet(_))
        | (StoredDocumentV::Schedule(_), Request::ScheduleCreate(_))
        | (StoredDocumentV::Schedule(_), Request::ScheduleDelete(_)) => true,
        (StoredDocumentV::Workflow(_), Request::ScheduleGet(_))
        | (StoredDocumentV::Workflow(_), Request::ScheduleCreate(_))
        | (StoredDocumentV::Workflow(_), Request::ScheduleDelete(_)) => false,
        (StoredDocumentV::Workflow(_), _) => true,
        (StoredDocumentV::Schedule(_), _) => false,
    }
}

pub open spec fn routed(document: StoredDocumentV, request: Request) -> bool {
    request_matches(document, request)
}

proof fn lemma_key_names_document(request: Request)
    ensures
        match (spec_key(request), spec_request_document(request)) {
            (Some(key), Some(document)) => key.skip(2) == document,
            (None, None) => true,
            _ => false,
        },
{
    match request {
        Request::PromiseGet(_)
        | Request::PromiseCreate(_)
        | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_)
        | Request::PromiseRegisterListener(_)
        | Request::TaskGet(_)
        | Request::TaskCreate(_)
        | Request::TaskAcquire(_)
        | Request::TaskFulfill(_)
        | Request::TaskRelease(_)
        | Request::TaskHalt(_)
        | Request::TaskContinue(_)
        | Request::TaskFence(_)
        | Request::TaskFenceCheck(_)
        | Request::TaskSuspend(_) => {
            lemma_origin_key(spec_request_document(request)->0);
        },
        Request::TaskHeartbeat(q) => {
            if q.tasks@.len() > 0 {
                lemma_origin_key(spec_request_document(request)->0);
            }
        },
        Request::ScheduleGet(_)
        | Request::ScheduleCreate(_)
        | Request::ScheduleDelete(_) => {
            lemma_schedule_key(spec_request_document(request)->0);
        },
    }
}

proof fn lemma_routed_document(document: StoredDocumentV, request: Request)
    requires
        routed(document, request),
    ensures
        spec_request_document(request) == Some(spec_stored_name(document)),
{
    lemma_key_names_document(request);
    match document {
        StoredDocumentV::Workflow(workflow) => {
            lemma_origin_key(workflow.document);
        },
        StoredDocumentV::Schedule(schedule) => {
            lemma_schedule_key(schedule.document);
        },
    }
}

/// A complete request transition preserves the full stored-document
/// invariant.  The process clamps `now` to the previous commit instant and
/// validates client time values against `MAX_TIME`; the explicit hypotheses
/// state those two boundary facts here.
pub proof fn request_preserves_well_formed(
    document: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
)
    requires
        well_formed(document),
        request_matches(document, request),
        spec_stored_committed_at(document) <= now,
        now <= MAX_TIME,
        0 < retry_timeout <= MAX_TIME,
    ensures
        well_formed(on_request(document, request, now, retry_timeout, REQUEST_SWEEP_STEPS as nat)),
{
    let transition = spec_request_transition(
        spec_stored_body(document),
        request,
        now,
        retry_timeout,
        REQUEST_SWEEP_STEPS as nat,
    );
    if transition.1 == spec_unavailable(request) {
        assert(on_request(document, request, now, retry_timeout, REQUEST_SWEEP_STEPS as nat) == document);
        return;
    }
    if transition.0 == spec_stored_body(document) {
        assert(on_request(document, request, now, retry_timeout, REQUEST_SWEEP_STEPS as nat) == document);
        return;
    }
    match document {
        StoredDocumentV::Schedule(_) => {
            match request {
                Request::ScheduleGet(_) => {
                    assert(well_formed(on_request(document, request, now, retry_timeout, REQUEST_SWEEP_STEPS as nat)));
                },
                Request::ScheduleCreate(q) => {
                    reveal(echod_types::spec_deadline_bounded);
                    echod_abstract::trusted::axiom_next_cron_after(q.cron@, now);
                    assert(well_formed(on_request(document, request, now, retry_timeout, REQUEST_SWEEP_STEPS as nat)));
                },
                Request::ScheduleDelete(_) => {
                    assert(well_formed(on_request(document, request, now, retry_timeout, REQUEST_SWEEP_STEPS as nat)));
                },
                _ => {},
            }
        },
        StoredDocumentV::Workflow(workflow) => {
            let limit = REQUEST_SWEEP_STEPS as nat;
            let original = DocumentBodyV::Workflow(workflow.objects);
            lemma_full_implies_relaxed(workflow, now);
            lemma_sweep_preserves_relaxed(
                workflow.document,
                workflow.objects,
                now,
                retry_timeout,
                limit,
            );
            let swept = spec_sweep(original, now, retry_timeout, limit).0;
            assert(swept is Workflow);
            assert(spec_earliest_in(swept, now) is None);
            lemma_handle_preserves_relaxed(
                workflow.document,
                swept->Workflow_0,
                request,
                now,
            );
            let handled = spec_handle(swept, request, now).0;
            assert(handled is Workflow);
            lemma_sweep_preserves_relaxed(
                workflow.document,
                handled->Workflow_0,
                now,
                retry_timeout,
                limit,
            );
            let closed = spec_sweep(handled, now, retry_timeout, limit).0;
            assert(closed is Workflow);
            assert(spec_earliest_in(closed, now) is None);
            lemma_relaxed_closed(
                workflow.document,
                closed->Workflow_0,
                now,
            );
            assert(well_formed(on_request(document, request, now, retry_timeout, REQUEST_SWEEP_STEPS as nat)));
        },
    }
}

} // verus!
