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
use crate::state::spec_sat_add;
#[cfg(verus_keep_ghost)]
use crate::document::{
    callback_targets_well_formed, promise_well_formed, suspended_rung_well_formed,
    task_cleared, task_well_formed, unique, value_empty, well_formed, ObjV, PromV,
    StoredDocumentV, TkV, WorkflowDocumentV,
};
#[cfg(verus_keep_ghost)]
use crate::state::{
    spec_advance_stored, spec_awaitable, spec_body_deadline, spec_earliest_in,
    spec_due_id, spec_handle, spec_key, spec_obj_due, spec_project_obj, spec_request_document, spec_request_transition,
    spec_resume, spec_run_due, spec_sorted, spec_sorted_present, spec_stored_body, spec_sweep,
    spec_stored_committed_at, spec_stored_name, spec_targeted, spec_unavailable,
    spec_unlease, DocumentBodyV, REQUEST_SWEEP_STEPS,
};


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

} // verus!
