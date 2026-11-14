//! Executable identifier bounds for production document transitions.
//!
//! This module isolates the only fact needed by invariant 1 about workflow
//! identifiers: every key in a retained workflow map is representable by
//! Rust's indexing type.  Most concrete transitions only replace values at
//! existing keys; the few transitions that insert a key cross an explicit
//! executable `String` boundary.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_concrete::document::document_ids_bounded;
#[cfg(verus_keep_ghost)]
use echod_concrete::node::{DocumentBodyV, ObjV, PendingV, StoredDocumentV};

#[cfg(verus_keep_ghost)]
verus! {

pub open spec fn workflow_ids_bounded(
    map: Map<Seq<char>, ObjV>,
) -> bool {
    forall|id: Seq<char>| map.contains_key(id) ==>
        id.len() <= usize::MAX as int
}

pub open spec fn body_ids_bounded(body: DocumentBodyV) -> bool {
    match body {
        DocumentBodyV::Workflow(map) => workflow_ids_bounded(map),
        DocumentBodyV::Schedule(_) => true,
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_stored_body_ids_bounded(
    stored: StoredDocumentV,
)
    requires
        document_ids_bounded(stored),
    ensures
        body_ids_bounded(echod_concrete::node::spec_stored_body(stored)),
{
    reveal(document_ids_bounded);
    reveal(body_ids_bounded);
    reveal(workflow_ids_bounded);
    reveal(echod_concrete::node::spec_stored_body);
}

#[verifier::spinoff_prover]
pub proof fn lemma_advance_stored_ids_bounded(
    before: StoredDocumentV,
    body: DocumentBodyV,
    committed_at: u64,
)
    requires
        body_ids_bounded(body),
    ensures
        document_ids_bounded(
            echod_concrete::node::spec_advance_stored(
                before,
                body,
                committed_at,
            ),
        ),
{
    reveal(document_ids_bounded);
    reveal(body_ids_bounded);
    reveal(workflow_ids_bounded);
    reveal(echod_concrete::node::spec_advance_stored);
}

#[verifier::spinoff_prover]
proof fn lemma_insert_existing_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    object: ObjV,
)
    requires
        workflow_ids_bounded(map),
        map.contains_key(id),
    ensures
        workflow_ids_bounded(map.insert(id, object)),
{
    reveal(workflow_ids_bounded);
}

#[verifier::spinoff_prover]
proof fn lemma_insert_bounded_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    object: ObjV,
)
    requires
        workflow_ids_bounded(map),
        id.len() <= usize::MAX as int,
    ensures
        workflow_ids_bounded(map.insert(id, object)),
{
    reveal(workflow_ids_bounded);
}

#[verifier::spinoff_prover]
proof fn lemma_spec_extend_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    pid: Seq<char>,
    tasks: Seq<echod_types::TaskRef>,
    now: u64,
    i: int,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_extend(
                map,
                pid,
                tasks,
                now,
                i,
            ),
        ),
    decreases tasks.len() - i,
{
    reveal_with_fuel(echod_concrete::node::spec_extend, 1);
    if 0 <= i && i < tasks.len() && map.contains_key(tasks[i].id@) {
        let object = echod_concrete::node::spec_project_obj(
            map[tasks[i].id@],
            now,
        );
        match object.task {
            Some(task) if task.state == echod_types::TaskState::Acquired
                && task.version == tasks[i].version
                && task.pid == Some(pid) => {
                let ttl = match task.ttl {
                    Some(value) => value,
                    None => 0,
                };
                let at = echod_concrete::store::spec_sat_add(now, ttl);
                let next = ObjV {
                    task: Some(echod_concrete::node::TkV {
                        lease_timeout_at: Some(at),
                        ..task
                    }),
                    ..object
                };
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    tasks[i].id@,
                    next,
                );
                lemma_spec_extend_preserves_ids_bounded(
                    map.insert(tasks[i].id@, next),
                    pid,
                    tasks,
                    now,
                    i + 1,
                );
            },
            _ => {
                lemma_spec_extend_preserves_ids_bounded(
                    map,
                    pid,
                    tasks,
                    now,
                    i + 1,
                );
            },
        }
    } else if 0 <= i && i < tasks.len() {
        lemma_spec_extend_preserves_ids_bounded(
            map,
            pid,
            tasks,
            now,
            i + 1,
        );
    }
}

#[verifier::spinoff_prover]
proof fn lemma_spec_add_callbacks_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    actions: Seq<echod_types::PromiseRegisterCallbackReq>,
    i: int,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_add_callbacks(
                map,
                id,
                actions,
                i,
            ),
        ),
    decreases actions.len() - i,
{
    reveal_with_fuel(echod_concrete::node::spec_add_callbacks, 1);
    if 0 <= i && i < actions.len()
        && map.contains_key(actions[i].awaited@)
    {
        let object = map[actions[i].awaited@];
        let callbacks =
            if object.promise.callbacks.contains(id) {
                object.promise.callbacks
            } else {
                object.promise.callbacks.push(id)
            };
        let next = ObjV {
            promise: echod_concrete::node::PromV {
                callbacks,
                ..object.promise
            },
            ..object
        };
        lemma_insert_existing_preserves_ids_bounded(
            map,
            actions[i].awaited@,
            next,
        );
        lemma_spec_add_callbacks_preserves_ids_bounded(
            map.insert(actions[i].awaited@, next),
            id,
            actions,
            i + 1,
        );
    } else if 0 <= i && i < actions.len() {
        lemma_spec_add_callbacks_preserves_ids_bounded(
            map,
            id,
            actions,
            i + 1,
        );
    }
}

#[verifier::spinoff_prover]
proof fn lemma_spec_resume_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    awaiter: Seq<char>,
    awaited: Seq<char>,
    since: u64,
    now: u64,
    retry_timeout: u64,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_resume(
                map,
                awaiter,
                awaited,
                since,
                now,
                retry_timeout,
            ),
        ),
{
    reveal(echod_concrete::node::spec_resume);
    if map.contains_key(awaiter) {
        lemma_insert_existing_preserves_ids_bounded(
            map,
            awaiter,
            map[awaiter],
        );
    }
}

#[verifier::spinoff_prover]
proof fn lemma_spec_project_keys_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: u64,
    retry_timeout: u64,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_project_keys(
                map,
                keys,
                count,
                now,
                retry_timeout,
            ),
        ),
    decreases count,
{
    reveal_with_fuel(echod_concrete::node::spec_project_keys, 1);
    if count > 0 {
        lemma_spec_project_keys_preserves_ids_bounded(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = echod_concrete::node::spec_project_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let id = keys[count as int - 1];
        if prior.contains_key(id) {
            lemma_insert_existing_preserves_ids_bounded(
                prior,
                id,
                echod_concrete::node::spec_project_due_object(
                    prior[id],
                    now,
                    retry_timeout,
                ),
            );
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_spec_resume_callbacks_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    callbacks: Seq<Seq<char>>,
    count: nat,
    awaited: Seq<char>,
    since: u64,
    now: u64,
    retry_timeout: u64,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_resume_callbacks(
                map,
                callbacks,
                count,
                awaited,
                since,
                now,
                retry_timeout,
            ),
        ),
    decreases count,
{
    reveal_with_fuel(
        echod_concrete::node::spec_resume_callbacks,
        1,
    );
    if count > 0 {
        lemma_spec_resume_callbacks_preserves_ids_bounded(
            map,
            callbacks,
            (count - 1) as nat,
            awaited,
            since,
            now,
            retry_timeout,
        );
        let prior = echod_concrete::node::spec_resume_callbacks(
            map,
            callbacks,
            (count - 1) as nat,
            awaited,
            since,
            now,
            retry_timeout,
        );
        lemma_spec_resume_preserves_ids_bounded(
            prior,
            callbacks[count as int - 1],
            awaited,
            since,
            now,
            retry_timeout,
        );
    }
}

#[verifier::spinoff_prover]
proof fn lemma_spec_drain_callbacks_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    count: nat,
    now: u64,
    retry_timeout: u64,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_drain_callbacks(
                map,
                id,
                count,
                now,
                retry_timeout,
            ),
        ),
    decreases count,
{
    reveal_with_fuel(echod_concrete::node::spec_drain_callbacks, 1);
    if count > 0 {
        lemma_spec_drain_callbacks_preserves_ids_bounded(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = echod_concrete::node::spec_drain_callbacks(
            map,
            id,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        if prior.contains_key(id)
            && prior[id].promise.callbacks.len() > 0
        {
            let object = prior[id];
            let popped = prior.insert(id, ObjV {
                promise: echod_concrete::node::PromV {
                    callbacks: object.promise.callbacks.skip(1),
                    ..object.promise
                },
                ..object
            });
            lemma_insert_existing_preserves_ids_bounded(
                prior,
                id,
                object,
            );
            lemma_spec_resume_preserves_ids_bounded(
                popped,
                object.promise.callbacks[0],
                id,
                match object.promise.settled_at {
                    Some(at) => at,
                    None => 0,
                },
                now,
                retry_timeout,
            );
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_spec_drain_settled_callbacks_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: u64,
    retry_timeout: u64,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_drain_settled_callbacks(
                map,
                id,
                now,
                retry_timeout,
            ),
        ),
{
    reveal(echod_concrete::node::spec_drain_settled_callbacks);
    if map.contains_key(id)
        && map[id].promise.state != echod_types::PromiseState::Pending
    {
        lemma_spec_drain_callbacks_preserves_ids_bounded(
            map,
            id,
            map[id].promise.callbacks.len(),
            now,
            retry_timeout,
        );
    }
}

#[verifier::spinoff_prover]
proof fn lemma_spec_drain_callback_keys_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: u64,
    retry_timeout: u64,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_drain_callback_keys(
                map,
                keys,
                count,
                now,
                retry_timeout,
            ),
        ),
    decreases count,
{
    reveal_with_fuel(
        echod_concrete::node::spec_drain_callback_keys,
        1,
    );
    if count > 0 {
        lemma_spec_drain_callback_keys_preserves_ids_bounded(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        let prior = echod_concrete::node::spec_drain_callback_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        lemma_spec_drain_settled_callbacks_preserves_ids_bounded(
            prior,
            keys[count as int - 1],
            now,
            retry_timeout,
        );
    }
}

#[verifier::spinoff_prover]
proof fn lemma_spec_clear_settled_listeners_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_clear_settled_listeners(map, id),
        ),
{
    reveal(echod_concrete::node::spec_clear_settled_listeners);
    if map.contains_key(id) {
        lemma_insert_existing_preserves_ids_bounded(
            map,
            id,
            map[id],
        );
    }
}

#[verifier::spinoff_prover]
proof fn lemma_spec_clear_listener_keys_preserves_ids_bounded(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        workflow_ids_bounded(map),
    ensures
        workflow_ids_bounded(
            echod_concrete::node::spec_clear_listener_keys(
                map,
                keys,
                count,
            ),
        ),
    decreases count,
{
    reveal_with_fuel(
        echod_concrete::node::spec_clear_listener_keys,
        1,
    );
    if count > 0 {
        lemma_spec_clear_listener_keys_preserves_ids_bounded(
            map,
            keys,
            (count - 1) as nat,
        );
        let prior = echod_concrete::node::spec_clear_listener_keys(
            map,
            keys,
            (count - 1) as nat,
        );
        lemma_spec_clear_settled_listeners_preserves_ids_bounded(
            prior,
            keys[count as int - 1],
        );
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_sweep_preserves_body_ids_bounded(
    body: DocumentBodyV,
    now: u64,
    retry_timeout: u64,
)
    requires
        body_ids_bounded(body),
    ensures
        body_ids_bounded(
            echod_concrete::node::spec_sweep(
                body,
                now,
                retry_timeout,
            ).0,
        ),
{
    reveal(echod_concrete::node::spec_sweep);
    reveal(echod_concrete::node::spec_project_workflow);
    reveal(echod_concrete::node::spec_drain_workflow);
    reveal(body_ids_bounded);
    reveal(workflow_ids_bounded);
    match body {
        DocumentBodyV::Workflow(map) => {
            let keys = echod_concrete::node::spec_sorted_present(map);
            lemma_spec_project_keys_preserves_ids_bounded(
                map,
                keys,
                keys.len(),
                now,
                retry_timeout,
            );
            let projected = echod_concrete::node::spec_project_workflow(
                map,
                now,
                retry_timeout,
            );
            assert(workflow_ids_bounded(projected));
            let projected_keys =
                echod_concrete::node::spec_sorted_present(projected);
            lemma_spec_drain_callback_keys_preserves_ids_bounded(
                projected,
                projected_keys,
                projected_keys.len(),
                now,
                retry_timeout,
            );
            let resumed = echod_concrete::node::spec_drain_callback_keys(
                projected,
                projected_keys,
                projected_keys.len(),
                now,
                retry_timeout,
            );
            assert(workflow_ids_bounded(resumed));
            lemma_spec_clear_listener_keys_preserves_ids_bounded(
                resumed,
                projected_keys,
                projected_keys.len(),
            );
            let drained =
                echod_concrete::node::spec_clear_listener_keys(
                    resumed,
                    projected_keys,
                    projected_keys.len(),
                );
            assert(workflow_ids_bounded(drained));
            assert(echod_concrete::node::spec_drain_workflow(
                projected,
                now,
                retry_timeout,
            ) == drained);
            assert(echod_concrete::node::spec_sweep(
                body,
                now,
                retry_timeout,
            ).0 == DocumentBodyV::Workflow(drained));
        },
        DocumentBodyV::Schedule(_) => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_promise_create_preserves_body_ids_bounded(
    body: DocumentBodyV,
    request: echod_types::PromiseCreateReq,
    now: u64,
)
    requires
        body_ids_bounded(body),
    ensures
        body_ids_bounded(
            echod_concrete::node::spec_promise_create(
                body,
                request,
                now,
            ).0,
        ),
{
    crate::verified::text::string_bounded(&request.id);
    reveal(echod_concrete::node::spec_promise_create);
    reveal(echod_concrete::node::spec_workflow_map);
    reveal(echod_concrete::node::spec_with_workflow);
    reveal(body_ids_bounded);
    reveal(workflow_ids_bounded);
    if request.timeout_at <= echod_types::MAX_TIME
        && !(echod_concrete::node::spec_timer(request.tags)
            && echod_concrete::node::spec_targeted(request.tags))
    {
        let map = echod_concrete::node::spec_workflow_map(body);
        if !map.contains_key(request.id@) {
            lemma_insert_bounded_preserves_ids_bounded(
                map,
                request.id@,
                echod_concrete::node::spec_new_obj(
                    request.timeout_at,
                    now,
                    request.param,
                    request.tags,
                    echod_concrete::node::spec_targeted(request.tags),
                ),
            );
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_handle_preserves_body_ids_bounded(
    body: DocumentBodyV,
    request: echod_types::Request,
    now: u64,
)
    requires
        body_ids_bounded(body),
    ensures
        body_ids_bounded(
            echod_concrete::node::spec_handle(body, request, now).0,
        ),
{
    reveal(echod_concrete::node::spec_handle);
    match request {
        echod_types::Request::PromiseGet(q) => {
            reveal(echod_concrete::node::spec_promise_get);
            reveal(echod_concrete::node::spec_opened);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
        },
        echod_types::Request::PromiseCreate(q) => {
            lemma_promise_create_preserves_body_ids_bounded(
                body,
                q,
                now,
            );
        },
        echod_types::Request::PromiseSettle(q) => {
            reveal(echod_concrete::node::spec_promise_settle);
            reveal(echod_concrete::node::spec_opened);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(
                echod_concrete::node::spec_opened(body),
            );
            if map.contains_key(q.id@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.id@,
                    map[q.id@],
                );
            }
        },
        echod_types::Request::PromiseRegisterCallback(q) => {
            reveal(echod_concrete::node::spec_register_callback);
            reveal(echod_concrete::node::spec_opened);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(
                echod_concrete::node::spec_opened(body),
            );
            if map.contains_key(q.awaited@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.awaited@,
                    map[q.awaited@],
                );
            }
        },
        echod_types::Request::PromiseRegisterListener(q) => {
            reveal(echod_concrete::node::spec_register_listener);
            reveal(echod_concrete::node::spec_opened);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(
                echod_concrete::node::spec_opened(body),
            );
            if map.contains_key(q.awaited@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.awaited@,
                    map[q.awaited@],
                );
            }
        },
        echod_types::Request::TaskGet(q) => {
            reveal(echod_concrete::node::spec_task_get);
            reveal(echod_concrete::node::spec_opened);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
        },
        echod_types::Request::TaskCreate(q) => {
            reveal(echod_concrete::node::spec_task_create);
            lemma_promise_create_preserves_body_ids_bounded(
                body,
                q.action,
                now,
            );
            let created =
                echod_concrete::node::spec_promise_create(
                    body,
                    q.action,
                    now,
                ).0;
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(created);
            if map.contains_key(q.action.id@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.action.id@,
                    map[q.action.id@],
                );
            }
        },
        echod_types::Request::TaskAcquire(q) => {
            reveal(echod_concrete::node::spec_task_acquire);
            reveal(echod_concrete::node::spec_opened);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(
                echod_concrete::node::spec_opened(body),
            );
            if map.contains_key(q.id@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.id@,
                    map[q.id@],
                );
            }
        },
        echod_types::Request::TaskFulfill(q) => {
            reveal(echod_concrete::node::spec_task_fulfill);
            reveal(echod_concrete::node::spec_held);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(body);
            if map.contains_key(q.id@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.id@,
                    map[q.id@],
                );
            }
        },
        echod_types::Request::TaskRelease(q) => {
            reveal(echod_concrete::node::spec_task_release);
            reveal(echod_concrete::node::spec_held);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(body);
            if map.contains_key(q.id@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.id@,
                    map[q.id@],
                );
            }
        },
        echod_types::Request::TaskHalt(q) => {
            reveal(echod_concrete::node::spec_task_halt);
            reveal(echod_concrete::node::spec_opened);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(
                echod_concrete::node::spec_opened(body),
            );
            if map.contains_key(q.id@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.id@,
                    map[q.id@],
                );
            }
        },
        echod_types::Request::TaskContinue(q) => {
            reveal(echod_concrete::node::spec_task_continue);
            reveal(echod_concrete::node::spec_opened);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(
                echod_concrete::node::spec_opened(body),
            );
            if map.contains_key(q.id@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.id@,
                    map[q.id@],
                );
            }
        },
        echod_types::Request::TaskHeartbeat(q) => {
            reveal(echod_concrete::node::spec_heartbeat);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            lemma_spec_extend_preserves_ids_bounded(
                echod_concrete::node::spec_workflow_map(body),
                q.pid@,
                q.tasks@,
                now,
                0,
            );
        },
        echod_types::Request::TaskSuspend(q) => {
            reveal(echod_concrete::node::spec_suspend);
            reveal(echod_concrete::node::spec_held);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            let map = echod_concrete::node::spec_workflow_map(body);
            lemma_spec_add_callbacks_preserves_ids_bounded(
                map,
                q.id@,
                q.actions@,
                0,
            );
            let callbacks =
                echod_concrete::node::spec_add_callbacks(
                    map,
                    q.id@,
                    q.actions@,
                    0,
                );
            if callbacks.contains_key(q.id@) {
                lemma_insert_existing_preserves_ids_bounded(
                    callbacks,
                    q.id@,
                    callbacks[q.id@],
                );
            }
            if map.contains_key(q.id@) {
                lemma_insert_existing_preserves_ids_bounded(
                    map,
                    q.id@,
                    map[q.id@],
                );
            }
        },
        echod_types::Request::TaskFence(q) => {
            reveal(echod_concrete::node::spec_fence);
            reveal(echod_concrete::node::spec_held);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
            match q.action {
                echod_types::TaskFenceAction::Create(action) => {
                    lemma_promise_create_preserves_body_ids_bounded(
                        echod_concrete::node::spec_with_workflow(
                            body,
                            echod_concrete::node::spec_workflow_map(body),
                        ),
                        action,
                        now,
                    );
                },
                echod_types::TaskFenceAction::Settle(action) => {
                    reveal(echod_concrete::node::spec_promise_settle);
                    reveal(echod_concrete::node::spec_opened);
                    let map =
                        echod_concrete::node::spec_workflow_map(body);
                    if map.contains_key(action.id@) {
                        lemma_insert_existing_preserves_ids_bounded(
                            map,
                            action.id@,
                            map[action.id@],
                        );
                    }
                },
            }
        },
        echod_types::Request::TaskFenceCheck(q) => {
            reveal(echod_concrete::node::spec_fence_check);
            reveal(echod_concrete::node::spec_held);
            reveal(echod_concrete::node::spec_workflow_map);
            reveal(echod_concrete::node::spec_with_workflow);
            reveal(body_ids_bounded);
            reveal(workflow_ids_bounded);
        },
        echod_types::Request::ScheduleGet(q) => {
            reveal(echod_concrete::node::spec_schedule_get);
            reveal(body_ids_bounded);
        },
        echod_types::Request::ScheduleCreate(q) => {
            reveal(echod_concrete::node::spec_schedule_create);
            reveal(body_ids_bounded);
        },
        echod_types::Request::ScheduleDelete(q) => {
            reveal(echod_concrete::node::spec_schedule_delete);
            reveal(body_ids_bounded);
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_fire_schedule_preserves_bounded_ids(
    body: DocumentBodyV,
    now: u64,
)
    requires
        body_ids_bounded(body),
    ensures
        body_ids_bounded(
            echod_concrete::node::spec_fire_schedule(body, now).0,
        ),
        forall|i: int|
            0 <= i
                && i
                    < echod_concrete::node::spec_fire_schedule(
                        body,
                        now,
                    ).1.len() ==>
                echod_concrete::node::spec_fire_schedule(
                    body,
                    now,
                ).1[i].promise.len() <= usize::MAX as int,
        forall|i: int|
            0 <= i
                && i
                    < echod_concrete::node::spec_fire_schedule(
                        body,
                        now,
                    ).1.len() ==>
                exists|carrier: String|
                    carrier@
                        == #[trigger] echod_concrete::node::spec_fire_schedule(
                            body,
                            now,
                        ).1[i].promise,
{
    reveal(echod_concrete::node::spec_fire_schedule);
    reveal(body_ids_bounded);
}

#[verifier::spinoff_prover]
pub proof fn lemma_occurrence_preserves_body_ids_bounded(
    body: DocumentBodyV,
    pending: PendingV,
    now: u64,
)
    requires
        body_ids_bounded(body),
        pending.promise.len() <= usize::MAX as int,
    ensures
        body_ids_bounded(
            echod_concrete::node::spec_occurrence(
                body,
                pending,
                now,
            ),
        ),
{
    reveal(echod_concrete::node::spec_occurrence);
    reveal(echod_concrete::node::spec_opened);
    reveal(echod_concrete::node::spec_workflow_map);
    reveal(echod_concrete::node::spec_with_workflow);
    reveal(body_ids_bounded);
    reveal(workflow_ids_bounded);
    let opened = echod_concrete::node::spec_opened(body);
    let map = echod_concrete::node::spec_workflow_map(opened);
    if !map.contains_key(pending.promise) && now >= pending.at {
        lemma_insert_bounded_preserves_ids_bounded(
            map,
            pending.promise,
            echod_concrete::node::spec_new_obj(
                echod_concrete::store::spec_sat_add(
                    pending.at,
                    pending.timeout,
                ),
                now,
                pending.param,
                pending.tags,
                echod_concrete::node::spec_targeted(pending.tags)
                    && !echod_concrete::node::spec_timer(pending.tags),
            ),
        );
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_occurrence_transition_preserves_body_ids_bounded(
    body: DocumentBodyV,
    pending: PendingV,
    now: u64,
    retry_timeout: u64,
)
    requires
        body_ids_bounded(body),
        pending.promise.len() <= usize::MAX as int,
    ensures
        body_ids_bounded(
            echod_concrete::node::spec_occurrence_transition(
                body,
                pending,
                now,
                retry_timeout,
            ).0,
        ),
{
    reveal(echod_concrete::node::spec_occurrence_transition);
    lemma_sweep_preserves_body_ids_bounded(
        body,
        now,
        retry_timeout,
    );
    let swept = echod_concrete::node::spec_sweep(
        body,
        now,
        retry_timeout,
    ).0;
    lemma_occurrence_preserves_body_ids_bounded(
        swept,
        pending,
        now,
    );
    lemma_sweep_preserves_body_ids_bounded(
        echod_concrete::node::spec_occurrence(
            swept,
            pending,
            now,
        ),
        now,
        retry_timeout,
    );
}

#[verifier::spinoff_prover]
pub proof fn lemma_due_transition_preserves_bounded_ids(
    body: DocumentBodyV,
    now: u64,
    retry_timeout: u64,
)
    requires
        body_ids_bounded(body),
    ensures
        body_ids_bounded(
            echod_concrete::node::spec_due_transition(
                body,
                now,
                retry_timeout,
            ).0,
        ),
        forall|i: int|
            0 <= i
                && i
                    < echod_concrete::node::spec_due_transition(
                        body,
                        now,
                        retry_timeout,
                    ).2.len() ==>
                echod_concrete::node::spec_due_transition(
                    body,
                    now,
                    retry_timeout,
                ).2[i].promise.len() <= usize::MAX as int,
{
    reveal(echod_concrete::node::spec_due_transition);
    match body {
        DocumentBodyV::Schedule(_) => {
            lemma_fire_schedule_preserves_bounded_ids(body, now);
        },
        DocumentBodyV::Workflow(_) => {
            lemma_sweep_preserves_body_ids_bounded(
                body,
                now,
                retry_timeout,
            );
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_request_transition_preserves_body_ids_bounded(
    body: DocumentBodyV,
    request: echod_types::Request,
    now: u64,
    retry_timeout: u64,
)
    requires
        body_ids_bounded(body),
    ensures
        body_ids_bounded(
            echod_concrete::node::spec_request_transition(
                body,
                request,
                now,
                retry_timeout,
            ).0,
        ),
{
    reveal(echod_concrete::node::spec_request_transition);
    match body {
        DocumentBodyV::Schedule(_) => {
            lemma_handle_preserves_body_ids_bounded(
                body,
                request,
                now,
            );
        },
        DocumentBodyV::Workflow(_) => {
            lemma_sweep_preserves_body_ids_bounded(
                body,
                now,
                retry_timeout,
            );
            let swept = echod_concrete::node::spec_sweep(
                body,
                now,
                retry_timeout,
            ).0;
            lemma_handle_preserves_body_ids_bounded(
                swept,
                request,
                now,
            );
            let handled = echod_concrete::node::spec_handle(
                swept,
                request,
                now,
            ).0;
            lemma_sweep_preserves_body_ids_bounded(
                handled,
                now,
                retry_timeout,
            );
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_process_step_preserves_body_ids_bounded(
    job: crate::verified::flight_spec::AJob,
    body: DocumentBodyV,
    now: u64,
    retry_timeout: u64,
)
    requires
        body_ids_bounded(body),
        job is Occurrence ==>
            job->Occurrence_0.promise.len() <= usize::MAX as int,
    ensures
        body_ids_bounded(
            crate::verified::flight_spec::spec_step(
                job,
                body,
                now,
                retry_timeout,
            ).0,
        ),
{
    reveal(crate::verified::flight_spec::spec_step);
    match job {
        crate::verified::flight_spec::AJob::Request(request) => {
            lemma_request_transition_preserves_body_ids_bounded(
                body,
                request,
                now,
                retry_timeout,
            );
        },
        crate::verified::flight_spec::AJob::Sweep => {
            lemma_sweep_preserves_body_ids_bounded(
                body,
                now,
                retry_timeout,
            );
        },
        crate::verified::flight_spec::AJob::Fire => {
            lemma_fire_schedule_preserves_bounded_ids(body, now);
        },
        crate::verified::flight_spec::AJob::Occurrence(pending) => {
            lemma_occurrence_preserves_body_ids_bounded(
                body,
                pending,
                now,
            );
        },
    }
}

} // verus!
