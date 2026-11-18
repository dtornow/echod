//! property_claim definitions for the concrete model.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::contrib::make_spec_type;
use echod_types::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::*;
use rover_spec::rover::comm::{Sched, ProcessEvent};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
use crate::state::{TkV, ObjV, PromiseEffectV, ProtocolEffectV, ProtocolEffectKeyV, DocumentBodyV, WorkflowDocumentV, ScheduleDocumentV, StoredDocumentV, Message, Proc, NoteV, NodeV, StoreV};
#[cfg(verus_keep_ghost)]
use crate::handler::{on_event, protocol_effect_key, document_effects, spec_stored_body, spec_stored_name, spec_advance_stored, spec_owns, spec_unavailable, spec_timer, spec_targeted, spec_awaitable, spec_request_transition, spec_sorted_present, spec_body_deadline, spec_find, spec_before};
use crate::rover::{Pid, Config, spec_world};
use rover_spec::rover::comm::Time;

use crate::handler::{on_request,request_document,record_effect,note_effect,note_effects,note_effect_keys};

verus! {
pub open spec fn production_document_canonical(data: crate::state::ProductionDocumentData) -> bool {
    match data {
        crate::state::ProductionDocumentData::Schedule(_) => true,
        crate::state::ProductionDocumentData::Workflow(entries) => {
            let map = crate::handler::production_document_data_rows(entries.deep_view());
            &&& entries@.map_values(|e: (String, crate::state::ProductionObjectData)| e.0@)
                == crate::handler::spec_sorted_present(map)
            &&& forall|i: int| 0 <= i < entries.len() ==> {
                map.contains_key(entries[i].0@) && map[entries[i].0@] == entries[i].1.deep_view()
            }
        },
    }
}

pub open spec fn production_debug_canonical(data: crate::state::ProductionDebugData) -> bool {
    match data {
        crate::state::ProductionDebugData::Snap { origins, .. } =>
            forall|i: int| 0 <= i < origins.len() ==> production_document_canonical(#[trigger] origins[i]),
        _ => true,
    }
}

pub open spec fn production_effect_canonical(data: crate::state::ProductionEffectData) -> bool {
    match data {
        crate::state::ProductionEffectData::Reply { response: Ok(crate::state::ProductionAnswerData::Debug { body, .. }), .. } =>
            production_debug_canonical(body),
        _ => true,
    }
}

pub open spec fn unique<T>(values: Seq<T>) -> bool {
    forall|i: int, j: int|
        0 <= i < values.len() && 0 <= j < values.len()
            && values[i] == values[j] ==> i == j
}

pub open spec fn value_empty(value: Value) -> bool {
    value@.data is None && value@.headers.len() == 0
}

pub open spec fn task_cleared(task: TkV) -> bool {
    task.pid is None
        && task.ttl is None
        && task.lease_timeout_at is None
        && task.retry_timeout_at is None
}

pub open spec fn strict_descendant(parent: Seq<char>, child: Seq<char>) -> bool {
    child.len() > parent.len() + 1
        && child.take(parent.len() as int + 1) == parent + seq!['.']
}

pub open spec fn promise_well_formed(
    id: Seq<char>,
    object: ObjV,
    committed_at: u64,
) -> bool {
    let promise = object.promise;
    &&& promise.timeout_at <= MAX_TIME
    &&& promise.created_at <= promise.timeout_at
    &&& promise.created_at <= committed_at
    &&& (promise.state == PromiseState::Pending) == (promise.settled_at is None)
    &&& match promise.settled_at {
        Some(at) => promise.created_at <= at <= promise.timeout_at && at <= committed_at,
        None => true,
    }
    &&& promise.state == PromiseState::Pending ==> {
        &&& promise.timeout_at > committed_at
        &&& value_empty(promise.value)
    }
    &&& promise.state == PromiseState::RejectedTimedout ==>
        promise.settled_at == Some(promise.timeout_at)
    &&& promise.settled_at == Some(promise.timeout_at) ==>
        value_empty(promise.value)
    &&& unique(promise.callbacks)
    &&& unique(promise.listeners)
    &&& !promise.callbacks.contains(id)
    &&& forall|i: int| 0 <= i < promise.callbacks.len() ==>
        origin(promise.callbacks[i]) == origin(id)
    &&& (promise.callbacks.len() > 0 || promise.listeners.len() > 0) ==>
        crate::handler::spec_awaitable(promise.tags)
    &&& promise.state != PromiseState::Pending ==>
        promise.callbacks.len() == 0 && promise.listeners.len() == 0
}

pub open spec fn task_well_formed(
    object: ObjV,
    committed_at: u64,
) -> bool {
    (object.task is Some) == crate::handler::spec_targeted(object.promise.tags)
        && match object.task {
            None => true,
            Some(task) => {
                &&& (task.state == TaskState::Acquired) == (task.pid is Some)
                &&& (task.state == TaskState::Acquired) == (task.ttl is Some)
                &&& (task.state == TaskState::Acquired) == (task.lease_timeout_at is Some)
                &&& (task.state == TaskState::Pending) == (task.retry_timeout_at is Some)
                &&& match task.ttl { Some(ttl) => 0 < ttl <= MAX_TIME, None => true }
                &&& task.state == TaskState::Acquired ==> {
                    &&& task.version > 0
                    &&& task.lease_timeout_at.unwrap() > committed_at
                }
                &&& task.state == TaskState::Pending ==>
                    task.retry_timeout_at.unwrap() > committed_at
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

pub open spec fn callback_targets_well_formed(
    objects: Map<Seq<char>, ObjV>,
    object: ObjV,
) -> bool {
    forall|i: int| 0 <= i < object.promise.callbacks.len() ==> {
        let awaiter = #[trigger] object.promise.callbacks[i];
        objects.contains_key(awaiter)
            && objects[awaiter].task is Some
            && crate::handler::spec_targeted(objects[awaiter].promise.tags)
    }
}

pub open spec fn suspended_rung_well_formed(
    objects: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    object: ObjV,
) -> bool {
    match object.task {
        Some(task) if task.state == TaskState::Suspended
            && object.promise.state == PromiseState::Pending =>
                exists|awaited: Seq<char>|
                    objects.contains_key(awaited)
                        && objects[awaited].promise.callbacks.contains(id),
        _ => true,
    }
}

pub open spec fn descendants_well_formed(
    objects: Map<Seq<char>, ObjV>,
) -> bool {
    forall|parent: Seq<char>, child: Seq<char>|
        objects.contains_key(parent)
            && objects.contains_key(child)
            && objects[parent].promise.state != PromiseState::Pending
            && strict_descendant(parent, child)
                ==> objects[child].promise.state != PromiseState::Pending
}

pub open spec fn workflow_body_well_formed(
    document: Seq<char>,
    objects: Map<Seq<char>, ObjV>,
    committed_at: u64,
) -> bool {
    forall|id: Seq<char>| objects.contains_key(id) ==> {
        &&& origin(id) == document
        &&& promise_well_formed(id, objects[id], committed_at)
        &&& task_well_formed(objects[id], committed_at)
        &&& callback_targets_well_formed(objects, objects[id])
        &&& suspended_rung_well_formed(objects, id, objects[id])
    }
}

pub open spec fn schedule_body_well_formed(
    document: Seq<char>,
    schedule: Option<Schedule>,
    committed_at: u64,
) -> bool {
    match schedule {
        Some(row) => {
            &&& row.id@ == document
            &&& row.promise_timeout <= MAX_TIME
            &&& row.created_at <= committed_at
            &&& match row.next_run_at {
                Some(next) => row.created_at <= next,
                None => true,
            }
            &&& match row.last_run_at {
                Some(last) => row.created_at <= last && match row.next_run_at {
                    Some(next) => last < next,
                    None => true,
                },
                None => true,
            }
            &&& !(crate::handler::spec_targeted(row.promise_tags)
                && crate::handler::spec_timer(row.promise_tags))
        },
        None => true,
    }
}

pub open spec fn body_well_formed(
    document: Seq<char>,
    body: DocumentBodyV,
    committed_at: u64,
) -> bool {
    match body {
        DocumentBodyV::Workflow(objects) =>
            workflow_body_well_formed(document, objects, committed_at),
        DocumentBodyV::Schedule(schedule) =>
            schedule_body_well_formed(document, schedule, committed_at),
    }
}

pub open spec fn workflow_well_formed(workflow: WorkflowDocumentV) -> bool {
    &&& workflow.committed_at <= MAX_TIME
    &&& forall|id: Seq<char>| #[trigger] workflow.objects.contains_key(id) ==> {
        &&& origin(id) == workflow.document
        &&& promise_well_formed(id, workflow.objects[id], workflow.committed_at)
        &&& task_well_formed(workflow.objects[id], workflow.committed_at)
        &&& callback_targets_well_formed(workflow.objects, workflow.objects[id])
        &&& suspended_rung_well_formed(workflow.objects, id, workflow.objects[id])
    }
    // Deferred until descendant settlement semantics are decided:
    // &&& descendants_well_formed(workflow.objects)
    &&& workflow.next_wake_at == match crate::handler::spec_body_deadline(
        DocumentBodyV::Workflow(workflow.objects),
    ) {
        Some(at) => Some(at as u64),
        None => None,
    }
}

pub open spec fn schedule_well_formed(schedule: ScheduleDocumentV) -> bool {
    &&& schedule.committed_at <= MAX_TIME
    &&& match schedule.schedule {
        Some(row) => {
            &&& row.id@ == schedule.document
            &&& row.promise_timeout <= MAX_TIME
            &&& row.created_at <= schedule.committed_at
            &&& match row.next_run_at {
                Some(next) => row.created_at <= next,
                None => true,
            }
            &&& match row.last_run_at {
                Some(last) => row.created_at <= last && match row.next_run_at {
                    Some(next) => last < next,
                    None => true,
                },
                None => true,
            }
            &&& !(crate::handler::spec_targeted(row.promise_tags)
                && crate::handler::spec_timer(row.promise_tags))
        },
        None => true,
    }
    &&& schedule.next_wake_at == match crate::handler::spec_body_deadline(
        DocumentBodyV::Schedule(schedule.schedule),
    ) {
        Some(at) => Some(at as u64),
        None => None,
    }
}

pub open spec fn well_formed(document: StoredDocumentV) -> bool {
    match document {
        StoredDocumentV::Workflow(workflow) => workflow_well_formed(workflow),
        StoredDocumentV::Schedule(schedule) => schedule_well_formed(schedule),
    }
}









pub open spec fn effects_match(
    before: StoredDocumentV,
    after: StoredDocumentV,
    notes: Seq<NoteV>,
) -> bool {
    &&& note_effects(notes) == document_effects(before, after)
    &&& note_effect_keys(notes).no_duplicates()
}

pub open spec fn collected_offers_valid(
    map: Map<Seq<char>, crate::state::ObjV>,
    notes: Seq<crate::state::NoteV>,
) -> bool {
    &&& note_effect_keys(notes).no_duplicates()
    &&& forall|i: int| 0 <= i < notes.len() ==> match #[trigger] notes[i] {
        crate::state::NoteV::Execute { id, version } =>
            map.contains_key(id) && map[id].task is Some
            && map[id].task.unwrap().state == TaskState::Pending
            && map[id].task.unwrap().version == version,
        _ => false,
    }
}

pub open spec fn request_effects_match(
    before: DocumentBodyV,
    now: Time,
    retry_timeout: u64,
    notes: Seq<NoteV>,
) -> bool {
    &&& notes == match before {
        DocumentBodyV::Workflow(objects) => crate::handler::spec_bulk_workflow(objects, now, retry_timeout).1,
        DocumentBodyV::Schedule(_) => Seq::empty(),
    }
    &&& note_effect_keys(notes).no_duplicates()
}

pub open spec fn safe_effect_config(now: u64, retry_timeout: u64) -> bool {
    retry_timeout > 0
        && (now as nat) + (retry_timeout as nat) <= u64::MAX as nat
}

pub open spec fn keys_strictly_sorted(keys: Seq<Seq<char>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < keys.len()
        ==> spec_before(#[trigger] keys[i], #[trigger] keys[j])
}

pub open spec fn document_object_order(doc: DocumentBodyV) -> bool {
    match doc {
        DocumentBodyV::Workflow(map) => {
            let keys = spec_sorted_present(map);
            &&& keys_strictly_sorted(keys)
            &&& keys.no_duplicates()
            &&& forall|key: Seq<char>| #[trigger] keys.contains(key)
                <==> map.contains_key(key)
        },
        DocumentBodyV::Schedule(_) => true,
    }
}

pub open spec fn document_keys_unique(node: NodeV) -> bool {
    forall|i: int, j: int| 0 <= i < j < node.documents.len()
        ==> #[trigger] node.documents[i].key != #[trigger] node.documents[j].key
}

pub open spec fn document_key_ownership(node: NodeV) -> bool {
    forall|i: int| 0 <= i < node.documents.len()
        ==> spec_owns(node, #[trigger] node.documents[i].key)
}

pub open spec fn flight_key_ownership(node: NodeV) -> bool {
    match node.flight {
        Some(flight) => spec_owns(node, flight.key),
        None => true,
    }
}

pub open spec fn node_operation_order(node: NodeV) -> bool {
    &&& node.next_op > 0
    &&& match node.flight {
        Some(flight) => flight.op < node.next_op,
        None => true,
    }
}

pub open spec fn store_entries_ordered(store: StoreV) -> bool {
    forall|i: int, j: int| 0 <= i < j < store.entries.len()
        ==> spec_before(
            #[trigger] store.entries[i].key,
            #[trigger] store.entries[j].key,
        )
}

pub open spec fn store_entries_unique(store: StoreV) -> bool {
    forall|i: int, j: int| 0 <= i < j < store.entries.len()
        ==> #[trigger] store.entries[i].key != #[trigger] store.entries[j].key
}

pub open spec fn store_versions_positive(store: StoreV) -> bool {
    forall|i: int| 0 <= i < store.entries.len()
        ==> #[trigger] store.entries[i].version > 0
}

pub open spec fn store_seen_unique(store: StoreV) -> bool {
    store.seen.no_duplicates()
}

pub open spec fn process_layout(config: Config) -> bool {
    let world = spec_world(config);
    &&& world.len() == config.nodes as nat + 1
    &&& forall|i: int| 0 <= i < config.nodes as int
        ==> #[trigger] world[i].0 == Pid::Node(i as u64)
    &&& world[config.nodes as int].0 == Pid::Store
    &&& forall|i: int, j: int| 0 <= i < j < world.len()
        ==> #[trigger] world[i].0 != #[trigger] world[j].0
}

pub open spec fn state_properties(state: Proc) -> bool {
    match state {
        Proc::Node(node) => {
            &&& document_keys_unique(node)
            &&& document_key_ownership(node)
            &&& flight_key_ownership(node)
            &&& node_operation_order(node)
        },
        Proc::Store(store) => {
            &&& store_entries_ordered(store)
            &&& store_entries_unique(store)
            &&& store_versions_positive(store)
            &&& store_seen_unique(store)
        },
    }
}

pub open spec fn transition_properties(before: Proc, after: Proc) -> bool {
    match (before, after) {
        (Proc::Node(old), Proc::Node(new)) => old.next_op <= new.next_op,
        (Proc::Store(old), Proc::Store(new)) => {
            &&& forall|i: int| 0 <= i < old.entries.len() ==> {
                let old_entry = #[trigger] old.entries[i];
                let key = old_entry.key;
                match spec_find(new.entries, key, 0) {
                    Some(j) => old_entry.version <= new.entries[j].version,
                    None => true,
                }
            }
            &&& forall|seen: (Pid, u64)| old.seen.contains(seen)
                ==> new.seen.contains(seen)
        },
        _ => false,
    }
}

pub open spec fn step_properties(
    before: Proc,
    outcome: StepResultV<Proc, Pid, Message>,
) -> bool {
    &&& state_properties(outcome.state)
    &&& transition_properties(before, outcome.state)
}

pub open spec fn property_claim(config: Config) -> bool {
    &&& process_layout(config)
    &&& forall|doc: DocumentBodyV| document_object_order(doc)
    &&& forall|i: int| 0 <= i < spec_world(config).len()
        ==> state_properties(#[trigger] spec_world(config)[i].1)
    &&& forall|before: Proc, now: Time, event: ProcessEvent<Pid, Message>, i: int|
            #![trigger before.on_event(config, now, event)[i]]
            state_properties(before)
            && 0 <= i
            && i < before.on_event(config, now, event).len()
            ==> step_properties(
                before,
                before.on_event(config, now, event)[i],
            )
}

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
}
