//! Mathematical persisted documents, partials, and endpoint effects.

use vstd::prelude::*;
use echod_types::{PromiseState, Schedule, Tags, TaskState, Value, MAX_TIME, MAX_VERSION};
#[cfg(verus_keep_ghost)]
use echod_types::origin;

verus! {


// The mathematical partial algebra.  The executable codec is deliberately
// separate: serde is a trusted byte boundary, while these equations are what
// handlers and compaction are proved against.

#[cfg(verus_keep_ghost)]
pub enum ChangeV<V> {
    Upsert { id: Seq<char>, value: V },
    Remove { id: Seq<char> },
}


#[cfg(verus_keep_ghost)]
pub struct PartialV<V> {
    pub document: Seq<char>,
    pub basever: nat,
    pub version: nat,
    pub committed_at: nat,
    pub next_wake_at: Option<nat>,
    pub changes: Seq<ChangeV<V>>,
}


#[cfg(verus_keep_ghost)]
pub struct FoldedV<V> {
    pub document: Seq<char>,
    pub version: nat,
    pub committed_at: nat,
    pub next_wake_at: Option<nat>,
    pub entries: Map<Seq<char>, V>,
}


#[cfg(verus_keep_ghost)]
pub open spec fn spec_apply_change<V>(entries: Map<Seq<char>, V>, change: ChangeV<V>) -> Map<Seq<char>, V> {
    match change {
        ChangeV::Upsert { id, value } => entries.insert(id, value),
        ChangeV::Remove { id } => entries.remove(id),
    }
}


#[cfg(verus_keep_ghost)]
pub open spec fn spec_apply_changes<V>(entries: Map<Seq<char>, V>, changes: Seq<ChangeV<V>>) -> Map<Seq<char>, V>
    decreases changes.len(),
{
    if changes.len() == 0 {
        entries
    } else {
        spec_apply_change(spec_apply_changes(entries, changes.drop_last()), changes.last())
    }
}


#[cfg(verus_keep_ghost)]
pub open spec fn spec_apply<V>(document: FoldedV<V>, partial: PartialV<V>) -> FoldedV<V> {
    FoldedV {
        document: document.document,
        version: partial.version,
        committed_at: partial.committed_at,
        next_wake_at: partial.next_wake_at,
        entries: spec_apply_changes(document.entries, partial.changes),
    }
}


#[cfg(verus_keep_ghost)]
pub open spec fn spec_compose<V>(first: PartialV<V>, second: PartialV<V>) -> PartialV<V> {
    PartialV {
        document: first.document,
        basever: first.basever,
        version: second.version,
        committed_at: second.committed_at,
        next_wake_at: second.next_wake_at,
        changes: first.changes + second.changes,
    }
}


pub struct PromV {
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
    pub callbacks: Seq<Seq<char>>,
    pub listeners: Seq<Seq<char>>,
}


pub struct TkV {
    pub state: TaskState,
    pub version: u64,
    pub pid: Option<Seq<char>>,
    pub ttl: Option<u64>,
    pub lease_timeout_at: Option<u64>,
    pub retry_timeout_at: Option<u64>,
    pub resumes: Seq<Seq<char>>,
}


pub struct ObjV {
    pub promise: PromV,
    pub task: Option<TkV>,
}


/// Storage-independent payload carried by an Unblock effect.
pub struct PromiseEffectV {
    pub id: Seq<char>,
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
}


/// The unordered effects implied by a committed document transition.
pub enum ProtocolEffectV {
    Execute { id: Seq<char>, version: u64 },
    Unblock {
        promise: Seq<char>,
        address: Seq<char>,
        record: PromiseEffectV,
    },
}


/// The idempotency key used when effects are released after CAS.
pub enum ProtocolEffectKeyV {
    Execute { id: Seq<char> },
    Unblock { promise: Seq<char>, address: Seq<char> },
}


/// Logical changes to the durable wake frontier. Physical timer tokens and
/// arm/delete ordering remain process concerns.
pub enum TimerEffectV {
    Add { at: u64 },
    Delete { at: u64 },
}


pub open spec fn protocol_effect_key(effect: ProtocolEffectV) -> ProtocolEffectKeyV {
    match effect {
        ProtocolEffectV::Execute { id, .. } => ProtocolEffectKeyV::Execute { id },
        ProtocolEffectV::Unblock { promise, address, .. } =>
            ProtocolEffectKeyV::Unblock { promise, address },
    }
}


pub open spec fn promise_effect(id: Seq<char>, promise: PromV) -> PromiseEffectV {
    PromiseEffectV {
        id,
        state: promise.state,
        param: promise.param,
        value: promise.value,
        tags: promise.tags,
        timeout_at: promise.timeout_at,
        created_at: promise.created_at,
        settled_at: promise.settled_at,
    }
}


/// The final document still contains an offer produced at this commit.
///
/// This deliberately describes the initial/final pair, not an intermediate
/// sweep step. If the handler acquires, settles, or halts a task after the
/// pre-sweep rearmed it, the final task is not pending and no Execute belongs
/// to the committed effect set.
pub open spec fn offer_committed(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    committed_at: u64,
) -> bool {
    after.contains_key(id)
        && match after[id].task {
            Some(new) => {
                &&& after[id].promise.state == PromiseState::Pending
                &&& new.state == TaskState::Pending
                &&& new.retry_timeout_at is Some
                &&& new.retry_timeout_at.unwrap() > committed_at
                &&& (!before.contains_key(id) || before[id] != after[id])
                &&& if before.contains_key(id) {
                    match before[id].task {
                        Some(old) if old.state == TaskState::Pending =>
                            match old.retry_timeout_at {
                                Some(at) => at <= committed_at,
                                None => true,
                            },
                        _ => true,
                    }
                } else {
                    true
                }
            },
            None => false,
        }
}


/// A listener present before the transaction was discharged by its final,
/// settled promise.
pub open spec fn listener_committed(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    promise: Seq<char>,
    address: Seq<char>,
) -> bool {
    before.contains_key(promise)
        && before[promise].promise.listeners.contains(address)
        && after.contains_key(promise)
        && after[promise].promise.state != PromiseState::Pending
        && !after[promise].promise.listeners.contains(address)
}


pub open spec fn workflow_effects(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    committed_at: u64,
) -> ISet<ProtocolEffectV> {
    ISet::new(|effect: ProtocolEffectV| match effect {
        ProtocolEffectV::Execute { id, version } =>
            offer_committed(before, after, id, committed_at)
                && after[id].task.unwrap().version == version,
        ProtocolEffectV::Unblock { promise, address, record } =>
            listener_committed(before, after, promise, address)
                && record == promise_effect(promise, after[promise].promise),
    })
}


/// Effects are derived from the two complete logical documents alone. The
/// new document's `committed_at` is the comparison clock.
pub open spec fn document_effects(
    before: StoredDocumentV,
    after: StoredDocumentV,
) -> ISet<ProtocolEffectV> {
    match (before, after) {
        (StoredDocumentV::Workflow(old), StoredDocumentV::Workflow(new)) =>
            workflow_effects(old.objects, new.objects, new.committed_at),
        _ => ISet::empty(),
    }
}


pub open spec fn stored_next_wake_at(document: StoredDocumentV) -> Option<u64> {
    match document {
        StoredDocumentV::Workflow(workflow) => workflow.next_wake_at,
        StoredDocumentV::Schedule(schedule) => schedule.next_wake_at,
    }
}


/// Timer additions/deletions are completely determined by the old and new
/// folded documents' wake frontiers.
pub open spec fn document_timer_effects(
    before: StoredDocumentV,
    after: StoredDocumentV,
) -> ISet<TimerEffectV> {
    let old = stored_next_wake_at(before);
    let new = stored_next_wake_at(after);
    ISet::new(|effect: TimerEffectV| match effect {
        TimerEffectV::Add { at } => new == Some(at) && new != old,
        TimerEffectV::Delete { at } => old == Some(at) && old != new,
    })
}


pub enum DocumentBodyV {
    Workflow(Map<Seq<char>, ObjV>),
    Schedule(Option<Schedule>),
}


pub struct WorkflowDocumentV {
    pub document: Seq<char>,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
    pub objects: Map<Seq<char>, ObjV>,
}


pub struct ScheduleDocumentV {
    pub document: Seq<char>,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
    pub schedule: Option<Schedule>,
}


pub enum StoredDocumentV {
    Workflow(WorkflowDocumentV),
    Schedule(ScheduleDocumentV),
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
        crate::node::spec_awaitable(promise.tags)
    &&& promise.state != PromiseState::Pending ==>
        promise.callbacks.len() == 0 && promise.listeners.len() == 0
}


pub open spec fn task_well_formed(
    object: ObjV,
    committed_at: u64,
) -> bool {
    (object.task is Some) == crate::node::spec_targeted(object.promise.tags)
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
            && crate::node::spec_targeted(objects[awaiter].promise.tags)
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
            &&& row.created_at <= row.next_run_at
            &&& match row.last_run_at {
                Some(last) => row.created_at <= last < row.next_run_at,
                None => true,
            }
            &&& !(crate::node::spec_targeted(row.promise_tags)
                && crate::node::spec_timer(row.promise_tags))
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
    &&& workflow.next_wake_at == match crate::node::spec_body_deadline(
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
            &&& row.created_at <= row.next_run_at
            &&& match row.last_run_at {
                Some(last) => row.created_at <= last < row.next_run_at,
                None => true,
            }
            &&& !(crate::node::spec_targeted(row.promise_tags)
                && crate::node::spec_timer(row.promise_tags))
        },
        None => true,
    }
    &&& schedule.next_wake_at == match crate::node::spec_body_deadline(
        DocumentBodyV::Schedule(schedule.schedule),
    ) {
        Some(at) => Some(at as u64),
        None => None,
    }
}


/// The full local invariant of a stored workflow or schedule document.
pub open spec fn well_formed(document: StoredDocumentV) -> bool {
    match document {
        StoredDocumentV::Workflow(workflow) => workflow_well_formed(workflow),
        StoredDocumentV::Schedule(schedule) => schedule_well_formed(schedule),
    }
}


pub struct LoadedDocumentV {
    pub document: StoredDocumentV,
    pub change_count: usize,
    pub bytes: u64,
}

} // verus!
