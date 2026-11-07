//! The values stored in workflow and schedule documents.
//!
//! A workflow document is a sorted table of [`Obj`] values, keyed by promise
//! id.  A schedule document is one [`Schedule`] or none.  The concrete
//! machine operates directly on these values; the process document codec
//! turns their partial byte representation into these values and back.
//!
//! This module owns the persisted vocabulary.  Operations on that vocabulary
//! remain grouped by purpose: object edits and handlers live in `node`, while
//! byte framing and storage calls live in the process.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_types::origin;
use echod_types::{PromiseState, Schedule, Tags, TaskState, Value};

#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};

verus! {

// ---------------------------------------------------------------------------
// Stored partials and their fold
// ---------------------------------------------------------------------------

/// One edit carried by a stored partial.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
#[cfg_attr(not(verus_keep_ghost), serde(tag = "op", rename_all = "snake_case"))]
pub enum Change<R> {
    Upsert { id: String, value: R },
    Remove { id: String },
}

/// The only unit stored for a document.  An ordinary commit spans one
/// version; compaction may combine adjacent partials and span several.
///
/// `next_wake_at` is redundant by design: document well-formedness ties it to
/// the least deadline of the value obtained after applying `changes`.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub struct Partial<R> {
    pub document: String,
    pub basever: u64,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
    pub changes: Vec<Change<R>>,
}

/// The logical document obtained by folding its stored partials.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
struct Folded<R> {
    pub document: String,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
    pub entries: Vec<(String, R)>,
}

#[cfg(not(verus_keep_ghost))]
impl<R> Folded<R> {
    pub fn empty(document: String) -> Self {
        Self {
            document,
            version: 0,
            committed_at: 0,
            next_wake_at: None,
            entries: Vec::new(),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl<R: Clone> Folded<R> {
    /// Apply one partial.  The checks are representation checks, not store
    /// concurrency control: S3's conditional write still decides which
    /// writer commits.
    pub fn apply(&self, partial: &Partial<R>) -> Result<Self, String> {
        if partial.document != self.document {
            return Err("partial names another document".to_string());
        }
        if partial.basever != self.version {
            return Err("partial base version does not match".to_string());
        }
        if partial.version <= partial.basever {
            return Err("partial version does not advance".to_string());
        }
        if partial.committed_at < self.committed_at {
            return Err("partial committed_at moves backwards".to_string());
        }

        let mut entries = self.entries.clone();
        for change in &partial.changes {
            match change {
                Change::Upsert { id, value } => {
                    match entries.iter().position(|(key, _)| key == id) {
                        Some(i) => entries[i] = (id.clone(), value.clone()),
                        None => entries.push((id.clone(), value.clone())),
                    }
                }
                Change::Remove { id } => entries.retain(|(key, _)| key != id),
            }
        }

        Ok(Self {
            document: self.document.clone(),
            version: partial.version,
            committed_at: partial.committed_at,
            next_wake_at: partial.next_wake_at,
            entries,
        })
    }
}

#[cfg(not(verus_keep_ghost))]
impl<R: Clone> Partial<R> {
    /// Combine two adjacent stored boundaries.  Their edits stay in order;
    /// a later canonical compactor may remove shadowed edits without changing
    /// the algebra.
    pub fn compose(&self, next: &Self) -> Result<Self, String> {
        if self.document != next.document {
            return Err("partials name different documents".to_string());
        }
        if self.version != next.basever {
            return Err("partials are not adjacent".to_string());
        }
        if next.committed_at < self.committed_at {
            return Err("partial committed_at moves backwards".to_string());
        }

        let mut changes = self.changes.clone();
        changes.extend(next.changes.clone());
        Ok(Self {
            document: self.document.clone(),
            basever: self.basever,
            version: next.version,
            committed_at: next.committed_at,
            next_wake_at: next.next_wake_at,
            changes,
        })
    }
}

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

/// Applying concatenated edits is the same as applying each sequence.
#[cfg(verus_keep_ghost)]
pub proof fn lemma_apply_changes_append<V>(
    entries: Map<Seq<char>, V>,
    first: Seq<ChangeV<V>>,
    second: Seq<ChangeV<V>>,
)
    ensures
        spec_apply_changes(entries, first + second)
            == spec_apply_changes(spec_apply_changes(entries, first), second),
    decreases second.len(),
{
    if second.len() == 0 {
        assert(first + second =~= first);
    } else {
        let prefix = second.drop_last();
        lemma_apply_changes_append(entries, first, prefix);
        assert((first + second).drop_last() =~= first + prefix);
        assert((first + second).last() == second.last());
    }
}

/// Compacting adjacent partials preserves their logical effect.
#[cfg(verus_keep_ghost)]
pub proof fn lemma_compose_preserves_apply<V>(
    document: FoldedV<V>,
    first: PartialV<V>,
    second: PartialV<V>,
)
    requires
        first.document == document.document,
        first.basever == document.version,
        second.document == document.document,
        second.basever == first.version,
        document.committed_at <= first.committed_at <= second.committed_at,
    ensures
        spec_apply(spec_apply(document, first), second)
            == spec_apply(document, spec_compose(first, second)),
{
    lemma_apply_changes_append(document.entries, first.changes, second.changes);
}

/// Either kind of logical document.  A physical object always has exactly
/// one shape: workflow objects contain promises; schedule objects contain at
/// most their one schedule.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub enum DocumentBody {
    Workflow(Objects),
    Schedule(Option<Schedule>),
}

/// The complete logical value of a workflow document.
#[derive(Debug, PartialEq, Eq)]
pub struct WorkflowDocument {
    pub document: String,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
    pub objects: Objects,
}

/// The complete logical value of a schedule document.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ScheduleDocument {
    pub document: String,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
    pub schedule: Option<Schedule>,
}

/// A loaded document. The variants are deliberately the two physical
/// document families; there is no unversioned document representation.
#[derive(Debug, PartialEq, Eq)]
pub enum StoredDocument {
    Workflow(WorkflowDocument),
    Schedule(ScheduleDocument),
}

/// A decoded document and the byte accounting needed to append or compact it.
#[derive(Debug, PartialEq, Eq)]
pub struct LoadedDocument {
    pub document: StoredDocument,
    pub change_count: usize,
    pub bytes: u64,
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
                &&& task.version <= u32::MAX as u64
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

pub open spec fn workflow_well_formed(workflow: WorkflowDocumentV) -> bool {
    &&& forall|id: Seq<char>| workflow.objects.contains_key(id) ==> {
        &&& origin(id) == workflow.document
        &&& promise_well_formed(id, workflow.objects[id], workflow.committed_at)
        &&& task_well_formed(workflow.objects[id], workflow.committed_at)
        &&& callback_targets_well_formed(workflow.objects, workflow.objects[id])
        &&& suspended_rung_well_formed(workflow.objects, id, workflow.objects[id])
    }
    &&& descendants_well_formed(workflow.objects)
    &&& workflow.next_wake_at == match crate::node::spec_body_deadline(
        DocumentBodyV::Workflow(workflow.objects),
    ) {
        Some(at) => Some(at as u64),
        None => None,
    }
}

pub open spec fn schedule_well_formed(schedule: ScheduleDocumentV) -> bool {
    &&& match schedule.schedule {
        Some(row) => {
            &&& row.id@ == schedule.document
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

/// A workflow document: the promises of one workflow, by id, in key order.
///
/// The ordering is a type invariant established in `node`; it gives the
/// executable table one canonical representation while its view is a map.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub struct Objects {
    pub(crate) entries: Vec<(String, Obj)>,
}

/// The value stored under one promise id.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub struct Obj {
    pub promise: Prom,
    pub task: Option<Tk>,
}

/// The durable promise fields.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub struct Prom {
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
    pub callbacks: Vec<String>,
    pub listeners: Vec<String>,
}

/// The durable task nested in a runnable promise.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub struct Tk {
    pub state: TaskState,
    pub version: u64,
    pub pid: Option<String>,
    pub ttl: Option<u64>,
    pub lease_timeout_at: Option<u64>,
    pub retry_timeout_at: Option<u64>,
    pub resumes: Vec<String>,
}

} // verus!

// ---------------------------------------------------------------------------
// Persisted rows and byte framing
// ---------------------------------------------------------------------------

/// The task fields nested in a persisted workflow row.
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Task {
    pub state: TaskState,
    pub version: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ttl: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pid: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lease_timeout_at: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub retry_timeout_at: Option<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub resumes: Vec<String>,
}

/// One persisted promise row in a workflow document.
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Promise {
    pub id: String,
    pub state: PromiseState,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub tags: Tags,
    #[serde(default)]
    pub param: Value,
    #[serde(default)]
    pub value: Value,
    pub timeout_at: u64,
    pub created_at: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub settled_at: Option<u64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub callbacks: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub listeners: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub task: Option<Task>,
}

#[cfg(not(verus_keep_ghost))]
impl Promise {
    pub fn into_entry(self) -> (String, Obj) {
        let Promise {
            id,
            state,
            tags,
            param,
            value,
            timeout_at,
            created_at,
            settled_at,
            callbacks,
            listeners,
            task,
        } = self;
        let promise = Prom {
            state,
            param,
            value,
            tags,
            timeout_at,
            created_at,
            settled_at,
            callbacks,
            listeners,
        };
        let task = task.map(|t| Tk {
            state: t.state,
            version: t.version,
            pid: t.pid,
            ttl: t.ttl,
            lease_timeout_at: t.lease_timeout_at,
            retry_timeout_at: t.retry_timeout_at,
            resumes: t.resumes,
        });
        (id, Obj { promise, task })
    }

    pub fn from_entry(id: String, obj: Obj) -> Self {
        let Obj { promise: p, task } = obj;
        let task = task.map(|t| Task {
            state: t.state,
            version: t.version,
            ttl: t.ttl,
            pid: t.pid,
            lease_timeout_at: t.lease_timeout_at,
            retry_timeout_at: t.retry_timeout_at,
            resumes: t.resumes,
        });
        Promise {
            id,
            state: p.state,
            tags: p.tags,
            param: p.param,
            value: p.value,
            timeout_at: p.timeout_at,
            created_at: p.created_at,
            settled_at: p.settled_at,
            callbacks: p.callbacks,
            listeners: p.listeners,
            task,
        }
    }
}

#[cfg(not(verus_keep_ghost))]
pub type WorkflowPartial = Partial<Promise>;
pub type SchedulePartial = Partial<Schedule>;

#[cfg(not(verus_keep_ghost))]
pub fn promises(body: &DocumentBody) -> Vec<Promise> {
    match body {
        DocumentBody::Workflow(objects) => objects
            .clone()
            .into_entries()
            .into_iter()
            .map(|(id, object)| Promise::from_entry(id, object))
            .collect(),
        DocumentBody::Schedule(_) => Vec::new(),
    }
}

#[cfg(not(verus_keep_ghost))]
pub fn schedules(body: &DocumentBody) -> Vec<Schedule> {
    match body {
        DocumentBody::Schedule(Some(schedule)) => vec![schedule.clone()],
        _ => Vec::new(),
    }
}

/// Each partial is one JSON line.  JSON escapes embedded newlines, so a
/// successful parse recovers exactly the stored partial boundaries.
#[cfg(not(verus_keep_ghost))]
pub mod codec {
    use serde::de::DeserializeOwned;
    use serde::Serialize;

    use super::{
        Change, DocumentBody, Folded, Objects, Partial, Promise, Schedule, ScheduleDocument,
        StoredDocument, WorkflowDocument,
    };

    pub fn encode_partial<R: Serialize>(partial: &Partial<R>) -> Result<Vec<u8>, String> {
        let mut bytes = serde_json::to_vec(partial).map_err(|e| e.to_string())?;
        bytes.push(b'\n');
        Ok(bytes)
    }

    pub fn encode_partials<R: Serialize>(partials: &[Partial<R>]) -> Result<Vec<u8>, String> {
        let mut bytes = Vec::new();
        for partial in partials {
            bytes.extend(encode_partial(partial)?);
        }
        Ok(bytes)
    }

    pub fn decode_partials<R: DeserializeOwned>(bytes: &[u8]) -> Result<Vec<Partial<R>>, String> {
        let mut partials = Vec::new();
        for line in bytes.split(|b| *b == b'\n') {
            if line.is_empty() {
                continue;
            }
            partials.push(serde_json::from_slice(line).map_err(|e| e.to_string())?);
        }
        Ok(partials)
    }

    fn fold_bytes<R: Clone + DeserializeOwned>(bytes: &[u8]) -> Result<(Folded<R>, usize), String> {
        let partials = decode_partials::<R>(bytes)?;
        let Some(first) = partials.first() else {
            return Err("a stored document has no partials".to_string());
        };
        let change_count = partials.iter().map(|p| p.changes.len()).sum();
        Ok((
            super::fold(first.document.clone(), &partials)?,
            change_count,
        ))
    }

    pub fn decode_workflow(bytes: &[u8]) -> Result<(WorkflowDocument, usize), String> {
        let (folded, change_count) = fold_bytes::<Promise>(bytes)?;
        if folded
            .entries
            .iter()
            .any(|(id, row)| id != &row.id || echod_types::origin_of(id) != folded.document)
        {
            return Err("promise id does not belong to its workflow document".to_string());
        }
        let mut entries: Vec<_> = folded
            .entries
            .into_iter()
            .map(|(_, row)| row.into_entry())
            .collect();
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        let objects = Objects { entries };
        let body = super::DocumentBody::Workflow(objects.clone());
        if crate::node::body_deadline(&body) != folded.next_wake_at {
            return Err("stored next_wake_at does not match the workflow document".to_string());
        }
        Ok((
            WorkflowDocument {
                document: folded.document,
                version: folded.version,
                committed_at: folded.committed_at,
                next_wake_at: folded.next_wake_at,
                objects,
            },
            change_count,
        ))
    }

    pub fn decode_schedule(bytes: &[u8]) -> Result<(ScheduleDocument, usize), String> {
        let (folded, change_count) = fold_bytes::<Schedule>(bytes)?;
        if folded.entries.len() > 1 {
            return Err("a schedule document contains more than one schedule".to_string());
        }
        let schedule = folded
            .entries
            .into_iter()
            .next()
            .map(|(_, schedule)| schedule);
        if let Some(row) = &schedule {
            if row.id != folded.document {
                return Err("schedule id does not match its document".to_string());
            }
        }
        let body = super::DocumentBody::Schedule(schedule.clone());
        if crate::node::body_deadline(&body) != folded.next_wake_at {
            return Err("stored next_wake_at does not match the schedule document".to_string());
        }
        Ok((
            ScheduleDocument {
                document: folded.document,
                version: folded.version,
                committed_at: folded.committed_at,
                next_wake_at: folded.next_wake_at,
                schedule,
            },
            change_count,
        ))
    }

    fn partial<R>(
        document: &str,
        basever: u64,
        version: u64,
        committed_at: u64,
        next_wake_at: Option<u64>,
        changes: Vec<Change<R>>,
    ) -> Partial<R> {
        Partial {
            document: document.to_string(),
            basever,
            version,
            committed_at,
            next_wake_at,
            changes,
        }
    }

    fn workflow_entries(body: &DocumentBody) -> Vec<(String, Promise)> {
        super::promises(body)
            .into_iter()
            .map(|promise| (promise.id.clone(), promise))
            .collect()
    }

    fn schedule_entries(body: &DocumentBody) -> Vec<(String, Schedule)> {
        super::schedules(body)
            .into_iter()
            .map(|schedule| (schedule.id.clone(), schedule))
            .collect()
    }

    fn changed<R: Serialize + Clone>(
        before: &[(String, R)],
        after: &[(String, R)],
    ) -> Vec<(String, R)> {
        let mut out = Vec::new();
        for (id, value) in after {
            let same = before
                .iter()
                .find(|(candidate, _)| candidate == id)
                .map(|(_, previous)| {
                    serde_json::to_vec(previous).ok() == serde_json::to_vec(value).ok()
                })
                .unwrap_or(false);
            if !same {
                out.push((id.clone(), value.clone()));
            }
        }
        out
    }

    fn changes<R: Serialize + Clone>(
        before: &[(String, R)],
        after: &[(String, R)],
    ) -> Vec<Change<R>> {
        let mut changes: Vec<_> = changed(before, after)
            .into_iter()
            .map(|(id, value)| Change::Upsert { id, value })
            .collect();
        for (id, _) in before {
            if !after.iter().any(|(candidate, _)| candidate == id) {
                changes.push(Change::Remove { id: id.clone() });
            }
        }
        changes
    }

    pub fn encode(document: &StoredDocument) -> Result<Vec<u8>, String> {
        match document {
            StoredDocument::Workflow(doc) => {
                let body = DocumentBody::Workflow(doc.objects.clone());
                let changes = workflow_entries(&body)
                    .into_iter()
                    .map(|(id, value)| Change::Upsert { id, value })
                    .collect();
                encode_partial(&partial(
                    &doc.document,
                    0,
                    doc.version,
                    doc.committed_at,
                    doc.next_wake_at,
                    changes,
                ))
            }
            StoredDocument::Schedule(doc) => {
                let body = DocumentBody::Schedule(doc.schedule.clone());
                let changes = schedule_entries(&body)
                    .into_iter()
                    .map(|(id, value)| Change::Upsert { id, value })
                    .collect();
                encode_partial(&partial(
                    &doc.document,
                    0,
                    doc.version,
                    doc.committed_at,
                    doc.next_wake_at,
                    changes,
                ))
            }
        }
    }

    pub fn encode_delta(
        before: &StoredDocument,
        after: &StoredDocument,
    ) -> Result<(Vec<u8>, usize), String> {
        match (before, after) {
            (StoredDocument::Workflow(before), StoredDocument::Workflow(after)) => {
                let before_body = DocumentBody::Workflow(before.objects.clone());
                let after_body = DocumentBody::Workflow(after.objects.clone());
                let changes = changes(
                    &workflow_entries(&before_body),
                    &workflow_entries(&after_body),
                );
                let count = changes.len();
                Ok((
                    encode_partial(&partial(
                        &after.document,
                        before.version,
                        after.version,
                        after.committed_at,
                        after.next_wake_at,
                        changes,
                    ))?,
                    count,
                ))
            }
            (StoredDocument::Schedule(before), StoredDocument::Schedule(after)) => {
                let before_body = DocumentBody::Schedule(before.schedule.clone());
                let after_body = DocumentBody::Schedule(after.schedule.clone());
                let changes = changes(
                    &schedule_entries(&before_body),
                    &schedule_entries(&after_body),
                );
                let count = changes.len();
                Ok((
                    encode_partial(&partial(
                        &after.document,
                        before.version,
                        after.version,
                        after.committed_at,
                        after.next_wake_at,
                        changes,
                    ))?,
                    count,
                ))
            }
            _ => Err("document kind changed".to_string()),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
fn fold<R: Clone>(document: String, partials: &[Partial<R>]) -> Result<Folded<R>, String> {
    let mut folded = Folded::empty(document);
    for partial in partials {
        folded = folded.apply(partial)?;
    }
    Ok(folded)
}

#[cfg(not(verus_keep_ghost))]
pub fn compact<R: Clone>(partials: &[Partial<R>]) -> Result<Option<Partial<R>>, String> {
    let Some(first) = partials.first() else {
        return Ok(None);
    };
    let mut result = first.clone();
    for partial in &partials[1..] {
        result = result.compose(partial)?;
    }
    Ok(Some(result))
}

#[cfg(all(test, not(verus_keep_ghost)))]
mod tests {
    use super::{codec, compact, fold, Change, Folded, Partial};

    fn partial(basever: u64, version: u64, value: &str) -> Partial<String> {
        Partial {
            document: "wf".to_string(),
            basever,
            version,
            committed_at: version * 10,
            next_wake_at: Some(version * 10 + 5),
            changes: vec![Change::Upsert {
                id: "wf:1".to_string(),
                value: value.to_string(),
            }],
        }
    }

    #[test]
    fn encoded_boundaries_round_trip() {
        let partials = vec![partial(0, 1, "one"), partial(1, 2, "two")];
        let bytes = codec::encode_partials(&partials).unwrap();
        assert_eq!(codec::decode_partials::<String>(&bytes).unwrap(), partials);
    }

    #[test]
    fn append_commutes_with_fold() {
        let first = partial(0, 1, "one");
        let second = partial(1, 2, "two");
        let before = fold("wf".to_string(), std::slice::from_ref(&first)).unwrap();
        let after = before.apply(&second).unwrap();
        assert_eq!(after, fold("wf".to_string(), &[first, second]).unwrap());
    }

    #[test]
    fn composition_preserves_the_fold() {
        let first = partial(0, 1, "one");
        let second = partial(1, 2, "two");
        let compacted = compact(&[first.clone(), second.clone()]).unwrap().unwrap();
        let empty = Folded::empty("wf".to_string());
        assert_eq!(
            empty.apply(&compacted).unwrap(),
            empty.apply(&first).unwrap().apply(&second).unwrap(),
        );
    }

    #[test]
    fn remove_is_part_of_the_algebra() {
        let first = partial(0, 1, "one");
        let remove = Partial {
            document: "wf".to_string(),
            basever: 1,
            version: 2,
            committed_at: 20,
            next_wake_at: None,
            changes: vec![Change::Remove {
                id: "wf:1".to_string(),
            }],
        };
        assert!(fold("wf".to_string(), &[first, remove])
            .unwrap()
            .entries
            .is_empty());
    }
}
