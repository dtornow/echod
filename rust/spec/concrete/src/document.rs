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
pub struct Document<R> {
    pub document: String,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
    pub entries: Vec<(String, R)>,
}

#[cfg(not(verus_keep_ghost))]
impl<R> Document<R> {
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
impl<R: Clone> Document<R> {
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

/// The document values used by the two physical document families.
pub type WorkflowDocument = Document<Obj>;
pub type ScheduleDocument = Document<Schedule>;

/// Their stored units.
pub type WorkflowPartial = Partial<Obj>;
pub type SchedulePartial = Partial<Schedule>;

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
pub struct DocumentV<V> {
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
pub open spec fn spec_apply<V>(document: DocumentV<V>, partial: PartialV<V>) -> DocumentV<V> {
    DocumentV {
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
    document: DocumentV<V>,
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
pub enum Doc {
    Origin(Objects),
    Schedule(Option<Schedule>),
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
pub struct TaskRow {
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
pub struct WorkflowRow {
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
    pub task: Option<TaskRow>,
}

#[cfg(not(verus_keep_ghost))]
impl WorkflowRow {
    pub fn into_entry(self) -> (String, Obj) {
        let WorkflowRow {
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
        let task = task.map(|t| TaskRow {
            state: t.state,
            version: t.version,
            ttl: t.ttl,
            pid: t.pid,
            lease_timeout_at: t.lease_timeout_at,
            retry_timeout_at: t.retry_timeout_at,
            resumes: t.resumes,
        });
        WorkflowRow {
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

/// Each partial is one JSON line.  JSON escapes embedded newlines, so a
/// successful parse recovers exactly the stored partial boundaries.
#[cfg(not(verus_keep_ghost))]
pub mod codec {
    use serde::de::DeserializeOwned;
    use serde::Serialize;

    use super::Partial;

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
}

#[cfg(not(verus_keep_ghost))]
pub fn fold<R: Clone>(document: String, partials: &[Partial<R>]) -> Result<Document<R>, String> {
    let mut folded = Document::empty(document);
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
    use super::{codec, compact, fold, Change, Document, Partial};

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
        let empty = Document::empty("wf".to_string());
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
