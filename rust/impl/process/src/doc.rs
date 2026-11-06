//! A document: a log of partials in the object, the concrete model's `Doc`
//! in memory.
//!
//! A workflow document holds `Promise` rows, a task inside each; a
//! schedule's holds its one `Schedule` row, or none. Each JSON line is one
//! partial and therefore one recoverable commit boundary. Reading folds the
//! partials and their edits by id, last edit winning; the rows then make the
//! `Doc` the concrete model's steps run on, `Objects::from_entries`, and the `Doc`
//! they leave is rows again, `Objects::into_entries`. Writing appends the
//! changed rows as one partial, or rewrites the whole object as one compacted
//! partial once enough rows are stale.
//!
//! Every partial carries the logical instant and version of the committed
//! document, its base version, and the document's next wake. The next step is
//! decided no earlier than the committed instant; conditional writes fence
//! every competing commit.
//!
//! The bytes are `codec`, plain Rust over serde, stated once each: a decode
//! is some function of the bytes, an encode some function of the header and
//! the document. What the process decides from a document is proved against
//! those statements.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use echod_concrete::{clone_doc, doc_deadline, empty_workflow, empty_schedule, keys_within, same_doc, Doc};
#[cfg(verus_keep_ghost)]
use echod_concrete::lemma_doc_view;

#[cfg(verus_keep_ghost)]
use echod_concrete::node::DocV;

verus! {

/// What was read: the document, how many rows the object holds, the bytes
/// it holds, so an append knows its offset, and the metadata of the last
/// committed partial.
#[make_spec_type]
pub struct Loaded {
    pub doc: Doc,
    pub row_count: usize,
    pub bytes: u64,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
}

impl Loaded {
    /// Nothing read: an workflow's empty document.
    pub fn empty_workflow() -> (r: Loaded)
        ensures
            r.deep_view() == spec_empty_workflow(),
    {
        Loaded { doc: empty_workflow(), row_count: 0, bytes: 0, version: 0, committed_at: 0, next_wake_at: None }
    }

    /// Nothing read: a schedule's empty document.
    pub fn empty_schedule() -> (r: Loaded)
        ensures
            r.deep_view() == spec_empty_schedule(),
    {
        Loaded { doc: empty_schedule(), row_count: 0, bytes: 0, version: 0, committed_at: 0, next_wake_at: None }
    }

    pub fn copy(&self) -> (r: Loaded)
        ensures
            r == *self,
    {
        Loaded {
            doc: clone_doc(&self.doc),
            row_count: self.row_count,
            bytes: self.bytes,
            version: self.version,
            committed_at: self.committed_at,
            next_wake_at: self.next_wake_at,
        }
    }
}

pub open spec fn spec_empty_workflow() -> LoadedSpec {
    LoadedSpec { doc: DocV::Workflow(Map::empty()), row_count: 0, bytes: 0, version: 0, committed_at: 0, next_wake_at: None }
}

pub open spec fn spec_empty_schedule() -> LoadedSpec {
    LoadedSpec { doc: DocV::Schedule(None), row_count: 0, bytes: 0, version: 0, committed_at: 0, next_wake_at: None }
}

#[make_spec_type]
pub struct Header {
    pub document: String,
    pub basever: u64,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
}

/// The nearest deadline of a document.
pub fn deadline(doc: &Doc) -> (r: Option<u64>)
    ensures
        echod_concrete::node::nat_v(r) == echod_concrete::node::spec_doc_deadline(doc@),
{
    doc_deadline(doc)
}

pub open spec fn spec_deadline_time(doc: DocV) -> Option<u64> {
    match echod_concrete::node::spec_doc_deadline(doc) {
        Some(t) => Some(t as u64),
        None => None,
    }
}

/// The instant a step on a document is decided at: the node's clock, or the
/// document's committed instant, whichever is later, so no step is decided
/// before the one that wrote what it read.
pub open spec fn spec_clamp_now(committed_at: u64, now: u64) -> u64 {
    if committed_at > now { committed_at } else { now }
}

pub fn clamp_now(committed_at: u64, now: u64) -> (r: u64)
    ensures
        r == spec_clamp_now(committed_at, now),
{
    if committed_at > now { committed_at } else { now }
}

/// `after` differs from `before`.
pub fn changed(before: &Doc, after: &Doc) -> (r: bool)
    ensures
        r == (before@ != after@),
{
    !same_doc(before, after)
}

/// A row of `before` is gone from `after`: an object removed, or the
/// schedule deleted. Such a document cannot be appended to.
pub open spec fn spec_removed_any(before: DocV, after: DocV) -> bool {
    match (before, after) {
        (DocV::Workflow(b), DocV::Workflow(a)) => !b.dom().subset_of(a.dom()),
        (DocV::Schedule(Some(_)), DocV::Schedule(None)) => true,
        (DocV::Schedule(_), DocV::Schedule(_)) => false,
        _ => true,
    }
}

pub fn removed_any(before: &Doc, after: &Doc) -> (r: bool)
    ensures
        r == spec_removed_any(before@, after@),
{
    proof {
        lemma_doc_view(before);
        lemma_doc_view(after);
    }
    match (before, after) {
        (Doc::Workflow(b), Doc::Workflow(a)) => !keys_within(b, a),
        (Doc::Schedule(Some(_)), Doc::Schedule(None)) => true,
        (Doc::Schedule(_), Doc::Schedule(_)) => false,
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// The bytes, stated
// ---------------------------------------------------------------------------

/// What the bytes of an origin's object say: the folded rows as a
/// document, or why they cannot be read.
pub uninterp spec fn spec_decode_workflow(bytes: Seq<u8>) -> Result<LoadedSpec, Seq<char>>;
/// What the bytes of a schedule's object say.
pub uninterp spec fn spec_decode_schedule(bytes: Seq<u8>) -> Result<LoadedSpec, Seq<char>>;
/// The header, then every row of the document, one line each.
pub uninterp spec fn spec_encode(header: HeaderSpec, doc: DocV) -> Seq<u8>;
/// The header, then the rows of `after` that differ from `before`, and how
/// many rows that is.
pub uninterp spec fn spec_encode_delta(header: HeaderSpec, before: DocV, after: DocV) -> (Seq<u8>, usize);

pub assume_specification [codec::decode_workflow](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_workflow(bytes@);

pub assume_specification [codec::decode_schedule](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_schedule(bytes@);

pub assume_specification [codec::encode](header: &Header, doc: &Doc) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode(header.deep_view(), doc@);

pub assume_specification [codec::encode_delta](header: &Header, before: &Doc, after: &Doc) -> (r: (Vec<u8>, usize))
    ensures
        (r.0@, r.1) == spec_encode_delta(header.deep_view(), before@, after@);

pub fn decode_workflow(bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_workflow(bytes@),
{
    codec::decode_workflow(bytes)
}

pub fn decode_schedule(bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_schedule(bytes@),
{
    codec::decode_schedule(bytes)
}

pub fn encode(header: &Header, doc: &Doc) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode(header.deep_view(), doc@),
{
    codec::encode(header, doc)
}

pub fn encode_delta(header: &Header, before: &Doc, after: &Doc) -> (r: (Vec<u8>, usize))
    ensures
        (r.0@, r.1) == spec_encode_delta(header.deep_view(), before@, after@),
{
    codec::encode_delta(header, before, after)
}

} // verus!

/// The rows on the wire, and the lines they make. Plain Rust over serde,
/// stated above.
#[cfg(not(verus_keep_ghost))]
pub mod codec {
    use echod_concrete::document::WorkflowRow;
    use echod_concrete::{Doc, Objects};
    use echod_types::Schedule;
    use serde::de::DeserializeOwned;
    use serde::Serialize;

    use super::{Header, Loaded};

    pub use echod_concrete::document::{TaskRow as Task, WorkflowRow as Promise};

    /// A row of a document: what it is keyed by, and the document the rows
    /// of an object make.
    pub trait Row: Serialize + DeserializeOwned + Clone + Send + Sync + 'static {
        fn id(&self) -> &str;
        /// The document the rows make: the model's `Doc`.
        fn doc_of(rows: &[Self]) -> Doc;
        /// The rows of a document: its objects, or its schedule.
        fn rows_of(doc: &Doc) -> Vec<Self>;
    }

    impl Row for WorkflowRow {
        fn id(&self) -> &str {
            &self.id
        }
        fn doc_of(rows: &[Self]) -> Doc {
            Doc::Workflow(Objects::from_entries(rows.iter().cloned().map(WorkflowRow::into_entry).collect()))
        }
        fn rows_of(doc: &Doc) -> Vec<Self> {
            match doc {
                Doc::Workflow(objs) => objs.clone().into_entries().into_iter().map(|(id, obj)| WorkflowRow::from_entry(id, obj)).collect(),
                Doc::Schedule(_) => Vec::new(),
            }
        }
    }

    impl Row for Schedule {
        fn id(&self) -> &str {
            &self.id
        }
        fn doc_of(rows: &[Self]) -> Doc {
            Doc::Schedule(rows.last().cloned())
        }
        fn rows_of(doc: &Doc) -> Vec<Self> {
            match doc {
                Doc::Schedule(Some(s)) => vec![s.clone()],
                _ => Vec::new(),
            }
        }
    }

    /// The rows of a workflow document: its promises.
    pub fn promises(doc: &Doc) -> Vec<WorkflowRow> {
        WorkflowRow::rows_of(doc)
    }

    /// The rows of a schedule's document: its schedule, if any.
    pub fn schedules(doc: &Doc) -> Vec<Schedule> {
        Schedule::rows_of(doc)
    }

    struct Decoded<R> {
        rows: Vec<R>,
        row_count: usize,
        version: u64,
        committed_at: u64,
        next_wake_at: Option<u64>,
    }

    fn decode<R: Row>(bytes: &[u8]) -> Result<Decoded<R>, String> {
        let partials = echod_concrete::document::codec::decode_partials::<R>(bytes)?;
        match partials.first() {
            Some(first) => {
                let document = first.document.clone();
                let row_count = partials.iter().map(|p| p.changes.len()).sum();
                let folded = echod_concrete::document::fold(document, &partials)?;
                for (id, row) in &folded.entries {
                    if row.id() != id {
                        return Err("partial key does not match its row".to_string());
                    }
                }
                Ok(Decoded {
                    rows: folded.entries.into_iter().map(|(_, row)| row).collect(),
                    row_count,
                    version: folded.version,
                    committed_at: folded.committed_at,
                    next_wake_at: folded.next_wake_at,
                })
            }
            None => Ok(Decoded {
                rows: Vec::new(),
                row_count: 0,
                version: 0,
                committed_at: 0,
                next_wake_at: None,
            }),
        }
    }

    pub fn decode_workflow(bytes: &[u8]) -> Result<Loaded, String> {
        let Decoded { rows, row_count, version, committed_at, next_wake_at } = decode::<WorkflowRow>(bytes)?;
        let doc = WorkflowRow::doc_of(&rows);
        if version > 0 && echod_concrete::doc_deadline(&doc) != next_wake_at {
            return Err("stored next_wake_at does not match the workflow document".to_string());
        }
        Ok(Loaded {
            doc,
            row_count,
            bytes: bytes.len() as u64,
            version,
            committed_at,
            next_wake_at,
        })
    }

    pub fn decode_schedule(bytes: &[u8]) -> Result<Loaded, String> {
        let Decoded { rows, row_count, version, committed_at, next_wake_at } = decode::<Schedule>(bytes)?;
        let doc = Schedule::doc_of(&rows);
        if version > 0 && echod_concrete::doc_deadline(&doc) != next_wake_at {
            return Err("stored next_wake_at does not match the schedule document".to_string());
        }
        Ok(Loaded {
            doc,
            row_count,
            bytes: bytes.len() as u64,
            version,
            committed_at,
            next_wake_at,
        })
    }

    fn partial<R>(header: &Header, basever: u64, changes: Vec<echod_concrete::document::Change<R>>) -> echod_concrete::document::Partial<R> {
        echod_concrete::document::Partial {
            document: header.document.clone(),
            basever,
            version: header.version,
            committed_at: header.committed_at,
            next_wake_at: header.next_wake_at,
            changes,
        }
    }

    /// A compacted partial from the empty document to `doc`.
    pub fn encode(header: &Header, doc: &Doc) -> Vec<u8> {
        match doc {
            Doc::Workflow(_) => {
                let changes = promises(doc).into_iter().map(|row| {
                    let id = row.id.clone();
                    echod_concrete::document::Change::Upsert { id, value: row }
                }).collect();
                echod_concrete::document::codec::encode_partial(&partial(header, 0, changes)).expect("a workflow partial serialises")
            }
            Doc::Schedule(_) => {
                let changes = schedules(doc).into_iter().map(|row| {
                    let id = row.id.clone();
                    echod_concrete::document::Change::Upsert { id, value: row }
                }).collect();
                echod_concrete::document::codec::encode_partial(&partial(header, 0, changes)).expect("a schedule partial serialises")
            }
        }
    }

    /// The rows of `after` that differ from `before`, by id.
    fn changed<R: Row>(before: &[R], after: &[R]) -> Vec<R> {
        let mut out = Vec::new();
        for p in after {
            let same = before.iter().find(|q| q.id() == p.id()).map(|q| serde_json::to_vec(q).ok() == serde_json::to_vec(p).ok()).unwrap_or(false);
            if !same {
                out.push(p.clone());
            }
        }
        out
    }

    fn changes<R: Row>(before: &[R], after: &[R]) -> Vec<echod_concrete::document::Change<R>> {
        let mut changes: Vec<_> = changed(before, after).into_iter().map(|row| {
            let id = row.id().to_string();
            echod_concrete::document::Change::Upsert { id, value: row }
        }).collect();
        for row in before {
            if !after.iter().any(|candidate| candidate.id() == row.id()) {
                changes.push(echod_concrete::document::Change::Remove { id: row.id().to_string() });
            }
        }
        changes
    }

    /// One partial carrying exactly the rows changed or removed.
    pub fn encode_delta(header: &Header, before: &Doc, after: &Doc) -> (Vec<u8>, usize) {
        match (before, after) {
            (Doc::Workflow(_), Doc::Workflow(_)) => {
                let changes = changes(&promises(before), &promises(after));
                let n = changes.len();
                let bytes = echod_concrete::document::codec::encode_partial(&partial(header, header.basever, changes)).expect("a workflow partial serialises");
                (bytes, n)
            }
            _ => {
                let changes = changes(&schedules(before), &schedules(after));
                let n = changes.len();
                let bytes = echod_concrete::document::codec::encode_partial(&partial(header, header.basever, changes)).expect("a schedule partial serialises");
                (bytes, n)
            }
        }
    }
}

/// Under Verus the bytes are stated, never built: serde is absent there.
#[cfg(verus_keep_ghost)]
pub mod codec {
    use echod_concrete::Doc;

    use super::{Header, Loaded};

    pub fn decode_workflow(_bytes: &[u8]) -> Result<Loaded, String> {
        unimplemented!()
    }

    pub fn decode_schedule(_bytes: &[u8]) -> Result<Loaded, String> {
        unimplemented!()
    }

    pub fn encode(_header: &Header, _doc: &Doc) -> Vec<u8> {
        unimplemented!()
    }

    pub fn encode_delta(_header: &Header, _before: &Doc, _after: &Doc) -> (Vec<u8>, usize) {
        unimplemented!()
    }
}

#[cfg(all(test, not(verus_keep_ghost)))]
mod tests {
    use echod_concrete::Doc;
    use echod_types::{Schedule, Value};

    use super::{codec, Header};

    fn schedule(next_run_at: u64) -> Schedule {
        Schedule {
            id: "schedule".to_string(),
            cron: "* * * * *".to_string(),
            promise_id: "wf:{{.id}}".to_string(),
            promise_timeout: 1_000,
            promise_param: Value::default(),
            promise_tags: Vec::new(),
            next_run_at,
            last_run_at: None,
            created_at: 1,
        }
    }

    fn header(basever: u64, version: u64, committed_at: u64, next_wake_at: Option<u64>) -> Header {
        Header {
            document: "schedule".to_string(),
            basever,
            version,
            committed_at,
            next_wake_at,
        }
    }

    #[test]
    fn schedule_partials_round_trip_and_keep_boundaries() {
        let first = Doc::Schedule(Some(schedule(20)));
        let mut bytes = codec::encode(&header(0, 1, 10, Some(20)), &first);

        let second = Doc::Schedule(Some(schedule(30)));
        let (delta, changed) = codec::encode_delta(&header(1, 2, 20, Some(30)), &first, &second);
        assert_eq!(changed, 1);
        bytes.extend(delta);

        let partials = echod_concrete::document::codec::decode_partials::<Schedule>(&bytes).unwrap();
        assert_eq!(partials.len(), 2);

        let loaded = codec::decode_schedule(&bytes).unwrap();
        assert_eq!(loaded.doc, second);
        assert_eq!(loaded.version, 2);
        assert_eq!(loaded.committed_at, 20);
        assert_eq!(loaded.next_wake_at, Some(30));
    }

    #[test]
    fn compacted_schedule_is_one_partial_with_same_document() {
        let doc = Doc::Schedule(Some(schedule(20)));
        let bytes = codec::encode(&header(0, 7, 10, Some(20)), &doc);
        let partials = echod_concrete::document::codec::decode_partials::<Schedule>(&bytes).unwrap();
        assert_eq!(partials.len(), 1);

        let loaded = codec::decode_schedule(&bytes).unwrap();
        assert_eq!(loaded.doc, doc);
        assert_eq!(loaded.version, 7);
    }
}
