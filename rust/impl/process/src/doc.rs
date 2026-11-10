//! A document: a log of rows in the object, the concrete model's `Doc` in
//! memory.
//!
//! An origin's document holds `Promise` rows, a task inside each; a
//! schedule's holds its one `Schedule` row, or none. The object is JSON
//! lines: a header, then one row per line, in commit order. Reading folds
//! the rows by id, last row winning; the rows then make the `Doc` the
//! concrete model's steps run on, `Objects::from_entries`, and the `Doc`
//! they leave is rows again, `Objects::into_entries`. Writing appends a
//! header and the rows the step changed, or rewrites the whole object once
//! enough rows are stale.
//!
//! The header carries the instant the step that wrote it was decided at —
//! the next step on the document is decided no earlier — and a nonce, so
//! that every write, a rewrite of the same rows included, is a new version:
//! the conditional writes of every commit in flight are fenced by it.
//!
//! The bytes are `codec`, plain Rust over serde, stated once each: a decode
//! is some function of the bytes, an encode some function of the header and
//! the document. What the process decides from a document is proved against
//! those statements.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use crate::concrete::{clone_doc, doc_deadline, empty_origin, empty_schedule, keys_within, same_doc, Doc};
#[cfg(verus_keep_ghost)]
use crate::concrete::document::lemma_doc_view;

#[cfg(verus_keep_ghost)]
use echod_concrete::node::DocV;

verus! {

/// What was read: the document, how many rows the object holds, the bytes
/// it holds, so an append knows its offset, and the stamp of the last
/// write.
#[make_spec_type]
pub struct Loaded {
    pub doc: Doc,
    pub row_count: usize,
    pub bytes: u64,
    pub stamp: u64,
}

impl Loaded {
    /// Nothing read: an origin's empty document.
    pub fn empty_origin() -> (r: Loaded)
        ensures
            r.deep_view() == spec_empty_origin(),
    {
        Loaded { doc: empty_origin(), row_count: 0, bytes: 0, stamp: 0 }
    }

    /// Nothing read: a schedule's empty document.
    pub fn empty_schedule() -> (r: Loaded)
        ensures
            r.deep_view() == spec_empty_schedule(),
    {
        Loaded { doc: empty_schedule(), row_count: 0, bytes: 0, stamp: 0 }
    }

    pub fn copy(&self) -> (r: Loaded)
        ensures
            r == *self,
    {
        Loaded { doc: clone_doc(&self.doc), row_count: self.row_count, bytes: self.bytes, stamp: self.stamp }
    }
}

pub open spec fn spec_empty_origin() -> LoadedSpec {
    LoadedSpec { doc: DocV::Origin(Map::empty()), row_count: 0, bytes: 0, stamp: 0 }
}

pub open spec fn spec_empty_schedule() -> LoadedSpec {
    LoadedSpec { doc: DocV::Schedule(None), row_count: 0, bytes: 0, stamp: 0 }
}

#[make_spec_type]
pub struct Header {
    pub stamp: u64,
    pub nonce: u64,
}

/// The nearest deadline of a document.
pub fn deadline(doc: &Doc) -> (r: Option<u64>)
    ensures
        crate::concrete::document::nat_v(r) == echod_concrete::node::spec_doc_deadline(doc@),
{
    doc_deadline(doc)
}

/// The instant a step on a document is decided at: the node's clock, or the
/// document's stamp — the instant of the step that wrote it — whichever is
/// later, so no step is decided before the one that wrote what it read.
pub open spec fn spec_clamp_now(stamp: u64, now: u64) -> u64 {
    if stamp > now { stamp } else { now }
}

pub fn clamp_now(stamp: u64, now: u64) -> (r: u64)
    ensures
        r == spec_clamp_now(stamp, now),
{
    if stamp > now { stamp } else { now }
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
        (DocV::Origin(b), DocV::Origin(a)) => !b.dom().subset_of(a.dom()),
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
        (Doc::Origin(b), Doc::Origin(a)) => !keys_within(b, a),
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
pub uninterp spec fn spec_decode_origin(bytes: Seq<u8>) -> Result<LoadedSpec, Seq<char>>;
/// What the bytes of a schedule's object say.
pub uninterp spec fn spec_decode_schedule(bytes: Seq<u8>) -> Result<LoadedSpec, Seq<char>>;
/// The header, then every row of the document, one line each.
pub uninterp spec fn spec_encode(header: HeaderSpec, doc: DocV) -> Seq<u8>;
/// The header, then the rows of `after` that differ from `before`, and how
/// many rows that is.
pub uninterp spec fn spec_encode_delta(header: HeaderSpec, before: DocV, after: DocV) -> (Seq<u8>, usize);

pub assume_specification [codec::decode_origin](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_origin(bytes@);

pub assume_specification [codec::decode_schedule](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_schedule(bytes@);

pub assume_specification [codec::encode](header: &Header, doc: &Doc) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode(header.deep_view(), doc@);

pub assume_specification [codec::encode_delta](header: &Header, before: &Doc, after: &Doc) -> (r: (Vec<u8>, usize))
    ensures
        (r.0@, r.1) == spec_encode_delta(header.deep_view(), before@, after@);

pub fn decode_origin(bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_origin(bytes@),
{
    codec::decode_origin(bytes)
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
    use crate::concrete::{Doc, Obj, Objects, Prom, Tk};
    use echod_types::{PromiseState, Schedule, Tags, TaskState, Value};
    use serde::de::DeserializeOwned;
    use serde::{Deserialize, Serialize};

    use super::{Header, Loaded};

    /// The task inside a promise's row: the concrete model's `Tk`.
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

    /// A promise's row: the concrete model's `Obj`, keyed by its id.
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

    impl Promise {
        /// The row as the model's object.
        pub fn into_entry(self) -> (String, Obj) {
            let Promise { id, state, tags, param, value, timeout_at, created_at, settled_at, callbacks, listeners, task } = self;
            let promise = Prom { state, param, value, tags, timeout_at, created_at, settled_at, callbacks, listeners };
            let task = task.map(|t| Tk { state: t.state, version: t.version, pid: t.pid, ttl: t.ttl, lease_timeout_at: t.lease_timeout_at, retry_timeout_at: t.retry_timeout_at, resumes: t.resumes });
            (id, Obj { promise, task })
        }

        /// The model's object as a row.
        pub fn from_entry(id: String, obj: Obj) -> Promise {
            let Obj { promise: p, task } = obj;
            let task = task.map(|t| Task { state: t.state, version: t.version, ttl: t.ttl, pid: t.pid, lease_timeout_at: t.lease_timeout_at, retry_timeout_at: t.retry_timeout_at, resumes: t.resumes });
            Promise { id, state: p.state, tags: p.tags, param: p.param, value: p.value, timeout_at: p.timeout_at, created_at: p.created_at, settled_at: p.settled_at, callbacks: p.callbacks, listeners: p.listeners, task }
        }
    }

    /// A row of a document: what it is keyed by, and the document the rows
    /// of an object make.
    pub trait Row: Serialize + DeserializeOwned + Clone + Send + Sync + 'static {
        fn id(&self) -> &str;
        /// The document the rows make: the model's `Doc`.
        fn doc_of(rows: &[Self]) -> Doc;
        /// The rows of a document: its objects, or its schedule.
        fn rows_of(doc: &Doc) -> Vec<Self>;
    }

    impl Row for Promise {
        fn id(&self) -> &str {
            &self.id
        }
        fn doc_of(rows: &[Self]) -> Doc {
            Doc::Origin(Objects::from_entries(rows.iter().cloned().map(Promise::into_entry).collect()))
        }
        fn rows_of(doc: &Doc) -> Vec<Self> {
            match doc {
                Doc::Origin(objs) => objs.clone().into_entries().into_iter().map(|(id, obj)| Promise::from_entry(id, obj)).collect(),
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

    /// The rows of an origin's document: its promises.
    pub fn promises(doc: &Doc) -> Vec<Promise> {
        Promise::rows_of(doc)
    }

    /// The rows of a schedule's document: its schedule, if any.
    pub fn schedules(doc: &Doc) -> Vec<Schedule> {
        Schedule::rows_of(doc)
    }

    #[derive(Serialize, Deserialize)]
    #[serde(deny_unknown_fields)]
    struct HeaderLine {
        stamp: u64,
        nonce: u64,
    }

    #[derive(Deserialize)]
    #[serde(untagged, bound = "R: DeserializeOwned")]
    enum Line<R> {
        Header(HeaderLine),
        Row(R),
    }

    /// Fold the object's rows by id, last wins, keeping first-seen order;
    /// the stamp is the last header's.
    pub fn decode<R: Row>(bytes: &[u8]) -> Result<(Vec<R>, usize, u64), String> {
        let mut rows: Vec<R> = Vec::new();
        let mut count = 0usize;
        let mut stamp = 0u64;
        for line in bytes.split(|b| *b == b'\n') {
            if line.is_empty() {
                continue;
            }
            match serde_json::from_slice::<Line<R>>(line).map_err(|e| format!("bad row: {e}"))? {
                Line::Header(h) => stamp = stamp.max(h.stamp),
                Line::Row(p) => {
                    count += 1;
                    match rows.iter().position(|q| q.id() == p.id()) {
                        Some(i) => rows[i] = p,
                        None => rows.push(p),
                    }
                }
            }
        }
        Ok((rows, count, stamp))
    }

    pub fn decode_origin(bytes: &[u8]) -> Result<Loaded, String> {
        let (rows, row_count, stamp) = decode::<Promise>(bytes)?;
        Ok(Loaded { doc: Promise::doc_of(&rows), row_count, bytes: bytes.len() as u64, stamp })
    }

    pub fn decode_schedule(bytes: &[u8]) -> Result<Loaded, String> {
        let (rows, row_count, stamp) = decode::<Schedule>(bytes)?;
        Ok(Loaded { doc: Schedule::doc_of(&rows), row_count, bytes: bytes.len() as u64, stamp })
    }

    fn write_rows<R: Row>(out: &mut Vec<u8>, rows: &[R]) {
        for p in rows {
            serde_json::to_writer(&mut *out, p).expect("a row serialises");
            out.push(b'\n');
        }
    }

    fn header_line(header: &Header) -> Vec<u8> {
        let mut out = Vec::new();
        serde_json::to_writer(&mut out, &HeaderLine { stamp: header.stamp, nonce: header.nonce }).expect("a header serialises");
        out.push(b'\n');
        out
    }

    /// The header, then the rows, one line each, newline-terminated.
    pub fn encode(header: &Header, doc: &Doc) -> Vec<u8> {
        let mut out = header_line(header);
        match doc {
            Doc::Origin(_) => write_rows(&mut out, &promises(doc)),
            Doc::Schedule(_) => write_rows(&mut out, &schedules(doc)),
        }
        out
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

    /// The header, then the rows of `after` that differ from `before`.
    pub fn encode_delta(header: &Header, before: &Doc, after: &Doc) -> (Vec<u8>, usize) {
        let mut out = header_line(header);
        let n = match (before, after) {
            (Doc::Origin(_), Doc::Origin(_)) => {
                let rows = changed(&promises(before), &promises(after));
                write_rows(&mut out, &rows);
                rows.len()
            }
            _ => {
                let rows = changed(&schedules(before), &schedules(after));
                write_rows(&mut out, &rows);
                rows.len()
            }
        };
        (out, n)
    }
}

/// Under Verus the bytes are stated, never built: serde is absent there.
#[cfg(verus_keep_ghost)]
pub mod codec {
    use crate::concrete::Doc;

    use super::{Header, Loaded};

    pub fn decode_origin(_bytes: &[u8]) -> Result<Loaded, String> {
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
