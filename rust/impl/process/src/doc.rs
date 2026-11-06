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

use echod_concrete::{doc_deadline, Doc, Obj, Objects, Prom, Tk};
use echod_types::{PromiseState, Schedule, Tags, TaskState, Value};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

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

/// A row of a document: what it is keyed by, and the document the rows of
/// an object make.
pub trait Row: Serialize + DeserializeOwned + Clone + Send + Sync + 'static {
    fn id(&self) -> &str;
    /// The document the rows make: the model's `Doc`.
    fn doc_of(rows: &[Self]) -> Doc;
    /// The rows of a document: its objects in key order, or its schedule.
    fn rows_of(doc: Doc) -> Vec<Self>;
    /// The rows as an origin's, which the node's cache holds; `None` for a
    /// schedule's, which it does not.
    fn promises(rows: &[Self]) -> Option<Vec<Promise>>;
}

impl Row for Promise {
    fn id(&self) -> &str {
        &self.id
    }
    fn doc_of(rows: &[Self]) -> Doc {
        Doc::Origin(Objects::from_entries(rows.iter().cloned().map(Promise::into_entry).collect()))
    }
    fn rows_of(doc: Doc) -> Vec<Self> {
        match doc {
            Doc::Origin(objs) => objs.into_entries().into_iter().map(|(id, obj)| Promise::from_entry(id, obj)).collect(),
            Doc::Schedule(_) => Vec::new(),
        }
    }
    fn promises(rows: &[Self]) -> Option<Vec<Promise>> {
        Some(rows.to_vec())
    }
}

impl Row for Schedule {
    fn id(&self) -> &str {
        &self.id
    }
    fn doc_of(rows: &[Self]) -> Doc {
        Doc::Schedule(rows.last().cloned())
    }
    fn rows_of(doc: Doc) -> Vec<Self> {
        match doc {
            Doc::Schedule(Some(s)) => vec![s],
            _ => Vec::new(),
        }
    }
    fn promises(_rows: &[Self]) -> Option<Vec<Promise>> {
        None
    }
}

/// The nearest deadline of a document: `doc_deadline` on its rows.
pub fn deadline<R: Row>(rows: &[R]) -> Option<u64> {
    doc_deadline(&R::doc_of(rows))
}

/// The instant a step on a document is decided at: the node's clock, or the
/// document's stamp — the instant of the step that wrote it — whichever is
/// later, so no step is decided before the one that wrote what it read.
pub fn clamp_now(stamp: u64, now: u64) -> u64 {
    stamp.max(now)
}

/// What was read: the folded rows, how many rows the object holds, the
/// bytes it holds, so an append knows its offset, and the stamp of the last
/// write.
#[derive(Clone)]
pub struct Loaded<R: Row = Promise> {
    pub rows: Vec<R>,
    pub row_count: usize,
    pub bytes: u64,
    pub stamp: u64,
}

impl<R: Row> Loaded<R> {
    pub fn empty() -> Self {
        Self { rows: vec![], row_count: 0, bytes: 0, stamp: 0 }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Header {
    pub stamp: u64,
    pub nonce: u64,
}

#[derive(Deserialize)]
#[serde(untagged, bound = "R: DeserializeOwned")]
enum Line<R> {
    Header(Header),
    Row(R),
}

/// Fold the object's rows by id, last wins, keeping first-seen order; the
/// stamp is the last header's.
pub fn decode<R: Row>(bytes: &[u8]) -> Result<Loaded<R>, String> {
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
    Ok(Loaded { rows, row_count: count, bytes: bytes.len() as u64, stamp })
}

/// The header, then the rows, one line each, newline-terminated.
pub fn encode<R: Row>(header: &Header, rows: &[R]) -> Vec<u8> {
    let mut out = Vec::new();
    serde_json::to_writer(&mut out, header).expect("a header serialises");
    out.push(b'\n');
    for p in rows {
        serde_json::to_writer(&mut out, p).expect("a row serialises");
        out.push(b'\n');
    }
    out
}

/// The rows of `after` that differ from `before`, by id.
pub fn changed<R: Row>(before: &[R], after: &[R]) -> Vec<R> {
    let mut out = Vec::new();
    for p in after {
        let same = before.iter().find(|q| q.id() == p.id()).map(|q| serde_json::to_vec(q).ok() == serde_json::to_vec(p).ok()).unwrap_or(false);
        if !same {
            out.push(p.clone());
        }
    }
    out
}
