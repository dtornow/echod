//! A document: a log of rows in the object, a map in memory.
//!
//! An origin's document holds `Promise` rows; a schedule's holds its one
//! `Schedule` row, or none. The object is JSON lines: a header, then one row
//! per line, in commit order. Reading folds the rows by id, last row
//! winning — `echod_kernel::store::fold_by`, which the kernel proves is what
//! compaction preserves. Writing appends a header and the rows the step
//! changed, or rewrites the whole object once enough rows are stale.
//!
//! The header carries the instant the step that wrote it was decided at —
//! the next step on the document is decided no earlier, which keeps every
//! step within what the kernel is proved for — and a nonce, so that every
//! write, a rewrite of the same rows included, is a new version: the
//! conditional writes of every commit in flight are fenced by it.

use echod_kernel::{Promise, Schedule, State};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

/// A row of a document: what it is keyed by, and the kernel state the rows
/// of a document make.
pub trait Row: Serialize + DeserializeOwned + Clone + Send + Sync + 'static {
    fn id(&self) -> &str;
    fn state_of(rows: &[Self]) -> State;
    /// The rows of a document from a kernel state: its objects, or its
    /// schedules.
    fn rows_of(s: &State) -> Vec<Self>;
    /// The rows as an origin's, which the node's cache holds; `None` for a
    /// schedule's, which it does not.
    fn promises(rows: &[Self]) -> Option<Vec<Promise>>;
}

impl Row for Promise {
    fn id(&self) -> &str {
        &self.id
    }
    fn state_of(rows: &[Self]) -> State {
        State { objects: rows.to_vec(), schedules: Vec::new(), outbox: Vec::new() }
    }
    fn rows_of(s: &State) -> Vec<Self> {
        s.objects.clone()
    }
    fn promises(rows: &[Self]) -> Option<Vec<Promise>> {
        Some(rows.to_vec())
    }
}

impl Row for Schedule {
    fn id(&self) -> &str {
        &self.id
    }
    fn state_of(rows: &[Self]) -> State {
        State { objects: Vec::new(), schedules: rows.to_vec(), outbox: Vec::new() }
    }
    fn rows_of(s: &State) -> Vec<Self> {
        s.schedules.clone()
    }
    fn promises(_rows: &[Self]) -> Option<Vec<Promise>> {
        None
    }
}

/// What was read: the folded rows, how many rows the object holds, the
/// bytes it holds, so an append knows its offset, the stamp of the last
/// write, and how many writes the document has seen.
#[derive(Clone)]
pub struct Loaded<R: Row = Promise> {
    pub rows: Vec<R>,
    pub row_count: usize,
    pub bytes: u64,
    pub stamp: u64,
    pub seq: u64,
}

impl<R: Row> Loaded<R> {
    pub fn empty() -> Self {
        Self { rows: vec![], row_count: 0, bytes: 0, stamp: 0, seq: 0 }
    }
}

/// The line a write puts first: the instant the step was decided at, a
/// nonce, and the write's number in the document's history (the previous
/// header's plus one), which orders two steps decided at one instant.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Header {
    pub stamp: u64,
    pub nonce: u64,
    #[serde(default)]
    pub seq: u64,
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
    let mut seq = 0u64;
    for line in bytes.split(|b| *b == b'\n') {
        if line.is_empty() {
            continue;
        }
        match serde_json::from_slice::<Line<R>>(line).map_err(|e| format!("bad row: {e}"))? {
            Line::Header(h) => {
                stamp = stamp.max(h.stamp);
                seq = seq.max(h.seq);
            }
            Line::Row(p) => {
                count += 1;
                match rows.iter().position(|q| q.id() == p.id()) {
                    Some(i) => rows[i] = p,
                    None => rows.push(p),
                }
            }
        }
    }
    Ok(Loaded { rows, row_count: count, bytes: bytes.len() as u64, stamp, seq })
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
