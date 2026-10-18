//! An origin's document: a log of rows in the object, a map in memory.
//!
//! The object is JSON lines: a header, then one `Promise` per row, in commit
//! order. Reading folds the rows by id, last row winning —
//! `echod_kernel::store::fold_by`, which the kernel proves is what
//! compaction preserves. Writing appends a header and the rows the step
//! changed, or rewrites the whole object once enough rows are stale.
//!
//! The header carries the instant the step that wrote it was decided at —
//! the next step on the document is decided no earlier, which keeps every
//! step within what the kernel is proved for — and a nonce, so that every
//! write, a rewrite of the same rows included, is a new version: the
//! conditional writes of every commit in flight are fenced by it.

use echod_kernel::Promise;
use serde::{Deserialize, Serialize};

/// What was read: the folded rows, how many rows the object holds, the
/// bytes it holds, so an append knows its offset, and the stamp of the last
/// write.
#[derive(Clone)]
pub struct Loaded {
    pub rows: Vec<Promise>,
    pub row_count: usize,
    pub bytes: u64,
    pub stamp: u64,
}

impl Loaded {
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
#[serde(untagged)]
enum Line {
    Header(Header),
    Row(Promise),
}

/// Fold the object's rows by id, last wins, keeping first-seen order; the
/// stamp is the last header's.
pub fn decode(bytes: &[u8]) -> Result<Loaded, String> {
    let mut rows: Vec<Promise> = Vec::new();
    let mut count = 0usize;
    let mut stamp = 0u64;
    for line in bytes.split(|b| *b == b'\n') {
        if line.is_empty() {
            continue;
        }
        match serde_json::from_slice::<Line>(line).map_err(|e| format!("bad row: {e}"))? {
            Line::Header(h) => stamp = stamp.max(h.stamp),
            Line::Row(p) => {
                count += 1;
                match rows.iter().position(|q| q.id == p.id) {
                    Some(i) => rows[i] = p,
                    None => rows.push(p),
                }
            }
        }
    }
    Ok(Loaded { rows, row_count: count, bytes: bytes.len() as u64, stamp })
}

/// The header, then the rows, one line each, newline-terminated.
pub fn encode(header: &Header, rows: &[Promise]) -> Vec<u8> {
    let mut out = Vec::new();
    serde_json::to_writer(&mut out, header).expect("a header serialises");
    out.push(b'\n');
    for p in rows {
        serde_json::to_writer(&mut out, p).expect("a promise serialises");
        out.push(b'\n');
    }
    out
}

/// The rows of `after` that differ from `before`, by id.
pub fn changed(before: &[Promise], after: &[Promise]) -> Vec<Promise> {
    let mut out = Vec::new();
    for p in after {
        let same = before.iter().find(|q| q.id == p.id).map(|q| serde_json::to_vec(q).ok() == serde_json::to_vec(p).ok()).unwrap_or(false);
        if !same {
            out.push(p.clone());
        }
    }
    out
}
