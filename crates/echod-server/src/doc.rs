//! An origin's document: a log of rows in the object, a map in memory.
//!
//! The object is JSON lines, one `Promise` per row, in commit order. Reading
//! folds the rows by id, last row winning — `echod_kernel::store::fold_by`,
//! which the kernel proves is what compaction preserves. Writing appends the
//! rows the step changed, or rewrites the whole object once enough rows are
//! stale.

use echod_kernel::Promise;

/// What was read: the folded rows, how many rows the object holds, and the
/// bytes it holds, so an append knows its offset.
#[derive(Clone)]
pub struct Loaded {
    pub rows: Vec<Promise>,
    pub row_count: usize,
    pub bytes: u64,
}

/// Fold the object's rows by id, last wins, keeping first-seen order.
pub fn decode(bytes: &[u8]) -> Result<Loaded, String> {
    let mut rows: Vec<Promise> = Vec::new();
    let mut count = 0usize;
    for line in bytes.split(|b| *b == b'\n') {
        if line.is_empty() {
            continue;
        }
        let p: Promise = serde_json::from_slice(line).map_err(|e| format!("bad row: {e}"))?;
        count += 1;
        match rows.iter().position(|q| q.id == p.id) {
            Some(i) => rows[i] = p,
            None => rows.push(p),
        }
    }
    Ok(Loaded { rows, row_count: count, bytes: bytes.len() as u64 })
}

/// Rows as the object holds them: one line each, newline-terminated.
pub fn encode(rows: &[Promise]) -> Vec<u8> {
    let mut out = Vec::new();
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
