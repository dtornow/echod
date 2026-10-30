//! A document: a log of verified binary segments in the object, a map in
//! memory.
//!
//! An origin's document holds `Promise` rows; a schedule's holds its one
//! `Schedule` row, or none. Every append is exactly one versioned,
//! self-framed `echod-codec` segment. Reading validates every segment and
//! folds rows by id, last row winning. Rewriting emits exactly one segment
//! containing the compacted rows.
//!
//! The header carries the instant the step that wrote it was decided at —
//! the next step on the document is decided no earlier, which keeps every
//! step within what the kernel is proved for — and a nonce, so that every
//! write, a rewrite of the same rows included, is a new version: the
//! conditional writes of every commit in flight are fenced by it.

use echod_codec::bridge::{promise_model, schedule_model};
use echod_codec::document::{
    decode_promise_document, decode_promise_segment, decode_schedule_document,
    decode_schedule_segment, encode_promise_segment, encode_schedule_segment, split_frame,
};
use echod_kernel::{Promise, Schedule, State};

mod sealed {
    pub trait Sealed {}

    impl Sealed for echod_kernel::Promise {}
    impl Sealed for echod_kernel::Schedule {}
}

/// A row of a document: what it is keyed by, and the kernel state the rows
/// of a document make.
pub trait Row: sealed::Sealed + Clone + Send + Sync + 'static {
    fn id(&self) -> &str;
    fn state_of(rows: &[Self]) -> State;
    /// The rows of a document from a kernel state: its objects, or its
    /// schedules.
    fn rows_of(s: &State) -> Vec<Self>;
    /// The rows as an origin's, which the node's cache holds; `None` for a
    /// schedule's, which it does not.
    fn promises(rows: &[Self]) -> Option<Vec<Promise>>;
    #[doc(hidden)]
    fn encode_segment(header: &Header, rows: &Vec<Self>) -> Result<Vec<u8>, &'static str>;
    #[doc(hidden)]
    fn decode_segment(bytes: &Vec<u8>) -> Result<(Header, Vec<Self>), &'static str>;
    #[doc(hidden)]
    fn decode_document(bytes: &Vec<u8>) -> Result<(Option<Header>, Vec<Self>), &'static str>;
    #[doc(hidden)]
    fn same(left: &Self, right: &Self) -> bool;
}

impl Row for Promise {
    fn id(&self) -> &str {
        &self.id
    }
    fn state_of(rows: &[Self]) -> State {
        State {
            objects: rows.to_vec(),
            schedules: Vec::new(),
            outbox: Vec::new(),
        }
    }
    fn rows_of(s: &State) -> Vec<Self> {
        s.objects.clone()
    }
    fn promises(rows: &[Self]) -> Option<Vec<Promise>> {
        Some(rows.to_vec())
    }
    fn encode_segment(header: &Header, rows: &Vec<Self>) -> Result<Vec<u8>, &'static str> {
        encode_promise_segment(header, rows)
    }
    fn decode_segment(bytes: &Vec<u8>) -> Result<(Header, Vec<Self>), &'static str> {
        decode_promise_segment(bytes)
    }
    fn decode_document(bytes: &Vec<u8>) -> Result<(Option<Header>, Vec<Self>), &'static str> {
        decode_promise_document(bytes)
    }
    fn same(left: &Self, right: &Self) -> bool {
        promise_model(left) == promise_model(right)
    }
}

impl Row for Schedule {
    fn id(&self) -> &str {
        &self.id
    }
    fn state_of(rows: &[Self]) -> State {
        State {
            objects: Vec::new(),
            schedules: rows.to_vec(),
            outbox: Vec::new(),
        }
    }
    fn rows_of(s: &State) -> Vec<Self> {
        s.schedules.clone()
    }
    fn promises(_rows: &[Self]) -> Option<Vec<Promise>> {
        None
    }
    fn encode_segment(header: &Header, rows: &Vec<Self>) -> Result<Vec<u8>, &'static str> {
        encode_schedule_segment(header, rows)
    }
    fn decode_segment(bytes: &Vec<u8>) -> Result<(Header, Vec<Self>), &'static str> {
        decode_schedule_segment(bytes)
    }
    fn decode_document(bytes: &Vec<u8>) -> Result<(Option<Header>, Vec<Self>), &'static str> {
        decode_schedule_document(bytes)
    }
    fn same(left: &Self, right: &Self) -> bool {
        schedule_model(left) == schedule_model(right)
    }
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
        Self {
            rows: vec![],
            row_count: 0,
            bytes: 0,
            stamp: 0,
        }
    }
}

pub use echod_codec::types::Header;

/// Fold the object's rows by id, last wins, keeping first-seen order; the
/// stamp remains the greatest stamp in any segment, as it was in the
/// previous persistence format.
pub fn decode<R: Row>(bytes: &[u8]) -> Result<Loaded<R>, String> {
    let document = bytes.to_vec();
    let (_, rows) = R::decode_document(&document).map_err(str::to_string)?;
    let mut remaining = document;
    let mut row_count = 0usize;
    let mut stamp = 0u64;
    while !remaining.is_empty() {
        let (segment, rest) = split_frame(&remaining)
            .ok_or_else(|| "malformed or truncated document segment".to_string())?;
        let (header, segment_rows) = R::decode_segment(&segment).map_err(str::to_string)?;
        row_count = row_count
            .checked_add(segment_rows.len())
            .ok_or_else(|| "document row count overflow".to_string())?;
        stamp = stamp.max(header.stamp);
        remaining = rest;
    }
    Ok(Loaded {
        rows,
        row_count,
        bytes: bytes.len() as u64,
        stamp,
    })
}

/// One verified, versioned segment containing the header and rows.
pub fn encode<R: Row>(header: &Header, rows: &[R]) -> Vec<u8> {
    R::encode_segment(header, &rows.to_vec()).expect("kernel rows are canonically encodable")
}

/// The rows of `after` that differ from `before`, by id.
pub fn changed<R: Row>(before: &[R], after: &[R]) -> Vec<R> {
    let mut out = Vec::new();
    for p in after {
        let same = before
            .iter()
            .find(|q| q.id() == p.id())
            .is_some_and(|q| R::same(q, p));
        if !same {
            out.push(p.clone());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use echod_codec::frame::FORMAT_VERSION;
    use echod_kernel::Value;

    fn schedule(id: &str, next_run_at: u64) -> Schedule {
        Schedule {
            id: id.into(),
            cron: "* * * * *".into(),
            promise_id: "promise".into(),
            promise_timeout: 10,
            promise_param: Value::empty(),
            promise_tags: vec![],
            next_run_at,
            last_run_at: None,
            created_at: 1,
        }
    }

    #[test]
    fn binary_segments_preserve_loaded_bookkeeping() {
        let old = schedule("same", 10);
        let new = schedule("same", 20);
        let first = encode(
            &Header {
                stamp: 30,
                nonce: 1,
            },
            &[old],
        );
        let second = encode(
            &Header {
                stamp: 20,
                nonce: 2,
            },
            &[new.clone()],
        );
        assert_eq!(&first[..4], b"ECHO");
        assert_eq!(first[4], FORMAT_VERSION);

        let mut bytes = first;
        bytes.extend_from_slice(&second);
        let loaded = decode::<Schedule>(&bytes).unwrap();
        assert_eq!(loaded.row_count, 2);
        assert_eq!(loaded.bytes, bytes.len() as u64);
        assert_eq!(loaded.stamp, 30);
        assert_eq!(loaded.rows.len(), 1);
        assert_eq!(schedule_model(&loaded.rows[0]), schedule_model(&new));
    }

    #[test]
    fn rewrite_is_one_segment_and_malformed_bytes_are_rejected() {
        let bytes = encode(&Header { stamp: 1, nonce: 2 }, &[schedule("a", 10)]);
        let (_, rest) = split_frame(&bytes).unwrap();
        assert!(rest.is_empty());

        for end in 1..bytes.len() {
            assert!(decode::<Schedule>(&bytes[..end]).is_err());
        }
        let mut wrong_version = bytes;
        wrong_version[4] = FORMAT_VERSION + 1;
        assert!(decode::<Schedule>(&wrong_version).is_err());
        assert!(decode::<Schedule>(b"{\"stamp\":1}\n").is_err());
    }
}
