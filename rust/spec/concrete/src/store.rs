//! The store protocol the concrete Rover model speaks.
//!
//! One definition. The process re-exports these types and sends them as
//! `Effect::Store`. The model's store process applies the same calls.

use vstd::prelude::*;

verus! {

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Etag(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreError {
    /// A conditional write found the object at another version.
    PreconditionFailed,
    /// The store did not answer, or answered with an error: the effect of
    /// a write is unknown.
    Unavailable(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Read {
    Body(Vec<u8>, Etag),
    NotModified,
    Absent,
}

/// A call on the store, as the executor makes it.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreCall {
    Get { key: String },
    GetIfNoneMatch { key: String, etag: Etag },
    PutIfMatch { key: String, body: Vec<u8>, etag: Etag },
    PutIfNoneMatch { key: String, body: Vec<u8> },
    AppendIfMatch { key: String, offset: u64, body: Vec<u8>, etag: Etag },
    Put { key: String, body: Vec<u8> },
    Delete { key: String },
    List { prefix: String, max_keys: usize },
    ListPrefixes { prefix: String },
}

impl StoreCall {
    #[verifier::external_body]
    pub fn key(&self) -> &str {
        match self {
            StoreCall::Get { key }
            | StoreCall::GetIfNoneMatch { key, .. }
            | StoreCall::PutIfMatch { key, .. }
            | StoreCall::PutIfNoneMatch { key, .. }
            | StoreCall::AppendIfMatch { key, .. }
            | StoreCall::Put { key, .. }
            | StoreCall::Delete { key } => key,
            StoreCall::List { prefix, .. } | StoreCall::ListPrefixes { prefix } => prefix,
        }
    }
}

/// What a store call answered.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreOutcome {
    /// `Get`: the object and its version, or nothing.
    Got(Option<(Vec<u8>, Etag)>),
    /// `GetIfNoneMatch`.
    Read(Read),
    /// A conditional write landed at this version.
    Written(Etag),
    /// `Put` or `Delete` landed.
    Done,
    /// `List` or `ListPrefixes`.
    Listed(Vec<String>),
    Failed(StoreError),
}

/// FNV-1a over the bytes. Ownership of a key is this hash modulo the fleet.
#[verifier::external_body]
pub fn fnv1a(s: &str) -> (r: u64) {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// The version a body quotes, as an S3 ETag: the same bytes are the same version.
#[verifier::external_body]
pub fn content_etag(body: &[u8]) -> Etag {
    Etag(format!("{:016x}", fnv1a(&String::from_utf8_lossy(body))))
}

} // verus!

#[cfg(not(verus_keep_ghost))]
impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StoreError::PreconditionFailed => f.write_str("precondition failed"),
            StoreError::Unavailable(m) => write!(f, "store unavailable: {m}"),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl std::error::Error for StoreError {}
