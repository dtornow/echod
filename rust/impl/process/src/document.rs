//! The process-facing, verified facade of the shared document module.
//!
//! `echod_concrete::document` owns WorkflowDocument, ScheduleDocument,
//! Partial, their values, and their serde codec. This module states that codec
//! once for the process verifier and provides the small body projections used
//! by the pure business machine. Store keys, ETags, and CAS stay outside.
//!
//! Every partial carries the logical instant and version of the committed
//! document, its base version, and the document's next wake. The next step is
//! decided no earlier than the committed instant; conditional writes fence
//! every competing commit.
//!
//! The bytes are `codec`, plain Rust over serde, stated once each: a decode
//! is some function of the bytes, an encode some function of the document.
//! What the process decides from a document is proved against
//! those statements.

use vstd::prelude::*;

use echod_concrete::{
    body_deadline, keys_within, same_body, stored_body, stored_committed_at, DocumentBody,
    StoredDocument,
};
pub use echod_concrete::LoadedDocument as Loaded;
#[cfg(verus_keep_ghost)]
use echod_concrete::lemma_doc_view;

#[cfg(verus_keep_ghost)]
use echod_concrete::node::{DocumentBodyV, LoadedDocumentV};

verus! {

#[cfg(verus_keep_ghost)]
pub type LoadedSpec = LoadedDocumentV;

pub open spec fn spec_loaded_body(loaded: LoadedSpec) -> DocumentBodyV {
    echod_concrete::node::spec_stored_body(loaded.document)
}

pub open spec fn spec_loaded_version(loaded: LoadedSpec) -> u64 {
    echod_concrete::node::spec_stored_version(loaded.document)
}

pub open spec fn spec_loaded_committed_at(loaded: LoadedSpec) -> u64 {
    echod_concrete::node::spec_stored_committed_at(loaded.document)
}

pub fn loaded_body(loaded: &Loaded) -> (r: DocumentBody)
    ensures r@ == spec_loaded_body(loaded.deep_view()),
{
    stored_body(&loaded.document)
}

pub fn loaded_version(loaded: &Loaded) -> (r: u64)
    ensures r == spec_loaded_version(loaded.deep_view()),
{
    echod_concrete::stored_version(&loaded.document)
}

pub fn loaded_committed_at(loaded: &Loaded) -> (r: u64)
    ensures r == spec_loaded_committed_at(loaded.deep_view()),
{
    stored_committed_at(&loaded.document)
}

pub open spec fn spec_empty_workflow(document: Seq<char>) -> LoadedSpec {
    LoadedSpec {
        document: echod_concrete::node::spec_empty_stored_workflow(document),
        change_count: 0,
        bytes: 0,
    }
}

pub open spec fn spec_empty_schedule(document: Seq<char>) -> LoadedSpec {
    LoadedSpec {
        document: echod_concrete::node::spec_empty_stored_schedule(document),
        change_count: 0,
        bytes: 0,
    }
}

/// The nearest deadline of a document.
pub fn deadline(doc: &DocumentBody) -> (r: Option<u64>)
    ensures
        echod_concrete::node::nat_v(r) == echod_concrete::node::spec_body_deadline(doc@),
{
    body_deadline(doc)
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
pub fn changed(before: &DocumentBody, after: &DocumentBody) -> (r: bool)
    ensures
        r == (before@ != after@),
{
    !same_body(before, after)
}

/// A row of `before` is gone from `after`: an object removed, or the
/// schedule deleted. Such a document cannot be appended to.
pub open spec fn spec_removed_any(before: DocumentBodyV, after: DocumentBodyV) -> bool {
    match (before, after) {
        (DocumentBodyV::Workflow(b), DocumentBodyV::Workflow(a)) => !b.dom().subset_of(a.dom()),
        (DocumentBodyV::Schedule(Some(_)), DocumentBodyV::Schedule(None)) => true,
        (DocumentBodyV::Schedule(_), DocumentBodyV::Schedule(_)) => false,
        _ => true,
    }
}

pub fn removed_any(before: &DocumentBody, after: &DocumentBody) -> (r: bool)
    ensures
        r == spec_removed_any(before@, after@),
{
    proof {
        lemma_doc_view(before);
        lemma_doc_view(after);
    }
    match (before, after) {
        (DocumentBody::Workflow(b), DocumentBody::Workflow(a)) => !keys_within(b, a),
        (DocumentBody::Schedule(Some(_)), DocumentBody::Schedule(None)) => true,
        (DocumentBody::Schedule(_), DocumentBody::Schedule(_)) => false,
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// The bytes, stated
// ---------------------------------------------------------------------------

/// What the bytes of a workflow object say: the folded partials as a
/// document, or why they cannot be read.
pub uninterp spec fn spec_decode_workflow(bytes: Seq<u8>) -> Result<LoadedSpec, Seq<char>>;
/// What the bytes of a schedule's object say.
pub uninterp spec fn spec_decode_schedule(bytes: Seq<u8>) -> Result<LoadedSpec, Seq<char>>;
/// One compacted partial containing the complete document.
pub uninterp spec fn spec_encode(document: echod_concrete::node::StoredDocumentV) -> Seq<u8>;
/// One partial containing the changes from `before` to `after`, and how many
/// changes that is.
pub uninterp spec fn spec_encode_delta(
    before: echod_concrete::node::StoredDocumentV,
    after: echod_concrete::node::StoredDocumentV,
) -> (Seq<u8>, usize);

pub assume_specification [codec::decode_workflow](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_workflow(bytes@);

pub assume_specification [codec::decode_schedule](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_schedule(bytes@);

pub assume_specification [codec::encode](document: &StoredDocument) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode(document@);

pub assume_specification [codec::encode_delta](before: &StoredDocument, after: &StoredDocument) -> (r: (Vec<u8>, usize))
    ensures
        (r.0@, r.1) == spec_encode_delta(before@, after@);

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

pub fn encode(document: &StoredDocument) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode(document@),
{
    codec::encode(document)
}

pub fn encode_delta(before: &StoredDocument, after: &StoredDocument) -> (r: (Vec<u8>, usize))
    ensures
        (r.0@, r.1) == spec_encode_delta(before@, after@),
{
    codec::encode_delta(before, after)
}

} // verus!

/// Plain Rust delegates to the shared document codec stated above.
#[cfg(not(verus_keep_ghost))]
pub mod codec {
    use echod_concrete::StoredDocument;

    use super::Loaded;

    pub use echod_concrete::document::{promises, Promise, Task};

    pub fn decode_workflow(bytes: &[u8]) -> Result<Loaded, String> {
        let (document, change_count) = echod_concrete::document::codec::decode_workflow(bytes)?;
        Ok(Loaded {
            document: StoredDocument::Workflow(document),
            change_count,
            bytes: bytes.len() as u64,
        })
    }

    pub fn decode_schedule(bytes: &[u8]) -> Result<Loaded, String> {
        let (document, change_count) = echod_concrete::document::codec::decode_schedule(bytes)?;
        Ok(Loaded {
            document: StoredDocument::Schedule(document),
            change_count,
            bytes: bytes.len() as u64,
        })
    }

    pub fn encode(document: &StoredDocument) -> Vec<u8> {
        echod_concrete::document::codec::encode(document)
            .expect("a stored document serialises")
    }

    pub fn encode_delta(before: &StoredDocument, after: &StoredDocument) -> (Vec<u8>, usize) {
        echod_concrete::document::codec::encode_delta(before, after)
            .expect("a document delta serialises")
    }
}

/// Under Verus the bytes are stated, never built: serde is absent there.
#[cfg(verus_keep_ghost)]
pub mod codec {
    use echod_concrete::StoredDocument;

    use super::Loaded;

    pub fn decode_workflow(_bytes: &[u8]) -> Result<Loaded, String> {
        unimplemented!()
    }

    pub fn decode_schedule(_bytes: &[u8]) -> Result<Loaded, String> {
        unimplemented!()
    }

    pub fn encode(_document: &echod_concrete::StoredDocument) -> Vec<u8> {
        unimplemented!()
    }

    pub fn encode_delta(
        _before: &echod_concrete::StoredDocument,
        _after: &echod_concrete::StoredDocument,
    ) -> (Vec<u8>, usize) {
        unimplemented!()
    }
}

#[cfg(all(test, not(verus_keep_ghost)))]
mod tests {
    use echod_concrete::{ScheduleDocument, StoredDocument};
    use echod_types::{Schedule, Value};

    use super::codec;

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

    fn document(version: u64, committed_at: u64, next_wake_at: u64) -> StoredDocument {
        StoredDocument::Schedule(ScheduleDocument {
            document: "schedule".to_string(),
            version,
            committed_at,
            next_wake_at: Some(next_wake_at),
            schedule: Some(schedule(next_wake_at)),
        })
    }

    #[test]
    fn schedule_partials_round_trip_and_keep_boundaries() {
        let first = document(1, 10, 20);
        let mut bytes = codec::encode(&first);

        let second = document(2, 20, 30);
        let (delta, changed) = codec::encode_delta(&first, &second);
        assert_eq!(changed, 1);
        bytes.extend(delta);

        let partials = echod_concrete::document::codec::decode_partials::<Schedule>(&bytes).unwrap();
        assert_eq!(partials.len(), 2);

        let loaded = codec::decode_schedule(&bytes).unwrap();
        let StoredDocument::Schedule(loaded) = loaded.document else {
            panic!("expected schedule document");
        };
        assert_eq!(loaded.schedule, Some(schedule(30)));
        assert_eq!(loaded.version, 2);
        assert_eq!(loaded.committed_at, 20);
        assert_eq!(loaded.next_wake_at, Some(30));
    }

    #[test]
    fn compacted_schedule_is_one_partial_with_same_document() {
        let document = document(7, 10, 20);
        let bytes = codec::encode(&document);
        let partials = echod_concrete::document::codec::decode_partials::<Schedule>(&bytes).unwrap();
        assert_eq!(partials.len(), 1);

        let loaded = codec::decode_schedule(&bytes).unwrap();
        let StoredDocument::Schedule(loaded) = loaded.document else {
            panic!("expected schedule document");
        };
        assert_eq!(loaded.schedule, Some(schedule(20)));
        assert_eq!(loaded.version, 7);
    }
}
