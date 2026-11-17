//! The process-facing, verified facade of the shared document module.
//!
//! `crate::concrete::document` owns WorkflowDocument, ScheduleDocument,
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

use crate::concrete::{
    body_deadline, keys_within, same_body, stored_body, stored_committed_at, DocumentBody,
    StoredDocument,
};
pub use crate::concrete::LoadedDocument as Loaded;
#[cfg(verus_keep_ghost)]
use crate::concrete::lemma_doc_view;

#[cfg(verus_keep_ghost)]
use crate::concrete::document::{DocumentBodyV, LoadedDocumentV};

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_document_spec_loaded_body as spec_loaded_body,
    production_document_spec_loaded_version as spec_loaded_version,
    production_document_spec_loaded_committed_at as spec_loaded_committed_at,
    production_document_spec_empty_workflow as spec_empty_workflow,
    production_document_spec_empty_schedule as spec_empty_schedule,
    production_document_spec_clamp_now as spec_clamp_now,
    production_document_spec_removed_any as spec_removed_any,
    production_document_spec_decode_workflow as spec_decode_workflow,
    production_document_spec_decode_schedule as spec_decode_schedule,
    production_document_spec_encode_body as spec_encode_body,
    production_document_spec_encode_delta as spec_encode_delta,
};

verus! {

#[cfg(verus_keep_ghost)]
pub type LoadedSpec = LoadedDocumentV;







pub fn loaded_body(loaded: &Loaded) -> (r: DocumentBody)
    ensures r@ == spec_loaded_body(loaded.deep_view()),
{
    stored_body(&loaded.document)
}

pub fn loaded_version(loaded: &Loaded) -> (r: u64)
    ensures r == spec_loaded_version(loaded.deep_view()),
{
    crate::concrete::stored_version(&loaded.document)
}

pub fn loaded_committed_at(loaded: &Loaded) -> (r: u64)
    ensures r == spec_loaded_committed_at(loaded.deep_view()),
{
    stored_committed_at(&loaded.document)
}





/// The nearest deadline of a document.
pub fn deadline(doc: &DocumentBody) -> (r: Option<u64>)
    ensures
        crate::concrete::document::nat_v(r) == crate::concrete::document::spec_body_deadline(doc@),
{
    body_deadline(doc)
}

/// The instant a step on a document is decided at: the node's clock, or the
/// document's committed instant, whichever is later, so no step is decided
/// before the one that wrote what it read.


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

/// What the bytes of a schedule's object say.

/// One compacted partial containing the complete document.

/// One partial containing the changes from `before` to `after`, and how many
/// changes that is.


pub assume_specification [codec::decode_workflow](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_workflow(bytes@);

pub assume_specification [codec::decode_schedule](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_schedule(bytes@);

pub assume_specification [codec::encode](document: &StoredDocument) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode_body(document@);

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
        r@ == spec_encode_body(document@),
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
    use crate::concrete::StoredDocument;

    use super::Loaded;

    pub use crate::concrete::values::{promises, Promise, Task};

    pub fn decode_workflow(bytes: &[u8]) -> Result<Loaded, String> {
        let (document, change_count) = crate::concrete::values::codec::decode_workflow(bytes)?;
        Ok(Loaded {
            document: StoredDocument::Workflow(document),
            change_count,
            bytes: bytes.len() as u64,
        })
    }

    pub fn decode_schedule(bytes: &[u8]) -> Result<Loaded, String> {
        let (document, change_count) = crate::concrete::values::codec::decode_schedule(bytes)?;
        Ok(Loaded {
            document: StoredDocument::Schedule(document),
            change_count,
            bytes: bytes.len() as u64,
        })
    }

    pub fn encode(document: &StoredDocument) -> Vec<u8> {
        crate::concrete::values::codec::encode(document)
            .expect("a stored document serialises")
    }

    pub fn encode_delta(before: &StoredDocument, after: &StoredDocument) -> (Vec<u8>, usize) {
        crate::concrete::values::codec::encode_delta(before, after)
            .expect("a document delta serialises")
    }
}

/// Under Verus the bytes are stated, never built: serde is absent there.
#[cfg(verus_keep_ghost)]
pub mod codec {
    use crate::concrete::StoredDocument;

    use super::Loaded;

    pub fn decode_workflow(_bytes: &[u8]) -> Result<Loaded, String> {
        unimplemented!()
    }

    pub fn decode_schedule(_bytes: &[u8]) -> Result<Loaded, String> {
        unimplemented!()
    }

    pub fn encode(_document: &crate::concrete::StoredDocument) -> Vec<u8> {
        unimplemented!()
    }

    pub fn encode_delta(
        _before: &crate::concrete::StoredDocument,
        _after: &crate::concrete::StoredDocument,
    ) -> (Vec<u8>, usize) {
        unimplemented!()
    }
}

#[cfg(all(test, not(verus_keep_ghost)))]
mod tests {
    use crate::concrete::{ScheduleDocument, StoredDocument};
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

        let partials = crate::concrete::values::codec::decode_partials::<Schedule>(&bytes).unwrap();
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
        let partials = crate::concrete::values::codec::decode_partials::<Schedule>(&bytes).unwrap();
        assert_eq!(partials.len(), 1);

        let loaded = codec::decode_schedule(&bytes).unwrap();
        let StoredDocument::Schedule(loaded) = loaded.document else {
            panic!("expected schedule document");
        };
        assert_eq!(loaded.schedule, Some(schedule(20)));
        assert_eq!(loaded.version, 7);
    }

    #[test]
    fn decodable_snapshot_without_newline_is_not_an_append_base() {
        let before = document(1, 10, 20);
        let after = document(2, 20, 30);
        let mut bytes = codec::encode(&before);
        assert_eq!(bytes.pop(), Some(b'\n'));
        assert!(codec::decode_schedule(&bytes).is_ok());
        let (delta, _) = codec::encode_delta(&before, &after);
        bytes.extend(delta);
        assert!(codec::decode_schedule(&bytes).is_err());
    }

    #[test]
    fn seeded_saturated_version_delta_cannot_be_folded() {
        let before = document(u64::MAX, 10, 20);
        let after = document(u64::MAX, 20, 30);
        let mut bytes = codec::encode(&before);
        assert!(codec::decode_schedule(&bytes).is_ok());
        let (delta, _) = codec::encode_delta(&before, &after);
        bytes.extend(delta);
        assert!(codec::decode_schedule(&bytes).is_err());
        assert!(codec::decode_schedule(&codec::encode(&after)).is_ok());
    }
}
