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

/// The narrow write-gate projection avoids exposing identifier-bound
/// quantifiers to the commit sequencer.
pub fn validate_for_write(document: &StoredDocument) -> (r: bool)
    ensures
        r == echod_concrete::document::well_formed(document@),
{
    echod_concrete::validate_well_formed(document)
}

pub open spec fn spec_empty_workflow(document: Seq<char>) -> LoadedSpec {
    LoadedSpec {
        document: echod_concrete::node::spec_empty_stored_workflow(document),
        change_count: 0,
        bytes: 0,
        append_certified: false,
    }
}

pub open spec fn spec_empty_schedule(document: Seq<char>) -> LoadedSpec {
    LoadedSpec {
        document: echod_concrete::node::spec_empty_stored_schedule(document),
        change_count: 0,
        bytes: 0,
        append_certified: false,
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
/// before the one that wrote what it read. Inputs beyond the persisted time
/// domain are saturated at its maximum; validated production clocks are
/// unchanged by this totalization.
pub open spec fn spec_clamp_now(committed_at: u64, now: u64) -> u64 {
    let ordered = if committed_at > now { committed_at } else { now };
    if ordered > echod_types::MAX_TIME {
        echod_types::MAX_TIME
    } else {
        ordered
    }
}

pub fn clamp_now(committed_at: u64, now: u64) -> (r: u64)
    ensures
        r == spec_clamp_now(committed_at, now),
{
    let ordered = if committed_at > now { committed_at } else { now };
    if ordered > echod_types::MAX_TIME {
        echod_types::MAX_TIME
    } else {
        ordered
    }
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

/// What serde says the bytes of a workflow object contain, before semantic
/// validation. This boundary deliberately promises no document invariant.
pub uninterp spec fn spec_decode_workflow_raw(bytes: Seq<u8>) -> Result<LoadedSpec, Seq<char>>;
/// The corresponding raw schedule decoder boundary.
pub uninterp spec fn spec_decode_schedule_raw(bytes: Seq<u8>) -> Result<LoadedSpec, Seq<char>>;

/// Reject a structurally decoded value unless it satisfies the complete
/// executable persisted-document predicate.
pub open spec fn spec_validate_decoded(
    decoded: Result<LoadedSpec, Seq<char>>,
) -> Result<LoadedSpec, Seq<char>> {
    match decoded {
        Ok(loaded) if echod_concrete::document::well_formed(loaded.document)
            && echod_concrete::document::document_ids_bounded(
                loaded.document,
            ) =>
            Ok(LoadedSpec {
                append_certified: false,
                ..loaded
            }),
        Ok(_) => Err(Seq::empty()),
        Err(error) => Err(error),
    }
}

/// The decoder visible to handlers is always semantically gated.
pub open spec fn spec_decode_workflow(
    bytes: Seq<u8>,
) -> Result<LoadedSpec, Seq<char>> {
    spec_validate_decoded(spec_decode_workflow_raw(bytes))
}

/// The schedule decoder visible to handlers is always semantically gated.
pub open spec fn spec_decode_schedule(
    bytes: Seq<u8>,
) -> Result<LoadedSpec, Seq<char>> {
    spec_validate_decoded(spec_decode_schedule_raw(bytes))
}

pub proof fn lemma_workflow_decode_success_is_well_formed(
    bytes: Seq<u8>,
    loaded: LoadedSpec,
)
    requires
        spec_decode_workflow(bytes) == Ok(loaded),
    ensures
        !loaded.append_certified,
        echod_concrete::document::well_formed(loaded.document),
        echod_concrete::document::document_ids_bounded(loaded.document),
{
}

pub proof fn lemma_schedule_decode_success_is_well_formed(
    bytes: Seq<u8>,
    loaded: LoadedSpec,
)
    requires
        spec_decode_schedule(bytes) == Ok(loaded),
    ensures
        !loaded.append_certified,
        echod_concrete::document::well_formed(loaded.document),
        echod_concrete::document::document_ids_bounded(loaded.document),
{
}

pub open spec fn loaded_workflow_has_identity(
    loaded: LoadedSpec,
    origin: Seq<char>,
) -> bool {
    match loaded.document {
        echod_concrete::node::StoredDocumentV::Workflow(workflow) =>
            workflow.document == origin,
        _ => false,
    }
}

pub open spec fn loaded_schedule_has_identity(
    loaded: LoadedSpec,
    id: Seq<char>,
) -> bool {
    match loaded.document {
        echod_concrete::node::StoredDocumentV::Schedule(schedule) =>
            schedule.document == id,
        _ => false,
    }
}

pub open spec fn spec_validate_workflow_identity(
    loaded: LoadedSpec,
    origin: Seq<char>,
) -> Result<LoadedSpec, Seq<char>> {
    if loaded_workflow_has_identity(loaded, origin) {
        Ok(loaded)
    } else {
        Err(Seq::empty())
    }
}

pub open spec fn spec_validate_schedule_identity(
    loaded: LoadedSpec,
    id: Seq<char>,
) -> Result<LoadedSpec, Seq<char>> {
    if loaded_schedule_has_identity(loaded, id) {
        Ok(loaded)
    } else {
        Err(Seq::empty())
    }
}

/// One compacted partial containing the complete document.
pub uninterp spec fn spec_encode(document: echod_concrete::node::StoredDocumentV) -> Seq<u8>;
/// One partial containing the changes from `before` to `after`, and how many
/// changes that is.
pub uninterp spec fn spec_encode_delta(
    before: echod_concrete::node::StoredDocumentV,
    after: echod_concrete::node::StoredDocumentV,
) -> (Seq<u8>, usize);

pub open spec fn spec_full_store_body_representable(
    document: echod_concrete::node::StoredDocumentV,
) -> bool {
    spec_encode(document).len() <= usize::MAX as int
}

pub open spec fn spec_delta_store_body_representable(
    before: echod_concrete::node::StoredDocumentV,
    after: echod_concrete::node::StoredDocumentV,
) -> bool {
    spec_encode_delta(before, after).0.len() <= usize::MAX as int
}

pub proof fn lemma_unrepresentable_full_store_body_rejected(
    state: crate::state::S,
    key: Seq<char>,
    document: echod_concrete::node::StoredDocumentV,
    owner: crate::state::Owner,
)
    requires
        !spec_full_store_body_representable(document),
    ensures
        crate::state::spec_store(
            state,
            echod_concrete::store::StoreReqSpec::PutIfNoneMatch {
                key,
                body: spec_encode(document),
            },
            owner,
        ) == (state, None),
{
    crate::state::lemma_unrepresentable_store_request_stutters(
        state,
        echod_concrete::store::StoreReqSpec::PutIfNoneMatch {
            key,
            body: spec_encode(document),
        },
        owner,
    );
}

pub proof fn lemma_unrepresentable_delta_store_body_rejected(
    state: crate::state::S,
    key: Seq<char>,
    etag: echod_concrete::store::EtagSpec,
    before: echod_concrete::node::StoredDocumentV,
    after: echod_concrete::node::StoredDocumentV,
    owner: crate::state::Owner,
)
    requires
        !spec_delta_store_body_representable(before, after),
    ensures
        crate::state::spec_store(
            state,
            echod_concrete::store::StoreReqSpec::AppIfMatch {
                key,
                offset: 0,
                body: spec_encode_delta(before, after).0,
                etag,
            },
            owner,
        ) == (state, None),
{
    crate::state::lemma_unrepresentable_store_request_stutters(
        state,
        echod_concrete::store::StoreReqSpec::AppIfMatch {
            key,
            offset: 0,
            body: spec_encode_delta(before, after).0,
            etag,
        },
        owner,
    );
}

pub assume_specification [codec::decode_workflow](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_workflow_raw(bytes@);

pub assume_specification [codec::decode_schedule](bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_schedule_raw(bytes@);

pub assume_specification [codec::encode](document: &StoredDocument) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode(document@);

pub assume_specification [codec::encode_delta](before: &StoredDocument, after: &StoredDocument) -> (r: (Vec<u8>, usize))
    ensures
        (r.0@, r.1) == spec_encode_delta(before@, after@);

pub fn decode_workflow(bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_workflow(bytes@),
        r is Ok ==> !r->Ok_0@.append_certified,
        r is Ok ==> echod_concrete::document::well_formed(r->Ok_0@.document),
        r is Ok ==> echod_concrete::document::document_ids_bounded(
            r->Ok_0@.document,
        ),
{
    match codec::decode_workflow(bytes) {
        Ok(mut loaded) => {
            loaded.append_certified = false;
            if echod_concrete::validate_loaded_well_formed(&loaded) {
                Ok(loaded)
            } else {
                Err(String::new())
            }
        },
        Err(error) => Err(error),
    }
}

pub fn decode_schedule(bytes: &[u8]) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view() == spec_decode_schedule(bytes@),
        r is Ok ==> !r->Ok_0@.append_certified,
        r is Ok ==> echod_concrete::document::well_formed(r->Ok_0@.document),
        r is Ok ==> echod_concrete::document::document_ids_bounded(
            r->Ok_0@.document,
        ),
{
    match codec::decode_schedule(bytes) {
        Ok(mut loaded) => {
            loaded.append_certified = false;
            if echod_concrete::validate_loaded_well_formed(&loaded) {
                Ok(loaded)
            } else {
                Err(String::new())
            }
        },
        Err(error) => Err(error),
    }
}

pub fn workflow_identity_matches(
    loaded: &Loaded,
    origin: &str,
) -> (r: bool)
    ensures
        r == loaded_workflow_has_identity(loaded.deep_view(), origin@),
{
    proof {
        echod_concrete::lemma_stored_document_view(&loaded.document);
        echod_concrete::lemma_stored_document_identity_view(
            &loaded.document,
        );
    }
    match &loaded.document {
        StoredDocument::Workflow(workflow) =>
            crate::verified::node::str_eq(
                workflow.document.as_str(),
                origin,
            ),
        StoredDocument::Schedule(_) => false,
    }
}

pub fn validate_workflow_identity(
    loaded: Loaded,
    origin: &str,
) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view()
            == spec_validate_workflow_identity(
                loaded.deep_view(),
                origin@,
            ),
{
    if workflow_identity_matches(&loaded, origin) {
        Ok(loaded)
    } else {
        Err(String::new())
    }
}

pub fn schedule_identity_matches(
    loaded: &Loaded,
    id: &str,
) -> (r: bool)
    ensures
        r == loaded_schedule_has_identity(loaded.deep_view(), id@),
{
    proof {
        echod_concrete::lemma_stored_document_view(&loaded.document);
        echod_concrete::lemma_stored_document_identity_view(
            &loaded.document,
        );
    }
    match &loaded.document {
        StoredDocument::Schedule(schedule) =>
            crate::verified::node::str_eq(
                schedule.document.as_str(),
                id,
            ),
        StoredDocument::Workflow(_) => false,
    }
}

pub fn validate_schedule_identity(
    loaded: Loaded,
    id: &str,
) -> (r: Result<Loaded, String>)
    ensures
        r.deep_view()
            == spec_validate_schedule_identity(
                loaded.deep_view(),
                id@,
            ),
{
    if schedule_identity_matches(&loaded, id) {
        Ok(loaded)
    } else {
        Err(String::new())
    }
}

pub fn encode(document: &StoredDocument) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode(document@),
        spec_full_store_body_representable(document@),
{
    let r = codec::encode(document);
    assert(r@.len() == r.len());
    r
}

pub fn encode_delta(before: &StoredDocument, after: &StoredDocument) -> (r: (Vec<u8>, usize))
    ensures
        (r.0@, r.1) == spec_encode_delta(before@, after@),
        spec_delta_store_body_representable(before@, after@),
{
    let r = codec::encode_delta(before, after);
    assert(r.0@.len() == r.0.len());
    r
}

} // verus!

/// Plain Rust delegates to the shared document codec stated above.
#[cfg(not(verus_keep_ghost))]
pub mod codec {
    use echod_concrete::StoredDocument;

    use super::Loaded;

    pub use echod_concrete::document::{promises, Promise, Task};

    pub fn decode_workflow(bytes: &[u8]) -> Result<Loaded, String> {
        let Some(encoded) = bytes.strip_prefix(b"W\n") else {
            return Err("stored document is not a workflow".to_string());
        };
        let (document, change_count) =
            echod_concrete::document::codec::decode_workflow(encoded)?;
        Ok(Loaded {
            document: StoredDocument::Workflow(document),
            change_count,
            bytes: bytes.len() as u64,
            append_certified: false,
        })
    }

    pub fn decode_schedule(bytes: &[u8]) -> Result<Loaded, String> {
        let Some(encoded) = bytes.strip_prefix(b"S\n") else {
            return Err("stored document is not a schedule".to_string());
        };
        let (document, change_count) =
            echod_concrete::document::codec::decode_schedule(encoded)?;
        Ok(Loaded {
            document: StoredDocument::Schedule(document),
            change_count,
            bytes: bytes.len() as u64,
            append_certified: false,
        })
    }

    pub fn encode(document: &StoredDocument) -> Vec<u8> {
        let mut encoded = match document {
            StoredDocument::Workflow(_) => b"W\n".to_vec(),
            StoredDocument::Schedule(_) => b"S\n".to_vec(),
        };
        encoded.extend(
            echod_concrete::document::codec::encode(document)
                .expect("a stored document serialises"),
        );
        encoded
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
    use echod_concrete::{Objects, ScheduleDocument, StoredDocument, WorkflowDocument};
    use echod_types::{Schedule, Value};

    use super::{
        codec, decode_schedule, decode_workflow,
        validate_schedule_identity, validate_workflow_identity,
    };

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

        let partials =
            echod_concrete::document::codec::decode_partials::<Schedule>(
                &bytes[2..],
            ).unwrap();
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
        let partials =
            echod_concrete::document::codec::decode_partials::<Schedule>(
                &bytes[2..],
            ).unwrap();
        assert_eq!(partials.len(), 1);

        let loaded = codec::decode_schedule(&bytes).unwrap();
        let StoredDocument::Schedule(loaded) = loaded.document else {
            panic!("expected schedule document");
        };
        assert_eq!(loaded.schedule, Some(schedule(20)));
        assert_eq!(loaded.version, 7);
    }

    #[test]
    fn handler_facing_decoder_rejects_semantically_invalid_document() {
        let invalid = StoredDocument::Workflow(WorkflowDocument {
            document: "wf".to_string(),
            version: 1,
            committed_at: echod_types::MAX_TIME + 1,
            next_wake_at: None,
            objects: Objects::empty(),
        });

        let bytes = codec::encode(&invalid);
        assert!(codec::decode_workflow(&bytes).is_ok());
        assert!(decode_workflow(&bytes).is_err());
    }

    #[test]
    fn workflow_identity_validation_rejects_swapped_origin() {
        let document = StoredDocument::Workflow(WorkflowDocument {
            document: "workflow-b".to_string(),
            version: 1,
            committed_at: 1,
            next_wake_at: None,
            objects: Objects::empty(),
        });
        let bytes = codec::encode(&document);
        let loaded = decode_workflow(&bytes).unwrap();
        assert!(validate_workflow_identity(
            loaded,
            "workflow-a",
        ).is_err());
    }

    #[test]
    fn schedule_identity_validation_rejects_swapped_id() {
        let document = StoredDocument::Schedule(ScheduleDocument {
            document: "schedule-b".to_string(),
            version: 1,
            committed_at: 1,
            next_wake_at: None,
            schedule: None,
        });
        let bytes = codec::encode(&document);
        let loaded = decode_schedule(&bytes).unwrap();
        assert!(validate_schedule_identity(
            loaded,
            "schedule-a",
        ).is_err());
    }

    #[test]
    fn workflow_bytes_are_rejected_by_schedule_loader() {
        let document = StoredDocument::Workflow(WorkflowDocument {
            document: "workflow".to_string(),
            version: 1,
            committed_at: 1,
            next_wake_at: None,
            objects: Objects::empty(),
        });
        let bytes = codec::encode(&document);
        assert!(decode_schedule(&bytes).is_err());
    }

    #[test]
    fn schedule_bytes_are_rejected_by_workflow_loader() {
        let document = StoredDocument::Schedule(ScheduleDocument {
            document: "schedule".to_string(),
            version: 1,
            committed_at: 1,
            next_wake_at: None,
            schedule: None,
        });
        let bytes = codec::encode(&document);
        assert!(decode_workflow(&bytes).is_err());
    }
}
