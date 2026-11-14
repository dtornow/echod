//! Executable concrete documents and store.

pub mod document;
pub mod values;
pub mod rover;
pub mod runtime;
pub mod store;

pub use values::{
    DocumentBody, LoadedDocument, Obj, Objects, Prom, ScheduleDocument, StoredDocument, Tk,
    WorkflowDocument,
};

#[cfg(verus_keep_ghost)]
pub use document::{lemma_doc_view, lemma_obj_view, lemma_outbound_view, lemma_pending_view};
pub use document::{
    advance_stored, body_deadline, body_len, clone_body, clone_stored, create_occurrence, empty_body,
    empty_schedule, empty_stored_schedule, empty_stored_workflow, empty_workflow, handle,
    keys_within, peek, request_transition, run_due, same_body, stored_body, stored_committed_at,
    stored_is_workflow, stored_next_wake_at, stored_version, sweep, Outbound, Pending,
};
pub use store::{content_etag, fnv1a, Etag, Read, StoreError, StoreReq, StoreRes};

#[cfg(test)]
mod world_tests;
#[cfg(test)]
mod request_tests;
