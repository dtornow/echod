//! The concrete Rover model.
//!
//! A world is the nodes and one store. Each node keeps its own documents
//! and takes one flight at a time. The abstract model is a separate machine.
//! This crate does not import its handlers. The document machine of `node.rs`
//! (`handle`, `fire_schedule`, `sweep`, `create_occurrence`) is the one the process
//! runs: each is proved equal to its specification here, and the process
//! wraps it in flights and commits. Refinement of this model to the abstract
//! one is `simulation`: the relation, the injected call, the observed output,
//! the shed and the empty heartbeat.
//!
//! Each file of the model holds the executable code and, below it, the same
//! step as a specification (`spec_*`, over the view types `*V`). The proof
//! files read the specifications.
//!
//! ```text
//! document.rs         persisted values; partial apply/fold/compose and their algebra
//! node.rs             one node: its documents, one flight, the handlers, the due step
//! store.rs            the store: its calls and their answers, one call applied
//! model.rs            the Rover model: nodes, one store, the initial world, one step
//! interpret.rs        the documents read as the abstract store; the promise handlers agree
//! handlers.rs         the remaining request handlers agree
//! timers.rs           the due step and the occurrence agree; `lemma_agreement`
//! relation.rs         the invariant, the simulation relation, and agreement
//! simulation.rs       the forward simulation and `lemma_refines`
//! refine.rs           the same statement, for the executable crate
//! ```

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]
#![allow(non_shorthand_field_patterns)]

pub mod document;
pub mod effects;
pub mod quick_n_dirty;
pub mod node;
pub mod store;
pub mod model;
pub mod interpret;
pub mod handlers;
pub mod timers;
pub mod relation;
pub mod simulation;

#[cfg(not(verus_keep_ghost))]
pub mod refine;

#[cfg(not(verus_keep_ghost))]
pub use refine::abstract_model;

pub use echod_types::*;
pub use document::{
    DocumentBody, LoadedDocument, Obj, Objects, Prom, ScheduleDocument, StoredDocument, Tk,
    WorkflowDocument,
};
pub use model::Model;
#[cfg(verus_keep_ghost)]
pub use node::{lemma_doc_view, lemma_obj_view, lemma_outbound_view, lemma_pending_view};
pub use node::{
    advance_stored, body_deadline, body_len, clone_body, clone_stored, create_occurrence, empty_body,
    empty_schedule, empty_stored_schedule, empty_stored_workflow, empty_workflow, fire_schedule,
    handle, keys_within, occurrence_transition, peek, request_transition, same_body, stored_body,
    stored_committed_at, stored_is_workflow, stored_next_wake_at, stored_version, sweep, Outbound,
    Pending,
};
pub use store::{content_etag, fnv1a, Etag, Read, StoreError, StoreReq, StoreRes};
