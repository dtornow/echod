//! The concrete Rover model.
//!
//! A world is the nodes and one store. Each node keeps its own documents
//! and takes one flight at a time. The abstract model is a separate machine.
//! This crate does not import its handlers, and the document specifications
//! the process proves against live in `echod-document`. Refinement of this
//! model to the abstract one is `simulation`: the relation, the injected call,
//! the observed output, the shed and the empty heartbeat, and the process
//! step that still has to be matched.
//!
//! Each file of the model holds the executable code and, below it, the same
//! step as a specification (`spec_*`, over the view types `*V`). The proof
//! files read the specifications.
//!
//! ```text
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
pub use model::Model;
pub use store::{content_etag, fnv1a, Etag, Read, StoreCall, StoreError, StoreOutcome};
