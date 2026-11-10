//! The mathematical Echod concrete model.
//!
//! This crate contains mathematical `*V` state, `spec_*` transitions,
//! passive protocol/store algebra, and the relation, simulation, and
//! refinement proofs. The sole executable concrete document/store
//! implementation lives in `echod-process::concrete`.
//!
//! A world is the nodes and one store. Each node keeps its own documents
//! and takes one flight at a time. The abstract model is a separate machine.
//!
//! ```text
//! node.rs             document/node state and transitions
//! store.rs            passive calls/outcomes and the mathematical store step
//! model.rs            the Rover spec: nodes, one store, the initial world, one step
//! interpret.rs        the documents read as the abstract store; the promise handlers agree
//! handlers.rs         the remaining request handlers agree
//! timers.rs           the due step and the occurrence agree; `lemma_agreement`
//! relation.rs         the invariant, the simulation relation, and agreement
//! simulation.rs       the forward simulation and `lemma_refines`
//! ```

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]
#![allow(non_shorthand_field_patterns)]

pub mod node;
pub mod store;
pub mod model;
pub mod interpret;
pub mod handlers;
pub mod timers;
pub mod relation;
pub mod simulation;

pub use model::{Proc, Spec};
pub use store::{Etag, Read, StoreCall, StoreError, StoreOutcome};
