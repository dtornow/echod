//! The mathematical Echod concrete model.
//!
//! This crate contains mathematical `*V` state, `spec_*` transitions,
//! passive protocol/store algebra, and its Rover adapter. The verified
//! concrete-to-abstract interpretation and simulation live in
//! `echod-refinement`. The sole executable concrete document/store
//! implementation lives in `echod-process::concrete`.
//! `echod-abstract-spec` remains a semantic dependency because the concrete
//! Rover boundary uses its `Call`/`Output`/`Dispatch` protocol types and
//! schedule transitions use its trusted cron and occurrence-expansion
//! functions.
//!
//! A world is the nodes and one store. Each node keeps its own documents
//! and takes one flight at a time.
//!
//! ```text
//! state.rs            node and store state, protocol algebra, and transitions
//! rover.rs            the Rover spec: nodes, one store, the initial world, one step
//! property_claim.rs   concrete integrity statements
//! property_proof.rs   their machine-checked proofs
//! ```

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]
#![allow(non_shorthand_field_patterns)]

pub mod state;
pub mod document;
pub mod request_claim;
pub mod effects_claim;
#[cfg(verus_keep_ghost)]
mod document_proof;
pub mod rover;
pub mod property_claim;
#[cfg(verus_keep_ghost)]
mod property_proof;

pub use rover::{Config, Proc, Spec};
pub use state::{Etag, Read, StoreReq, StoreError, StoreRes};
#[cfg(verus_keep_ghost)]
pub use property_proof::property_proof;
