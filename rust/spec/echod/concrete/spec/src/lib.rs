//! The mathematical Echod concrete model.
//!
//! This crate contains mathematical `*V` state, `spec_*` transitions,
//! passive protocol/store algebra, and its Rover adapter. The verified
//! concrete-to-abstract interpretation and simulation live in
//! `echod-refinement`. The sole executable concrete document/store
//! implementation lives in `echod-process::concrete`.
//! Shared payloads and trusted mathematical declarations live in
//! `echod-types::{protocol, common}`. Neither this crate nor the executable
//! process depends on the abstract model.
//!
//! A world is the nodes and one store. Each node keeps its own documents
//! and takes one flight at a time.
//!
//! ```text
//! state.rs            node, store and document structures
//! handler.rs          node/store dispatch and transitions, document algebra
//! rover.rs            the Rover wiring, initial world and observation
//! property_claim.rs   concrete integrity statements
//! property_proof.rs   their machine-checked proofs
//! ```

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]
#![allow(non_shorthand_field_patterns)]

pub mod state;
#[cfg(verus_keep_ghost)]
pub mod handler;
pub mod rover;
#[cfg(verus_keep_ghost)]
pub mod property_claim;
#[cfg(verus_keep_ghost)]
pub mod property_proof;
#[cfg(verus_keep_ghost)]
pub mod codec_algebra;

pub use rover::{Config, Spec};
pub use state::Proc;
pub use state::{Etag, Read, StoreReq, StoreError, StoreRes};
#[cfg(verus_keep_ghost)]
pub use property_proof::property_proof;
