//! The mathematical Echod concrete model.
//!
//! This crate contains mathematical `*V` state, `spec_*` transitions,
//! passive protocol/store algebra, and its Rover adapter. The verified
//! concrete-to-abstract interpretation and simulation live in
//! `echod-concrete-refinement`. The sole executable concrete document/store
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
//! node.rs             document/node state and transitions
//! store.rs            passive calls/outcomes and the mathematical store step
//! model.rs            the Rover spec: nodes, one store, the initial world, one step
//! ```

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]
#![allow(non_shorthand_field_patterns)]

pub mod node;
pub mod store;
pub mod model;

pub use model::{Proc, Spec};
pub use store::{Etag, Read, StoreCall, StoreError, StoreOutcome};
