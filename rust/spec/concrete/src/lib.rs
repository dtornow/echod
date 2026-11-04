//! The concrete Rover model.
//!
//! A world is the nodes and one store. Each node keeps its own documents
//! and takes one flight at a time. The abstract model is a separate machine.
//! This crate does not import its handlers, and the document specifications
//! the process proves against live in `echod-document`. Refinement of this
//! model to the abstract one is stated in `refine` and is not proved yet.
//!
//! ```text
//! plane.rs            one node: its documents, one flight, the store round trip
//! model.rs            the Rover model: nodes, one store, the initial world
//! rover_model.rs      RoverModel for that world
//! refine.rs           the statement against the abstract Rover model
//! store.rs            store calls and their answers
//! ```

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]

pub mod model;
mod plane;
pub mod store;

#[cfg(not(verus_keep_ghost))]
mod rover_model;

#[cfg(not(verus_keep_ghost))]
pub mod refine;

#[cfg(not(verus_keep_ghost))]
pub use refine::abstract_model;

pub use echod_types::*;
pub use model::Model;
pub use store::{content_etag, fnv1a, Etag, Read, StoreCall, StoreError, StoreOutcome};
