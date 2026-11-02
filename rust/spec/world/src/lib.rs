//! The nodes and one store, as a Rover world.
//!
//! The store calls and their answers are `echod_logic`'s. The document
//! catalogue stays in `echod_concrete`. This crate does not define a second
//! store protocol.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

pub mod model;

#[cfg(not(verus_keep_ghost))]
mod rover_model;

#[cfg(not(verus_keep_ghost))]
pub mod refine;

#[cfg(not(verus_keep_ghost))]
pub use refine::abstract_model;
