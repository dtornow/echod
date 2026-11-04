//! The document the process proves its handlers against.
//!
//! A promise, its task, and a schedule are rows. The handlers are functions
//! of those rows. This crate is the specification those `ensures` name. The
//! abstract model and the concrete model do not import it: each is its own
//! machine, and a refinement proof is what relates them.

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]

pub mod commit_spec;
pub mod external_proof;
pub mod fold_proof;
pub mod internal_proof;
pub mod internal_spec;
pub mod node_spec;
pub mod object;
pub mod object_proof;
pub mod on_event;
pub mod properties;
pub mod properties_proof;
pub mod spec;
pub mod state;
pub mod steps_spec;
pub mod tags;
pub mod tags_proof;
pub mod timeouts;
pub mod types;
