//! Verified refinement from the Echod concrete model to the abstract model.
//!
//! The concrete and abstract crates define their independent mathematical
//! semantics. This crate interprets concrete documents as an abstract store,
//! proves request and internal-work agreement, defines the simulation
//! relation, and discharges the model-specific forward simulation.
//!
//! ```text
//! interpretation.rs  concrete documents interpreted as the abstract store
//! requests.rs        agreement of concrete and abstract request handlers
//! work.rs            agreement of due work and occurrences
//! relation.rs        world invariant and concrete/abstract coupling
//! simulation.rs      forward simulation and `lemma_refines`
//! ```

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]
#![allow(non_shorthand_field_patterns)]

pub mod interpretation;
pub mod requests;
pub mod work;
pub mod relation;
pub mod simulation;

#[cfg(verus_keep_ghost)]
pub use simulation::lemma_refines;
