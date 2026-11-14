//! Standalone mathematical Resonate model interpreted by Rover.
//!
//! `state.rs` contains state, request, and internal-work transitions;
//! `rover.rs` contains process orchestration and the Rover adapter.
//! Property claims and proofs remain separate.

#![allow(
    clippy::ptr_arg,
    clippy::single_match,
    clippy::collapsible_match,
    clippy::match_like_matches_macro,
    clippy::vec_init_then_push,
    clippy::len_zero,
    non_shorthand_field_patterns
)]

pub mod state;
pub mod rover;
pub mod property_claim;
#[cfg(verus_keep_ghost)]
mod property_proof;
pub mod axioms;

pub use state::Config;
pub use rover::{Proc, Spec};
pub use echod_types as types;
#[cfg(verus_keep_ghost)]
pub use property_proof::property_proof;
