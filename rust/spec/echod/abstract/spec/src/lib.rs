//! Standalone mathematical Resonate model interpreted by Rover.
//!
//! `state.rs` contains state structures; `handler.rs` contains transitions.
//! `rover.rs` contains initialization, observation and thin event delegation.
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
#[cfg(verus_keep_ghost)]
pub mod handler;
pub mod rover;
#[cfg(verus_keep_ghost)]
pub mod property_claim;
#[cfg(verus_keep_ghost)]
pub mod property_proof;
pub mod axioms;

pub use rover::Config;
pub use rover::Spec;
pub use state::Proc;
pub use echod_types as types;
#[cfg(verus_keep_ghost)]
pub use property_proof::property_proof;
