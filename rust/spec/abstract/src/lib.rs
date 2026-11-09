//! The complete standalone Resonate model interpreted by Rover.
//!
//! `machine` is the store and handlers; `model` adapts one service process to
//! Rover; `view` holds mathematical views and their lemmas; `catalogue` states
//! conformance properties; `trusted` contains the explicit trust boundary.
//! `model::Spec` implements `RoverSpec::Spec`; `RoverSpec::State<model::Spec>`
//! is the complete mathematical state.

#![allow(
    clippy::ptr_arg,
    clippy::single_match,
    clippy::collapsible_match,
    clippy::match_like_matches_macro,
    clippy::vec_init_then_push,
    clippy::len_zero,
    non_shorthand_field_patterns
)]

pub mod model;
pub mod trusted;
pub mod machine;
mod hashed_map;
pub mod protocol;
pub mod catalogue;
pub mod view;

pub use model::Spec;
pub use trusted::{PMap, PSet};
pub use echod_types as types;
pub use machine::*;
pub use protocol::{BoundaryEvent, Call, Message, Output};
