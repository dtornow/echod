//! Standalone mathematical Resonate model interpreted by Rover.

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
pub mod protocol;
pub mod requests;
pub mod work;
pub mod rover;
pub mod catalogue;
pub mod axioms;

pub use state::Config;
pub use rover::{Proc, Spec};
pub use protocol::{BoundaryEvent, Call, Dispatch, Message, Output};
pub use echod_types as types;
