//! The complete standalone Resonate model interpreted by Rover.
//!
//! The protocol, executable handlers, mathematical twins, exploration hints,
//! and abstract process all live here.

#![allow(
    clippy::ptr_arg,
    clippy::single_match,
    clippy::collapsible_match,
    clippy::match_like_matches_macro,
    clippy::vec_init_then_push,
    clippy::len_zero,
    non_shorthand_field_patterns
)]

pub mod abstract_model;
pub mod collections;
pub mod exec;
mod explore;
mod model;
pub mod protocol;
pub mod properties;
pub mod spec;

pub use collections::{PMap, PSet};
pub use exec::*;
pub use explore::{IDS, MARKS, PLAIN, SCHEDULES};
pub use model::{on, Key};
pub use protocol::{BoundaryEvent, Call, Message, Output};
