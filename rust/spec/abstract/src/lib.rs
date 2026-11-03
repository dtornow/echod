//! The complete standalone Resonate model interpreted by Rover.
//!
//! The protocol, the executable handlers, exploration hints, and the abstract
//! process all live here.

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

pub use abstract_model::Model;
pub use collections::{PMap, PSet};
pub use echod_types as types;
pub use exec::*;
pub use explore::{plain, IDS, MARKS, SCHEDULES};
pub use model::{next_cron, Key};
pub use protocol::{BoundaryEvent, Call, Message, Output};
