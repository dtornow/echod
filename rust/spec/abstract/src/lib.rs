//! The complete standalone Resonate model interpreted by Rover.
//!
//! `machine` is the store and its handlers, `model` is one process's step,
//! `view` is the ghost twin, and `trusted` is the maps and the cron engine.

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
mod explore;
mod footprint;
pub mod protocol;
pub mod properties;
pub mod view;

pub use model::Model;
pub use trusted::{PMap, PSet};
pub use echod_types as types;
pub use machine::*;
pub use explore::{plain, IDS, MARKS, SCHEDULES};
pub use footprint::{next_cron, Key};
pub use protocol::{BoundaryEvent, Call, Message, Output};
