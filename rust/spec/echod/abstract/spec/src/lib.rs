//! The complete standalone Resonate model interpreted by Rover.
//!
//! `machine` is the transition relation; `model` adapts one mathematical
//! service process to Rover; `view` holds mathematical views and their lemmas;
//! `catalogue` states conformance properties; `trusted` contains the explicit
//! axiomatic boundary. Executable realizations live in
//! `echod-abstract-exec`.
//! [`Spec`] implements `RoverSpec::Spec`;
//! `RoverSpec::State<Spec>` is the complete mathematical
//! state.

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
pub mod protocol;
pub mod catalogue;
pub mod view;

pub use machine::Config;
pub use model::{Proc, Spec};
pub use echod_types as types;
pub use machine::Dispatch;
pub use protocol::{BoundaryEvent, Call, Message, Output};
