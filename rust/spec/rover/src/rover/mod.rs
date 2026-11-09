//! A Rust + Verus Rover world.
//!
//! - [`comm`] contains values shared by specifications and executable tests.
//! - [`spec`] contains stateful mathematical processes, world semantics, and
//!   refinement.
//! - [`test`] contains executable realizations, bounded search, and verified
//!   replay.

pub mod comm;
pub mod spec;
pub mod test;
