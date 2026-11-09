//! A Rust + Verus Rover world.
//!
//! - [`comm`] contains values shared by specifications and executions.
//! - [`spec`] contains stateful mathematical processes, world semantics, and
//!   refinement.

pub mod comm;
pub mod spec;

pub use spec as RoverSpec;
