//! A Rust + Verus Rover world.
//!
//! - [`comm`] contains values shared by specifications and executions.
//! - [`spec`] contains stateful mathematical processes, world semantics, and
//!   refinement.
//! - [`exec`] contains executable realizations, bounded search, and verified
//!   replay.

pub mod comm;
pub mod exec;
pub mod spec;

pub use exec as RoverExec;
pub use spec as RoverSpec;
