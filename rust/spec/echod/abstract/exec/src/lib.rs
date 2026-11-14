//! Executable realization of `echod_abstract_spec`.

#![allow(non_shorthand_field_patterns)]

pub mod state;
pub mod requests;
pub mod work;
pub mod rover;
pub mod projection;
pub mod collections;
pub mod runtime;
pub mod coverage;

pub use echod_abstract_spec::Config;
pub use rover::{Proc, Spec};

#[cfg(test)]
mod protocol_bounds_tests;
