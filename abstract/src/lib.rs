//! Independent port of `resonate-specification/spec/{01-protocol,02-abstract}`.
//!
//! The executable layer deliberately uses no crate from the rest of echod.
//! A semantic action only emits effects. Observation bookkeeping
//! (`Invoke`, `Return`, `Receive`, `Clock`) lives in `system` and never calls
//! or changes a handler.

#![cfg_attr(not(verus_keep_ghost), allow(dead_code, unused_imports, unused_variables))]

pub mod external;
pub mod internal;
pub mod promise_spec;
pub mod schedule_spec;
pub mod state;
pub mod system;
pub mod task_spec;
pub mod types;

pub use state::{apply_all, Config, Effect, State, Transition};
pub use system::{
    compose_detached, decompose, handle_external, handle_internal, handle_semantic,
    run_semantic, ExternalAction, InternalAction, Observation, Request, Response,
    SemanticAction,
};
pub use types::*;
