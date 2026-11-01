//! The concrete specification.
//!
//! The catalogue, the handler specifications, and the step `on_event` is
//! proved against live here. The kernel depends on this crate: a handler's
//! `ensures` names `spec_promise_create` and the other `spec_*` functions.
//! This crate depends on the abstract model, and on neither the kernel nor
//! the process.
//!
//! ```text
//! types.rs            rows, records, requests; the twins, derived
//! tags.rs             tags: first match wins; otype, timer, target
//! state.rs            the document as three maps, and the fold that makes them
//! object.rs           projection and the per-object edits the handlers share
//! properties.rs       the catalogue, transcribed
//! spec.rs             the handlers as functions of that document
//! internal_spec.rs    the sweep, as functions of that document
//! on_event.rs         the one step a node takes
//! refine.rs           the abstract model this step refines
//! ```

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

pub mod external_proof;
pub mod internal_spec;
pub mod object;
pub mod object_proof;
pub mod on_event;
pub mod properties;
pub mod properties_proof;
pub mod spec;
pub mod state;
pub mod tags;
pub mod tags_proof;
pub mod types;

#[cfg(not(verus_keep_ghost))]
pub mod refine;

#[cfg(not(verus_keep_ghost))]
pub use refine::abstract_server;

pub use types::*;
