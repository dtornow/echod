//! echod-kernel: the Resonate state machine over one document store.
//!
//! The specification is `resonatehq/resonate`, `spec/02-abstract`: a state of
//! objects, schedules and an outbox, one transition per request, and a
//! catalogue of 92 properties every run satisfies. This crate is that machine
//! as executable Rust, with the catalogue as the `ensures` of every step.
//!
//! ```text
//! types.rs       rows, records, requests, responses; abstract twins and views
//! ident.rs       ids and the three trusted string primitives
//! tags.rs        tags: first match wins; otype, timer, target
//! store.rs       State: row vectors whose view is three maps, via the fold
//! properties.rs  the catalogue, transcribed
//! object.rs      projection and the per-object helpers the handlers share
//! external.rs    the 18 request handlers
//! internal.rs    the 6 internal steps
//! ```
//!
//! `./verify.sh` runs Verus; `cargo build` compiles the same sources with the
//! ghost code erased.

pub mod external;
pub mod external_sched;
pub mod external_task;
pub mod external_task2;
pub mod frame;
pub mod ident;
pub mod object;
pub mod properties;
pub mod store;
pub mod tags;
pub mod types;

pub use store::{AState, State};
pub use types::*;
