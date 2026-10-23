//! echod-kernel: the Resonate state machine over one document store.
//!
//! The specification is `resonatehq/resonate`, `spec/02-abstract`: a state of
//! objects, schedules and an outbox, one transition per request, and a
//! catalogue of 92 properties every run satisfies. This crate is that machine
//! as executable Rust, with the catalogue as the `ensures` of every step.
//!
//! ```text
//! types.rs       rows, records, requests, responses, ids; the twins, derived; the trusted string primitives
//! tags.rs        tags: first match wins; otype, timer, target
//! tags_proof.rs  what `get` returns
//! store.rs       State: row vectors whose view is three maps, via the fold
//! store_proof.rs  the fold lemmas and the row readers
//! properties.rs  the catalogue, transcribed
//! properties_proof.rs  its theorems: the frame every step ends with, the folds
//! object.rs      projection and the per-object helpers the handlers share
//! object_proof.rs  its two lemmas on `without`
//! external.rs    the 18 request handlers, each a function of the abstract state; `handle` over `Request`
//! external_proof.rs  their lemmas: one per handler, and the projection and frame lemmas they share
//! internal.rs    the 6 internal steps
//! internal_proof.rs  their lemmas
//! steps.rs       what a node runs around a request: sweep, drain, next_deadline, clamp_now, schedule_due
//! node.rs        what a node remembers and decides: membership, cache versions, armed keys; step for step with its spec
//! commit.rs      the commit's decisions: which key to arm before the write, which to remove after, which to remember
//! ```
//!
//! The first group is the specification's machine, one document at a
//! time. The last three are this design's: a node over a bucket, verified
//! the same way, and what `echod-system` defines a node's actions as.
//!
//! `./verify.sh` runs Verus; `cargo build` compiles the same sources with the
//! ghost code erased.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

pub mod commit;
pub mod external;
pub mod external_proof;
pub mod internal;
pub mod internal_proof;
pub mod node;
pub mod object;
pub mod object_proof;
pub mod properties;
pub mod properties_proof;
pub mod store;
pub mod steps;
pub mod store_proof;
pub mod tags;
pub mod tags_proof;
pub mod types;

pub use store::*;
pub use types::*;
