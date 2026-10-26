//! The Resonate server protocol as an accordant model, written in Verus.
//!
//! * `exec`: the server as it runs, verified: what each request and each piece
//!   of internal work does, and the safety properties proved about it.
//! * `spec`: the server as mathematics: the `spec fn` twins of `exec`'s
//!   handlers over the state's view, which the trace semantics and the
//!   refinement proofs are stated over.
//! * `collections`: what the spec trusts (persistent maps and sets, string
//!   helpers).
//! * `model`: plain-Rust glue to the checker's `Model`, `Footprint` and
//!   `Partitioned` traits.
//! * `explore`: plain-Rust glue for testing: marks (what a step did) and
//!   suggestions (requests worth trying next).
//!
//! `cargo build` compiles it as ordinary Rust (the proofs erased);
//! `cargo verus verify -p resonate` verifies it.

// Verus specifies `String` (its contents as a sequence), so ids are `&String`;
// and it verifies explicit matches, loops and pushes more readily than the
// idioms these lints suggest.
#![allow(
    clippy::ptr_arg,
    clippy::single_match,
    clippy::collapsible_match,
    clippy::match_like_matches_macro,
    clippy::vec_init_then_push,
    clippy::len_zero
)]

pub mod collections;
mod explore;
mod model;
pub mod exec;
pub mod spec;

pub use collections::{PMap, PSet};
pub use explore::{IDS, MARKS, PLAIN, SCHEDULES};
pub use model::{on, Key};
pub use exec::*;
