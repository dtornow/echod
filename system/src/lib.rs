//! echod-system: the whole system as a state machine, and its theorems.
//! Proof only: nothing in this crate runs.
//!
//! The kernel proves one document's transitions and one node's decisions.
//! This crate is the layer above: several nodes over one bucket, each with
//! its own clock, cache and view of the membership, under crashes and
//! joins. It is written the way Anvil writes a cluster — a state, actions
//! with preconditions and transitions, `init` and `next` — so that the TLA
//! embedding (`tla/`) can state safety as `always(inv)` and, later,
//! liveness as `leads_to`. A node's actions are defined as the kernel's
//! `node`, `commit` and `steps` functions, so the theorems are about the
//! code `echod-logic` runs.
//!
//! ```text
//! model.rs      the state and the nine actions; requests enter through the kernel's `spec_handle`
//! theorems.rs   the invariant, one lemma per action, the four theorems
//! tla/          the temporal logic, vendored from Anvil's verus-tla
//! ```
//!
//! What is proved (`theorems.rs`), with nothing assumed of any clock:
//! every document in the bucket satisfies the kernel's catalogue; every
//! deadline in every document has a key in the bucket at or before it; a
//! cached body whose version the bucket still holds is the bucket's document;
//! and every occurrence a schedule has fired has its promise in the bucket.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

#[cfg(verus_keep_ghost)]
pub mod model;
#[cfg(verus_keep_ghost)]
pub mod theorems;
pub mod tla;
