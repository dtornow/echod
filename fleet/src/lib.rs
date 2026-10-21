//! echod-fleet: the multi-node system as a state machine, and its proof.
//!
//! The kernel proves one origin's transitions. This crate is the layer above:
//! several nodes over one bucket, each with its own clock, cache and view of
//! the membership, under crashes and joins. It is written the way Anvil
//! writes a cluster — a state, actions with preconditions and transitions,
//! `init` and `next` — so that the TLA embedding (`tla/`) can state safety
//! as `always(inv)` and, later, liveness as `leads_to`.
//!
//! ```text
//! node.rs           the node core: executable, with its specification, step for step
//! txn.rs            the commit's decisions, the same way
//! step.rs           sweep, drain, next_deadline, clamp_now: verified over the kernel
//! cluster.rs        the state and the nine actions; requests enter through the kernel's `spec_handle`
//! cluster_proof.rs  the invariant, one lemma per action, the four theorems
//! tla/              the temporal logic, vendored from Anvil's verus-tla
//! ```
//!
//! What is proved (`cluster_proof.rs`), with nothing assumed of any clock:
//! every document in the bucket satisfies the kernel's catalogue; every
//! deadline in every document has a key in the bucket at or before it; a
//! cached body whose version the bucket still holds is the bucket's document;
//! and every occurrence a schedule has fired has its promise in the bucket.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

#[cfg(verus_keep_ghost)]
pub mod cluster;
#[cfg(verus_keep_ghost)]
pub mod cluster_proof;
pub mod node;
pub mod step;
pub mod tla;
pub mod txn;
