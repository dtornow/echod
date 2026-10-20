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
//! tla/            the temporal logic, vendored from Anvil's verus-tla
//! node/core.rs    the node: executable, with its specification, step for step
//! spec/cluster.rs the state and the actions; a node's are the core's spec functions
//! proof/safety.rs the invariant and its induction
//! ```
//!
//! What is proved (`proof/safety.rs`): under bounded clock skew, two nodes
//! never both act as owner of one origin, and a node that answers from its
//! cache answers from the bucket's current document.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

pub mod node;
#[cfg(verus_keep_ghost)]
pub mod proof;
#[cfg(verus_keep_ghost)]
pub mod spec;
pub mod tla;
