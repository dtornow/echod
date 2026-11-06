//! The proved half of the process's own bookkeeping: what a node decides
//! about the membership, its cache, and the deadline keys it armed, and
//! which key a commit arms, removes, and remembers. Each function ensures
//! it computes its `spec_*`.
//!
//! The document machine is `echod_concrete`: `handle`, `sweep`, `run_due`
//! and `create_occurrence` are proved there to compute `spec_handle`,
//! `spec_sweep`, `spec_run_due` and `spec_occurrence`, the steps of the
//! concrete Rover model. `doc.rs` turns a document's rows into its `Doc`
//! and back; the handlers order the store calls around those steps.
//!
//! `cargo verus verify -p echod-process` checks this module. `cargo build`
//! compiles it with the ghost code erased.
//!
//! ```text
//! node.rs            membership, cache versions, armed keys
//! node_spec.rs       what each of those decisions means
//! commit.rs          which key to arm, which to remove, which to remember
//! commit_spec.rs     what each of those decisions means
//! ```

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

pub mod commit;
pub mod commit_spec;
pub mod node;
pub mod node_spec;

pub use echod_types::*;
