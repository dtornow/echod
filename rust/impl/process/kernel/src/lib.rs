//! echod-kernel: the Resonate state machine over one document store.
//!
//! The specification it is proved against is `echod_concrete`: the catalogue,
//! and one `spec_*` function per handler. This crate is that machine as
//! executable Rust. Every handler ensures the catalogue and ensures it
//! computes its `spec_*`.
//!
//! ```text
//! store.rs           State: three row vectors whose view is the concrete AState
//! store_proof.rs     a row at an index is the entry at its key
//! external.rs        the 18 request handlers; each ensures it computes its spec_*
//! internal.rs        the 6 internal steps; each ensures it computes its spec
//! steps.rs           sweep, drain, next_deadline, clamp_now, schedule_due
//! node.rs            membership, cache versions, armed keys
//! commit.rs          which key to arm, which to remove, which to remember
//! ```
//!
//! Every executable function ensures it computes its specification in
//! `echod_concrete`. Theorems about those specifications live there too.
//!
//! `./verify.sh` verifies the concrete specification and then this crate.
//! `cargo build` compiles the same sources with the ghost code erased.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

pub mod commit;
pub mod external;
pub mod internal;
pub mod node;
pub mod store;
pub mod steps;
pub mod store_proof;

/// Rows, records, requests. Defined in the concrete specification; the
/// executable items are what `cargo build` keeps.
pub mod types {
    pub use echod_concrete::types::*;
}

pub use store::*;
pub use types::*;

/// Tags, and the executable readers (`exec_otype`, `exec_timer_targeted`).
pub mod tags {
    pub use echod_concrete::tags::*;
}

/// Projection and the per-object edits. `create_promise` is executable.
pub mod object {
    pub use echod_concrete::object::*;
}

#[cfg(verus_keep_ghost)]
pub mod properties {
    pub use echod_concrete::properties::*;
}

#[cfg(verus_keep_ghost)]
pub mod properties_proof {
    pub use echod_concrete::properties_proof::*;
}

#[cfg(verus_keep_ghost)]
pub mod external_proof {
    pub use echod_concrete::external_proof::*;
}

#[cfg(verus_keep_ghost)]
pub mod object_proof {
    pub use echod_concrete::object_proof::*;
}

#[cfg(verus_keep_ghost)]
pub mod tags_proof {
    pub use echod_concrete::tags_proof::*;
}

#[cfg(verus_keep_ghost)]
pub mod spec {
    pub use echod_concrete::spec::*;
}

#[cfg(verus_keep_ghost)]
pub mod internal_spec {
    pub use echod_concrete::internal_spec::*;
}

#[cfg(verus_keep_ghost)]
pub mod internal_proof {
    pub use echod_concrete::internal_proof::*;
}

#[cfg(verus_keep_ghost)]
pub mod steps_spec {
    pub use echod_concrete::steps_spec::*;
}

#[cfg(verus_keep_ghost)]
pub mod node_spec {
    pub use echod_concrete::node_spec::*;
}

#[cfg(verus_keep_ghost)]
pub mod commit_spec {
    pub use echod_concrete::commit_spec::*;
}
