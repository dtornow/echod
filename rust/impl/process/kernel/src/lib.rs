//! echod-kernel: the Resonate state machine over one document store.
//!
//! The specification it is proved against is `echod_concrete`: the catalogue,
//! and one `spec_*` function per handler. This crate is that machine as
//! executable Rust. Every handler ensures the catalogue and ensures it
//! computes its `spec_*`.
//!
//! ```text
//! store.rs           State: three row vectors whose view is the concrete AState
//! store_proof.rs     the fold lemmas and the row readers
//! external.rs        the 18 request handlers; `handle` over `Request`
//! internal.rs        the 6 internal steps
//! internal_proof.rs  their lemmas
//! steps.rs           sweep, drain, next_deadline, clamp_now, schedule_due
//! node.rs            membership, cache versions, armed keys
//! commit.rs          which key to arm, which to remove, which to remember
//! ```
//!
//! The vocabulary, the catalogue and the `spec_*` functions are
//! `echod_concrete`. This crate depends on that one. The process calls these
//! functions; it does not reimplement them.
//!
//! `./verify.sh` verifies the concrete specification and then this crate.
//! `cargo build` compiles the same sources with the ghost code erased.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

pub mod commit;
pub mod external;
pub mod internal;
pub mod internal_proof;
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
