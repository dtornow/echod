//! The proved half of the process: one document, and what a node decides
//! about membership, its cache, and the deadline keys it armed.
//!
//! `./verify.sh` loads this file as its crate root, then the document
//! specification. `cargo build` loads it as `echod_logic::verified`, with
//! the ghost code erased. The modules beside this one run the store calls
//! these functions decide between.
//!
//! `types`, `tags`, `object`, and the specification modules are
//! `echod_document`. A handler ensures it computes its `spec_*`.
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

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

pub mod commit;
pub mod external;
pub mod internal;
pub mod node;
pub mod steps;
pub mod store;
pub mod store_proof;

pub use echod_document::object;
pub use echod_document::tags;
pub use echod_document::types;

#[cfg(verus_keep_ghost)]
pub use echod_document::external_proof;
#[cfg(verus_keep_ghost)]
pub use echod_document::internal_proof;
#[cfg(verus_keep_ghost)]
pub use echod_document::internal_spec;
#[cfg(verus_keep_ghost)]
pub use echod_document::properties;
#[cfg(verus_keep_ghost)]
pub use echod_document::properties_proof;
#[cfg(verus_keep_ghost)]
pub use echod_document::spec;
#[cfg(verus_keep_ghost)]
pub use echod_document::steps_spec;

pub use store::*;
pub use types::*;
