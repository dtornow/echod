//! The concrete Rover model.
//!
//! Rover steps this crate's `Model`: the nodes and one store. The handler
//! specifications live here too, and the process depends on this crate so a
//! handler's `ensures` can name `spec_promise_create` and the other `spec_*`
//! functions. This crate depends on Rover and on the abstract model, and
//! does not depend on the process. The refinement of this model to the
//! abstract one is stated in `refine` and is not proved yet.
//!
//! ```text
//! plane.rs            one node: its documents, one flight, the store round trip
//! model.rs            the Rover model: nodes, one store, the initial world
//! rover_model.rs      RoverModel for that world
//! refine.rs           the statement against the abstract Rover model
//! store.rs            store calls and their answers
//! types.rs            rows, the outbox, identifiers; echod_types re-exported
//! tags.rs             tags: first match wins; otype, timer, target
//! state.rs            the document as three maps, and the fold that makes them
//! fold_proof.rs       a row edit is the map edit; compaction replays the same document
//! object.rs           projection and the per-object edits the handlers share
//! properties.rs       the catalogue, transcribed
//! spec.rs             the handlers as functions of that document
//! internal_spec.rs    the internal steps, as functions of that document
//! internal_proof.rs   the catalogue lemmas for those steps
//! steps_spec.rs       sweep, drain, deadlines, and the lemmas about them
//! node_spec.rs        membership, cache, armed keys
//! commit_spec.rs      which key a commit arms, removes, and remembers
//! timeouts.rs         an origin's nearest deadline, filed in its time bucket
//! on_event.rs         the document step inside a loaded request
//! ```

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]

pub mod commit_spec;
pub mod external_proof;
pub mod fold_proof;
pub mod internal_proof;
pub mod internal_spec;
pub mod model;
pub mod node_spec;
pub mod object;
pub mod object_proof;
pub mod on_event;
mod plane;
pub mod properties;
pub mod properties_proof;
pub mod spec;
pub mod state;
pub mod steps_spec;
pub mod store;
pub mod tags;
pub mod tags_proof;
pub mod timeouts;
pub mod types;

#[cfg(not(verus_keep_ghost))]
mod rover_model;

#[cfg(not(verus_keep_ghost))]
pub mod refine;

#[cfg(not(verus_keep_ghost))]
pub use refine::abstract_model;

pub use model::Model;
pub use store::{content_etag, fnv1a, Etag, Read, StoreCall, StoreError, StoreOutcome};
pub use types::*;
