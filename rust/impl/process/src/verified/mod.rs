//! The node's own bookkeeping: what a node decides about the membership,
//! its cache, and the deadline keys it armed, and which key a commit arms,
//! removes, and remembers. Each function ensures it computes its `spec_*`,
//! as does every function of the crate around it, up to `State::on_event`.
//!
//! The document machine is `echod_concrete`: `handle`, `sweep`, `run_due`
//! and `create_occurrence` are proved there to compute `spec_handle`,
//! `spec_sweep`, `spec_run_due` and `spec_occurrence`, the steps of the
//! concrete Rover model. `doc.rs` turns a document's rows into its `Doc`
//! and back; the handlers order the store calls around those steps.
//!
//! ```text
//! node.rs            membership, cache versions, armed keys
//! node_spec.rs       what each of those decisions means
//! commit.rs          which key to arm, which to remove, which to remember
//! commit_spec.rs     what each of those decisions means
//! flight.rs          the step on a document, and the commit: one store call after another
//! flight_spec.rs     the step as the model's; the sequence, and lemma_sequence: its calls in order
//! table.rs           a table of entries, viewed as a map
//! text.rs            strings: build, compare, strip a prefix
//! ```
//!
//! # What is assumed
//!
//! Verus checks `State::on_event == spec_on_event` against these, each
//! stated as a specification and assumed of its executable function:
//!
//! - The text of keys, `keys.rs`: `spec_doc_key`, `spec_timer_key`,
//!   `spec_parse_timer_key` and the rest are uninterpreted functions of
//!   their arguments; `text::*` is assumed to compute them. A key is some
//!   function of prefix, origin, instant and token; which string it is
//!   stays outside the proof.
//! - The bytes of a document, `doc.rs`: `spec_encode`, `spec_encode_delta`,
//!   `spec_decode_origin`, `spec_decode_schedule`; `codec::*` (serde) is
//!   assumed to compute them. Likewise an announcement's and a
//!   configuration's bytes, `state_node.rs`.
//! - Strings as characters: `text::strip_prefix`, `text::starts_with`,
//!   `text::u64_text`, `node::clone_string`, `node::str_eq`.
//! - Hashing: `node::fnv1a` computes `node_spec::hash`, an uninterpreted
//!   function of the string; `echod_concrete::content_etag` likewise.
//! - Copies: `echod_abstract::trusted::copy` returns its argument;
//!   `flight::copy_error` the same for a `StoreError`.
//! - The store: `StoreOutcome` is what the store answered. Whether S3
//!   answers as `echod_concrete::store::spec_apply` says is the store's
//!   fidelity, outside the proof; the simulator exercises it.
//! - The runtime: the clock handed in on every event, the effects
//!   performed in the order they leave, and each store answer returned
//!   under its op id.
//!
//! `cargo verus verify -p echod-process` checks the crate (the dependencies
//! with `--no-verify`); `cargo build` compiles it with the ghost code erased.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

pub mod commit;
pub mod commit_spec;
pub mod flight;
#[cfg(verus_keep_ghost)]
pub mod flight_spec;
pub mod node;
pub mod node_spec;
pub mod table;
pub mod text;

pub use echod_types::*;
