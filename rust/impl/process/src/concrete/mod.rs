//! Executable realization of the mathematical concrete model.

pub mod document;
pub mod rover;
pub mod runtime;
pub mod store;

pub use document::{
    clone_doc, create_occurrence, doc_deadline, doc_len, empty_doc, empty_origin, empty_schedule,
    handle, keys_within, peek, run_due, same_doc, sweep, Doc, Obj, Objects, Outbound, Pending, Prom, Tk,
};
pub use store::{content_etag, before, Etag, Read, StoreCall, StoreError, StoreOutcome};

#[cfg(test)]
mod world_tests;
