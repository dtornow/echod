//! The process's document, read as the concrete Rover model's document.
//!
//! `rust/impl/process` is proved against `echod-document`: each request
//! handler computes `echod_document::spec::spec_handle` on an `AState`. The
//! concrete Rover model's node computes `echod_concrete::node::spec_handle`
//! on a `DocV`, and that model refines the abstract one. This crate links
//! the two documents.
//!
//! Proved, by Verus (`handlers::lemma_handle_agrees`): for every request,
//! when `relation::doc_rel(a, doc, now)` relates the process's `AState` to
//! the model's `DocV`, the two `spec_handle`s leave related documents and
//! answer the same response (`s@ == r`). `relation::lemma_rel_later`
//! carries the relation to a later clock, so it holds from one request to
//! the next.
//!
//! The relation compares objects through their projection at `now`: the
//! process persists what a read projects, the model projects on every read
//! and writes only what a handler changes. Schedules are compared as
//! records.
//!
//! The statement has hypotheses, each a fact the process establishes before
//! its handler runs, or a bound the protocol keeps: `relation::req_ok` on
//! the request (every instant and duration at most `MAX_TIME`; a schedule's
//! `next_run_at` is the cron engine's next run; a heartbeat names one
//! origin; a `resonate:delay` tag parses the same on both sides),
//! `relation::doc_ok` on the document (a task's version is below
//! `MAX_VERSION`, its ttl at most `MAX_TIME`), `relation::kind_ok` (the
//! request reaches the document of its kind) and `now <= MAX_TIME`.
//!
//! Trusted here: `handlers::axiom_tags_realised` (every abstract tag list is
//! some `Tags`), together with `echod_abstract::trusted`.
//!
//! Outside this crate: the due step. The process's `sweep` and `drain` are
//! specified by reachability (`swept_by`, `drained`); the model's
//! `spec_run_due` is a function. Where they differ is listed in the pull
//! request. Cargo erases everything here.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code))]

#[cfg(verus_keep_ghost)]
pub mod relation;
#[cfg(verus_keep_ghost)]
pub mod handlers;
