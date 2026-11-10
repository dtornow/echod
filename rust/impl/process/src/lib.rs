//! echod-logic: the decision core of a node, with no I/O in it.
//!
//! The core is a state machine: `State`, `Event` in, `Effect`s out,
//! `on_event` the only step. Every call on the store leaves as an
//! `Effect::Store` under an op id and comes back as `Event::Completed`
//! under the same id; every answer to a client leaves as `Effect::Reply`;
//! the clock is read by whoever drives the core and handed in on every
//! event. Nothing here waits, sleeps, locks or spawns, so the same events
//! in the same order give the same effects, on a server, in a simulation,
//! or in a test that feeds them by hand.
//!
//! ```text
//! handler.rs         on_event. A network request above the line; below it,
//!                    a store answer, the heartbeat, or the wheel
//! handler_node.rs    the announcement, the membership, who owns a target
//! handler_docs.rs    one origin: its promises, the task inside each, a sweep
//! handler_sched.rs   one schedule: create, read, delete, a run coming due
//! handler_timers.rs  which keys are due; an origin to docs, a schedule to sched
//! state.rs           the node, the timers, the cache, the steps in progress
//! state_node.rs      the members and the epoch, the versions of origins seen
//! state_timers.rs    deadline keys ordered by when they fall due
//! types.rs           events, store calls and outcomes, effects, notes
//! config.rs          the dials
//! keys.rs            where everything lives under the bucket
//! doc.rs             a document: rows in, the model's Doc, rows out
//! target.rs          an origin's document, or a schedule's
//! reason.rs          the words a refusal carries
//! cache.rs           documents this node remembers, by LRU under a byte budget
//! debug.rs           debug.reset, debug.snap, debug.tick
//! verified/          the node's bookkeeping: membership, cache, keys, the commit sequence, and the trust list
//! ```
//!
//! The whole crate is proved: `State::on_event` ensures it computes
//! `handler::spec_on_event`, the step of the process as a specification
//! over `StateSpec`, and every function beneath it ensures its own
//! `spec_*` the same way. `cargo verus verify -p echod-process` checks it;
//! `cargo build` compiles the same sources with the ghost code erased.
//! What is assumed is listed in `verified/mod.rs`.
//!
//! The local concrete document machine decides a request, sweep, schedule
//! run, or occurrence. Each executable step is proved here to compute the
//! mathematical transition in `echod-rover-concrete-spec`.
//! The handlers turn a document's rows into the model's `Doc`, run the
//! step by `verified::flight::decide`, and commit by `verified::flight::
//! Sequence`, which orders the store calls around it — key, document,
//! previous key, fired key — and is proved to: `flight_spec::lemma_sequence`
//! is that order, `lemma_step_is_decide` ties the document written and the
//! write's condition to the concrete model's `spec_decide`. The runtime
//! admits a protocol envelope and performs what comes out.

// The `verus!` macro writes a destructuring `let` with every field named
// twice; the lint on that is noise here.
#![allow(non_shorthand_field_patterns)]

// Every module is inside `verus!`: cargo compiles the code, cargo-verus
// checks that `State::on_event` computes `spec_on_event`.
pub mod cache;
pub mod config;
pub mod concrete;
pub mod debug;
pub mod doc;
pub mod handler;
pub mod handler_docs;
pub mod handler_node;
pub mod handler_sched;
pub mod handler_timers;
pub mod keys;
pub mod reason;
pub mod state;
pub mod state_node;
pub mod state_timers;
pub mod target;
pub mod types;
pub mod verified;

pub use config::Config;
pub use state::{Snapshot, State};
pub use state_node::{Announcement, Configuration, Membership};
pub use target::Target;
pub use types::{Answer, Armed, Call, DebugBody, DebugCall, Effect, Event, Message, Note};
