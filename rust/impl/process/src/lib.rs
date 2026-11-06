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
//! verified/          the node's proved bookkeeping: membership, cache, keys
//! ```
//!
//! The concrete Rover model decides: a request is `echod_concrete::handle`,
//! a sweep `echod_concrete::sweep`, a schedule's run `run_due` and
//! `create_occurrence`, each proved there to compute its specification.
//! The handlers turn a document's rows into the model's `Doc`, run the
//! step, and order the store calls around it. The runtime admits a protocol
//! envelope and performs what comes out.

// Under Verus only `verified` is loaded and checked; the modules around it
// are plain Rust, compiled by cargo.
#[cfg(not(verus_keep_ghost))]
pub mod cache;
#[cfg(not(verus_keep_ghost))]
pub mod config;
#[cfg(not(verus_keep_ghost))]
mod debug;
#[cfg(not(verus_keep_ghost))]
pub mod doc;
#[cfg(not(verus_keep_ghost))]
mod handler;
#[cfg(not(verus_keep_ghost))]
mod handler_docs;
#[cfg(not(verus_keep_ghost))]
mod handler_node;
#[cfg(not(verus_keep_ghost))]
mod handler_sched;
#[cfg(not(verus_keep_ghost))]
mod handler_timers;
#[cfg(not(verus_keep_ghost))]
pub mod keys;
#[cfg(not(verus_keep_ghost))]
pub mod reason;
#[cfg(not(verus_keep_ghost))]
mod state;
#[cfg(not(verus_keep_ghost))]
mod state_node;
#[cfg(not(verus_keep_ghost))]
mod state_timers;
#[cfg(not(verus_keep_ghost))]
pub mod target;
#[cfg(not(verus_keep_ghost))]
pub mod types;
pub mod verified;

#[cfg(not(verus_keep_ghost))]
pub use config::Config;
#[cfg(not(verus_keep_ghost))]
pub use state::{Snapshot, State};
#[cfg(not(verus_keep_ghost))]
pub use state_node::{Announcement, Configuration, Membership};
#[cfg(not(verus_keep_ghost))]
pub use target::Target;
#[cfg(not(verus_keep_ghost))]
pub use types::{Answer, Armed, Call, DebugBody, DebugCall, Effect, Event, Message, Note};
#[cfg(not(verus_keep_ghost))]
pub(crate) use state::Owner;
