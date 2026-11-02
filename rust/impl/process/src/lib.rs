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
//! state_docs.rs      the promise rows of one origin
//! state_sched.rs     one schedule's rows
//! state_timers.rs    deadline keys ordered by when they fall due
//! types.rs           events, store calls and outcomes, effects, notes
//! config.rs          the dials
//! keys.rs            where everything lives under the bucket
//! doc.rs             a document: rows in, rows out, the fold between
//! target.rs          an origin's document, or a schedule's
//! reason.rs          the words a refusal carries
//! cache.rs           documents this node remembers, by LRU under a byte budget
//! debug.rs           debug.reset, debug.snap, debug.tick
//! verified/          the proved document machine
//! ```
//!
//! `verified` decides. The handlers order the store calls around those
//! decisions. The runtime admits a protocol envelope and performs what comes
//! out. `./verify.sh` proves `verified`; it does not load the rest.

pub mod cache;
pub mod config;
mod debug;
pub mod doc;
mod handler;
mod handler_docs;
mod handler_node;
mod handler_sched;
mod handler_timers;
pub mod keys;
pub mod reason;
mod state;
mod state_docs;
mod state_node;
mod state_sched;
mod state_timers;
pub mod target;
pub mod types;
pub mod verified;

pub use config::Config;
pub use state::{Snapshot, State};
pub use state_node::{Announcement, Configuration, Membership};
pub use target::Target;
pub use types::{Answer, Armed, Call, DebugBody, DebugCall, Effect, Event, Note};
pub use verified::Message;

pub(crate) use state::Owner;
