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
//! types.rs      the vocabulary: events, store calls and outcomes, effects, notes
//! config.rs     the dials
//! keys.rs       where everything lives under the bucket
//! doc.rs        a document, an origin's or a schedule's: rows in, rows out, the fold between
//! wire.rs       the kernel's vocabulary to the protocol's and back
//! cache.rs      what a node remembers: documents by LRU under a byte budget
//! dispatch.rs   the envelope to the kernel's request, and the document it runs on
//! flight.rs     one step on one document, from load to commit: the verified protocol, one store call at a time; the fire across two
//! members.rs    the nodes: announce, list, read the configuration, write the next epoch
//! timers.rs     deadlines as keys in time buckets, held in a wheel, fired by the owner
//! debug.rs      debug.reset, debug.snap, debug.tick: what a test that owns the clock asks for
//! ```
//!
//! What stays verified beneath, all of it the kernel's: `handle` runs every
//! request, `NodeCore` and `Commit` take every decision about membership,
//! cache and deadline keys, and `steps` runs the sweep and the drain.
//! The core is the shim the proof stops at, now with nothing in it but
//! the order of calls.

use std::collections::HashMap;

use echod_kernel::node::{Key, NodeCore};
use echod_kernel::Config as KernelConfig;
use resonate_core::types::RequestEnvelope;

use crate::cache::{Cache, Cached, MemoryCache};
use crate::keys::KeySpace;
use crate::types::*;

pub mod cache;
pub mod config;
pub mod debug;
pub mod dispatch;
pub mod doc;
pub mod flight;
pub mod keys;
pub mod members;
pub mod timers;
pub mod types;
pub mod wire;

pub use config::Config;
pub use dispatch::Target;
pub use types::{Effect, Event, Note};

/// Who waits for a store call's answer.
pub(crate) enum Owner {
    Flight(FlightId),
    Members,
    Timers,
    Debug,
    /// The node's announcement being withdrawn: its answer ends the node.
    Leaving,
    /// Nobody: a best-effort call whose answer changes nothing.
    Ignored,
}

/// What a node holds and decides with: the verified core, the cache, the
/// flights on documents, the membership and the timers.
pub struct State {
    pub(crate) cfg: Config,
    pub(crate) keys: KeySpace,
    pub(crate) kcfg: KernelConfig,
    /// The verified node: its view of the configuration, its cache's
    /// versions, and the deadline key it last armed per target.
    pub(crate) core: NodeCore,
    pub(crate) cache: MemoryCache,
    /// The latest instant any announcement carried.
    pub(crate) fleet_at: u64,
    /// The node's clock as the last event read it.
    pub(crate) clock: u64,
    tokens: u64,
    next_op: OpId,
    pub(crate) next_flight: FlightId,
    pub(crate) ops: HashMap<OpId, Owner>,
    pub(crate) flights: flight::Flights,
    pub(crate) members: members::Members,
    pub(crate) timers: timers::Timers,
    pub(crate) debug: debug::Debug,
    /// Whether the node keeps itself going: heartbeats and timers.
    pub(crate) loops: bool,
    pub(crate) stopping: bool,
    stopped: bool,
    out: Vec<Effect>,
    last_wake: Option<u64>,
}

/// What an observer reads of the node at a glance.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Snapshot {
    pub cache_entries: u64,
    pub cache_bytes: u64,
    pub cache_evictions: u64,
    pub epoch: u64,
    pub members: u64,
    pub fresh: bool,
    pub acting: bool,
    pub timers_armed: u64,
}

impl State {
    pub fn new(cfg: Config) -> Self {
        let keys = KeySpace::new(&cfg.prefix, cfg.timer_bucket_ms);
        let kcfg = cfg.kernel();
        let core = NodeCore::new(cfg.node_id.clone(), cfg.node_ttl_ms);
        let cache = MemoryCache::new(cfg.cache_entries, cfg.cache_bytes);
        let seed = keys::fnv1a(&format!("{}/{}", cfg.url, cfg.node_id)) | 1;
        let members = members::Members::new(&cfg);
        Self {
            keys,
            kcfg,
            core,
            cache,
            fleet_at: 0,
            clock: 0,
            tokens: seed,
            next_op: 1,
            next_flight: 1,
            ops: HashMap::new(),
            flights: flight::Flights::new(),
            members,
            timers: timers::Timers::new(),
            debug: debug::Debug::default(),
            loops: false,
            stopping: false,
            stopped: false,
            out: Vec::new(),
            last_wake: None,
            cfg,
        }
    }

    /// The one step: an event in, the effects it calls for out.
    pub fn on_event(&mut self, event: Event) -> Vec<Effect> {
        match event {
            Event::Start { clock, loops } => {
                self.clock = clock;
                self.loops = loops;
                let now = self.now();
                self.members_refresh(now);
            }
            Event::Request { id, envelope, clock } => {
                self.clock = clock;
                self.request(id, envelope);
            }
            Event::Completed { op, outcome, clock } => {
                self.clock = clock;
                match self.ops.remove(&op) {
                    Some(Owner::Flight(f)) => self.flight_completed(f, op, outcome),
                    Some(Owner::Members) => self.members_completed(op, outcome),
                    Some(Owner::Timers) => self.timers_completed(op, outcome),
                    Some(Owner::Debug) => self.debug_completed(op, outcome),
                    Some(Owner::Leaving) => self.stopped = true,
                    Some(Owner::Ignored) | None => {}
                }
            }
            Event::Tick { clock } => {
                self.clock = clock;
                // A wake that came early asks again below.
                self.last_wake = None;
                if self.loops && !self.stopping {
                    let now = self.now();
                    self.members_tick(now);
                    self.timers_run(now);
                }
            }
            Event::Stop { clock } => {
                self.clock = clock;
                self.stop();
            }
        }
        self.schedule_wake();
        std::mem::take(&mut self.out)
    }

    // -----------------------------------------------------------------------
    // What an observer reads
    // -----------------------------------------------------------------------

    pub fn config(&self) -> &Config {
        &self.cfg
    }

    pub fn id(&self) -> &str {
        &self.cfg.node_id
    }

    pub fn url(&self) -> &str {
        &self.cfg.url
    }

    /// The fleet's time: this node's clock, or the latest announcement it
    /// has listed, whichever is later.
    pub fn now(&self) -> u64 {
        self.clock.max(self.fleet_at)
    }

    /// Whether this node acts as owner of what the members make it the
    /// owner of: fresh, in a configuration with members.
    pub fn acting(&self) -> bool {
        !self.core.members.is_empty() && self.core.fresh(self.now())
    }

    /// Whether this node's view of the membership is young enough to act on.
    pub fn fresh(&self) -> bool {
        self.core.fresh(self.now())
    }

    pub fn membership(&self) -> members::Membership {
        self.members.snapshot(&self.core)
    }

    /// The member that owns `target` by the members this node holds.
    pub fn owner(&self, target: &str) -> Option<String> {
        self.core.owner(target)
    }

    /// The node has withdrawn its announcement: nothing more to do.
    pub fn stopped(&self) -> bool {
        self.stopped
    }

    pub fn snapshot(&self) -> Snapshot {
        let c = self.cache.stats();
        Snapshot {
            cache_entries: c.entries as u64,
            cache_bytes: c.bytes,
            cache_evictions: c.evictions,
            epoch: self.core.epoch,
            members: self.core.members.len() as u64,
            fresh: self.fresh(),
            acting: self.acting(),
            timers_armed: self.timers.wheel.len() as u64,
        }
    }

    pub fn keys(&self) -> &KeySpace {
        &self.keys
    }

    // -----------------------------------------------------------------------
    // Requests
    // -----------------------------------------------------------------------

    fn request(&mut self, id: RequestId, envelope: RequestEnvelope) {
        if self.cfg.debug && envelope.kind.starts_with("debug.") {
            return self.debug_request(id, envelope);
        }
        let now = match (self.cfg.debug, envelope.head.debug_time) {
            (true, Some(t)) => t.max(0) as u64,
            _ => self.now(),
        };
        match dispatch::decode(&envelope, now) {
            Err(resp) => self.emit(Effect::Reply { id, response: Ok(resp) }),
            Ok(d) => {
                let stage = match d.then {
                    Some((then, check)) => flight::Stage::Detached { then, check: Some(Box::new(check)) },
                    None => flight::Stage::Whole,
                };
                let work = flight::Work::Request { id, kind: envelope.kind, corr: envelope.head.corr_id, req: d.request, action_kind: d.action_kind, now, stage };
                self.submit(d.target, work, None, false);
            }
        }
    }

    fn stop(&mut self) {
        self.stopping = true;
        self.loops = false;
        // A refresh in flight finishes first, so the announcement it
        // writes does not outlive the withdrawal.
        if self.members.refreshing() {
            self.members.leave_pending = true;
        } else {
            self.leave();
        }
    }

    pub(crate) fn leave(&mut self) {
        let key = self.keys.node_key(&self.cfg.node_id);
        self.store(StoreCall::Delete { key }, Owner::Leaving);
    }

    // -----------------------------------------------------------------------
    // Shared helpers
    // -----------------------------------------------------------------------

    pub(crate) fn emit(&mut self, e: Effect) {
        self.out.push(e);
    }

    pub(crate) fn note(&mut self, n: Note) {
        self.out.push(Effect::Note(n));
    }

    /// Issue a store call; `owner` gets its answer.
    pub(crate) fn store(&mut self, call: StoreCall, owner: Owner) -> OpId {
        let op = self.next_op;
        self.next_op += 1;
        self.ops.insert(op, owner);
        self.out.push(Effect::Store { op, call });
        op
    }

    /// A token no other arm of this node has used.
    pub(crate) fn token(&mut self) -> u64 {
        let t = self.tokens;
        self.tokens = self.tokens.wrapping_add(0x9e37_79b9_7f4a_7c15);
        t
    }

    /// The name of a key in the bucket, armed by `by`.
    pub(crate) fn key_name(&self, k: &Key, by: &str) -> String {
        if let Some(id) = k.origin.strip_prefix("sched:") {
            self.keys.sched_timer_key(id, k.at, k.token, by)
        } else {
            self.keys.timer_key(&k.origin, k.at, k.token, by)
        }
    }

    /// Remember a document and report its version to the core: read or
    /// wrote.
    pub(crate) fn remember(&mut self, origin: &str, c: Cached) {
        let (etag, filled_at) = (c.etag.clone(), c.filled_at);
        for evicted in self.cache.put(origin, c) {
            self.core.forget(&evicted);
        }
        self.core.filled(origin, etag.0, filled_at);
    }

    pub(crate) fn forget(&mut self, origin: &str) {
        self.cache.forget(origin);
        self.core.forget(origin);
    }

    /// Ask for a tick at the earliest instant anything is due, when that
    /// moved.
    fn schedule_wake(&mut self) {
        if !self.loops || self.stopping {
            return;
        }
        let now = self.now();
        let at = [self.members.wake_at(), self.timers.wake_at(now)].into_iter().flatten().min();
        if at != self.last_wake {
            if let Some(at) = at {
                self.emit(Effect::Wake { after_ms: at.saturating_sub(now).max(1) });
            }
            self.last_wake = at;
        }
    }
}

pub fn unavailable(e: StoreError) -> resonate_core::Unavailable {
    resonate_core::Unavailable::new(e.to_string())
}
