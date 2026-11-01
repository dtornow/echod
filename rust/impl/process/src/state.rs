//! What this process keeps: the node, the timers, the document cache, and
//! the steps in progress.
//!
//! The object a step loaded sits with that step. Several documents can be
//! mid-step at once, one each, so there is no single loaded object here.
//! The cache is the documents this process remembers between steps.

use std::collections::HashMap;

use crate::cache::{Cache, MemoryCache};
use crate::handler_docs::Flights;
use crate::keys::KeySpace;
use crate::state_node::Node;
use crate::state_timers::Timers;
use crate::types::*;
use crate::verified::Config as RowsConfig;
use crate::verified::node::Key;
use crate::Config;

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

/// The process. `on_event` is the only step.
pub struct State {
    pub(crate) cfg: Config,
    pub(crate) keys: KeySpace,
    /// `retry_timeout` and `compact`, as the document handlers take them.
    pub(crate) rows_cfg: RowsConfig,
    /// Membership, the epoch, and the versions of origins this process has seen.
    pub(crate) node: Node,
    /// Deadline keys ordered by when they fall due, and a listing filling the wheel.
    pub(crate) timers: Timers,
    pub(crate) cache: MemoryCache,
    /// The node's clock as the last event read it.
    pub(crate) clock: u64,
    tokens: u64,
    next_op: OpId,
    pub(crate) next_flight: FlightId,
    pub(crate) ops: HashMap<OpId, Owner>,
    /// One step in progress per document, and the queue behind it.
    pub(crate) flights: Flights,
    pub(crate) debug: crate::debug::Debug,
    /// Whether the node keeps itself going: heartbeats and timers.
    pub(crate) loops: bool,
    pub(crate) stopping: bool,
    stopped: bool,
    out: Vec<Effect>,
    /// The wake last asked of the runtime, so the same one is not asked twice.
    last_wake: Option<(u64, Armed)>,
}

impl State {
    pub fn new(cfg: Config) -> Self {
        let keys = KeySpace::new(&cfg.prefix, cfg.timer_bucket_ms);
        let rows_cfg = RowsConfig { retry_timeout: cfg.retry_timeout, compact: cfg.compact };
        let cache = MemoryCache::new(cfg.cache_entries, cfg.cache_bytes);
        let seed = crate::keys::fnv1a(&format!("{}/{}", cfg.url, cfg.node_id)) | 1;
        Self {
            node: Node::new(&cfg),
            timers: Timers::new(),
            cache,
            clock: 0,
            tokens: seed,
            next_op: 1,
            next_flight: 1,
            ops: HashMap::new(),
            flights: Flights::new(),
            debug: crate::debug::Debug::default(),
            loops: false,
            stopping: false,
            stopped: false,
            out: Vec::new(),
            last_wake: None,
            keys,
            rows_cfg,
            cfg,
        }
    }

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
        self.clock.max(self.node.fleet_at)
    }

    /// Whether this node acts as owner of what the members make it the
    /// owner of: fresh, in a configuration with members.
    pub fn acting(&self) -> bool {
        !self.node.core.members.is_empty() && self.node.core.fresh(self.now())
    }

    /// Whether this node's view of the membership is young enough to act on.
    pub fn fresh(&self) -> bool {
        self.node.core.fresh(self.now())
    }

    pub fn membership(&self) -> crate::state_node::Membership {
        self.node.members.snapshot(&self.node.core)
    }

    /// The member that owns `target` by the members this node holds.
    pub fn owner(&self, target: &str) -> Option<String> {
        self.node.core.owner(target)
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
            epoch: self.node.core.epoch,
            members: self.node.core.members.len() as u64,
            fresh: self.fresh(),
            acting: self.acting(),
            timers_armed: self.timers.wheel.len() as u64,
        }
    }

    pub fn keys(&self) -> &KeySpace {
        &self.keys
    }

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

    /// Remember a document and report its version to the core: read or wrote.
    pub(crate) fn remember(&mut self, origin: &str, c: crate::cache::Cached) {
        let (etag, filled_at) = (c.etag.clone(), c.filled_at);
        for evicted in self.cache.put(origin, c) {
            self.node.core.forget(&evicted);
        }
        self.node.core.filled(origin, etag.0, filled_at);
    }

    pub(crate) fn forget(&mut self, origin: &str) {
        self.cache.forget(origin);
        self.node.core.forget(origin);
    }

    pub(crate) fn take_out(&mut self) -> Vec<Effect> {
        std::mem::take(&mut self.out)
    }

    pub(crate) fn set_clock(&mut self, clock: u64) {
        self.clock = clock;
    }

    pub(crate) fn clear_wake(&mut self) {
        self.last_wake = None;
    }

    pub(crate) fn mark_stopped(&mut self) {
        self.stopped = true;
    }

    pub(crate) fn wake_moved(&mut self, next: Option<(u64, Armed)>) -> bool {
        if next == self.last_wake {
            return false;
        }
        self.last_wake = next;
        true
    }
}
