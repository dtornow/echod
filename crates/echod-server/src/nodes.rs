//! The nodes: announce, heartbeat, the configuration, and who owns what.
//!
//! A node announces itself as `nodes/<id>` holding its URL and when it last
//! did so, and refreshes that every `heartbeat`. The member list is one
//! object, `nodes/members`, holding the members and the epoch it was written
//! in; whoever sees the announced set differ from it writes the next epoch
//! with a conditional put, so epochs are totally ordered and every node that
//! reads the object reads the same sequence. A node keeps the epoch and the
//! members it read and when it read them. It acts as owner of an origin
//! when its view is fresh (read within a TTL, by its own clock) and its
//! members make it the owner.
//!
//! None of this is safety. Writes are conditional on the version read, and
//! `echod-fleet` proves the documents correct and every deadline covered
//! whichever node acts; a node's cache is used only once a conditional read
//! has confirmed its version. Membership steers where requests go, which
//! node caches an origin, and which node fires its deadlines: two nodes
//! acting on one origin at once waste work, and nothing more.
//!
//! The state behind the rules, and the decisions, are not here: they are
//! `echod_fleet::node::core::NodeCore`, executable Rust verified to compute
//! the fleet model's specification functions step for step. This module is
//! the trusted shim around that core: it announces, lists, reads the
//! configuration object and hands the result to `read_config`; it asks
//! `acts`; it reports every document version read or written with
//! `filled`, and every entry dropped with `forget`. Membership is decided
//! on the fleet's time, the later of a node's clock and the latest
//! announcement it listed, which absorbs a clock that steps back or runs
//! slow.
//!
//! Ownership is `hash(key) mod n` over the members in order. A load balancer
//! that applies the same function over `nodes/members` sends every request
//! for an origin to the node that caches it and fires its deadlines.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, RwLock};
use std::time::Duration;

use echod_fleet::node::core::{Armed, Key, NodeCore};
use echod_fleet::node::txn::Txn;
use serde::{Deserialize, Serialize};

use crate::keys::KeySpace;
use crate::metrics::{ConfigWrite, Metrics};
use crate::store::{Etag, Store};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Announcement {
    pub id: String,
    pub url: String,
    /// The instant of the latest announcement, ms.
    pub at: u64,
}

/// The configuration object: the members, and the epoch it was written in.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct Members {
    pub epoch: u64,
    pub members: Vec<String>,
}

/// A snapshot of what a node holds of the membership, for whoever looks.
#[derive(Debug, Clone, Default)]
pub struct Membership {
    /// Every node announced within a TTL, as of the last listing.
    pub nodes: BTreeMap<String, Announcement>,
    /// The epoch read, and its members in order: what ownership is computed over.
    pub epoch: u64,
    pub members: Vec<String>,
    /// The ETag of the configuration object read, for the next conditional put.
    pub etag: Option<Etag>,
    /// When the configuration was last read.
    pub last_read: u64,
    pub read_any: bool,
}

impl Membership {
    /// The member ids in order: the table a load balancer needs.
    pub fn ids(&self) -> Vec<String> {
        self.members.clone()
    }
}

/// What the shim keeps beside the core: who announced, and the version of
/// the configuration object read.
#[derive(Default)]
struct Listing {
    nodes: BTreeMap<String, Announcement>,
    etag: Option<Etag>,
}

pub struct Nodes {
    store: Arc<dyn Store>,
    keys: KeySpace,
    me: RwLock<Announcement>,
    heartbeat: Duration,
    ttl: u64,
    /// The verified node: its view of the configuration and its cache's versions.
    core: Mutex<NodeCore>,
    listing: RwLock<Listing>,
    clock: Arc<dyn crate::env::Clock>,
    /// The latest instant any announcement carried.
    fleet_at: std::sync::atomic::AtomicU64,
    /// Bumped whenever the member set changes.
    generation: tokio::sync::watch::Sender<u64>,
    metrics: Arc<Metrics>,
}

impl Nodes {
    pub fn new(store: Arc<dyn Store>, keys: KeySpace, id: String, url: String, heartbeat: Duration, ttl: u64, clock: Arc<dyn crate::env::Clock>, metrics: Arc<Metrics>) -> Self {
        let core = NodeCore::new(id.clone(), ttl);
        let me = Announcement { id, url, at: 0 };
        let (generation, _) = tokio::sync::watch::channel(0);
        Self { store, keys, me: RwLock::new(me), heartbeat, ttl, core: Mutex::new(core), listing: RwLock::new(Listing::default()), clock, fleet_at: std::sync::atomic::AtomicU64::new(0), generation, metrics }
    }

    fn core(&self) -> std::sync::MutexGuard<'_, NodeCore> {
        self.core.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// The fleet's time: this node's clock, or the latest announcement it has
    /// listed, whichever is later.
    pub fn now(&self) -> u64 {
        self.clock.now().max(self.fleet_at.load(std::sync::atomic::Ordering::Relaxed))
    }

    pub fn ttl(&self) -> u64 {
        self.ttl
    }

    pub fn heartbeat_ms(&self) -> u64 {
        self.heartbeat.as_millis() as u64
    }

    fn me(&self) -> Announcement {
        self.me.read().unwrap_or_else(|e| e.into_inner()).clone()
    }

    /// Changes of membership, for whoever must act on them.
    pub fn generations(&self) -> tokio::sync::watch::Receiver<u64> {
        self.generation.subscribe()
    }

    pub fn id(&self) -> String {
        self.me().id
    }

    pub fn url(&self) -> String {
        self.me().url
    }

    pub fn members(&self) -> Membership {
        let l = self.listing.read().unwrap_or_else(|e| e.into_inner());
        let c = self.core();
        Membership { nodes: l.nodes.clone(), epoch: c.epoch, members: c.members.clone(), etag: l.etag.clone(), last_read: c.last_read, read_any: c.read_any }
    }

    /// Is this node the owner of `key` per the members it holds? No while
    /// nobody is a member yet.
    pub fn owns(&self, key: &str) -> bool {
        self.owner_id(key).map(|o| o == self.id()).unwrap_or(false)
    }

    /// The member that owns `key`: `hash(key) mod n` over the members in
    /// order, as the core computes it.
    pub fn owner_id(&self, key: &str) -> Option<String> {
        self.core().owner(key)
    }

    /// The owner of `key`, with its announcement; `None` while the owner is
    /// not among the nodes listed, or nobody is a member yet.
    pub fn owner(&self, key: &str) -> Option<Announcement> {
        let id = self.owner_id(key)?;
        if id == self.id() {
            return Some(self.me());
        }
        self.listing.read().unwrap_or_else(|e| e.into_inner()).nodes.get(&id).cloned()
    }

    /// Whether this node's view of the membership is young enough to act on.
    pub fn fresh(&self, now: u64) -> bool {
        self.core().fresh(now)
    }

    /// Whether this node acts as owner of what the members make it the
    /// owner of: fresh, in a configuration with members.
    pub fn acting(&self) -> bool {
        let now = self.now();
        let c = self.core();
        !c.members.is_empty() && c.fresh(now)
    }

    /// Does this node act as owner of `key` right now: fresh, and the owner
    /// per its members? The core's `acts`. Routing, not safety.
    pub fn acts(&self, key: &str, now: u64) -> bool {
        self.core().acts(key, now)
    }

    /// This node read `origin` at version `etag` from the bucket, or wrote
    /// it there, at `now`.
    pub fn filled(&self, origin: &str, etag: &Etag, now: u64) {
        self.core().filled(origin, etag.0.clone(), now);
    }

    /// Begin a commit on `origin`, loaded at `etag`: `NodeCore::begin`.
    pub fn begin(&self, origin: &str, etag: Option<&Etag>, deadline: Option<u64>, changed: bool, fired: Option<Key>) -> Txn {
        let e = etag.map(|e| e.0.clone());
        self.core().begin(origin, e.as_ref(), deadline, changed, fired)
    }

    /// After the write at `etag`: remember the key kept: `NodeCore::finish`.
    pub fn finish(&self, txn: &Txn, etag: &Etag) {
        self.core().finish(txn, &etag.0);
    }

    /// A fired key was collected: `NodeCore::collected`.
    pub fn collected(&self, origin: &str, key: &Key) {
        self.core().collected(origin, key);
    }

    /// The key remembered for `target`, with the version written with it.
    pub fn armed_for(&self, target: &str) -> Option<Armed> {
        self.core().armed_for(target).cloned()
    }

    pub fn set_armed(&self, target: &str, a: Option<Armed>) {
        self.core().set_armed(target, a);
    }

    /// This node dropped what it held of `origin`.
    pub fn forget(&self, origin: &str) {
        self.core().forget(origin);
    }

    /// Announce this node, list the others, read the configuration, and
    /// write the next epoch if the announced set has moved away from it.
    pub async fn refresh(&self, now: u64) -> Result<(), crate::store::StoreError> {
        let r = self.refresh_inner(now).await;
        self.metrics.membership_refresh(r.is_ok());
        r
    }

    async fn refresh_inner(&self, now: u64) -> Result<(), crate::store::StoreError> {
        let mine = {
            let mut me = self.me.write().unwrap_or_else(|e| e.into_inner());
            me.at = now;
            me.clone()
        };
        let body = serde_json::to_vec(&mine).expect("an announcement serialises");
        self.store.put(&self.keys.node_key(&mine.id), body).await?;
        let keys = self.store.list(&self.keys.node_prefix(), 10_000).await?;
        let mut nodes = BTreeMap::new();
        nodes.insert(mine.id.clone(), mine.clone());
        for key in keys {
            if self.keys.node_of_key(&key).as_deref() == Some(mine.id.as_str()) {
                continue;
            }
            let Some((bytes, _)) = self.store.get(&key).await? else { continue };
            let Ok(a) = serde_json::from_slice::<Announcement>(&bytes) else {
                continue; // the configuration object, or something unreadable
            };
            self.fleet_at.fetch_max(a.at, std::sync::atomic::Ordering::Relaxed);
            if a.at + self.ttl >= now {
                nodes.insert(a.id.clone(), a);
            } else if a.at + 2 * self.ttl < now {
                // Long dead: collect it. A node that is merely slow writes again.
                let _ = self.store.delete(&key).await;
            }
        }
        // The configuration: read it, and take it on.
        let (config, etag) = match self.store.get(&self.keys.members_key()).await? {
            Some((bytes, etag)) => (serde_json::from_slice::<Members>(&bytes).unwrap_or_default(), Some(etag)),
            None => (Members::default(), None),
        };
        let now = self.now();
        let changed = {
            let mut c = self.core();
            let changed = !(c.read_any && c.epoch == config.epoch);
            if changed {
                tracing::info!(epoch = config.epoch, members = ?config.members, "configuration read");
            }
            c.read_config(now, config.epoch, config.members.clone());
            changed
        };
        {
            let mut l = self.listing.write().unwrap_or_else(|e| e.into_inner());
            l.nodes = nodes.clone();
            l.etag = etag.clone();
        }
        if changed {
            self.metrics.configuration_change();
            self.generation.send_modify(|g| *g += 1);
        }
        // The announced set is the members the configuration should name.
        // Any node may write the next epoch; a lost race is read next time.
        let live: Vec<String> = nodes.keys().cloned().collect();
        if live != config.members {
            let next = Members { epoch: config.epoch + 1, members: live };
            let body = serde_json::to_vec(&next).expect("a configuration serialises");
            let r = match &etag {
                Some(etag) => self.store.put_if_match(&self.keys.members_key(), body, etag).await,
                None => self.store.put_if_none_match(&self.keys.members_key(), body).await,
            };
            match r {
                Ok(_) => {
                    self.metrics.configuration_write(ConfigWrite::Written);
                    tracing::info!(epoch = next.epoch, members = ?next.members, "configuration written");
                }
                Err(crate::store::StoreError::PreconditionFailed) => self.metrics.configuration_write(ConfigWrite::Conflict),
                Err(e) => {
                    self.metrics.configuration_write(ConfigWrite::Failed);
                    return Err(e);
                }
            }
        }
        Ok(())
    }

    /// Withdraw this node's announcement.
    pub async fn leave(&self) {
        let _ = self.store.delete(&self.keys.node_key(&self.id())).await;
    }

    /// The heartbeat loop: announce and list until told to stop.
    pub fn spawn(self: Arc<Self>, mut shutdown: tokio::sync::watch::Receiver<bool>) -> tokio::task::JoinHandle<()> {
        tokio::spawn(async move {
            loop {
                if let Err(e) = self.refresh(self.now()).await {
                    tracing::warn!(error = %e, "node heartbeat failed");
                }
                tokio::select! {
                    biased;
                    _ = shutdown.changed() => {
                        self.leave().await;
                        return;
                    }
                    _ = tokio::time::sleep(self.heartbeat) => {}
                }
            }
        })
    }
}
