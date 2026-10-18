//! The nodes: announce, heartbeat, the configuration, and who owns what.
//!
//! A node announces itself as `nodes/<id>` holding its URL and when it last
//! did so, and refreshes that every `heartbeat`. The member list is one
//! object, `nodes/members`, holding the members and the epoch it was written
//! in; whoever sees the announced set differ from it writes the next epoch
//! with a conditional put, so epochs are totally ordered and every node that
//! reads the object reads the same sequence. A node keeps the epoch and the
//! members it read, when it read them, and when it first read the epoch it
//! holds. It acts as owner of an origin only when its view is fresh (read
//! within a TTL), its members make it the owner, and it has held its epoch
//! for the grace; and it trusts a cache entry only if the entry was filled
//! while it was acting. Writes are conditional on the version read.
//!
//! These are the rules `echod-fleet` proves exclusive and sound under
//! bounded clock skew with `grace > ttl + 4 skew`: a node in an older epoch
//! is fresh for at most a TTL after a read that preceded the newer epoch; a
//! node in the newer epoch acts only a grace after it first read it; the
//! windows do not meet. Membership is decided on the fleet's time, the
//! later of a node's clock and the latest announcement it listed, which
//! absorbs a clock that steps back or runs slow.
//!
//! Ownership is `hash(key) mod n` over the members in order. A load balancer
//! that applies the same function over `nodes/members` sends every request
//! for an origin to the node that caches it and fires its deadlines.

use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};
use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::keys::{fnv1a, KeySpace};
use crate::store::Store;

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

/// What a node holds of the membership.
#[derive(Debug, Clone, Default)]
pub struct Membership {
    /// Every node announced within a TTL, as of the last listing.
    pub nodes: BTreeMap<String, Announcement>,
    /// The epoch read, and its members in order: what ownership is computed over.
    pub epoch: u64,
    pub members: Vec<String>,
    /// The ETag of the configuration object read, for the next conditional put.
    pub etag: Option<crate::store::Etag>,
    /// When the configuration was last read, and when the epoch held was first read.
    pub last_read: u64,
    pub held: u64,
    pub read_any: bool,
}

impl Membership {
    /// The member that owns `key`: the one at `hash(key) mod n` in id order.
    pub fn owner_of(&self, key: &str) -> Option<&Announcement> {
        let n = self.members.len() as u64;
        if n == 0 {
            return None;
        }
        self.nodes.get(&self.members[(fnv1a(key) % n) as usize])
    }

    /// The member ids in order: the table a load balancer needs.
    pub fn ids(&self) -> Vec<String> {
        self.members.clone()
    }
}

pub struct Nodes {
    store: Arc<dyn Store>,
    keys: KeySpace,
    me: RwLock<Announcement>,
    heartbeat: Duration,
    ttl: u64,
    /// The grace: `ttl + 4 skew`, and one more.
    grace: u64,
    members: RwLock<Membership>,
    clock: Arc<dyn crate::env::Clock>,
    /// The latest instant any announcement carried.
    fleet_at: std::sync::atomic::AtomicU64,
    /// Bumped whenever the member set changes.
    generation: tokio::sync::watch::Sender<u64>,
}

impl Nodes {
    pub fn new(store: Arc<dyn Store>, keys: KeySpace, id: String, url: String, heartbeat: Duration, ttl: u64, skew: u64, clock: Arc<dyn crate::env::Clock>) -> Self {
        let me = Announcement { id, url, at: 0 };
        let (generation, _) = tokio::sync::watch::channel(0);
        Self { store, keys, me: RwLock::new(me), heartbeat, ttl, grace: ttl + 4 * skew + 1, members: RwLock::new(Membership::default()), clock, fleet_at: std::sync::atomic::AtomicU64::new(0), generation }
    }

    pub fn grace(&self) -> u64 {
        self.grace
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
        self.members.read().unwrap_or_else(|e| e.into_inner()).clone()
    }

    /// Is this node the owner of `key` per the members it holds? No while
    /// nobody is a member yet.
    pub fn owns(&self, key: &str) -> bool {
        self.owner(key).map(|o| o.id == self.id()).unwrap_or(false)
    }

    pub fn owner(&self, key: &str) -> Option<Announcement> {
        self.members().owner_of(key).cloned()
    }

    /// Whether this node's view of the membership is young enough to act on.
    pub fn fresh(&self, now: u64) -> bool {
        let m = self.members();
        m.read_any && m.last_read + self.ttl >= now
    }

    /// Does this node act as owner of `key` right now: fresh, the owner per
    /// its members, and holding its epoch for the grace? The model's `acts`.
    pub fn acts(&self, key: &str, now: u64) -> bool {
        let m = self.members();
        m.read_any && m.last_read + self.ttl >= now && m.held + self.grace <= now && m.owner_of(key).map(|o| o.id == self.id()).unwrap_or(false)
    }

    /// The instant from which a cache entry filled by this node may be
    /// trusted, while it acts: the grace after it first read its epoch. The
    /// model's `trusts`. `None` while it does not act on `key`.
    pub fn trust_after(&self, key: &str, now: u64) -> Option<u64> {
        if !self.acts(key, now) {
            return None;
        }
        Some(self.members().held + self.grace)
    }

    /// Announce this node, list the others, read the configuration, and
    /// write the next epoch if the announced set has moved away from it.
    pub async fn refresh(&self, now: u64) -> Result<(), crate::store::StoreError> {
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
        let mut changed = false;
        {
            let mut m = self.members.write().unwrap_or_else(|e| e.into_inner());
            let same = m.read_any && m.epoch == config.epoch;
            if !same {
                tracing::info!(epoch = config.epoch, members = ?config.members, "configuration read");
                m.held = now;
                changed = true;
            }
            m.nodes = nodes.clone();
            m.epoch = config.epoch;
            m.members = config.members.clone();
            m.etag = etag.clone();
            m.last_read = now;
            m.read_any = true;
        }
        if changed {
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
                Ok(_) => tracing::info!(epoch = next.epoch, members = ?next.members, "configuration written"),
                Err(crate::store::StoreError::PreconditionFailed) => {}
                Err(e) => return Err(e),
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
