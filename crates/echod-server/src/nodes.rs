//! The nodes: announce, heartbeat, list, and who owns what.
//!
//! A node announces itself as `nodes/<id>` holding its URL, when it first
//! announced and when it last did, and refreshes that every `heartbeat`. Every
//! heartbeat it also lists `nodes/`. Nothing is agreed on; each node sees the
//! bucket and decides alone, and the conditional writes keep the state right
//! whatever it decides. Membership steers who serves an origin, who fires its
//! deadlines, and whose cache may be trusted — and for the last of these to
//! be sound, two nodes must never both act as owner of one origin while one
//! of them trusts its cache. Three rules give that:
//!
//! - **A node joins late.** It counts as a member only once its first
//!   announcement is a TTL old, so every node has listed it by then. Until
//!   then it owns nothing.
//! - **A change suspends trust.** When the member set a node sees changes, it
//!   trusts no cache entry filled before `now + ttl + heartbeat`: long enough
//!   for every other node to have seen the same change and stopped writing
//!   what it no longer owns.
//! - **A stale view serves nothing.** A node whose last listing is a TTL old
//!   may be fenced out and does not know it; it answers 503 until it can list.
//!
//! All of this is decided on the **fleet's time**: the later of a node's own
//! clock and the latest announcement it has listed. A clock that steps back
//! or runs slow is absorbed; the fleet runs on its fastest clock. What is not
//! absorbed is a clock that steps forward by about a TTL at once: the node
//! sees every peer expire, and for a heartbeat writes as owner of origins
//! whose owners still trust their caches. The rules hold while any node's
//! skew plus its largest step, plus a heartbeat, stays under the TTL.
//!
//! Ownership is `hash(key) mod n` over the members in id order. A load
//! balancer that applies the same function sends every request for an origin
//! to the node that caches it and fires its deadlines.

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
    /// The instant of the first announcement, ms.
    #[serde(default)]
    pub since: u64,
}

/// The nodes a node knows of, including itself.
#[derive(Debug, Clone, Default)]
pub struct Membership {
    /// Every node announced within a TTL.
    pub nodes: BTreeMap<String, Announcement>,
    /// The ids of the members: announced within a TTL, and first announced at
    /// least a TTL ago. In order; what ownership is computed over.
    pub members: Vec<String>,
    /// When this member set was first seen.
    pub stable_since: u64,
    /// When the listing behind this membership succeeded.
    pub refreshed_at: u64,
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
    members: RwLock<Membership>,
    clock: Arc<dyn crate::env::Clock>,
    /// The latest instant any announcement carried.
    fleet_at: std::sync::atomic::AtomicU64,
    /// Bumped whenever the member set changes.
    generation: tokio::sync::watch::Sender<u64>,
}

impl Nodes {
    pub fn new(store: Arc<dyn Store>, keys: KeySpace, id: String, url: String, heartbeat: Duration, ttl: u64, clock: Arc<dyn crate::env::Clock>) -> Self {
        let me = Announcement { id, url, at: 0, since: 0 };
        let (generation, _) = tokio::sync::watch::channel(0);
        Self { store, keys, me: RwLock::new(me), heartbeat, ttl, members: RwLock::new(Membership::default()), clock, fleet_at: std::sync::atomic::AtomicU64::new(0), generation }
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

    /// Is this node the owner of `key`? No while nobody is a member yet.
    pub fn owns(&self, key: &str) -> bool {
        self.owner(key).map(|o| o.id == self.id()).unwrap_or(false)
    }

    pub fn owner(&self, key: &str) -> Option<Announcement> {
        self.members().owner_of(key).cloned()
    }

    /// Whether this node's view of the membership is young enough to act on.
    pub fn fresh(&self, now: u64) -> bool {
        let m = self.members();
        m.refreshed_at > 0 && m.refreshed_at + self.ttl >= now
    }

    /// The instant from which a cache entry may be trusted: a TTL and a
    /// heartbeat after the member set last changed, so every node has seen
    /// the change and stopped writing what it no longer owns. `None` while
    /// the view is stale.
    pub fn trust_after(&self, now: u64) -> Option<u64> {
        if !self.fresh(now) {
            return None;
        }
        Some(self.members().stable_since + self.ttl + self.heartbeat.as_millis() as u64)
    }

    /// Announce this node, then list the others.
    pub async fn refresh(&self, now: u64) -> Result<(), crate::store::StoreError> {
        let mine = {
            let mut me = self.me.write().unwrap_or_else(|e| e.into_inner());
            if me.since == 0 {
                me.since = now;
            }
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
                tracing::warn!(key = %key, "unreadable announcement ignored");
                continue;
            };
            self.fleet_at.fetch_max(a.at, std::sync::atomic::Ordering::Relaxed);
            if a.at + self.ttl >= now {
                nodes.insert(a.id.clone(), a);
            } else if a.at + 2 * self.ttl < now {
                // Long dead: collect it. A node that is merely slow writes again.
                let _ = self.store.delete(&key).await;
            }
        }
        let members: Vec<String> = nodes.values().filter(|a| a.since + self.ttl <= now).map(|a| a.id.clone()).collect();
        let mut m = self.members.write().unwrap_or_else(|e| e.into_inner());
        let changed = m.members != members;
        if changed {
            tracing::info!(members = ?members, "membership changed");
            m.stable_since = now;
        }
        m.nodes = nodes;
        m.members = members;
        m.refreshed_at = now;
        drop(m);
        if changed {
            self.generation.send_modify(|g| *g += 1);
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
