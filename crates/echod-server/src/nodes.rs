//! The nodes: announce, heartbeat, list, and who owns what.
//!
//! A node announces itself as `nodes/<id>` holding its URL and the instant it
//! last did so, and refreshes that every `heartbeat`. Every heartbeat it also
//! lists `nodes/` and keeps the ones announced within `ttl`: that is the
//! membership. Nothing is agreed on; each node sees the bucket and decides
//! alone, and the conditional writes keep the state right whatever it decides.
//! Membership only steers who serves an origin, who fires its deadlines, and
//! whose cache may be trusted.
//!
//! Ownership is rendezvous hashing: for a key, the live node with the highest
//! hash of `(node, key)` owns it. A node joining or leaving moves only the keys
//! that hash to it, and every node computes the same answer from the same list.

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
    /// The instant of the announcement, ms.
    pub at: u64,
}

/// The nodes a node knows of, including itself.
#[derive(Debug, Clone, Default)]
pub struct Membership {
    pub nodes: BTreeMap<String, Announcement>,
}

impl Membership {
    /// The live node that owns `key`, by rendezvous hashing.
    pub fn owner_of(&self, key: &str) -> Option<&Announcement> {
        self.nodes.values().max_by_key(|n| (fnv1a(&format!("{}\u{0}{}", n.id, key)), n.id.clone()))
    }
}

pub struct Nodes {
    store: Arc<dyn Store>,
    keys: KeySpace,
    me: Announcement,
    heartbeat: Duration,
    ttl: u64,
    members: RwLock<Membership>,
}

impl Nodes {
    pub fn new(store: Arc<dyn Store>, keys: KeySpace, id: String, url: String, heartbeat: Duration, ttl: u64) -> Self {
        let me = Announcement { id: id.clone(), url, at: 0 };
        let mut members = Membership::default();
        members.nodes.insert(id, me.clone());
        Self { store, keys, me, heartbeat, ttl, members: RwLock::new(members) }
    }

    pub fn id(&self) -> &str {
        &self.me.id
    }

    pub fn url(&self) -> &str {
        &self.me.url
    }

    pub fn members(&self) -> Membership {
        self.members.read().unwrap_or_else(|e| e.into_inner()).clone()
    }

    /// Is this node the owner of `key`? Yes when nobody else is known.
    pub fn owns(&self, key: &str) -> bool {
        self.owner(key).map(|o| o.id == self.me.id).unwrap_or(true)
    }

    pub fn owner(&self, key: &str) -> Option<Announcement> {
        self.members().owner_of(key).cloned()
    }

    /// Announce this node, then list the others.
    pub async fn refresh(&self, now: u64) -> Result<(), crate::store::StoreError> {
        let mine = Announcement { at: now, ..self.me.clone() };
        let body = serde_json::to_vec(&mine).expect("an announcement serialises");
        self.store.put(&self.keys.node_key(&self.me.id), body).await?;
        let keys = self.store.list(&self.keys.node_prefix(), 10_000).await?;
        let mut nodes = BTreeMap::new();
        nodes.insert(self.me.id.clone(), mine);
        for key in keys {
            if self.keys.node_of_key(&key).as_deref() == Some(self.me.id.as_str()) {
                continue;
            }
            let Some((bytes, _)) = self.store.get(&key).await? else { continue };
            let Ok(a) = serde_json::from_slice::<Announcement>(&bytes) else {
                tracing::warn!(key = %key, "unreadable announcement ignored");
                continue;
            };
            if a.at + self.ttl >= now {
                nodes.insert(a.id.clone(), a);
            } else if a.at + 2 * self.ttl < now {
                // Long dead: collect it. A node that is merely slow writes again.
                let _ = self.store.delete(&key).await;
            }
        }
        let before: Vec<String> = self.members().nodes.keys().cloned().collect();
        let after: Vec<String> = nodes.keys().cloned().collect();
        if before != after {
            tracing::info!(nodes = ?after, "membership changed");
        }
        *self.members.write().unwrap_or_else(|e| e.into_inner()) = Membership { nodes };
        Ok(())
    }

    /// Withdraw this node's announcement.
    pub async fn leave(&self) {
        let _ = self.store.delete(&self.keys.node_key(&self.me.id)).await;
    }

    /// The heartbeat loop: announce and list until told to stop.
    pub fn spawn(self: Arc<Self>, mut shutdown: tokio::sync::watch::Receiver<bool>) -> tokio::task::JoinHandle<()> {
        tokio::spawn(async move {
            loop {
                if let Err(e) = self.refresh(resonate_core::util::system_time_ms() as u64).await {
                    tracing::warn!(error = %e, "node heartbeat failed");
                }
                tokio::select! {
                    _ = tokio::time::sleep(self.heartbeat) => {}
                    _ = shutdown.changed() => {
                        self.leave().await;
                        return;
                    }
                }
            }
        })
    }
}
