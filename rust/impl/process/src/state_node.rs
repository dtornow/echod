//! The fleet, as this process holds it: who has announced, the epoch, and
//! the refresh that is bringing the next one in.
//!
//! The steps that announce, list, and write the epoch are `handler_node`.
//!
//! A node announces itself as `nodes/<id>` holding its URL and when it last
//! did so, and refreshes that every heartbeat. The configuration is one
//! object, `members`, holding the members and the epoch it was written
//! in; whoever sees the announced set differ from it writes the next epoch
//! with a conditional put, so epochs are totally ordered and every node
//! that reads the object reads the same sequence. A node keeps the epoch
//! and the members it read and when it read them. It acts as owner of a
//! target when its view is fresh (read within a TTL, by its own clock) and
//! its members make it the owner.
//!
//! None of this is safety. Writes are conditional on the version read. A
//! node's cache is used only once a conditional read has confirmed its
//! version. Membership steers which node caches an origin and which fires
//! its deadlines: two nodes acting on one origin at once waste work, and
//! nothing more.
//!
//! The decisions are `verified::node::NodeCore`. `handler_node` announces,
//! lists, reads the configuration object and hands the result to
//! `read_config`. Membership is decided on
//! the fleet's time, the later of a node's clock and the latest
//! announcement it listed, which absorbs a clock that steps back or runs
//! slow.
//!
//! Ownership is `hash(target) mod n` over the members in order. A load
//! balancer that applies the same function over `members` sends every
//! request for an origin to the node that caches it and fires its
//! deadlines.

use std::collections::{BTreeMap, HashSet};

use crate::verified::node::NodeCore;
use serde::{Deserialize, Serialize};

use crate::types::*;
use crate::Config;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Announcement {
    pub id: String,
    pub url: String,
    /// The instant of the latest announcement, ms.
    pub at: u64,
}

/// The configuration object: the members, and the epoch it was written in.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct Configuration {
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
    /// The version of the configuration object read, for the next conditional put.
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

/// A refresh in progress: announce, list, read each, read the
/// configuration, write the next epoch if the announced set moved.
pub(crate) enum Refresh {
    Announcing { op: OpId, now: u64 },
    Listing { op: OpId, now: u64 },
    Reading { pending: HashSet<OpId>, nodes: BTreeMap<String, Announcement>, now: u64, failed: Option<StoreError> },
    Config { op: OpId, nodes: BTreeMap<String, Announcement> },
    Writing { op: OpId, next: Configuration },
}

impl Refresh {
    pub(crate) fn expects(&self, op: OpId) -> bool {
        match self {
            Refresh::Announcing { op: o, .. } | Refresh::Listing { op: o, .. } | Refresh::Config { op: o, .. } | Refresh::Writing { op: o, .. } => *o == op,
            Refresh::Reading { pending, .. } => pending.contains(&op),
        }
    }
}

pub(crate) struct Members {
    pub(crate) me: Announcement,
    pub(crate) heartbeat_ms: u64,
    pub(crate) ttl: u64,
    /// Who announced, and the version of the configuration object read.
    pub(crate) nodes: BTreeMap<String, Announcement>,
    pub(crate) etag: Option<Etag>,
    pub(crate) next_heartbeat: Option<u64>,
    pub(crate) refresh: Option<Refresh>,
    /// The first refresh that succeeded started the timers.
    pub(crate) read_once: bool,
    /// The node stopped while a refresh was in flight: leave when it ends.
    pub(crate) leave_pending: bool,
}

impl Members {
    pub fn new(cfg: &Config) -> Self {
        Self {
            me: Announcement { id: cfg.node_id.clone(), url: cfg.url.clone(), at: 0 },
            heartbeat_ms: cfg.heartbeat_ms,
            ttl: cfg.node_ttl_ms,
            nodes: BTreeMap::new(),
            etag: None,
            next_heartbeat: None,
            refresh: None,
            read_once: false,
            leave_pending: false,
        }
    }

    pub fn refreshing(&self) -> bool {
        self.refresh.is_some()
    }

    pub fn wake_at(&self) -> Option<u64> {
        if self.refreshing() {
            None
        } else {
            self.next_heartbeat
        }
    }

    pub fn snapshot(&self, core: &NodeCore) -> Membership {
        Membership { nodes: self.nodes.clone(), epoch: core.epoch, members: core.members.clone(), etag: self.etag.clone(), last_read: core.last_read, read_any: core.read_any }
    }
}

/// What this process holds of the fleet: the proved membership core, the
/// refresh in progress, and the latest instant any announcement carried.
pub(crate) struct Node {
    pub core: crate::verified::node::NodeCore,
    pub members: Members,
    pub fleet_at: u64,
}

impl Node {
    pub fn new(cfg: &crate::Config) -> Self {
        Self {
            core: crate::verified::node::NodeCore::new(cfg.node_id.clone(), cfg.node_ttl_ms),
            members: Members::new(cfg),
            fleet_at: 0,
        }
    }
}
