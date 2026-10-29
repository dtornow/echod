//! The nodes: announce, list, read the configuration, write the next
//! epoch, and who owns what.
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
//! None of this is safety. Writes are conditional on the version read, and
//! `echod-system` proves the documents correct and every deadline covered
//! whichever node acts; a node's cache is used only once a conditional
//! read has confirmed its version. Membership steers which node caches an
//! origin and which fires its deadlines: two nodes acting on one origin at
//! once waste work, and nothing more.
//!
//! The state behind the rules, and the decisions, are not here: they are
//! `echod_kernel::node::NodeCore`, executable Rust verified to compute the
//! system model's specification functions step for step. This module is
//! the shim around that core: it announces, lists, reads the configuration
//! object and hands the result to `read_config`. Membership is decided on
//! the fleet's time, the later of a node's clock and the latest
//! announcement it listed, which absorbs a clock that steps back or runs
//! slow.
//!
//! Ownership is `hash(target) mod n` over the members in order. A load
//! balancer that applies the same function over `members` sends every
//! request for an origin to the node that caches it and fires its
//! deadlines.

use std::collections::{BTreeMap, HashSet};

use echod_codec::bridge::{
    decode_announcement, decode_membership, encode_announcement, encode_membership,
};
use echod_codec::text::Text;
use echod_codec::types as codec;
use echod_kernel::node::NodeCore;
use serde::{Deserialize, Serialize};

use crate::types::*;
use crate::{Config, Owner, State};

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

fn encode_announcement_body(value: &Announcement) -> Result<Vec<u8>, &'static str> {
    encode_announcement(&codec::Announcement {
        id: Text::from_string(&value.id),
        url: Text::from_string(&value.url),
        at: value.at,
    })
}

fn decode_announcement_body(bytes: &[u8]) -> Result<Announcement, &'static str> {
    let value = decode_announcement(&bytes.to_vec())?;
    Ok(Announcement {
        id: value.id.into_string(),
        url: value.url.into_string(),
        at: value.at,
    })
}

fn encode_configuration_body(value: &Configuration) -> Result<Vec<u8>, &'static str> {
    encode_membership(&codec::Membership {
        epoch: value.epoch,
        members: value.members.iter().map(Text::from_string).collect(),
    })
}

fn decode_configuration_body(bytes: &[u8]) -> Result<Configuration, &'static str> {
    let value = decode_membership(&bytes.to_vec())?;
    Ok(Configuration {
        epoch: value.epoch,
        members: value.members.into_iter().map(Text::into_string).collect(),
    })
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
enum Refresh {
    Announcing {
        op: OpId,
        now: u64,
    },
    Listing {
        op: OpId,
        now: u64,
    },
    Reading {
        pending: HashSet<OpId>,
        nodes: BTreeMap<String, Announcement>,
        now: u64,
        failed: Option<StoreError>,
    },
    Config {
        op: OpId,
        nodes: BTreeMap<String, Announcement>,
    },
    Writing {
        op: OpId,
        next: Configuration,
    },
}

impl Refresh {
    fn expects(&self, op: OpId) -> bool {
        match self {
            Refresh::Announcing { op: o, .. }
            | Refresh::Listing { op: o, .. }
            | Refresh::Config { op: o, .. }
            | Refresh::Writing { op: o, .. } => *o == op,
            Refresh::Reading { pending, .. } => pending.contains(&op),
        }
    }
}

pub(crate) struct Members {
    me: Announcement,
    heartbeat_ms: u64,
    ttl: u64,
    /// Who announced, and the version of the configuration object read.
    nodes: BTreeMap<String, Announcement>,
    etag: Option<Etag>,
    next_heartbeat: Option<u64>,
    refresh: Option<Refresh>,
    /// The first refresh that succeeded started the timers.
    read_once: bool,
    /// The node stopped while a refresh was in flight: leave when it ends.
    pub leave_pending: bool,
}

impl Members {
    pub fn new(cfg: &Config) -> Self {
        Self {
            me: Announcement {
                id: cfg.node_id.clone(),
                url: cfg.url.clone(),
                at: 0,
            },
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
        Membership {
            nodes: self.nodes.clone(),
            epoch: core.epoch,
            members: core.members.clone(),
            etag: self.etag.clone(),
            last_read: core.last_read,
            read_any: core.read_any,
        }
    }
}

impl State {
    /// Does this node own `target` per the members it holds? No while
    /// nobody is a member yet.
    pub(crate) fn owns(&self, target: &str) -> bool {
        self.core.owner(target).as_deref() == Some(self.cfg.node_id.as_str())
    }

    /// Announce this node, list the others, read the configuration, and
    /// write the next epoch if the announced set has moved away from it.
    pub(crate) fn members_refresh(&mut self, now: u64) {
        if self.members.refreshing() {
            return;
        }
        self.members.me.at = now;
        let body =
            encode_announcement_body(&self.members.me).expect("an announcement is encodable");
        let key = self.keys.node_key(&self.members.me.id);
        let op = self.store(StoreCall::Put { key, body }, Owner::Members);
        self.members.refresh = Some(Refresh::Announcing { op, now });
    }

    pub(crate) fn members_tick(&mut self, now: u64) {
        if !self.members.refreshing() && self.members.next_heartbeat.is_none_or(|t| t <= now) {
            self.members_refresh(now);
        }
    }

    pub(crate) fn members_completed(&mut self, op: OpId, outcome: StoreOutcome) {
        let Some(refresh) = self.members.refresh.take() else {
            return;
        };
        if !refresh.expects(op) {
            self.members.refresh = Some(refresh);
            return;
        }
        match refresh {
            Refresh::Announcing { now, .. } => match outcome {
                StoreOutcome::Done => {
                    let op = self.store(
                        StoreCall::List {
                            prefix: self.keys.node_prefix(),
                            max_keys: 10_000,
                        },
                        Owner::Members,
                    );
                    self.members.refresh = Some(Refresh::Listing { op, now });
                }
                StoreOutcome::Failed(e) => self.refresh_ended(Err(e)),
                _ => self.refresh_ended(Err(unexpected())),
            },
            Refresh::Listing { now, .. } => match outcome {
                StoreOutcome::Listed(keys) => {
                    let mut nodes = BTreeMap::new();
                    nodes.insert(self.members.me.id.clone(), self.members.me.clone());
                    let mut pending = HashSet::new();
                    for key in keys {
                        if self.keys.node_of_key(&key).as_deref()
                            == Some(self.members.me.id.as_str())
                        {
                            continue;
                        }
                        pending.insert(self.store(StoreCall::Get { key }, Owner::Members));
                    }
                    if pending.is_empty() {
                        self.read_configuration(nodes);
                    } else {
                        self.members.refresh = Some(Refresh::Reading {
                            pending,
                            nodes,
                            now,
                            failed: None,
                        });
                    }
                }
                StoreOutcome::Failed(e) => self.refresh_ended(Err(e)),
                _ => self.refresh_ended(Err(unexpected())),
            },
            Refresh::Reading {
                mut pending,
                mut nodes,
                now,
                mut failed,
            } => {
                pending.remove(&op);
                match outcome {
                    StoreOutcome::Got(Some((bytes, _))) => {
                        if let Ok(a) = decode_announcement_body(&bytes) {
                            self.fleet_at = self.fleet_at.max(a.at);
                            if a.at + self.members.ttl >= now {
                                nodes.insert(a.id.clone(), a);
                            } else if a.at + 2 * self.members.ttl < now {
                                // Long dead: collect it. A node that is merely slow writes again.
                                let key = self.keys.node_key(&a.id);
                                self.store(StoreCall::Delete { key }, Owner::Ignored);
                            }
                        }
                        // anything unreadable is not a node
                    }
                    StoreOutcome::Got(None) => {}
                    StoreOutcome::Failed(e) => failed = Some(e),
                    _ => failed = Some(unexpected()),
                }
                if !pending.is_empty() {
                    self.members.refresh = Some(Refresh::Reading {
                        pending,
                        nodes,
                        now,
                        failed,
                    });
                } else if let Some(e) = failed {
                    self.refresh_ended(Err(e));
                } else {
                    self.read_configuration(nodes);
                }
            }
            Refresh::Config { nodes, .. } => match outcome {
                StoreOutcome::Got(read) => {
                    let (config, etag) = match read {
                        Some((bytes, etag)) => (
                            decode_configuration_body(&bytes).unwrap_or_default(),
                            Some(etag),
                        ),
                        None => (Configuration::default(), None),
                    };
                    self.take_on(config, etag, nodes);
                }
                StoreOutcome::Failed(e) => self.refresh_ended(Err(e)),
                _ => self.refresh_ended(Err(unexpected())),
            },
            Refresh::Writing { next, .. } => match outcome {
                StoreOutcome::Written(_) => {
                    self.note(Note::ConfigurationWrite(ConfigWrite::Written));
                    self.note(Note::ConfigurationWritten {
                        epoch: next.epoch,
                        members: next.members,
                    });
                    self.refresh_ended(Ok(()));
                }
                StoreOutcome::Failed(StoreError::PreconditionFailed) => {
                    // A lost race is read next time.
                    self.note(Note::ConfigurationWrite(ConfigWrite::Conflict));
                    self.refresh_ended(Ok(()));
                }
                StoreOutcome::Failed(e) => {
                    self.note(Note::ConfigurationWrite(ConfigWrite::Failed));
                    self.refresh_ended(Err(e));
                }
                _ => self.refresh_ended(Err(unexpected())),
            },
        }
    }

    /// The configuration: read it, and take it on.
    fn read_configuration(&mut self, nodes: BTreeMap<String, Announcement>) {
        let op = self.store(
            StoreCall::Get {
                key: self.keys.members_key(),
            },
            Owner::Members,
        );
        self.members.refresh = Some(Refresh::Config { op, nodes });
    }

    fn take_on(
        &mut self,
        config: Configuration,
        etag: Option<Etag>,
        nodes: BTreeMap<String, Announcement>,
    ) {
        let now = self.now();
        let changed = !(self.core.read_any && self.core.epoch == config.epoch);
        if changed {
            self.note(Note::ConfigurationRead {
                epoch: config.epoch,
                members: config.members.clone(),
            });
        }
        self.core
            .read_config(now, config.epoch, config.members.clone());
        self.members.nodes = nodes.clone();
        self.members.etag = etag.clone();
        if changed {
            self.note(Note::ConfigurationChange);
            // Ownership moved: every node's share of the deadlines did.
            self.timers_membership_changed();
        }
        // The announced set is the members the configuration should name.
        // Any node may write the next epoch; a lost race is read next time.
        let live: Vec<String> = nodes.keys().cloned().collect();
        if live != config.members {
            let next = Configuration {
                epoch: config.epoch + 1,
                members: live,
            };
            let body = encode_configuration_body(&next).expect("a membership is encodable");
            let key = self.keys.members_key();
            let call = match etag {
                Some(etag) => StoreCall::PutIfMatch { key, body, etag },
                None => StoreCall::PutIfNoneMatch { key, body },
            };
            let op = self.store(call, Owner::Members);
            self.members.refresh = Some(Refresh::Writing { op, next });
        } else {
            self.refresh_ended(Ok(()));
        }
    }

    fn refresh_ended(&mut self, r: Result<(), StoreError>) {
        self.members.refresh = None;
        let now = self.now();
        self.note(Note::MembershipRefresh { ok: r.is_ok() });
        match r {
            Ok(()) => {
                if !self.members.read_once {
                    self.members.read_once = true;
                    self.timers_start(now);
                }
            }
            Err(e) => self.note(Note::RefreshFailed {
                error: e.to_string(),
            }),
        }
        self.members.next_heartbeat = Some(now + self.members.heartbeat_ms);
        if self.members.leave_pending {
            self.members.leave_pending = false;
            self.leave();
        } else if self.loops {
            self.timers_run(now);
        }
    }
}

fn unexpected() -> StoreError {
    StoreError::Unavailable("the store answered something else".into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use echod_codec::frame::FORMAT_VERSION;

    #[test]
    fn announcement_and_membership_use_versioned_binary_bodies() {
        let announcement = Announcement {
            id: "node-東京".into(),
            url: "https://例.example/🦀".into(),
            at: 42,
        };
        let announcement_bytes = encode_announcement_body(&announcement).unwrap();
        assert_eq!(&announcement_bytes[..4], b"ECHO");
        assert_eq!(announcement_bytes[4], FORMAT_VERSION);
        assert_eq!(
            decode_announcement_body(&announcement_bytes).unwrap(),
            announcement
        );

        let configuration = Configuration {
            epoch: 7,
            members: vec!["alpha".into(), "节点".into()],
        };
        let membership_bytes = encode_configuration_body(&configuration).unwrap();
        assert_eq!(&membership_bytes[..4], b"ECHO");
        assert_eq!(membership_bytes[4], FORMAT_VERSION);
        assert_eq!(
            decode_configuration_body(&membership_bytes).unwrap(),
            configuration
        );
    }

    #[test]
    fn membership_bodies_reject_malformed_and_legacy_json_bytes() {
        let bytes = encode_configuration_body(&Configuration {
            epoch: 1,
            members: vec!["node".into()],
        })
        .unwrap();
        for end in 0..bytes.len() {
            assert!(decode_configuration_body(&bytes[..end]).is_err());
        }
        let mut wrong_version = bytes;
        wrong_version[4] = FORMAT_VERSION + 1;
        assert!(decode_configuration_body(&wrong_version).is_err());
        assert!(decode_configuration_body(br#"{"epoch":1,"members":["node"]}"#).is_err());
        assert!(decode_announcement_body(br#"{"id":"node","url":"u","at":1}"#).is_err());
    }
}
