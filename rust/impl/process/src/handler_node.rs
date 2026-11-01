//! The announcement, the membership, and whether this process owns a target.
//!
//! A refresh is one announcement, the list of the others, a read of the
//! configuration, and a write of the next epoch when the announced set has
//! moved. Ownership is the proved core's, over the members it was given.

use std::collections::{BTreeMap, HashSet};

use crate::state_node::{Announcement, Configuration, Refresh};
use crate::types::*;
use crate::{Owner, State};

impl State {
    /// Does this node own `target` per the members it holds? No while
    /// nobody is a member yet.
    pub(crate) fn owns(&self, target: &str) -> bool {
        self.node.core.owner(target).as_deref() == Some(self.cfg.node_id.as_str())
    }

    /// Announce this node, list the others, read the configuration, and
    /// write the next epoch if the announced set has moved away from it.
    pub(crate) fn members_refresh(&mut self, now: u64) {
        if self.node.members.refreshing() {
            return;
        }
        self.node.members.me.at = now;
        let body = serde_json::to_vec(&self.node.members.me).expect("an announcement serialises");
        let key = self.keys.node_key(&self.node.members.me.id);
        let op = self.store(StoreCall::Put { key, body }, Owner::Members);
        self.node.members.refresh = Some(Refresh::Announcing { op, now });
    }

    pub(crate) fn members_tick(&mut self, now: u64) {
        if !self.node.members.refreshing() && self.node.members.next_heartbeat.is_none_or(|t| t <= now) {
            self.members_refresh(now);
        }
    }

    pub(crate) fn members_completed(&mut self, op: OpId, outcome: StoreOutcome) {
        let Some(refresh) = self.node.members.refresh.take() else { return };
        if !refresh.expects(op) {
            self.node.members.refresh = Some(refresh);
            return;
        }
        match refresh {
            Refresh::Announcing { now, .. } => match outcome {
                StoreOutcome::Done => {
                    let op = self.store(StoreCall::List { prefix: self.keys.node_prefix(), max_keys: 10_000 }, Owner::Members);
                    self.node.members.refresh = Some(Refresh::Listing { op, now });
                }
                StoreOutcome::Failed(e) => self.refresh_ended(Err(e)),
                _ => self.refresh_ended(Err(unexpected())),
            },
            Refresh::Listing { now, .. } => match outcome {
                StoreOutcome::Listed(keys) => {
                    let mut nodes = BTreeMap::new();
                    nodes.insert(self.node.members.me.id.clone(), self.node.members.me.clone());
                    let mut pending = HashSet::new();
                    for key in keys {
                        if self.keys.node_of_key(&key).as_deref() == Some(self.node.members.me.id.as_str()) {
                            continue;
                        }
                        pending.insert(self.store(StoreCall::Get { key }, Owner::Members));
                    }
                    if pending.is_empty() {
                        self.read_configuration(nodes);
                    } else {
                        self.node.members.refresh = Some(Refresh::Reading { pending, nodes, now, failed: None });
                    }
                }
                StoreOutcome::Failed(e) => self.refresh_ended(Err(e)),
                _ => self.refresh_ended(Err(unexpected())),
            },
            Refresh::Reading { mut pending, mut nodes, now, mut failed } => {
                pending.remove(&op);
                match outcome {
                    StoreOutcome::Got(Some((bytes, _))) => {
                        if let Ok(a) = serde_json::from_slice::<Announcement>(&bytes) {
                            self.node.fleet_at = self.node.fleet_at.max(a.at);
                            if a.at + self.node.members.ttl >= now {
                                nodes.insert(a.id.clone(), a);
                            } else if a.at + 2 * self.node.members.ttl < now {
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
                    self.node.members.refresh = Some(Refresh::Reading { pending, nodes, now, failed });
                } else if let Some(e) = failed {
                    self.refresh_ended(Err(e));
                } else {
                    self.read_configuration(nodes);
                }
            }
            Refresh::Config { nodes, .. } => match outcome {
                StoreOutcome::Got(read) => {
                    let (config, etag) = match read {
                        Some((bytes, etag)) => (serde_json::from_slice::<Configuration>(&bytes).unwrap_or_default(), Some(etag)),
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
                    self.note(Note::ConfigurationWritten { epoch: next.epoch, members: next.members });
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
        let op = self.store(StoreCall::Get { key: self.keys.members_key() }, Owner::Members);
        self.node.members.refresh = Some(Refresh::Config { op, nodes });
    }

    fn take_on(&mut self, config: Configuration, etag: Option<Etag>, nodes: BTreeMap<String, Announcement>) {
        let now = self.now();
        let changed = !(self.node.core.read_any && self.node.core.epoch == config.epoch);
        if changed {
            self.note(Note::ConfigurationRead { epoch: config.epoch, members: config.members.clone() });
        }
        self.node.core.read_config(now, config.epoch, config.members.clone());
        self.node.members.nodes = nodes.clone();
        self.node.members.etag = etag.clone();
        if changed {
            self.note(Note::ConfigurationChange);
            // Ownership moved: every node's share of the deadlines did.
            self.timers_membership_changed();
        }
        // The announced set is the members the configuration should name.
        // Any node may write the next epoch; a lost race is read next time.
        let live: Vec<String> = nodes.keys().cloned().collect();
        if live != config.members {
            let next = Configuration { epoch: config.epoch + 1, members: live };
            let body = serde_json::to_vec(&next).expect("a configuration serialises");
            let key = self.keys.members_key();
            let call = match etag {
                Some(etag) => StoreCall::PutIfMatch { key, body, etag },
                None => StoreCall::PutIfNoneMatch { key, body },
            };
            let op = self.store(call, Owner::Members);
            self.node.members.refresh = Some(Refresh::Writing { op, next });
        } else {
            self.refresh_ended(Ok(()));
        }
    }

    fn refresh_ended(&mut self, r: Result<(), StoreError>) {
        self.node.members.refresh = None;
        let now = self.now();
        self.note(Note::MembershipRefresh { ok: r.is_ok() });
        match r {
            Ok(()) => {
                if !self.node.members.read_once {
                    self.node.members.read_once = true;
                    self.timers_start(now);
                }
            }
            Err(e) => self.note(Note::RefreshFailed { error: e.to_string() }),
        }
        self.node.members.next_heartbeat = Some(now + self.node.members.heartbeat_ms);
        if self.node.members.leave_pending {
            self.node.members.leave_pending = false;
            self.leave();
        } else if self.loops {
            self.timers_run(now);
        }
    }
}

fn unexpected() -> StoreError {
    StoreError::Unavailable("the store answered something else".into())
}
