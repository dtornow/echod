//! The announcement, the membership, and whether this process owns a target.
//!
//! A refresh is one announcement, the list of the others, a read of the
//! configuration, and a write of the next epoch when the announced set has
//! moved. Ownership is the proved core's, over the members it was given.

use vstd::prelude::*;

use crate::verified::table::Table;
use crate::verified::text::copy_string;

use crate::handler_docs::take_opt;
use crate::state::{Owner, State};
use crate::state_node::{announcement_bytes, configuration_bytes, copy_members, parse_announcement, parse_configuration, same_members, Configuration, Refresh, Roster};
use crate::types::*;

#[cfg(verus_keep_ghost)]
use crate::handler_timers::*;
#[cfg(verus_keep_ghost)]
use crate::keys::*;
#[cfg(verus_keep_ghost)]
use crate::state::*;
#[cfg(verus_keep_ghost)]
use crate::state_node::*;
#[cfg(verus_keep_ghost)]
use crate::verified::node_spec::spec_read_config;
#[cfg(verus_keep_ghost)]
use crate::concrete::store::{EtagSpec, StoreErrorSpec, StoreReqSpec};

verus! {

// ---------------------------------------------------------------------------
// Stated
// ---------------------------------------------------------------------------

pub open spec fn spec_with_members(s: S, m: MembersSpec) -> S {
    S { node: NodeSpec { members: m, ..s.node }, ..s }
}

/// Announce this node, list the others, read the configuration, and write
/// the next epoch if the announced set has moved away from it.
#[verifier::opaque]
pub open spec fn spec_members_refresh(s: S, now: u64) -> S {
    if s.node.members.refreshing() {
        s
    } else {
        let me = AnnouncementSpec { at: now, ..s.node.members.me };
        let s = spec_with_members(s, MembersSpec { me, ..s.node.members });
        let body = spec_announcement_bytes(me);
        let key = spec_node_key(s.keys.prefix, me.id);
        let (s, op) = spec_store(s, StoreReqSpec::Put { key, body }, Owner::Members);
        spec_with_members(s, MembersSpec { refresh: Some(RefreshSpec::Announcing { op, now }), ..s.node.members })
    }
}

#[verifier::opaque]
pub open spec fn spec_members_tick(s: S, now: u64) -> S {
    let due = match s.node.members.next_heartbeat {
        Some(t) => t <= now,
        None => true,
    };
    if !s.node.members.refreshing() && due { spec_members_refresh(s, now) } else { s }
}

/// A `Get` for every node listed but this one; `pending` collects the ops.
pub open spec fn spec_read_nodes(s: S, keys: Seq<Seq<char>>, pending: Map<OpId, bool>) -> (S, Map<OpId, bool>)
    decreases keys.len(),
{
    if keys.len() == 0 {
        (s, pending)
    } else {
        let key = keys[0];
        let (s, pending) = if spec_node_of_key(s.keys.prefix, key) == Some(s.node.members.me.id) {
            (s, pending)
        } else {
            let (s, op) = spec_store(s, StoreReqSpec::Get { key }, Owner::Members);
            (s, pending.insert(op, true))
        };
        spec_read_nodes(s, keys.drop_first(), pending)
    }
}

#[verifier::opaque]
pub open spec fn spec_members_completed(s: S, op: OpId, outcome: StoreRes) -> S {
    match s.node.members.refresh {
        None => s,
        Some(refresh) => {
            if !refresh.expects(op) {
                s
            } else {
                let s = spec_with_members(s, MembersSpec { refresh: None, ..s.node.members });
                match refresh {
                    RefreshSpec::Announcing { now, .. } => spec_announced(s, now, outcome),
                    RefreshSpec::Listing { now, .. } => spec_listed(s, now, outcome),
                    RefreshSpec::Reading { pending, nodes, now, failed } => spec_read_one(s, pending.remove(op), nodes, now, failed, outcome),
                    RefreshSpec::Config { nodes, .. } => spec_configured(s, nodes, outcome),
                    RefreshSpec::Writing { next, .. } => spec_written(s, next, outcome),
                }
            }
        },
    }
}

/// Announced: list the nodes.
#[verifier::opaque]
pub open spec fn spec_announced(s: S, now: u64, outcome: StoreRes) -> S {
    match outcome {
        StoreRes::Put { result: Ok(()) } => {
            let (s, op) = spec_store(s, StoreReqSpec::List { prefix: spec_node_prefix(s.keys.prefix), max_keys: 10_000 }, Owner::Members);
            spec_with_members(s, MembersSpec { refresh: Some(RefreshSpec::Listing { op, now }), ..s.node.members })
        },
        StoreRes::Put { result: Err(e) } => spec_refresh_ended(s, Err(e.deep_view())),
        _ => spec_refresh_ended(s, Err(spec_unexpected())),
    }
}

/// Listed: read every node's announcement, this node's known already.
#[verifier::opaque]
pub open spec fn spec_listed(s: S, now: u64, outcome: StoreRes) -> S {
    match outcome {
        StoreRes::List { result: Ok(keys) } => {
            let nodes = RosterSpec { entries: spec_roster_insert(Seq::empty(), s.node.members.me.id, s.node.members.me) };
            let (s, pending) = spec_read_nodes(s, keys.deep_view(), Map::empty());
            if pending =~= Map::<OpId, bool>::empty() {
                spec_read_configuration(s, nodes)
            } else {
                spec_with_members(s, MembersSpec { refresh: Some(RefreshSpec::Reading { pending, nodes, now, failed: None }), ..s.node.members })
            }
        },
        StoreRes::List { result: Err(e) } => spec_refresh_ended(s, Err(e.deep_view())),
        _ => spec_refresh_ended(s, Err(spec_unexpected())),
    }
}

/// One announcement read: a live node joins the roster, a long dead one
/// is collected, anything unreadable is not a node.
#[verifier::opaque]
pub open spec fn spec_read_one(s: S, pending: Map<OpId, bool>, nodes: RosterSpec, now: u64, failed: Option<StoreErrorSpec>, outcome: StoreRes) -> S {
    let (s, nodes, failed) = match outcome {
        StoreRes::Get { result: Ok(Some((bytes, _))) } => match spec_parse_announcement(bytes@) {
            Some(a) => {
                let fleet_at = if s.node.fleet_at > a.at { s.node.fleet_at } else { a.at };
                let s = S { node: NodeSpec { fleet_at, ..s.node }, ..s };
                if a.at.saturating_add(s.node.members.ttl) >= now {
                    (s, RosterSpec { entries: spec_roster_insert(nodes.entries, a.id, a) }, failed)
                } else if a.at.saturating_add((2 as u64).saturating_mul(s.node.members.ttl)) < now {
                    let key = spec_node_key(s.keys.prefix, a.id);
                    let (s, _op) = spec_store(s, StoreReqSpec::Del { key }, Owner::Ignored);
                    (s, nodes, failed)
                } else {
                    (s, nodes, failed)
                }
            },
            None => (s, nodes, failed),
        },
        StoreRes::Get { result: Ok(None) } => (s, nodes, failed),
        StoreRes::Get { result: Err(e) } => (s, nodes, Some(e.deep_view())),
        _ => (s, nodes, Some(spec_unexpected())),
    };
    if !(pending =~= Map::<OpId, bool>::empty()) {
        spec_with_members(s, MembersSpec { refresh: Some(RefreshSpec::Reading { pending, nodes, now, failed }), ..s.node.members })
    } else {
        match failed {
            Some(e) => spec_refresh_ended(s, Err(e)),
            None => spec_read_configuration(s, nodes),
        }
    }
}

/// The configuration read: take it on.
#[verifier::opaque]
pub open spec fn spec_configured(s: S, nodes: RosterSpec, outcome: StoreRes) -> S {
    match outcome {
        StoreRes::Get { result: Ok(read) } => {
            let (config, etag) = match read {
                Some((bytes, etag)) => (spec_parse_configuration(bytes@), Some(etag.deep_view())),
                None => (ConfigurationSpec { epoch: 0, members: Seq::empty() }, None),
            };
            spec_take_on(s, config, etag, nodes)
        },
        StoreRes::Get { result: Err(e) } => spec_refresh_ended(s, Err(e.deep_view())),
        _ => spec_refresh_ended(s, Err(spec_unexpected())),
    }
}

/// The configuration written, or not.
#[verifier::opaque]
pub open spec fn spec_written(s: S, next: ConfigurationSpec, outcome: StoreRes) -> S {
    match outcome {
        StoreRes::PutIfMatch { result: Ok(_) } | StoreRes::PutIfNoneMatch { result: Ok(_) } => {
            let s = spec_note(s, NoteSpec::ConfigurationWrite(ConfigWrite::Written));
            let s = spec_note(s, NoteSpec::ConfigurationWritten { epoch: next.epoch, members: next.members });
            spec_refresh_ended(s, Ok(()))
        },
        StoreRes::PutIfMatch { result: Err(StoreError::PreconditionFailed) }
        | StoreRes::PutIfNoneMatch { result: Err(StoreError::PreconditionFailed) } => {
            let s = spec_note(s, NoteSpec::ConfigurationWrite(ConfigWrite::Conflict));
            spec_refresh_ended(s, Ok(()))
        },
        StoreRes::PutIfMatch { result: Err(e) } | StoreRes::PutIfNoneMatch { result: Err(e) } => {
            let s = spec_note(s, NoteSpec::ConfigurationWrite(ConfigWrite::Failed));
            spec_refresh_ended(s, Err(e.deep_view()))
        },
        _ => spec_refresh_ended(s, Err(spec_unexpected())),
    }
}

/// The configuration: read it, and take it on.
#[verifier::opaque]
pub open spec fn spec_read_configuration(s: S, nodes: RosterSpec) -> S {
    let (s, op) = spec_store(s, StoreReqSpec::Get { key: spec_members_key(s.keys.prefix) }, Owner::Members);
    spec_with_members(s, MembersSpec { refresh: Some(RefreshSpec::Config { op, nodes }), ..s.node.members })
}

#[verifier::opaque]
pub open spec fn spec_take_on(s: S, config: ConfigurationSpec, etag: Option<EtagSpec>, nodes: RosterSpec) -> S {
    let now = spec_now(s);
    let changed = !(s.node.core.read_any && s.node.core.epoch == config.epoch as nat);
    let s = if changed { spec_note(s, NoteSpec::ConfigurationRead { epoch: config.epoch, members: config.members }) } else { s };
    let core = spec_read_config(s.node.core, now as nat, config.epoch as nat, config.members);
    let s = S { node: NodeSpec { core, members: MembersSpec { nodes, etag, ..s.node.members }, ..s.node }, ..s };
    let s = if changed {
        let s = spec_note(s, NoteSpec::ConfigurationChange);
        spec_timers_membership_changed(s)
    } else {
        s
    };
    spec_write_members(s, config, etag, nodes)
}

/// The announced set is the members the configuration should name. Any
/// node may write the next epoch; a lost race is read next time.
#[verifier::opaque]
pub open spec fn spec_write_members(s: S, config: ConfigurationSpec, etag: Option<EtagSpec>, nodes: RosterSpec) -> S {
    let live = spec_roster_ids(nodes.entries);
    if live != config.members {
        let next = ConfigurationSpec { epoch: config.epoch.saturating_add(1), members: live };
        let body = spec_configuration_bytes(next);
        let key = spec_members_key(s.keys.prefix);
        let call = match etag {
            Some(etag) => StoreReqSpec::PutIfMatch { key, body, etag },
            None => StoreReqSpec::PutIfNoneMatch { key, body },
        };
        let (s, op) = spec_store(s, call, Owner::Members);
        spec_with_members(s, MembersSpec { refresh: Some(RefreshSpec::Writing { op, next }), ..s.node.members })
    } else {
        spec_refresh_ended(s, Ok(()))
    }
}

/// A refresh's end, as the specification sees it.
pub open spec fn spec_ended(r: Result<(), StoreError>) -> Result<(), StoreErrorSpec> {
    match r {
        Ok(()) => Ok(()),
        Err(e) => Err(e.deep_view()),
    }
}

#[verifier::opaque]
pub open spec fn spec_refresh_ended(s: S, r: Result<(), StoreErrorSpec>) -> S {
    let s = spec_with_members(s, MembersSpec { refresh: None, ..s.node.members });
    let now = spec_now(s);
    let s = spec_note(s, NoteSpec::MembershipRefresh { ok: r is Ok });
    let s = match r {
        Ok(()) => {
            if !s.node.members.read_once {
                spec_timers_start(spec_with_members(s, MembersSpec { read_once: true, ..s.node.members }), now)
            } else {
                s
            }
        },
        Err(e) => spec_note(s, NoteSpec::RefreshFailed { error: spec_error_text(e) }),
    };
    let s = spec_with_members(s, MembersSpec { next_heartbeat: Some(now.saturating_add(s.node.members.heartbeat_ms)), ..s.node.members });
    if s.loops {
        spec_timers_run(s, now)
    } else {
        s
    }
}

// ---------------------------------------------------------------------------
// Run
// ---------------------------------------------------------------------------

impl State {
    /// Announce this node, list the others, read the configuration, and
    /// write the next epoch if the announced set has moved away from it.
    pub fn members_refresh(&mut self, now: u64)
        ensures
            final(self).deep_view() == spec_members_refresh(old(self).deep_view(), now),
    {
        proof {
            reveal(spec_members_refresh);
        }
        if self.node.members.refreshing() {
            return;
        }
        self.node.members.me.at = now;
        let body = announcement_bytes(&self.node.members.me);
        let key = self.keys.node_key(self.node.members.me.id.as_str());
        let op = self.store(StoreReq::Put { key, body }, Owner::Members);
        self.node.members.refresh = Some(Refresh::Announcing { op, now });
    }

    pub fn members_tick(&mut self, now: u64)
        ensures
            final(self).deep_view() == spec_members_tick(old(self).deep_view(), now),
    {
        proof {
            reveal(spec_members_tick);
        }
        let due = match self.node.members.next_heartbeat {
            Some(t) => t <= now,
            None => true,
        };
        if !self.node.members.refreshing() && due {
            self.members_refresh(now);
        }
    }

    /// A `Get` for every node listed but this one.
    fn read_nodes(&mut self, keys: &Vec<String>, pending: &mut Table<OpId, bool>)
        ensures
            (final(self).deep_view(), final(pending).deep_view()) == spec_read_nodes(old(self).deep_view(), keys.deep_view(), old(pending).deep_view()),
    {
        let ghost ks = keys.deep_view();
        let ghost s0 = old(self).deep_view();
        let ghost p0 = old(pending).deep_view();
        let mut i: usize = 0;
        proof {
            assert(ks.skip(0) =~= ks);
        }
        while i < keys.len()
            invariant
                i <= keys.len(),
                ks == keys.deep_view(),
                spec_read_nodes(s0, ks, p0) == spec_read_nodes(self.deep_view(), ks.skip(i as int), pending.deep_view()),
            decreases keys.len() - i,
        {
            proof {
                assert(ks.skip(i as int).drop_first() =~= ks.skip(i as int + 1));
                assert(ks.skip(i as int)[0] == ks[i as int]);
            }
            let key = copy_string(&keys[i]);
            let mine = match self.keys.node_of_key(key.as_str()) {
                Some(id) => crate::verified::node::str_eq(id.as_str(), self.node.members.me.id.as_str()),
                None => false,
            };
            if !mine {
                let op = self.store(StoreReq::Get { key }, Owner::Members);
                pending.insert(op, true);
            }
            i += 1;
        }
        proof {
            assert(ks.skip(i as int) =~= Seq::<Seq<char>>::empty());
        }
    }

    pub fn members_completed(&mut self, op: OpId, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_members_completed(old(self).deep_view(), op, outcome),
    {
        proof {
            reveal(spec_members_completed);
        }
        let refresh = match take_opt(&mut self.node.members.refresh) {
            Some(r) => r,
            None => return,
        };
        if !refresh.expects(op) {
            self.node.members.refresh = Some(refresh);
            return;
        }
        match refresh {
            Refresh::Announcing { now, .. } => self.announced(now, outcome),
            Refresh::Listing { now, .. } => self.listed(now, outcome),
            Refresh::Reading { mut pending, nodes, now, failed } => {
                pending.remove(&op);
                self.read_one(pending, nodes, now, failed, outcome);
            },
            Refresh::Config { nodes, .. } => self.configured(nodes, outcome),
            Refresh::Writing { next, .. } => self.written(next, outcome),
        }
    }

    /// Announced: list the nodes.
    fn announced(&mut self, now: u64, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_announced(old(self).deep_view(), now, outcome),
    {
        proof {
            reveal(spec_announced);
        }
        match outcome {
            StoreRes::Put { result: Ok(()) } => {
                let prefix = self.keys.node_prefix();
                let op = self.store(StoreReq::List { prefix, max_keys: 10_000 }, Owner::Members);
                self.node.members.refresh = Some(Refresh::Listing { op, now });
            },
            StoreRes::Put { result: Err(e) } => self.refresh_ended(Err(e)),
            _ => self.refresh_ended(Err(unexpected())),
        }
    }

    /// Listed: read every node's announcement, this node's known already.
    fn listed(&mut self, now: u64, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_listed(old(self).deep_view(), now, outcome),
    {
        proof {
            reveal(spec_listed);
        }
        match outcome {
            StoreRes::List { result: Ok(keys) } => {
                let mut nodes = Roster::new();
                nodes.insert(copy_string(&self.node.members.me.id), self.node.members.me.copy());
                let mut pending: Table<OpId, bool> = Table::new();
                self.read_nodes(&keys, &mut pending);
                if pending.is_empty() {
                    self.read_configuration(nodes);
                } else {
                    self.node.members.refresh = Some(Refresh::Reading { pending, nodes, now, failed: None });
                }
            },
            StoreRes::List { result: Err(e) } => self.refresh_ended(Err(e)),
            _ => self.refresh_ended(Err(unexpected())),
        }
    }

    /// One announcement read: a live node joins the roster, a long dead one
    /// is collected, anything unreadable is not a node.
    fn read_one(&mut self, pending: Table<OpId, bool>, mut nodes: Roster, now: u64, failed: Option<StoreError>, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_read_one(old(self).deep_view(), pending@, nodes.deep_view(), now, failed.deep_view(), outcome),
    {
        proof {
            reveal(spec_read_one);
        }
        let failed = match outcome {
            StoreRes::Get { result: Ok(Some((bytes, _))) } => {
                if let Some(a) = parse_announcement(bytes.as_slice()) {
                    if a.at > self.node.fleet_at {
                        self.node.fleet_at = a.at;
                    }
                    if a.at.saturating_add(self.node.members.ttl) >= now {
                        nodes.insert(copy_string(&a.id), a);
                    } else if a.at.saturating_add((2 as u64).saturating_mul(self.node.members.ttl)) < now {
                        // Long dead: collect it. A node that is merely slow writes again.
                        let key = self.keys.node_key(a.id.as_str());
                        self.store(StoreReq::Del { key }, Owner::Ignored);
                    }
                }
                failed
            },
            StoreRes::Get { result: Ok(None) } => failed,
            StoreRes::Get { result: Err(e) } => Some(e),
            _ => Some(unexpected()),
        };
        if !pending.is_empty() {
            self.node.members.refresh = Some(Refresh::Reading { pending, nodes, now, failed });
        } else {
            match failed {
                Some(e) => self.refresh_ended(Err(e)),
                None => self.read_configuration(nodes),
            }
        }
    }

    /// The configuration read: take it on.
    fn configured(&mut self, nodes: Roster, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_configured(old(self).deep_view(), nodes.deep_view(), outcome),
    {
        proof {
            reveal(spec_configured);
        }
        match outcome {
            StoreRes::Get { result: Ok(read) } => {
                let (config, etag) = match read {
                    Some((bytes, etag)) => (parse_configuration(bytes.as_slice()), Some(etag)),
                    None => {
                        let empty = Configuration { epoch: 0, members: Vec::new() };
                        proof {
                            assert(empty.deep_view().members =~= Seq::<Seq<char>>::empty());
                        }
                        (empty, None)
                    },
                };
                self.take_on(config, etag, nodes);
            },
            StoreRes::Get { result: Err(e) } => self.refresh_ended(Err(e)),
            _ => self.refresh_ended(Err(unexpected())),
        }
    }

    /// The configuration written, or not.
    fn written(&mut self, next: Configuration, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_written(old(self).deep_view(), next.deep_view(), outcome),
    {
        proof {
            reveal(spec_written);
        }
        match outcome {
            StoreRes::PutIfMatch { result: Ok(_) } | StoreRes::PutIfNoneMatch { result: Ok(_) } => {
                self.note(Note::ConfigurationWrite(ConfigWrite::Written));
                let Configuration { epoch, members } = next;
                self.note(Note::ConfigurationWritten { epoch, members });
                self.refresh_ended(Ok(()));
            },
            StoreRes::PutIfMatch { result: Err(StoreError::PreconditionFailed) }
            | StoreRes::PutIfNoneMatch { result: Err(StoreError::PreconditionFailed) } => {
                // A lost race is read next time.
                self.note(Note::ConfigurationWrite(ConfigWrite::Conflict));
                self.refresh_ended(Ok(()));
            },
            StoreRes::PutIfMatch { result: Err(e) } | StoreRes::PutIfNoneMatch { result: Err(e) } => {
                self.note(Note::ConfigurationWrite(ConfigWrite::Failed));
                self.refresh_ended(Err(e));
            },
            _ => self.refresh_ended(Err(unexpected())),
        }
    }

    /// The configuration: read it, and take it on.
    fn read_configuration(&mut self, nodes: Roster)
        ensures
            final(self).deep_view() == spec_read_configuration(old(self).deep_view(), nodes.deep_view()),
    {
        proof {
            reveal(spec_read_configuration);
        }
        let key = self.keys.members_key();
        let op = self.store(StoreReq::Get { key }, Owner::Members);
        self.node.members.refresh = Some(Refresh::Config { op, nodes });
    }

    fn take_on(&mut self, config: Configuration, etag: Option<Etag>, nodes: Roster)
        ensures
            final(self).deep_view() == spec_take_on(old(self).deep_view(), config.deep_view(), etag.deep_view(), nodes.deep_view()),
    {
        proof {
            reveal(spec_take_on);
        }
        let now = self.now();
        let changed = !(self.node.core.read_any && self.node.core.epoch == config.epoch);
        if changed {
            self.note(Note::ConfigurationRead { epoch: config.epoch, members: copy_members(&config.members) });
        }
        self.node.core.read_config(now, config.epoch, copy_members(&config.members));
        self.node.members.nodes = nodes.copy();
        self.node.members.etag = match &etag {
            Some(e) => Some(Etag(copy_string(&e.0))),
            None => None,
        };
        if changed {
            self.note(Note::ConfigurationChange);
            // Ownership moved: every node's share of the deadlines did.
            self.timers_membership_changed();
        }
        self.write_members(config, etag, nodes);
    }

    /// The announced set is the members the configuration should name.
    /// Any node may write the next epoch; a lost race is read next time.
    fn write_members(&mut self, config: Configuration, etag: Option<Etag>, nodes: Roster)
        ensures
            final(self).deep_view() == spec_write_members(old(self).deep_view(), config.deep_view(), etag.deep_view(), nodes.deep_view()),
    {
        proof {
            reveal(spec_write_members);
        }
        let live: Vec<String> = nodes.ids();
        if !same_members(&live, &config.members) {
            let next = Configuration { epoch: config.epoch.saturating_add(1), members: live };
            let body = configuration_bytes(&next);
            let key = self.keys.members_key();
            let call = match etag {
                Some(etag) => StoreReq::PutIfMatch { key, body, etag },
                None => StoreReq::PutIfNoneMatch { key, body },
            };
            let op = self.store(call, Owner::Members);
            self.node.members.refresh = Some(Refresh::Writing { op, next });
        } else {
            self.refresh_ended(Ok(()));
        }
    }

    fn refresh_ended(&mut self, r: Result<(), StoreError>)
        ensures
            final(self).deep_view() == spec_refresh_ended(old(self).deep_view(), spec_ended(r)),
    {
        proof {
            reveal(spec_refresh_ended);
        }
        self.node.members.refresh = None;
        let now = self.now();
        let ok = match &r {
            Ok(_) => true,
            Err(_) => false,
        };
        self.note(Note::MembershipRefresh { ok });
        match r {
            Ok(()) => {
                if !self.node.members.read_once {
                    self.node.members.read_once = true;
                    self.timers_start(now);
                }
            },
            Err(e) => self.note(Note::RefreshFailed { error: error_text(&e) }),
        }
        self.node.members.next_heartbeat = Some(now.saturating_add(self.node.members.heartbeat_ms));
        if self.loops {
            self.timers_run(now);
        }
    }
}

} // verus!
