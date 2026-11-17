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

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_handler_node_spec_with_members as spec_with_members,
    production_handler_node_spec_members_refresh as spec_members_refresh,
    production_handler_node_spec_members_tick as spec_members_tick,
    production_handler_node_spec_read_nodes as spec_read_nodes,
    production_handler_node_spec_members_completed as spec_members_completed,
    production_handler_node_spec_announced as spec_announced,
    production_handler_node_spec_listed as spec_listed,
    production_handler_node_spec_read_one as spec_read_one,
    production_handler_node_spec_configured as spec_configured,
    production_handler_node_spec_written as spec_written,
    production_handler_node_spec_read_configuration as spec_read_configuration,
    production_handler_node_spec_take_on as spec_take_on,
    production_handler_node_spec_write_members as spec_write_members,
    production_handler_node_spec_ended as spec_ended,
    production_handler_node_spec_refresh_ended as spec_refresh_ended,
};

verus! {

// ---------------------------------------------------------------------------
// Stated
// ---------------------------------------------------------------------------



/// Announce this node, list the others, read the configuration, and write
/// the next epoch if the announced set has moved away from it.




/// A `Get` for every node listed but this one; `pending` collects the ops.




/// Announced: list the nodes.


/// Listed: read every node's announcement, this node's known already.


/// One announcement read: a live node joins the roster, a long dead one
/// is collected, anything unreadable is not a node.


/// The configuration read: take it on.


/// The configuration written, or not.


/// The configuration: read it, and take it on.




/// The announced set is the members the configuration should name. Any
/// node may write the next epoch; a lost race is read next time.


/// A refresh's end, as the specification sees it.




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
