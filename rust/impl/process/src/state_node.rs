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
//!
//! The announced set is a `Roster`: announcements in id order, so that the
//! members a node writes are in the order every node computes ownership
//! over. The bytes of an announcement and of the configuration are
//! `codec`, plain Rust over serde, stated once each.


use vstd::prelude::*;

use crate::concrete::store::before;

use crate::types::*;
use crate::verified::node::{str_eq, NodeCore};
use crate::verified::table::Table;
use crate::verified::text::copy_string;
use crate::Config;

#[cfg(verus_keep_ghost)]
use crate::concrete::store::{spec_before, EtagSpec, StoreErrorSpec};
#[cfg(verus_keep_ghost)]
use crate::verified::node_spec::ANode;

#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionAnnouncementV as AnnouncementSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionConfigurationV as ConfigurationSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionRosterV as RosterSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionMembersV as MembersSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionNodeStateV as NodeSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionRefreshV as RefreshSpec;

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_state_node_spec_roster_insert as spec_roster_insert,
    production_state_node_spec_roster_ids as spec_roster_ids,
    production_state_node_spec_members_new as spec_members_new,
    production_state_node_spec_node_new as spec_node_new,
    production_state_node_spec_announcement_bytes as spec_announcement_bytes,
    production_state_node_spec_parse_announcement as spec_parse_announcement,
    production_state_node_spec_configuration_bytes as spec_configuration_bytes,
    production_state_node_spec_parse_configuration as spec_parse_configuration,
};

verus! {
#[cfg(verus_keep_ghost)]
impl DeepView for Announcement {
    type V = AnnouncementSpec;
    open spec fn deep_view(&self) -> AnnouncementSpec {
        AnnouncementSpec {
            id: self.id.deep_view(),
            url: self.url.deep_view(),
            at: self.at.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Announcement {
    type V = AnnouncementSpec;
    open spec fn view(&self) -> AnnouncementSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Configuration {
    type V = ConfigurationSpec;
    open spec fn deep_view(&self) -> ConfigurationSpec {
        ConfigurationSpec {
            epoch: self.epoch.deep_view(),
            members: self.members.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Configuration {
    type V = ConfigurationSpec;
    open spec fn view(&self) -> ConfigurationSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Roster {
    type V = RosterSpec;
    open spec fn deep_view(&self) -> RosterSpec {
        RosterSpec {
            entries: self.entries.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Roster {
    type V = RosterSpec;
    open spec fn view(&self) -> RosterSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Members {
    type V = MembersSpec;
    open spec fn deep_view(&self) -> MembersSpec {
        MembersSpec {
            me: self.me.deep_view(),
            heartbeat_ms: self.heartbeat_ms.deep_view(),
            ttl: self.ttl.deep_view(),
            nodes: self.nodes.deep_view(),
            etag: self.etag.deep_view(),
            next_heartbeat: self.next_heartbeat.deep_view(),
            refresh: self.refresh.deep_view(),
            read_once: self.read_once.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Members {
    type V = MembersSpec;
    open spec fn view(&self) -> MembersSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Node {
    type V = NodeSpec;
    open spec fn deep_view(&self) -> NodeSpec {
        NodeSpec {
            core: self.core.deep_view(),
            members: self.members.deep_view(),
            fleet_at: self.fleet_at.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Node {
    type V = NodeSpec;
    open spec fn view(&self) -> NodeSpec { self.deep_view() }
}
#[derive(Debug, Clone, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]


pub struct Announcement {
    pub id: String,
    pub url: String,
    /// The instant of the latest announcement, ms.
    pub at: u64,
}

impl Announcement {
    pub fn copy(&self) -> (r: Announcement)
        ensures
            r == *self,
    {
        Announcement { id: copy_string(&self.id), url: copy_string(&self.url), at: self.at }
    }
}

/// The configuration object: the members, and the epoch it was written in.
#[derive(Debug, Clone, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize, Default))]
pub struct Configuration {
    pub epoch: u64,
    pub members: Vec<String>,
}

// ---------------------------------------------------------------------------
// The roster: announcements in id order
// ---------------------------------------------------------------------------

pub type Announced = (String, Announcement);
#[cfg(verus_keep_ghost)]
pub type AnnouncedSpec = (Seq<char>, AnnouncementSpec);

pub struct Roster {
    pub entries: Vec<Announced>,
}

/// `id, a` filed in id order, in place of any announcement under `id`.


/// The ids, in order.


proof fn lemma_roster_insert_step(s: Seq<AnnouncedSpec>, id: Seq<char>, a: AnnouncementSpec, i: int)
    requires
        0 <= i <= s.len(),
        forall|j: int| 0 <= j < i ==> (#[trigger] s[j]).0 != id && !spec_before(id, s[j].0),
    ensures
        spec_roster_insert(s, id, a) == s.take(i) + spec_roster_insert(s.skip(i), id, a),
    decreases i,
{
    if i == 0 {
        assert(s.skip(0) =~= s);
        assert(s.take(0) + spec_roster_insert(s, id, a) =~= spec_roster_insert(s, id, a));
    } else {
        lemma_roster_insert_step(s, id, a, i - 1);
        let rest = s.skip(i - 1);
        assert(rest.drop_first() =~= s.skip(i));
        assert(rest[0] == s[i - 1]);
        assert(s.take(i - 1) + (seq![s[i - 1]] + spec_roster_insert(s.skip(i), id, a)) =~= s.take(i) + spec_roster_insert(s.skip(i), id, a));
    }
}

impl Roster {
    pub fn new() -> (r: Roster)
        ensures
            r.deep_view().entries == Seq::<AnnouncedSpec>::empty(),
    {
        let r = Roster { entries: Vec::new() };
        proof {
            assert(r.entries.deep_view() =~= Seq::<AnnouncedSpec>::empty());
        }
        r
    }

    /// File `a` under `id`, in place of any announcement under it.
    pub fn insert(&mut self, id: String, a: Announcement)
        ensures
            final(self).deep_view().entries == spec_roster_insert(old(self).deep_view().entries, id@, a.deep_view()),
    {
        let ghost s = self.entries.deep_view();
        let ghost av = a.deep_view();
        let ghost idv = id@;
        let mut i = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                s == self.entries.deep_view(),
                s == old(self).deep_view().entries,
                id@ == idv,
                a.deep_view() == av,
                forall|j: int| 0 <= j < i ==> (#[trigger] s[j]).0 != idv && !spec_before(idv, s[j].0),
            decreases self.entries.len() - i,
        {
            if str_eq(self.entries[i].0.as_str(), id.as_str()) {
                proof {
                    lemma_roster_insert_step(s, idv, av, i as int);
                    assert(s.skip(i as int)[0] == s[i as int]);
                    assert(s.skip(i as int).drop_first() =~= s.skip(i as int + 1));
                }
                self.entries.set(i, (id, a));
                proof {
                    assert(self.entries.deep_view() =~= s.take(i as int) + (seq![(idv, av)] + s.skip(i as int + 1)));
                }
                return;
            }
            if before(&id, &self.entries[i].0) {
                proof {
                    lemma_roster_insert_step(s, idv, av, i as int);
                    assert(s.skip(i as int)[0] == s[i as int]);
                }
                self.entries.insert(i, (id, a));
                proof {
                    assert(self.entries.deep_view() =~= s.take(i as int) + (seq![(idv, av)] + s.skip(i as int)));
                }
                return;
            }
            i += 1;
        }
        proof {
            lemma_roster_insert_step(s, idv, av, i as int);
            assert(s.skip(i as int).len() == 0);
        }
        self.entries.push((id, a));
        proof {
            assert(self.entries.deep_view() =~= s.take(i as int) + seq![(idv, av)]);
        }
    }

    /// The ids, in order: the members the configuration should name.
    pub fn ids(&self) -> (r: Vec<String>)
        ensures
            r.deep_view() == spec_roster_ids(self.deep_view().entries),
    {
        let ghost s = self.entries.deep_view();
        let mut out: Vec<String> = Vec::new();
        let mut i = 0;
        proof {
            assert(out.deep_view() =~= spec_roster_ids(s.take(0)));
        }
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                s == self.entries.deep_view(),
                out.deep_view() == spec_roster_ids(s.take(i as int)),
            decreases self.entries.len() - i,
        {
            let ghost o0 = out.deep_view();
            out.push(copy_string(&self.entries[i].0));
            proof {
                assert(out.deep_view() =~= o0.push(s[i as int].0));
                assert(spec_roster_ids(s.take(i as int + 1)) =~= spec_roster_ids(s.take(i as int)).push(s[i as int].0));
            }
            i += 1;
        }
        proof {
            assert(s.take(i as int) =~= s);
        }
        out
    }

    pub fn copy(&self) -> (r: Roster)
        ensures
            r.deep_view() == self.deep_view(),
    {
        let ghost s = self.entries.deep_view();
        let mut out: Vec<Announced> = Vec::new();
        let mut i = 0;
        proof {
            assert(out.deep_view() =~= s.take(0));
        }
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                s == self.entries.deep_view(),
                out.deep_view() == s.take(i as int),
            decreases self.entries.len() - i,
        {
            let ghost o0 = out.deep_view();
            let e = &self.entries[i];
            out.push((copy_string(&e.0), e.1.copy()));
            proof {
                assert(out.deep_view() =~= o0.push(s[i as int]));
                assert(s.take(i as int + 1) =~= s.take(i as int).push(s[i as int]));
            }
            i += 1;
        }
        proof {
            assert(s.take(i as int) =~= s);
        }
        Roster { entries: out }
    }
}

/// `a == b` on member lists.
pub fn same_members(a: &Vec<String>, b: &Vec<String>) -> (r: bool)
    ensures
        r == (a.deep_view() == b.deep_view()),
{
    proof {
        assert(a.deep_view().len() == a@.len());
        assert(b.deep_view().len() == b@.len());
    }
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> a.deep_view()[j] == b.deep_view()[j],
        decreases a.len() - i,
    {
        if !str_eq(a[i].as_str(), b[i].as_str()) {
            proof {
                assert(a.deep_view()[i as int] != b.deep_view()[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(a.deep_view() =~= b.deep_view());
    }
    true
}

pub fn copy_members(a: &Vec<String>) -> (r: Vec<String>)
    ensures
        r.deep_view() == a.deep_view(),
{
    let ghost s = a.deep_view();
    let mut out: Vec<String> = Vec::new();
    let mut i = 0;
    proof {
        assert(out.deep_view() =~= s.take(0));
    }
    while i < a.len()
        invariant
            i <= a.len(),
            s == a.deep_view(),
            out.deep_view() == s.take(i as int),
        decreases a.len() - i,
    {
        let ghost o0 = out.deep_view();
        out.push(copy_string(&a[i]));
        proof {
            assert(out.deep_view() =~= o0.push(s[i as int]));
            assert(s.take(i as int + 1) =~= s.take(i as int).push(s[i as int]));
        }
        i += 1;
    }
    proof {
        assert(s.take(i as int) =~= s);
    }
    out
}

// ---------------------------------------------------------------------------
// The refresh
// ---------------------------------------------------------------------------

/// A refresh in progress: announce, list, read each, read the
/// configuration, write the next epoch if the announced set moved.
pub enum Refresh {
    Announcing { op: OpId, now: u64 },
    Listing { op: OpId, now: u64 },
    Reading { pending: Table<OpId, bool>, nodes: Roster, now: u64, failed: Option<StoreError> },
    Config { op: OpId, nodes: Roster },
    Writing { op: OpId, next: Configuration },
}



#[cfg(verus_keep_ghost)]
impl DeepView for Refresh {
    type V = RefreshSpec;
    open spec fn deep_view(&self) -> RefreshSpec {
        match self {
            Refresh::Announcing { op, now } => RefreshSpec::Announcing { op: *op, now: *now },
            Refresh::Listing { op, now } => RefreshSpec::Listing { op: *op, now: *now },
            Refresh::Reading { pending, nodes, now, failed } => RefreshSpec::Reading { pending: pending.deep_view(), nodes: nodes.deep_view(), now: *now, failed: failed.deep_view() },
            Refresh::Config { op, nodes } => RefreshSpec::Config { op: *op, nodes: nodes.deep_view() },
            Refresh::Writing { op, next } => RefreshSpec::Writing { op: *op, next: next.deep_view() },
        }
    }
}



impl Refresh {
    pub fn expects(&self, op: OpId) -> (r: bool)
        ensures
            r == self.deep_view().expects(op),
    {
        match self {
            Refresh::Announcing { op: o, .. } | Refresh::Listing { op: o, .. } | Refresh::Config { op: o, .. } | Refresh::Writing { op: o, .. } => *o == op,
            Refresh::Reading { pending, .. } => pending.contains(&op),
        }
    }
}

pub struct Members {
    pub me: Announcement,
    pub heartbeat_ms: u64,
    pub ttl: u64,
    /// Who announced, and the version of the configuration object read.
    pub nodes: Roster,
    pub etag: Option<Etag>,
    pub next_heartbeat: Option<u64>,
    pub refresh: Option<Refresh>,
    /// The first refresh that succeeded started the timers.
    pub read_once: bool,
}





impl Members {
    pub fn new(cfg: &Config) -> (r: Members)
        ensures
            r.deep_view() == spec_members_new(cfg.deep_view()),
    {
        Members {
            me: Announcement { id: copy_string(&cfg.node_id), url: copy_string(&cfg.url), at: 0 },
            heartbeat_ms: cfg.heartbeat_ms,
            ttl: cfg.node_ttl_ms,
            nodes: Roster::new(),
            etag: None,
            next_heartbeat: None,
            refresh: None,
            read_once: false,
        }
    }

    pub fn refreshing(&self) -> (r: bool)
        ensures
            r == self.deep_view().refreshing(),
    {
        self.refresh.is_some()
    }

    pub fn wake_at(&self) -> (r: Option<u64>)
        ensures
            r == self.deep_view().wake_at(),
    {
        if self.refreshing() { None } else { self.next_heartbeat }
    }
}

/// What this process holds of the fleet: the proved membership core, the
/// refresh in progress, and the latest instant any announcement carried.
pub struct Node {
    pub core: NodeCore,
    pub members: Members,
    pub fleet_at: u64,
}



impl Node {
    pub fn new(cfg: &Config) -> (r: Node)
        ensures
            r.deep_view() == spec_node_new(cfg.deep_view()),
    {
        Node {
            core: NodeCore::new(copy_string(&cfg.node_id), cfg.node_ttl_ms),
            members: Members::new(cfg),
            fleet_at: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// The bytes, stated
// ---------------------------------------------------------------------------




/// What the configuration object says; bytes that do not parse say the
/// default: epoch 0, no members.


pub assume_specification [codec::announcement_bytes](a: &Announcement) -> (r: Vec<u8>)
    ensures
        r@ == spec_announcement_bytes(a.deep_view());

pub assume_specification [codec::parse_announcement](bytes: &[u8]) -> (r: Option<Announcement>)
    ensures
        r.deep_view() == spec_parse_announcement(bytes@);

pub assume_specification [codec::configuration_bytes](c: &Configuration) -> (r: Vec<u8>)
    ensures
        r@ == spec_configuration_bytes(c.deep_view());

pub assume_specification [codec::parse_configuration](bytes: &[u8]) -> (r: Configuration)
    ensures
        r.deep_view() == spec_parse_configuration(bytes@);

pub fn announcement_bytes(a: &Announcement) -> (r: Vec<u8>)
    ensures
        r@ == spec_announcement_bytes(a.deep_view()),
{
    codec::announcement_bytes(a)
}

pub fn parse_announcement(bytes: &[u8]) -> (r: Option<Announcement>)
    ensures
        r.deep_view() == spec_parse_announcement(bytes@),
{
    codec::parse_announcement(bytes)
}

pub fn configuration_bytes(c: &Configuration) -> (r: Vec<u8>)
    ensures
        r@ == spec_configuration_bytes(c.deep_view()),
{
    codec::configuration_bytes(c)
}

pub fn parse_configuration(bytes: &[u8]) -> (r: Configuration)
    ensures
        r.deep_view() == spec_parse_configuration(bytes@),
{
    codec::parse_configuration(bytes)
}

} // verus!

/// A snapshot of what a node holds of the membership, for whoever looks.
#[derive(Debug, Clone, Default)]
pub struct Membership {
    /// Every node announced within a TTL, as of the last listing.
    pub nodes: std::collections::BTreeMap<String, Announcement>,
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

#[cfg(not(verus_keep_ghost))]
impl Members {
    pub fn snapshot(&self, core: &NodeCore) -> Membership {
        let nodes = self.nodes.entries.iter().map(|(id, a)| (id.clone(), a.clone())).collect();
        Membership { nodes, epoch: core.epoch, members: core.members.clone(), etag: self.etag.clone(), last_read: core.last_read, read_any: core.read_any }
    }
}

#[cfg(not(verus_keep_ghost))]
pub mod codec {
    use super::{Announcement, Configuration};

    pub fn announcement_bytes(a: &Announcement) -> Vec<u8> {
        serde_json::to_vec(a).expect("an announcement serialises")
    }

    pub fn parse_announcement(bytes: &[u8]) -> Option<Announcement> {
        serde_json::from_slice::<Announcement>(bytes).ok()
    }

    pub fn configuration_bytes(c: &Configuration) -> Vec<u8> {
        serde_json::to_vec(c).expect("a configuration serialises")
    }

    pub fn parse_configuration(bytes: &[u8]) -> Configuration {
        serde_json::from_slice::<Configuration>(bytes).unwrap_or_default()
    }
}

/// Under Verus the bytes are stated, never built: serde is absent there.
#[cfg(verus_keep_ghost)]
pub mod codec {
    use super::{Announcement, Configuration};

    pub fn announcement_bytes(_a: &Announcement) -> Vec<u8> {
        unimplemented!()
    }

    pub fn parse_announcement(_bytes: &[u8]) -> Option<Announcement> {
        unimplemented!()
    }

    pub fn configuration_bytes(_c: &Configuration) -> Vec<u8> {
        unimplemented!()
    }

    pub fn parse_configuration(_bytes: &[u8]) -> Configuration {
        unimplemented!()
    }
}
