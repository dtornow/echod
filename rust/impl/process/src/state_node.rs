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

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use echod_concrete::store::before;

use crate::types::*;
use crate::verified::node::{str_eq, NodeCore};
use crate::verified::table::Table;
use crate::verified::text::copy_string;
use crate::Config;

#[cfg(verus_keep_ghost)]
use echod_concrete::store::{spec_before, EtagSpec, StoreErrorSpec};
#[cfg(verus_keep_ghost)]
use crate::verified::node_spec::ANode;

#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};

verus! {

#[make_spec_type]
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
#[make_spec_type]
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

#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Roster {
    pub entries: Vec<Announced>,
}

/// `id, a` filed in id order, in place of any announcement under `id`.
pub open spec fn spec_roster_insert(s: Seq<AnnouncedSpec>, id: Seq<char>, a: AnnouncementSpec) -> Seq<AnnouncedSpec>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![(id, a)]
    } else if s[0].0 == id {
        seq![(id, a)] + s.drop_first()
    } else if spec_before(id, s[0].0) {
        seq![(id, a)] + s
    } else {
        seq![s[0]] + spec_roster_insert(s.drop_first(), id, a)
    }
}

/// The ids, in order.
pub open spec fn spec_roster_ids(s: Seq<AnnouncedSpec>) -> Seq<Seq<char>> {
    s.map_values(|e: AnnouncedSpec| e.0)
}

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
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Refresh {
    Announcing { op: OpId, now: u64 },
    Listing { op: OpId, now: u64 },
    Reading { pending: Table<OpId, bool>, nodes: Roster, now: u64, failed: Option<StoreError> },
    Config { op: OpId, nodes: Roster },
    Writing { op: OpId, next: Configuration },
}

#[cfg(verus_keep_ghost)]
pub ghost enum RefreshSpec {
    Announcing { op: OpId, now: u64 },
    Listing { op: OpId, now: u64 },
    Reading { pending: Map<OpId, bool>, nodes: RosterSpec, now: u64, failed: Option<StoreErrorSpec> },
    Config { op: OpId, nodes: RosterSpec },
    Writing { op: OpId, next: ConfigurationSpec },
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

#[cfg(verus_keep_ghost)]
impl RefreshSpec {
    pub open spec fn expects(self, op: OpId) -> bool {
        match self {
            RefreshSpec::Announcing { op: o, .. } | RefreshSpec::Listing { op: o, .. } | RefreshSpec::Config { op: o, .. } | RefreshSpec::Writing { op: o, .. } => o == op,
            RefreshSpec::Reading { pending, .. } => pending.contains_key(op),
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

#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
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

pub open spec fn spec_members_new(cfg: crate::config::ConfigSpec) -> MembersSpec {
    MembersSpec {
        me: AnnouncementSpec { id: cfg.node_id, url: cfg.url, at: 0 },
        heartbeat_ms: cfg.heartbeat_ms,
        ttl: cfg.node_ttl_ms,
        nodes: RosterSpec { entries: Seq::empty() },
        etag: None,
        next_heartbeat: None,
        refresh: None,
        read_once: false,
    }
}

#[cfg(verus_keep_ghost)]
impl MembersSpec {
    pub open spec fn refreshing(self) -> bool {
        self.refresh is Some
    }

    pub open spec fn wake_at(self) -> Option<u64> {
        if self.refreshing() { None } else { self.next_heartbeat }
    }
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
#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Node {
    pub core: NodeCore,
    pub members: Members,
    pub fleet_at: u64,
}

pub open spec fn spec_node_new(cfg: crate::config::ConfigSpec) -> NodeSpec {
    NodeSpec {
        core: ANode {
            id: cfg.node_id, ttl: cfg.node_ttl_ms as nat, read_any: false, epoch: 0,
            members: Seq::empty(), last_read: 0, cache: Map::empty(), armed: Map::empty(),
        },
        members: spec_members_new(cfg),
        fleet_at: 0,
    }
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

pub uninterp spec fn spec_announcement_bytes(a: AnnouncementSpec) -> Seq<u8>;
pub uninterp spec fn spec_parse_announcement(bytes: Seq<u8>) -> Option<AnnouncementSpec>;
pub uninterp spec fn spec_configuration_bytes(c: ConfigurationSpec) -> Seq<u8>;
/// What the configuration object says; bytes that do not parse say the
/// default: epoch 0, no members.
pub uninterp spec fn spec_parse_configuration(bytes: Seq<u8>) -> ConfigurationSpec;

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
