//! The fleet: nodes over one bucket, as a state machine.
//!
//! The bucket holds every document's version and one configuration object:
//! the member list and the epoch it was written in. A node reads the
//! configuration, keeps the epoch and the members it read, and remembers on
//! its own clock when it first read the epoch it holds. It acts as owner of
//! an origin only when its view is fresh, its members make it the owner, and
//! it has held the epoch for the grace. Writes are conditional on the
//! document version the writer read.
//!
//! Real time is a ghost variable: nodes never see it, but the hypothesis on
//! clocks — every live clock within `skew` of real time — is stated with it,
//! and so are the facts about when an epoch was written and when a node read
//! it. Nothing a node does depends on `now`.

use vstd::prelude::*;

verus! {

pub type Id = nat;
pub type Origin = nat;

/// The hash a load balancer and every node agree on. Any function will do.
pub uninterp spec fn hash(o: Origin) -> nat;

/// The configuration object in the bucket.
pub struct Config {
    pub epoch: nat,
    pub members: Seq<Id>,
}

pub struct Store {
    /// Each document's version. Absent is version 0.
    pub docs: Map<Origin, nat>,
    pub config: Config,
    /// Ghost: the real time each epoch was written at, for epochs up to the current.
    pub written: Map<nat, nat>,
}

impl Store {
    pub open spec fn version(self, o: Origin) -> nat {
        if self.docs.contains_key(o) { self.docs[o] } else { 0 }
    }
}

pub struct Cached {
    pub version: nat,
    /// The node's clock when the entry was read, written or revalidated.
    pub filled_at: nat,
}

pub struct Node {
    pub id: Id,
    pub alive: bool,
    pub clock: nat,
    /// Whether the configuration has been read at all.
    pub read_any: bool,
    pub epoch: nat,
    pub members: Seq<Id>,
    /// The node's clock at its last read of the configuration.
    pub last_read: nat,
    /// The node's clock when it first read the epoch it holds.
    pub held: nat,
    /// Ghost: real time of the last read, and of the first read of the epoch.
    pub last_read_real: nat,
    pub held_real: nat,
    pub cache: Map<Origin, Cached>,
}

pub struct Cluster {
    /// Ghost: real time.
    pub now: nat,
    pub nodes: Map<Id, Node>,
    pub store: Store,
}

/// The constants: a view is fresh for `ttl` after it was read; a clock is
/// within `skew` of real time; a node acts as owner `grace` after it first
/// read the epoch it holds. The proof needs `grace > ttl + 4 skew`.
pub struct Params {
    pub ttl: nat,
    pub skew: nat,
    pub grace: nat,
}

impl Params {
    pub open spec fn wf(self) -> bool {
        self.grace > self.ttl + 4 * self.skew
    }
}

// ---------------------------------------------------------------------------
// What a node decides
// ---------------------------------------------------------------------------

/// `hash(o) mod n` over the members in order.
pub open spec fn owner(members: Seq<Id>, o: Origin) -> Option<Id> {
    if members.len() == 0 { None } else { Some(members[(hash(o) % members.len()) as int]) }
}

pub open spec fn fresh(p: Params, n: Node) -> bool {
    n.read_any && n.last_read + p.ttl >= n.clock
}

/// The node acts as owner of `o`: serves it, writes it, fires its deadlines.
pub open spec fn acts(p: Params, n: Node, o: Origin) -> bool {
    &&& n.alive
    &&& fresh(p, n)
    &&& owner(n.members, o) == Some(n.id)
    &&& n.held + p.grace <= n.clock
}

/// The node answers `o` from its cache without asking the bucket.
pub open spec fn trusts(p: Params, n: Node, o: Origin) -> bool {
    &&& acts(p, n, o)
    &&& n.cache.contains_key(o)
    &&& n.cache[o].filled_at >= n.held + p.grace
}

// ---------------------------------------------------------------------------
// The actions
// ---------------------------------------------------------------------------

pub enum Step {
    /// Real time passes.
    Advance(nat),
    /// A node's clock advances.
    Tick(Id, nat),
    /// A node starts, with a clock within skew of real time.
    Join(Id, nat),
    Crash(Id),
    /// A node reads the configuration.
    ReadConfig(Id),
    /// A node writes a new configuration, conditionally on the epoch it holds.
    Propose(Id, Seq<Id>),
    /// A node reads a document from the bucket.
    ReadStore(Id, Origin),
    /// A node's conditional write lands.
    Write(Id, Origin),
    /// A node's conditional write is refused.
    WriteFail(Id, Origin),
    /// A node answers from its cache.
    ReadCached(Id, Origin),
}

pub open spec fn init() -> spec_fn(Cluster) -> bool {
    |s: Cluster| init_state(s)
}

pub open spec fn init_state(s: Cluster) -> bool {
    &&& s.now == 0
    &&& s.nodes == Map::<Id, Node>::empty()
    &&& s.store.docs == Map::<Origin, nat>::empty()
    &&& s.store.config == Config { epoch: 0, members: Seq::empty() }
    &&& s.store.written == Map::<nat, nat>::empty().insert(0, 0)
}

pub open spec fn clock_ok(p: Params, now: nat, clock: nat) -> bool {
    clock + p.skew >= now && clock <= now + p.skew
}

pub open spec fn advance(p: Params, s: Cluster, d: nat) -> Option<Cluster> {
    if forall |i: Id| #[trigger] s.nodes.contains_key(i) && s.nodes[i].alive ==> clock_ok(p, s.now + d, s.nodes[i].clock) {
        Some(Cluster { now: s.now + d, ..s })
    } else {
        None
    }
}

pub open spec fn tick(p: Params, s: Cluster, i: Id, d: nat) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive && clock_ok(p, s.now, s.nodes[i].clock + d) {
        let n = s.nodes[i];
        Some(Cluster { nodes: s.nodes.insert(i, Node { clock: n.clock + d, ..n }), ..s })
    } else {
        None
    }
}

pub open spec fn join(p: Params, s: Cluster, i: Id, clock: nat) -> Option<Cluster> {
    if !s.nodes.contains_key(i) && clock_ok(p, s.now, clock) {
        let n = Node {
            id: i, alive: true, clock, read_any: false, epoch: 0, members: Seq::empty(),
            last_read: 0, held: 0, last_read_real: 0, held_real: 0, cache: Map::empty(),
        };
        Some(Cluster { nodes: s.nodes.insert(i, n), ..s })
    } else {
        None
    }
}

pub open spec fn crash(s: Cluster, i: Id) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let n = s.nodes[i];
        Some(Cluster { nodes: s.nodes.insert(i, Node { alive: false, ..n }), ..s })
    } else {
        None
    }
}

pub open spec fn read_config(s: Cluster, i: Id) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let n = s.nodes[i];
        let same = n.read_any && n.epoch == s.store.config.epoch;
        let n2 = Node {
            read_any: true,
            epoch: s.store.config.epoch,
            members: s.store.config.members,
            last_read: n.clock,
            last_read_real: s.now,
            held: if same { n.held } else { n.clock },
            held_real: if same { n.held_real } else { s.now },
            ..n
        };
        Some(Cluster { nodes: s.nodes.insert(i, n2), ..s })
    } else {
        None
    }
}

pub open spec fn propose(s: Cluster, i: Id, members: Seq<Id>) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let e = s.store.config.epoch + 1;
        Some(Cluster {
            store: Store { config: Config { epoch: e, members }, written: s.store.written.insert(e, s.now), ..s.store },
            ..s
        })
    } else {
        None
    }
}

pub open spec fn read_store(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let n = s.nodes[i];
        let n2 = Node { cache: n.cache.insert(o, Cached { version: s.store.version(o), filled_at: n.clock }), ..n };
        Some(Cluster { nodes: s.nodes.insert(i, n2), ..s })
    } else {
        None
    }
}

pub open spec fn write(p: Params, s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    if s.nodes.contains_key(i) && acts(p, s.nodes[i], o) && s.nodes[i].cache.contains_key(o)
        && s.nodes[i].cache[o].version == s.store.version(o)
    {
        let n = s.nodes[i];
        let v = s.store.version(o) + 1;
        let n2 = Node { cache: n.cache.insert(o, Cached { version: v, filled_at: n.clock }), ..n };
        Some(Cluster { nodes: s.nodes.insert(i, n2), store: Store { docs: s.store.docs.insert(o, v), ..s.store }, ..s })
    } else {
        None
    }
}

pub open spec fn write_fail(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let n = s.nodes[i];
        Some(Cluster { nodes: s.nodes.insert(i, Node { cache: n.cache.remove(o), ..n }), ..s })
    } else {
        None
    }
}

pub open spec fn read_cached(p: Params, s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    if s.nodes.contains_key(i) && trusts(p, s.nodes[i], o) { Some(s) } else { None }
}

pub open spec fn step(p: Params, s: Cluster, st: Step) -> Option<Cluster> {
    match st {
        Step::Advance(d) => advance(p, s, d),
        Step::Tick(i, d) => tick(p, s, i, d),
        Step::Join(i, c) => join(p, s, i, c),
        Step::Crash(i) => crash(s, i),
        Step::ReadConfig(i) => read_config(s, i),
        Step::Propose(i, m) => propose(s, i, m),
        Step::ReadStore(i, o) => read_store(s, i, o),
        Step::Write(i, o) => write(p, s, i, o),
        Step::WriteFail(i, o) => write_fail(s, i, o),
        Step::ReadCached(i, o) => read_cached(p, s, i, o),
    }
}

pub open spec fn next_by(p: Params, st: Step, s: Cluster, s2: Cluster) -> bool {
    step(p, s, st) == Some(s2)
}

pub open spec fn next(p: Params) -> spec_fn(Cluster, Cluster) -> bool {
    |s: Cluster, s2: Cluster| exists |st: Step| #[trigger] next_by(p, st, s, s2)
}

} // verus!
