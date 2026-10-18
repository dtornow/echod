//! The fleet: nodes over one bucket, as a state machine.
//!
//! A node's part of the state is the node core's view (`node::core::ANode`),
//! and a node's actions are the core's specification functions: what the
//! executable node is proved to compute. Around the core, the model keeps
//! what the node does not see — whether it is alive, its clock, and, ghost,
//! real time at the moments that matter — and the environment: the bucket
//! with every document's version and one configuration object, the member
//! list and the epoch it was written in.
//!
//! Real time is a ghost variable: nodes never see it, but the hypothesis on
//! clocks — every live clock within `skew` of real time — is stated with it,
//! and so are the facts about when an epoch was written and when a node read
//! it. Nothing a node does depends on `now`.

use vstd::prelude::*;

use crate::node::core::*;

verus! {

/// The configuration object in the bucket.
pub struct Config {
    pub epoch: nat,
    pub members: Seq<Id>,
}

pub struct Store {
    /// Each document's version: its ETag. Absent means no object.
    pub docs: Map<Origin, Seq<char>>,
    pub config: Config,
    /// Ghost: the real time each epoch was written at, for epochs up to the current.
    pub written: Map<nat, nat>,
}

impl Store {
    pub open spec fn etag(self, o: Origin) -> Option<Seq<char>> {
        if self.docs.contains_key(o) { Some(self.docs[o]) } else { None }
    }
}

pub struct Node {
    /// What the executable node keeps and decides on.
    pub core: ANode,
    pub alive: bool,
    pub clock: nat,
    /// Ghost: real time of the last configuration read, and of the first read of the epoch held.
    pub last_read_real: nat,
    pub held_real: nat,
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
// What a node decides: the core's functions, at the node's clock
// ---------------------------------------------------------------------------

pub open spec fn owner(members: Seq<Id>, o: Origin) -> Option<Id> {
    spec_owner(members, o)
}

pub open spec fn fresh(n: Node) -> bool {
    spec_fresh(n.core, n.clock)
}

pub open spec fn acts(n: Node, o: Origin) -> bool {
    n.alive && spec_acts(n.core, o, n.clock)
}

pub open spec fn trusts(n: Node, o: Origin) -> bool {
    n.alive && spec_trusts(n.core, o, n.clock)
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
    /// A node creates a document that does not exist, with a fresh version.
    Create(Id, Origin, Seq<char>),
    /// A node's conditional write lands, with a fresh version.
    Write(Id, Origin, Seq<char>),
    /// A node's conditional write is refused, or it drops an entry.
    Forget(Id, Origin),
    /// A node answers from its cache.
    ReadCached(Id, Origin),
}

pub open spec fn init() -> spec_fn(Cluster) -> bool {
    |s: Cluster| init_state(s)
}

pub open spec fn init_state(s: Cluster) -> bool {
    &&& s.now == 0
    &&& s.nodes == Map::<Id, Node>::empty()
    &&& s.store.docs == Map::<Origin, Seq<char>>::empty()
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

/// A fresh node: the core as `NodeCore::new` makes it.
pub open spec fn fresh_core(p: Params, i: Id) -> ANode {
    ANode { id: i, ttl: p.ttl, grace: p.grace, read_any: false, epoch: 0, members: Seq::empty(), last_read: 0, held: 0, cache: Map::empty() }
}

pub open spec fn join(p: Params, s: Cluster, i: Id, clock: nat) -> Option<Cluster> {
    if !s.nodes.contains_key(i) && clock_ok(p, s.now, clock) {
        let n = Node { core: fresh_core(p, i), alive: true, clock, last_read_real: 0, held_real: 0 };
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

/// The node reads the configuration and takes it on: `NodeCore::read_config`.
pub open spec fn read_config(s: Cluster, i: Id) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let n = s.nodes[i];
        let same = n.core.read_any && n.core.epoch == s.store.config.epoch;
        let n2 = Node {
            core: spec_read_config(n.core, n.clock, s.store.config.epoch, s.store.config.members),
            last_read_real: s.now,
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

/// The node reads `o` from the bucket: `NodeCore::filled` with the version
/// read, or `NodeCore::forget` if there is no object.
pub open spec fn read_store(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let n = s.nodes[i];
        let core = match s.store.etag(o) {
            Some(e) => spec_filled(n.core, o, e, n.clock),
            None => spec_forget(n.core, o),
        };
        Some(Cluster { nodes: s.nodes.insert(i, Node { core, ..n }), ..s })
    } else {
        None
    }
}

/// The acting owner creates `o`, which does not exist, at a fresh version.
pub open spec fn create(s: Cluster, i: Id, o: Origin, e: Seq<char>) -> Option<Cluster> {
    if s.nodes.contains_key(i) && acts(s.nodes[i], o) && !s.store.docs.contains_key(o) {
        let n = s.nodes[i];
        let n2 = Node { core: spec_filled(n.core, o, e, n.clock), ..n };
        Some(Cluster { nodes: s.nodes.insert(i, n2), store: Store { docs: s.store.docs.insert(o, e), ..s.store }, ..s })
    } else {
        None
    }
}

/// The acting owner's conditional write lands: the version it holds is the
/// bucket's, and the bucket moves to a fresh one.
pub open spec fn write(s: Cluster, i: Id, o: Origin, e: Seq<char>) -> Option<Cluster> {
    if s.nodes.contains_key(i) && acts(s.nodes[i], o) && s.nodes[i].core.cache.contains_key(o)
        && Some(s.nodes[i].core.cache[o].etag) == s.store.etag(o) && Some(e) != s.store.etag(o)
    {
        let n = s.nodes[i];
        let n2 = Node { core: spec_filled(n.core, o, e, n.clock), ..n };
        Some(Cluster { nodes: s.nodes.insert(i, n2), store: Store { docs: s.store.docs.insert(o, e), ..s.store }, ..s })
    } else {
        None
    }
}

pub open spec fn forget(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let n = s.nodes[i];
        Some(Cluster { nodes: s.nodes.insert(i, Node { core: spec_forget(n.core, o), ..n }), ..s })
    } else {
        None
    }
}

pub open spec fn read_cached(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    if s.nodes.contains_key(i) && trusts(s.nodes[i], o) { Some(s) } else { None }
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
        Step::Create(i, o, e) => create(s, i, o, e),
        Step::Write(i, o, e) => write(s, i, o, e),
        Step::Forget(i, o) => forget(s, i, o),
        Step::ReadCached(i, o) => read_cached(s, i, o),
    }
}

pub open spec fn next_by(p: Params, st: Step, s: Cluster, s2: Cluster) -> bool {
    step(p, s, st) == Some(s2)
}

pub open spec fn next(p: Params) -> spec_fn(Cluster, Cluster) -> bool {
    |s: Cluster, s2: Cluster| exists |st: Step| #[trigger] next_by(p, st, s, s2)
}

} // verus!
