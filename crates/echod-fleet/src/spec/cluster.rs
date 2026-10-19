//! The fleet: nodes over one bucket, as a state machine.
//!
//! The bucket holds every origin's document — a kernel state, the objects
//! the kernel is proved over — with its version, the instant of the step
//! that wrote it, and the deadline keys armed for it; and one configuration
//! object, the member list and the epoch it was written in.
//!
//! A node's part of the state is the node core's view (`node::core::ANode`)
//! and the commits it has in flight (`node::txn::ATxn`, with what the model
//! sees of each: the version loaded, the documents before and after, the
//! instant). A node's actions are the core's specification functions: what
//! the executable node is proved to compute. A commit is the applier's
//! protocol, one store operation per action: arm the key for the document's
//! nearest deadline, write the document conditionally on the version
//! loaded, remove the key replaced, remember the key kept, delete the key
//! fired. A fired key that found nothing due is collected only after a
//! conditional rewrite of the document, which fences any commit that armed
//! it and has not written yet.
//!
//! Around the core, the model keeps what the node does not see — whether it
//! is alive, its clock, and, ghost, real time at the moments that matter —
//! and the kernel's steps as the relation the kernel proves of them: what a
//! step makes of a document is anything the catalogue allows, reached by
//! steps at one instant (`node::step::reach`), and a sweep leaves nothing
//! due (`node::step::no_due`).
//!
//! Real time is a ghost variable: nodes never see it, but the hypothesis on
//! clocks — every live clock within `skew` of real time — is stated with it.

use vstd::prelude::*;

use crate::node::core::*;
use crate::node::step::*;
use crate::node::txn::*;
use echod_kernel::types::*;

verus! {

/// The configuration object in the bucket.
pub struct Config {
    pub epoch: nat,
    pub members: Seq<Id>,
}

pub struct Store {
    /// Each origin's document. Absent means no object.
    pub docs: Map<Origin, Doc>,
    /// Each document's version: its ETag. Same domain as `docs`.
    pub etags: Map<Origin, Seq<char>>,
    /// The instant of the step that wrote each document. Same domain as `docs`.
    pub stamps: Map<Origin, nat>,
    /// Ghost: every version ever written, with its content. A write's version is new.
    pub versions: Map<Seq<char>, Doc>,
    /// Ghost: the real time each version was written at.
    pub born: Map<Seq<char>, nat>,
    /// Ghost: every epoch's members, for epochs up to the current.
    pub configs: Map<nat, Seq<Id>>,
    /// Ghost: the key that covers each document's nearest deadline — the one
    /// the last write kept.
    pub keeper: Map<Origin, AKey>,
    /// The deadline keys in the bucket.
    pub timers: Set<AKey>,
    /// Ghost: every key ever armed, and by whom. An arm's key is new.
    pub armer: Map<AKey, Id>,
    /// Ghost: the order of events in the bucket. Every arm and every write
    /// takes the next number: `armed_seq` for keys, `born_seq` for versions.
    pub counter: nat,
    pub armed_seq: Map<AKey, nat>,
    pub born_seq: Map<Seq<char>, nat>,
    /// Ghost: the node that wrote each version.
    pub writer: Map<Seq<char>, Id>,
    pub config: Config,
    /// Ghost: the real time each epoch was written at, for epochs up to the current.
    pub written: Map<nat, nat>,
}

impl Store {
    pub open spec fn etag(self, o: Origin) -> Option<Seq<char>> {
        if self.etags.contains_key(o) { Some(self.etags[o]) } else { None }
    }

    pub open spec fn doc(self, o: Origin) -> Doc {
        if self.docs.contains_key(o) { self.docs[o] } else { Map::empty() }
    }

    pub open spec fn stamp(self, o: Origin) -> nat {
        if self.stamps.contains_key(o) { self.stamps[o] } else { 0 }
    }
}

/// Where a commit is.
pub enum Phase {
    /// Decided, nothing in the store yet.
    Decided,
    /// The key for the new deadline is in the store.
    Armed,
    /// The document is in the store.
    Written,
}

/// A commit in flight, as the model sees it.
pub struct Flight {
    /// The node's decision.
    pub c: ATxn,
    /// The version the store is expected to hold: the one loaded, then,
    /// once written, the one written.
    pub cur: Option<Seq<char>>,
    pub loaded: Doc,
    pub new: Doc,
    /// The instant the step was decided at.
    pub t: nat,
    pub phase: Phase,
    /// Ghost: real time when it began; the node's epoch, `held_real` and
    /// `last_read_real` then.
    pub begun: nat,
    pub epoch: nat,
    pub held_real: nat,
    pub lr: nat,
    /// Ghost: the bucket's event count when it began; the version it loaded
    /// and that version's number (0 if none).
    pub seq0: nat,
    pub letag: Option<Seq<char>>,
    pub lseq: nat,
}

pub struct Node {
    /// What the executable node keeps and decides on.
    pub core: ANode,
    /// The documents cached beside the versions the core remembers: the
    /// body cache, which holds the version the core's entry names.
    pub bodies: Map<Origin, Doc>,
    pub alive: bool,
    pub clock: nat,
    /// Ghost: real time of the last configuration read, and of the first read of the epoch held.
    pub last_read_real: nat,
    pub held_real: nat,
    /// The commits in flight, one per origin at most.
    pub txns: Map<Origin, Flight>,
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
// The kernel's steps, on documents
// ---------------------------------------------------------------------------

/// `b` is what kernel steps at `t` make of document `a`: for some kernel
/// states holding these objects, the catalogue holds of the first and the
/// second is reached from it.
pub open spec fn kreach(t: nat, a: Doc, b: Doc) -> bool {
    exists |sa: echod_kernel::store::AState, sb: echod_kernel::store::AState|
        sa.objects == a && sb.objects == b && echod_kernel::properties::inv(t, sa) && #[trigger] reach(t, sa, sb)
}

/// A sweep at `t`: kernel steps, after which nothing is due at `t`; if
/// nothing fired (`did` false), the document is as it was.
pub open spec fn swept(t: nat, a: Doc, b: Doc, did: bool) -> bool {
    &&& kreach(t, a, b)
    &&& no_due(t, b)
    &&& !did ==> b == a
}

pub open spec fn next_is(d: Doc, deadline: Option<nat>) -> bool {
    match deadline {
        Some(x) => is_next(d, x),
        None => forall |t: nat| !has_deadline(d, t),
    }
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
    /// A node drops a cache entry.
    Forget(Id, Origin),
    /// The acting owner loads a document and decides a step on it: a request
    /// (`fired` none) or the sweep behind a fired key. The instant, what the
    /// step made of the document, whether the sweep fired anything, and the
    /// document's nearest deadline after.
    Begin(Id, Origin, nat, Doc, Option<AKey>, bool, Option<nat>),
    /// The key for the new deadline is put.
    Arm(Id, Origin, AKey),
    /// The conditional write of the document lands, at a new version.
    Commit(Id, Origin, Seq<char>),
    /// The conditional write is refused.
    CommitFail(Id, Origin),
    /// The key replaced, or no longer needed, is deleted.
    Disarm(Id, Origin),
    /// The node remembers the key kept and deletes the key fired, if it can.
    Finish(Id, Origin, bool),
    /// A fired key that found nothing due is collected: the document is
    /// rewritten conditionally, at a new version, then the key is deleted.
    Collect(Id, Origin, Seq<char>),
    /// The conditional rewrite is refused; the key stays.
    CollectFail(Id, Origin),
    /// A request that changed nothing is done.
    Done(Id, Origin),
    /// A store operation failed before the document was written.
    Abort(Id, Origin),
}

pub open spec fn init() -> spec_fn(Cluster) -> bool {
    |s: Cluster| init_state(s)
}

pub open spec fn init_state(s: Cluster) -> bool {
    &&& s.now == 0
    &&& s.nodes == Map::<Id, Node>::empty()
    &&& s.store.docs == Map::<Origin, Doc>::empty()
    &&& s.store.etags == Map::<Origin, Seq<char>>::empty()
    &&& s.store.stamps == Map::<Origin, nat>::empty()
    &&& s.store.versions == Map::<Seq<char>, Doc>::empty()
    &&& s.store.born == Map::<Seq<char>, nat>::empty()
    &&& s.store.configs == Map::<nat, Seq<Id>>::empty().insert(0, Seq::empty())
    &&& s.store.keeper == Map::<Origin, AKey>::empty()
    &&& s.store.timers == Set::<AKey>::empty()
    &&& s.store.armer == Map::<AKey, Id>::empty()
    &&& s.store.counter == 0
    &&& s.store.armed_seq == Map::<AKey, nat>::empty()
    &&& s.store.born_seq == Map::<Seq<char>, nat>::empty()
    &&& s.store.writer == Map::<Seq<char>, Id>::empty()
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
    ANode { id: i, ttl: p.ttl, grace: p.grace, read_any: false, epoch: 0, members: Seq::empty(), last_read: 0, held: 0, cache: Map::empty(), armed: Map::empty() }
}

pub open spec fn join(p: Params, s: Cluster, i: Id, clock: nat) -> Option<Cluster> {
    if !s.nodes.contains_key(i) && clock_ok(p, s.now, clock) {
        let n = Node { core: fresh_core(p, i), bodies: Map::empty(), alive: true, clock, last_read_real: 0, held_real: 0, txns: Map::empty() };
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
            store: Store { config: Config { epoch: e, members }, written: s.store.written.insert(e, s.now), configs: s.store.configs.insert(e, members), ..s.store },
            ..s
        })
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

/// The acting owner loads `o` — from its cache if it trusts it, from the
/// bucket otherwise — and decides a step at `t`, the later of its clock
/// and the document's stamp: `NodeCore::begin`.
pub open spec fn begin(s: Cluster, i: Id, o: Origin, t: nat, new: Doc, fired: Option<AKey>, did: bool, deadline: Option<nat>) -> Option<Cluster> {
    let n = s.nodes[i];
    let loaded = if trusts(n, o) { n.bodies[o] } else { s.store.doc(o) };
    let changed = did || new != loaded;
    if s.nodes.contains_key(i) && acts(n, o) && !n.txns.contains_key(o)
        && t >= n.clock && t >= s.store.stamp(o) && t <= MAX_TIME
        && (match fired {
            Some(k) => k.origin == o && k.at <= n.clock && s.store.armer.contains_key(k) && swept(t, loaded, new, did),
            None => !did && kreach(t, loaded, new),
        })
        && next_is(new, deadline)
    {
        let (core, bodies) = if trusts(n, o) {
            (n.core, n.bodies)
        } else if s.store.docs.contains_key(o) {
            (spec_filled(n.core, o, s.store.etags[o], n.clock, false), n.bodies.insert(o, s.store.docs[o]))
        } else {
            (spec_forget(n.core, o), n.bodies)
        };
        let x = Flight {
            c: spec_begin(core, o, s.store.etag(o), deadline, changed, fired),
            cur: s.store.etag(o),
            loaded,
            new,
            t,
            phase: Phase::Decided,
            begun: s.now,
            epoch: n.core.epoch,
            held_real: n.held_real,
            lr: n.last_read_real,
            seq0: s.store.counter,
            letag: s.store.etag(o),
            lseq: match s.store.etag(o) { Some(e) => s.store.born_seq[e], None => 0 },
        };
        Some(Cluster { nodes: s.nodes.insert(i, Node { core, bodies, txns: n.txns.insert(o, x), ..n }), ..s })
    } else {
        None
    }
}

pub open spec fn arm(s: Cluster, i: Id, o: Origin, k: AKey) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Decided && x.c.rearm
        && k.origin == o && Some(k.at) == x.c.deadline && !s.store.armer.contains_key(k)
    {
        let x2 = Flight { c: spec_armed(x.c, k), phase: Phase::Armed, ..x };
        Some(Cluster {
            nodes: s.nodes.insert(i, Node { txns: n.txns.insert(o, x2), ..n }),
            store: Store {
                timers: s.store.timers.insert(k),
                armer: s.store.armer.insert(k, i),
                armed_seq: s.store.armed_seq.insert(k, s.store.counter),
                counter: s.store.counter + 1,
                ..s.store
            },
            ..s
        })
    } else {
        None
    }
}

/// The write may go once the key is armed, if one had to be.
pub open spec fn ready(x: Flight) -> bool {
    x.c.changed && (if x.c.rearm { x.phase is Armed } else { x.phase is Decided })
}

pub open spec fn commit(s: Cluster, i: Id, o: Origin, e: Seq<char>) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && ready(x)
        && s.store.etag(o) == x.cur && !s.store.versions.contains_key(e)
    {
        let x2 = Flight { cur: Some(e), phase: Phase::Written, ..x };
        let keeper = match spec_keep(x.c) {
            Some(k) => s.store.keeper.insert(o, k),
            None => s.store.keeper.remove(o),
        };
        Some(Cluster {
            nodes: s.nodes.insert(i, Node { core: spec_filled(n.core, o, e, n.clock, true), bodies: n.bodies.insert(o, x.new), txns: n.txns.insert(o, x2), ..n }),
            store: Store {
                docs: s.store.docs.insert(o, x.new),
                etags: s.store.etags.insert(o, e),
                stamps: s.store.stamps.insert(o, x.t),
                versions: s.store.versions.insert(e, x.new),
                born: s.store.born.insert(e, s.now),
                born_seq: s.store.born_seq.insert(e, s.store.counter),
                writer: s.store.writer.insert(e, i),
                counter: s.store.counter + 1,
                keeper,
                ..s.store
            },
            ..s
        })
    } else {
        None
    }
}

pub open spec fn commit_fail(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && ready(x) && s.store.etag(o) != x.cur {
        Some(Cluster { nodes: s.nodes.insert(i, Node { core: spec_forget(n.core, o), txns: n.txns.remove(o), ..n }), ..s })
    } else {
        None
    }
}

pub open spec fn disarm(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Written && spec_to_disarm(x.c) is Some {
        let p = spec_to_disarm(x.c).unwrap();
        Some(Cluster { store: Store { timers: s.store.timers.remove(p), ..s.store }, ..s })
    } else {
        None
    }
}

/// The node remembers what it kept with the version written
/// (`NodeCore::finish`); the key fired, whoever armed it, is collected
/// (`NodeCore::collected`) and deleted — unless the delete failed, in which
/// case it stays and fires again.
pub open spec fn finish(s: Cluster, i: Id, o: Origin, deleted: bool) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Written && x.cur is Some
        && (deleted ==> x.c.fired is Some)
    {
        let core1 = spec_finish(n.core, x.c, x.cur.unwrap());
        let (core2, timers) = match x.c.fired {
            Some(k) => (if deleted { spec_collected(core1, o, k) } else { core1 }, if deleted { s.store.timers.remove(k) } else { s.store.timers }),
            None => (core1, s.store.timers),
        };
        Some(Cluster {
            nodes: s.nodes.insert(i, Node { core: core2, txns: n.txns.remove(o), ..n }),
            store: Store { timers, ..s.store },
            ..s
        })
    } else {
        None
    }
}

/// Nothing was due: rewrite the document at a new version, conditionally
/// on the version loaded, then delete the key fired.
pub open spec fn collect(s: Cluster, i: Id, o: Origin, e: Seq<char>) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Decided && !x.c.changed && x.c.fired is Some
        && s.store.etag(o) == x.cur && !s.store.versions.contains_key(e)
    {
        let k = x.c.fired.unwrap();
        Some(Cluster {
            nodes: s.nodes.insert(i, Node { core: spec_collected(spec_filled(n.core, o, e, n.clock, true), o, k), bodies: n.bodies.insert(o, x.loaded), txns: n.txns.remove(o), ..n }),
            store: Store {
                docs: s.store.docs.insert(o, x.loaded),
                etags: s.store.etags.insert(o, e),
                stamps: s.store.stamps.insert(o, x.t),
                versions: s.store.versions.insert(e, x.loaded),
                born: s.store.born.insert(e, s.now),
                born_seq: s.store.born_seq.insert(e, s.store.counter),
                writer: s.store.writer.insert(e, i),
                counter: s.store.counter + 1,
                timers: s.store.timers.remove(k),
                ..s.store
            },
            ..s
        })
    } else {
        None
    }
}

pub open spec fn collect_fail(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Decided && !x.c.changed && x.c.fired is Some
        && s.store.etag(o) != x.cur
    {
        Some(Cluster { nodes: s.nodes.insert(i, Node { core: spec_forget(n.core, o), txns: n.txns.remove(o), ..n }), ..s })
    } else {
        None
    }
}

pub open spec fn done(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Decided && !x.c.changed && x.c.fired is None {
        Some(Cluster { nodes: s.nodes.insert(i, Node { txns: n.txns.remove(o), ..n }), ..s })
    } else {
        None
    }
}

pub open spec fn abort(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && !(x.phase is Written) {
        Some(Cluster { nodes: s.nodes.insert(i, Node { core: spec_forget(n.core, o), txns: n.txns.remove(o), ..n }), ..s })
    } else {
        None
    }
}

pub open spec fn step(p: Params, s: Cluster, st: Step) -> Option<Cluster> {
    match st {
        Step::Advance(d) => advance(p, s, d),
        Step::Tick(i, d) => tick(p, s, i, d),
        Step::Join(i, c) => join(p, s, i, c),
        Step::Crash(i) => crash(s, i),
        Step::ReadConfig(i) => read_config(s, i),
        Step::Propose(i, m) => propose(s, i, m),
        Step::Forget(i, o) => forget(s, i, o),
        Step::Begin(i, o, t, new, fired, did, deadline) => begin(s, i, o, t, new, fired, did, deadline),
        Step::Arm(i, o, k) => arm(s, i, o, k),
        Step::Commit(i, o, e) => commit(s, i, o, e),
        Step::CommitFail(i, o) => commit_fail(s, i, o),
        Step::Disarm(i, o) => disarm(s, i, o),
        Step::Finish(i, o, deleted) => finish(s, i, o, deleted),
        Step::Collect(i, o, e) => collect(s, i, o, e),
        Step::CollectFail(i, o) => collect_fail(s, i, o),
        Step::Done(i, o) => done(s, i, o),
        Step::Abort(i, o) => abort(s, i, o),
    }
}

pub open spec fn next_by(p: Params, st: Step, s: Cluster, s2: Cluster) -> bool {
    step(p, s, st) == Some(s2)
}

pub open spec fn next(p: Params) -> spec_fn(Cluster, Cluster) -> bool {
    |s: Cluster, s2: Cluster| exists |st: Step| #[trigger] next_by(p, st, s, s2)
}

} // verus!
