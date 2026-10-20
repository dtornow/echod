//! The fleet: nodes over one bucket, as a state machine.
//!
//! The bucket holds every origin's document — a kernel state, the objects
//! the kernel is proved over — with its version, the instant of the step
//! that wrote it, and the deadline keys armed for it.
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
//! it and has not written yet. Every write has three outcomes: applied,
//! refused by its condition, or unknown — the bucket applied it or did not,
//! and the node, told only that it failed, gives the commit up.
//!
//! Around the core, the model keeps what the node does not see — whether it
//! is alive and its clock — and the kernel's steps as the relation the
//! kernel proves of them: what a step makes of a document is anything the
//! catalogue allows, reached by steps at one instant (`node::step::reach`),
//! and a sweep leaves nothing due (`node::step::no_due`).
//!
//! There is no real time and no hypothesis on clocks. A node's clock is its
//! own, advances as it will, and is read for one purpose: the instant a
//! step is decided at, which is where the kernel judges what has expired.
//! Nothing a node decides is trusted across nodes: every load is the
//! bucket's current document, and every write is conditional on the
//! version loaded. Which node acts on an origin is the server's routing,
//! not the model's concern: the theorems hold whoever acts.

use vstd::prelude::*;

use crate::node::core::*;
use crate::node::step::*;
use crate::node::txn::*;
use crate::tla::action::*;
use echod_kernel::types::*;

verus! {

/// An event in the bucket: a key armed, a version written.
pub enum Event {
    Armed(AKey),
    Born(Seq<char>),
}

/// The bucket: what it holds, and nothing it does not.
pub struct Store {
    /// Each origin's document. Absent means no object.
    pub docs: Map<Origin, Doc>,
    /// Each document's version: its ETag. Same domain as `docs`.
    pub etags: Map<Origin, Seq<char>>,
    /// The instant of the step that wrote each document, carried in the
    /// object's header. Same domain as `docs`.
    pub stamps: Map<Origin, nat>,
    /// The deadline keys in the bucket.
    pub timers: Set<AKey>,
}

/// What the proof remembers of the bucket's past. Ghost: no node reads any
/// of it, and no action's guard depends on it except two that state what is
/// assumed of S3 — a new version is never a version seen before, a new key
/// never a key seen before. An inductive invariant is a predicate on one
/// state; what it has to say about the past is recorded here.
pub struct History {
    /// Every version ever written, with its content.
    pub versions: Map<Seq<char>, Doc>,
    /// The node that wrote each version.
    pub writer: Map<Seq<char>, Id>,
    /// Every key ever armed, and by whom.
    pub armer: Map<AKey, Id>,
    /// The key that covers each document's nearest deadline: the one the
    /// last write kept.
    pub keeper: Map<Origin, AKey>,
    /// The order of events in the bucket. Every arm and every write takes
    /// the next number.
    pub counter: nat,
    pub order: Map<Event, nat>,
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
    /// The node's own clock: no relation to any other.
    pub clock: nat,
    /// The commits in flight, one per origin at most.
    pub txns: Map<Origin, Flight>,
}

pub struct Cluster {
    pub nodes: Map<Id, Node>,
    pub store: Store,
    /// Ghost: the bucket's past.
    pub hist: History,
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
    /// A node's clock advances.
    Tick(Id, nat),
    /// A node starts, with any clock.
    Join(Id, nat),
    Crash(Id),
    /// A node drops a cache entry.
    Forget(Id, Origin),
    /// A node loads a document and decides a step on it: a request
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
    /// The put of the key failed as far as the node knows; the bucket may
    /// hold it or not. The node gives up the commit.
    ArmUnknown(Id, Origin, AKey, bool),
    /// The write of the document failed as far as the node knows; the
    /// bucket may hold it or not. The node gives up the commit.
    CommitUnknown(Id, Origin, Seq<char>, bool),
    /// The rewrite that collects a key failed as far as the node knows; the
    /// bucket may hold it or not. The key stays.
    CollectUnknown(Id, Origin, Seq<char>, bool),
}

pub open spec fn init() -> spec_fn(Cluster) -> bool {
    |s: Cluster| init_state(s)
}

pub open spec fn init_state(s: Cluster) -> bool {
    &&& s.nodes == Map::<Id, Node>::empty()
    &&& s.store.docs == Map::<Origin, Doc>::empty()
    &&& s.store.etags == Map::<Origin, Seq<char>>::empty()
    &&& s.store.stamps == Map::<Origin, nat>::empty()
    &&& s.store.timers == Set::<AKey>::empty()
    &&& s.hist.versions == Map::<Seq<char>, Doc>::empty()
    &&& s.hist.writer == Map::<Seq<char>, Id>::empty()
    &&& s.hist.armer == Map::<AKey, Id>::empty()
    &&& s.hist.keeper == Map::<Origin, AKey>::empty()
    &&& s.hist.counter == 0
    &&& s.hist.order == Map::<Event, nat>::empty()
}

/// A node's clock advances, by any amount.
pub open spec fn tick(s: Cluster, i: Id, d: nat) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let n = s.nodes[i];
        Some(Cluster { nodes: s.nodes.insert(i, Node { clock: n.clock + d, ..n }), ..s })
    } else {
        None
    }
}

/// A fresh node: the core as `NodeCore::new` makes it. Its membership
/// dial, `ttl`, is the server's routing and nothing here reads it.
pub open spec fn fresh_core(i: Id) -> ANode {
    ANode { id: i, ttl: 0, read_any: false, epoch: 0, members: Seq::empty(), last_read: 0, cache: Map::empty(), armed: Map::empty() }
}

/// A node starts, with any clock.
pub open spec fn join(s: Cluster, i: Id, clock: nat) -> Option<Cluster> {
    if !s.nodes.contains_key(i) {
        let n = Node { core: fresh_core(i), bodies: Map::empty(), alive: true, clock, txns: Map::empty() };
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

pub open spec fn forget(s: Cluster, i: Id, o: Origin) -> Option<Cluster> {
    if s.nodes.contains_key(i) && s.nodes[i].alive {
        let n = s.nodes[i];
        Some(Cluster { nodes: s.nodes.insert(i, Node { core: spec_forget(n.core, o), ..n }), ..s })
    } else {
        None
    }
}

/// A node loads `o` — the bucket's current document; a cached body is
/// used only once a conditional read has confirmed its version — and
/// decides a step at `t`, the later of its clock and the document's
/// stamp: `NodeCore::begin`. Any live node may: which one does is routing.
pub open spec fn begin(s: Cluster, i: Id, o: Origin, t: nat, new: Doc, fired: Option<AKey>, did: bool, deadline: Option<nat>) -> Option<Cluster> {
    let n = s.nodes[i];
    let loaded = s.store.doc(o);
    let changed = did || new != loaded;
    if s.nodes.contains_key(i) && n.alive && !n.txns.contains_key(o)
        && t >= n.clock && t >= s.store.stamp(o) && t <= MAX_TIME
        && (match fired {
            Some(k) => k.origin == o && k.at <= n.clock && s.hist.armer.contains_key(k) && swept(t, loaded, new, did),
            None => !did && kreach(t, loaded, new),
        })
        && next_is(new, deadline)
    {
        let (core, bodies) = if s.store.docs.contains_key(o) {
            (spec_filled(n.core, o, s.store.etags[o], n.clock), n.bodies.insert(o, s.store.docs[o]))
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
            seq0: s.hist.counter,
            letag: s.store.etag(o),
            lseq: match s.store.etag(o) { Some(e) => s.hist.order[Event::Born(e)], None => 0 },
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
        && k.origin == o && Some(k.at) == x.c.deadline && !s.hist.armer.contains_key(k)
    {
        let x2 = Flight { c: spec_armed(x.c, k), phase: Phase::Armed, ..x };
        Some(Cluster {
            nodes: s.nodes.insert(i, Node { txns: n.txns.insert(o, x2), ..n }),
            store: Store { timers: s.store.timers.insert(k), ..s.store },
            hist: History {
                armer: s.hist.armer.insert(k, i),
                order: s.hist.order.insert(Event::Armed(k), s.hist.counter),
                counter: s.hist.counter + 1,
                ..s.hist
            },
            ..s
        })
    } else {
        None
    }
}

/// What the history records of a write: version `e` holding `d`, by `i`,
/// next in the order of events; and which key covers the document.
pub open spec fn written(s: Cluster, e: Seq<char>, d: Doc, i: Id, keeper: Map<Origin, AKey>) -> History {
    History {
        versions: s.hist.versions.insert(e, d),
        order: s.hist.order.insert(Event::Born(e), s.hist.counter),
        writer: s.hist.writer.insert(e, i),
        counter: s.hist.counter + 1,
        keeper,
        ..s.hist
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
        && s.store.etag(o) == x.cur && !s.hist.versions.contains_key(e)
    {
        let x2 = Flight { cur: Some(e), phase: Phase::Written, ..x };
        let keeper = match spec_keep(x.c) {
            Some(k) => s.hist.keeper.insert(o, k),
            None => s.hist.keeper.remove(o),
        };
        Some(Cluster {
            nodes: s.nodes.insert(i, Node { core: spec_filled(n.core, o, e, n.clock), bodies: n.bodies.insert(o, x.new), txns: n.txns.insert(o, x2), ..n }),
            store: Store {
                docs: s.store.docs.insert(o, x.new),
                etags: s.store.etags.insert(o, e),
                stamps: s.store.stamps.insert(o, x.t),
                ..s.store
            },
            hist: written(s, e, x.new, i, keeper),
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
        && s.store.etag(o) == x.cur && !s.hist.versions.contains_key(e)
    {
        let k = x.c.fired.unwrap();
        Some(Cluster {
            nodes: s.nodes.insert(i, Node { core: spec_collected(spec_filled(n.core, o, e, n.clock), o, k), bodies: n.bodies.insert(o, x.loaded), txns: n.txns.remove(o), ..n }),
            store: Store {
                docs: s.store.docs.insert(o, x.loaded),
                etags: s.store.etags.insert(o, e),
                stamps: s.store.stamps.insert(o, x.t),
                timers: s.store.timers.remove(k),
                ..s.store
            },
            hist: written(s, e, x.loaded, i, s.hist.keeper),
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

/// The node gives up a commit it does not know the outcome of: it trusts
/// nothing cached for the origin and forgets the commit. What it put and
/// wrote stays as it landed.
pub open spec fn give_up(s: Cluster, i: Id, o: Origin) -> Cluster {
    let n = s.nodes[i];
    Cluster { nodes: s.nodes.insert(i, Node { core: spec_forget(n.core, o), txns: n.txns.remove(o), ..n }), ..s }
}

/// The key's put: landed or not, the node does not know.
pub open spec fn arm_unknown(s: Cluster, i: Id, o: Origin, k: AKey, landed: bool) -> Option<Cluster> {
    if landed {
        match arm(s, i, o, k) {
            Some(s1) => Some(give_up(s1, i, o)),
            None => None,
        }
    } else {
        let n = s.nodes[i];
        let x = n.txns[o];
        if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Decided && x.c.rearm { Some(give_up(s, i, o)) } else { None }
    }
}

/// The document's write: landed or not, the node does not know.
pub open spec fn commit_unknown(s: Cluster, i: Id, o: Origin, e: Seq<char>, landed: bool) -> Option<Cluster> {
    if landed {
        match commit(s, i, o, e) {
            Some(s1) => Some(give_up(s1, i, o)),
            None => None,
        }
    } else {
        let n = s.nodes[i];
        let x = n.txns[o];
        if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && ready(x) { Some(give_up(s, i, o)) } else { None }
    }
}

/// The rewrite that collects a key: landed or not, the node does not know;
/// the key is not deleted either way.
pub open spec fn collect_unknown(s: Cluster, i: Id, o: Origin, e: Seq<char>, landed: bool) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Decided && !x.c.changed && x.c.fired is Some
        && (landed ==> s.store.etag(o) == x.cur && !s.hist.versions.contains_key(e))
    {
        let (store, hist) = if landed {
            (Store {
                docs: s.store.docs.insert(o, x.loaded),
                etags: s.store.etags.insert(o, e),
                stamps: s.store.stamps.insert(o, x.t),
                ..s.store
            }, written(s, e, x.loaded, i, s.hist.keeper))
        } else {
            (s.store, s.hist)
        };
        Some(give_up(Cluster { store, hist, ..s }, i, o))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// The actions as `Action` values, Anvil's shape
// ---------------------------------------------------------------------------
//
// Each is a precondition and a transition over the action's input, from the
// function above that computes it: enabled where that function is `Some`,
// and then its state. The temporal rules take them as they are — the
// induction now, fairness and liveness later.

pub open spec fn tick_action() -> Action<Cluster, (Id, nat), ()> {
    Action {
        precondition: |input: (Id, nat), s: Cluster| { let i = input.0; let d = input.1; tick(s, i, d) is Some },
        transition: |input: (Id, nat), s: Cluster| { let i = input.0; let d = input.1; (tick(s, i, d).unwrap(), ()) },
    }
}

pub open spec fn join_action() -> Action<Cluster, (Id, nat), ()> {
    Action {
        precondition: |input: (Id, nat), s: Cluster| { let i = input.0; let c = input.1; join(s, i, c) is Some },
        transition: |input: (Id, nat), s: Cluster| { let i = input.0; let c = input.1; (join(s, i, c).unwrap(), ()) },
    }
}

pub open spec fn crash_action() -> Action<Cluster, Id, ()> {
    Action {
        precondition: |input: Id, s: Cluster| { let i = input; crash(s, i) is Some },
        transition: |input: Id, s: Cluster| { let i = input; (crash(s, i).unwrap(), ()) },
    }
}

pub open spec fn forget_action() -> Action<Cluster, (Id, Origin), ()> {
    Action {
        precondition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; forget(s, i, o) is Some },
        transition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; (forget(s, i, o).unwrap(), ()) },
    }
}

pub open spec fn begin_action() -> Action<Cluster, (Id, Origin, nat, Doc, Option<AKey>, bool, Option<nat>), ()> {
    Action {
        precondition: |input: (Id, Origin, nat, Doc, Option<AKey>, bool, Option<nat>), s: Cluster| { let i = input.0; let o = input.1; let t = input.2; let new = input.3; let fired = input.4; let did = input.5; let deadline = input.6; begin(s, i, o, t, new, fired, did, deadline) is Some },
        transition: |input: (Id, Origin, nat, Doc, Option<AKey>, bool, Option<nat>), s: Cluster| { let i = input.0; let o = input.1; let t = input.2; let new = input.3; let fired = input.4; let did = input.5; let deadline = input.6; (begin(s, i, o, t, new, fired, did, deadline).unwrap(), ()) },
    }
}

pub open spec fn arm_action() -> Action<Cluster, (Id, Origin, AKey), ()> {
    Action {
        precondition: |input: (Id, Origin, AKey), s: Cluster| { let i = input.0; let o = input.1; let k = input.2; arm(s, i, o, k) is Some },
        transition: |input: (Id, Origin, AKey), s: Cluster| { let i = input.0; let o = input.1; let k = input.2; (arm(s, i, o, k).unwrap(), ()) },
    }
}

pub open spec fn commit_action() -> Action<Cluster, (Id, Origin, Seq<char>), ()> {
    Action {
        precondition: |input: (Id, Origin, Seq<char>), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; commit(s, i, o, e) is Some },
        transition: |input: (Id, Origin, Seq<char>), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; (commit(s, i, o, e).unwrap(), ()) },
    }
}

pub open spec fn commit_fail_action() -> Action<Cluster, (Id, Origin), ()> {
    Action {
        precondition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; commit_fail(s, i, o) is Some },
        transition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; (commit_fail(s, i, o).unwrap(), ()) },
    }
}

pub open spec fn disarm_action() -> Action<Cluster, (Id, Origin), ()> {
    Action {
        precondition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; disarm(s, i, o) is Some },
        transition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; (disarm(s, i, o).unwrap(), ()) },
    }
}

pub open spec fn finish_action() -> Action<Cluster, (Id, Origin, bool), ()> {
    Action {
        precondition: |input: (Id, Origin, bool), s: Cluster| { let i = input.0; let o = input.1; let deleted = input.2; finish(s, i, o, deleted) is Some },
        transition: |input: (Id, Origin, bool), s: Cluster| { let i = input.0; let o = input.1; let deleted = input.2; (finish(s, i, o, deleted).unwrap(), ()) },
    }
}

pub open spec fn collect_action() -> Action<Cluster, (Id, Origin, Seq<char>), ()> {
    Action {
        precondition: |input: (Id, Origin, Seq<char>), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; collect(s, i, o, e) is Some },
        transition: |input: (Id, Origin, Seq<char>), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; (collect(s, i, o, e).unwrap(), ()) },
    }
}

pub open spec fn collect_fail_action() -> Action<Cluster, (Id, Origin), ()> {
    Action {
        precondition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; collect_fail(s, i, o) is Some },
        transition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; (collect_fail(s, i, o).unwrap(), ()) },
    }
}

pub open spec fn done_action() -> Action<Cluster, (Id, Origin), ()> {
    Action {
        precondition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; done(s, i, o) is Some },
        transition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; (done(s, i, o).unwrap(), ()) },
    }
}

pub open spec fn arm_unknown_action() -> Action<Cluster, (Id, Origin, AKey, bool), ()> {
    Action {
        precondition: |input: (Id, Origin, AKey, bool), s: Cluster| { let i = input.0; let o = input.1; let k = input.2; let landed = input.3; arm_unknown(s, i, o, k, landed) is Some },
        transition: |input: (Id, Origin, AKey, bool), s: Cluster| { let i = input.0; let o = input.1; let k = input.2; let landed = input.3; (arm_unknown(s, i, o, k, landed).unwrap(), ()) },
    }
}

pub open spec fn commit_unknown_action() -> Action<Cluster, (Id, Origin, Seq<char>, bool), ()> {
    Action {
        precondition: |input: (Id, Origin, Seq<char>, bool), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; let landed = input.3; commit_unknown(s, i, o, e, landed) is Some },
        transition: |input: (Id, Origin, Seq<char>, bool), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; let landed = input.3; (commit_unknown(s, i, o, e, landed).unwrap(), ()) },
    }
}

pub open spec fn collect_unknown_action() -> Action<Cluster, (Id, Origin, Seq<char>, bool), ()> {
    Action {
        precondition: |input: (Id, Origin, Seq<char>, bool), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; let landed = input.3; collect_unknown(s, i, o, e, landed) is Some },
        transition: |input: (Id, Origin, Seq<char>, bool), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; let landed = input.3; (collect_unknown(s, i, o, e, landed).unwrap(), ()) },
    }
}

/// The next-state relation, one step at a time: the step's action, forward
/// on the step's input.
pub open spec fn next_step(s: Cluster, s2: Cluster, st: Step) -> bool {
    match st {
        Step::Tick(i, d) => tick_action().forward((i, d))(s, s2),
        Step::Join(i, c) => join_action().forward((i, c))(s, s2),
        Step::Crash(i) => crash_action().forward(i)(s, s2),
        Step::Forget(i, o) => forget_action().forward((i, o))(s, s2),
        Step::Begin(i, o, t, new, fired, did, deadline) => begin_action().forward((i, o, t, new, fired, did, deadline))(s, s2),
        Step::Arm(i, o, k) => arm_action().forward((i, o, k))(s, s2),
        Step::Commit(i, o, e) => commit_action().forward((i, o, e))(s, s2),
        Step::CommitFail(i, o) => commit_fail_action().forward((i, o))(s, s2),
        Step::Disarm(i, o) => disarm_action().forward((i, o))(s, s2),
        Step::Finish(i, o, deleted) => finish_action().forward((i, o, deleted))(s, s2),
        Step::Collect(i, o, e) => collect_action().forward((i, o, e))(s, s2),
        Step::CollectFail(i, o) => collect_fail_action().forward((i, o))(s, s2),
        Step::Done(i, o) => done_action().forward((i, o))(s, s2),
        Step::ArmUnknown(i, o, k, landed) => arm_unknown_action().forward((i, o, k, landed))(s, s2),
        Step::CommitUnknown(i, o, e, landed) => commit_unknown_action().forward((i, o, e, landed))(s, s2),
        Step::CollectUnknown(i, o, e, landed) => collect_unknown_action().forward((i, o, e, landed))(s, s2),
    }
}

pub open spec fn next() -> spec_fn(Cluster, Cluster) -> bool {
    |s: Cluster, s2: Cluster| exists |st: Step| #[trigger] next_step(s, s2, st)
}

} // verus!
