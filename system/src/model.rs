//! The fleet: nodes over one bucket, as a state machine.
//!
//! The bucket holds every origin's document — a kernel state, the objects
//! the kernel is proved over — with its version, the instant of the step
//! that wrote it, and the deadline keys armed for it.
//!
//! A node's part of the state is the node core's view (`node::ANode`)
//! and the commits it has in flight (`txn::ACommit`, with what the model
//! sees of each: the version loaded, the documents before and after, the
//! instant). A node's actions are the core's specification functions: what
//! the executable node is proved to compute. A commit is the applier's
//! protocol, one store round trip per action. `Prepare` loads and decides,
//! and touches nothing. `AddTimer` puts the key for the document's nearest
//! deadline. `Process` puts the document, conditionally on the version
//! loaded. `DelTimer` deletes the key replaced and the key fired, and the
//! node remembers the key kept. `Done` closes a commit that changed
//! nothing. Each put carries the store's answer, `Outcome`: applied,
//! refused by its condition, or unknown — the bucket applied it or did not,
//! and the node, told only that it failed, gives the commit up. A fired key
//! that found nothing due is collected only after a conditional rewrite of
//! the document, which fences any commit that armed it and has not written
//! yet; that rewrite is `Process` of an unchanged document.
//!
//! Around the core, the model keeps what the node does not see — whether it
//! is alive and its clock — and the kernel's steps as what the node's
//! verified functions ensure of them: a handler's or a fire's function, then
//! what `drain` ensures (`step::drained`); `sweep` then `drain` for a sweep
//! (`step::swept_by`); `schedule_due` for a schedule's key with nothing due.
//!
//! There is no real time and no hypothesis on clocks. A node's clock is its
//! own, advances as it will, and is read for one purpose: the instant a
//! step is decided at, which is where the kernel judges what has expired.
//! Nothing a node decides is trusted across nodes: every load is the
//! bucket's current document, and every write is conditional on the
//! version loaded. Which node acts on an origin is the server's routing,
//! not the model's concern: the theorems hold whoever acts.

use vstd::prelude::*;

use echod_kernel::commit::*;
use echod_kernel::node::*;
use echod_kernel::steps::*;
use crate::tla::action::*;
use echod_kernel::external::spec_handle;
use echod_kernel::internal::spec_fire;
use echod_kernel::store::object_order;
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
        if self.docs.contains_key(o) { self.docs[o] } else { empty_doc() }
    }

    pub open spec fn stamp(self, o: Origin) -> nat {
        if self.stamps.contains_key(o) { self.stamps[o] } else { 0 }
    }
}

/// Where a commit is: the last of its actions taken. After `Prepare`
/// nothing is in the store; after `AddTimer` the key for the new deadline
/// is; after `Process` the document is.
pub enum Phase {
    Prepare,
    AddTimer,
    Process,
}

/// The second half of a fire: the schedule's commit, decided with the
/// origin's and run once the origin's is done. What it loaded of the
/// schedule's document and at which version, what it writes, the
/// document's deadline after, and the key whose firing this is.
pub struct Pending {
    pub target: Origin,
    /// The occurrence's promise, in the origin the first half commits.
    pub pid: Seq<char>,
    pub cur: Option<Seq<char>>,
    pub loaded: Doc,
    pub new: Doc,
    pub deadline: Option<nat>,
    pub fired: AKey,
}

/// A commit in flight, as the model sees it.
pub struct Flight {
    /// What it is for.
    pub work: Work,
    /// A fire's commit on the schedule, to follow this one.
    pub then: Option<Pending>,
    /// The node's decision.
    pub c: ACommit,
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

/// What a step is for: a request, with the document as the sweep before its
/// handler left it; the sweep behind a fired key; or the fire behind a
/// schedule's key — the schedule, the promise its occurrence expands to, the
/// run after, and the schedule document's deadline after.
pub enum Work {
    Request(ARequest, Doc),
    Sweep(AKey),
    Fire(AKey, Seq<char>, Seq<char>, u64, Option<nat>),
}

// ---------------------------------------------------------------------------
// Targets: what a document is named for
// ---------------------------------------------------------------------------

/// The promise id a schedule's template expands to at an instant: the
/// server's `Applier::expand`, trusted to be a function of the three.
pub uninterp spec fn expand(template: Seq<char>, sid: Seq<char>, at: nat) -> Seq<char>;

/// A schedule's document is named for it.
pub open spec fn sched_target(sid: Seq<char>) -> Origin {
    "sched:"@ + sid
}

pub open spec fn is_sched(o: Origin) -> bool {
    o.len() >= 6 && o.take(6) == "sched:"@
}

/// A schedule's document holds no objects; an origin's no schedule.
pub open spec fn shaped(o: Origin, d: Doc) -> bool {
    if is_sched(o) { d.objects == Map::<Seq<char>, APromise>::empty() } else { d.schedules == Map::<Seq<char>, ASchedule>::empty() }
}

/// The document a request is served on: its id's origin, or its
/// schedule's. A heartbeat with no task names none.
pub open spec fn request_target(req: ARequest) -> Option<Origin> {
    match req {
        ARequest::PromiseGet(q) => Some(origin(q.id)),
        ARequest::PromiseCreate(q) => Some(origin(q.id)),
        ARequest::PromiseSettle(q) => Some(origin(q.id)),
        ARequest::PromiseRegisterCallback(q) => Some(origin(q.awaited)),
        ARequest::PromiseRegisterListener(q) => Some(origin(q.awaited)),
        ARequest::ScheduleGet(q) => Some(sched_target(q.id)),
        ARequest::ScheduleCreate(q) => Some(sched_target(q.id)),
        ARequest::ScheduleDelete(q) => Some(sched_target(q.id)),
        ARequest::TaskGet(q) => Some(origin(q.id)),
        ARequest::TaskCreate(q) => Some(origin(q.action.id)),
        ARequest::TaskAcquire(q) => Some(origin(q.id)),
        ARequest::TaskFulfill(q) => Some(origin(q.id)),
        ARequest::TaskRelease(q) => Some(origin(q.id)),
        ARequest::TaskHalt(q) => Some(origin(q.id)),
        ARequest::TaskContinue(q) => Some(origin(q.id)),
        ARequest::TaskFence(q) => Some(origin(q.id)),
        ARequest::TaskFenceCheck(q) => Some(origin(q.id)),
        ARequest::TaskHeartbeat(q) => if q.tasks.len() > 0 { Some(origin(q.tasks[0].id)) } else { None },
        ARequest::TaskSuspend(q) => Some(origin(q.id)),
    }
}

/// Ghost: a request answered — where, at what instant it was decided, what
/// it asked, and what it was told. A request is answered when its write
/// lands, or at once when it changed nothing; one that lost its race is
/// decided again and answered then. The log records each at its
/// linearization point: a write at its commit, which is conditional on the
/// version it read, so the document is then as read; a request that
/// changed nothing at its read, which is what its answer was computed on
/// and all it depends on. The node sends that answer later, but nothing it
/// sends depends on anything after the read.
pub struct Served {
    pub origin: Origin,
    pub at: nat,
    pub req: ARequest,
    pub resp: AResponse,
}

pub struct Cluster {
    pub nodes: Map<Id, Node>,
    pub store: Store,
    /// Ghost: the bucket's past.
    pub hist: History,
    /// Ghost: every request served, in order.
    pub log: Seq<Served>,
    /// The fleet's one configured retry timeout (`Config::retry_timeout`),
    /// the kernel's `cfg.retry_timeout`: every node runs the sweep with it.
    pub rt: nat,
}

// ---------------------------------------------------------------------------
// The kernel's steps, on documents
// ---------------------------------------------------------------------------

/// `b` is what kernel steps at `t` make of the kernel state `a`: the drain
/// after a request. Nothing is assumed of `a`; what holds of it is proved.
pub open spec fn kreach_from(t: nat, a: echod_kernel::store::AState, b: Doc) -> bool {
    exists |sb: echod_kernel::store::AState| strip(sb) == b && #[trigger] drained(t, a, sb)
}

/// A fire's two documents from the fired state: the origin's is what the
/// drain makes of its objects; the schedule's is its schedules, which the
/// drain leaves.
pub open spec fn kreach_fire(t: nat, a: echod_kernel::store::AState, o: Doc, c: Doc) -> bool {
    exists |sb: echod_kernel::store::AState| objects_only(sb) == o && schedules_only(sb) == c && #[trigger] drained(t, a, sb)
}

/// A sweep at `t`: what `sweep` then `drain` make of the document, given
/// the catalogue holds of it.
pub open spec fn swept(t: nat, a: Doc, b: Doc, did: bool) -> bool {
    &&& echod_kernel::properties::inv(t, full(a))
    &&& exists |m: echod_kernel::store::AState, sb: echod_kernel::store::AState|
        #[trigger] swept_by(t, full(a), m, did) && #[trigger] drained(t, m, sb) && strip(sb) == b
}

// What the node computes, as the kernel's functions. `logic::flight::decide`
// runs the verified `sweep` and `handle` on the document it loaded, and
// `process_schedule` then `sweep` for a fire; each is proved to compute the
// spec function named here, so these are the step's values, not a contract
// on them. The relational facts above (`swept`, `kreach_from`,
// `kreach_fire`) are what the same functions ensure; `sweep`'s postcondition
// states both at once, which is what keeps the two conjuncts consistent.

/// A timer's step: the single pass over the document's rows in stored order.
pub open spec fn computed_sweep(loaded: Doc, t: nat, rt: nat, new: Doc) -> bool {
    exists |ids: Seq<Seq<char>>| #[trigger] object_order(full(loaded), ids)
        && new == strip(executable_single_pass(full(loaded), ids, t, rt))
}

/// A request's step: sweep, the handler, sweep. `m` is the swept document
/// the handler ran on; its answer is what the request is told.
pub open spec fn computed_request(loaded: Doc, req: ARequest, t: nat, rt: nat, m: Doc, new: Doc) -> bool {
    exists |ids1: Seq<Seq<char>>, ids2: Seq<Seq<char>>| {
        &&& #[trigger] object_order(full(loaded), ids1)
        &&& m == strip(executable_single_pass(full(loaded), ids1, t, rt))
        &&& #[trigger] object_order(spec_handle(full(m), req, t).0, ids2)
        &&& new == strip(executable_single_pass(spec_handle(full(m), req, t).0, ids2, t, rt))
    }
}

/// A fire's step on the two documents: `process_schedule`, then the sweep
/// of the origin's rows (the occurrence's promise among them).
pub open spec fn computed_fire(fired: echod_kernel::store::AState, t: nat, rt: nat, new: Doc) -> bool {
    exists |ids: Seq<Seq<char>>| #[trigger] object_order(fired, ids)
        && new == objects_only(executable_single_pass(fired, ids, t, rt))
}

pub open spec fn next_is(d: Doc, deadline: Option<nat>) -> bool {
    match deadline {
        Some(x) => is_next(d, x),
        None => forall |t: nat| !has_deadline(d, t),
    }
}

// ---------------------------------------------------------------------------
// The actions. The commit's puts are given case by case — applied, refused,
// unknown; a changed document and an unchanged one — and folded into one
// action per round trip below.
// ---------------------------------------------------------------------------

/// The store's answer to a put.
pub enum Outcome {
    Applied,
    /// Refused by its condition. A key's put has none, so a key is never refused.
    Refused,
    /// Failed as far as the node knows; whether the bucket applied it.
    Unknown(bool),
}

pub enum Step {
    /// A node's clock advances.
    Tick(Id, nat),
    /// A node starts, with any clock.
    Join(Id, nat),
    Crash(Id),
    /// A node drops a cache entry.
    Forget(Id, Origin),
    /// A node loads a document and decides a step on it: a request, or the
    /// sweep behind a fired key. The instant, what the step made of the
    /// document, whether the sweep fired anything, and the document's
    /// nearest deadline after. Nothing in the store moves.
    Prepare(Id, Origin, nat, Work, Doc, bool, Option<nat>),
    /// The key for the new deadline is put.
    AddTimer(Id, Origin, AKey, Outcome),
    /// The document is put, conditionally on the version loaded, at a new
    /// version: the commit of a changed document, or the rewrite that
    /// collects a fired key behind an unchanged one.
    Process(Id, Origin, Seq<char>, Outcome),
    /// After the write: the key replaced and the key fired are deleted, each
    /// if the delete went through, and the node remembers the key kept.
    DelTimer(Id, Origin, bool, bool),
    /// A request that changed nothing is done.
    Done(Id, Origin),
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
    &&& s.log == Seq::<Served>::empty()
    &&& s.rt <= MAX_TIME
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
/// stamp: `NodeCore::prepare`. A request is the kernel's handler for it,
/// `spec_handle`, then the drain; a sweep is the step module's contract.
/// Any live node may: which one does is routing. A request served is
/// logged with its answer.
/// No commit of the node is on `o`, nor has one to come on it.
pub open spec fn free(n: Node, o: Origin) -> bool {
    &&& !n.txns.contains_key(o)
    &&& forall |q: Origin| #[trigger] n.txns.contains_key(q) ==> match n.txns[q].then { Some(p) => p.target != o, None => true }
}

/// A fire's second half, decided with its first: the schedule `sid` at
/// `pid`'s origin, `k` its key, the run after `next`.
pub open spec fn fire_pending(s: Cluster, k: AKey, sid: Seq<char>, pid: Seq<char>, next: u64, t: nat, deadline: Option<nat>, loaded: Doc) -> Pending {
    let st = sched_target(sid);
    let sd = s.store.doc(st);
    let occ = AOccurrence { at: sd.schedules[sid].next_run_at, promise_id: pid };
    let fired_state = spec_fire(joint(loaded, sd), sid, seq![occ], next, t);
    Pending { target: st, pid, cur: s.store.etag(st), loaded: sd, new: schedules_only(fired_state), deadline, fired: k }
}

pub open spec fn prepare(s: Cluster, i: Id, o: Origin, t: nat, work: Work, new: Doc, did: bool, deadline: Option<nat>) -> Option<Cluster> {
    let n = s.nodes[i];
    let loaded = s.store.doc(o);
    let changed = did || new != loaded;
    let fired = match work { Work::Sweep(k) => Some(k), Work::Request(..) => None, Work::Fire(..) => None };
    if s.nodes.contains_key(i) && n.alive && free(n, o)
        && t >= n.clock && t >= s.store.stamp(o) && t <= MAX_TIME
        && (match work {
            // a sweep: `sweep` then `drain`; on a schedule's document, `schedule_due` found nothing due
            Work::Sweep(k) => k.origin == o && k.at <= n.clock && s.hist.armer.contains_key(k) && swept(t, loaded, new, did)
                && computed_sweep(loaded, t, s.rt, new)
                && (is_sched(o) ==> schedules_idle(t, loaded.schedules)),
            // a request: `sweep` (every lease and deadline on the document read
            // against the clock, as Lean's `Object.project` reads them), then
            // its handler on the swept document, then `drain`
            Work::Request(req, m) => !did && request_target(req) == Some(o)
                && (exists |d: bool| #[trigger] swept_by(t, full(loaded), full(m), d))
                && kreach_from(t, spec_handle(full(m), req, t).0, new)
                && computed_request(loaded, req, t, s.rt, m, new),
            Work::Fire(k, sid, pid, next, deadline_s) => {
                let st = sched_target(sid);
                let sd = s.store.doc(st);
                let p = fire_pending(s, k, sid, pid, next, t, deadline_s, loaded);
                &&& !did
                &&& origin(pid) == o
                &&& k.origin == st && k.at <= n.clock && s.hist.armer.contains_key(k)
                &&& free(n, st)
                &&& t >= s.store.stamp(st)
                &&& sd.schedules.contains_key(sid) && sd.schedules[sid].next_run_at <= t
                &&& pid == expand(sd.schedules[sid].promise_id, sid, sd.schedules[sid].next_run_at as nat)
                &&& next > sd.schedules[sid].next_run_at && next <= MAX_TIME
                &&& kreach_fire(t, spec_fire(joint(loaded, sd), sid, seq![AOccurrence { at: sd.schedules[sid].next_run_at, promise_id: pid }], next, t), new, p.new)
                &&& computed_fire(spec_fire(joint(loaded, sd), sid, seq![AOccurrence { at: sd.schedules[sid].next_run_at, promise_id: pid }], next, t), t, s.rt, new)
                &&& next_is(p.new, deadline_s)
            }
        })
        && next_is(new, deadline)
    {
        // the load fills the cache: an origin's document; a schedule's is not cached
        let (core, bodies) = if is_sched(o) {
            (n.core, n.bodies)
        } else if s.store.docs.contains_key(o) {
            (spec_filled(n.core, o, s.store.etags[o], n.clock), n.bodies.insert(o, s.store.docs[o]))
        } else {
            (spec_forget(n.core, o), n.bodies)
        };
        let then = match work {
            Work::Fire(k, sid, pid, next, deadline_s) => Some(fire_pending(s, k, sid, pid, next, t, deadline_s, loaded)),
            _ => None,
        };
        let x = Flight {
            work,
            then,
            c: spec_prepare(core, o, s.store.etag(o), deadline, changed, fired),
            cur: s.store.etag(o),
            loaded,
            new,
            t,
            phase: Phase::Prepare,
            seq0: s.hist.counter,
            letag: s.store.etag(o),
            lseq: match s.store.etag(o) { Some(e) => s.hist.order[Event::Born(e)], None => 0 },
        };
        Some(Cluster {
            nodes: s.nodes.insert(i, Node { core, bodies, txns: n.txns.insert(o, x), ..n }),
            // a request that changed nothing is answered from this read
            log: if changed { s.log } else { answered(s, o, x) },
            ..s
        })
    } else {
        None
    }
}

pub open spec fn arm(s: Cluster, i: Id, o: Origin, k: AKey) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Prepare && x.c.rearm
        && k.origin == o && Some(k.at) == x.c.deadline && !s.hist.armer.contains_key(k)
    {
        let x2 = Flight { c: spec_armed(x.c, k), phase: Phase::AddTimer, ..x };
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
/// The log once the step `x` on `o` is answered: its request and the
/// response the kernel gave it on the document it loaded. Anything but a
/// request answers nothing.
pub open spec fn answered(s: Cluster, o: Origin, x: Flight) -> Seq<Served> {
    match x.work {
        Work::Request(req, m) => s.log.push(Served { origin: o, at: x.t, req, resp: spec_handle(full(m), req, x.t).1 }),
        _ => s.log,
    }
}

pub open spec fn ready(x: Flight) -> bool {
    x.c.changed && (if x.c.rearm { x.phase is AddTimer } else { x.phase is Prepare })
}

pub open spec fn commit(s: Cluster, i: Id, o: Origin, e: Seq<char>) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && ready(x)
        && s.store.etag(o) == x.cur && !s.hist.versions.contains_key(e)
    {
        let x2 = Flight { cur: Some(e), phase: Phase::Process, ..x };
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
            log: answered(s, o, x),
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
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Process && spec_to_disarm(x.c) is Some {
        let p = spec_to_disarm(x.c).unwrap();
        Some(Cluster { store: Store { timers: s.store.timers.remove(p), ..s.store }, ..s })
    } else {
        None
    }
}

/// A fire's second half begins where its first ends: the schedule's
/// commit, decided from what was loaded with the origin, with the key
/// fired; `NodeCore::prepare` on the schedule's document.
pub open spec fn continued(s: Cluster, core: ANode, p: Pending, t: nat) -> Flight {
    Flight {
        work: Work::Sweep(p.fired),
        then: None,
        c: spec_prepare(core, p.target, p.cur, p.deadline, p.new != p.loaded, Some(p.fired)),
        cur: p.cur,
        loaded: p.loaded,
        new: p.new,
        t,
        phase: Phase::Prepare,
        seq0: s.hist.counter,
        letag: p.cur,
        lseq: match p.cur { Some(e) => s.hist.order[Event::Born(e)], None => 0 },
    }
}

/// The node's commits once the one on `o` is done: removed, or, when a
/// fire's second half follows, replaced by it on the schedule's document.
pub open spec fn after(s: Cluster, core: ANode, n: Node, o: Origin) -> Map<Origin, Flight> {
    let x = n.txns[o];
    match x.then {
        Some(p) => n.txns.remove(o).insert(p.target, continued(s, core, p, x.t)),
        None => n.txns.remove(o),
    }
}

/// The node remembers what it kept with the version written
/// (`NodeCore::finish`); the key fired, whoever armed it, is collected
/// (`NodeCore::collected`) and deleted — unless the delete failed, in which
/// case it stays and fires again.
pub open spec fn finish(s: Cluster, i: Id, o: Origin, deleted: bool) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Process && x.cur is Some
        && (deleted ==> x.c.fired is Some)
    {
        let core1 = spec_finish(n.core, x.c, x.cur.unwrap());
        let (core2, timers) = match x.c.fired {
            Some(k) => (if deleted { spec_collected(core1, o, k) } else { core1 }, if deleted { s.store.timers.remove(k) } else { s.store.timers }),
            None => (core1, s.store.timers),
        };
        Some(Cluster {
            nodes: s.nodes.insert(i, Node { core: core2, txns: after(s, core2, n, o), ..n }),
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
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Prepare && !x.c.changed && x.c.fired is Some
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
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Prepare && !x.c.changed && x.c.fired is Some
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
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Prepare && !x.c.changed && x.c.fired is None {
        Some(Cluster { nodes: s.nodes.insert(i, Node { txns: after(s, n.core, n, o), ..n }), ..s })
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
        if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Prepare && x.c.rearm { Some(give_up(s, i, o)) } else { None }
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
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Prepare && !x.c.changed && x.c.fired is Some
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
// The round trips, by outcome
// ---------------------------------------------------------------------------

/// The key's put. A put without a condition is never refused.
pub open spec fn add_timer(s: Cluster, i: Id, o: Origin, k: AKey, out: Outcome) -> Option<Cluster> {
    match out {
        Outcome::Applied => arm(s, i, o, k),
        Outcome::Refused => None,
        Outcome::Unknown(landed) => arm_unknown(s, i, o, k, landed),
    }
}

/// The document's put: the commit of a changed document, or the rewrite
/// that collects a fired key behind an unchanged one.
pub open spec fn process_doc(s: Cluster, i: Id, o: Origin, e: Seq<char>, out: Outcome) -> Option<Cluster> {
    let n = s.nodes[i];
    if s.nodes.contains_key(i) && n.txns.contains_key(o) && n.txns[o].c.changed {
        match out {
            Outcome::Applied => commit(s, i, o, e),
            Outcome::Refused => commit_fail(s, i, o),
            Outcome::Unknown(landed) => commit_unknown(s, i, o, e, landed),
        }
    } else {
        match out {
            Outcome::Applied => collect(s, i, o, e),
            Outcome::Refused => collect_fail(s, i, o),
            Outcome::Unknown(landed) => collect_unknown(s, i, o, e, landed),
        }
    }
}

/// After the write: the key replaced is deleted if `prev` and the key
/// fired if `fired`, each a delete that may have failed silently; and the
/// node remembers the key kept. Two round trips, but the document is
/// written and both keys are dead, so nothing observes their order.
pub open spec fn del_timer(s: Cluster, i: Id, o: Origin, prev: bool, fired: bool) -> Option<Cluster> {
    let n = s.nodes[i];
    let x = n.txns[o];
    if s.nodes.contains_key(i) && n.alive && n.txns.contains_key(o) && x.phase is Process
        && (prev ==> spec_to_disarm(x.c) is Some)
    {
        let s1 = if prev { disarm(s, i, o).unwrap() } else { s };
        finish(s1, i, o, fired)
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

pub open spec fn prepare_action() -> Action<Cluster, (Id, Origin, nat, Work, Doc, bool, Option<nat>), ()> {
    Action {
        precondition: |input: (Id, Origin, nat, Work, Doc, bool, Option<nat>), s: Cluster| { let i = input.0; let o = input.1; let t = input.2; let work = input.3; let new = input.4; let did = input.5; let deadline = input.6; prepare(s, i, o, t, work, new, did, deadline) is Some },
        transition: |input: (Id, Origin, nat, Work, Doc, bool, Option<nat>), s: Cluster| { let i = input.0; let o = input.1; let t = input.2; let work = input.3; let new = input.4; let did = input.5; let deadline = input.6; (prepare(s, i, o, t, work, new, did, deadline).unwrap(), ()) },
    }
}

pub open spec fn add_timer_action() -> Action<Cluster, (Id, Origin, AKey, Outcome), ()> {
    Action {
        precondition: |input: (Id, Origin, AKey, Outcome), s: Cluster| { let i = input.0; let o = input.1; let k = input.2; let out = input.3; add_timer(s, i, o, k, out) is Some },
        transition: |input: (Id, Origin, AKey, Outcome), s: Cluster| { let i = input.0; let o = input.1; let k = input.2; let out = input.3; (add_timer(s, i, o, k, out).unwrap(), ()) },
    }
}

pub open spec fn process_action() -> Action<Cluster, (Id, Origin, Seq<char>, Outcome), ()> {
    Action {
        precondition: |input: (Id, Origin, Seq<char>, Outcome), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; let out = input.3; process_doc(s, i, o, e, out) is Some },
        transition: |input: (Id, Origin, Seq<char>, Outcome), s: Cluster| { let i = input.0; let o = input.1; let e = input.2; let out = input.3; (process_doc(s, i, o, e, out).unwrap(), ()) },
    }
}

pub open spec fn del_timer_action() -> Action<Cluster, (Id, Origin, bool, bool), ()> {
    Action {
        precondition: |input: (Id, Origin, bool, bool), s: Cluster| { let i = input.0; let o = input.1; let prev = input.2; let fired = input.3; del_timer(s, i, o, prev, fired) is Some },
        transition: |input: (Id, Origin, bool, bool), s: Cluster| { let i = input.0; let o = input.1; let prev = input.2; let fired = input.3; (del_timer(s, i, o, prev, fired).unwrap(), ()) },
    }
}

pub open spec fn done_action() -> Action<Cluster, (Id, Origin), ()> {
    Action {
        precondition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; done(s, i, o) is Some },
        transition: |input: (Id, Origin), s: Cluster| { let i = input.0; let o = input.1; (done(s, i, o).unwrap(), ()) },
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
        Step::Prepare(i, o, t, work, new, did, deadline) => prepare_action().forward((i, o, t, work, new, did, deadline))(s, s2),
        Step::AddTimer(i, o, k, out) => add_timer_action().forward((i, o, k, out))(s, s2),
        Step::Process(i, o, e, out) => process_action().forward((i, o, e, out))(s, s2),
        Step::DelTimer(i, o, prev, fired) => del_timer_action().forward((i, o, prev, fired))(s, s2),
        Step::Done(i, o) => done_action().forward((i, o))(s, s2),
    }
}

pub open spec fn next() -> spec_fn(Cluster, Cluster) -> bool {
    |s: Cluster, s2: Cluster| exists |st: Step| #[trigger] next_step(s, s2, st)
}

} // verus!
