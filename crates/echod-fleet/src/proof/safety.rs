//! The invariant, and the induction that keeps it.
//!
//! Three theorems come out of it:
//!
//! - **Catalogue.** Every document in the bucket satisfies the kernel's
//!   catalogue at the instant it was written.
//! - **Timers.** Every deadline in every document has a deadline key in the
//!   bucket at or before it — at all times, through every commit, crash and
//!   collection, whoever acts.
//! - **Revalidation.** A cached body whose version the bucket still holds
//!   is the bucket's document: a conditional read that says not modified
//!   can be trusted.
//!
//! All three rest on the commit protocol alone: the key before the
//! document, the document conditionally on the version loaded, a remembered
//! key relied on only for the version it was written with, a fired key
//! deleted only by the node that armed it or after a conditional rewrite
//! that found nothing due. No clock is assumed anything of.

use vstd::prelude::*;

use crate::node::core::*;
use crate::node::step::*;
use crate::node::txn::*;
use crate::spec::cluster::*;
use crate::tla::defs::*;
use crate::tla::rules::*;
use echod_kernel::external::spec_handle;
use echod_kernel::internal::spec_fire;
use echod_kernel::types::{origin, AOccurrence, ARequest, ASchedule};
use echod_kernel::external_proof::lemma_spec_handle;
use echod_kernel::types::MAX_TIME;

verus! {

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

/// The store holds the version a commit expects.
pub open spec fn live(s: Cluster, o: Origin, x: Flight) -> bool {
    s.store.etag(o) == x.cur
}

pub open spec fn has_any(d: Doc) -> bool {
    exists |t: nat| has_deadline(d, t)
}

/// The document is the one a written commit left, covered by the key it kept.
pub open spec fn kept_covers(s: Cluster, o: Origin, x: Flight) -> bool {
    &&& s.store.docs.contains_key(o) && s.store.docs[o] == x.new
    &&& match spec_keep(x.c) {
        Some(k) => s.hist.keeper.contains_key(o) && s.hist.keeper[o] == k,
        None => true,
    }
}

/// A cache entry names a version that exists, which the body cache holds,
/// filled no later than the clock.
pub open spec fn inv_cache(s: Cluster, i: Id, o: Origin) -> bool {
    let n = s.nodes[i];
    let e = n.core.cache[o];
    &&& e.filled_at <= n.clock
    &&& s.store.docs.contains_key(o)
    &&& n.bodies.contains_key(o)
    &&& s.hist.versions.contains_key(e.etag)
    &&& n.bodies[o] == s.hist.versions[e.etag]
}

/// A remembered key: this node's, for this origin; and while the document
/// is still the version it was written with, it is the document's cover.
pub open spec fn inv_armed(s: Cluster, i: Id, o: Origin) -> bool {
    let a = s.nodes[i].core.armed[o];
    &&& a.key.origin == o
    &&& s.hist.armer.contains_key(a.key) && s.hist.armer[a.key] == i
    &&& s.hist.versions.contains_key(a.etag)
    &&& s.hist.writer[a.etag] == i
    &&& s.store.etag(o) == Some(a.etag) ==> s.store.docs.contains_key(o) && s.hist.keeper.contains_key(o) && s.hist.keeper[o] == a.key && has_any(s.store.docs[o])
    // the key was not fired by a commit of another node that wrote an earlier version
    &&& forall |j: Id| #[trigger] s.nodes.contains_key(j) && j != i && s.nodes[j].txns.contains_key(o) && s.nodes[j].txns[o].phase is Written
        && s.hist.order[Event::Born(a.etag)] >= s.hist.order[Event::Born(s.nodes[j].txns[o].cur.unwrap())]
        ==> Some(a.key) != s.nodes[j].txns[o].c.fired
}

/// The promise schedule `sid`'s row `c` fired at `t` is in the bucket, in
/// its origin's document.
pub open spec fn has_promise(s: Cluster, c: ASchedule, sid: Seq<char>, t: nat) -> bool {
    let pid = expand(c.promise_id, sid, t);
    s.store.docs.contains_key(origin(pid)) && s.store.docs[origin(pid)].objects.contains_key(pid)
}

/// Every row with a last run has that run's promise in the bucket.
pub open spec fn runs_have_promises(s: Cluster, d: Doc) -> bool {
    forall |sid: Seq<char>| #[trigger] d.schedules.contains_key(sid) && d.schedules[sid].last_run_at is Some
        ==> has_promise(s, d.schedules[sid], sid, d.schedules[sid].last_run_at.unwrap() as nat)
}

/// A fire's second half, waiting on its first: what it will commit is
/// decided, satisfies the catalogue, is shaped for the schedule's
/// document, and was loaded at a version the bucket wrote; the key it
/// fires is the schedule's, armed, and due. Its row's last run is the
/// occurrence the first half commits, whose promise is in the origin's
/// document once that commit has landed, or when it had nothing to land.
pub open spec fn inv_pending(s: Cluster, o: Origin, x: Flight, p: Pending) -> bool {
    &&& is_sched(p.target) && p.target != o
    &&& origin(p.pid) == o
    &&& x.new.objects.contains_key(p.pid)
    &&& x.phase is Written ==> s.store.docs.contains_key(o) && s.store.docs[o].objects.contains_key(p.pid)
    &&& x.new == x.loaded ==> s.store.docs.contains_key(o) && s.store.docs[o].objects.contains_key(p.pid)
    &&& forall |sid: Seq<char>| #[trigger] p.new.schedules.contains_key(sid) && p.new.schedules[sid].last_run_at is Some
        ==> has_promise(s, p.new.schedules[sid], sid, p.new.schedules[sid].last_run_at.unwrap() as nat)
            || expand(p.new.schedules[sid].promise_id, sid, p.new.schedules[sid].last_run_at.unwrap() as nat) == p.pid
    &&& echod_kernel::properties::inv(x.t, full(p.loaded))
    &&& echod_kernel::properties::inv(x.t, full(p.new))
    &&& next_is(p.new, p.deadline)
    &&& shaped(p.target, p.loaded) && shaped(p.target, p.new)
    &&& p.new != p.loaded
    &&& p.fired.origin == p.target && p.fired.at <= x.t && s.hist.armer.contains_key(p.fired)
    &&& p.cur is Some ==> s.hist.versions.contains_key(p.cur.unwrap()) && s.hist.versions[p.cur.unwrap()] == p.loaded
    &&& p.cur is None ==> p.loaded == empty_doc()
    &&& s.store.etag(p.target) == p.cur ==> s.store.stamp(p.target) <= x.t
}

/// A commit in flight: what it loaded, what it decided, and where in the
/// bucket's order of events each of its keys and versions falls.
pub open spec fn inv_txn(s: Cluster, i: Id, o: Origin) -> bool {
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    &&& c.origin == o
    &&& shaped(o, x.loaded) && shaped(o, x.new)
    &&& x.loaded.objects.dom() <= x.new.objects.dom()
    &&& runs_have_promises(s, x.new)
    &&& match x.then { Some(p) => inv_pending(s, o, x, p), None => true }
    // the order of events: what it loaded was written before it began; what it armed, after
    &&& x.seq0 <= s.hist.counter
    &&& x.lseq <= x.seq0
    &&& !(x.phase is Written) ==> x.letag == x.cur
    &&& x.letag is Some ==> s.hist.versions.contains_key(x.letag.unwrap()) && s.hist.order[Event::Born(x.letag.unwrap())] == x.lseq
    &&& x.letag is None ==> x.lseq == 0
    &&& c.fired is Some ==> s.hist.order[Event::Armed(c.fired.unwrap())] < x.seq0
    &&& c.previous is Some ==> s.hist.order[Event::Armed(c.previous.unwrap())] < x.seq0
        && n.core.armed.contains_key(o) && n.core.armed[o].key == c.previous.unwrap() && Some(n.core.armed[o].etag) == x.letag
    &&& c.armed_now is Some ==> s.hist.order[Event::Armed(c.armed_now.unwrap())] >= x.seq0
    &&& x.phase is Written ==> {
        &&& s.hist.order[Event::Born(x.cur.unwrap())] >= x.seq0
        &&& s.hist.writer[x.cur.unwrap()] == i
        &&& s.store.etags.contains_key(o) && s.hist.order[Event::Born(s.store.etags[o])] >= s.hist.order[Event::Born(x.cur.unwrap())]
        // no other node's version landed between its load and its write
        &&& forall |j: Id| #[trigger] s.nodes.contains_key(j) && j != i && s.nodes[j].txns.contains_key(o) && s.nodes[j].txns[o].phase is Written
            && s.hist.order[Event::Born(s.nodes[j].txns[o].cur.unwrap())] < s.hist.order[Event::Born(x.cur.unwrap())]
            ==> x.lseq >= s.hist.order[Event::Born(s.nodes[j].txns[o].cur.unwrap())]
    }
    &&& x.t <= MAX_TIME
    &&& echod_kernel::properties::inv(x.t, full(x.loaded))
    &&& echod_kernel::properties::inv(x.t, full(x.new))
    &&& next_is(x.new, c.deadline)
    &&& c.fired is Some ==> c.fired.unwrap().origin == o && c.fired.unwrap().at <= x.t && s.hist.armer.contains_key(c.fired.unwrap())
    &&& !c.changed ==> x.new == x.loaded && (c.fired is Some ==> no_due(x.t, x.loaded))
    &&& c.rearm == (c.changed && c.deadline is Some && (c.previous is None || c.previous.unwrap().at != c.deadline.unwrap()))
    &&& c.previous is Some ==> {
        let q = c.previous.unwrap();
        &&& q.origin == o
        &&& s.hist.armer.contains_key(q) && s.hist.armer[q] == i
        &&& Some(q) != c.fired
        &&& !(x.phase is Written) && live(s, o, x) ==> s.store.docs.contains_key(o) && s.hist.keeper.contains_key(o) && s.hist.keeper[o] == q && has_any(s.store.docs[o])
    }
    &&& x.phase is Decided ==> c.armed_now is None
    &&& x.phase is Armed ==> c.rearm && c.armed_now is Some
    &&& c.armed_now is Some ==> {
        let k = c.armed_now.unwrap();
        &&& k.origin == o
        &&& Some(k.at) == c.deadline
        &&& s.hist.armer.contains_key(k) && s.hist.armer[k] == i
        &&& Some(k) != c.previous
        &&& Some(k) != c.fired
        &&& !(x.phase is Written) && live(s, o, x) ==> s.store.timers.contains(k)
    }
    &&& x.cur is Some ==> s.hist.versions.contains_key(x.cur.unwrap())
    &&& !(x.phase is Written) ==> (live(s, o, x) ==> s.store.doc(o) == x.loaded && s.store.stamp(o) <= x.t)
    &&& x.phase is Written ==> {
        &&& c.changed
        &&& x.cur is Some
        &&& c.rearm ==> c.armed_now is Some
        &&& live(s, o, x) ==> kept_covers(s, o, x) && s.store.stamps.contains_key(o) && s.store.stamps[o] == x.t
        // the document's cover is never the key it fired, nor the key it removes
        &&& kept_covers(s, o, x) || (!live(s, o, x) && (s.hist.keeper.contains_key(o) ==>
            Some(s.hist.keeper[o]) != c.fired && ((c.rearm || c.deadline is None) ==> Some(s.hist.keeper[o]) != c.previous)))
    }
}

/// Every document satisfies the catalogue at its stamp, and is the content
/// of its version.
pub open spec fn inv_store(s: Cluster) -> bool {
    &&& forall |o: Origin| #[trigger] s.store.docs.contains_key(o) ==> {
        &&& s.store.etags.contains_key(o)
        &&& s.store.stamps.contains_key(o)
        &&& s.store.stamps[o] <= MAX_TIME
        &&& echod_kernel::properties::inv(s.store.stamps[o], full(s.store.docs[o]))
        &&& shaped(o, s.store.docs[o])
        &&& runs_have_promises(s, s.store.docs[o])
        &&& s.hist.versions.contains_key(s.store.etags[o])
        &&& s.hist.versions[s.store.etags[o]] == s.store.docs[o]
    }
    &&& forall |o: Origin| #[trigger] s.store.etags.contains_key(o) ==> s.store.docs.contains_key(o)
    &&& forall |k: AKey| #[trigger] s.store.timers.contains(k) ==> s.hist.armer.contains_key(k)
    &&& forall |k: AKey| #[trigger] s.hist.armer.contains_key(k) ==> s.hist.order.contains_key(Event::Armed(k)) && s.hist.order[Event::Armed(k)] < s.hist.counter
    &&& forall |e: Seq<char>| #[trigger] s.hist.versions.contains_key(e) ==>
        s.hist.order.contains_key(Event::Born(e)) && s.hist.order[Event::Born(e)] < s.hist.counter && s.hist.writer.contains_key(e)
    &&& forall |e1: Seq<char>, e2: Seq<char>| #[trigger] s.hist.versions.contains_key(e1) && #[trigger] s.hist.versions.contains_key(e2)
        && s.hist.order[Event::Born(e1)] == s.hist.order[Event::Born(e2)] ==> e1 == e2
}

/// Every document with a deadline is covered: its keeper is in the bucket,
/// for it, at its nearest deadline.
pub open spec fn inv_timer(s: Cluster) -> bool {
    forall |o: Origin| #[trigger] s.store.docs.contains_key(o) && has_any(s.store.docs[o]) ==> {
        &&& s.hist.keeper.contains_key(o)
        &&& s.store.timers.contains(s.hist.keeper[o])
        &&& s.hist.keeper[o].origin == o
        &&& is_next(s.store.docs[o], s.hist.keeper[o].at)
    }
}

pub open spec fn inv() -> spec_fn(Cluster) -> bool {
    |s: Cluster| {
        &&& inv_store(s)
        &&& inv_timer(s)
        &&& forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.cache.contains_key(o) ==> inv_cache(s, i, o)
        &&& forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.armed.contains_key(o) ==> inv_armed(s, i, o)
        &&& forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(o) ==> inv_txn(s, i, o)
    }
}

/// The invariant from its conjuncts, stated so each lemma proves them apart.
pub proof fn assemble(s: Cluster)
    requires
        inv_store(s),
        inv_timer(s),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.cache.contains_key(o) ==> inv_cache(s, i, o),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.armed.contains_key(o) ==> inv_armed(s, i, o),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(o) ==> inv_txn(s, i, o),
    ensures
        inv()(s),
{
}

/// The invariant's conjuncts from the invariant.
pub proof fn disassemble(s: Cluster)
    requires inv()(s),
    ensures
        inv_store(s),
        inv_timer(s),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.cache.contains_key(o) ==> inv_cache(s, i, o),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.armed.contains_key(o) ==> inv_armed(s, i, o),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(o) ==> inv_txn(s, i, o),
{
}

// ---------------------------------------------------------------------------
// The theorems, from the invariant
// ---------------------------------------------------------------------------

/// A cached body whose version the bucket still holds is the bucket's
/// document: a conditional read answered "not modified" may be served
/// from the cache.
pub proof fn revalidation(s: Cluster, i: Id, o: Origin)
    requires
        inv()(s),
        s.nodes.contains_key(i),
        s.nodes[i].core.cache.contains_key(o),
        Some(s.nodes[i].core.cache[o].etag) == s.store.etag(o),
    ensures
        s.store.docs.contains_key(o),
        s.nodes[i].bodies.contains_key(o),
        s.nodes[i].bodies[o] == s.store.docs[o],
{
    assert(inv_cache(s, i, o));
}

/// Every document in the bucket satisfies the kernel's catalogue at the
/// instant it was written.
pub proof fn catalogue(s: Cluster, o: Origin)
    requires
        inv()(s),
        s.store.docs.contains_key(o),
    ensures
        echod_kernel::properties::inv(s.store.stamps[o], full(s.store.docs[o])),
{
}

/// Every deadline in every document has a deadline key in the bucket for
/// its origin, at or before it.
pub proof fn timers_cover(s: Cluster, o: Origin, t: nat)
    requires
        inv()(s),
        s.store.docs.contains_key(o),
        has_deadline(s.store.docs[o], t),
    ensures
        exists |k: AKey| #[trigger] s.store.timers.contains(k) && k.origin == o && k.at <= t,
{
    let k = s.hist.keeper[o];
    assert(s.store.timers.contains(k) && k.origin == o && k.at <= t);
}

/// In particular: every pending promise that is not internal has a timer
/// at or before its deadline, every acquired task at or before its lease,
/// every pending task at or before its retry.
pub proof fn promises_have_timers(s: Cluster, o: Origin, id: Seq<char>)
    requires
        inv()(s),
        s.store.docs.contains_key(o),
        s.store.docs[o].objects.contains_key(id),
    ensures
        ({ let q = s.store.docs[o].objects[id];
            q.state == echod_kernel::types::PromiseState::Pending && q.otype() != echod_kernel::tags::OType::Internal
                ==> exists |k: AKey| #[trigger] s.store.timers.contains(k) && k.origin == o && k.at <= q.timeout_at }),
        ({ let q = s.store.docs[o].objects[id];
            lease_deadline(q) is Some ==> exists |k: AKey| #[trigger] s.store.timers.contains(k) && k.origin == o && k.at <= lease_deadline(q).unwrap() }),
        ({ let q = s.store.docs[o].objects[id];
            retry_deadline(q) is Some ==> exists |k: AKey| #[trigger] s.store.timers.contains(k) && k.origin == o && k.at <= retry_deadline(q).unwrap() }),
{
    let d = s.store.docs[o];
    let q = d.objects[id];
    if q.state == echod_kernel::types::PromiseState::Pending && q.otype() != echod_kernel::tags::OType::Internal {
        assert(deadline_at(q, q.timeout_at as nat));
        assert(objects_deadline(d.objects, q.timeout_at as nat));
        timers_cover(s, o, q.timeout_at as nat);
    }
    if lease_deadline(q) is Some {
        let t = lease_deadline(q).unwrap();
        assert(deadline_at(q, t));
        assert(objects_deadline(d.objects, t));
        timers_cover(s, o, t);
    }
    if retry_deadline(q) is Some {
        let t = retry_deadline(q).unwrap();
        assert(deadline_at(q, t));
        assert(objects_deadline(d.objects, t));
        timers_cover(s, o, t);
    }
}

/// Every occurrence a schedule has fired has its promise: the schedule's
/// row says its last run, and the promise its template expands to at
/// that run is in the bucket, in its origin's document.
pub proof fn occurrences(s: Cluster, o: Origin, id: Seq<char>)
    requires
        inv()(s),
        s.store.docs.contains_key(o),
        s.store.docs[o].schedules.contains_key(id),
        s.store.docs[o].schedules[id].last_run_at is Some,
    ensures
        ({ let c = s.store.docs[o].schedules[id];
            let pid = expand(c.promise_id, id, c.last_run_at.unwrap() as nat);
            s.store.docs.contains_key(origin(pid)) && s.store.docs[origin(pid)].objects.contains_key(pid) }),
{
    assert(runs_have_promises(s, s.store.docs[o]));
}

/// And every schedule has a timer at or before its next run.
pub proof fn schedules_have_timers(s: Cluster, o: Origin, id: Seq<char>)
    requires
        inv()(s),
        s.store.docs.contains_key(o),
        s.store.docs[o].schedules.contains_key(id),
    ensures
        exists |k: AKey| #[trigger] s.store.timers.contains(k) && k.origin == o && k.at <= s.store.docs[o].schedules[id].next_run_at,
{
    let d = s.store.docs[o];
    let t = d.schedules[id].next_run_at as nat;
    assert(schedules_deadline(d.schedules, t));
    timers_cover(s, o, t);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// The catalogue holds of an empty document at any instant.
proof fn lemma_inv_empty(t: nat)
    ensures echod_kernel::properties::inv(t, full(empty_doc())),
{
    reveal(echod_kernel::properties::inv);
}

/// An id's origin runs to the first colon, so it never names a schedule's
/// document.
proof fn lemma_origin_no_colon(id: Seq<char>)
    ensures forall |j: int| 0 <= j < origin(id).len() ==> #[trigger] origin(id)[j] != ':',
    decreases id.len(),
{
    if id.len() == 0 || id[0] == ':' {
    } else {
        lemma_origin_no_colon(id.drop_first());
        let r = seq![id[0]] + origin(id.drop_first());
        assert forall |j: int| 0 <= j < r.len() implies #[trigger] r[j] != ':' by {
            if j > 0 {
                assert(r[j] == origin(id.drop_first())[j - 1]);
            }
        }
    }
}

proof fn lemma_origin_not_sched(id: Seq<char>)
    ensures !is_sched(origin(id)),
{
    lemma_origin_no_colon(id);
    if is_sched(origin(id)) {
        assert(origin(id).take(6)[5] == "sched:"@[5]);
        assert("sched:"@[5] == ':') by { reveal_strlit("sched:"); }
        assert(origin(id)[5] == ':');
    }
}

/// A document the kernel reached at `t` from one satisfying the catalogue
/// satisfies it.
proof fn lemma_kreach_inv(t: nat, a: Doc, b: Doc)
    requires kreach(t, a, b),
    ensures echod_kernel::properties::inv(t, full(b)),
{
    let (sa, sb) = choose |sa: echod_kernel::store::AState, sb: echod_kernel::store::AState|
        strip(sa) == a && strip(sb) == b && echod_kernel::properties::inv(t, sa) && #[trigger] reach(t, sa, sb);
    lemma_reach_inv(t, sa, sb);
    lemma_inv_full(t, sb);
}

// ---------------------------------------------------------------------------
// The induction
// ---------------------------------------------------------------------------

pub proof fn lemma_init(s: Cluster)
    requires init_state(s),
    ensures inv()(s),
{
}

/// Node `i` keeps its part; the store and every other node are as they were.
proof fn lemma_node_only(s: Cluster, s2: Cluster, i: Id)
    requires
        inv()(s),
        s2.store == s.store,
        s2.hist == s.hist,
        s2.nodes.contains_key(i),
        forall |k: Id| k != i ==> (s2.nodes.contains_key(k) <==> s.nodes.contains_key(k)) && (s.nodes.contains_key(k) ==> s2.nodes[k] == s.nodes[k]),
        forall |o: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(o) ==> inv_cache(s2, i, o),
        forall |o: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(o) ==> inv_armed(s2, i, o),
        forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) ==> inv_txn(s2, i, o),
        // a written commit of node i is as it was: other nodes' parts mention those
        forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) && s2.nodes[i].txns[o].phase is Written
            ==> s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(o) && s2.nodes[i].txns[o] == s.nodes[i].txns[o],
    ensures inv()(s2),
{
    disassemble(s);
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].core.cache.contains_key(o) implies inv_cache(s2, k, o) by {
        if k != i { assert(inv_cache(s, k, o)); }
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].core.armed.contains_key(o) implies inv_armed(s2, k, o) by {
        if k != i {
            assert(inv_armed(s, k, o));
            let a = s2.nodes[k].core.armed[o];
            assert forall |j: Id| #[trigger] s2.nodes.contains_key(j) && j != k && s2.nodes[j].txns.contains_key(o) && s2.nodes[j].txns[o].phase is Written
                && s2.hist.order[Event::Born(a.etag)] >= s2.hist.order[Event::Born(s2.nodes[j].txns[o].cur.unwrap())]
                implies Some(a.key) != s2.nodes[j].txns[o].c.fired by {
                if j == i {
                    assert(s2.nodes[i].txns.contains_key(o) && s2.nodes[i].txns[o].phase is Written);
                    assert(s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(o) && s2.nodes[i].txns[o] == s.nodes[i].txns[o]);
                } else {
                    assert(s2.nodes[j] == s.nodes[j]);
                }
                assert(s.nodes.contains_key(j) && s.nodes[j].txns.contains_key(o) && s.nodes[j].txns[o] == s2.nodes[j].txns[o]);
            }
        }
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].txns.contains_key(o) implies inv_txn(s2, k, o) by {
        if k != i {
            assert(inv_txn(s, k, o));
            let x = s2.nodes[k].txns[o];
            if x.phase is Written {
                assert forall |j: Id| #[trigger] s2.nodes.contains_key(j) && j != k && s2.nodes[j].txns.contains_key(o) && s2.nodes[j].txns[o].phase is Written
                    && s2.hist.order[Event::Born(s2.nodes[j].txns[o].cur.unwrap())] < s2.hist.order[Event::Born(x.cur.unwrap())]
                    implies x.lseq >= s2.hist.order[Event::Born(s2.nodes[j].txns[o].cur.unwrap())] by {
                    if j == i {
                        assert(s2.nodes[i].txns.contains_key(o) && s2.nodes[i].txns[o].phase is Written);
                        assert(s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(o) && s2.nodes[i].txns[o] == s.nodes[i].txns[o]);
                    } else {
                        assert(s2.nodes[j] == s.nodes[j]);
                    }
                    assert(s.nodes.contains_key(j) && s.nodes[j].txns.contains_key(o) && s.nodes[j].txns[o] == s2.nodes[j].txns[o]);
                }
            }
        }
    }
    assert(inv_store(s2));
    assert(inv_timer(s2));
    assemble(s2);
}

proof fn lemma_tick(s: Cluster, s2: Cluster, i: Id, d: nat)
    requires inv()(s), tick(s, i, d) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(o) implies inv_cache(s2, i, o) by { assert(inv_cache(s, i, o)); }
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(o) implies inv_armed(s2, i, o) by { assert(inv_armed(s, i, o)); }
    assert forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) implies inv_txn(s2, i, o) by { assert(inv_txn(s, i, o)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q].phase is Written
        implies s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q] == s.nodes[i].txns[q] by {}
    lemma_node_only(s, s2, i);
}

proof fn lemma_join(s: Cluster, s2: Cluster, i: Id, c: nat)
    requires inv()(s), join(s, i, c) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(o) implies inv_cache(s2, i, o) by {}
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(o) implies inv_armed(s2, i, o) by {}
    assert forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) implies inv_txn(s2, i, o) by {}
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q].phase is Written
        implies s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q] == s.nodes[i].txns[q] by {}
    lemma_node_only(s, s2, i);
}

proof fn lemma_crash(s: Cluster, s2: Cluster, i: Id)
    requires inv()(s), crash(s, i) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(o) implies inv_cache(s2, i, o) by { assert(inv_cache(s, i, o)); }
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(o) implies inv_armed(s2, i, o) by { assert(inv_armed(s, i, o)); }
    assert forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) implies inv_txn(s2, i, o) by { assert(inv_txn(s, i, o)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q].phase is Written
        implies s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q] == s.nodes[i].txns[q] by {}
    lemma_node_only(s, s2, i);
}

proof fn lemma_forget(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv()(s), forget(s, i, o) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(s2, i, q) by { assert(inv_cache(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(s2, i, q) by { assert(inv_txn(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q].phase is Written
        implies s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q] == s.nodes[i].txns[q] by {}
    lemma_node_only(s, s2, i);
}

// --- the commit protocol ---

/// A document kernel steps reach at `t` from a state the catalogue holds of
/// satisfies the catalogue.
proof fn lemma_kreach_from_inv(t: nat, a: echod_kernel::store::AState, b: Doc)
    requires kreach_from(t, a, b), echod_kernel::properties::inv(t, a),
    ensures echod_kernel::properties::inv(t, full(b)),
{
    let sb = choose |sb: echod_kernel::store::AState| strip(sb) == b && #[trigger] reach(t, a, sb);
    lemma_reach_inv(t, a, sb);
    lemma_inv_full(t, sb);
}

/// What was loaded has its runs' promises: the bucket's document does,
/// and an empty one has no runs.
proof fn lemma_loaded_runs(s: Cluster, o: Origin)
    requires inv()(s),
    ensures runs_have_promises(s, s.store.doc(o)),
{
    disassemble(s);
    if s.store.docs.contains_key(o) {
        assert(runs_have_promises(s, s.store.docs[o]));
    } else {
        assert(s.store.doc(o) == empty_doc());
        assert forall |sid: Seq<char>| #[trigger] empty_doc().schedules.contains_key(sid) && empty_doc().schedules[sid].last_run_at is Some implies false by {}
    }
}

/// On a schedule's document a request is one of the schedule's three; the
/// handler's schedules are the loaded ones, less one, or plus one with no
/// run yet.
proof fn lemma_sched_request_runs(s: Cluster, o: Origin, req: ARequest, t: nat, d: Doc)
    requires inv()(s), is_sched(o), request_target(req) == Some(o), d.schedules == spec_handle(full(s.store.doc(o)), req, t).0.schedules,
    ensures runs_have_promises(s, d),
{
    lemma_loaded_runs(s, o);
    let loaded = s.store.doc(o);
    match req {
        ARequest::ScheduleGet(q) => {}
        ARequest::ScheduleCreate(q) => {
            let h = echod_kernel::external::spec_schedule_create(full(loaded), q, t).0;
            assert forall |sid: Seq<char>| #[trigger] d.schedules.contains_key(sid) && d.schedules[sid].last_run_at is Some
                implies has_promise(s, d.schedules[sid], sid, d.schedules[sid].last_run_at.unwrap() as nat) by {
                if sid == q.id && !loaded.schedules.contains_key(q.id) {
                    assert(d.schedules[sid].last_run_at is None);
                } else {
                    assert(loaded.schedules.contains_key(sid) && d.schedules[sid] == loaded.schedules[sid]);
                }
            }
        }
        ARequest::ScheduleDelete(q) => {}
        ARequest::PromiseGet(q) => { lemma_origin_not_sched(q.id); }
        ARequest::PromiseCreate(q) => { lemma_origin_not_sched(q.id); }
        ARequest::PromiseSettle(q) => { lemma_origin_not_sched(q.id); }
        ARequest::PromiseRegisterCallback(q) => { lemma_origin_not_sched(q.awaited); }
        ARequest::PromiseRegisterListener(q) => { lemma_origin_not_sched(q.awaited); }
        ARequest::TaskGet(q) => { lemma_origin_not_sched(q.id); }
        ARequest::TaskCreate(q) => { lemma_origin_not_sched(q.action.id); }
        ARequest::TaskAcquire(q) => { lemma_origin_not_sched(q.id); }
        ARequest::TaskFulfill(q) => { lemma_origin_not_sched(q.id); }
        ARequest::TaskRelease(q) => { lemma_origin_not_sched(q.id); }
        ARequest::TaskHalt(q) => { lemma_origin_not_sched(q.id); }
        ARequest::TaskContinue(q) => { lemma_origin_not_sched(q.id); }
        ARequest::TaskFence(q) => { lemma_origin_not_sched(q.id); }
        ARequest::TaskHeartbeat(q) => { if q.tasks.len() > 0 { lemma_origin_not_sched(q.tasks[0].id); } }
        ARequest::TaskSuspend(q) => { lemma_origin_not_sched(q.id); }
    }
}

/// A fire's two documents satisfy the catalogue: the fired state does, the
/// steps after keep it, and each document is one side of the result.
proof fn lemma_kreach_fire_inv(t: nat, a: echod_kernel::store::AState, o: Doc, c: Doc)
    requires kreach_fire(t, a, o, c), echod_kernel::properties::inv(t, a),
    ensures echod_kernel::properties::inv(t, full(o)), echod_kernel::properties::inv(t, full(c)),
{
    let sb = choose |sb: echod_kernel::store::AState| objects_only(sb) == o && schedules_only(sb) == c && #[trigger] reach(t, a, sb);
    lemma_reach_inv(t, a, sb);
    lemma_inv_objects_only(t, sb);
    lemma_inv_schedules_only(t, sb);
}

proof fn lemma_prepare(s: Cluster, s2: Cluster, i: Id, o: Origin, t: nat, work: Work, new: Doc, did: bool, deadline: Option<nat>)
    requires inv()(s), prepare(s, i, o, t, work, new, did, deadline) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    let n = s.nodes[i];
    let n2 = s2.nodes[i];
    let x = n2.txns[o];
    assert(x.loaded == s.store.doc(o));
    if s.store.docs.contains_key(o) {
        lemma_inv_at(s.store.stamps[o], t, full(s.store.docs[o]));
    } else {
        lemma_inv_empty(t);
    }
    assert(echod_kernel::properties::inv(t, full(x.loaded)));
    lemma_loaded_runs(s, o);
    match work {
        Work::Sweep(_) => {
            lemma_kreach_inv(t, x.loaded, x.new);
            // an origin's document has no runs; a schedule's is as loaded
            if is_sched(o) {
                assert(x.new == x.loaded);
            }
            assert(runs_have_promises(s2, x.new));
        }
        Work::Request(req) => {
            // the handler keeps the catalogue; the drain keeps it from there
            lemma_spec_handle(t, full(x.loaded), req);
            lemma_kreach_from_inv(t, spec_handle(full(x.loaded), req, t).0, x.new);
            if is_sched(o) {
                lemma_sched_request_runs(s, o, req, t, x.new);
            }
            assert(runs_have_promises(s2, x.new));
        }
        Work::Fire(k, sid, pid, next, deadline_s) => {
            // the origin's objects beside the schedule's row satisfy the
            // catalogue; firing keeps it; the steps after keep it; each
            // document is one side of the result
            let st = sched_target(sid);
            let sd = s.store.doc(st);
            let p = x.then.unwrap();
            lemma_origin_not_sched(pid);
            assert(!is_sched(o));
            assert(is_sched(st)) by { reveal_strlit("sched:"); assert(st.take(6) =~= "sched:"@); }
            if s.store.docs.contains_key(st) {
                lemma_inv_at(s.store.stamps[st], t, full(s.store.docs[st]));
            } else {
                lemma_inv_empty(t);
            }
            assert(echod_kernel::properties::inv(t, full(sd)));
            assert(shaped(st, sd));
            lemma_inv_joint(t, x.loaded, sd);
            let occ = AOccurrence { at: sd.schedules[sid].next_run_at, promise_id: pid };
            let occs: Seq<AOccurrence> = seq![occ];
            assert(occs.len() == 1 && occs[0] == occ);
            echod_kernel::internal_proof::lemma_spec_fire(t, joint(x.loaded, sd), sid, occs, next);
            lemma_kreach_fire_inv(t, spec_fire(joint(x.loaded, sd), sid, occs, next, t), x.new, p.new);
            // the second half: changed, since the run after is later
            assert(p.new.schedules[sid].next_run_at == next);
            assert(p.loaded.schedules[sid].next_run_at != next);
            assert(p.new != p.loaded);
            if s.store.etags.contains_key(st) {
                assert(s.hist.versions.contains_key(s.store.etags[st]));
            }
            // the occurrence's promise is in the fired state, which the steps after keep
            let fired = spec_fire(joint(x.loaded, sd), sid, occs, next, t);
            assert(fired.objects.contains_key(occs[0].promise_id));
            assert(x.new.objects.contains_key(pid));
            assert(x.loaded.objects.dom() <= fired.objects.dom());
            assert forall |y: Seq<char>| x.loaded.objects.dom().contains(y) implies x.new.objects.dom().contains(y) by {
                assert(fired.objects.dom().contains(y));
            }
            if x.new == x.loaded {
                assert(x.loaded.objects.contains_key(pid));
                assert(s.store.docs.contains_key(o));
            }
            // the schedule's rows after: the fired row's run is this occurrence; the rest as loaded
            lemma_loaded_runs(s, st);
            assert forall |q: Seq<char>| #[trigger] p.new.schedules.contains_key(q) && p.new.schedules[q].last_run_at is Some
                implies has_promise(s2, p.new.schedules[q], q, p.new.schedules[q].last_run_at.unwrap() as nat)
                    || expand(p.new.schedules[q].promise_id, q, p.new.schedules[q].last_run_at.unwrap() as nat) == p.pid by {
                if q == sid {
                    assert(p.new.schedules[q].last_run_at == Some(occ.at));
                    assert(p.new.schedules[q].promise_id == sd.schedules[sid].promise_id);
                } else {
                    assert(sd.schedules.contains_key(q) && p.new.schedules[q] == sd.schedules[q]);
                }
            }
            assert(runs_have_promises(s2, x.new));
            assert(inv_pending(s2, o, x, p));
        }
    }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(s2, i, q) by {
        if q == o && s.store.docs.contains_key(o) {
            assert(s.hist.versions.contains_key(s.store.etags[o]));
        } else {
            assert(inv_cache(s, i, q));
        }
    }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(s2, i, q) by {
        if q == o {
            let c = x.c;
            if c.previous is Some {
                assert(n.core.armed.contains_key(o));
                assert(inv_armed(s, i, o));
            }
            if x.cur is Some {
                assert(s.hist.versions.contains_key(x.cur.unwrap()));
            }
            assert(c.origin == o);
            assert(x.t <= MAX_TIME);
            assert(echod_kernel::properties::inv(x.t, full(x.loaded)));
            assert(echod_kernel::properties::inv(x.t, full(x.new)));
            assert(next_is(x.new, c.deadline));
            assert(c.fired is Some ==> c.fired.unwrap().origin == o && c.fired.unwrap().at <= x.t && s2.hist.armer.contains_key(c.fired.unwrap()));
            assert(!c.changed ==> x.new == x.loaded);
            assert(!c.changed && c.fired is Some ==> no_due(x.t, x.loaded));
            assert(c.rearm == (c.changed && c.deadline is Some && (c.previous is None || c.previous.unwrap().at != c.deadline.unwrap())));
            if c.previous is Some {
                let q = c.previous.unwrap();
                assert(q.origin == o);
                assert(s2.hist.armer.contains_key(q) && s2.hist.armer[q] == i);
                assert(Some(q) != c.fired);
                assert(live(s2, o, x));
                assert(s2.store.docs.contains_key(o) && s2.hist.keeper.contains_key(o) && s2.hist.keeper[o] == q && has_any(s2.store.docs[o]));
            }
            assert(x.phase is Decided && c.armed_now is None);
            assert(x.cur is Some ==> s2.hist.versions.contains_key(x.cur.unwrap()));
            assert(live(s2, o, x) ==> s2.store.doc(o) == x.loaded && s2.store.stamp(o) <= x.t);
            assert(inv_txn(s2, i, o));
        } else {
            assert(inv_txn(s, i, q));
        }
    }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q].phase is Written
        implies s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q] == s.nodes[i].txns[q] by {}
    lemma_node_only(s, s2, i);
}

/// Every node but `i` keeps its part when the store changes only in ways
/// that do not touch them: stated per lemma, this is the common frame.
proof fn lemma_arm(s: Cluster, s2: Cluster, i: Id, o: Origin, k: AKey)
    requires inv()(s), arm(s, i, o, k) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    assert(inv_txn(s, i, o));
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(s2, j, q) by {
        assert(inv_cache(s, j, q));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) implies inv_armed(s2, j, q) by {
        assert(inv_armed(s, j, q));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(s2, j, q) by {
        assert(inv_txn(s, j, q));
        if j == i && q == o {
            assert(inv_txn(s2, i, o));
        }
    }
    assert(inv_store(s2));
    assert(inv_timer(s2));
    assemble(s2);
}

proof fn lemma_commit_cache(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), commit(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) ==> inv_cache(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    let kept = spec_keep(c);
    if c.deadline is Some {
        if c.rearm {
            assert(x.phase is Armed);
            assert(s.store.timers.contains(c.armed_now.unwrap()));
        } else {
            let q = c.previous.unwrap();
            assert(s.hist.keeper[o] == q && has_any(s.store.docs[o]));
            assert(s.store.timers.contains(q));
        }
        assert(kept is Some && s2.store.timers.contains(kept.unwrap()) && Some(kept.unwrap().at) == c.deadline && kept.unwrap().origin == o);
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(s2, j, q) by {
        if j == i && q == o {
        } else {
            assert(inv_cache(s, j, q));
        }
    }
}

proof fn lemma_commit_armed(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), commit(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) ==> inv_armed(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    let kept = spec_keep(c);
    if c.deadline is Some {
        if c.rearm {
            assert(x.phase is Armed);
            assert(s.store.timers.contains(c.armed_now.unwrap()));
        } else {
            let q = c.previous.unwrap();
            assert(s.hist.keeper[o] == q && has_any(s.store.docs[o]));
            assert(s.store.timers.contains(q));
        }
        assert(kept is Some && s2.store.timers.contains(kept.unwrap()) && Some(kept.unwrap().at) == c.deadline && kept.unwrap().origin == o);
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) implies inv_armed(s2, j, q) by {
        assert(inv_armed(s, j, q));
    }
}

proof fn lemma_commit_txns(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), commit(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) ==> inv_txn(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    let kept = spec_keep(c);
    if c.deadline is Some {
        if c.rearm {
            assert(x.phase is Armed);
            assert(s.store.timers.contains(c.armed_now.unwrap()));
        } else {
            let q = c.previous.unwrap();
            assert(s.hist.keeper[o] == q && has_any(s.store.docs[o]));
            assert(s.store.timers.contains(q));
        }
        assert(kept is Some && s2.store.timers.contains(kept.unwrap()) && Some(kept.unwrap().at) == c.deadline && kept.unwrap().origin == o);
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(s2, j, q) by {
        assert(inv_txn(s, j, q));
        if j == i && q == o {
            assert(inv_txn(s2, i, o));
        } else if q == o {
            let y = s.nodes[j].txns[o];
            assert(j != i);
            assert(!live(s2, o, y));
            if y.phase is Written {
                if !kept_covers(s2, o, y) {
                    if s2.hist.keeper.contains_key(o) {
                        assert(s2.hist.keeper[o] == kept.unwrap());
                        assert(s2.hist.armer[kept.unwrap()] == i);
                    }
                }
            }
            assert(inv_txn(s2, j, q));
        } else {
            assert(inv_txn(s2, j, q));
        }
    }
}

proof fn lemma_commit_store(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), commit(s, i, o, e) == Some(s2),
    ensures inv_store(s2), inv_timer(s2),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    let kept = spec_keep(c);
    if c.deadline is Some {
        if c.rearm {
            assert(x.phase is Armed);
            assert(s.store.timers.contains(c.armed_now.unwrap()));
        } else {
            let q = c.previous.unwrap();
            assert(s.hist.keeper[o] == q && has_any(s.store.docs[o]));
            assert(s.store.timers.contains(q));
        }
        assert(kept is Some && s2.store.timers.contains(kept.unwrap()) && Some(kept.unwrap().at) == c.deadline && kept.unwrap().origin == o);
    }
    assert(inv_store(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) implies {
            &&& s2.store.etags.contains_key(q)
            &&& s2.store.stamps.contains_key(q)
            &&& s2.store.stamps[q] <= MAX_TIME
            &&& echod_kernel::properties::inv(s2.store.stamps[q], full(s2.store.docs[q]))
            &&& s2.hist.versions.contains_key(s2.store.etags[q])
            &&& s2.hist.versions[s2.store.etags[q]] == s2.store.docs[q]
        } by {
            if q != o {
                assert(s.store.docs.contains_key(q));
            }
        }
        assert forall |v: Seq<char>| #[trigger] s2.hist.versions.contains_key(v) implies s2.hist.order.contains_key(Event::Born(v)) && s2.hist.order[Event::Born(v)] < s2.hist.counter && s2.hist.writer.contains_key(v) by {
            if v != e { assert(s.hist.versions.contains_key(v)); }
        }
    }
    assert(inv_timer(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) && has_any(s2.store.docs[q]) implies {
            &&& s2.hist.keeper.contains_key(q)
            &&& s2.store.timers.contains(s2.hist.keeper[q])
            &&& s2.hist.keeper[q].origin == q
            &&& is_next(s2.store.docs[q], s2.hist.keeper[q].at)
        } by {
            if q == o {
                assert(c.deadline is Some);
            } else {
                assert(s.store.docs.contains_key(q) && has_any(s.store.docs[q]));
            }
        }
    }
}

proof fn lemma_commit(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), commit(s, i, o, e) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    lemma_commit_cache(s, s2, i, o, e);
    lemma_commit_armed(s, s2, i, o, e);
    lemma_commit_txns(s, s2, i, o, e);
    lemma_commit_store(s, s2, i, o, e);
    assemble(s2);
}

proof fn lemma_commit_fail(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv()(s), commit_fail(s, i, o) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(s2, i, q) by { assert(inv_cache(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(s2, i, q) by { assert(inv_txn(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q].phase is Written
        implies s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q] == s.nodes[i].txns[q] by {}
    lemma_node_only(s, s2, i);
}

proof fn lemma_disarm(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv()(s), disarm(s, i, o) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let q0 = spec_to_disarm(c).unwrap();
    assert(inv_txn(s, i, o));
    assert(c.previous == Some(q0));
    assert(s.hist.armer[q0] == i && q0.origin == o);
    assert(c.changed && (c.deadline is None || c.rearm));
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(s2, j, q) by {
        assert(inv_cache(s, j, q));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) implies inv_armed(s2, j, q) by {
        assert(inv_armed(s, j, q));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(s2, j, q) by {
        assert(inv_txn(s, j, q));
        let y = s.nodes[j].txns[q];
        if y.c.armed_now is Some {
            let k = y.c.armed_now.unwrap();
            if k == q0 {
                // the same key: same armer and origin, so this node's own on o — but this node's only commit on o is x, whose key is not its previous
                assert(s.hist.armer[k] == j);
                assert(j == i);
                assert(k.origin == q);
                assert(q == o);
                assert(y == x);
                assert(Some(k) != c.previous);
                assert(false);
            }
        }
    }
    assert(inv_store(s2));
    assert(inv_timer(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) && has_any(s2.store.docs[q]) implies {
            &&& s2.hist.keeper.contains_key(q)
            &&& s2.store.timers.contains(s2.hist.keeper[q])
            &&& s2.hist.keeper[q].origin == q
            &&& is_next(s2.store.docs[q], s2.hist.keeper[q].at)
        } by {
            assert(s.store.docs.contains_key(q) && has_any(s.store.docs[q]));
            if q == o {
                let kp = s.hist.keeper[o];
                if kept_covers(s, o, x) {
                    if c.deadline is None {
                        assert(!has_any(s.store.docs[o]));
                        assert(false);
                    } else {
                        assert(kp == c.armed_now.unwrap());
                        assert(kp != q0);
                    }
                } else {
                    assert(!live(s, o, x));
                    assert(Some(kp) != c.previous);
                    assert(kp != q0);
                }
            } else {
                assert(s.hist.keeper[q].origin == q);
                assert(s.hist.keeper[q] != q0);
            }
        }
    }
    assemble(s2);
}

proof fn lemma_finish_cache(s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv()(s), finish(s, i, o, deleted) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) ==> inv_cache(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_txn(s, i, o));
    let kept = spec_keep(c);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(s2, j, q) by {
        assert(inv_cache(s, j, q));
    }
}

proof fn lemma_finish_armed(s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv()(s), finish(s, i, o, deleted) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) ==> inv_armed(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_txn(s, i, o));
    let kept = spec_keep(c);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) implies inv_armed(s2, j, q) by {
        if j == i && q == o {
            // the key kept, with the version written
            assert(kept is Some);
            let k = kept.unwrap();
            assert(s2.nodes[i].core.armed[o].key == k && s2.nodes[i].core.armed[o].etag == e);
            if c.rearm {
                assert(k == c.armed_now.unwrap());
            } else {
                assert(k == c.previous.unwrap());
            }
            if s2.store.etag(o) == Some(e) {
                assert(live(s, o, x));
                assert(kept_covers(s, o, x));
                assert(has_deadline(x.new, c.deadline.unwrap()));
            }
            assert(s.hist.writer[e] == i);
            assert forall |j2: Id| #[trigger] s2.nodes.contains_key(j2) && j2 != i && s2.nodes[j2].txns.contains_key(o) && s2.nodes[j2].txns[o].phase is Written
                && s2.hist.order[Event::Born(e)] >= s2.hist.order[Event::Born(s2.nodes[j2].txns[o].cur.unwrap())]
                implies Some(k) != s2.nodes[j2].txns[o].c.fired by {
                let y = s.nodes[j2].txns[o];
                assert(inv_txn(s, j2, o));
                let ey = y.cur.unwrap();
                assert(s.hist.writer[ey] == j2);
                assert(ey != e);
                assert(s.hist.order[Event::Born(ey)] != s.hist.order[Event::Born(e)]);
                assert(s.hist.order[Event::Born(ey)] < s.hist.order[Event::Born(e)]);
                assert(x.lseq >= s.hist.order[Event::Born(ey)]);
                assert(s.hist.order[Event::Born(ey)] >= y.seq0);
                if y.c.fired is Some {
                    let f = y.c.fired.unwrap();
                    assert(s.hist.order[Event::Armed(f)] < y.seq0);
                    if c.rearm {
                        assert(s.hist.order[Event::Armed(k)] >= x.seq0);
                        assert(k != f);
                    } else {
                        assert(n.core.armed.contains_key(o) && n.core.armed[o].key == k && Some(n.core.armed[o].etag) == x.letag);
                        assert(inv_armed(s, i, o));
                        assert(s.hist.order[Event::Born(n.core.armed[o].etag)] == x.lseq);
                        assert(Some(k) != y.c.fired);
                    }
                }
            }
        } else {
            assert(inv_armed(s, j, q));
        }
    }
}

/// A fire's second half, as a commit of its own: everything the Decided
/// phase asks follows from what was kept of it while the first half ran,
/// and from the node's key for the schedule's document, which the first
/// half did not touch.
proof fn lemma_continued(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires
        inv()(s),
        s.nodes.contains_key(i),
        s.nodes[i].txns.contains_key(o),
        s.nodes[i].txns[o].then is Some,
        s.nodes[i].txns[o].phase is Written || s.nodes[i].txns[o].new == s.nodes[i].txns[o].loaded,
        s2.nodes.contains_key(i),
        ({ let p = s.nodes[i].txns[o].then.unwrap();
            &&& s2.nodes[i].txns.contains_key(p.target)
            &&& s2.nodes[i].txns[p.target] == continued(s, s2.nodes[i].core, p, s.nodes[i].txns[o].t)
            &&& s2.nodes[i].core.armed.contains_key(p.target) ==> s.nodes[i].core.armed.contains_key(p.target) && s2.nodes[i].core.armed[p.target] == s.nodes[i].core.armed[p.target]
        }),
        s2.hist == s.hist,
        s2.store.docs == s.store.docs,
        s2.store.etags == s.store.etags,
        s2.store.stamps == s.store.stamps,
    ensures
        inv_txn(s2, i, s.nodes[i].txns[o].then.unwrap().target),
{
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let p = x.then.unwrap();
    let st = p.target;
    assert(inv_txn(s, i, o));
    assert(inv_pending(s, o, x, p));
    let core2 = s2.nodes[i].core;
    let y = s2.nodes[i].txns[st];
    let c = y.c;
    assert(y == continued(s, core2, p, x.t));
    assert(c == spec_prepare(core2, st, p.cur, p.deadline, p.new != p.loaded, Some(p.fired)));
    assert(c.changed);
    if p.cur is Some {
        assert(s.hist.versions.contains_key(p.cur.unwrap()));
        assert(s.hist.order[Event::Born(p.cur.unwrap())] < s.hist.counter);
    }
    assert(s.hist.order[Event::Armed(p.fired)] < s.hist.counter);
    if c.previous is Some {
        assert(core2.armed.contains_key(st) && core2.armed[st].key == c.previous.unwrap() && Some(core2.armed[st].etag) == p.cur);
        assert(inv_armed(s, i, st));
        assert(s.hist.order[Event::Armed(c.previous.unwrap())] < s.hist.counter);
        if live(s2, st, y) {
            assert(s.store.etag(st) == Some(n.core.armed[st].etag));
        }
    }
    if live(s2, st, y) {
        if p.cur is Some {
            assert(s.store.etags.contains_key(st));
            assert(s.store.docs[st] == s.hist.versions[s.store.etags[st]]);
            assert(s2.store.doc(st) == p.loaded);
        } else {
            assert(!s.store.etags.contains_key(st));
            assert(!s.store.docs.contains_key(st));
            assert(s2.store.doc(st) == p.loaded);
        }
        assert(s2.store.stamp(st) <= y.t);
    }
    // the occurrence's promise is in the origin's document, so the row's run has it
    assert(s.store.docs.contains_key(o) && s.store.docs[o].objects.contains_key(p.pid));
    assert forall |q: Seq<char>| #[trigger] y.new.schedules.contains_key(q) && y.new.schedules[q].last_run_at is Some
        implies has_promise(s2, y.new.schedules[q], q, y.new.schedules[q].last_run_at.unwrap() as nat) by {
        let t = y.new.schedules[q].last_run_at.unwrap() as nat;
        if expand(y.new.schedules[q].promise_id, q, t) == p.pid {
            assert(origin(p.pid) == o);
        } else {
            assert(has_promise(s, p.new.schedules[q], q, t));
        }
    }
    assert(y.loaded.objects.dom() <= y.new.objects.dom());
    assert(inv_txn(s2, i, st));
}

proof fn lemma_finish_txns(s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv()(s), finish(s, i, o, deleted) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) ==> inv_txn(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_txn(s, i, o));
    let kept = spec_keep(c);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(s2, j, q) by {
      if j == i && x.then is Some && q == x.then.unwrap().target {
        lemma_continued(s, s2, i, o);
      } else {
        assert(inv_txn(s, j, q));
        let y = s.nodes[j].txns[q];
        if deleted && y.c.armed_now is Some && live(s, q, y) && !(y.phase is Written) {
            let k = y.c.armed_now.unwrap();
            let f = c.fired.unwrap();
            if k == f {
                assert(k.origin == q);
                assert(q == o);
                if j == i { assert(y == x); assert(false); }
                // y loaded the bucket's version, which is this commit's or later; its key was armed after
                assert(y.letag == y.cur && y.cur == s.store.etag(o));
                assert(y.lseq == s.hist.order[Event::Born(s.store.etags[o])]);
                assert(s.hist.order[Event::Born(s.store.etags[o])] >= s.hist.order[Event::Born(x.cur.unwrap())]);
                assert(s.hist.order[Event::Born(x.cur.unwrap())] >= x.seq0);
                assert(s.hist.order[Event::Armed(f)] < x.seq0);
                assert(s.hist.order[Event::Armed(k)] >= y.seq0);
                assert(y.seq0 >= y.lseq);
                assert(false);
            }
        }
      }
    }
}

proof fn lemma_finish_store(s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv()(s), finish(s, i, o, deleted) == Some(s2),
    ensures inv_store(s2), inv_timer(s2),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_txn(s, i, o));
    let kept = spec_keep(c);
    assert(inv_store(s2)) by {
        assert(s2.store.docs == s.store.docs && s2.hist.versions == s.hist.versions && s2.hist.armer == s.hist.armer && s2.hist.counter == s.hist.counter);
        assert forall |k: AKey| #[trigger] s2.store.timers.contains(k) implies s.hist.armer.contains_key(k) by {
            assert(s.store.timers.contains(k));
        }
    }
    assert(inv_timer(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) && has_any(s2.store.docs[q]) implies {
            &&& s2.hist.keeper.contains_key(q)
            &&& s2.store.timers.contains(s2.hist.keeper[q])
            &&& s2.hist.keeper[q].origin == q
            &&& is_next(s2.store.docs[q], s2.hist.keeper[q].at)
        } by {
            assert(s.store.docs.contains_key(q) && has_any(s.store.docs[q]));
            if deleted {
                let f = c.fired.unwrap();
                let kp = s.hist.keeper[q];
                if q == o {
                    if kept_covers(s, o, x) {
                        if c.deadline is None {
                            assert(!has_any(s.store.docs[o]));
                            assert(false);
                        } else {
                            assert(kp == kept.unwrap());
                            if c.rearm {
                                assert(kp == c.armed_now.unwrap());
                                assert(Some(kp) != c.fired);
                            } else {
                                assert(kp == c.previous.unwrap());
                                assert(Some(kp) != c.fired);
                            }
                            assert(kp != f);
                        }
                    } else {
                        assert(!live(s, o, x));
                        assert(Some(kp) != c.fired);
                        assert(kp != f);
                    }
                } else {
                    assert(kp.origin == q);
                    assert(kp != f);
                }
            }
        }
    }
}

proof fn lemma_finish(s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv()(s), finish(s, i, o, deleted) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    lemma_finish_cache(s, s2, i, o, deleted);
    lemma_finish_armed(s, s2, i, o, deleted);
    lemma_finish_txns(s, s2, i, o, deleted);
    lemma_finish_store(s, s2, i, o, deleted);
    assemble(s2);
}

proof fn lemma_collect_cache(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), collect(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) ==> inv_cache(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(s2, j, q) by {
        if j == i && q == o {
        } else {
            assert(inv_cache(s, j, q));
        }
    }
}

proof fn lemma_collect_armed(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), collect(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) ==> inv_armed(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) implies inv_armed(s2, j, q) by {
        assert(inv_armed(s, j, q));
        if j == i && q == o {
            assert(s2.nodes[i].core.armed[o] == n.core.armed[o]);
        }
    }
}

proof fn lemma_collect_txns(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), collect(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) ==> inv_txn(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(s2, j, q) by {
        assert(inv_txn(s, j, q));
        let y = s.nodes[j].txns[q];
        assert(!(j == i && q == o));
        if q == o {
            assert(!live(s2, o, y));
            if y.phase is Written {
                // the document and its keeper are as they were
            }
        }
        if y.c.armed_now is Some {
            let kk = y.c.armed_now.unwrap();
            if kk == k && live(s2, q, y) && !(y.phase is Written) {
                assert(q == o);
                assert(false);
            }
        }
    }
}

proof fn lemma_collect_store(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), collect(s, i, o, e) == Some(s2),
    ensures inv_store(s2), inv_timer(s2),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert(inv_store(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) implies {
            &&& s2.store.etags.contains_key(q)
            &&& s2.store.stamps.contains_key(q)
            &&& s2.store.stamps[q] <= MAX_TIME
            &&& echod_kernel::properties::inv(s2.store.stamps[q], full(s2.store.docs[q]))
            &&& s2.hist.versions.contains_key(s2.store.etags[q])
            &&& s2.hist.versions[s2.store.etags[q]] == s2.store.docs[q]
        } by {
            if q != o {
                assert(s.store.docs.contains_key(q));
            }
        }
        assert forall |v: Seq<char>| #[trigger] s2.hist.versions.contains_key(v) implies s2.hist.order.contains_key(Event::Born(v)) && s2.hist.order[Event::Born(v)] < s2.hist.counter && s2.hist.writer.contains_key(v) by {
            if v != e { assert(s.hist.versions.contains_key(v)); }
        }
    }
    assert(inv_timer(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) && has_any(s2.store.docs[q]) implies {
            &&& s2.hist.keeper.contains_key(q)
            &&& s2.store.timers.contains(s2.hist.keeper[q])
            &&& s2.hist.keeper[q].origin == q
            &&& is_next(s2.store.docs[q], s2.hist.keeper[q].at)
        } by {
            if q == o {
                assert(s2.store.docs[o] == x.loaded);
                assert(s.store.docs.contains_key(o));
                assert(has_any(s.store.docs[o]));
                let kp = s.hist.keeper[o];
                assert(has_deadline(x.loaded, kp.at));
                assert(kp.at > x.t);
                assert(k.at <= x.t);
                assert(kp != k);
            } else {
                assert(s.store.docs.contains_key(q) && has_any(s.store.docs[q]));
                assert(s.hist.keeper[q].origin == q);
                assert(s.hist.keeper[q] != k);
            }
        }
    }
}

proof fn lemma_collect(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), collect(s, i, o, e) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    lemma_collect_cache(s, s2, i, o, e);
    lemma_collect_armed(s, s2, i, o, e);
    lemma_collect_txns(s, s2, i, o, e);
    lemma_collect_store(s, s2, i, o, e);
    assemble(s2);
}

proof fn lemma_collect_fail(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv()(s), collect_fail(s, i, o) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(s2, i, q) by { assert(inv_cache(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(s2, i, q) by { assert(inv_txn(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q].phase is Written
        implies s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q] == s.nodes[i].txns[q] by {}
    lemma_node_only(s, s2, i);
}

proof fn lemma_done(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv()(s), done(s, i, o) == Some(s2),
    ensures inv()(s2),
{
    disassemble(s);
    let x = s.nodes[i].txns[o];
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(s2, i, q) by { assert(inv_cache(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(s2, i, q) by {
        if x.then is Some && q == x.then.unwrap().target {
            assert(inv_txn(s, i, o));
            assert(x.new == x.loaded);
            lemma_continued(s, s2, i, o);
        } else {
            assert(inv_txn(s, i, q));
        }
    }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q].phase is Written
        implies s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q] == s.nodes[i].txns[q] by {}
    lemma_node_only(s, s2, i);
}

/// Giving up a commit keeps the invariant: what the node wrote stays, what
/// it remembers of the origin goes.
proof fn lemma_give_up(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv()(s), s.nodes.contains_key(i), s2 == give_up(s, i, o),
    ensures inv()(s2),
{
    disassemble(s);
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(s2, i, q) by { assert(inv_cache(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by {
        assert(inv_armed(s, i, q));
        let a = s2.nodes[i].core.armed[q];
        assert forall |j: Id| #[trigger] s2.nodes.contains_key(j) && j != i && s2.nodes[j].txns.contains_key(q) && s2.nodes[j].txns[q].phase is Written
            && s2.hist.order[Event::Born(a.etag)] >= s2.hist.order[Event::Born(s2.nodes[j].txns[q].cur.unwrap())]
            implies Some(a.key) != s2.nodes[j].txns[q].c.fired by {
            assert(s2.nodes[j] == s.nodes[j]);
        }
    }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(s2, i, q) by {
        assert(inv_txn(s, i, q));
        let x = s2.nodes[i].txns[q];
        if x.phase is Written {
            assert forall |j: Id| #[trigger] s2.nodes.contains_key(j) && j != i && s2.nodes[j].txns.contains_key(q) && s2.nodes[j].txns[q].phase is Written
                && s2.hist.order[Event::Born(s2.nodes[j].txns[q].cur.unwrap())] < s2.hist.order[Event::Born(x.cur.unwrap())]
                implies x.lseq >= s2.hist.order[Event::Born(s2.nodes[j].txns[q].cur.unwrap())] by {
                assert(s2.nodes[j] == s.nodes[j]);
            }
        }
    }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q].phase is Written
        implies s.nodes.contains_key(i) && s.nodes[i].txns.contains_key(q) && s2.nodes[i].txns[q] == s.nodes[i].txns[q] by {}
    lemma_node_only(s, s2, i);
}

proof fn lemma_arm_unknown(s: Cluster, s2: Cluster, i: Id, o: Origin, k: AKey, landed: bool)
    requires inv()(s), arm_unknown(s, i, o, k, landed) == Some(s2),
    ensures inv()(s2),
{
    if landed {
        let s1 = arm(s, i, o, k).unwrap();
        lemma_arm(s, s1, i, o, k);
        lemma_give_up(s1, s2, i, o);
    } else {
        lemma_give_up(s, s2, i, o);
    }
}

proof fn lemma_commit_unknown(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>, landed: bool)
    requires inv()(s), commit_unknown(s, i, o, e, landed) == Some(s2),
    ensures inv()(s2),
{
    if landed {
        let s1 = commit(s, i, o, e).unwrap();
        lemma_commit(s, s1, i, o, e);
        lemma_give_up(s1, s2, i, o);
    } else {
        lemma_give_up(s, s2, i, o);
    }
}

proof fn lemma_cu_cache(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), collect_unknown(s, i, o, e, true) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) ==> inv_cache(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(s2, j, q) by {
        assert(!(j == i && q == o));
        assert(inv_cache(s, j, q));
    }
}

proof fn lemma_cu_armed(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), collect_unknown(s, i, o, e, true) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) ==> inv_armed(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) implies inv_armed(s2, j, q) by {
        assert(inv_armed(s, j, q));
    }
}

proof fn lemma_cu_txns(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), collect_unknown(s, i, o, e, true) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) ==> inv_txn(s2, j, q),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(s2, j, q) by {
        assert(inv_txn(s, j, q));
        let y = s.nodes[j].txns[q];
        assert(!(j == i && q == o));
        if q == o {
            assert(!live(s2, o, y));
        }
    }
}

proof fn lemma_cu_store(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv()(s), collect_unknown(s, i, o, e, true) == Some(s2),
    ensures inv_store(s2), inv_timer(s2),
{
    disassemble(s);
    disassemble(s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_txn(s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert(inv_store(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) implies {
            &&& s2.store.etags.contains_key(q)
            &&& s2.store.stamps.contains_key(q)
            &&& s2.store.stamps[q] <= MAX_TIME
            &&& echod_kernel::properties::inv(s2.store.stamps[q], full(s2.store.docs[q]))
            &&& s2.hist.versions.contains_key(s2.store.etags[q])
            &&& s2.hist.versions[s2.store.etags[q]] == s2.store.docs[q]
        } by {
            if q != o {
                assert(s.store.docs.contains_key(q));
            }
        }
        assert forall |v: Seq<char>| #[trigger] s2.hist.versions.contains_key(v) implies s2.hist.order.contains_key(Event::Born(v)) && s2.hist.order[Event::Born(v)] < s2.hist.counter && s2.hist.writer.contains_key(v) by {
            if v != e { assert(s.hist.versions.contains_key(v)); }
        }
    }
    assert(inv_timer(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) && has_any(s2.store.docs[q]) implies {
            &&& s2.hist.keeper.contains_key(q)
            &&& s2.store.timers.contains(s2.hist.keeper[q])
            &&& s2.hist.keeper[q].origin == q
            &&& is_next(s2.store.docs[q], s2.hist.keeper[q].at)
        } by {
            if q == o {
                assert(s2.store.docs[o] == x.loaded);
                assert(s.store.docs.contains_key(o));
                assert(has_any(s.store.docs[o]));
            } else {
                assert(s.store.docs.contains_key(q) && has_any(s.store.docs[q]));
            }
        }
    }
}

/// The rewrite landed, and the node gave up: the same document at a new
/// version, this node's cache of it gone, its commit gone. The same shape
/// as `collect` without the key's deletion.
proof fn lemma_collect_unknown(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>, landed: bool)
    requires inv()(s), collect_unknown(s, i, o, e, landed) == Some(s2),
    ensures inv()(s2),
{
    if !landed {
        lemma_give_up(s, s2, i, o);
        return;
    }
    disassemble(s);
    lemma_cu_cache(s, s2, i, o, e);
    lemma_cu_armed(s, s2, i, o, e);
    lemma_cu_txns(s, s2, i, o, e);
    lemma_cu_store(s, s2, i, o, e);
    assert(live(s, o, s.nodes[i].txns[o]));
    assemble(s2);
}

/// The key's put, by outcome.
proof fn lemma_add_timer(s: Cluster, s2: Cluster, i: Id, o: Origin, k: AKey, out: Outcome)
    requires inv()(s), add_timer(s, i, o, k, out) == Some(s2),
    ensures inv()(s2),
{
    match out {
        Outcome::Applied => lemma_arm(s, s2, i, o, k),
        Outcome::Refused => assert(false),
        Outcome::Unknown(landed) => lemma_arm_unknown(s, s2, i, o, k, landed),
    }
}

/// The document's put, by outcome: a changed document commits, an
/// unchanged one collects.
proof fn lemma_write_doc(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>, out: Outcome)
    requires inv()(s), write_doc(s, i, o, e, out) == Some(s2),
    ensures inv()(s2),
{
    let n = s.nodes[i];
    if s.nodes.contains_key(i) && n.txns.contains_key(o) && n.txns[o].c.changed {
        match out {
            Outcome::Applied => lemma_commit(s, s2, i, o, e),
            Outcome::Refused => lemma_commit_fail(s, s2, i, o),
            Outcome::Unknown(landed) => lemma_commit_unknown(s, s2, i, o, e, landed),
        }
    } else {
        match out {
            Outcome::Applied => lemma_collect(s, s2, i, o, e),
            Outcome::Refused => lemma_collect_fail(s, s2, i, o),
            Outcome::Unknown(landed) => lemma_collect_unknown(s, s2, i, o, e, landed),
        }
    }
}

/// The two deletes after the write, in sequence: each keeps the invariant
/// on its own, so their composition does.
proof fn lemma_del_timer(s: Cluster, s2: Cluster, i: Id, o: Origin, prev: bool, fired: bool)
    requires inv()(s), del_timer(s, i, o, prev, fired) == Some(s2),
    ensures inv()(s2),
{
    let s1 = if prev { disarm(s, i, o).unwrap() } else { s };
    if prev {
        lemma_disarm(s, s1, i, o);
    }
    lemma_finish(s1, s2, i, o, fired);
}

pub proof fn lemma_next(s: Cluster, s2: Cluster)
    requires inv()(s), next()(s, s2),
    ensures inv()(s2),
{
    let st = choose |st: Step| #[trigger] next_step(s, s2, st);
    match st {
        Step::Tick(i, d) => lemma_tick(s, s2, i, d),
        Step::Join(i, c) => lemma_join(s, s2, i, c),
        Step::Crash(i) => lemma_crash(s, s2, i),
        Step::Forget(i, o) => lemma_forget(s, s2, i, o),
        Step::Prepare(i, o, t, work, new, did, deadline) => lemma_prepare(s, s2, i, o, t, work, new, did, deadline),
        Step::AddTimer(i, o, k, out) => lemma_add_timer(s, s2, i, o, k, out),
        Step::Write(i, o, e, out) => lemma_write_doc(s, s2, i, o, e, out),
        Step::DelTimer(i, o, prev, fired) => lemma_del_timer(s, s2, i, o, prev, fired),
        Step::Done(i, o) => lemma_done(s, s2, i, o),
    }
}

// ---------------------------------------------------------------------------
// The theorem, in the temporal logic
// ---------------------------------------------------------------------------

/// Every execution that starts in `init` and steps by `next` satisfies the
/// invariant forever — and with it exclusion, currency, the catalogue on
/// every document, and a timer for every deadline.
pub proof fn safety(spec: TempPred<Cluster>)
    requires
        spec.entails(lift_state(init())),
        spec.entails(always(lift_action(next()))),
    ensures
        spec.entails(always(lift_state(inv()))),
{
    assert forall |s: Cluster| #[trigger] init()(s) implies inv()(s) by { lemma_init(s); }
    assert forall |s: Cluster, s2: Cluster| inv()(s) && #[trigger] next()(s, s2) implies inv()(s2) by { lemma_next(s, s2); }
    init_invariant::<Cluster>(spec, init(), next(), inv());
}

} // verus!

verus! {

/// The invariant is not vacuous: a cluster with a node, a document, and
/// the node's cache entry for it satisfies it.
pub proof fn not_vacuous(o: Origin)
    ensures exists |s: Cluster| #[trigger] inv()(s) && s.nodes.contains_key(seq!['n']) && s.store.docs.contains_key(o),
{
    let me: Id = seq!['n'];
    let e: Seq<char> = seq!['v'];
    let empty: Doc = empty_doc();
    let core = ANode {
        id: me, ttl: 0, read_any: false, epoch: 0, members: Seq::empty(),
        last_read: 0,
        cache: Map::empty().insert(o, AEntry { etag: e, filled_at: 0 }),
        armed: Map::empty(),
    };
    let n = Node { core, bodies: Map::empty().insert(o, empty), alive: true, clock: 0, txns: Map::empty() };
    let s = Cluster {
        nodes: Map::empty().insert(me, n),
        store: Store {
            docs: Map::empty().insert(o, empty),
            etags: Map::empty().insert(o, e),
            stamps: Map::empty().insert(o, 0),
            timers: Set::empty(),
        },
        hist: History {
            versions: Map::empty().insert(e, empty),
            writer: Map::empty().insert(e, me),
            armer: Map::empty(),
            keeper: Map::empty(),
            counter: 1,
            order: Map::empty().insert(Event::Born(e), 0),
        },
        log: Seq::empty(),
    };
    lemma_inv_empty(0);
    assert(shaped(o, empty));
    assert(inv_store(s));
    assert(inv_timer(s)) by {
        assert forall |q: Origin| #[trigger] s.store.docs.contains_key(q) && has_any(s.store.docs[q]) implies false by {
            let t = choose |t: nat| has_deadline(empty, t);
            if objects_deadline(empty.objects, t) {
                let id = choose |id: Seq<char>| #[trigger] empty.objects.contains_key(id) && deadline_at(empty.objects[id], t);
            } else {
                let id = choose |id: Seq<char>| #[trigger] empty.schedules.contains_key(id) && empty.schedules[id].next_run_at as nat == t;
            }
        }
    }
    assert forall |i: Id, q: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.cache.contains_key(q) implies inv_cache(s, i, q) by {}
    assert forall |i: Id, q: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.armed.contains_key(q) implies inv_armed(s, i, q) by {}
    assert forall |i: Id, q: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(q) implies inv_txn(s, i, q) by {}
    assemble(s);
    assert(s.store.docs.contains_key(o));
}

} // verus!
