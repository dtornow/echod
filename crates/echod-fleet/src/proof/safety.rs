//! The invariant, and the induction that keeps it.
//!
//! Four theorems come out of it:
//!
//! - **Exclusion.** Two live nodes never both act as owner of one origin.
//! - **Currency.** A node that answers an origin from its cache holds the
//!   bucket's current version of it.
//! - **Catalogue.** Every document in the bucket satisfies the kernel's
//!   catalogue at the instant it was written.
//! - **Timers.** Every deadline in every document has a deadline key in the
//!   bucket at or before it — at all times, through every commit, crash,
//!   collection and change of ownership.
//!
//! The first two rest on the hypothesis that every live clock is within
//! `skew` of real time and on `grace > ttl + 4 skew`. The last two rest on
//! the commit protocol alone: the key before the document, the document
//! conditionally on the version loaded, a remembered key relied on only for
//! the version it was written with, a fired key deleted only by the node
//! that armed it or after a conditional rewrite that found nothing due.

use vstd::prelude::*;

use crate::node::core::*;
use crate::node::step::*;
use crate::node::txn::*;
use crate::spec::cluster::*;
use crate::tla::defs::*;
use crate::tla::rules::*;
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
        Some(k) => s.store.keeper.contains_key(o) && s.store.keeper[o] == k,
        None => true,
    }
}

/// What holds of one node.
pub open spec fn inv_node(p: Params, s: Cluster, i: Id) -> bool {
    let n = s.nodes[i];
    let c = n.core;
    &&& c.id == i
    &&& c.ttl == p.ttl
    &&& c.grace == p.grace
    &&& c.epoch <= s.store.config.epoch
    &&& n.alive ==> clock_ok(p, s.now, n.clock)
    &&& c.read_any ==> {
        &&& c.last_read <= n.clock
        &&& c.held <= c.last_read
        &&& n.last_read_real <= s.now
        &&& n.held_real <= n.last_read_real
        &&& c.last_read <= n.last_read_real + p.skew
        &&& c.held + p.skew >= n.held_real
        // the epoch it holds was written before it first read it
        &&& n.held_real >= s.store.written[c.epoch]
        // an epoch it does not hold yet was written after its last read
        &&& c.epoch < s.store.config.epoch ==> n.last_read_real <= s.store.written[c.epoch + 1]
        // the members it holds are the epoch's
        &&& c.members == s.store.configs[c.epoch]
    }
}

/// A cache entry names a version that exists, which the body cache holds,
/// filled no later than the clock; a version this node wrote while acting
/// was written no earlier than the grace after it first read its epoch.
pub open spec fn inv_cache(p: Params, s: Cluster, i: Id, o: Origin) -> bool {
    let n = s.nodes[i];
    let e = n.core.cache[o];
    &&& e.filled_at <= n.clock
    &&& s.store.docs.contains_key(o)
    &&& n.bodies.contains_key(o)
    &&& s.store.versions.contains_key(e.etag)
    &&& n.bodies[o] == s.store.versions[e.etag]
    &&& e.wrote && e.filled_at >= n.core.held + p.grace ==> s.store.born.contains_key(e.etag) && s.store.born[e.etag] + 2 * p.skew >= n.held_real + p.grace
}

/// A remembered key: this node's, for this origin; and while the document
/// is still the version it was written with, it is the document's cover.
pub open spec fn inv_armed(s: Cluster, i: Id, o: Origin) -> bool {
    let a = s.nodes[i].core.armed[o];
    &&& a.key.origin == o
    &&& s.store.armer.contains_key(a.key) && s.store.armer[a.key] == i
    &&& s.store.versions.contains_key(a.etag)
    &&& s.store.etag(o) == Some(a.etag) ==> s.store.docs.contains_key(o) && s.store.keeper.contains_key(o) && s.store.keeper[o] == a.key && has_any(s.store.docs[o])
}

/// A commit in flight. The node acted as owner of `o` when it began: it
/// held its epoch for the grace, and its view was fresh; the version it
/// loaded was written before.
pub open spec fn inv_txn(p: Params, s: Cluster, i: Id, o: Origin) -> bool {
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    &&& c.origin == o
    &&& n.core.read_any
    &&& x.begun <= s.now
    &&& x.lr <= x.begun
    &&& x.epoch <= s.store.config.epoch
    &&& x.held_real + p.grace <= x.begun + 2 * p.skew
    &&& s.store.written[x.epoch] <= x.held_real
    &&& x.epoch < s.store.config.epoch ==> x.lr <= s.store.written[x.epoch + 1]
    &&& x.begun <= x.lr + p.ttl + 2 * p.skew
    &&& owner(s.store.configs[x.epoch], o) == Some(i)
    &&& x.cur is Some ==> s.store.born.contains_key(x.cur.unwrap()) && (x.phase is Written || s.store.born[x.cur.unwrap()] <= x.begun)
    &&& x.t <= MAX_TIME
    &&& echod_kernel::properties::inv(x.t, full(x.loaded))
    &&& echod_kernel::properties::inv(x.t, full(x.new))
    &&& next_is(x.new, c.deadline)
    &&& c.fired is Some ==> c.fired.unwrap().origin == o && c.fired.unwrap().at <= x.t && s.store.armer.contains_key(c.fired.unwrap())
    &&& !c.changed ==> x.new == x.loaded && (c.fired is Some ==> no_due(x.t, x.loaded))
    &&& c.rearm == (c.changed && c.deadline is Some && (c.previous is None || c.previous.unwrap().at != c.deadline.unwrap()))
    &&& c.previous is Some ==> {
        let q = c.previous.unwrap();
        &&& q.origin == o
        &&& s.store.armer.contains_key(q) && s.store.armer[q] == i
        &&& Some(q) != c.fired
        &&& !(x.phase is Written) && live(s, o, x) ==> s.store.docs.contains_key(o) && s.store.keeper.contains_key(o) && s.store.keeper[o] == q && has_any(s.store.docs[o])
    }
    &&& x.phase is Decided ==> c.armed_now is None
    &&& x.phase is Armed ==> c.rearm && c.armed_now is Some
    &&& c.armed_now is Some ==> {
        let k = c.armed_now.unwrap();
        &&& k.origin == o
        &&& Some(k.at) == c.deadline
        &&& s.store.armer.contains_key(k) && s.store.armer[k] == i
        &&& Some(k) != c.previous
        &&& Some(k) != c.fired
        &&& !(x.phase is Written) && live(s, o, x) ==> s.store.timers.contains(k)
    }
    &&& x.cur is Some ==> s.store.versions.contains_key(x.cur.unwrap())
    &&& !(x.phase is Written) ==> (live(s, o, x) ==> s.store.doc(o) == x.loaded && s.store.stamp(o) <= x.t)
    &&& x.phase is Written ==> {
        &&& c.changed
        &&& x.cur is Some
        &&& c.rearm ==> c.armed_now is Some
        &&& live(s, o, x) ==> kept_covers(s, o, x) && s.store.stamps.contains_key(o) && s.store.stamps[o] == x.t
        &&& kept_covers(s, o, x) || (!live(s, o, x) && (s.store.keeper.contains_key(o) ==> s.store.armer.contains_key(s.store.keeper[o]) && s.store.armer[s.store.keeper[o]] != i))
    }
}

/// The epochs: each one's members and write time, in order, none in the future.
pub open spec fn inv_written(s: Cluster) -> bool {
    &&& forall |e: nat| e <= s.store.config.epoch ==> #[trigger] s.store.written.contains_key(e) && s.store.configs.contains_key(e)
    &&& forall |e: nat, e2: nat| e <= e2 && e2 <= s.store.config.epoch ==> #[trigger] s.store.written[e] <= #[trigger] s.store.written[e2]
    &&& s.store.written[s.store.config.epoch] <= s.now
    &&& s.store.configs[s.store.config.epoch] == s.store.config.members
}

/// Every document satisfies the catalogue at its stamp, and is the content
/// of its version.
pub open spec fn inv_store(s: Cluster) -> bool {
    &&& forall |o: Origin| #[trigger] s.store.docs.contains_key(o) ==> {
        &&& s.store.etags.contains_key(o)
        &&& s.store.stamps.contains_key(o)
        &&& s.store.stamps[o] <= MAX_TIME
        &&& echod_kernel::properties::inv(s.store.stamps[o], full(s.store.docs[o]))
        &&& s.store.versions.contains_key(s.store.etags[o])
        &&& s.store.versions[s.store.etags[o]] == s.store.docs[o]
    }
    &&& forall |o: Origin| #[trigger] s.store.etags.contains_key(o) ==> s.store.docs.contains_key(o)
    &&& forall |k: AKey| #[trigger] s.store.timers.contains(k) ==> s.store.armer.contains_key(k)
    &&& forall |e: Seq<char>| #[trigger] s.store.versions.contains_key(e) ==> s.store.born.contains_key(e) && s.store.born[e] <= s.now
}

/// Every document with a deadline is covered: its keeper is in the bucket,
/// for it, at its nearest deadline.
pub open spec fn inv_timer(s: Cluster) -> bool {
    forall |o: Origin| #[trigger] s.store.docs.contains_key(o) && has_any(s.store.docs[o]) ==> {
        &&& s.store.keeper.contains_key(o)
        &&& s.store.timers.contains(s.store.keeper[o])
        &&& s.store.keeper[o].origin == o
        &&& is_next(s.store.docs[o], s.store.keeper[o].at)
    }
}

/// A version this node wrote while acting as owner of `o`, in the bucket's
/// own epoch or while its view is fresh, is the bucket's version: no write
/// by anyone else has landed since. The node trusts exactly such entries.
pub open spec fn inv_entry(p: Params, s: Cluster, i: Id, o: Origin) -> bool {
    let n = s.nodes[i];
    let c = n.core;
    n.alive && c.read_any && (c.epoch == s.store.config.epoch || fresh(n)) && owner(c.members, o) == Some(i)
        && c.cache.contains_key(o) && c.cache[o].wrote && c.cache[o].filled_at >= c.held + p.grace
        ==> Some(c.cache[o].etag) == s.store.etag(o)
}

pub open spec fn inv(p: Params) -> spec_fn(Cluster) -> bool {
    |s: Cluster| {
        &&& p.wf()
        &&& inv_written(s)
        &&& inv_store(s)
        &&& inv_timer(s)
        &&& forall |i: Id| #[trigger] s.nodes.contains_key(i) ==> inv_node(p, s, i)
        &&& forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.cache.contains_key(o) ==> inv_cache(p, s, i, o)
        &&& forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.armed.contains_key(o) ==> inv_armed(s, i, o)
        &&& forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(o) ==> inv_txn(p, s, i, o)
        &&& forall |i: Id, o: Origin| #[trigger] s.nodes.contains_key(i) ==> #[trigger] inv_entry(p, s, i, o)
    }
}

/// The invariant from its conjuncts, stated so each lemma proves them apart.
pub proof fn assemble(p: Params, s: Cluster)
    requires
        p.wf(),
        inv_written(s),
        inv_store(s),
        inv_timer(s),
        forall |i: Id| #[trigger] s.nodes.contains_key(i) ==> inv_node(p, s, i),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.cache.contains_key(o) ==> inv_cache(p, s, i, o),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.armed.contains_key(o) ==> inv_armed(s, i, o),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(o) ==> inv_txn(p, s, i, o),
        forall |i: Id, o: Origin| #[trigger] s.nodes.contains_key(i) ==> #[trigger] inv_entry(p, s, i, o),
    ensures
        inv(p)(s),
{
}

/// The invariant's conjuncts from the invariant.
pub proof fn disassemble(p: Params, s: Cluster)
    requires inv(p)(s),
    ensures
        p.wf(),
        inv_written(s),
        inv_store(s),
        inv_timer(s),
        forall |i: Id| #[trigger] s.nodes.contains_key(i) ==> inv_node(p, s, i),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.cache.contains_key(o) ==> inv_cache(p, s, i, o),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.armed.contains_key(o) ==> inv_armed(s, i, o),
        forall |i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(o) ==> inv_txn(p, s, i, o),
        forall |i: Id, o: Origin| #[trigger] s.nodes.contains_key(i) ==> #[trigger] inv_entry(p, s, i, o),
{
}

// ---------------------------------------------------------------------------
// The theorems, from the invariant
// ---------------------------------------------------------------------------

/// Two live nodes never both act as owner of one origin.
pub proof fn exclusion(p: Params, s: Cluster, i: Id, j: Id, o: Origin)
    requires
        inv(p)(s),
        s.nodes.contains_key(i),
        s.nodes.contains_key(j),
        acts(s.nodes[i], o),
        acts(s.nodes[j], o),
    ensures
        i == j,
{
    let n = s.nodes[i];
    let m = s.nodes[j];
    assert(inv_node(p, s, i));
    assert(inv_node(p, s, j));
    if n.core.epoch == m.core.epoch {
        assert(n.core.members == s.store.configs[n.core.epoch]);
        assert(m.core.members == s.store.configs[m.core.epoch]);
    } else if n.core.epoch < m.core.epoch {
        timing(p, s, i, j);
    } else {
        timing(p, s, j, i);
    }
}

/// A node in an older epoch cannot be fresh while a node in a newer epoch
/// has held its epoch for the grace.
proof fn timing(p: Params, s: Cluster, i: Id, j: Id)
    requires
        inv(p)(s),
        s.nodes.contains_key(i),
        s.nodes.contains_key(j),
        s.nodes[i].alive, s.nodes[j].alive,
        s.nodes[i].core.read_any, s.nodes[j].core.read_any,
        s.nodes[i].core.epoch < s.nodes[j].core.epoch,
        fresh(s.nodes[i]),
        s.nodes[j].core.held + p.grace <= s.nodes[j].clock,
    ensures
        false,
{
    let n = s.nodes[i];
    let m = s.nodes[j];
    assert(inv_node(p, s, i));
    assert(inv_node(p, s, j));
    assert(s.store.written[n.core.epoch + 1] <= s.store.written[m.core.epoch]);
    assert(n.last_read_real <= m.held_real);
    assert(s.now <= n.clock + p.skew);
    assert(n.clock <= n.core.last_read + p.ttl);
    assert(s.now <= n.last_read_real + p.ttl + 2 * p.skew);
    assert(m.clock <= s.now + p.skew);
    assert(m.held_real + p.grace <= s.now + 2 * p.skew);
    assert(p.grace <= p.ttl + 4 * p.skew);
}

/// A node that answers from its cache holds the bucket's current version.
pub proof fn currency(p: Params, s: Cluster, i: Id, o: Origin)
    requires
        inv(p)(s),
        s.nodes.contains_key(i),
        trusts(s.nodes[i], o),
    ensures
        Some(s.nodes[i].core.cache[o].etag) == s.store.etag(o),
        s.store.docs.contains_key(o),
        s.nodes[i].bodies.contains_key(o),
        s.nodes[i].bodies[o] == s.store.docs[o],
{
    assert(inv_node(p, s, i));
    assert(inv_entry(p, s, i, o));
    assert(inv_cache(p, s, i, o));
}

/// Every document in the bucket satisfies the kernel's catalogue at the
/// instant it was written.
pub proof fn catalogue(p: Params, s: Cluster, o: Origin)
    requires
        inv(p)(s),
        s.store.docs.contains_key(o),
    ensures
        echod_kernel::properties::inv(s.store.stamps[o], full(s.store.docs[o])),
{
}

/// Every deadline in every document has a deadline key in the bucket for
/// its origin, at or before it.
pub proof fn timers_cover(p: Params, s: Cluster, o: Origin, t: nat)
    requires
        inv(p)(s),
        s.store.docs.contains_key(o),
        has_deadline(s.store.docs[o], t),
    ensures
        exists |k: AKey| #[trigger] s.store.timers.contains(k) && k.origin == o && k.at <= t,
{
    let k = s.store.keeper[o];
    assert(s.store.timers.contains(k) && k.origin == o && k.at <= t);
}

/// In particular: every pending promise that is not internal has a timer
/// at or before its deadline, every acquired task at or before its lease,
/// every pending task at or before its retry.
pub proof fn promises_have_timers(p: Params, s: Cluster, o: Origin, id: Seq<char>)
    requires
        inv(p)(s),
        s.store.docs.contains_key(o),
        s.store.docs[o].contains_key(id),
    ensures
        ({ let q = s.store.docs[o][id];
            q.state == echod_kernel::types::PromiseState::Pending && q.otype() != echod_kernel::tags::OType::Internal
                ==> exists |k: AKey| #[trigger] s.store.timers.contains(k) && k.origin == o && k.at <= q.timeout_at }),
        ({ let q = s.store.docs[o][id];
            lease_deadline(q) is Some ==> exists |k: AKey| #[trigger] s.store.timers.contains(k) && k.origin == o && k.at <= lease_deadline(q).unwrap() }),
        ({ let q = s.store.docs[o][id];
            retry_deadline(q) is Some ==> exists |k: AKey| #[trigger] s.store.timers.contains(k) && k.origin == o && k.at <= retry_deadline(q).unwrap() }),
{
    let d = s.store.docs[o];
    let q = d[id];
    if q.state == echod_kernel::types::PromiseState::Pending && q.otype() != echod_kernel::tags::OType::Internal {
        assert(deadline_at(q, q.timeout_at));
        assert(has_deadline(d, q.timeout_at));
        timers_cover(p, s, o, q.timeout_at);
    }
    if lease_deadline(q) is Some {
        let t = lease_deadline(q).unwrap();
        assert(deadline_at(q, t));
        assert(has_deadline(d, t));
        timers_cover(p, s, o, t);
    }
    if retry_deadline(q) is Some {
        let t = retry_deadline(q).unwrap();
        assert(deadline_at(q, t));
        assert(has_deadline(d, t));
        timers_cover(p, s, o, t);
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// The catalogue holds of an empty document at any instant.
proof fn lemma_inv_empty(t: nat)
    ensures echod_kernel::properties::inv(t, full(Map::empty())),
{
    reveal(echod_kernel::properties::inv);
}

/// A document the kernel reached at `t` from one satisfying the catalogue
/// satisfies it.
proof fn lemma_kreach_inv(t: nat, a: Doc, b: Doc)
    requires kreach(t, a, b),
    ensures echod_kernel::properties::inv(t, full(b)),
{
    let (sa, sb) = choose |sa: echod_kernel::store::AState, sb: echod_kernel::store::AState|
        sa.objects == a && sb.objects == b && echod_kernel::properties::inv(t, sa) && #[trigger] reach(t, sa, sb);
    lemma_reach_inv(t, sa, sb);
    lemma_inv_full(t, sb);
}

/// The document a node loads is the bucket's: read from it, or trusted
/// from a cache the invariant keeps current.
proof fn lemma_loaded(p: Params, s: Cluster, i: Id, o: Origin)
    requires inv(p)(s), s.nodes.contains_key(i), s.nodes[i].alive,
    ensures
        (if trusts(s.nodes[i], o) { s.nodes[i].bodies[o] } else { s.store.doc(o) }) == s.store.doc(o),
{
    if trusts(s.nodes[i], o) {
        currency(p, s, i, o);
    }
}

// ---------------------------------------------------------------------------
// The induction
// ---------------------------------------------------------------------------

pub proof fn lemma_init(p: Params, s: Cluster)
    requires p.wf(), init_state(s),
    ensures inv(p)(s),
{
    assert(s.store.written.contains_key(0));
    assert(s.store.configs.contains_key(0));
    assert forall |e: nat| e <= s.store.config.epoch implies #[trigger] s.store.written.contains_key(e) && s.store.configs.contains_key(e) by {}
}

/// Node `i` keeps its part; the store and every other node are as they were.
proof fn lemma_node_only(p: Params, s: Cluster, s2: Cluster, i: Id)
    requires
        inv(p)(s),
        s2.store == s.store,
        s2.now == s.now,
        s2.nodes.contains_key(i),
        forall |k: Id| k != i ==> (s2.nodes.contains_key(k) <==> s.nodes.contains_key(k)) && (s.nodes.contains_key(k) ==> s2.nodes[k] == s.nodes[k]),
        inv_node(p, s2, i),
        forall |o: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(o) ==> inv_cache(p, s2, i, o),
        forall |o: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(o) ==> inv_armed(s2, i, o),
        forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) ==> inv_txn(p, s2, i, o),
        forall |o: Origin| #[trigger] inv_entry(p, s2, i, o),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert forall |k: Id| #[trigger] s2.nodes.contains_key(k) implies inv_node(p, s2, k) by {
        if k != i { assert(inv_node(p, s, k)); }
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].core.cache.contains_key(o) implies inv_cache(p, s2, k, o) by {
        if k != i { assert(inv_cache(p, s, k, o)); }
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].core.armed.contains_key(o) implies inv_armed(s2, k, o) by {
        if k != i { assert(inv_armed(s, k, o)); }
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].txns.contains_key(o) implies inv_txn(p, s2, k, o) by {
        if k != i { assert(inv_txn(p, s, k, o)); }
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry(p, s2, k, o) by {
        if k != i { assert(inv_entry(p, s, k, o)); }
    }
    assert(inv_written(s2));
    assert(inv_store(s2));
    assert(inv_timer(s2));
    assemble(p, s2);
}

proof fn lemma_advance(p: Params, s: Cluster, s2: Cluster, d: nat)
    requires inv(p)(s), advance(p, s, d) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert forall |i: Id| #[trigger] s2.nodes.contains_key(i) implies inv_node(p, s2, i) by {
        assert(inv_node(p, s, i));
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].core.cache.contains_key(o) implies inv_cache(p, s2, k, o) by {
        assert(inv_cache(p, s, k, o));
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].core.armed.contains_key(o) implies inv_armed(s2, k, o) by {
        assert(inv_armed(s, k, o));
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].txns.contains_key(o) implies inv_txn(p, s2, k, o) by {
        assert(inv_txn(p, s, k, o));
    }
    assert forall |i: Id, o: Origin| #[trigger] s2.nodes.contains_key(i) implies #[trigger] inv_entry(p, s2, i, o) by {
        assert(inv_entry(p, s, i, o));
    }
    assert(inv_written(s2));
    assert(inv_store(s2));
    assert(inv_timer(s2));
    assemble(p, s2);
}

proof fn lemma_tick(p: Params, s: Cluster, s2: Cluster, i: Id, d: nat)
    requires inv(p)(s), tick(p, s, i, d) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert(inv_node(p, s, i));
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(o) implies inv_cache(p, s2, i, o) by { assert(inv_cache(p, s, i, o)); }
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(o) implies inv_armed(s2, i, o) by { assert(inv_armed(s, i, o)); }
    assert forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) implies inv_txn(p, s2, i, o) by { assert(inv_txn(p, s, i, o)); }
    assert forall |o: Origin| #[trigger] inv_entry(p, s2, i, o) by { assert(inv_entry(p, s, i, o)); }
    lemma_node_only(p, s, s2, i);
}

proof fn lemma_join(p: Params, s: Cluster, s2: Cluster, i: Id, c: nat)
    requires inv(p)(s), join(p, s, i, c) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert(inv_node(p, s2, i));
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(o) implies inv_cache(p, s2, i, o) by {}
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(o) implies inv_armed(s2, i, o) by {}
    assert forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) implies inv_txn(p, s2, i, o) by {}
    assert forall |o: Origin| #[trigger] inv_entry(p, s2, i, o) by {}
    lemma_node_only(p, s, s2, i);
}

proof fn lemma_crash(p: Params, s: Cluster, s2: Cluster, i: Id)
    requires inv(p)(s), crash(s, i) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert(inv_node(p, s, i));
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(o) implies inv_cache(p, s2, i, o) by { assert(inv_cache(p, s, i, o)); }
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(o) implies inv_armed(s2, i, o) by { assert(inv_armed(s, i, o)); }
    assert forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) implies inv_txn(p, s2, i, o) by { assert(inv_txn(p, s, i, o)); }
    assert forall |o: Origin| #[trigger] inv_entry(p, s2, i, o) by { assert(inv_entry(p, s, i, o)); }
    lemma_node_only(p, s, s2, i);
}

proof fn lemma_read_config(p: Params, s: Cluster, s2: Cluster, i: Id)
    requires inv(p)(s), read_config(s, i) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    let n = s.nodes[i];
    let n2 = s2.nodes[i];
    assert(inv_node(p, s, i));
    assert(s.store.written.contains_key(s.store.config.epoch));
    assert(inv_node(p, s2, i));
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(o) implies inv_cache(p, s2, i, o) by {
        assert(inv_cache(p, s, i, o));
        if !(n.core.read_any && n.core.epoch == s.store.config.epoch) {
            // held is now the clock: no entry was filled after held + grace
            assert(n2.core.cache[o].filled_at <= n2.clock);
            assert(n2.core.held == n2.clock);
        }
    }
    assert forall |o: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(o) implies inv_armed(s2, i, o) by { assert(inv_armed(s, i, o)); }
    assert forall |o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) implies inv_txn(p, s2, i, o) by { assert(inv_txn(p, s, i, o)); }
    assert forall |o: Origin| #[trigger] inv_entry(p, s2, i, o) by {
        assert(inv_entry(p, s, i, o));
        if !(n.core.read_any && n.core.epoch == s.store.config.epoch) {
            if n2.core.cache.contains_key(o) {
                assert(inv_cache(p, s, i, o));
                assert(n2.core.cache[o].filled_at <= n2.clock);
                assert(n2.core.held == n2.clock);
            }
        }
    }
    lemma_node_only(p, s, s2, i);
}

proof fn lemma_propose(p: Params, s: Cluster, s2: Cluster, i: Id, m: Seq<Id>)
    requires inv(p)(s), propose(s, i, m) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    let e = s.store.config.epoch + 1;
    assert(inv_written(s2)) by {
        assert forall |a: nat| a <= s2.store.config.epoch implies #[trigger] s2.store.written.contains_key(a) && s2.store.configs.contains_key(a) by {}
        assert forall |a: nat, b: nat| a <= b && b <= s2.store.config.epoch implies #[trigger] s2.store.written[a] <= #[trigger] s2.store.written[b] by {
            if b == e {
                if a < e {
                    assert(s.store.written[a] <= s.store.written[s.store.config.epoch]);
                }
            }
        }
    }
    assert forall |k: Id| #[trigger] s2.nodes.contains_key(k) implies inv_node(p, s2, k) by {
        assert(inv_node(p, s, k));
        let n = s.nodes[k];
        if n.core.read_any {
            assert(s2.store.written[n.core.epoch] == s.store.written[n.core.epoch]);
            assert(s2.store.configs[n.core.epoch] == s.store.configs[n.core.epoch]);
            if n.core.epoch < s2.store.config.epoch {
                if n.core.epoch + 1 == e {
                    assert(s2.store.written[e] == s.now);
                } else {
                    assert(s2.store.written[n.core.epoch + 1] == s.store.written[n.core.epoch + 1]);
                }
            }
        }
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].core.cache.contains_key(o) implies inv_cache(p, s2, k, o) by {
        assert(inv_cache(p, s, k, o));
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].core.armed.contains_key(o) implies inv_armed(s2, k, o) by {
        assert(inv_armed(s, k, o));
    }
    assert forall |k: Id, o: Origin| s2.nodes.contains_key(k) && #[trigger] s2.nodes[k].txns.contains_key(o) implies inv_txn(p, s2, k, o) by {
        assert(inv_txn(p, s, k, o));
        let x = s.nodes[k].txns[o];
        assert(s2.store.written[x.epoch] == s.store.written[x.epoch]);
        assert(s2.store.configs[x.epoch] == s.store.configs[x.epoch]);
        if x.epoch < s2.store.config.epoch {
            if x.epoch + 1 == e {
                assert(s2.store.written[e] == s.now);
                assert(x.lr <= s.now);
            } else {
                assert(s2.store.written[x.epoch + 1] == s.store.written[x.epoch + 1]);
            }
        }
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry(p, s2, k, o) by {
        assert(inv_entry(p, s, k, o));
        assert(inv_node(p, s, k));
    }
    assert(inv_store(s2));
    assert(inv_timer(s2));
    assemble(p, s2);
}

proof fn lemma_forget(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv(p)(s), forget(s, i, o) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert(inv_node(p, s, i));
    assert(inv_node(p, s2, i));
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(p, s2, i, q) by { assert(inv_cache(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(p, s2, i, q) by { assert(inv_txn(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] inv_entry(p, s2, i, q) by { assert(inv_entry(p, s, i, q)); }
    lemma_node_only(p, s, s2, i);
}

// --- the commit protocol ---

proof fn lemma_begin(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, t: nat, new: Doc, fired: Option<AKey>, did: bool, deadline: Option<nat>)
    requires inv(p)(s), begin(s, i, o, t, new, fired, did, deadline) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    let n = s.nodes[i];
    let n2 = s2.nodes[i];
    let x = n2.txns[o];
    assert(inv_node(p, s, i));
    lemma_loaded(p, s, i, o);
    assert(x.loaded == s.store.doc(o));
    if s.store.docs.contains_key(o) {
        lemma_inv_at(s.store.stamps[o], t, full(s.store.docs[o]));
    } else {
        lemma_inv_empty(t);
    }
    assert(echod_kernel::properties::inv(t, full(x.loaded)));
    lemma_kreach_inv(t, x.loaded, x.new);
    assert(inv_node(p, s2, i));
    // the node acted: it held its epoch for the grace and its view was fresh
    assert(n.core.held + p.grace <= n.clock);
    assert(n.held_real + p.grace <= s.now + 2 * p.skew);
    assert(s.now <= n.last_read_real + p.ttl + 2 * p.skew);
    assert(owner(n.core.members, o) == Some(i));
    assert(n.core.members == s.store.configs[n.core.epoch]);
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(p, s2, i, q) by {
        if q == o && !trusts(n, o) && s.store.docs.contains_key(o) {
            assert(s.store.versions.contains_key(s.store.etags[o]));
        } else {
            assert(inv_cache(p, s, i, q));
        }
    }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(p, s2, i, q) by {
        if q == o {
            let c = x.c;
            if c.previous is Some {
                assert(n.core.armed.contains_key(o));
                assert(inv_armed(s, i, o));
            }
            if x.cur is Some {
                assert(s.store.versions.contains_key(x.cur.unwrap()));
                assert(s.store.born.contains_key(x.cur.unwrap()) && s.store.born[x.cur.unwrap()] <= s.now);
            }
            assert(c.origin == o);
            assert(n2.core.read_any);
            assert(x.begun <= s2.now);
            assert(x.lr <= x.begun);
            assert(x.epoch <= s2.store.config.epoch);
            assert(x.held_real + p.grace <= x.begun + 2 * p.skew);
            assert(s2.store.written[x.epoch] <= x.held_real);
            assert(x.epoch < s2.store.config.epoch ==> x.lr <= s2.store.written[x.epoch + 1]);
            assert(x.begun <= x.lr + p.ttl + 2 * p.skew);
            assert(owner(s2.store.configs[x.epoch], o) == Some(i));
            assert(x.t <= MAX_TIME);
            assert(echod_kernel::properties::inv(x.t, full(x.loaded)));
            assert(echod_kernel::properties::inv(x.t, full(x.new)));
            assert(next_is(x.new, c.deadline));
            assert(c.fired is Some ==> c.fired.unwrap().origin == o && c.fired.unwrap().at <= x.t && s2.store.armer.contains_key(c.fired.unwrap()));
            assert(!c.changed ==> x.new == x.loaded);
            assert(!c.changed && c.fired is Some ==> no_due(x.t, x.loaded));
            assert(c.rearm == (c.changed && c.deadline is Some && (c.previous is None || c.previous.unwrap().at != c.deadline.unwrap())));
            if c.previous is Some {
                let q = c.previous.unwrap();
                assert(q.origin == o);
                assert(s2.store.armer.contains_key(q) && s2.store.armer[q] == i);
                assert(Some(q) != c.fired);
                assert(live(s2, o, x));
                assert(s2.store.docs.contains_key(o) && s2.store.keeper.contains_key(o) && s2.store.keeper[o] == q && has_any(s2.store.docs[o]));
            }
            assert(x.phase is Decided && c.armed_now is None);
            assert(x.cur is Some ==> s2.store.versions.contains_key(x.cur.unwrap()));
            assert(live(s2, o, x) ==> s2.store.doc(o) == x.loaded && s2.store.stamp(o) <= x.t);
            assert(inv_txn(p, s2, i, o));
        } else {
            assert(inv_txn(p, s, i, q));
        }
    }
    assert forall |q: Origin| #[trigger] inv_entry(p, s2, i, q) by {
        assert(inv_entry(p, s, i, q));
    }
    lemma_node_only(p, s, s2, i);
}

/// Every node but `i` keeps its part when the store changes only in ways
/// that do not touch them: stated per lemma, this is the common frame.
proof fn lemma_arm(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, k: AKey)
    requires inv(p)(s), arm(s, i, o, k) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    assert(inv_txn(p, s, i, o));
    assert forall |j: Id| #[trigger] s2.nodes.contains_key(j) implies inv_node(p, s2, j) by {
        assert(inv_node(p, s, j));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(p, s2, j, q) by {
        assert(inv_cache(p, s, j, q));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) implies inv_armed(s2, j, q) by {
        assert(inv_armed(s, j, q));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(p, s2, j, q) by {
        assert(inv_txn(p, s, j, q));
        if j == i && q == o {
            assert(inv_txn(p, s2, i, o));
        }
    }
    assert forall |j: Id, q: Origin| #[trigger] s2.nodes.contains_key(j) implies #[trigger] inv_entry(p, s2, j, q) by {
        assert(inv_entry(p, s, j, q));
    }
    assert(inv_written(s2));
    assert(inv_store(s2));
    assert(inv_timer(s2));
    assemble(p, s2);
}

/// A node with a commit on `o` in flight, loaded at the bucket's current
/// version, acted as owner of `o` when it began. Another node cannot now
/// hold a trusted entry for `o`: a version it wrote while acting as owner,
/// in the bucket's epoch or while fresh. The epochs decide: equal, both
/// own `o`, so they are one node; the commit's newer, the other's view is
/// stale; the commit's older, its node was fresh in an old epoch after the
/// other held a newer one for the grace.
proof fn lemma_no_trusted_entry(p: Params, s: Cluster, i: Id, j: Id, o: Origin)
    requires
        inv(p)(s),
        s.nodes.contains_key(i), s.nodes.contains_key(j), i != j,
        s.nodes[i].txns.contains_key(o),
        live(s, o, s.nodes[i].txns[o]),
        !(s.nodes[i].txns[o].phase is Written),
        s.nodes[j].alive, s.nodes[j].core.read_any, owner(s.nodes[j].core.members, o) == Some(j),
        s.nodes[j].core.epoch == s.store.config.epoch || fresh(s.nodes[j]),
        s.nodes[j].core.cache.contains_key(o),
        s.nodes[j].core.cache[o].wrote,
        s.nodes[j].core.cache[o].filled_at >= s.nodes[j].core.held + p.grace,
    ensures
        false,
{
    disassemble(p, s);
    let x = s.nodes[i].txns[o];
    let m = s.nodes[j];
    assert(inv_txn(p, s, i, o));
    assert(inv_node(p, s, j));
    assert(inv_entry(p, s, j, o));
    assert(inv_cache(p, s, j, o));
    let v = m.core.cache[o].etag;
    assert(Some(v) == s.store.etag(o));
    assert(x.cur == Some(v));
    assert(s.store.born[v] <= x.begun);
    assert(s.store.born[v] + 2 * p.skew >= m.held_real + p.grace);
    if x.epoch == m.core.epoch {
        assert(owner(s.store.configs[x.epoch], o) == Some(i));
        assert(m.core.members == s.store.configs[m.core.epoch]);
        assert(false);
    } else if x.epoch > m.core.epoch {
        assert(m.core.epoch < s.store.config.epoch);
        assert(m.last_read_real <= s.store.written[m.core.epoch + 1]);
        assert(s.store.written[m.core.epoch + 1] <= s.store.written[x.epoch]);
        assert(s.store.written[x.epoch] <= x.held_real);
        assert(x.held_real + p.grace <= x.begun + 2 * p.skew);
        assert(x.begun <= s.now);
        // so the other node's last read is older than the grace, less the slack: stale
        assert(fresh(m));
        assert(s.now <= m.clock + p.skew);
        assert(m.clock <= m.core.last_read + p.ttl);
        assert(m.core.last_read <= m.last_read_real + p.skew);
        assert(s.now <= m.last_read_real + p.ttl + 2 * p.skew);
        assert(false);
    } else {
        assert(x.epoch < s.store.config.epoch);
        assert(x.lr <= s.store.written[x.epoch + 1]);
        assert(s.store.written[x.epoch + 1] <= s.store.written[m.core.epoch]);
        assert(s.store.written[m.core.epoch] <= m.held_real);
        assert(x.begun <= x.lr + p.ttl + 2 * p.skew);
        assert(false);
    }
}

/// After a write of `o` by `i`, every cache entry of another node for `o`
/// that the invariant protects was shown impossible; this node's own entry
/// is the version written.
proof fn lemma_entries_after_write(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires
        inv(p)(s),
        s.nodes.contains_key(i),
        s.nodes[i].txns.contains_key(o),
        live(s, o, s.nodes[i].txns[o]),
        !(s.nodes[i].txns[o].phase is Written),
        s2.store.etag(o) == Some(e),
        s2.now == s.now,
        s2.store.config == s.store.config,
        s2.store.written == s.store.written,
        s2.store.configs == s.store.configs,
        forall |j: Id| #[trigger] s2.nodes.contains_key(j) <==> s.nodes.contains_key(j),
        forall |j: Id| j != i && #[trigger] s2.nodes.contains_key(j) ==> s2.nodes[j] == s.nodes[j],
        s2.nodes[i].core == spec_filled(s.nodes[i].core, o, e, s.nodes[i].clock, true) || s2.nodes[i].core == spec_collected(spec_filled(s.nodes[i].core, o, e, s.nodes[i].clock, true), o, s.nodes[i].txns[o].c.fired.unwrap()),
        s2.nodes[i].alive == s.nodes[i].alive,
        s2.nodes[i].clock == s.nodes[i].clock,
        forall |q: Origin| q != o ==> s2.store.etag(q) == s.store.etag(q),
    ensures
        forall |j: Id, q: Origin| #[trigger] s2.nodes.contains_key(j) ==> #[trigger] inv_entry(p, s2, j, q),
{
    disassemble(p, s);
    assert forall |j: Id, q: Origin| #[trigger] s2.nodes.contains_key(j) implies #[trigger] inv_entry(p, s2, j, q) by {
        assert(inv_entry(p, s, j, q));
        assert(inv_node(p, s, j));
        if q == o {
            if j == i {
                assert(s2.nodes[i].core.cache[o].etag == e);
            } else {
                let m = s.nodes[j];
                if m.alive && m.core.read_any && (m.core.epoch == s.store.config.epoch || fresh(m)) && owner(m.core.members, o) == Some(j)
                    && m.core.cache.contains_key(o) && m.core.cache[o].wrote && m.core.cache[o].filled_at >= m.core.held + p.grace {
                    lemma_no_trusted_entry(p, s, i, j, o);
                }
            }
        }
    }
}

proof fn lemma_commit_nodes(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), commit(s, i, o, e) == Some(s2),
    ensures forall |j: Id| #[trigger] s2.nodes.contains_key(j) ==> inv_node(p, s2, j),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    let kept = spec_keep(c);
    if c.deadline is Some {
        if c.rearm {
            assert(x.phase is Armed);
            assert(s.store.timers.contains(c.armed_now.unwrap()));
        } else {
            let q = c.previous.unwrap();
            assert(s.store.keeper[o] == q && has_any(s.store.docs[o]));
            assert(s.store.timers.contains(q));
        }
        assert(kept is Some && s2.store.timers.contains(kept.unwrap()) && Some(kept.unwrap().at) == c.deadline && kept.unwrap().origin == o);
    }
    assert forall |j: Id| #[trigger] s2.nodes.contains_key(j) implies inv_node(p, s2, j) by {
        assert(inv_node(p, s, j));
    }
}

proof fn lemma_commit_cache(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), commit(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) ==> inv_cache(p, s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    let kept = spec_keep(c);
    if c.deadline is Some {
        if c.rearm {
            assert(x.phase is Armed);
            assert(s.store.timers.contains(c.armed_now.unwrap()));
        } else {
            let q = c.previous.unwrap();
            assert(s.store.keeper[o] == q && has_any(s.store.docs[o]));
            assert(s.store.timers.contains(q));
        }
        assert(kept is Some && s2.store.timers.contains(kept.unwrap()) && Some(kept.unwrap().at) == c.deadline && kept.unwrap().origin == o);
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(p, s2, j, q) by {
        if j == i && q == o {
            // a version this node wrote now, while acting when it began
            if n.clock >= n.core.held + p.grace {
                assert(n.held_real <= n.core.held + p.skew);
                assert(n.clock <= s.now + p.skew);
            }
        } else {
            assert(inv_cache(p, s, j, q));
        }
    }
}

proof fn lemma_commit_armed(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), commit(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) ==> inv_armed(s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    let kept = spec_keep(c);
    if c.deadline is Some {
        if c.rearm {
            assert(x.phase is Armed);
            assert(s.store.timers.contains(c.armed_now.unwrap()));
        } else {
            let q = c.previous.unwrap();
            assert(s.store.keeper[o] == q && has_any(s.store.docs[o]));
            assert(s.store.timers.contains(q));
        }
        assert(kept is Some && s2.store.timers.contains(kept.unwrap()) && Some(kept.unwrap().at) == c.deadline && kept.unwrap().origin == o);
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) implies inv_armed(s2, j, q) by {
        assert(inv_armed(s, j, q));
    }
}

proof fn lemma_commit_txns(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), commit(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) ==> inv_txn(p, s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    let kept = spec_keep(c);
    if c.deadline is Some {
        if c.rearm {
            assert(x.phase is Armed);
            assert(s.store.timers.contains(c.armed_now.unwrap()));
        } else {
            let q = c.previous.unwrap();
            assert(s.store.keeper[o] == q && has_any(s.store.docs[o]));
            assert(s.store.timers.contains(q));
        }
        assert(kept is Some && s2.store.timers.contains(kept.unwrap()) && Some(kept.unwrap().at) == c.deadline && kept.unwrap().origin == o);
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(p, s2, j, q) by {
        assert(inv_txn(p, s, j, q));
        if j == i && q == o {
            assert(inv_txn(p, s2, i, o));
        } else if q == o {
            let y = s.nodes[j].txns[o];
            assert(j != i);
            assert(!live(s2, o, y));
            if y.phase is Written {
                if !kept_covers(s2, o, y) {
                    if s2.store.keeper.contains_key(o) {
                        assert(s2.store.keeper[o] == kept.unwrap());
                        assert(s2.store.armer[kept.unwrap()] == i);
                    }
                }
            }
            assert(inv_txn(p, s2, j, q));
        } else {
            assert(inv_txn(p, s2, j, q));
        }
    }
}

proof fn lemma_commit_store(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), commit(s, i, o, e) == Some(s2),
    ensures inv_written(s2), inv_store(s2), inv_timer(s2),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    let kept = spec_keep(c);
    if c.deadline is Some {
        if c.rearm {
            assert(x.phase is Armed);
            assert(s.store.timers.contains(c.armed_now.unwrap()));
        } else {
            let q = c.previous.unwrap();
            assert(s.store.keeper[o] == q && has_any(s.store.docs[o]));
            assert(s.store.timers.contains(q));
        }
        assert(kept is Some && s2.store.timers.contains(kept.unwrap()) && Some(kept.unwrap().at) == c.deadline && kept.unwrap().origin == o);
    }
    assert(inv_written(s2));
    assert(inv_store(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) implies {
            &&& s2.store.etags.contains_key(q)
            &&& s2.store.stamps.contains_key(q)
            &&& s2.store.stamps[q] <= MAX_TIME
            &&& echod_kernel::properties::inv(s2.store.stamps[q], full(s2.store.docs[q]))
            &&& s2.store.versions.contains_key(s2.store.etags[q])
            &&& s2.store.versions[s2.store.etags[q]] == s2.store.docs[q]
        } by {
            if q != o {
                assert(s.store.docs.contains_key(q));
            }
        }
        assert forall |v: Seq<char>| #[trigger] s2.store.versions.contains_key(v) implies s2.store.born.contains_key(v) && s2.store.born[v] <= s2.now by {
            if v != e { assert(s.store.versions.contains_key(v)); }
        }
    }
    assert(inv_timer(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) && has_any(s2.store.docs[q]) implies {
            &&& s2.store.keeper.contains_key(q)
            &&& s2.store.timers.contains(s2.store.keeper[q])
            &&& s2.store.keeper[q].origin == q
            &&& is_next(s2.store.docs[q], s2.store.keeper[q].at)
        } by {
            if q == o {
                assert(c.deadline is Some);
            } else {
                assert(s.store.docs.contains_key(q) && has_any(s.store.docs[q]));
            }
        }
    }
}

proof fn lemma_commit(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), commit(s, i, o, e) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    lemma_commit_nodes(p, s, s2, i, o, e);
    lemma_commit_cache(p, s, s2, i, o, e);
    lemma_commit_armed(p, s, s2, i, o, e);
    lemma_commit_txns(p, s, s2, i, o, e);
    lemma_commit_store(p, s, s2, i, o, e);
    lemma_entries_after_write(p, s, s2, i, o, e);
    assemble(p, s2);
}

proof fn lemma_commit_fail(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv(p)(s), commit_fail(s, i, o) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert(inv_node(p, s, i));
    assert(inv_node(p, s2, i));
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(p, s2, i, q) by { assert(inv_cache(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(p, s2, i, q) by { assert(inv_txn(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] inv_entry(p, s2, i, q) by { assert(inv_entry(p, s, i, q)); }
    lemma_node_only(p, s, s2, i);
}

proof fn lemma_disarm(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv(p)(s), disarm(s, i, o) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let q0 = spec_to_disarm(c).unwrap();
    assert(inv_txn(p, s, i, o));
    assert(c.previous == Some(q0));
    assert(s.store.armer[q0] == i && q0.origin == o);
    assert(c.changed && (c.deadline is None || c.rearm));
    assert forall |j: Id| #[trigger] s2.nodes.contains_key(j) implies inv_node(p, s2, j) by {
        assert(inv_node(p, s, j));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(p, s2, j, q) by {
        assert(inv_cache(p, s, j, q));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) implies inv_armed(s2, j, q) by {
        assert(inv_armed(s, j, q));
    }
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(p, s2, j, q) by {
        assert(inv_txn(p, s, j, q));
        let y = s.nodes[j].txns[q];
        if y.c.armed_now is Some {
            let k = y.c.armed_now.unwrap();
            if k == q0 {
                // the same key: same armer and origin, so this node's own on o — but this node's only commit on o is x, whose key is not its previous
                assert(s.store.armer[k] == j);
                assert(j == i);
                assert(k.origin == q);
                assert(q == o);
                assert(y == x);
                assert(Some(k) != c.previous);
                assert(false);
            }
        }
    }
    assert forall |j: Id, q: Origin| #[trigger] s2.nodes.contains_key(j) implies #[trigger] inv_entry(p, s2, j, q) by {
        assert(inv_entry(p, s, j, q));
    }
    assert(inv_written(s2));
    assert(inv_store(s2));
    assert(inv_timer(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) && has_any(s2.store.docs[q]) implies {
            &&& s2.store.keeper.contains_key(q)
            &&& s2.store.timers.contains(s2.store.keeper[q])
            &&& s2.store.keeper[q].origin == q
            &&& is_next(s2.store.docs[q], s2.store.keeper[q].at)
        } by {
            assert(s.store.docs.contains_key(q) && has_any(s.store.docs[q]));
            if q == o {
                let kp = s.store.keeper[o];
                if kept_covers(s, o, x) {
                    if c.deadline is None {
                        assert(!has_any(s.store.docs[o]));
                        assert(false);
                    } else {
                        assert(kp == c.armed_now.unwrap());
                        assert(kp != q0);
                    }
                } else {
                    assert(s.store.armer[kp] != i);
                    assert(kp != q0);
                }
            } else {
                assert(s.store.keeper[q].origin == q);
                assert(s.store.keeper[q] != q0);
            }
        }
    }
    assemble(p, s2);
}

proof fn lemma_finish_nodes(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv(p)(s), finish(s, i, o, deleted) == Some(s2),
    ensures forall |j: Id| #[trigger] s2.nodes.contains_key(j) ==> inv_node(p, s2, j),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    let kept = spec_keep(c);
    assert forall |j: Id| #[trigger] s2.nodes.contains_key(j) implies inv_node(p, s2, j) by {
        assert(inv_node(p, s, j));
    }
}

proof fn lemma_finish_cache(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv(p)(s), finish(s, i, o, deleted) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) ==> inv_cache(p, s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    let kept = spec_keep(c);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(p, s2, j, q) by {
        assert(inv_cache(p, s, j, q));
    }
}

proof fn lemma_finish_armed(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv(p)(s), finish(s, i, o, deleted) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) ==> inv_armed(s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
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
        } else {
            assert(inv_armed(s, j, q));
        }
    }
}

proof fn lemma_finish_txns(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv(p)(s), finish(s, i, o, deleted) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) ==> inv_txn(p, s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    let kept = spec_keep(c);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(p, s2, j, q) by {
        assert(inv_txn(p, s, j, q));
        let y = s.nodes[j].txns[q];
        if deleted && y.c.armed_now is Some {
            let k = y.c.armed_now.unwrap();
            let f = c.fired.unwrap();
            if k == f {
                assert(s.store.armer[k] == j);
                assert(s.store.armer[f] == i);
                assert(j == i);
                assert(k.origin == q);
                assert(q == o);
                assert(y == x);
                assert(Some(k) != c.fired);
                assert(false);
            }
        }
    }
}

proof fn lemma_finish_entries(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv(p)(s), finish(s, i, o, deleted) == Some(s2),
    ensures forall |j: Id, q: Origin| #[trigger] s2.nodes.contains_key(j) ==> #[trigger] inv_entry(p, s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    let kept = spec_keep(c);
    assert forall |j: Id, q: Origin| #[trigger] s2.nodes.contains_key(j) implies #[trigger] inv_entry(p, s2, j, q) by {
        assert(inv_entry(p, s, j, q));
    }
}

proof fn lemma_finish_store(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv(p)(s), finish(s, i, o, deleted) == Some(s2),
    ensures inv_written(s2), inv_store(s2), inv_timer(s2),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let e = x.cur.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    let kept = spec_keep(c);
    assert(inv_written(s2));
    assert(inv_store(s2));
    assert(inv_timer(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) && has_any(s2.store.docs[q]) implies {
            &&& s2.store.keeper.contains_key(q)
            &&& s2.store.timers.contains(s2.store.keeper[q])
            &&& s2.store.keeper[q].origin == q
            &&& is_next(s2.store.docs[q], s2.store.keeper[q].at)
        } by {
            assert(s.store.docs.contains_key(q) && has_any(s.store.docs[q]));
            if deleted {
                let f = c.fired.unwrap();
                let kp = s.store.keeper[q];
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
                        assert(s.store.armer[kp] != i);
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

proof fn lemma_finish(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires inv(p)(s), finish(s, i, o, deleted) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    lemma_finish_nodes(p, s, s2, i, o, deleted);
    lemma_finish_cache(p, s, s2, i, o, deleted);
    lemma_finish_armed(p, s, s2, i, o, deleted);
    lemma_finish_txns(p, s, s2, i, o, deleted);
    lemma_finish_entries(p, s, s2, i, o, deleted);
    lemma_finish_store(p, s, s2, i, o, deleted);
    assemble(p, s2);
}

proof fn lemma_collect_nodes(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), collect(s, i, o, e) == Some(s2),
    ensures forall |j: Id| #[trigger] s2.nodes.contains_key(j) ==> inv_node(p, s2, j),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert forall |j: Id| #[trigger] s2.nodes.contains_key(j) implies inv_node(p, s2, j) by {
        assert(inv_node(p, s, j));
    }
}

proof fn lemma_collect_cache(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), collect(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) ==> inv_cache(p, s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.cache.contains_key(q) implies inv_cache(p, s2, j, q) by {
        if j == i && q == o {
            if n.clock >= n.core.held + p.grace {
                assert(n.held_real <= n.core.held + p.skew);
                assert(n.clock <= s.now + p.skew);
            }
        } else {
            assert(inv_cache(p, s, j, q));
        }
    }
}

proof fn lemma_collect_armed(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), collect(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].core.armed.contains_key(q) ==> inv_armed(s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
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

proof fn lemma_collect_txns(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), collect(s, i, o, e) == Some(s2),
    ensures forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) ==> inv_txn(p, s2, j, q),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert forall |j: Id, q: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(q) implies inv_txn(p, s2, j, q) by {
        assert(inv_txn(p, s, j, q));
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

proof fn lemma_collect_store(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), collect(s, i, o, e) == Some(s2),
    ensures inv_written(s2), inv_store(s2), inv_timer(s2),
{
    disassemble(p, s);
    disassemble(p, s);
    let n = s.nodes[i];
    let x = n.txns[o];
    let c = x.c;
    let k = c.fired.unwrap();
    assert(inv_node(p, s, i));
    assert(inv_txn(p, s, i, o));
    assert(live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(no_due(x.t, x.loaded));
    lemma_no_due(x.t, x.loaded);
    assert(inv_written(s2));
    assert(inv_store(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) implies {
            &&& s2.store.etags.contains_key(q)
            &&& s2.store.stamps.contains_key(q)
            &&& s2.store.stamps[q] <= MAX_TIME
            &&& echod_kernel::properties::inv(s2.store.stamps[q], full(s2.store.docs[q]))
            &&& s2.store.versions.contains_key(s2.store.etags[q])
            &&& s2.store.versions[s2.store.etags[q]] == s2.store.docs[q]
        } by {
            if q != o {
                assert(s.store.docs.contains_key(q));
            }
        }
        assert forall |v: Seq<char>| #[trigger] s2.store.versions.contains_key(v) implies s2.store.born.contains_key(v) && s2.store.born[v] <= s2.now by {
            if v != e { assert(s.store.versions.contains_key(v)); }
        }
    }
    assert(inv_timer(s2)) by {
        assert forall |q: Origin| #[trigger] s2.store.docs.contains_key(q) && has_any(s2.store.docs[q]) implies {
            &&& s2.store.keeper.contains_key(q)
            &&& s2.store.timers.contains(s2.store.keeper[q])
            &&& s2.store.keeper[q].origin == q
            &&& is_next(s2.store.docs[q], s2.store.keeper[q].at)
        } by {
            if q == o {
                assert(s2.store.docs[o] == x.loaded);
                assert(s.store.docs.contains_key(o));
                assert(has_any(s.store.docs[o]));
                let kp = s.store.keeper[o];
                assert(has_deadline(x.loaded, kp.at));
                assert(kp.at > x.t);
                assert(k.at <= x.t);
                assert(kp != k);
            } else {
                assert(s.store.docs.contains_key(q) && has_any(s.store.docs[q]));
                assert(s.store.keeper[q].origin == q);
                assert(s.store.keeper[q] != k);
            }
        }
    }
}

proof fn lemma_collect(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires inv(p)(s), collect(s, i, o, e) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    lemma_collect_nodes(p, s, s2, i, o, e);
    lemma_collect_cache(p, s, s2, i, o, e);
    lemma_collect_armed(p, s, s2, i, o, e);
    lemma_collect_txns(p, s, s2, i, o, e);
    lemma_collect_store(p, s, s2, i, o, e);
    lemma_entries_after_write(p, s, s2, i, o, e);
    assemble(p, s2);
}

proof fn lemma_collect_fail(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv(p)(s), collect_fail(s, i, o) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert(inv_node(p, s, i));
    assert(inv_node(p, s2, i));
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(p, s2, i, q) by { assert(inv_cache(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(p, s2, i, q) by { assert(inv_txn(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] inv_entry(p, s2, i, q) by { assert(inv_entry(p, s, i, q)); }
    lemma_node_only(p, s, s2, i);
}

proof fn lemma_done(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv(p)(s), done(s, i, o) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert(inv_node(p, s, i));
    assert(inv_node(p, s2, i));
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(p, s2, i, q) by { assert(inv_cache(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(p, s2, i, q) by { assert(inv_txn(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] inv_entry(p, s2, i, q) by { assert(inv_entry(p, s, i, q)); }
    lemma_node_only(p, s, s2, i);
}

proof fn lemma_abort(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv(p)(s), abort(s, i, o) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert(inv_node(p, s, i));
    assert(inv_node(p, s2, i));
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.cache.contains_key(q) implies inv_cache(p, s2, i, q) by { assert(inv_cache(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].core.armed.contains_key(q) implies inv_armed(s2, i, q) by { assert(inv_armed(s, i, q)); }
    assert forall |q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies inv_txn(p, s2, i, q) by { assert(inv_txn(p, s, i, q)); }
    assert forall |q: Origin| #[trigger] inv_entry(p, s2, i, q) by { assert(inv_entry(p, s, i, q)); }
    lemma_node_only(p, s, s2, i);
}

pub proof fn lemma_next(p: Params, s: Cluster, s2: Cluster)
    requires inv(p)(s), next(p)(s, s2),
    ensures inv(p)(s2),
{
    let st = choose |st: Step| #[trigger] next_by(p, st, s, s2);
    match st {
        Step::Advance(d) => lemma_advance(p, s, s2, d),
        Step::Tick(i, d) => lemma_tick(p, s, s2, i, d),
        Step::Join(i, c) => lemma_join(p, s, s2, i, c),
        Step::Crash(i) => lemma_crash(p, s, s2, i),
        Step::ReadConfig(i) => lemma_read_config(p, s, s2, i),
        Step::Propose(i, m) => lemma_propose(p, s, s2, i, m),
        Step::Forget(i, o) => lemma_forget(p, s, s2, i, o),
        Step::Begin(i, o, t, new, fired, did, deadline) => lemma_begin(p, s, s2, i, o, t, new, fired, did, deadline),
        Step::Arm(i, o, k) => lemma_arm(p, s, s2, i, o, k),
        Step::Commit(i, o, e) => lemma_commit(p, s, s2, i, o, e),
        Step::CommitFail(i, o) => lemma_commit_fail(p, s, s2, i, o),
        Step::Disarm(i, o) => lemma_disarm(p, s, s2, i, o),
        Step::Finish(i, o, deleted) => lemma_finish(p, s, s2, i, o, deleted),
        Step::Collect(i, o, e) => lemma_collect(p, s, s2, i, o, e),
        Step::CollectFail(i, o) => lemma_collect_fail(p, s, s2, i, o),
        Step::Done(i, o) => lemma_done(p, s, s2, i, o),
        Step::Abort(i, o) => lemma_abort(p, s, s2, i, o),
    }
}

// ---------------------------------------------------------------------------
// The theorem, in the temporal logic
// ---------------------------------------------------------------------------

/// Every execution that starts in `init` and steps by `next` satisfies the
/// invariant forever — and with it exclusion, currency, the catalogue on
/// every document, and a timer for every deadline.
pub proof fn safety(p: Params, spec: TempPred<Cluster>)
    requires
        p.wf(),
        spec.entails(lift_state(init())),
        spec.entails(always(lift_action(next(p)))),
    ensures
        spec.entails(always(lift_state(inv(p)))),
{
    assert forall |s: Cluster| #[trigger] init()(s) implies inv(p)(s) by { lemma_init(p, s); }
    assert forall |s: Cluster, s2: Cluster| inv(p)(s) && #[trigger] next(p)(s, s2) implies inv(p)(s2) by { lemma_next(p, s, s2); }
    init_invariant::<Cluster>(spec, init(), next(p), inv(p));
}

} // verus!

verus! {

/// The invariant is not vacuous: a fleet of one node, past the grace, holding
/// a document it wrote, trusts its cache of it and satisfies the invariant.
pub proof fn not_vacuous(p: Params, o: Origin)
    requires p.wf(),
    ensures exists |s: Cluster| #[trigger] inv(p)(s) && s.nodes.contains_key(seq!['n']) && trusts(s.nodes[seq!['n']], o),
{
    let now = p.grace;
    let me: Id = seq!['n'];
    let e: Seq<char> = seq!['v'];
    let empty: Doc = Map::empty();
    let core = ANode {
        id: me, ttl: p.ttl, grace: p.grace, read_any: true, epoch: 0, members: seq![me],
        last_read: now, held: 0,
        cache: Map::empty().insert(o, AEntry { etag: e, filled_at: now, wrote: true }),
        armed: Map::empty(),
    };
    let n = Node { core, bodies: Map::empty().insert(o, empty), alive: true, clock: now, last_read_real: now, held_real: 0, txns: Map::empty() };
    let s = Cluster {
        now,
        nodes: Map::empty().insert(me, n),
        store: Store {
            docs: Map::empty().insert(o, empty),
            etags: Map::empty().insert(o, e),
            stamps: Map::empty().insert(o, 0),
            versions: Map::empty().insert(e, empty),
            born: Map::empty().insert(e, now),
            configs: Map::empty().insert(0, seq![me]),
            keeper: Map::empty(),
            timers: Set::empty(),
            armer: Map::empty(),
            config: Config { epoch: 0, members: seq![me] },
            written: Map::empty().insert(0, 0),
        },
    };
    lemma_inv_empty(0);
    assert(owner(seq![me], o) == Some(me));
    assert(inv_node(p, s, me));
    assert(inv_written(s));
    assert(inv_store(s));
    assert(inv_timer(s)) by {
        assert forall |q: Origin| #[trigger] s.store.docs.contains_key(q) && has_any(s.store.docs[q]) implies false by {
            let t = choose |t: nat| has_deadline(empty, t);
            let id = choose |id: Seq<char>| #[trigger] empty.contains_key(id) && deadline_at(empty[id], t);
        }
    }
    assert forall |i: Id| #[trigger] s.nodes.contains_key(i) implies inv_node(p, s, i) by {}
    assert forall |i: Id, q: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.cache.contains_key(q) implies inv_cache(p, s, i, q) by {}
    assert forall |i: Id, q: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].core.armed.contains_key(q) implies inv_armed(s, i, q) by {}
    assert forall |i: Id, q: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(q) implies inv_txn(p, s, i, q) by {}
    assert forall |i: Id, q: Origin| #[trigger] s.nodes.contains_key(i) implies #[trigger] inv_entry(p, s, i, q) by {}
    assemble(p, s);
    assert(trusts(s.nodes[me], o));
}

} // verus!
