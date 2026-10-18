//! The invariant, and the induction that keeps it.
//!
//! Two theorems come out of it:
//!
//! - **Exclusion.** Two live nodes never both act as owner of one origin.
//! - **Currency.** A node that answers an origin from its cache holds the
//!   bucket's current version of it.
//!
//! Both rest on the hypothesis that every live clock is within `skew` of
//! real time and on `grace > ttl + 4 skew`: a node in an old epoch is fresh
//! for at most `ttl` after its last read, which happened before the newer
//! epoch was written; a node in the newer epoch acts only `grace` after it
//! first read it; with the clock slack on both sides, the two windows do not
//! meet.

use vstd::prelude::*;

use crate::spec::cluster::*;
use crate::tla::defs::*;
use crate::tla::rules::*;

verus! {

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

/// What holds of one node.
pub open spec fn inv_node(p: Params, s: Cluster, i: Id) -> bool {
    let n = s.nodes[i];
    &&& n.id == i
    &&& n.epoch <= s.store.config.epoch
    &&& n.alive ==> clock_ok(p, s.now, n.clock)
    &&& n.read_any ==> {
        &&& n.last_read <= n.clock
        &&& n.held <= n.last_read
        &&& n.last_read_real <= s.now
        &&& n.held_real <= n.last_read_real
        &&& n.last_read <= n.last_read_real + p.skew
        &&& n.held + p.skew >= n.held_real
        // the epoch it holds was written before it first read it
        &&& n.held_real >= s.store.written[n.epoch]
        // an epoch it does not hold yet was written after its last read
        &&& n.epoch < s.store.config.epoch ==> n.last_read_real <= s.store.written[n.epoch + 1]
        // the members it holds are the epoch's
        &&& n.epoch == s.store.config.epoch ==> n.members == s.store.config.members
    }
    &&& forall |o: Origin| #[trigger] n.cache.contains_key(o) ==> n.cache[o].filled_at <= n.clock
}

/// Two nodes holding one epoch hold its members.
pub open spec fn inv_members(s: Cluster) -> bool {
    forall |i: Id, j: Id| s.nodes.contains_key(i) && s.nodes.contains_key(j)
        && s.nodes[i].read_any && s.nodes[j].read_any && s.nodes[i].epoch == s.nodes[j].epoch
        ==> #[trigger] s.nodes[i].members == #[trigger] s.nodes[j].members
}

/// The epochs' write times: one per epoch, in order, none in the future.
pub open spec fn inv_written(s: Cluster) -> bool {
    &&& forall |e: nat| e <= s.store.config.epoch ==> #[trigger] s.store.written.contains_key(e)
    &&& forall |e: nat, e2: nat| e <= e2 && e2 <= s.store.config.epoch ==> #[trigger] s.store.written[e] <= #[trigger] s.store.written[e2]
    &&& s.store.written[s.store.config.epoch] <= s.now
}

/// A cache entry filled by the owner, after the grace, in the bucket's own
/// epoch, is the bucket's version. Freshness is not required: in the
/// bucket's epoch, nobody else is the owner.
pub open spec fn inv_entry_current_epoch(p: Params, s: Cluster, i: Id, o: Origin) -> bool {
    let n = s.nodes[i];
    n.alive && n.read_any && n.epoch == s.store.config.epoch && owner(n.members, o) == Some(i)
        && n.cache.contains_key(o) && n.cache[o].filled_at >= n.held + p.grace
        ==> n.cache[o].version == s.store.version(o)
}

/// The same for a node in an older epoch, while it is fresh: the newer
/// epoch's owner has not begun to act.
pub open spec fn inv_entry_old_epoch(p: Params, s: Cluster, i: Id, o: Origin) -> bool {
    let n = s.nodes[i];
    n.alive && n.read_any && n.epoch < s.store.config.epoch && fresh(p, n) && owner(n.members, o) == Some(i)
        && n.cache.contains_key(o) && n.cache[o].filled_at >= n.held + p.grace
        ==> n.cache[o].version == s.store.version(o)
}

pub open spec fn inv(p: Params) -> spec_fn(Cluster) -> bool {
    |s: Cluster| {
        &&& p.wf()
        &&& inv_written(s)
        &&& inv_members(s)
        &&& forall |i: Id| #[trigger] s.nodes.contains_key(i) ==> inv_node(p, s, i)
        &&& forall |i: Id, o: Origin| #[trigger] s.nodes.contains_key(i) ==> #[trigger] inv_entry_current_epoch(p, s, i, o)
        &&& forall |i: Id, o: Origin| #[trigger] s.nodes.contains_key(i) ==> #[trigger] inv_entry_old_epoch(p, s, i, o)
    }
}

/// The invariant from its conjuncts, stated so each lemma proves them apart.
pub proof fn assemble(p: Params, s: Cluster)
    requires
        p.wf(),
        inv_written(s),
        inv_members(s),
        forall |i: Id| #[trigger] s.nodes.contains_key(i) ==> inv_node(p, s, i),
        forall |i: Id, o: Origin| #[trigger] s.nodes.contains_key(i) ==> #[trigger] inv_entry_current_epoch(p, s, i, o),
        forall |i: Id, o: Origin| #[trigger] s.nodes.contains_key(i) ==> #[trigger] inv_entry_old_epoch(p, s, i, o),
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
        inv_members(s),
        forall |i: Id| #[trigger] s.nodes.contains_key(i) ==> inv_node(p, s, i),
        forall |i: Id, o: Origin| #[trigger] s.nodes.contains_key(i) ==> #[trigger] inv_entry_current_epoch(p, s, i, o),
        forall |i: Id, o: Origin| #[trigger] s.nodes.contains_key(i) ==> #[trigger] inv_entry_old_epoch(p, s, i, o),
{
}

// ---------------------------------------------------------------------------
// The two theorems, from the invariant
// ---------------------------------------------------------------------------

/// Two live nodes never both act as owner of one origin.
pub proof fn exclusion(p: Params, s: Cluster, i: Id, j: Id, o: Origin)
    requires
        inv(p)(s),
        s.nodes.contains_key(i),
        s.nodes.contains_key(j),
        acts(p, s.nodes[i], o),
        acts(p, s.nodes[j], o),
    ensures
        i == j,
{
    let n = s.nodes[i];
    let m = s.nodes[j];
    assert(inv_node(p, s, i));
    assert(inv_node(p, s, j));
    if n.epoch == m.epoch {
        assert(n.members == m.members);
    } else if n.epoch < m.epoch {
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
        s.nodes[i].read_any, s.nodes[j].read_any,
        s.nodes[i].epoch < s.nodes[j].epoch,
        fresh(p, s.nodes[i]),
        s.nodes[j].held + p.grace <= s.nodes[j].clock,
    ensures
        false,
{
    let n = s.nodes[i];
    let m = s.nodes[j];
    assert(inv_node(p, s, i));
    assert(inv_node(p, s, j));
    // n read before epoch n.epoch + 1 was written, which is no later than
    // m's epoch was written, which is no later than m first read it.
    assert(s.store.written[n.epoch + 1] <= s.store.written[m.epoch]);
    assert(n.last_read_real <= m.held_real);
    // n is fresh: real time is within ttl + 2 skew of its last read.
    assert(s.now <= n.clock + p.skew);
    assert(n.clock <= n.last_read + p.ttl);
    assert(s.now <= n.last_read_real + p.ttl + 2 * p.skew);
    // m has held for the grace: real time is at least grace - 2 skew past its first read.
    assert(m.clock <= s.now + p.skew);
    assert(m.held_real + p.grace <= s.now + 2 * p.skew);
    assert(p.grace <= p.ttl + 4 * p.skew);
}

/// A node that answers from its cache holds the bucket's current version.
pub proof fn currency(p: Params, s: Cluster, i: Id, o: Origin)
    requires
        inv(p)(s),
        s.nodes.contains_key(i),
        trusts(p, s.nodes[i], o),
    ensures
        s.nodes[i].cache[o].version == s.store.version(o),
{
    assert(inv_node(p, s, i));
    assert(inv_entry_current_epoch(p, s, i, o));
    assert(inv_entry_old_epoch(p, s, i, o));
}

// ---------------------------------------------------------------------------
// The induction
// ---------------------------------------------------------------------------

pub proof fn lemma_init(p: Params, s: Cluster)
    requires p.wf(), init_state(s),
    ensures inv(p)(s),
{
    assert(s.store.written.contains_key(0));
    assert forall |e: nat| e <= s.store.config.epoch implies #[trigger] s.store.written.contains_key(e) by {}
}

proof fn lemma_advance(p: Params, s: Cluster, s2: Cluster, d: nat)
    requires inv(p)(s), advance(p, s, d) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert forall |i: Id| #[trigger] s2.nodes.contains_key(i) implies inv_node(p, s2, i) by {
        assert(inv_node(p, s, i));
    }
    assert forall |i: Id, o: Origin| #[trigger] s2.nodes.contains_key(i) implies #[trigger] inv_entry_current_epoch(p, s2, i, o) by {
        assert(inv_entry_current_epoch(p, s, i, o));
        assert(inv_entry_old_epoch(p, s, i, o));
        assert(inv_node(p, s, i));
    }
    assert forall |i: Id, o: Origin| #[trigger] s2.nodes.contains_key(i) implies #[trigger] inv_entry_old_epoch(p, s2, i, o) by {
        assert(inv_entry_current_epoch(p, s, i, o));
        assert(inv_entry_old_epoch(p, s, i, o));
        assert(inv_node(p, s, i));
    }
    assert(inv_written(s2));
    assert(inv_members(s2));
    assemble(p, s2);
}

proof fn lemma_tick(p: Params, s: Cluster, s2: Cluster, i: Id, d: nat)
    requires inv(p)(s), tick(p, s, i, d) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert forall |k: Id| #[trigger] s2.nodes.contains_key(k) implies inv_node(p, s2, k) by {
        assert(inv_node(p, s, k));
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_current_epoch(p, s2, k, o) by {
        assert(inv_entry_current_epoch(p, s, k, o));
        assert(inv_entry_old_epoch(p, s, k, o));
        assert(inv_node(p, s, k));
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_old_epoch(p, s2, k, o) by {
        assert(inv_entry_current_epoch(p, s, k, o));
        assert(inv_entry_old_epoch(p, s, k, o));
        assert(inv_node(p, s, k));
    }
    assert(inv_written(s2));
    assert(inv_members(s2));
    assemble(p, s2);
}

proof fn lemma_join(p: Params, s: Cluster, s2: Cluster, i: Id, c: nat)
    requires inv(p)(s), join(p, s, i, c) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert forall |k: Id| #[trigger] s2.nodes.contains_key(k) implies inv_node(p, s2, k) by {
        if k != i { assert(inv_node(p, s, k)); }
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_current_epoch(p, s2, k, o) by {
        if k != i {
            assert(inv_entry_current_epoch(p, s, k, o));
        }
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_old_epoch(p, s2, k, o) by {
        if k != i {
            assert(inv_entry_old_epoch(p, s, k, o));
        }
    }
    assert(inv_written(s2));
    assert(inv_members(s2));
    assemble(p, s2);
}

proof fn lemma_crash(p: Params, s: Cluster, s2: Cluster, i: Id)
    requires inv(p)(s), crash(s, i) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert forall |k: Id| #[trigger] s2.nodes.contains_key(k) implies inv_node(p, s2, k) by {
        assert(inv_node(p, s, k));
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_current_epoch(p, s2, k, o) by {
        assert(inv_entry_current_epoch(p, s, k, o));
        assert(inv_entry_old_epoch(p, s, k, o));
        assert(inv_node(p, s, k));
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_old_epoch(p, s2, k, o) by {
        assert(inv_entry_current_epoch(p, s, k, o));
        assert(inv_entry_old_epoch(p, s, k, o));
        assert(inv_node(p, s, k));
    }
    assert(inv_written(s2));
    assert(inv_members(s2));
    assemble(p, s2);
}

proof fn lemma_read_config(p: Params, s: Cluster, s2: Cluster, i: Id)
    requires inv(p)(s), read_config(s, i) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    let n = s.nodes[i];
    let n2 = s2.nodes[i];
    assert(inv_node(p, s, i));
    assert forall |k: Id| #[trigger] s2.nodes.contains_key(k) implies inv_node(p, s2, k) by {
        assert(inv_node(p, s, k));
        if k == i {
            assert(s.store.written.contains_key(s.store.config.epoch));
        }
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_current_epoch(p, s2, k, o) by {
        assert(inv_entry_current_epoch(p, s, k, o));
        assert(inv_entry_old_epoch(p, s, k, o));
        assert(inv_node(p, s, k));
        if k == i {
            if n.read_any && n.epoch == s.store.config.epoch {
                // held unchanged; the entry condition is as before
            } else {
                // held is now the clock: no entry was filled after held + grace
                if n2.cache.contains_key(o) {
                    assert(n2.cache[o].filled_at <= n2.clock);
                    assert(n2.held == n2.clock);
                }
            }
        }
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_old_epoch(p, s2, k, o) by {
        assert(inv_entry_current_epoch(p, s, k, o));
        assert(inv_entry_old_epoch(p, s, k, o));
        assert(inv_node(p, s, k));
        if k == i {
            if n.read_any && n.epoch == s.store.config.epoch {
                // held unchanged; the entry condition is as before
            } else {
                // held is now the clock: no entry was filled after held + grace
                if n2.cache.contains_key(o) {
                    assert(n2.cache[o].filled_at <= n2.clock);
                    assert(n2.held == n2.clock);
                }
            }
        }
    }
    assert(inv_written(s2));
    assert(inv_members(s2));
    assemble(p, s2);
}

proof fn lemma_propose(p: Params, s: Cluster, s2: Cluster, i: Id, m: Seq<Id>)
    requires inv(p)(s), propose(s, i, m) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    let e = s.store.config.epoch + 1;
    assert(inv_written(s2)) by {
        assert forall |a: nat| a <= s2.store.config.epoch implies #[trigger] s2.store.written.contains_key(a) by {}
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
        if n.read_any {
            assert(s2.store.written[n.epoch] == s.store.written[n.epoch]);
            if n.epoch < s2.store.config.epoch {
                if n.epoch + 1 == e {
                    assert(s2.store.written[e] == s.now);
                } else {
                    assert(s2.store.written[n.epoch + 1] == s.store.written[n.epoch + 1]);
                }
            }
        }
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_current_epoch(p, s2, k, o) by {
        assert(inv_entry_current_epoch(p, s, k, o));
        assert(inv_entry_old_epoch(p, s, k, o));
        assert(inv_node(p, s, k));
        let n = s.nodes[k];
        assert(inv_node(p, s, k));
        // In the new epoch nobody holds it yet. In an old epoch: either it
        // was the current one, whose entries were current, or it was old
        // already.
    }
    assert forall |k: Id, o: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_old_epoch(p, s2, k, o) by {
        assert(inv_entry_current_epoch(p, s, k, o));
        assert(inv_entry_old_epoch(p, s, k, o));
        assert(inv_node(p, s, k));
        let n = s.nodes[k];
        assert(inv_node(p, s, k));
        // In the new epoch nobody holds it yet. In an old epoch: either it
        // was the current one, whose entries were current, or it was old
        // already.
    }
    assert(inv_written(s2));
    assert(inv_members(s2));
    assemble(p, s2);
}

proof fn lemma_read_store(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv(p)(s), read_store(s, i, o) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert forall |k: Id| #[trigger] s2.nodes.contains_key(k) implies inv_node(p, s2, k) by {
        assert(inv_node(p, s, k));
    }
    assert forall |k: Id, q: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_current_epoch(p, s2, k, q) by {
        assert(inv_entry_current_epoch(p, s, k, q));
        assert(inv_entry_old_epoch(p, s, k, q));
        assert(inv_node(p, s, k));
    }
    assert forall |k: Id, q: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_old_epoch(p, s2, k, q) by {
        assert(inv_entry_current_epoch(p, s, k, q));
        assert(inv_entry_old_epoch(p, s, k, q));
        assert(inv_node(p, s, k));
    }
    assert(inv_written(s2));
    assert(inv_members(s2));
    assemble(p, s2);
}

proof fn lemma_write(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv(p)(s), write(p, s, i, o) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    let w = s.nodes[i];
    assert(inv_node(p, s, i));
    assert forall |k: Id| #[trigger] s2.nodes.contains_key(k) implies inv_node(p, s2, k) by {
        assert(inv_node(p, s, k));
    }
    assert forall |k: Id, q: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_current_epoch(p, s2, k, q) by {
        assert(inv_entry_current_epoch(p, s, k, q));
        assert(inv_entry_old_epoch(p, s, k, q));
        assert(inv_node(p, s, k));
        assert(inv_node(p, s, k));
        let n = s.nodes[k];
        if q == o && k != i {
            // Another node's entry for the written origin: it cannot have
            // been filled by an owner in a live window, since the writer is
            // the owner now.
            if n.alive && n.read_any && owner(n.members, o) == Some(k) && n.cache.contains_key(o) && n.cache[o].filled_at >= n.held + p.grace {
                // n holds the epoch for the grace (its entry was filled after
                // held + grace, and filled_at <= clock)
                assert(n.held + p.grace <= n.clock);
                if n.epoch == s.store.config.epoch {
                    // same epoch as the writer: same members, one owner
                    assert(w.epoch == s.store.config.epoch || w.epoch < s.store.config.epoch);
                    if w.epoch == s.store.config.epoch {
                        assert(w.members == n.members);
                        assert(false);
                    } else {
                        // the writer is fresh in an older epoch; n holds the newer for the grace
                        timing(p, s, i, k);
                    }
                } else if fresh(p, n) {
                    // n fresh in an older epoch than the bucket's
                    if w.epoch == n.epoch {
                        assert(w.members == n.members);
                        assert(false);
                    } else if w.epoch < n.epoch {
                        timing(p, s, i, k);
                    } else {
                        timing(p, s, k, i);
                    }
                }
            }
        }
    }
    assert forall |k: Id, q: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_old_epoch(p, s2, k, q) by {
        assert(inv_entry_current_epoch(p, s, k, q));
        assert(inv_entry_old_epoch(p, s, k, q));
        assert(inv_node(p, s, k));
        assert(inv_node(p, s, k));
        let n = s.nodes[k];
        if q == o && k != i {
            // Another node's entry for the written origin: it cannot have
            // been filled by an owner in a live window, since the writer is
            // the owner now.
            if n.alive && n.read_any && owner(n.members, o) == Some(k) && n.cache.contains_key(o) && n.cache[o].filled_at >= n.held + p.grace {
                // n holds the epoch for the grace (its entry was filled after
                // held + grace, and filled_at <= clock)
                assert(n.held + p.grace <= n.clock);
                if n.epoch == s.store.config.epoch {
                    // same epoch as the writer: same members, one owner
                    assert(w.epoch == s.store.config.epoch || w.epoch < s.store.config.epoch);
                    if w.epoch == s.store.config.epoch {
                        assert(w.members == n.members);
                        assert(false);
                    } else {
                        // the writer is fresh in an older epoch; n holds the newer for the grace
                        timing(p, s, i, k);
                    }
                } else if fresh(p, n) {
                    // n fresh in an older epoch than the bucket's
                    if w.epoch == n.epoch {
                        assert(w.members == n.members);
                        assert(false);
                    } else if w.epoch < n.epoch {
                        timing(p, s, i, k);
                    } else {
                        timing(p, s, k, i);
                    }
                }
            }
        }
    }
    assert(inv_written(s2));
    assert(inv_members(s2));
    assemble(p, s2);
}

proof fn lemma_write_fail(p: Params, s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires inv(p)(s), write_fail(s, i, o) == Some(s2),
    ensures inv(p)(s2),
{
    disassemble(p, s);
    assert forall |k: Id| #[trigger] s2.nodes.contains_key(k) implies inv_node(p, s2, k) by {
        assert(inv_node(p, s, k));
    }
    assert forall |k: Id, q: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_current_epoch(p, s2, k, q) by {
        assert(inv_entry_current_epoch(p, s, k, q));
        assert(inv_entry_old_epoch(p, s, k, q));
        assert(inv_node(p, s, k));
    }
    assert forall |k: Id, q: Origin| #[trigger] s2.nodes.contains_key(k) implies #[trigger] inv_entry_old_epoch(p, s2, k, q) by {
        assert(inv_entry_current_epoch(p, s, k, q));
        assert(inv_entry_old_epoch(p, s, k, q));
        assert(inv_node(p, s, k));
    }
    assert(inv_written(s2));
    assert(inv_members(s2));
    assemble(p, s2);
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
        Step::ReadStore(i, o) => lemma_read_store(p, s, s2, i, o),
        Step::Write(i, o) => lemma_write(p, s, s2, i, o),
        Step::WriteFail(i, o) => lemma_write_fail(p, s, s2, i, o),
        Step::ReadCached(i, o) => {}
    }
}

// ---------------------------------------------------------------------------
// The theorem, in the temporal logic
// ---------------------------------------------------------------------------

/// Every execution that starts in `init` and steps by `next` satisfies the
/// invariant forever — and with it exclusion and currency.
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

/// The invariant is not vacuous: a fleet of one node, past the grace, acts
/// on and trusts its cache of an origin, and satisfies the invariant.
pub proof fn not_vacuous(p: Params, o: Origin)
    requires p.wf(),
    ensures exists |s: Cluster| #[trigger] inv(p)(s) && s.nodes.contains_key(1) && trusts(p, s.nodes[1], o),
{
    let now = p.grace;
    let n = Node {
        id: 1, alive: true, clock: now, read_any: true, epoch: 0, members: seq![1nat],
        last_read: now, held: 0, last_read_real: now, held_real: 0,
        cache: Map::empty().insert(o, Cached { version: 0, filled_at: now }),
    };
    let s = Cluster {
        now,
        nodes: Map::empty().insert(1, n),
        store: Store { docs: Map::empty(), config: Config { epoch: 0, members: seq![1nat] }, written: Map::empty().insert(0, 0) },
    };
    assert(owner(seq![1nat], o) == Some(1nat));
    assert(inv_node(p, s, 1));
    assert(inv_written(s));
    assert(inv_members(s));
    assert forall |i: Id| #[trigger] s.nodes.contains_key(i) implies inv_node(p, s, i) by {}
    assert forall |i: Id, q: Origin| #[trigger] s.nodes.contains_key(i) implies #[trigger] inv_entry_current_epoch(p, s, i, q) by {}
    assert forall |i: Id, q: Origin| #[trigger] s.nodes.contains_key(i) implies #[trigger] inv_entry_old_epoch(p, s, i, q) by {}
    assemble(p, s);
    assert(trusts(p, s.nodes[1], o));
}

} // verus!
