//! The proofs of tags: what `get` returns at a match and at none. Nothing
//! here is executed.

use vstd::prelude::*;

use crate::types::str_eq;
use crate::tags::*;
use crate::types::{ATags, Tags};

verus! {

// ---------------------------------------------------------------------------
// The recursive definition, as an index
// ---------------------------------------------------------------------------

/// If `i` is the first index whose key is `k`, `tags_get` returns its value.
pub proof fn lemma_tags_get_at(t: ATags, k: Seq<char>, i: int)
    requires
        0 <= i < t.len(),
        t[i].0 == k,
        forall|j: int| 0 <= j < i ==> t[j].0 != k,
    ensures
        tags_get(t, k) == Some(t[i].1),
    decreases i,
{
    if i == 0 {
    } else {
        assert(t[0].0 != k);
        let r = t.drop_first();
        assert(r[i - 1] == t[i]);
        assert forall|j: int| 0 <= j < i - 1 implies r[j].0 != k by {
            assert(r[j] == t[j + 1]);
        }
        lemma_tags_get_at(r, k, i - 1);
    }
}

/// If no key is `k`, `tags_get` returns `None`.
pub proof fn lemma_tags_get_none(t: ATags, k: Seq<char>)
    requires
        forall|j: int| 0 <= j < t.len() ==> t[j].0 != k,
    ensures
        tags_get(t, k) is None,
    decreases t.len(),
{
    if t.len() == 0 {
    } else {
        let r = t.drop_first();
        assert forall|j: int| 0 <= j < r.len() implies r[j].0 != k by {
            assert(r[j] == t[j + 1]);
        }
        lemma_tags_get_none(r, k);
    }
}

// ---------------------------------------------------------------------------
// Stamping
// ---------------------------------------------------------------------------

/// Stripping commutes with a push.
pub proof fn lemma_strip_push(t: ATags, x: (Seq<char>, Seq<char>))
    ensures
        strip(t.push(x)) == if stamped_key(x.0) { strip(t) } else { strip(t).push(x) },
    decreases t.len(),
{
    let u = t.push(x);
    if t.len() == 0 {
        assert(u.drop_first() =~= Seq::<(Seq<char>, Seq<char>)>::empty());
        assert(strip(u.drop_first()) =~= Seq::<(Seq<char>, Seq<char>)>::empty());
        if !stamped_key(x.0) {
            assert(strip(u) =~= strip(t).push(x));
        }
    } else {
        assert(u[0] == t[0]);
        assert(u.drop_first() =~= t.drop_first().push(x));
        lemma_strip_push(t.drop_first(), x);
        if !stamped_key(t[0].0) && !stamped_key(x.0) {
            assert(strip(u) =~= strip(t).push(x));
        }
    }
}

/// `get` on an append: the first list answers if it can.
pub proof fn lemma_tags_get_append(a: ATags, b: ATags, k: Seq<char>)
    ensures
        tags_get(a + b, k) == if tags_has(a, k) { tags_get(a, k) } else { tags_get(b, k) },
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_tags_get_append(a.drop_first(), b, k);
    }
}

/// Stripping leaves every key it does not strip where it was.
pub proof fn lemma_strip_get(t: ATags, k: Seq<char>)
    requires !stamped_key(k),
    ensures tags_get(strip(t), k) == tags_get(t, k),
    decreases t.len(),
{
    if t.len() == 0 {
    } else {
        lemma_strip_get(t.drop_first(), k);
        if stamped_key(t[0].0) {
            assert(t[0].0 != k);
        } else {
            let u = seq![t[0]] + strip(t.drop_first());
            assert(u[0] == t[0]);
            assert(u.drop_first() =~= strip(t.drop_first()));
        }
    }
}

/// The stamp carries none of the keys it does not set.
pub proof fn lemma_lineage_get(sid: Seq<char>, pid: Seq<char>, k: Seq<char>)
    requires !stamped_key(k),
    ensures tags_get(lineage(sid, pid), k) is None,
{
    let l = lineage(sid, pid);
    assert(l[0].0 == "resonate:schedule"@);
    assert(l[1].0 == "resonate:origin"@);
    assert(l[2].0 == "resonate:branch"@);
    assert(l[3].0 == "resonate:parent"@);
    assert(l[4].0 == "resonate:prefix"@);
    assert forall|j: int| 0 <= j < l.len() implies l[j].0 != k by {
        assert(j == 0 || j == 1 || j == 2 || j == 3 || j == 4);
    }
    lemma_tags_get_none(l, k);
}

/// A key the stamp does not set reads the same off the stamped tags.
pub proof fn lemma_stamp_get(t: ATags, sid: Seq<char>, pid: Seq<char>, k: Seq<char>)
    requires !stamped_key(k),
    ensures tags_get(spec_stamp(t, sid, pid), k) == tags_get(t, k),
{
    lemma_tags_get_append(strip(t), lineage(sid, pid), k);
    lemma_strip_get(t, k);
    lemma_lineage_get(sid, pid, k);
}

/// The stamp neither makes a timer nor gives one a target.
pub proof fn lemma_stamp_timer(t: ATags, sid: Seq<char>, pid: Seq<char>)
    ensures
        timer_targeted(spec_stamp(t, sid, pid)) == timer_targeted(t),
        otype(spec_stamp(t, sid, pid)) == otype(t),
{
    assert(!stamped_key("resonate:timer"@) && !stamped_key("resonate:target"@) && !stamped_key("resonate:scope"@) && !stamped_key("resonate:external"@)) by {
        reveal_strlit("resonate:timer");
        reveal_strlit("resonate:target");
        reveal_strlit("resonate:scope");
        reveal_strlit("resonate:external");
        reveal_strlit("resonate:schedule");
        reveal_strlit("resonate:origin");
        reveal_strlit("resonate:branch");
        reveal_strlit("resonate:parent");
        reveal_strlit("resonate:prefix");
    }
    lemma_stamp_get(t, sid, pid, "resonate:timer"@);
    lemma_stamp_get(t, sid, pid, "resonate:target"@);
    lemma_stamp_get(t, sid, pid, "resonate:scope"@);
    lemma_stamp_get(t, sid, pid, "resonate:external"@);
}

} // verus!
