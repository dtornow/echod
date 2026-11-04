//! The fold: what a log of rows is as a map.
//!
//! Pushing, replacing and removing a row are `insert` and `remove` on
//! `fold_by`. A compaction, rows rewritten one per id in any order, folds
//! to the same document. The kernel's `State` methods are proved by these.

use vstd::prelude::*;

use crate::state::*;

verus! {

/// The fold's domain is exactly the keys the rows carry.
pub proof fn lemma_fold_dom<T, K, V>(s: Seq<T>, key: spec_fn(T) -> K, val: spec_fn(T) -> V)
    ensures
        forall|k: K| #[trigger] fold_by(s, key, val).contains_key(k) <==> mentions(s, key, k),
    decreases s.len(),
{
    if s.len() == 0 {
        assert forall|k: K| !mentions(s, key, k) by {
            if mentions(s, key, k) {
                let i = choose|i: int| 0 <= i < s.len() && #[trigger] key(s[i]) == k;
            }
        }
    } else {
        let init = s.drop_last();
        lemma_fold_dom(init, key, val);
        assert forall|k: K| #[trigger] fold_by(s, key, val).contains_key(k) implies mentions(s, key, k) by {
            if k == key(s.last()) {
                assert(key(s[s.len() - 1]) == k);
            } else {
                assert(fold_by(init, key, val).contains_key(k));
                assert(mentions(init, key, k));
                let i = choose|i: int| 0 <= i < init.len() && #[trigger] key(init[i]) == k;
                assert(s[i] == init[i]);
                assert(key(s[i]) == k);
            }
        }
        assert forall|k: K| mentions(s, key, k) implies #[trigger] fold_by(s, key, val).contains_key(k) by {
            let i = choose|i: int| 0 <= i < s.len() && #[trigger] key(s[i]) == k;
            if i == s.len() - 1 {
            } else {
                assert(init[i] == s[i]);
                assert(key(init[i]) == k);
                assert(mentions(init, key, k));
                assert(fold_by(init, key, val).contains_key(k));
            }
        }
    }
}

/// With distinct keys, the fold holds every row's value under its key.
pub proof fn lemma_fold_distinct<T, K, V>(s: Seq<T>, key: spec_fn(T) -> K, val: spec_fn(T) -> V)
    requires
        distinct_by(s, key),
    ensures
        forall|i: int| 0 <= i < s.len()
            ==> fold_by(s, key, val).contains_key(#[trigger] key(s[i]))
                && fold_by(s, key, val)[key(s[i])] == val(s[i]),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let init = s.drop_last();
        let last = s.last();
        assert forall|i: int, j: int|
            0 <= i < init.len() && 0 <= j < init.len() && #[trigger] key(init[i]) == #[trigger] key(init[j])
            implies i == j by {
            assert(init[i] == s[i]);
            assert(init[j] == s[j]);
        }
        lemma_fold_distinct(init, key, val);
        assert forall|i: int| 0 <= i < s.len()
            implies fold_by(s, key, val).contains_key(#[trigger] key(s[i]))
                && fold_by(s, key, val)[key(s[i])] == val(s[i]) by {
            if i == s.len() - 1 {
            } else {
                assert(key(s[i]) != key(last));
                assert(init[i] == s[i]);
            }
        }
    }
}

/// `c` is a compaction of `s`: rows with distinct keys, one for each key of
/// `s`'s fold, each carrying the value the fold holds there. Row order is
/// unconstrained.
pub open spec fn is_compaction<T, K, V>(c: Seq<T>, s: Seq<T>, key: spec_fn(T) -> K, val: spec_fn(T) -> V) -> bool {
    &&& distinct_by(c, key)
    &&& forall|i: int| 0 <= i < c.len()
        ==> fold_by(s, key, val).contains_key(#[trigger] key(c[i])) && val(c[i]) == fold_by(s, key, val)[key(c[i])]
    &&& forall|k: K| #[trigger] fold_by(s, key, val).contains_key(k) ==> mentions(c, key, k)
}

/// Compaction replays to the same document: a compaction of a log folds to
/// what the log folds to. The object at `wf/<origin>` is a log of rows, and
/// a rewrite as one row per id, in any order, reads back the same.
pub proof fn compaction_replays_to_the_same_document<T, K, V>(c: Seq<T>, s: Seq<T>, key: spec_fn(T) -> K, val: spec_fn(T) -> V)
    requires
        is_compaction(c, s, key, val),
    ensures
        fold_by(c, key, val) == fold_by(s, key, val),
{
    lemma_fold_dom(c, key, val);
    lemma_fold_distinct(c, key, val);
    assert forall|k: K| #[trigger] fold_by(c, key, val).contains_key(k) implies fold_by(s, key, val).contains_key(k) by {
        let i = choose|i: int| 0 <= i < c.len() && #[trigger] key(c[i]) == k;
    }
    assert forall|k: K| #[trigger] fold_by(s, key, val).contains_key(k) implies fold_by(c, key, val).contains_key(k) by {
        let i = choose|i: int| 0 <= i < c.len() && #[trigger] key(c[i]) == k;
    }
    assert forall|k: K| #[trigger] fold_by(c, key, val).contains_key(k) implies fold_by(c, key, val)[k] == fold_by(s, key, val)[k] by {
        let i = choose|i: int| 0 <= i < c.len() && #[trigger] key(c[i]) == k;
    }
    assert(fold_by(c, key, val) =~= fold_by(s, key, val));
}

/// Pushing a row is inserting at its key.
pub proof fn lemma_fold_push<T, K, V>(s: Seq<T>, key: spec_fn(T) -> K, val: spec_fn(T) -> V, p: T)
    ensures
        fold_by(s.push(p), key, val) == fold_by(s, key, val).insert(key(p), val(p)),
{
    assert(s.push(p).drop_last() =~= s);
    assert(s.push(p).last() == p);
}

/// Replacing the row at `i` by one with the same key is inserting at that key.
pub proof fn lemma_fold_update<T, K, V>(s: Seq<T>, key: spec_fn(T) -> K, val: spec_fn(T) -> V, i: int, p: T)
    requires
        distinct_by(s, key),
        0 <= i < s.len(),
        key(s[i]) == key(p),
    ensures
        distinct_by(s.update(i, p), key),
        fold_by(s.update(i, p), key, val) =~= fold_by(s, key, val).insert(key(p), val(p)),
{
    let t = s.update(i, p);
    assert forall|a: int, b: int|
        0 <= a < t.len() && 0 <= b < t.len() && #[trigger] key(t[a]) == #[trigger] key(t[b])
        implies a == b by {
        assert(key(t[a]) == key(s[a]));
        assert(key(t[b]) == key(s[b]));
    }
    lemma_fold_dom(s, key, val);
    lemma_fold_dom(t, key, val);
    lemma_fold_distinct(s, key, val);
    lemma_fold_distinct(t, key, val);
    let m = fold_by(s, key, val).insert(key(p), val(p));
    let n = fold_by(t, key, val);
    assert forall|k: K| #[trigger] n.contains_key(k) implies m.contains_key(k) by {
        let j = choose|j: int| 0 <= j < t.len() && #[trigger] key(t[j]) == k;
        assert(key(s[j]) == k);
    }
    assert forall|k: K| #[trigger] m.contains_key(k) implies n.contains_key(k) by {
        if k == key(p) {
            assert(key(t[i]) == k);
        } else {
            let j = choose|j: int| 0 <= j < s.len() && #[trigger] key(s[j]) == k;
            assert(key(t[j]) == k);
        }
    }
    assert forall|k: K| #[trigger] n.contains_key(k) implies n[k] == m[k] by {
        let j = choose|j: int| 0 <= j < t.len() && #[trigger] key(t[j]) == k;
        if j == i {
        } else {
            assert(t[j] == s[j]);
            assert(key(s[j]) == k);
            assert(k != key(p));
        }
    }
}

/// Removing the row at `i` is removing its key.
pub proof fn lemma_fold_remove<T, K, V>(s: Seq<T>, key: spec_fn(T) -> K, val: spec_fn(T) -> V, i: int)
    requires
        distinct_by(s, key),
        0 <= i < s.len(),
    ensures
        distinct_by(s.remove(i), key),
        fold_by(s.remove(i), key, val) =~= fold_by(s, key, val).remove(key(s[i])),
{
    let t = s.remove(i);
    assert forall|a: int, b: int|
        0 <= a < t.len() && 0 <= b < t.len() && #[trigger] key(t[a]) == #[trigger] key(t[b])
        implies a == b by {
        let a0 = if a < i { a } else { a + 1 };
        let b0 = if b < i { b } else { b + 1 };
        assert(t[a] == s[a0]);
        assert(t[b] == s[b0]);
    }
    lemma_fold_dom(s, key, val);
    lemma_fold_dom(t, key, val);
    lemma_fold_distinct(s, key, val);
    lemma_fold_distinct(t, key, val);
    let m = fold_by(s, key, val).remove(key(s[i]));
    let n = fold_by(t, key, val);
    assert forall|k: K| #[trigger] n.contains_key(k) implies m.contains_key(k) by {
        let j = choose|j: int| 0 <= j < t.len() && #[trigger] key(t[j]) == k;
        let j0 = if j < i { j } else { j + 1 };
        assert(t[j] == s[j0]);
        assert(key(s[j0]) == k);
        assert(j0 != i);
    }
    assert forall|k: K| #[trigger] m.contains_key(k) implies n.contains_key(k) by {
        let j = choose|j: int| 0 <= j < s.len() && #[trigger] key(s[j]) == k;
        assert(j != i);
        let j0 = if j < i { j } else { j - 1 };
        assert(t[j0] == s[j]);
        assert(key(t[j0]) == k);
    }
    assert forall|k: K| #[trigger] n.contains_key(k) implies n[k] == m[k] by {
        let j = choose|j: int| 0 <= j < t.len() && #[trigger] key(t[j]) == k;
        let j0 = if j < i { j } else { j + 1 };
        assert(t[j] == s[j0]);
        assert(key(s[j0]) == k);
    }
}

} // verus!
