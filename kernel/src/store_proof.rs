//! The proofs of the store: the fold lemmas, generic in the row, and the
//! lemmas that read a row of the state at an index or an id through the fold.
//! Nothing here is executed.

use vstd::prelude::*;

use crate::store::*;
use crate::types::*;

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

/// Replacing an object row by another carrying the same id preserves the
/// executable object order.
pub proof fn lemma_object_ids_update(s: Seq<Promise>, i: int, p: Promise)
    requires
        0 <= i < s.len(),
        s[i].id@ == p.id@,
    ensures
        s.update(i, p).map_values(|q: Promise| q.id@)
            == s.map_values(|q: Promise| q.id@),
{
    let t = s.update(i, p);
    assert(t.len() == s.len());
    assert forall|j: int| 0 <= j < t.len()
        implies #[trigger] t[j].id@ == s[j].id@ by {
        if j != i {
            assert(t[j] == s[j]);
        }
    }
    assert(t.map_values(|q: Promise| q.id@)
        =~= s.map_values(|q: Promise| q.id@));
}

/// Replacing an outbox row by another carrying the same key preserves its
/// executable position.
pub proof fn lemma_outbox_keys_update(
    s: Seq<OutboxEntry>,
    i: int,
    e: OutboxEntry,
)
    requires
        0 <= i < s.len(),
        s[i]@.key() == e@.key(),
    ensures
        s.update(i, e).map_values(|q: OutboxEntry| q@.key())
            == s.map_values(|q: OutboxEntry| q@.key()),
{
    let t = s.update(i, e);
    assert(t.len() == s.len());
    assert forall|j: int| 0 <= j < t.len()
        implies #[trigger] t[j]@.key() == s[j]@.key() by {
        if j != i {
            assert(t[j] == s[j]);
        }
    }
    assert(t.map_values(|q: OutboxEntry| q@.key())
        =~= s.map_values(|q: OutboxEntry| q@.key()));
}

impl State {
    // --- objects ---

    /// The row vector itself supplies a sound order witness for its folded
    /// object map.  In particular, this does not identify that order with
    /// `Map::dom().to_seq()`, whose order is unspecified.
    pub proof fn lemma_object_order(self)
        requires
            self.wf(),
        ensures
            object_order(self@, object_ids(self)),
    {
        lemma_fold_dom(self.objects@, obj_key(), obj_val());
        assert(object_ids(self).no_duplicates()) by {
            assert forall|i: int, j: int|
                0 <= i < object_ids(self).len()
                && 0 <= j < object_ids(self).len()
                && object_ids(self)[i] == object_ids(self)[j]
                implies i == j by {
                assert(object_ids(self)[i] == obj_key()(self.objects@[i]));
                assert(object_ids(self)[j] == obj_key()(self.objects@[j]));
            }
        }
        assert forall|i: int| 0 <= i < object_ids(self).len()
            implies self@.objects.contains_key(#[trigger] object_ids(self)[i]) by {
            assert(mentions(self.objects@, obj_key(), object_ids(self)[i])) by {
                assert(obj_key()(self.objects@[i]) == object_ids(self)[i]);
            }
        }
        assert forall|id: Seq<char>| #[trigger] self@.objects.contains_key(id)
            implies object_ids(self).contains(id) by {
            let i = choose|i: int| 0 <= i < self.objects@.len()
                && #[trigger] obj_key()(self.objects@[i]) == id;
            assert(object_ids(self)[i] == id);
        }
    }

    /// The row at `i` is the entry at its id.
    pub proof fn lemma_object_at(self, i: int)
        requires
            self.wf(),
            0 <= i < self.objects@.len(),
        ensures
            self@.objects.contains_key(self.objects@[i].id@),
            self@.objects[self.objects@[i].id@] == self.objects@[i]@,
    {
        lemma_fold_distinct(self.objects@, obj_key(), obj_val());
        assert(obj_key()(self.objects@[i]) == self.objects@[i].id@);
    }

    /// An id is in the map iff a row carries it.
    pub proof fn lemma_object_dom(self, id: Seq<char>)
        ensures
            self@.objects.contains_key(id) <==> mentions(self.objects@, obj_key(), id),
    {
        lemma_fold_dom(self.objects@, obj_key(), obj_val());
    }

    // --- schedules ---

    pub proof fn lemma_schedule_at(self, i: int)
        requires
            self.wf(),
            0 <= i < self.schedules@.len(),
        ensures
            self@.schedules.contains_key(self.schedules@[i].id@),
            self@.schedules[self.schedules@[i].id@] == self.schedules@[i]@,
    {
        lemma_fold_distinct(self.schedules@, sched_key(), sched_val());
        assert(sched_key()(self.schedules@[i]) == self.schedules@[i].id@);
    }

    pub proof fn lemma_schedule_dom(self, id: Seq<char>)
        ensures
            self@.schedules.contains_key(id) <==> mentions(self.schedules@, sched_key(), id),
    {
        lemma_fold_dom(self.schedules@, sched_key(), sched_val());
    }

    // --- outbox ---

    pub proof fn lemma_outbox_at(self, i: int)
        requires
            self.wf(),
            0 <= i < self.outbox@.len(),
        ensures
            self@.outbox.contains_key(self.outbox@[i]@.key()),
            self@.outbox[self.outbox@[i]@.key()] == self.outbox@[i]@,
    {
        lemma_fold_distinct(self.outbox@, out_key(), out_val());
        assert(out_key()(self.outbox@[i]) == self.outbox@[i]@.key());
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
