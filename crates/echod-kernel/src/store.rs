//! The store: rows in a vector, a map in the specification.
//!
//! The object at `wf/<origin>` is a log of rows; the document is the fold of
//! the rows by id, last row winning. Here the fold is `fold_by`, generic in
//! the key, and the kernel's state is three row vectors whose abstract view is
//! three maps. The lemmas tie a vector operation to a map operation:
//!
//! - a row found at index `i` is the map's entry at its key;
//! - replacing the row at `i` is `insert` at its key;
//! - pushing a row with a fresh key is `insert` at its key.

use vstd::prelude::*;

use crate::types::*;

verus! {

// ---------------------------------------------------------------------------
// The fold
// ---------------------------------------------------------------------------

/// Replay rows: each row replaces the entry at its key.
pub open spec fn fold_by<T, K, V>(s: Seq<T>, key: spec_fn(T) -> K, val: spec_fn(T) -> V) -> Map<K, V>
    decreases s.len(),
{
    if s.len() == 0 {
        Map::empty()
    } else {
        fold_by(s.drop_last(), key, val).insert(key(s.last()), val(s.last()))
    }
}

/// Some row carries key `k`.
pub open spec fn mentions<T, K>(s: Seq<T>, key: spec_fn(T) -> K, k: K) -> bool {
    exists|i: int| 0 <= i < s.len() && #[trigger] key(s[i]) == k
}

/// No two rows share a key.
pub open spec fn distinct_by<T, K>(s: Seq<T>, key: spec_fn(T) -> K) -> bool {
    forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && #[trigger] key(s[i]) == #[trigger] key(s[j]) ==> i == j
}

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

// ---------------------------------------------------------------------------
// The state
// ---------------------------------------------------------------------------

/// Everything the machine reads and writes: objects, schedules, outbox.
pub struct State {
    pub objects: Vec<Promise>,
    pub schedules: Vec<Schedule>,
    pub outbox: Vec<OutboxEntry>,
}

/// The state as the specification sees it.
pub struct AState {
    pub objects: Map<Seq<char>, APromise>,
    pub schedules: Map<Seq<char>, ASchedule>,
    pub outbox: Map<OutboxKey, AOutboxEntry>,
}

pub open spec fn obj_key() -> spec_fn(Promise) -> Seq<char> {
    |p: Promise| p.id@
}
pub open spec fn obj_val() -> spec_fn(Promise) -> APromise {
    |p: Promise| p@
}
pub open spec fn sched_key() -> spec_fn(Schedule) -> Seq<char> {
    |c: Schedule| c.id@
}
pub open spec fn sched_val() -> spec_fn(Schedule) -> ASchedule {
    |c: Schedule| c@
}
pub open spec fn out_key() -> spec_fn(OutboxEntry) -> OutboxKey {
    |e: OutboxEntry| e@.key()
}
pub open spec fn out_val() -> spec_fn(OutboxEntry) -> AOutboxEntry {
    |e: OutboxEntry| e@
}

impl View for State {
    type V = AState;
    open spec fn view(&self) -> AState {
        AState {
            objects: fold_by(self.objects@, obj_key(), obj_val()),
            schedules: fold_by(self.schedules@, sched_key(), sched_val()),
            outbox: fold_by(self.outbox@, out_key(), out_val()),
        }
    }
}

impl State {
    /// Rows carry distinct keys. The fold is then a bijection with the rows,
    /// and every row is the entry at its key.
    pub open spec fn wf(self) -> bool {
        &&& distinct_by(self.objects@, obj_key())
        &&& distinct_by(self.schedules@, sched_key())
        &&& distinct_by(self.outbox@, out_key())
    }

    pub fn new() -> (s: State)
        ensures
            s.wf(),
            s@.objects =~= Map::empty(),
            s@.schedules =~= Map::empty(),
            s@.outbox =~= Map::empty(),
    {
        State { objects: Vec::new(), schedules: Vec::new(), outbox: Vec::new() }
    }

    // --- objects ---

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

    /// Find the row carrying `id`.
    pub fn find_object(&self, id: &String) -> (r: Option<usize>)
        ensures
            match r {
                Some(i) => i < self.objects@.len() && self.objects@[i as int].id@ == id@,
                None => !self@.objects.contains_key(id@),
            },
    {
        let mut i: usize = 0;
        while i < self.objects.len()
            invariant
                i <= self.objects@.len(),
                forall|j: int| 0 <= j < i ==> self.objects@[j].id@ != id@,
            decreases self.objects@.len() - i,
        {
            if self.objects[i].id == *id {
                return Some(i);
            }
            i += 1;
        }
        proof {
            self.lemma_object_dom(id@);
            assert forall|j: int| 0 <= j < self.objects@.len() implies #[trigger] obj_key()(self.objects@[j]) != id@ by {}
        }
        None
    }

    /// Replace the row at `i` by `p`, which carries the same id.
    pub fn set_object(&mut self, i: usize, p: Promise)
        requires
            old(self).wf(),
            i < old(self).objects@.len(),
            old(self).objects@[i as int].id@ == p.id@,
        ensures
            final(self).wf(),
            final(self).objects@ == old(self).objects@.update(i as int, p),
            final(self).schedules == old(self).schedules,
            final(self).outbox == old(self).outbox,
            final(self)@.objects =~= old(self)@.objects.insert(p.id@, p@),
            final(self)@.schedules == old(self)@.schedules,
            final(self)@.outbox == old(self)@.outbox,
    {
        proof {
            lemma_fold_update(self.objects@, obj_key(), obj_val(), i as int, p);
        }
        self.objects[i] = p;
    }

    /// Add a row whose id no row carries.
    pub fn push_object(&mut self, p: Promise)
        requires
            old(self).wf(),
            !old(self)@.objects.contains_key(p.id@),
        ensures
            final(self).wf(),
            final(self).objects@ == old(self).objects@.push(p),
            final(self).schedules == old(self).schedules,
            final(self).outbox == old(self).outbox,
            final(self)@.objects == old(self)@.objects.insert(p.id@, p@),
            final(self)@.schedules == old(self)@.schedules,
            final(self)@.outbox == old(self)@.outbox,
    {
        proof {
            let s = self.objects@;
            self.lemma_object_dom(p.id@);
            lemma_fold_push(s, obj_key(), obj_val(), p);
            let t = s.push(p);
            assert forall|a: int, b: int|
                0 <= a < t.len() && 0 <= b < t.len() && #[trigger] obj_key()(t[a]) == #[trigger] obj_key()(t[b])
                implies a == b by {
                if a == s.len() && b < s.len() {
                    assert(obj_key()(s[b]) == p.id@);
                    assert(mentions(s, obj_key(), p.id@));
                }
                if b == s.len() && a < s.len() {
                    assert(obj_key()(s[a]) == p.id@);
                    assert(mentions(s, obj_key(), p.id@));
                }
            }
        }
        self.objects.push(p);
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

    pub fn find_schedule(&self, id: &String) -> (r: Option<usize>)
        ensures
            match r {
                Some(i) => i < self.schedules@.len() && self.schedules@[i as int].id@ == id@,
                None => !self@.schedules.contains_key(id@),
            },
    {
        let mut i: usize = 0;
        while i < self.schedules.len()
            invariant
                i <= self.schedules@.len(),
                forall|j: int| 0 <= j < i ==> self.schedules@[j].id@ != id@,
            decreases self.schedules@.len() - i,
        {
            if self.schedules[i].id == *id {
                return Some(i);
            }
            i += 1;
        }
        proof {
            self.lemma_schedule_dom(id@);
            assert forall|j: int| 0 <= j < self.schedules@.len() implies #[trigger] sched_key()(self.schedules@[j]) != id@ by {}
        }
        None
    }

    pub fn set_schedule(&mut self, i: usize, c: Schedule)
        requires
            old(self).wf(),
            i < old(self).schedules@.len(),
            old(self).schedules@[i as int].id@ == c.id@,
        ensures
            final(self).wf(),
            final(self).objects == old(self).objects,
            final(self).outbox == old(self).outbox,
            final(self)@.objects == old(self)@.objects,
            final(self)@.schedules =~= old(self)@.schedules.insert(c.id@, c@),
            final(self)@.outbox == old(self)@.outbox,
    {
        proof {
            lemma_fold_update(self.schedules@, sched_key(), sched_val(), i as int, c);
        }
        self.schedules[i] = c;
    }

    pub fn push_schedule(&mut self, c: Schedule)
        requires
            old(self).wf(),
            !old(self)@.schedules.contains_key(c.id@),
        ensures
            final(self).wf(),
            final(self).objects == old(self).objects,
            final(self).outbox == old(self).outbox,
            final(self)@.objects == old(self)@.objects,
            final(self)@.schedules == old(self)@.schedules.insert(c.id@, c@),
            final(self)@.outbox == old(self)@.outbox,
    {
        proof {
            let s = self.schedules@;
            self.lemma_schedule_dom(c.id@);
            lemma_fold_push(s, sched_key(), sched_val(), c);
            let t = s.push(c);
            assert forall|a: int, b: int|
                0 <= a < t.len() && 0 <= b < t.len() && #[trigger] sched_key()(t[a]) == #[trigger] sched_key()(t[b])
                implies a == b by {
                if a == s.len() && b < s.len() {
                    assert(sched_key()(s[b]) == c.id@);
                    assert(mentions(s, sched_key(), c.id@));
                }
                if b == s.len() && a < s.len() {
                    assert(sched_key()(s[a]) == c.id@);
                    assert(mentions(s, sched_key(), c.id@));
                }
            }
        }
        self.schedules.push(c);
    }

    /// Remove the schedule row at `i`.
    pub fn remove_schedule(&mut self, i: usize)
        requires
            old(self).wf(),
            i < old(self).schedules@.len(),
        ensures
            final(self).wf(),
            final(self).objects == old(self).objects,
            final(self).outbox == old(self).outbox,
            final(self)@.objects == old(self)@.objects,
            final(self)@.schedules =~= old(self)@.schedules.remove(old(self).schedules@[i as int].id@),
            final(self)@.outbox == old(self)@.outbox,
    {
        proof {
            lemma_fold_remove(self.schedules@, sched_key(), sched_val(), i as int);
        }
        self.schedules.remove(i);
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
