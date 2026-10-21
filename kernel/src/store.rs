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

use crate::store_proof::*;

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
#[cfg(verus_keep_ghost)]
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

#[cfg(verus_keep_ghost)]
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

    /// The row carrying `e`'s key, if any.
    pub fn find_outbox(&self, e: &OutboxEntry) -> (r: Option<usize>)
        ensures
            match r {
                Some(i) => i < self.outbox@.len() && self.outbox@[i as int]@.key() == e@.key(),
                None => !self@.outbox.contains_key(e@.key()),
            },
    {
        let mut i: usize = 0;
        while i < self.outbox.len()
            invariant
                i <= self.outbox@.len(),
                forall|j: int| 0 <= j < i ==> self.outbox@[j]@.key() != e@.key(),
            decreases self.outbox@.len() - i,
        {
            if same_key(&self.outbox[i], e) {
                return Some(i);
            }
            i += 1;
        }
        proof {
            lemma_fold_dom(self.outbox@, out_key(), out_val());
            assert forall|j: int| 0 <= j < self.outbox@.len() implies #[trigger] out_key()(self.outbox@[j]) != e@.key() by {}
        }
        None
    }

    /// `setMessage`: one entry per key, the newest winning.
    pub fn upsert_outbox(&mut self, e: OutboxEntry)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).objects == old(self).objects,
            final(self).schedules == old(self).schedules,
            final(self)@.objects == old(self)@.objects,
            final(self)@.schedules == old(self)@.schedules,
            final(self)@.outbox =~= old(self)@.outbox.insert(e@.key(), e@),
    {
        match self.find_outbox(&e) {
            Some(i) => {
                proof {
                    lemma_fold_update(self.outbox@, out_key(), out_val(), i as int, e);
                }
                self.outbox[i] = e;
            }
            None => {
                proof {
                    let s = self.outbox@;
                    lemma_fold_dom(s, out_key(), out_val());
                    lemma_fold_push(s, out_key(), out_val(), e);
                    let t = s.push(e);
                    assert forall|a: int, b: int|
                        0 <= a < t.len() && 0 <= b < t.len() && #[trigger] out_key()(t[a]) == #[trigger] out_key()(t[b])
                        implies a == b by {
                        if a == s.len() && b < s.len() {
                            assert(out_key()(s[b]) == e@.key());
                            assert(mentions(s, out_key(), e@.key()));
                        }
                        if b == s.len() && a < s.len() {
                            assert(out_key()(s[a]) == e@.key());
                            assert(mentions(s, out_key(), e@.key()));
                        }
                    }
                }
                self.outbox.push(e);
            }
        }
    }

    /// Hand the outbox to the caller, emptying it. The abstract outbox is what
    /// the catalogue constrains; the server delivers it and starts afresh.
    pub fn take_outbox(&mut self) -> (r: Vec<OutboxEntry>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).objects == old(self).objects,
            final(self).schedules == old(self).schedules,
            r == old(self).outbox,
            final(self).outbox@ == Seq::<OutboxEntry>::empty(),
    {
        let mut out: Vec<OutboxEntry> = Vec::new();
        core::mem::swap(&mut out, &mut self.outbox);
        proof {
            assert forall|a: int, b: int|
                0 <= a < self.outbox@.len() && 0 <= b < self.outbox@.len()
                && #[trigger] out_key()(self.outbox@[a]) == #[trigger] out_key()(self.outbox@[b])
                implies a == b by {}
        }
        out
    }
}

/// Do two entries share a key?
pub fn same_key(x: &OutboxEntry, y: &OutboxEntry) -> (r: bool)
    ensures r == (x@.key() == y@.key()),
{
    match (&x.message, &y.message) {
        (Message::Execute { task_id: a, .. }, Message::Execute { task_id: b, .. }) => *a == *b,
        (Message::Unblock(ra), Message::Unblock(rb)) => ra.id == rb.id && x.address == y.address,
        _ => false,
    }
}

} // verus!
