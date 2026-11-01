//! A row of `State`, read through the fold. The fold's own lemmas are
//! `echod_concrete::fold_proof`. These say the row at an index is the entry
//! at its key.

use vstd::prelude::*;

use crate::store::*;
use crate::types::*;

#[cfg(verus_keep_ghost)]
pub use echod_concrete::fold_proof::*;

verus! {

impl State {
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

} // verus!
