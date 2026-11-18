//! One schedule: create, read, delete, and a run coming due.
//!
//! A run is two commits. The concrete model's `run_due` on the schedule's
//! document says which occurrence is due and advances the schedule; the
//! occurrence is a promise in its origin, `create_occurrence`, committed
//! there first; then the advanced schedule is committed and the key that
//! fired it is deleted. The schedule holds its own slot the whole time and
//! takes the origin's slot for the first commit.

use vstd::prelude::*;

use crate::verified::runtime::copy;
use crate::concrete::DocumentBody;

use crate::verified::flight::{self, Decided, Job};
use crate::verified::text::{copy_string, text};

use crate::document::{self, Loaded};
use crate::handler_docs::{copy_fired, FireCtx, Flight, Phase, Progress, Queued, Work, Working};
use crate::keys::origin_of;
use crate::state::State;
use crate::target::Target;
use crate::types::*;

#[cfg(verus_keep_ghost)]
use crate::handler_docs::*;
#[cfg(verus_keep_ghost)]
use crate::keys::*;
#[cfg(verus_keep_ghost)]
use crate::state::*;
#[cfg(verus_keep_ghost)]
use crate::verified::flight_spec::*;
#[cfg(verus_keep_ghost)]
use crate::concrete::document::{pend_v, spec_body_deadline, DocumentBodyV};

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_handler_sched_spec_loaded_schedule as spec_loaded_schedule,
    production_handler_sched_spec_run_schedule as spec_run_schedule,
    production_handler_sched_spec_schedule_row as spec_schedule_row,
    production_handler_sched_spec_fire_decide as spec_fire_decide,
    production_handler_sched_spec_fire_idle as spec_fire_idle,
    production_handler_sched_spec_fire_claim as spec_fire_claim,
    production_handler_sched_spec_fire_load_origin as spec_fire_load_origin,
    production_handler_sched_spec_fire_run as spec_fire_run,
    production_handler_sched_spec_fire_advance as spec_fire_advance,
};

verus! {

/// The store answered a load of schedule `id`, read in full: not cached.




/// The schedule's row, if the document holds one.


/// The schedule is loaded: its due occurrence, if any, as a promise in the
/// occurrence's origin, then the schedule advanced, each its own commit, in
/// that order. A schedule not due, or gone, is rewritten unchanged so the
/// key can be collected behind the write.


/// Nothing due: a sweep of the schedule's document, rewritten unchanged.


/// The origin's slot, now or when it frees.




/// Both documents loaded: the model's `create_occurrence` on the origin's
/// document, committed first.


/// Then the schedule, advanced, with the key fired.


/// The schedule's row, if the document holds one.
pub fn schedule_row(doc: &DocumentBody) -> (r: Option<crate::verified::Schedule>)
    ensures
        r.deep_view() == spec_schedule_row(doc@),
{
    proof {
        crate::concrete::lemma_doc_view(doc);
    }
    match doc {
        DocumentBody::Schedule(Some(row)) => Some(copy(row)),
        _ => None,
    }
}

impl State {
    /// The store answered a load of schedule `id`, read in full: not cached.
    pub fn loaded_schedule(&mut self, id: &str, outcome: StoreRes) -> (r: Result<Working, String>)
        ensures
            (final(self).deep_view(), r.deep_view()) == spec_loaded_schedule(old(self).deep_view(), id@, outcome),
    {
        proof {
            reveal(spec_loaded_schedule);
        }
        let key = self.keys.sched_key(id);
        let target = Target::Schedule(text(id)).name();
        match outcome {
            StoreRes::Get { result: Ok(None) } => {
                let loaded = Loaded::empty_schedule(text(id));
                Ok(Working { target, key, loaded, etag: None })
            },
            StoreRes::Get { result: Ok(Some((bytes, etag))) } => match document::decode_schedule(bytes.as_slice()) {
                Ok(loaded) => Ok(Working { target, key, loaded, etag: Some(etag) }),
                Err(e) => Err(e),
            },
            StoreRes::Get { result: Err(e) } => Err(error_text(&e)),
            _ => Err(error_text(&unexpected())),
        }
    }

    pub fn run_schedule(&mut self, f: Flight, w: Working)
        ensures
            final(self).deep_view() == spec_run_schedule(old(self).deep_view(), f.deep_view(), w.deep_view()),
    {
        proof {
            reveal(spec_run_schedule);
        }
        let (mut commit, done) = self.decide(&f.work, w);
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                let f = Flight { phase: Phase::Schedule { commit, done }, ..f };
                self.inflight(f);
            },
            Progress::Done(fired) => self.committed(f, done, fired),
            Progress::Failed(e) => self.commit_failed(f, e),
        }
    }

    // -----------------------------------------------------------------------
    // The fire: two documents
    // -----------------------------------------------------------------------

    /// The schedule is loaded: its due occurrence, if any, as a promise in
    /// the occurrence's origin, then the schedule advanced, each its own
    /// commit, in that order. A schedule not due, or gone, is rewritten
    /// unchanged so the key can be collected behind the write.
    pub fn fire_decide(&mut self, f: Flight, ws: Working)
        ensures
            final(self).deep_view() == spec_fire_decide(old(self).deep_view(), f.deep_view(), ws.deep_view()),
    {
        proof {
            reveal(spec_fire_decide);
        }
        let (fired, now) = match &f.work {
            Work::Fire { fired, now, .. } => (copy_fired(fired), *now),
            _ => return self.fail(f, text("not a fire")),
        };
        let t1 = document::clamp_now(document::loaded_committed_at(&ws.loaded), now);
        // the decision is the model's: the occurrence due at the instant, or none
        let body = document::loaded_body(&ws.loaded);
        let Decided { doc: advanced, response: _, born, notes: _ } = flight::decide(Job::Fire, body, t1, self.cfg.retry_timeout, 0);
        let mut born = born;
        let ghost born0 = born@;
        let row = schedule_row(&document::loaded_body(&ws.loaded));
        let last = born.pop();
        proof {
            assert(pend_v(born0).len() == born0.len());
            if born0.len() > 0 {
                assert(pend_v(born0).last() == born0.last()@);
            }
        }
        let due = match (row, last) {
            (Some(row), Some(pending)) => Some((row, pending)),
            _ => None,
        };
        match due {
            None => self.fire_idle(f, ws, t1, fired),
            Some((row, pending)) => {
                proof {
                    crate::concrete::lemma_pending_view(&pending);
                }
                let next = match schedule_row(&advanced) {
                    Some(c) => c.next_run_at,
                    None => None,
                };
                let origin = text(origin_of(pending.promise.as_str()));
                self.fire_claim(f, FireCtx { ws, row, advanced, pending, t1, origin, next });
            },
        }
    }

    /// Nothing due: a sweep of the schedule's document, rewritten unchanged.
    fn fire_idle(&mut self, f: Flight, ws: Working, t1: u64, fired: Option<FiredKey>)
        ensures
            final(self).deep_view() == spec_fire_idle(old(self).deep_view(), f.deep_view(), ws.deep_view(), t1, fired.deep_view()),
    {
        proof {
            reveal(spec_fire_idle);
        }
        let mut f = f;
        f.idle = true;
        let body = document::loaded_body(&ws.loaded);
        let deadline = document::deadline(&body);
        let flight = f.id;
        self.note(Note::SweepBegin { flight, target: copy_string(&ws.target), now: t1 });
        let after = body;
        let mut commit = self.commit_new(ws, after, deadline, t1, fired);
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                let f = Flight { phase: Phase::FireIdle { commit }, ..f };
                self.inflight(f);
            },
            Progress::Done(fired) => {
                self.note(Note::SweepEnd { flight, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                self.finish(f, Ok(fired));
            },
            Progress::Failed(e) => {
                self.note(Note::SweepEnd { flight, committed: false });
                self.commit_failed(f, e);
            },
        }
    }

    /// The origin's slot, now or when it frees.
    fn fire_claim(&mut self, f: Flight, ctx: FireCtx)
        ensures
            final(self).deep_view() == spec_fire_claim(old(self).deep_view(), f.deep_view(), ctx.deep_view()),
    {
        proof {
            reveal(spec_fire_claim);
        }
        let ghost s1 = self.deep_view();
        let name = copy_string(&ctx.origin);
        let mut slot = self.slot_take(name.as_str());
        if slot.busy.is_some() {
            let ghost q0 = slot.queue.deep_view();
            slot.queue.push(Queued::Waiter(f.id));
            proof {
                assert(slot.queue.deep_view() =~= q0.push(QueuedSpec::Waiter(f.id)));
            }
            self.slot_put(name.as_str(), slot);
            proof {
                crate::handler_docs::lemma_remove_insert(s1.flights.slots, name@, self.flights.slots.deep_view()[name@]);
            }
            let f = Flight { phase: Phase::FireWaitingOrigin(ctx), ..f };
            self.inflight(f);
        } else {
            slot.busy = Some(f.id);
            self.slot_put(name.as_str(), slot);
            proof {
                crate::handler_docs::lemma_remove_insert(s1.flights.slots, name@, self.flights.slots.deep_view()[name@]);
            }
            self.fire_load_origin(f, ctx);
        }
    }

    pub fn fire_load_origin(&mut self, f: Flight, ctx: FireCtx)
        ensures
            final(self).deep_view() == spec_fire_load_origin(old(self).deep_view(), f.deep_view(), ctx.deep_view()),
    {
        proof {
            reveal(spec_fire_load_origin);
        }
        let (op, revalidating) = self.load_origin(f.id, ctx.origin.as_str());
        let f = Flight { phase: Phase::FireLoadingOrigin { op, revalidating, ctx }, ..f };
        self.inflight(f);
    }

    /// Both documents loaded: the model's `create_occurrence` on the
    /// workflow document, committed first.
    pub fn fire_run(&mut self, f: Flight, ctx: FireCtx, wo: Working)
        ensures
            final(self).deep_view() == spec_fire_run(old(self).deep_view(), f.deep_view(), ctx.deep_view(), wo.deep_view()),
    {
        proof {
            reveal(spec_fire_run);
        }
        let t = document::clamp_now(document::loaded_committed_at(&wo.loaded), ctx.t1);
        let Decided { doc: after, response: _, born: _, notes: _ } = flight::decide(Job::Occurrence(copy(&ctx.pending)), document::loaded_body(&wo.loaded), t, self.cfg.retry_timeout, 0);
        let deadline = document::deadline(&after);
        let flight = f.id;
        proof {
            crate::concrete::lemma_pending_view(&ctx.pending);
        }
        self.note(Note::FireBegin { flight, origin: copy_string(&ctx.origin), now: t, row: Box::new(copy(&ctx.row)), at: ctx.pending.at, promise_id: copy_string(&ctx.pending.promise), next: ctx.next });
        let mut commit = self.commit_new(wo, after, deadline, t, None);
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                let f = Flight { phase: Phase::FireOrigin { commit, ctx, t }, ..f };
                self.inflight(f);
            },
            Progress::Done(_) => {
                self.note(Note::FireEnd { flight, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                self.release(ctx.origin.as_str());
                self.fire_advance(f, ctx, t);
            },
            Progress::Failed(e) => {
                self.note(Note::FireEnd { flight, committed: false });
                self.forget(ctx.origin.as_str());
                self.release(ctx.origin.as_str());
                self.commit_failed(f, e);
            },
        }
    }

    /// Then the schedule, advanced, with the key fired.
    pub fn fire_advance(&mut self, f: Flight, ctx: FireCtx, t: u64)
        ensures
            final(self).deep_view() == spec_fire_advance(old(self).deep_view(), f.deep_view(), ctx.deep_view(), t),
    {
        proof {
            reveal(spec_fire_advance);
        }
        let (id, fired) = match &f.work {
            Work::Fire { schedule, fired, .. } => (copy_string(schedule), copy_fired(fired)),
            _ => return self.fail(f, text("not a fire")),
        };
        let flight = f.id;
        proof {
            crate::concrete::lemma_pending_view(&ctx.pending);
        }
        self.note(Note::AdvanceBegin { flight, schedule: id, now: t, at: ctx.pending.at, next: ctx.next });
        let FireCtx { ws, row: _, advanced, pending: _, t1: _, origin: _, next: _ } = ctx;
        let deadline = document::deadline(&advanced);
        let mut commit = self.commit_new(ws, advanced, deadline, t, fired);
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                let f = Flight { phase: Phase::FireSchedule { commit }, ..f };
                self.inflight(f);
            },
            Progress::Done(fired) => {
                self.note(Note::AdvanceEnd { flight, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                self.finish(f, Ok(fired));
            },
            Progress::Failed(e) => {
                self.note(Note::AdvanceEnd { flight, committed: false });
                self.commit_failed(f, e);
            },
        }
    }
}

} // verus!
