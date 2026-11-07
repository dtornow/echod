//! One schedule: create, read, delete, and a run coming due.
//!
//! A run is two commits. The concrete model's `run_due` on the schedule's
//! document says which occurrence is due and advances the schedule; the
//! occurrence is a promise in its origin, `create_occurrence`, committed
//! there first; then the advanced schedule is committed and the key that
//! fired it is deleted. The schedule holds its own slot the whole time and
//! takes the origin's slot for the first commit.

use vstd::prelude::*;

use echod_abstract::trusted::copy;
use echod_concrete::DocumentBody;

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
use echod_concrete::node::{pend_v, spec_body_deadline, DocumentBodyV};

verus! {

/// The store answered a load of schedule `id`, read in full: not cached.
#[verifier::opaque]
pub open spec fn spec_loaded_schedule(s: S, id: Seq<char>, outcome: StoreOutcome) -> (S, Result<WorkingSpec, Seq<char>>) {
    let key = spec_sched_key(s.keys.prefix, id);
    let target = crate::target::spec_name(crate::target::TargetSpec::Schedule(id));
    match outcome {
        StoreOutcome::Got(None) => (s, Ok(spec_working(target, key, document::spec_empty_schedule(id), None))),
        StoreOutcome::Got(Some((bytes, etag))) => match document::spec_decode_schedule(bytes@) {
            Ok(loaded) => (s, Ok(spec_working(target, key, loaded, Some(etag.deep_view())))),
            Err(e) => (s, Err(e)),
        },
        StoreOutcome::Failed(e) => (s, Err(spec_error_text(e.deep_view()))),
        _ => (s, Err(spec_error_text(spec_unexpected()))),
    }
}

#[verifier::opaque]
pub open spec fn spec_run_schedule(s: S, f: FlightSpec, w: WorkingSpec) -> S {
    let (s, commit, done) = spec_decide(s, f.work, w);
    let (s, commit, p) = spec_commit_advance(s, f.id, commit, None);
    match p {
        ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::Schedule { commit, done }, ..f }),
        ProgressSpec::Done(fired) => spec_committed(s, f, done, fired),
        ProgressSpec::Failed(e) => spec_commit_failed(s, f, e),
    }
}

/// The schedule's row, if the document holds one.
pub open spec fn spec_schedule_row(doc: DocumentBodyV) -> Option<crate::verified::ScheduleSpec> {
    match doc {
        DocumentBodyV::Schedule(Some(row)) => Some(row.deep_view()),
        _ => None,
    }
}

/// The schedule is loaded: its due occurrence, if any, as a promise in the
/// occurrence's origin, then the schedule advanced, each its own commit, in
/// that order. A schedule not due, or gone, is rewritten unchanged so the
/// key can be collected behind the write.
#[verifier::opaque]
pub open spec fn spec_fire_decide(s: S, f: FlightSpec, ws: WorkingSpec) -> S {
    match f.work {
        WorkSpec::Fire { fired, now, .. } => {
            let t1 = document::spec_clamp_now(document::spec_loaded_committed_at(ws.loaded), now);
            let body = document::spec_loaded_body(ws.loaded);
            let (advanced, _response, born, _notes) = spec_step(AJob::Fire, body, t1, s.cfg.retry_timeout, 0);
            let due = match (spec_schedule_row(body), born.len() > 0) {
                (Some(row), true) => Some((row, born.last())),
                _ => None,
            };
            match due {
                None => spec_fire_idle(s, f, ws, t1, fired),
                Some((row, pending)) => {
                    let next = match spec_schedule_row(advanced) {
                        Some(c) => c.next_run_at,
                        None => pending.at,
                    };
                    let origin = echod_types::origin(pending.promise);
                    spec_fire_claim(s, f, FireCtxSpec { ws, row, advanced, pending, t1, origin, next })
                },
            }
        },
        _ => spec_fail(s, f, "not a fire"@),
    }
}

/// Nothing due: a sweep of the schedule's document, rewritten unchanged.
#[verifier::opaque]
pub open spec fn spec_fire_idle(s: S, f: FlightSpec, ws: WorkingSpec, t1: u64, fired: Option<AFired>) -> S {
    let f = FlightSpec { idle: true, ..f };
    let body = document::spec_loaded_body(ws.loaded);
    let deadline = spec_body_deadline(body);
    let s = spec_note(s, NoteSpec::SweepBegin { flight: f.id, target: ws.target, now: t1 });
    let (s, commit) = spec_commit_new(s, ws, body, deadline, t1, fired);
    let (s, commit, p) = spec_commit_advance(s, f.id, commit, None);
    match p {
        ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::FireIdle { commit }, ..f }),
        ProgressSpec::Done(fired) => {
            let s = spec_note(s, NoteSpec::SweepEnd { flight: f.id, committed: true });
            let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Committed));
            spec_finish(s, f, Ok(fired))
        },
        ProgressSpec::Failed(e) => {
            let s = spec_note(s, NoteSpec::SweepEnd { flight: f.id, committed: false });
            spec_commit_failed(s, f, e)
        },
    }
}

/// The origin's slot, now or when it frees.
#[verifier::opaque]
pub open spec fn spec_fire_claim(s: S, f: FlightSpec, ctx: FireCtxSpec) -> S {
    let origin = ctx.origin;
    let slot = spec_slot_of(s, origin);
    if slot.busy is Some {
        let s = spec_with_slot(s, origin, SlotSpec { queue: slot.queue.push(QueuedSpec::Waiter(f.id)), ..slot });
        spec_inflight(s, FlightSpec { phase: PhaseSpec::FireWaitingOrigin(ctx), ..f })
    } else {
        let s = spec_with_slot(s, origin, SlotSpec { busy: Some(f.id), ..slot });
        spec_fire_load_origin(s, f, ctx)
    }
}

#[verifier::opaque]
pub open spec fn spec_fire_load_origin(s: S, f: FlightSpec, ctx: FireCtxSpec) -> S {
    let (s, op, revalidating) = spec_load_origin(s, f.id, ctx.origin);
    spec_inflight(s, FlightSpec { phase: PhaseSpec::FireLoadingOrigin { op, revalidating, ctx }, ..f })
}

/// Both documents loaded: the model's `create_occurrence` on the origin's
/// document, committed first.
#[verifier::opaque]
pub open spec fn spec_fire_run(s: S, f: FlightSpec, ctx: FireCtxSpec, wo: WorkingSpec) -> S {
    let t = document::spec_clamp_now(document::spec_loaded_committed_at(wo.loaded), ctx.t1);
    let (after, _r, _b, _n) = spec_step(AJob::Occurrence(ctx.pending), document::spec_loaded_body(wo.loaded), t, s.cfg.retry_timeout, 0);
    let deadline = spec_body_deadline(after);
    let s = spec_note(s, NoteSpec::FireBegin { flight: f.id, origin: ctx.origin, now: t, row: ctx.row, at: ctx.pending.at, promise_id: ctx.pending.promise, next: ctx.next });
    let (s, commit) = spec_commit_new(s, wo, after, deadline, t, None);
    let (s, commit, p) = spec_commit_advance(s, f.id, commit, None);
    match p {
        ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::FireOrigin { commit, ctx, t }, ..f }),
        ProgressSpec::Done(_) => {
            let s = spec_note(s, NoteSpec::FireEnd { flight: f.id, committed: true });
            let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Committed));
            let s = spec_release(s, ctx.origin);
            spec_fire_advance(s, f, ctx, t)
        },
        ProgressSpec::Failed(e) => {
            let s = spec_note(s, NoteSpec::FireEnd { flight: f.id, committed: false });
            let s = spec_forget_origin(s, ctx.origin);
            let s = spec_release(s, ctx.origin);
            spec_commit_failed(s, f, e)
        },
    }
}

/// Then the schedule, advanced, with the key fired.
#[verifier::opaque]
pub open spec fn spec_fire_advance(s: S, f: FlightSpec, ctx: FireCtxSpec, t: u64) -> S {
    match f.work {
        WorkSpec::Fire { schedule, fired, .. } => {
            let s = spec_note(s, NoteSpec::AdvanceBegin { flight: f.id, schedule, now: t, at: ctx.pending.at, next: ctx.next });
            let deadline = spec_body_deadline(ctx.advanced);
            let (s, commit) = spec_commit_new(s, ctx.ws, ctx.advanced, deadline, t, fired);
            let (s, commit, p) = spec_commit_advance(s, f.id, commit, None);
            match p {
                ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::FireSchedule { commit }, ..f }),
                ProgressSpec::Done(fired) => {
                    let s = spec_note(s, NoteSpec::AdvanceEnd { flight: f.id, committed: true });
                    let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Committed));
                    spec_finish(s, f, Ok(fired))
                },
                ProgressSpec::Failed(e) => {
                    let s = spec_note(s, NoteSpec::AdvanceEnd { flight: f.id, committed: false });
                    spec_commit_failed(s, f, e)
                },
            }
        },
        _ => spec_fail(s, f, "not a fire"@),
    }
}

/// The schedule's row, if the document holds one.
pub fn schedule_row(doc: &DocumentBody) -> (r: Option<crate::verified::Schedule>)
    ensures
        r.deep_view() == spec_schedule_row(doc@),
{
    proof {
        echod_concrete::lemma_doc_view(doc);
    }
    match doc {
        DocumentBody::Schedule(Some(row)) => Some(copy(row)),
        _ => None,
    }
}

impl State {
    /// The store answered a load of schedule `id`, read in full: not cached.
    pub fn loaded_schedule(&mut self, id: &str, outcome: StoreOutcome) -> (r: Result<Working, String>)
        ensures
            (final(self).deep_view(), r.deep_view()) == spec_loaded_schedule(old(self).deep_view(), id@, outcome),
    {
        proof {
            reveal(spec_loaded_schedule);
        }
        let key = self.keys.sched_key(id);
        let target = Target::Schedule(text(id)).name();
        match outcome {
            StoreOutcome::Got(None) => {
                let loaded = Loaded::empty_schedule(text(id));
                Ok(Working { target, key, loaded, etag: None })
            },
            StoreOutcome::Got(Some((bytes, etag))) => match document::decode_schedule(bytes.as_slice()) {
                Ok(loaded) => Ok(Working { target, key, loaded, etag: Some(etag) }),
                Err(e) => Err(e),
            },
            StoreOutcome::Failed(e) => Err(error_text(&e)),
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
                    echod_concrete::lemma_pending_view(&pending);
                }
                let next = match schedule_row(&advanced) {
                    Some(c) => c.next_run_at,
                    None => pending.at,
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
            echod_concrete::lemma_pending_view(&ctx.pending);
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
            echod_concrete::lemma_pending_view(&ctx.pending);
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
