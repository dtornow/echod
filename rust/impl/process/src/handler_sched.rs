//! One schedule: create, read, delete, and a run coming due.
//!
//! A run is two commits. The concrete model's `run_due` on the schedule's
//! document says which occurrence is due and advances the schedule; the
//! occurrence is a promise in its origin, `create_occurrence`, committed
//! there first; then the advanced schedule is committed and the key that
//! fired it is deleted. The schedule holds its own slot the whole time and
//! takes the origin's slot for the first commit.

use echod_concrete::{create_occurrence, doc_deadline, run_due};

use crate::verified::Schedule;

use crate::doc::{self, Loaded, Promise, Row};
use crate::handler_docs::{unexpected, FireCtx, Flight, Phase, Progress, Queued, Work, Working};
use crate::keys::origin_of;
use crate::target::Target;
use crate::types::*;
use crate::State;

impl State {

    /// The store answered a load of schedule `id`, read in full: not cached.
    pub(crate) fn loaded_schedule(&mut self, id: &str, outcome: StoreOutcome) -> Result<Working<Schedule>, String> {
        let key = self.keys.sched_key(id);
        let target = Target::Schedule(id.to_string()).name();
        match outcome {
            StoreOutcome::Got(None) => Ok(Working { target, key, loaded: Loaded::empty(), etag: None }),
            StoreOutcome::Got(Some((bytes, etag))) => {
                let loaded = doc::decode(&bytes)?;
                Ok(Working { target, key, loaded, etag: Some(etag) })
            }
            StoreOutcome::Failed(e) => Err(e.to_string()),
            _ => Err(unexpected().to_string()),
        }
    }

    pub(crate) fn run_schedule(&mut self, mut f: Flight, w: Working<Schedule>) {
        let (commit, done) = self.decide(&f.work, w);
        let mut commit = commit;
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                f.phase = Phase::Schedule { commit, done };
                self.flights.inflight.insert(f.id, f);
            }
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
    pub(crate) fn fire_decide(&mut self, mut f: Flight, ws: Working<Schedule>) {
        let Work::Fire { fired, now, .. } = &f.work else { return self.fail(f, "not a fire".to_string()) };
        let (fired, now) = (fired.clone(), *now);
        let t1 = doc::clamp_now(ws.loaded.stamp, now);
        // the decision is the model's: the occurrence due at the instant, or none
        let (advanced, mut born, _) = run_due(Schedule::doc_of(&ws.loaded.rows), t1, self.cfg.retry_timeout);
        let due = match (ws.loaded.rows.last().cloned(), born.pop()) {
            (Some(row), Some(pending)) => Some((row, pending)),
            _ => None,
        };
        let Some((row, pending)) = due else {
            // a sweep of the schedule's document that finds nothing due
            f.idle = true;
            let rows = ws.loaded.rows.clone();
            let deadline = doc::deadline(&rows);
            self.note(Note::SweepBegin { flight: f.id, target: ws.target.clone(), now: t1 });
            let mut commit = self.commit_new(ws, rows, deadline, t1, fired);
            match self.commit_advance(f.id, &mut commit, None) {
                Progress::Issued => {
                    f.phase = Phase::FireIdle { commit };
                    self.flights.inflight.insert(f.id, f);
                }
                Progress::Done(fired) => {
                    self.note(Note::SweepEnd { flight: f.id, committed: true });
                    self.note(Note::Commit(CommitOutcome::Committed));
                    self.finish(f, Ok(fired));
                }
                Progress::Failed(e) => {
                    self.note(Note::SweepEnd { flight: f.id, committed: false });
                    self.commit_failed(f, e);
                }
            }
            return;
        };
        let advanced = Schedule::rows_of(advanced);
        let next = advanced.first().map(|c| c.next_run_at).unwrap_or(pending.at);
        let origin = origin_of(&pending.promise).to_string();
        let ctx = FireCtx { ws, row, advanced, pending, t1, origin, next };
        // the origin's slot, now or when it frees
        let slot = self.flights.slots.entry(ctx.origin.clone()).or_default();
        if slot.busy.is_some() {
            slot.queue.push_back(Queued::Waiter(f.id));
            f.phase = Phase::FireWaitingOrigin(ctx);
            self.flights.inflight.insert(f.id, f);
        } else {
            slot.busy = Some(f.id);
            self.fire_load_origin(f, ctx);
        }
    }

    pub(crate) fn fire_load_origin(&mut self, mut f: Flight, ctx: FireCtx) {
        let (op, revalidating) = self.load_origin(f.id, &ctx.origin);
        f.phase = Phase::FireLoadingOrigin { op, revalidating, ctx };
        self.flights.inflight.insert(f.id, f);
    }

    /// Both documents loaded: the model's `create_occurrence` on the
    /// origin's document, committed first.
    pub(crate) fn fire_run(&mut self, mut f: Flight, ctx: FireCtx, wo: Working<Promise>) {
        let t = doc::clamp_now(wo.loaded.stamp, ctx.t1);
        let doc = create_occurrence(Promise::doc_of(&wo.loaded.rows), &ctx.pending, t);
        let deadline = doc_deadline(&doc);
        let rows = Promise::rows_of(doc);
        self.note(Note::FireBegin { flight: f.id, origin: ctx.origin.clone(), now: t, row: Box::new(ctx.row.clone()), at: ctx.pending.at, promise_id: ctx.pending.promise.clone(), next: ctx.next });
        let mut commit = self.commit_new(wo, rows, deadline, t, None);
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                f.phase = Phase::FireOrigin { commit, ctx, t };
                self.flights.inflight.insert(f.id, f);
            }
            Progress::Done(_) => {
                self.note(Note::FireEnd { flight: f.id, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                self.release(&ctx.origin);
                self.fire_advance(f, ctx, t);
            }
            Progress::Failed(e) => {
                self.note(Note::FireEnd { flight: f.id, committed: false });
                self.forget(&ctx.origin);
                self.release(&ctx.origin);
                self.commit_failed(f, e);
            }
        }
    }

    /// Then the schedule, advanced, with the key fired.
    pub(crate) fn fire_advance(&mut self, mut f: Flight, ctx: FireCtx, t: u64) {
        let Work::Fire { schedule, fired, .. } = &f.work else { return self.fail(f, "not a fire".to_string()) };
        let (id, fired) = (schedule.clone(), fired.clone());
        self.note(Note::AdvanceBegin { flight: f.id, schedule: id, now: t, at: ctx.pending.at, next: ctx.next });
        let FireCtx { ws, advanced, .. } = ctx;
        let deadline = doc::deadline(&advanced);
        let mut commit = self.commit_new(ws, advanced, deadline, t, fired);
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                f.phase = Phase::FireSchedule { commit };
                self.flights.inflight.insert(f.id, f);
            }
            Progress::Done(fired) => {
                self.note(Note::AdvanceEnd { flight: f.id, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                self.finish(f, Ok(fired));
            }
            Progress::Failed(e) => {
                self.note(Note::AdvanceEnd { flight: f.id, committed: false });
                self.commit_failed(f, e);
            }
        }
    }
}
