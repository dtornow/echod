//! One schedule: create, read, delete, and a run coming due.
//!
//! A run is two commits. The schedule's row says which occurrence is due;
//! that occurrence is a promise in its origin, committed there first; then
//! the schedule advances and the key that fired it is deleted. The schedule
//! holds its own slot the whole time and takes the origin's slot for the
//! first commit.

use crate::verified::steps;
use crate::verified::{Occurrence, Schedule, ScheduleTimeoutReq, State as Rows};

use crate::doc::{self, Loaded, Row};
use crate::handler_docs::{unexpected, FireCtx, Flight, Phase, Progress, Queued, Work, Working};
use crate::keys::origin_of;
use crate::target::Target;
use crate::types::*;
use crate::verified::Promise;
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

    /// The promise id an occurrence expands to.
    pub fn expand(template: &str, id: &str, at: u64) -> String {
        template.replace("{{.id}}", id).replace("{{.timestamp}}", &at.to_string())
    }

    /// The schedule is loaded: its due occurrence, if any, as a promise in
    /// the occurrence's origin, then the schedule advanced, each its own
    /// commit, in that order. A schedule not due, or gone, is rewritten
    /// unchanged so the key can be collected behind the write.
    pub(crate) fn fire_decide(&mut self, mut f: Flight, ws: Working<Schedule>) {
        let Work::Fire { schedule, fired, now } = &f.work else { return self.fail(f, "not a fire".to_string()) };
        let (id, fired, now) = (schedule.clone(), fired.clone(), *now);
        let t1 = steps::clamp_now(ws.loaded.stamp, now);
        // the decision is the step module's: a row due at the instant, or none
        let due = steps::schedule_due(&Schedule::state_of(&ws.loaded.rows), t1).map(|i| ws.loaded.rows[i].clone());
        let Some(c) = due else {
            // a sweep of the schedule's document that finds nothing due
            f.idle = true;
            let rows = ws.loaded.rows.clone();
            self.note(Note::SweepBegin { flight: f.id, target: ws.target.clone(), now: t1 });
            let mut commit = self.commit_new(ws, rows, t1, false, fired);
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
        let at = c.next_run_at;
        let promise_id = Self::expand(&c.promise_id, &id, at);
        let origin = origin_of(&promise_id).to_string();
        let next = crate::cron::next_after(&c.cron, at as i64).max(at as i64 + 1) as u64;
        let ctx = FireCtx { ws, row: c, t1, at, promise_id, origin, next };
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

    /// Both documents loaded: the kernel's `process_schedule` on the row
    /// beside the origin's objects, then the origin committed first.
    pub(crate) fn fire_run(&mut self, mut f: Flight, ctx: FireCtx, wo: Working<Promise>) {
        let Work::Fire { schedule, .. } = &f.work else { return self.fail(f, "not a fire".to_string()) };
        let id = schedule.clone();
        let t = steps::clamp_now(wo.loaded.stamp, ctx.t1);
        let req = ScheduleTimeoutReq { schedule: id, occurrences: vec![Occurrence { at: ctx.at, promise_id: ctx.promise_id.clone() }], next_run_at: ctx.next };
        let docs = crate::state_docs::Docs { rows: wo.loaded.rows.clone() };
        let sched = crate::state_sched::Sched { rows: ctx.ws.loaded.rows.clone() };
        let mut state = Rows { objects: docs.rows, schedules: sched.rows, outbox: Vec::new() };
        state.process_schedule(&req, t, &self.rows_cfg);
        steps::drain(&mut state, t, &self.rows_cfg);
        self.note(Note::FireBegin { flight: f.id, origin: ctx.origin.clone(), now: t, row: Box::new(ctx.row.clone()), at: ctx.at, promise_id: ctx.promise_id.clone(), next: ctx.next });
        let mut commit = self.commit_new(wo, state.objects, t, false, None);
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                f.phase = Phase::FireOrigin { commit, ctx, schedules: state.schedules, outbox: state.outbox, t };
                self.flights.inflight.insert(f.id, f);
            }
            Progress::Done(_) => {
                self.note(Note::FireEnd { flight: f.id, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                for e in &state.outbox {
                    self.send(e);
                }
                self.release(&ctx.origin);
                self.fire_advance(f, ctx, state.schedules, t);
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
    pub(crate) fn fire_advance(&mut self, mut f: Flight, ctx: FireCtx, schedules: Vec<Schedule>, t: u64) {
        let Work::Fire { schedule, fired, .. } = &f.work else { return self.fail(f, "not a fire".to_string()) };
        let (id, fired) = (schedule.clone(), fired.clone());
        self.note(Note::AdvanceBegin { flight: f.id, schedule: id, now: t, at: ctx.at, next: ctx.next });
        let FireCtx { ws, .. } = ctx;
        let mut commit = self.commit_new(ws, schedules, t, false, fired);
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
