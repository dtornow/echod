//! One step on one document, from load to commit, one store call at a
//! time.
//!
//! Per document, one flight at a time: the rest queue behind it. A flight
//! loads the document, runs the kernel, drains what the step left owed,
//! then commits by the verified protocol of `echod_kernel::commit`, each store
//! call between its decisions: the key for the document's nearest deadline
//! is put before the document, the document is written conditionally on
//! the version loaded, the key replaced is removed after, the key kept is
//! remembered with the version written, and the key that fired is deleted:
//! the write fences every commit still in flight that armed it. A fire that
//! found nothing due rewrites the document at a new version first, for the
//! same reason, and only then deletes the key. A lost race re-reads and
//! re-decides.
//!
//! A schedule's key fires on two documents: the schedule's row decides the
//! occurrence's promise, the kernel's `process_schedule` runs on the row
//! beside the promise's origin, and the origin is committed first, then
//! the schedule with the key fired: the system model's `Fire`, with its
//! pending half. The fire holds the schedule's slot throughout and takes
//! the origin's for the first commit; no flight on an origin ever waits
//! for a schedule's slot, so none of this waits in a circle.
//!
//! The cache holds the last document this node read or wrote for an
//! origin. It is never used without asking the store: every load
//! revalidates with `If-None-Match`, and the body is used only when the
//! store says the version held is current (the system's revalidation
//! theorem). Every version read or written, and every entry dropped, is
//! reported to the core, so what it decides on is what the cache holds. A
//! schedule's document is not cached.

use std::collections::{HashMap, VecDeque};

use echod_kernel::node::Key;
use echod_kernel::steps;
use echod_kernel::commit::Commit as Plan;
use echod_kernel::{self as k, Occurrence, OutboxEntry, Promise, Schedule, ScheduleTimeoutReq, State as KState};
use resonate_core::{util, Unavailable};

use crate::cache::{Cache, Cached};
use crate::dispatch::Target;
use crate::doc::{self, Header, Loaded, Row};
use crate::keys::origin_of;
use crate::types::*;
use crate::{unavailable, Owner, State};

/// What a flight does.
pub(crate) enum Work {
    Request { id: RequestId, kind: String, corr: String, req: k::Request, action_kind: Option<String>, now: u64 },
    Sweep { fired: FiredKey, now: u64 },
    Fire { schedule: String, fired: FiredKey, now: u64 },
}

impl Work {
    fn now(&self) -> u64 {
        match self {
            Work::Request { now, .. } | Work::Sweep { now, .. } | Work::Fire { now, .. } => *now,
        }
    }
}

/// The key that fired a flight, for the timers when it ends.
#[derive(Clone)]
pub(crate) struct Firing {
    pub key: String,
    pub at: u64,
    pub kind: TimerKind,
    pub lag: u64,
}

/// The document a flight works on.
pub(crate) struct Working<R: Row> {
    /// The target's name.
    pub target: String,
    /// The object's key.
    pub key: String,
    pub loaded: Loaded<R>,
    pub etag: Option<Etag>,
}

/// A commit in progress: the verified plan, and the store call between
/// its decisions that is waited on.
pub(crate) struct Committing<R: Row> {
    w: Working<R>,
    rows: Vec<R>,
    changed: Vec<R>,
    changed_any: bool,
    now: u64,
    fired: Option<FiredKey>,
    plan: Plan,
    step: Step,
}

enum Step {
    Start,
    PuttingKey { op: OpId, key: Key, name: String },
    Writing { op: OpId, mode: WriteMode, row_count: usize, bytes: u64, len: usize, idle: bool },
    DeletingPrevious { op: OpId, key: Key, name: String },
    DeletingFired { op: OpId, key: Key, name: String },
    Over,
}

impl Step {
    /// The store call the step waits on.
    fn expects(&self) -> Option<OpId> {
        match self {
            Step::PuttingKey { op, .. } | Step::Writing { op, .. } | Step::DeletingPrevious { op, .. } | Step::DeletingFired { op, .. } => Some(*op),
            Step::Start | Step::Over => None,
        }
    }
}

enum Progress {
    Issued,
    Done(Fired),
    Failed(StoreError),
}

/// What a committed step answers with.
struct Done {
    response: Option<k::Response>,
    outbox: Vec<OutboxEntry>,
    did: bool,
}

/// A fire past its decision: the schedule as loaded, the occurrence, and
/// what the kernel is asked.
struct FireCtx {
    ws: Working<Schedule>,
    row: Schedule,
    t1: u64,
    at: u64,
    promise_id: String,
    origin: String,
    next: u64,
}

enum Phase {
    Idle,
    Loading { op: OpId, revalidating: Option<Cached> },
    Origin { commit: Committing<Promise>, done: Done },
    Schedule { commit: Committing<Schedule>, done: Done },
    FireLoadingSchedule { op: OpId },
    FireWaitingOrigin(FireCtx),
    FireLoadingOrigin { op: OpId, revalidating: Option<Cached>, ctx: FireCtx },
    FireIdle { commit: Committing<Schedule> },
    FireOrigin { commit: Committing<Promise>, ctx: FireCtx, schedules: Vec<Schedule>, outbox: Vec<OutboxEntry>, t: u64 },
    FireSchedule { commit: Committing<Schedule> },
}

impl Phase {
    /// The store call the flight waits on.
    fn expects(&self) -> Option<OpId> {
        match self {
            Phase::Idle | Phase::FireWaitingOrigin(_) => None,
            Phase::Loading { op, .. } | Phase::FireLoadingSchedule { op } | Phase::FireLoadingOrigin { op, .. } => Some(*op),
            Phase::Origin { commit, .. } | Phase::FireOrigin { commit, .. } => commit.step.expects(),
            Phase::Schedule { commit, .. } | Phase::FireIdle { commit } | Phase::FireSchedule { commit } => commit.step.expects(),
        }
    }
}

struct Flight {
    id: FlightId,
    target: Target,
    work: Work,
    attempt: u32,
    phase: Phase,
    firing: Option<Firing>,
}

enum Queued {
    Work(Box<(Target, Work, Option<Firing>)>),
    Waiter(FlightId),
}

#[derive(Default)]
struct Slot {
    busy: Option<FlightId>,
    queue: VecDeque<Queued>,
}

pub(crate) struct Flights {
    slots: HashMap<String, Slot>,
    inflight: HashMap<FlightId, Flight>,
    max_retries: u32,
}

impl Flights {
    pub fn new() -> Self {
        Self { slots: HashMap::new(), inflight: HashMap::new(), max_retries: 8 }
    }

}

fn unexpected() -> StoreError {
    StoreError::Unavailable("the store answered something else".into())
}

impl State {
    // -----------------------------------------------------------------------
    // Slots: one flight per document
    // -----------------------------------------------------------------------

    /// Run `work` on `target`, after whatever is on it already.
    pub(crate) fn submit(&mut self, target: Target, work: Work, firing: Option<Firing>) {
        let name = target.name();
        if let Work::Sweep { now, .. } = &work {
            let flight = self.next_flight;
            self.note(Note::SweepBegin { flight, target: name.clone(), now: *now });
        }
        let slot = self.flights.slots.entry(name).or_default();
        if slot.busy.is_some() {
            slot.queue.push_back(Queued::Work(Box::new((target, work, firing))));
            return;
        }
        self.start(target, work, firing);
    }

    fn start(&mut self, target: Target, work: Work, firing: Option<Firing>) {
        let id = self.next_flight;
        self.next_flight += 1;
        self.flights.slots.entry(target.name()).or_default().busy = Some(id);
        let f = Flight { id, target, work, attempt: 0, phase: Phase::Idle, firing };
        self.begin(f);
    }

    /// The slot of `name` is free: whatever waits on it goes next.
    fn release(&mut self, name: &str) {
        let Some(slot) = self.flights.slots.get_mut(name) else { return };
        slot.busy = None;
        match slot.queue.pop_front() {
            None => {
                self.flights.slots.remove(name);
            }
            Some(Queued::Work(q)) => {
                let (target, work, firing) = *q;
                self.start(target, work, firing);
            }
            Some(Queued::Waiter(fid)) => {
                slot.busy = Some(fid);
                if let Some(mut f) = self.flights.inflight.remove(&fid) {
                    match std::mem::replace(&mut f.phase, Phase::Idle) {
                        Phase::FireWaitingOrigin(ctx) => self.fire_load_origin(f, ctx),
                        _ => self.fail(f, Unavailable::new("a flight waited for a slot it did not need")),
                    }
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // A flight's course
    // -----------------------------------------------------------------------

    /// Start, or start over after a lost race.
    fn begin(&mut self, mut f: Flight) {
        match &f.work {
            Work::Fire { schedule, .. } => {
                let key = self.keys.sched_key(schedule);
                let op = self.store(StoreCall::Get { key }, Owner::Flight(f.id));
                f.phase = Phase::FireLoadingSchedule { op };
            }
            _ => {
                let (op, revalidating) = match &f.target {
                    Target::Origin(o) => self.load_origin(f.id, o),
                    Target::Schedule(id) => (self.store(StoreCall::Get { key: self.keys.sched_key(id) }, Owner::Flight(f.id)), None),
                };
                f.phase = Phase::Loading { op, revalidating };
            }
        }
        self.flights.inflight.insert(f.id, f);
    }

    fn retry(&mut self, mut f: Flight) {
        f.attempt += 1;
        if f.attempt > self.flights.max_retries {
            self.note(Note::Commit(CommitOutcome::Exhausted));
            let what = match f.target {
                Target::Origin(_) => "document",
                Target::Schedule(_) => "schedule",
            };
            self.fail(f, Unavailable::new(format!("too many races on the {what}")));
        } else {
            self.begin(f);
        }
    }

    /// A store call a flight waited on has its answer.
    pub(crate) fn flight_completed(&mut self, fid: FlightId, op: OpId, outcome: StoreOutcome) {
        let Some(mut f) = self.flights.inflight.remove(&fid) else { return };
        if f.phase.expects() != Some(op) {
            // an answer to a call this flight no longer waits on
            self.flights.inflight.insert(fid, f);
            return;
        }
        match std::mem::replace(&mut f.phase, Phase::Idle) {
            Phase::Loading { revalidating, .. } => match f.target.clone() {
                Target::Origin(origin) => match self.loaded_origin(&origin, revalidating, outcome) {
                    Ok(w) => self.run_origin(f, w),
                    Err(e) => self.fail(f, e),
                },
                Target::Schedule(id) => match self.loaded_schedule(&id, outcome) {
                    Ok(w) => self.run_schedule(f, w),
                    Err(e) => self.fail(f, e),
                },
            },
            Phase::Origin { mut commit, done } => match self.commit_advance(fid, &mut commit, Some(outcome)) {
                Progress::Issued => {
                    f.phase = Phase::Origin { commit, done };
                    self.flights.inflight.insert(fid, f);
                }
                Progress::Done(fired) => self.committed(f, done, fired),
                Progress::Failed(e) => self.commit_failed(f, e),
            },
            Phase::Schedule { mut commit, done } => match self.commit_advance(fid, &mut commit, Some(outcome)) {
                Progress::Issued => {
                    f.phase = Phase::Schedule { commit, done };
                    self.flights.inflight.insert(fid, f);
                }
                Progress::Done(fired) => self.committed(f, done, fired),
                Progress::Failed(e) => self.commit_failed(f, e),
            },
            Phase::FireLoadingSchedule { .. } => {
                let Work::Fire { schedule, .. } = &f.work else { return self.fail(f, Unavailable::new("not a fire")) };
                match self.loaded_schedule(&schedule.clone(), outcome) {
                    Ok(ws) => self.fire_decide(f, ws),
                    Err(e) => self.fail(f, e),
                }
            }
            Phase::FireLoadingOrigin { revalidating, ctx, .. } => match self.loaded_origin(&ctx.origin, revalidating, outcome) {
                Ok(wo) => self.fire_run(f, ctx, wo),
                Err(e) => {
                    self.release(&ctx.origin);
                    self.fail(f, e);
                }
            },
            Phase::FireIdle { mut commit } => match self.commit_advance(fid, &mut commit, Some(outcome)) {
                Progress::Issued => {
                    f.phase = Phase::FireIdle { commit };
                    self.flights.inflight.insert(fid, f);
                }
                Progress::Done(fired) => {
                    self.note(Note::SweepEnd { flight: fid, committed: true });
                    self.note(Note::Commit(CommitOutcome::Committed));
                    self.finish(f, Ok(fired));
                }
                Progress::Failed(e) => {
                    self.note(Note::SweepEnd { flight: fid, committed: false });
                    self.commit_failed(f, e);
                }
            },
            Phase::FireOrigin { mut commit, ctx, schedules, outbox, t } => match self.commit_advance(fid, &mut commit, Some(outcome)) {
                Progress::Issued => {
                    f.phase = Phase::FireOrigin { commit, ctx, schedules, outbox, t };
                    self.flights.inflight.insert(fid, f);
                }
                Progress::Done(_) => {
                    self.note(Note::FireEnd { flight: fid, committed: true });
                    self.note(Note::Commit(CommitOutcome::Committed));
                    for e in &outbox {
                        self.send(e);
                    }
                    self.release(&ctx.origin);
                    self.fire_advance(f, ctx, schedules, t);
                }
                Progress::Failed(e) => {
                    self.note(Note::FireEnd { flight: fid, committed: false });
                    self.forget(&ctx.origin);
                    self.release(&ctx.origin);
                    self.commit_failed(f, e);
                }
            },
            Phase::FireSchedule { mut commit } => match self.commit_advance(fid, &mut commit, Some(outcome)) {
                Progress::Issued => {
                    f.phase = Phase::FireSchedule { commit };
                    self.flights.inflight.insert(fid, f);
                }
                Progress::Done(fired) => {
                    self.note(Note::AdvanceEnd { flight: fid, committed: true });
                    self.note(Note::Commit(CommitOutcome::Committed));
                    self.finish(f, Ok(fired));
                }
                Progress::Failed(e) => {
                    self.note(Note::AdvanceEnd { flight: fid, committed: false });
                    self.commit_failed(f, e);
                }
            },
            _ => self.fail(f, Unavailable::new("an answer the flight did not wait for")),
        }
    }

    // -----------------------------------------------------------------------
    // Loading
    // -----------------------------------------------------------------------

    /// Ask for an origin's document: revalidated against the store when
    /// the cache holds a version, read in full otherwise.
    fn load_origin(&mut self, fid: FlightId, origin: &str) -> (OpId, Option<Cached>) {
        let key = self.keys.doc_key(origin);
        match self.cache.get(origin) {
            Some(c) => {
                let etag = c.etag.clone();
                (self.store(StoreCall::GetIfNoneMatch { key, etag }, Owner::Flight(fid)), Some(c))
            }
            None => {
                self.note(Note::Cache(CacheResult::Miss));
                (self.store(StoreCall::Get { key }, Owner::Flight(fid)), None)
            }
        }
    }

    /// The store answered a load of `origin`. Cache bookkeeping is on the
    /// fleet's time.
    fn loaded_origin(&mut self, origin: &str, revalidating: Option<Cached>, outcome: StoreOutcome) -> Result<Working<Promise>, Unavailable> {
        let now = self.now();
        let key = self.keys.doc_key(origin);
        let w = |loaded: Loaded<Promise>, etag: Option<Etag>| Working { target: origin.to_string(), key: key.clone(), loaded, etag };
        match (revalidating, outcome) {
            (Some(c), StoreOutcome::Read(Read::NotModified)) => {
                self.note(Note::Cache(CacheResult::Revalidated));
                self.remember(origin, Cached { filled_at: now, ..c.clone() });
                Ok(w(c.loaded, Some(c.etag)))
            }
            (Some(_), StoreOutcome::Read(Read::Absent)) => {
                self.note(Note::Cache(CacheResult::Absent));
                self.forget(origin);
                Ok(w(Loaded::empty(), None))
            }
            (Some(_), StoreOutcome::Read(Read::Body(bytes, etag))) => {
                self.note(Note::Cache(CacheResult::Refreshed));
                let loaded: Loaded<Promise> = doc::decode(&bytes).map_err(Unavailable::new)?;
                self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone(), filled_at: now });
                Ok(w(loaded, Some(etag)))
            }
            (None, StoreOutcome::Got(None)) => Ok(w(Loaded::empty(), None)),
            (None, StoreOutcome::Got(Some((bytes, etag)))) => {
                let loaded: Loaded<Promise> = doc::decode(&bytes).map_err(Unavailable::new)?;
                self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone(), filled_at: now });
                Ok(w(loaded, Some(etag)))
            }
            (_, StoreOutcome::Failed(e)) => Err(unavailable(e)),
            _ => Err(unavailable(unexpected())),
        }
    }

    /// The store answered a load of schedule `id`, read in full: not cached.
    fn loaded_schedule(&mut self, id: &str, outcome: StoreOutcome) -> Result<Working<Schedule>, Unavailable> {
        let key = self.keys.sched_key(id);
        let target = Target::Schedule(id.to_string()).name();
        match outcome {
            StoreOutcome::Got(None) => Ok(Working { target, key, loaded: Loaded::empty(), etag: None }),
            StoreOutcome::Got(Some((bytes, etag))) => {
                let loaded = doc::decode(&bytes).map_err(Unavailable::new)?;
                Ok(Working { target, key, loaded, etag: Some(etag) })
            }
            StoreOutcome::Failed(e) => Err(unavailable(e)),
            _ => Err(unavailable(unexpected())),
        }
    }

    // -----------------------------------------------------------------------
    // The step
    // -----------------------------------------------------------------------

    /// Run the flight's step on an origin's document and start its commit.
    fn run_origin(&mut self, mut f: Flight, w: Working<Promise>) {
        let (commit, done) = self.decide(&f.work, w);
        let mut commit = commit;
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                f.phase = Phase::Origin { commit, done };
                self.flights.inflight.insert(f.id, f);
            }
            Progress::Done(fired) => self.committed(f, done, fired),
            Progress::Failed(e) => self.commit_failed(f, e),
        }
    }

    fn run_schedule(&mut self, mut f: Flight, w: Working<Schedule>) {
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

    /// The step: decided no earlier than the last step on the document,
    /// the kernel being proved for an instant at or after it; then the
    /// drain. A lost race runs this again on what it re-read, so the step
    /// decides from the state it is given, which every kernel handler does.
    fn decide<R: Row>(&mut self, work: &Work, w: Working<R>) -> (Committing<R>, Done) {
        let mut state = R::state_of(&w.loaded.rows);
        let now = steps::clamp_now(w.loaded.stamp, work.now());
        let (response, did) = match work {
            Work::Request { req, .. } => (Some(state.handle(req, now, &self.kcfg)), false),
            Work::Sweep { .. } => {
                let did = steps::sweep(&mut state, now, &self.kcfg);
                (None, did)
            }
            Work::Fire { .. } => (None, false),
        };
        steps::drain(&mut state, now, &self.kcfg);
        let rows = R::rows_of(&state);
        let fired = match work {
            Work::Sweep { fired, .. } => Some(fired.clone()),
            _ => None,
        };
        let commit = self.commit_new(w, rows, now, did, fired);
        (commit, Done { response, outbox: state.outbox, did })
    }

    /// A committed step: the messages out, the answer back.
    fn committed(&mut self, f: Flight, done: Done, fired: Fired) {
        self.note(Note::Commit(CommitOutcome::Committed));
        for e in &done.outbox {
            self.send(e);
        }
        match &f.work {
            Work::Request { id, kind, corr, action_kind, .. } => {
                let resp = done.response.as_ref().map(|r| crate::wire::response_out(kind, corr, action_kind.as_deref(), r));
                let response = resp.ok_or_else(|| Unavailable::new("no answer"));
                self.emit(Effect::Reply { id: *id, response });
            }
            Work::Sweep { .. } => {
                self.note(Note::Sweep(if done.did { SweepOutcome::Fired } else { SweepOutcome::Idle }));
                self.note(Note::SweepEnd { flight: f.id, committed: true });
            }
            Work::Fire { .. } => {}
        }
        self.finish(f, Ok(fired));
    }

    /// The commit's store call failed: a lost race re-decides, anything
    /// else ends the flight with nothing cached.
    fn commit_failed(&mut self, f: Flight, e: StoreError) {
        if let Target::Origin(o) = &f.target {
            // A write that may or may not have landed: trust nothing cached.
            self.forget(&o.clone());
        }
        match e {
            StoreError::PreconditionFailed => {
                self.note(Note::Commit(CommitOutcome::Raced));
                self.note(Note::Raced { target: f.target.name(), attempt: f.attempt });
                self.retry(f);
            }
            e => {
                self.note(Note::Commit(CommitOutcome::Failed));
                self.fail(f, unavailable(e));
            }
        }
    }

    /// The flight ends without a commit.
    fn fail(&mut self, f: Flight, e: Unavailable) {
        match &f.work {
            Work::Request { id, .. } => self.emit(Effect::Reply { id: *id, response: Err(e.clone()) }),
            Work::Sweep { .. } => {
                self.note(Note::Sweep(SweepOutcome::Failed));
                self.note(Note::SweepEnd { flight: f.id, committed: false });
            }
            Work::Fire { .. } => {}
        }
        self.finish(f, Err(e));
    }

    /// The flight is over: its slot goes to the next, and the key that
    /// fired it hears how it went.
    fn finish(&mut self, f: Flight, r: Result<Fired, Unavailable>) {
        let name = f.target.name();
        self.release(&name);
        if let Some(firing) = f.firing {
            let now = self.now();
            self.timer_fired(firing, now, r);
        }
    }

    pub(crate) fn send(&mut self, e: &OutboxEntry) {
        let (address, message) = crate::wire::message_out(e, &self.cfg.url);
        self.emit(Effect::Send { address, message });
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
    fn fire_decide(&mut self, mut f: Flight, ws: Working<Schedule>) {
        let Work::Fire { schedule, fired, now } = &f.work else { return self.fail(f, Unavailable::new("not a fire")) };
        let (id, fired, now) = (schedule.clone(), fired.clone(), *now);
        let t1 = steps::clamp_now(ws.loaded.stamp, now);
        // the decision is the step module's: a row due at the instant, or none
        let due = steps::schedule_due(&Schedule::state_of(&ws.loaded.rows), t1).map(|i| ws.loaded.rows[i].clone());
        let Some(c) = due else {
            // a sweep of the schedule's document that finds nothing due
            let rows = ws.loaded.rows.clone();
            self.note(Note::SweepBegin { flight: f.id, target: ws.target.clone(), now: t1 });
            let mut commit = self.commit_new(ws, rows, t1, false, Some(fired));
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
        let next = util::compute_next_cron(&c.cron, at as i64).max(at as i64 + 1) as u64;
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

    fn fire_load_origin(&mut self, mut f: Flight, ctx: FireCtx) {
        let (op, revalidating) = self.load_origin(f.id, &ctx.origin);
        f.phase = Phase::FireLoadingOrigin { op, revalidating, ctx };
        self.flights.inflight.insert(f.id, f);
    }

    /// Both documents loaded: the kernel's `process_schedule` on the row
    /// beside the origin's objects, then the origin committed first.
    fn fire_run(&mut self, mut f: Flight, ctx: FireCtx, wo: Working<Promise>) {
        let Work::Fire { schedule, .. } = &f.work else { return self.fail(f, Unavailable::new("not a fire")) };
        let id = schedule.clone();
        let t = steps::clamp_now(wo.loaded.stamp, ctx.t1);
        let req = ScheduleTimeoutReq { schedule: id, occurrences: vec![Occurrence { at: ctx.at, promise_id: ctx.promise_id.clone() }], next_run_at: ctx.next };
        let mut state = KState { objects: wo.loaded.rows.clone(), schedules: ctx.ws.loaded.rows.clone(), outbox: Vec::new() };
        state.process_schedule(&req, t, &self.kcfg);
        steps::drain(&mut state, t, &self.kcfg);
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
    fn fire_advance(&mut self, mut f: Flight, ctx: FireCtx, schedules: Vec<Schedule>, t: u64) {
        let Work::Fire { schedule, fired, .. } = &f.work else { return self.fail(f, Unavailable::new("not a fire")) };
        let (id, fired) = (schedule.clone(), fired.clone());
        self.note(Note::AdvanceBegin { flight: f.id, schedule: id, now: t, at: ctx.at, next: ctx.next });
        let FireCtx { ws, .. } = ctx;
        let mut commit = self.commit_new(ws, schedules, t, false, Some(fired));
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

    // -----------------------------------------------------------------------
    // The commit
    // -----------------------------------------------------------------------

    /// The decisions before the first store call: the rows that changed,
    /// the nearest deadline, and the verified `prepare`. `did` is whether a
    /// sweep fired anything; `fired` the key whose firing this is.
    fn commit_new<R: Row>(&mut self, w: Working<R>, rows: Vec<R>, now: u64, did: bool, fired: Option<FiredKey>) -> Committing<R> {
        let changed = doc::changed(&w.loaded.rows, &rows);
        let changed_any = did || !changed.is_empty() || rows.len() != w.loaded.rows.len();
        let deadline = steps::next_deadline(&R::state_of(&rows));
        let etag = w.etag.as_ref().map(|e| e.0.clone());
        let plan = self.core.prepare(&w.target, etag.as_ref(), deadline, changed_any, fired.as_ref().map(|f| f.key.clone()));
        Committing { w, rows, changed, changed_any, now, fired, plan, step: Step::Start }
    }

    /// Drive a commit: `answer` is the store's answer to the call the
    /// commit waits on, if it waits on one. Returns with the next call
    /// issued, or the commit over.
    fn commit_advance<R: Row>(&mut self, fid: FlightId, c: &mut Committing<R>, answer: Option<StoreOutcome>) -> Progress {
        let me = self.cfg.node_id.clone();
        match std::mem::replace(&mut c.step, Step::Over) {
            Step::Start => {
                if c.changed_any {
                    // (1) the key for the new deadline, before the state that arms it
                    if let Some(at) = c.plan.arm_at() {
                        let key = Key { origin: c.w.target.clone(), at, token: self.token() };
                        let name = self.key_name(&key, &me);
                        let op = self.store(StoreCall::Put { key: name.clone(), body: Vec::new() }, Owner::Flight(fid));
                        c.step = Step::PuttingKey { op, key, name };
                        return Progress::Issued;
                    }
                    self.issue_write(fid, c, false);
                    Progress::Issued
                } else if c.fired.is_some() {
                    // Nothing was due: rewrite the document at a new version,
                    // so that no commit in flight that armed this key can
                    // land on the version it loaded; then the key goes.
                    self.issue_write(fid, c, true);
                    Progress::Issued
                } else {
                    Progress::Done(Fired::Kept)
                }
            }
            Step::PuttingKey { key, name, .. } => match answer {
                Some(StoreOutcome::Done) => {
                    self.timers.wheel.arm(key.at, name);
                    c.plan.armed(key);
                    // (2) the document
                    self.issue_write(fid, c, false);
                    Progress::Issued
                }
                Some(StoreOutcome::Failed(e)) => Progress::Failed(e),
                _ => Progress::Failed(unexpected()),
            },
            Step::Writing { mode, row_count, bytes, len, idle, .. } => match answer {
                Some(StoreOutcome::Written(etag)) => {
                    self.note(Note::DocumentWrite { mode, bytes: len });
                    // an origin's document is remembered as written; a schedule's is not cached
                    if let Some(rows) = R::promises(&c.rows) {
                        let filled_at = self.now();
                        self.remember(&c.w.target, Cached { loaded: Loaded { rows, row_count, bytes, stamp: c.now }, etag: etag.clone(), filled_at });
                    }
                    c.w.etag = Some(etag.clone());
                    if idle {
                        return self.delete_fired(fid, c);
                    }
                    // (3) the key replaced, or no longer needed
                    if let Some(key) = c.plan.to_disarm() {
                        let name = self.key_name(&key, &me);
                        let op = self.store(StoreCall::Delete { key: name.clone() }, Owner::Flight(fid));
                        c.step = Step::DeletingPrevious { op, key, name };
                        return Progress::Issued;
                    }
                    // (4) the key kept, with the version written
                    self.core.finish(&c.plan, &etag.0);
                    self.delete_fired(fid, c)
                }
                Some(StoreOutcome::Failed(e)) => Progress::Failed(e),
                _ => Progress::Failed(unexpected()),
            },
            Step::DeletingPrevious { key, name, .. } => {
                // Best effort: a key that stays fires again and is collected then.
                match answer {
                    Some(StoreOutcome::Done) => self.timers.wheel.disarm(key.at, &name),
                    Some(StoreOutcome::Failed(e)) => self.note(Note::KeyNotDeleted { key: name, error: e.to_string() }),
                    _ => {}
                }
                let etag = c.w.etag.clone().unwrap_or_else(|| Etag(String::new()));
                self.core.finish(&c.plan, &etag.0);
                self.delete_fired(fid, c)
            }
            Step::DeletingFired { key, name, .. } => match answer {
                Some(StoreOutcome::Done) => {
                    self.timers.wheel.disarm(key.at, &name);
                    Progress::Done(Fired::Deleted)
                }
                Some(StoreOutcome::Failed(e)) => {
                    self.note(Note::KeyNotDeleted { key: name, error: e.to_string() });
                    Progress::Done(Fired::Kept)
                }
                _ => Progress::Done(Fired::Kept),
            },
            Step::Over => Progress::Done(Fired::Kept),
        }
    }

    /// (5) the key fired: the write that just landed fences every commit
    /// that armed it and has not written yet.
    fn delete_fired<R: Row>(&mut self, fid: FlightId, c: &mut Committing<R>) -> Progress {
        let Some(f) = c.fired.clone() else { return Progress::Done(Fired::Kept) };
        self.core.collected(&c.w.target, &f.key);
        let name = self.key_name(&f.key, &f.by);
        let op = self.store(StoreCall::Delete { key: name.clone() }, Owner::Flight(fid));
        c.step = Step::DeletingFired { op, key: f.key, name };
        Progress::Issued
    }

    /// Write the document at a new version, conditionally on the version
    /// loaded: the rows the step changed appended, or the whole document.
    fn issue_write<R: Row>(&mut self, fid: FlightId, c: &mut Committing<R>, idle: bool) {
        let header = Header { stamp: c.now, nonce: self.token() };
        let changed: &[R] = if idle { &[] } else { &c.changed };
        let (call, mode, row_count, bytes) = match &c.w.etag {
            None => {
                let body = doc::encode(&header, &c.rows);
                let (n, b) = (c.rows.len(), body.len() as u64);
                (StoreCall::PutIfNoneMatch { key: c.w.key.clone(), body }, WriteMode::Create, n, b)
            }
            Some(etag) => {
                // a row gone — a schedule deleted — cannot be appended; the
                // document is rewritten without it
                let removed = c.w.loaded.rows.iter().any(|q| !c.rows.iter().any(|p| p.id() == q.id()));
                let stale_after = (c.w.loaded.row_count + changed.len()).saturating_sub(c.rows.len());
                let append = !removed && self.cfg.appendable && self.kcfg.compact > 0 && stale_after < self.kcfg.compact as usize;
                if append {
                    let body = doc::encode(&header, changed);
                    let (n, b) = (c.w.loaded.row_count + changed.len(), c.w.loaded.bytes + body.len() as u64);
                    (StoreCall::AppendIfMatch { key: c.w.key.clone(), offset: c.w.loaded.bytes, body, etag: etag.clone() }, WriteMode::Append, n, b)
                } else {
                    let body = doc::encode(&header, &c.rows);
                    let (n, b) = (c.rows.len(), body.len() as u64);
                    (StoreCall::PutIfMatch { key: c.w.key.clone(), body, etag: etag.clone() }, WriteMode::Rewrite, n, b)
                }
            }
        };
        let len = match &call {
            StoreCall::PutIfNoneMatch { body, .. } | StoreCall::AppendIfMatch { body, .. } | StoreCall::PutIfMatch { body, .. } => body.len(),
            _ => 0,
        };
        let op = self.store(call, Owner::Flight(fid));
        c.step = Step::Writing { op, mode, row_count, bytes, len, idle };
    }
}
