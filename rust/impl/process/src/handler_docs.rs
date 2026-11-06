//! One origin: its promises, the task inside each, and a sweep of it.
//!
//! One step runs on a document at a time; the rest queue behind it. The step
//! loads the document, decides by `verified::flight::decide` — the concrete
//! model's `handle` for a request, `sweep` for a due key — and commits by
//! `verified::flight::Sequence`: the deadline key, then the document, then
//! the key that key replaced, then the key that fired. This file names the
//! keys, builds the bytes, makes each call the sequence asks for, and
//! brings the answer back; the wheel and the cache follow the answers. A
//! lost race re-reads and decides again. A schedule's run uses the same
//! commit; the decision itself is `handler_sched`.
//!
//! The cache holds the last document this process read or wrote for an
//! origin, and is never used without asking the store.

use std::collections::{HashMap, VecDeque};

use echod_concrete::{doc_deadline, peek, Doc, Outbound, Pending};

use crate::verified::flight::{self, Act, Decided, Job, Outcome, Sequence};
use crate::verified::node::Key;
use crate::verified::{Request, Response, Schedule, TaskFenceInnerRes, TaskFenceRes};

use crate::cache::{Cache, Cached};
use crate::doc::{self, Header, Loaded, Promise, Row};
use crate::target::Target;
use crate::types::*;
use crate::{Owner, State};

/// What a flight does.
pub(crate) enum Work {
    Request { id: RequestId, kind: String, corr: String, req: Request, action_kind: Option<String>, now: u64, stage: Stage },
    /// `fired` is the key whose firing this is; none for a sweep or a fire
    /// a test asked for.
    Sweep { fired: Option<FiredKey>, now: u64 },
    Fire { schedule: String, fired: Option<FiredKey>, now: u64 },
}

/// Where a request stands when it spans two documents: a fence whose create
/// targets another origin (a detached workflow) commits the create on that
/// origin first, then the fence's check on the task's, and answers as one
/// fence. A request on one document is `Whole`.
pub(crate) enum Stage {
    Whole,
    /// The create, with the check to run on the task's document once it has
    /// committed (taken when it is submitted).
    Detached { then: Target, check: Option<Box<Request>> },
    /// The check, with the create's answer to fold into the fence's (taken
    /// when the answer goes out).
    Check { inner: Option<crate::verified::PromiseRes> },
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

/// A commit in progress: the verified sequence, and the store call it
/// asked for that is waited on.
pub(crate) struct Committing<R: Row> {
    w: Working<R>,
    rows: Vec<R>,
    changed: Vec<R>,
    now: u64,
    seq: Sequence,
    issued: Option<Issued>,
}

/// The call made for the sequence's last act, with what the answer needs.
enum Issued {
    /// A key put or deleted: the wheel follows the answer.
    Key { op: OpId, key: Key, name: String, arm: bool },
    /// The document written: the cache follows the answer.
    Write { op: OpId, mode: WriteMode, row_count: usize, bytes: u64, len: usize },
}

impl<R: Row> Committing<R> {
    /// The store call the commit waits on.
    fn expects(&self) -> Option<OpId> {
        match &self.issued {
            Some(Issued::Key { op, .. }) | Some(Issued::Write { op, .. }) => Some(*op),
            None => None,
        }
    }
}

pub(crate) enum Progress {
    Issued,
    Done(Fired),
    Failed(StoreError),
}

/// How many due steps one sweep runs before it commits. A document with
/// more due is committed with its nearest deadline past, which arms a key
/// that fires at once.
pub(crate) const SWEEP_STEPS: u64 = 256;

/// What a committed step answers with.
pub(crate) struct Done {
    response: Option<Response>,
    /// Why the request was refused, in the protocol's words, if it was.
    why: Option<String>,
    /// What the step tells workers once its write lands.
    outbox: Vec<(String, Message)>,
    did: bool,
}

/// A fire past its decision: the schedule as loaded and as advanced, the
/// occurrence due, and the origin it is born in.
pub(crate) struct FireCtx {
    pub(crate) ws: Working<Schedule>,
    pub(crate) row: Schedule,
    pub(crate) advanced: Vec<Schedule>,
    pub(crate) pending: Pending,
    pub(crate) t1: u64,
    pub(crate) origin: String,
    pub(crate) next: u64,
}

/// What a step's notes say to whom: an `Execute` goes to the address the
/// task's promise is targeted at; an `Unblock` to the listener's.
pub(crate) fn dispatches(doc: &Doc, notes: Vec<Outbound>) -> Vec<(String, Message)> {
    notes
        .into_iter()
        .filter_map(|n| match n {
            Outbound::Execute { id, version } => {
                let obj = peek(doc, &id)?;
                let address = crate::reason::target_of(&obj.promise.tags)?.to_string();
                Some((address, Message::Execute { task_id: id, version }))
            }
            Outbound::Unblock { address, promise } => Some((address, Message::Unblock(promise))),
        })
        .collect()
}

pub(crate) enum Phase {
    Idle,
    Loading { op: OpId, revalidating: Option<Cached> },
    Origin { commit: Committing<Promise>, done: Done },
    Schedule { commit: Committing<Schedule>, done: Done },
    FireLoadingSchedule { op: OpId },
    FireWaitingOrigin(FireCtx),
    FireLoadingOrigin { op: OpId, revalidating: Option<Cached>, ctx: FireCtx },
    FireIdle { commit: Committing<Schedule> },
    FireOrigin { commit: Committing<Promise>, ctx: FireCtx, t: u64 },
    FireSchedule { commit: Committing<Schedule> },
}

impl Phase {
    /// The store call the flight waits on.
    fn expects(&self) -> Option<OpId> {
        match self {
            Phase::Idle | Phase::FireWaitingOrigin(_) => None,
            Phase::Loading { op, .. } | Phase::FireLoadingSchedule { op } | Phase::FireLoadingOrigin { op, .. } => Some(*op),
            Phase::Origin { commit, .. } | Phase::FireOrigin { commit, .. } => commit.expects(),
            Phase::Schedule { commit, .. } | Phase::FireIdle { commit } | Phase::FireSchedule { commit } => commit.expects(),
        }
    }
}

pub(crate) struct Flight {
    pub(crate) id: FlightId,
    pub(crate) target: Target,
    pub(crate) work: Work,
    pub(crate) attempt: u32,
    pub(crate) phase: Phase,
    pub(crate) firing: Option<Firing>,
    /// Started by `debug.tick`, which hears how it ended.
    pub(crate) debug: bool,
    /// A sweep that fired nothing, or a fire that found nothing due.
    pub(crate) idle: bool,
}

pub(crate) enum Queued {
    Work(Box<(Target, Work, Option<Firing>, bool)>),
    Waiter(FlightId),
}

#[derive(Default)]
pub(crate) struct Slot {
    pub(crate) busy: Option<FlightId>,
    pub(crate) queue: VecDeque<Queued>,
}

pub(crate) struct Flights {
    pub(crate) slots: HashMap<String, Slot>,
    pub(crate) inflight: HashMap<FlightId, Flight>,
    pub(crate) max_retries: u32,
}

impl Flights {
    pub fn new() -> Self {
        Self { slots: HashMap::new(), inflight: HashMap::new(), max_retries: 8 }
    }

}

pub(crate) fn unexpected() -> StoreError {
    StoreError::Unavailable("the store answered something else".into())
}

impl State {
    // -----------------------------------------------------------------------
    // Slots: one flight per document
    // -----------------------------------------------------------------------

    /// Run `work` on `target`, after whatever is on it already.
    pub(crate) fn submit(&mut self, target: Target, work: Work, firing: Option<Firing>, debug: bool) {
        let name = target.name();
        if let Work::Sweep { now, .. } = &work {
            let flight = self.next_flight;
            self.note(Note::SweepBegin { flight, target: name.clone(), now: *now });
        }
        let slot = self.flights.slots.entry(name).or_default();
        if slot.busy.is_some() {
            slot.queue.push_back(Queued::Work(Box::new((target, work, firing, debug))));
            return;
        }
        self.start(target, work, firing, debug);
    }

    fn start(&mut self, target: Target, work: Work, firing: Option<Firing>, debug: bool) {
        let id = self.next_flight;
        self.next_flight += 1;
        self.flights.slots.entry(target.name()).or_default().busy = Some(id);
        let f = Flight { id, target, work, attempt: 0, phase: Phase::Idle, firing, debug, idle: false };
        self.begin(f);
    }

    /// The slot of `name` is free: whatever waits on it goes next.
    pub(crate) fn release(&mut self, name: &str) {
        let Some(slot) = self.flights.slots.get_mut(name) else { return };
        slot.busy = None;
        match slot.queue.pop_front() {
            None => {
                self.flights.slots.remove(name);
            }
            Some(Queued::Work(q)) => {
                let (target, work, firing, debug) = *q;
                self.start(target, work, firing, debug);
            }
            Some(Queued::Waiter(fid)) => {
                slot.busy = Some(fid);
                if let Some(mut f) = self.flights.inflight.remove(&fid) {
                    match std::mem::replace(&mut f.phase, Phase::Idle) {
                        Phase::FireWaitingOrigin(ctx) => self.fire_load_origin(f, ctx),
                        _ => self.fail(f, "a flight waited for a slot it did not need".to_string()),
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
            self.fail(f, format!("too many races on the {what}"));
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
                let Work::Fire { schedule, .. } = &f.work else { return self.fail(f, "not a fire".to_string()) };
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
            Phase::FireOrigin { mut commit, ctx, t } => match self.commit_advance(fid, &mut commit, Some(outcome)) {
                Progress::Issued => {
                    f.phase = Phase::FireOrigin { commit, ctx, t };
                    self.flights.inflight.insert(fid, f);
                }
                Progress::Done(_) => {
                    self.note(Note::FireEnd { flight: fid, committed: true });
                    self.note(Note::Commit(CommitOutcome::Committed));
                    self.release(&ctx.origin);
                    self.fire_advance(f, ctx, t);
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
            _ => self.fail(f, "an answer the flight did not wait for".to_string()),
        }
    }

    // -----------------------------------------------------------------------
    // Loading
    // -----------------------------------------------------------------------

    /// Ask for an origin's document: revalidated against the store when
    /// the cache holds a version, read in full otherwise.
    pub(crate) fn load_origin(&mut self, fid: FlightId, origin: &str) -> (OpId, Option<Cached>) {
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
    fn loaded_origin(&mut self, origin: &str, revalidating: Option<Cached>, outcome: StoreOutcome) -> Result<Working<Promise>, String> {
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
                let loaded: Loaded<Promise> = doc::decode(&bytes)?;
                self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone(), filled_at: now });
                Ok(w(loaded, Some(etag)))
            }
            (None, StoreOutcome::Got(None)) => Ok(w(Loaded::empty(), None)),
            (None, StoreOutcome::Got(Some((bytes, etag)))) => {
                let loaded: Loaded<Promise> = doc::decode(&bytes)?;
                self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone(), filled_at: now });
                Ok(w(loaded, Some(etag)))
            }
            (_, StoreOutcome::Failed(e)) => Err(e.to_string()),
            _ => Err(unexpected().to_string()),
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

    /// The step: `verified::flight::decide`, the concrete model's step on
    /// the document the rows make, decided no earlier than the last step
    /// on the document. A request is `handle`; a due key is `sweep`, every
    /// due step on the document up to `SWEEP_STEPS`. A lost race runs this
    /// again on what it re-read.
    pub(crate) fn decide<R: Row>(&mut self, work: &Work, w: Working<R>) -> (Committing<R>, Done) {
        let doc = R::doc_of(&w.loaded.rows);
        let now = doc::clamp_now(w.loaded.stamp, work.now());
        let job = match work {
            Work::Request { req, .. } => Job::Request(req.clone()),
            Work::Sweep { .. } => Job::Sweep,
            Work::Fire { .. } => Job::Fire,
        };
        let Decided { doc, response, notes, .. } = flight::decide(job, doc, now, self.cfg.retry_timeout, SWEEP_STEPS);
        let why = match (work, &response) {
            (Work::Request { req, kind, .. }, Some(r)) => {
                let status = crate::reason::status_of(r);
                (status >= 400).then(|| crate::reason::reason_for(kind, req, status, &doc))
            }
            _ => None,
        };
        let outbox = dispatches(&doc, notes);
        let deadline = doc_deadline(&doc);
        let rows = R::rows_of(doc);
        let fired = match work {
            Work::Sweep { fired, .. } => fired.clone(),
            _ => None,
        };
        let commit = self.commit_new(w, rows, deadline, now, fired);
        let did = matches!(work, Work::Sweep { .. }) && commit.seq.changed;
        (commit, Done { response, why, outbox, did })
    }

    /// A committed step: the messages out, the answer back.
    pub(crate) fn committed(&mut self, f: Flight, done: Done, fired: Fired) {
        self.note(Note::Commit(CommitOutcome::Committed));
        let Done { response, why, outbox, did } = done;
        for (address, message) in outbox {
            self.send(address, message);
        }
        let mut f = f;
        match &mut f.work {
            Work::Request { id, kind, corr, action_kind, now, stage: Stage::Detached { then, check }, .. } => {
                // The create has landed; the fence's check follows on the task's document.
                match (response, check.take()) {
                    (Some(Response::Promise(inner)), Some(check)) => {
                        let work = Work::Request { id: *id, kind: kind.clone(), corr: corr.clone(), req: *check, action_kind: action_kind.clone(), now: *now, stage: Stage::Check { inner: Some(inner) } };
                        let then = then.clone();
                        self.submit(then, work, None, f.debug);
                    }
                    _ => self.emit(Effect::Reply { id: *id, response: Err("no answer".to_string()) }),
                }
            }
            Work::Request { id, kind, corr, action_kind, stage: Stage::Check { inner }, .. } => {
                // The fence's answer: the check's status, with the create's record inside when it held.
                let response = match (response, inner.take()) {
                    (Some(Response::Status(st)), Some(inner)) => {
                        let action = (st.status == 200).then_some(TaskFenceInnerRes::Create(inner));
                        let response = Response::TaskFence(TaskFenceRes { status: st.status, action });
                        Ok(Answer::Step { kind: kind.clone(), corr: corr.clone(), action_kind: action_kind.clone(), response, why })
                    }
                    _ => Err("no answer".to_string()),
                };
                self.emit(Effect::Reply { id: *id, response });
            }
            Work::Request { id, kind, corr, action_kind, stage: Stage::Whole, .. } => {
                let response = match response {
                    Some(response) => Ok(Answer::Step { kind: kind.clone(), corr: corr.clone(), action_kind: action_kind.clone(), response, why }),
                    None => Err("no answer".to_string()),
                };
                self.emit(Effect::Reply { id: *id, response });
            }
            Work::Sweep { .. } => {
                self.note(Note::Sweep(if did { SweepOutcome::Fired } else { SweepOutcome::Idle }));
                self.note(Note::SweepEnd { flight: f.id, committed: true });
            }
            Work::Fire { .. } => {}
        }
        f.idle = !did;
        self.finish(f, Ok(fired));
    }

    /// The commit's store call failed: a lost race re-decides, anything
    /// else ends the flight with nothing cached.
    pub(crate) fn commit_failed(&mut self, f: Flight, e: StoreError) {
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
                self.fail(f, e.to_string());
            }
        }
    }

    /// The flight ends without a commit.
    pub(crate) fn fail(&mut self, f: Flight, e: String) {
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
    pub(crate) fn finish(&mut self, f: Flight, r: Result<Fired, String>) {
        let name = f.target.name();
        self.release(&name);
        if let Some(firing) = f.firing {
            let now = self.now();
            self.timer_fired(firing, now, r);
        }
        if f.debug {
            self.debug_flight_done(&f.work, f.idle);
        }
    }

    pub(crate) fn send(&mut self, address: String, message: Message) {
        self.emit(Effect::Send { address, message });
    }

    // -----------------------------------------------------------------------
    // The commit
    // -----------------------------------------------------------------------

    /// The decisions before the first store call: the rows that changed,
    /// and the verified sequence, planned from the document's nearest
    /// deadline. `fired` is the key whose firing this is.
    pub(crate) fn commit_new<R: Row>(&mut self, w: Working<R>, rows: Vec<R>, deadline: Option<u64>, now: u64, fired: Option<FiredKey>) -> Committing<R> {
        let changed = doc::changed(&w.loaded.rows, &rows);
        let changed_any = !changed.is_empty() || rows.len() != w.loaded.rows.len();
        let etag = w.etag.as_ref().map(|e| e.0.clone());
        let token = self.token();
        let seq = Sequence::new(&self.node.core, &w.target, etag.as_ref(), deadline, changed_any, fired, token);
        Committing { w, rows, changed, now, seq, issued: None }
    }

    /// Drive a commit: `answer` is the store's answer to the call the
    /// commit waits on, if it waits on one. The wheel and the cache follow
    /// the answer; the sequence decides the next call; this makes it.
    /// Returns with that call issued, or the commit over.
    pub(crate) fn commit_advance<R: Row>(&mut self, fid: FlightId, c: &mut Committing<R>, answer: Option<StoreOutcome>) -> Progress {
        if let Some(issued) = c.issued.take() {
            self.answered(c, issued, answer.as_ref());
        }
        match c.seq.advance(&mut self.node.core, answer.as_ref()) {
            Outcome::Act(Act::PutKey(key)) => {
                let name = self.key_name(&key, &self.cfg.node_id.clone());
                let op = self.store(StoreCall::Put { key: name.clone(), body: Vec::new() }, Owner::Flight(fid));
                c.issued = Some(Issued::Key { op, key, name, arm: true });
                Progress::Issued
            }
            Outcome::Act(Act::Write { cond, idle }) => {
                self.issue_write(fid, c, cond, idle);
                Progress::Issued
            }
            Outcome::Act(Act::DeleteKey { key, by }) => {
                let name = self.key_name(&key, &by);
                let op = self.store(StoreCall::Delete { key: name.clone() }, Owner::Flight(fid));
                c.issued = Some(Issued::Key { op, key, name, arm: false });
                Progress::Issued
            }
            Outcome::Act(Act::Done { deleted }) => Progress::Done(if deleted { Fired::Deleted } else { Fired::Kept }),
            Outcome::Failed(Some(e)) => Progress::Failed(e),
            Outcome::Failed(None) => Progress::Failed(unexpected()),
        }
    }

    /// What follows from the answer to the last call, outside the sequence:
    /// a key put is armed in the wheel, a key deleted leaves it (a delete
    /// that failed is noted; the key fires again and is collected then), a
    /// document written is remembered.
    fn answered<R: Row>(&mut self, c: &mut Committing<R>, issued: Issued, answer: Option<&StoreOutcome>) {
        match (issued, answer) {
            (Issued::Key { key, name, arm: true, .. }, Some(StoreOutcome::Done)) => self.timers.wheel.arm(key.at, name),
            (Issued::Key { key, name, arm: false, .. }, Some(StoreOutcome::Done)) => self.timers.wheel.disarm(key.at, &name),
            (Issued::Key { name, arm: false, .. }, Some(StoreOutcome::Failed(e))) => self.note(Note::KeyNotDeleted { key: name, error: e.to_string() }),
            (Issued::Write { mode, row_count, bytes, len, .. }, Some(StoreOutcome::Written(etag))) => {
                self.note(Note::DocumentWrite { mode, bytes: len });
                // an origin's document is remembered as written; a schedule's is not cached
                if let Some(rows) = R::promises(&c.rows) {
                    let filled_at = self.now();
                    self.remember(&c.w.target, Cached { loaded: Loaded { rows, row_count, bytes, stamp: c.now }, etag: etag.clone(), filled_at });
                }
                c.w.etag = Some(etag.clone());
            }
            _ => {}
        }
    }

    /// Write the document at a new version, conditionally on `cond`, the
    /// version loaded: the rows the step changed appended, or the whole
    /// document.
    fn issue_write<R: Row>(&mut self, fid: FlightId, c: &mut Committing<R>, cond: Option<String>, idle: bool) {
        let header = Header { stamp: c.now, nonce: self.token() };
        let changed: &[R] = if idle { &[] } else { &c.changed };
        let (call, mode, row_count, bytes) = match cond {
            None => {
                let body = doc::encode(&header, &c.rows);
                let (n, b) = (c.rows.len(), body.len() as u64);
                (StoreCall::PutIfNoneMatch { key: c.w.key.clone(), body }, WriteMode::Create, n, b)
            }
            Some(etag) => {
                let etag = Etag(etag);
                // a row gone — a schedule deleted — cannot be appended; the
                // document is rewritten without it
                let removed = c.w.loaded.rows.iter().any(|q| !c.rows.iter().any(|p| p.id() == q.id()));
                let stale_after = (c.w.loaded.row_count + changed.len()).saturating_sub(c.rows.len());
                let append = !removed && self.cfg.appendable && self.cfg.compact > 0 && stale_after < self.cfg.compact as usize;
                if append {
                    let body = doc::encode(&header, changed);
                    let (n, b) = (c.w.loaded.row_count + changed.len(), c.w.loaded.bytes + body.len() as u64);
                    (StoreCall::AppendIfMatch { key: c.w.key.clone(), offset: c.w.loaded.bytes, body, etag }, WriteMode::Append, n, b)
                } else {
                    let body = doc::encode(&header, &c.rows);
                    let (n, b) = (c.rows.len(), body.len() as u64);
                    (StoreCall::PutIfMatch { key: c.w.key.clone(), body, etag }, WriteMode::Rewrite, n, b)
                }
            }
        };
        let len = match &call {
            StoreCall::PutIfNoneMatch { body, .. } | StoreCall::AppendIfMatch { body, .. } | StoreCall::PutIfMatch { body, .. } => body.len(),
            _ => 0,
        };
        let op = self.store(call, Owner::Flight(fid));
        c.issued = Some(Issued::Write { op, mode, row_count, bytes, len });
    }
}
