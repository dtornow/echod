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
//!
//! Every method has its `spec_*` twin: the step as the specification
//! states it, over `StateSpec`. Verus checks each method computes its twin.


use vstd::prelude::*;

use crate::verified::runtime::copy;
use crate::concrete::{
    advance_stored, body_len, clone_stored, peek, stored_body, stored_is_workflow, DocumentBody,
    Outbound, StoredDocument,
};

use crate::verified::flight::{self, Act, Decided, FiredKey, Job, Outcome, Sequence};
use crate::verified::node::Key;
use crate::verified::table::Table;
use crate::verified::text::{concat, copy_string, text};
use crate::verified::{Request, Response, TaskFenceInnerRes, TaskFenceRes};

use crate::cache::Cached;
use crate::document::{self, Loaded};
use crate::state::{Owner, State};
use crate::target::Target;
use crate::types::*;

#[cfg(verus_keep_ghost)]
use crate::cache::CachedSpec;
#[cfg(verus_keep_ghost)]
use crate::document::LoadedSpec;
#[cfg(verus_keep_ghost)]
use crate::keys::*;
#[cfg(verus_keep_ghost)]
use crate::state::*;
#[cfg(verus_keep_ghost)]
use crate::state_node::NodeSpec;
#[cfg(verus_keep_ghost)]
use crate::state_timers::{TimerWheelSpec, TimersSpec};
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;
#[cfg(verus_keep_ghost)]
use crate::verified::flight_spec::*;
#[cfg(verus_keep_ghost)]
use crate::verified::node::AKey;
#[cfg(verus_keep_ghost)]
use crate::verified::PromiseResSpec;
#[cfg(verus_keep_ghost)]
use crate::concrete::document::{
    notes_v, spec_body_deadline, spec_workflow_map, DocumentBodyV, NoteV, ScheduleDocumentV,
    StoredDocumentV, WorkflowDocumentV,
};
#[cfg(verus_keep_ghost)]
use crate::concrete::store::{EtagSpec, StoreErrorSpec, StoreReqSpec};
#[cfg(verus_keep_ghost)]
use echod_types::spec::AResponse;

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionFiringV as FiringSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionWorkingV as WorkingSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionCommittingV as CommittingSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionDoneV as DoneSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionFireCtxV as FireCtxSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionFlightV as FlightSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionDocumentSlotV as SlotSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionFlightsV as FlightsSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionWorkV as WorkSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionStageV as StageSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionIssuedV as IssuedSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionProgressV as ProgressSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionPhaseV as PhaseSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionQueuedV as QueuedSpec;

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_handler_docs_spec_flights_new as spec_flights_new,
    production_handler_docs_spec_empty_slot as spec_empty_slot,
    production_handler_docs_spec_slot_of as spec_slot_of,
    production_handler_docs_spec_with_slot as spec_with_slot,
    production_handler_docs_spec_without_slot as spec_without_slot,
    production_handler_docs_spec_inflight as spec_inflight,
    production_handler_docs_spec_take_flight as spec_take_flight,
    production_handler_docs_spec_dispatch as spec_dispatch,
    production_handler_docs_spec_dispatches as spec_dispatches,
    production_handler_docs_spec_submit as spec_submit,
    production_handler_docs_spec_start as spec_start,
    production_handler_docs_spec_release as spec_release,
    production_handler_docs_spec_resume as spec_resume,
    production_handler_docs_spec_begin as spec_begin,
    production_handler_docs_spec_retry as spec_retry,
    production_handler_docs_spec_flight_completed as spec_flight_completed,
    production_handler_docs_spec_answered_phase as spec_answered_phase,
    production_handler_docs_spec_answered_loading as spec_answered_loading,
    production_handler_docs_spec_answered_origin as spec_answered_origin,
    production_handler_docs_spec_answered_schedule as spec_answered_schedule,
    production_handler_docs_spec_answered_fire_loading_schedule as spec_answered_fire_loading_schedule,
    production_handler_docs_spec_answered_fire_loading_origin as spec_answered_fire_loading_origin,
    production_handler_docs_spec_answered_fire_idle as spec_answered_fire_idle,
    production_handler_docs_spec_answered_fire_origin as spec_answered_fire_origin,
    production_handler_docs_spec_answered_fire_schedule as spec_answered_fire_schedule,
    production_handler_docs_spec_load_origin as spec_load_origin,
    production_handler_docs_spec_working as spec_working,
    production_handler_docs_spec_loaded_origin as spec_loaded_origin,
    production_handler_docs_spec_run_origin as spec_run_origin,
    production_handler_docs_spec_decide as spec_decide,
    production_handler_docs_spec_send_all as spec_send_all,
    production_handler_docs_spec_committed as spec_committed,
    production_handler_docs_spec_commit_failed as spec_commit_failed,
    production_handler_docs_spec_fail as spec_fail,
    production_handler_docs_spec_finish as spec_finish,
    production_handler_docs_spec_commit_new as spec_commit_new,
    production_handler_docs_spec_commit_advance as spec_commit_advance,
    production_handler_docs_spec_answered as spec_answered,
    production_handler_docs_spec_issue_write as spec_issue_write,
};

verus! {
#[cfg(verus_keep_ghost)]
impl DeepView for Firing {
    type V = FiringSpec;
    open spec fn deep_view(&self) -> FiringSpec {
        FiringSpec {
            key: self.key.deep_view(),
            at: self.at.deep_view(),
            kind: self.kind.deep_view(),
            lag: self.lag.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Firing {
    type V = FiringSpec;
    open spec fn view(&self) -> FiringSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Working {
    type V = WorkingSpec;
    open spec fn deep_view(&self) -> WorkingSpec {
        WorkingSpec {
            target: self.target.deep_view(),
            key: self.key.deep_view(),
            loaded: self.loaded.deep_view(),
            etag: self.etag.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Working {
    type V = WorkingSpec;
    open spec fn view(&self) -> WorkingSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Committing {
    type V = CommittingSpec;
    open spec fn deep_view(&self) -> CommittingSpec {
        CommittingSpec {
            w: self.w.deep_view(),
            after: self.after.deep_view(),
            now: self.now.deep_view(),
            seq: self.seq.deep_view(),
            issued: self.issued.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Committing {
    type V = CommittingSpec;
    open spec fn view(&self) -> CommittingSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Done {
    type V = DoneSpec;
    open spec fn deep_view(&self) -> DoneSpec {
        DoneSpec {
            response: self.response.deep_view(),
            why: self.why.deep_view(),
            outbox: self.outbox.deep_view(),
            did: self.did.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Done {
    type V = DoneSpec;
    open spec fn view(&self) -> DoneSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for FireCtx {
    type V = FireCtxSpec;
    open spec fn deep_view(&self) -> FireCtxSpec {
        FireCtxSpec {
            ws: self.ws.deep_view(),
            row: self.row.deep_view(),
            advanced: self.advanced.deep_view(),
            pending: self.pending.deep_view(),
            t1: self.t1.deep_view(),
            origin: self.origin.deep_view(),
            next: self.next.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for FireCtx {
    type V = FireCtxSpec;
    open spec fn view(&self) -> FireCtxSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Flight {
    type V = FlightSpec;
    open spec fn deep_view(&self) -> FlightSpec {
        FlightSpec {
            id: self.id.deep_view(),
            target: self.target.deep_view(),
            work: self.work.deep_view(),
            attempt: self.attempt.deep_view(),
            phase: self.phase.deep_view(),
            firing: self.firing.deep_view(),
            debug: self.debug.deep_view(),
            idle: self.idle.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Flight {
    type V = FlightSpec;
    open spec fn view(&self) -> FlightSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Slot {
    type V = SlotSpec;
    open spec fn deep_view(&self) -> SlotSpec {
        SlotSpec {
            busy: self.busy.deep_view(),
            queue: self.queue.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Slot {
    type V = SlotSpec;
    open spec fn view(&self) -> SlotSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Flights {
    type V = FlightsSpec;
    open spec fn deep_view(&self) -> FlightsSpec {
        FlightsSpec {
            slots: self.slots.deep_view(),
            inflight: self.inflight.deep_view(),
            max_retries: self.max_retries.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Flights {
    type V = FlightsSpec;
    open spec fn view(&self) -> FlightsSpec { self.deep_view() }
}


// ---------------------------------------------------------------------------
// What a flight is
// ---------------------------------------------------------------------------

/// What a flight does.
pub enum Work {
    Request { id: RequestId, kind: String, corr: String, req: Request, action_kind: Option<String>, now: u64, stage: Stage },
    /// `fired` is the key whose firing this is; none for a sweep or a fire
    /// a test asked for.
    Sweep { fired: Option<FiredKey>, now: u64 },
    Fire { schedule: String, fired: Option<FiredKey>, now: u64 },
}



#[cfg(verus_keep_ghost)]
impl DeepView for Work {
    type V = WorkSpec;
    open spec fn deep_view(&self) -> WorkSpec {
        match self {
            Work::Request { id, kind, corr, req, action_kind, now, stage } => WorkSpec::Request {
                id: *id, kind: kind@, corr: corr@, req: *req, action_kind: action_kind.deep_view(), now: *now, stage: stage.deep_view(),
            },
            Work::Sweep { fired, now } => WorkSpec::Sweep { fired: fired.deep_view(), now: *now },
            Work::Fire { schedule, fired, now } => WorkSpec::Fire { schedule: schedule@, fired: fired.deep_view(), now: *now },
        }
    }
}



impl Work {
    pub fn now(&self) -> (r: u64)
        ensures
            r == self.deep_view().now(),
    {
        match self {
            Work::Request { now, .. } | Work::Sweep { now, .. } | Work::Fire { now, .. } => *now,
        }
    }
}

/// Where a request stands when it spans two documents: a fence whose create
/// targets another origin (a detached workflow) commits the create on that
/// origin first, then the fence's check on the task's, and answers as one
/// fence. A request on one document is `Whole`.
pub enum Stage {
    Whole,
    /// The create, with the check to run on the task's document once it has
    /// committed.
    Detached { then: Target, check: Option<Request> },
    /// The check, with the create's answer to fold into the fence's.
    Check { inner: Option<crate::verified::PromiseRes> },
}



#[cfg(verus_keep_ghost)]
impl DeepView for Stage {
    type V = StageSpec;
    open spec fn deep_view(&self) -> StageSpec {
        match self {
            Stage::Whole => StageSpec::Whole,
            Stage::Detached { then, check } => StageSpec::Detached { then: then.deep_view(), check: *check },
            Stage::Check { inner } => StageSpec::Check { inner: inner.deep_view() },
        }
    }
}

/// The key that fired a flight, for the timers when it ends.
pub struct Firing {
    pub key: String,
    pub at: u64,
    pub kind: TimerKind,
    pub lag: u64,
}

impl Firing {
    pub fn copy(&self) -> (r: Firing)
        ensures
            r.deep_view() == self.deep_view(),
    {
        Firing { key: copy_string(&self.key), at: self.at, kind: self.kind, lag: self.lag }
    }
}

/// The document a flight works on.
pub struct Working {
    /// The target's name.
    pub target: String,
    /// The object's key.
    pub key: String,
    pub loaded: Loaded,
    pub etag: Option<Etag>,
}

/// A commit in progress: the verified sequence, and the store call it
/// asked for that is waited on.
pub struct Committing {
    pub w: Working,
    /// The document as the step left it.
    pub after: StoredDocument,
    pub now: u64,
    pub seq: Sequence,
    pub issued: Option<Issued>,
}

/// The call made for the sequence's last act, with what the answer needs.
pub enum Issued {
    /// A key put or deleted: the wheel follows the answer.
    Key { op: OpId, key: Key, name: String, arm: bool },
    /// The document written: the cache follows the answer.
    Write { op: OpId, mode: WriteMode, change_count: usize, bytes: u64, len: usize },
}



#[cfg(verus_keep_ghost)]
impl DeepView for Issued {
    type V = IssuedSpec;
    open spec fn deep_view(&self) -> IssuedSpec {
        match self {
            Issued::Key { op, key, name, arm } => IssuedSpec::Key { op: *op, key: key@, name: name@, arm: *arm },
            Issued::Write { op, mode, change_count, bytes, len } => IssuedSpec::Write { op: *op, mode: *mode, change_count: *change_count, bytes: *bytes, len: *len },
        }
    }
}



impl Committing {
    pub fn expects(&self) -> (r: Option<OpId>)
        ensures
            r == self.deep_view().expects(),
    {
        match &self.issued {
            Some(Issued::Key { op, .. }) | Some(Issued::Write { op, .. }) => Some(*op),
            None => None,
        }
    }
}

pub enum Progress {
    Issued,
    Done(Fired),
    Failed(StoreError),
}



#[cfg(verus_keep_ghost)]
impl DeepView for Progress {
    type V = ProgressSpec;
    open spec fn deep_view(&self) -> ProgressSpec {
        match self {
            Progress::Issued => ProgressSpec::Issued,
            Progress::Done(f) => ProgressSpec::Done(*f),
            Progress::Failed(e) => ProgressSpec::Failed(e.deep_view()),
        }
    }
}

/// How many due steps one sweep runs before it commits. A document with
/// more due is committed with its nearest deadline past, which arms a key
/// that fires at once.
pub const SWEEP_STEPS: u64 = crate::concrete::document::REQUEST_SWEEP_STEPS;

/// What a committed step answers with.
pub struct Done {
    pub response: Option<Response>,
    /// Why the request was refused, in the protocol's words, if it was.
    pub why: Option<String>,
    /// What the step tells workers once its write lands.
    pub outbox: Vec<(String, Message)>,
    pub did: bool,
}

/// A fire past its decision: the schedule as loaded and as advanced, the
/// occurrence due, and the origin it is born in.
pub struct FireCtx {
    pub ws: Working,
    pub row: crate::verified::Schedule,
    pub advanced: DocumentBody,
    pub pending: crate::concrete::Pending,
    pub t1: u64,
    pub origin: String,
    pub next: Option<u64>,
}

pub enum Phase {
    Idle,
    Loading { op: OpId, revalidating: Option<Cached> },
    Origin { commit: Committing, done: Done },
    Schedule { commit: Committing, done: Done },
    FireLoadingSchedule { op: OpId },
    FireWaitingOrigin(FireCtx),
    FireLoadingOrigin { op: OpId, revalidating: Option<Cached>, ctx: FireCtx },
    FireIdle { commit: Committing },
    FireOrigin { commit: Committing, ctx: FireCtx, t: u64 },
    FireSchedule { commit: Committing },
}



#[cfg(verus_keep_ghost)]
impl DeepView for Phase {
    type V = PhaseSpec;
    open spec fn deep_view(&self) -> PhaseSpec {
        match self {
            Phase::Idle => PhaseSpec::Idle,
            Phase::Loading { op, revalidating } => PhaseSpec::Loading { op: *op, revalidating: revalidating.deep_view() },
            Phase::Origin { commit, done } => PhaseSpec::Origin { commit: commit.deep_view(), done: done.deep_view() },
            Phase::Schedule { commit, done } => PhaseSpec::Schedule { commit: commit.deep_view(), done: done.deep_view() },
            Phase::FireLoadingSchedule { op } => PhaseSpec::FireLoadingSchedule { op: *op },
            Phase::FireWaitingOrigin(ctx) => PhaseSpec::FireWaitingOrigin(ctx.deep_view()),
            Phase::FireLoadingOrigin { op, revalidating, ctx } => PhaseSpec::FireLoadingOrigin { op: *op, revalidating: revalidating.deep_view(), ctx: ctx.deep_view() },
            Phase::FireIdle { commit } => PhaseSpec::FireIdle { commit: commit.deep_view() },
            Phase::FireOrigin { commit, ctx, t } => PhaseSpec::FireOrigin { commit: commit.deep_view(), ctx: ctx.deep_view(), t: *t },
            Phase::FireSchedule { commit } => PhaseSpec::FireSchedule { commit: commit.deep_view() },
        }
    }
}



impl Phase {
    pub fn expects(&self) -> (r: Option<OpId>)
        ensures
            r == self.deep_view().expects(),
    {
        match self {
            Phase::Idle | Phase::FireWaitingOrigin(_) => None,
            Phase::Loading { op, .. } | Phase::FireLoadingSchedule { op } | Phase::FireLoadingOrigin { op, .. } => Some(*op),
            Phase::Origin { commit, .. } | Phase::FireOrigin { commit, .. } => commit.expects(),
            Phase::Schedule { commit, .. } | Phase::FireIdle { commit } | Phase::FireSchedule { commit } => commit.expects(),
        }
    }
}

pub struct Flight {
    pub id: FlightId,
    pub target: Target,
    pub work: Work,
    pub attempt: u32,
    pub phase: Phase,
    pub firing: Option<Firing>,
    /// Started by `debug.tick`, which hears how it ended.
    pub debug: bool,
    /// A sweep that fired nothing, or a fire that found nothing due.
    pub idle: bool,
}

pub enum Queued {
    Work { target: Target, work: Work, firing: Option<Firing>, debug: bool },
    Waiter(FlightId),
}



#[cfg(verus_keep_ghost)]
impl DeepView for Queued {
    type V = QueuedSpec;
    open spec fn deep_view(&self) -> QueuedSpec {
        match self {
            Queued::Work { target, work, firing, debug } => QueuedSpec::Work { target: target.deep_view(), work: work.deep_view(), firing: firing.deep_view(), debug: *debug },
            Queued::Waiter(f) => QueuedSpec::Waiter(*f),
        }
    }
}

/// One document's lane: the flight on it, and the ones waiting.
pub struct Slot {
    pub busy: Option<FlightId>,
    pub queue: Vec<Queued>,
}

pub struct Flights {
    pub slots: Table<String, Slot>,
    pub inflight: Table<FlightId, Flight>,
    pub max_retries: u32,
}



impl Flights {
    pub fn new() -> (r: Flights)
        ensures
            r.deep_view() == spec_flights_new(),
    {
        Flights { slots: Table::new(), inflight: Table::new(), max_retries: 8 }
    }
}



/// The slot of `name`, or an empty one.






/// `f` in flight.




// ---------------------------------------------------------------------------
// What a step's notes say to whom
// ---------------------------------------------------------------------------

/// An `Execute` goes to the address the task's promise is targeted at; an
/// `Unblock` to the listener's.




pub fn dispatches(doc: &DocumentBody, notes: &Vec<Outbound>) -> (r: Vec<(String, Message)>)
    ensures
        r.deep_view() == spec_dispatches(doc@, notes_v(notes@)),
{
    let ghost nv = notes_v(notes@);
    let mut out: Vec<(String, Message)> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(out.deep_view() =~= Seq::<(Seq<char>, MessageSpec)>::empty());
        assert(nv.take(0) =~= Seq::<NoteV>::empty());
    }
    while i < notes.len()
        invariant
            i <= notes.len(),
            nv == notes_v(notes@),
            nv.len() == notes.len(),
            out.deep_view() == spec_dispatches(doc@, nv.take(i as int)),
        decreases notes.len() - i,
    {
        let ghost before = out.deep_view();
        proof {
            assert(nv[i as int] == notes@[i as int]@);
            crate::concrete::lemma_outbound_view(&notes@[i as int]);
        }
        match &notes[i] {
            Outbound::Execute { id, version } => {
                match peek(doc, id) {
                    Some(obj) => {
                        proof {
                            crate::concrete::lemma_obj_view(&obj);
                        }
                        match crate::reason::target_of(&obj.promise.tags) {
                            Some(address) => {
                                out.push((address, Message::Execute { task_id: copy_string(id), version: *version }));
                            },
                            None => {},
                        }
                    },
                    None => {},
                }
            },
            Outbound::Unblock { address, promise } => {
                out.push((copy_string(address), Message::Unblock(copy(promise))));
            },
        }
        proof {
            assert(nv.take(i as int + 1).drop_last() =~= nv.take(i as int));
            assert(nv.take(i as int + 1).last() == nv[i as int]);
            match spec_dispatch(doc@, nv[i as int]) {
                Some(m) => {
                    assert(out.deep_view() =~= before.push(m));
                },
                None => {},
            }
        }
        i += 1;
    }
    proof {
        assert(nv.take(i as int) =~= nv);
    }
    out
}

/// Whether a document is an origin's.
pub fn is_workflow(d: &DocumentBody) -> (r: bool)
    ensures
        r == (d@ is Workflow),
{
    proof {
        crate::concrete::lemma_doc_view(d);
    }
    match d {
        DocumentBody::Workflow(_) => true,
        DocumentBody::Schedule(_) => false,
    }
}

// ---------------------------------------------------------------------------
// The steps, stated
// ---------------------------------------------------------------------------

/// Run `work` on `target`, after whatever is on it already.




/// The slot of `name` is free: whatever waits on it goes next.


/// A flight waiting on a slot has it: go on where it stopped.


/// Start, or start over after a lost race.




/// A store call a flight waited on has its answer.


/// The phase the flight was in says what the answer is for.


















/// Ask for a workflow document: revalidated against the store when the
/// cache holds a version, read in full otherwise.




/// The store answered a load of `origin`. Cache bookkeeping is on the
/// fleet's time.


/// Run the flight's step on a workflow document and start its commit.


/// The step: the concrete model's, on the document, decided no earlier
/// than the last step on it.




/// A committed step: the messages out, the answer back.


/// The commit's store call failed: a lost race re-decides, anything else
/// ends the flight with nothing cached.


/// The flight ends without a commit.


/// The flight is over: its slot goes to the next, and the key that fired
/// it hears how it went.


/// The decisions before the first store call: whether the document
/// changed, and the verified sequence, planned from the document's nearest
/// deadline. `fired` is the key whose firing this is.


/// Drive a commit: `answer` is the store's answer to the call the commit
/// waits on, if it waits on one. The wheel and the cache follow the
/// answer; the sequence decides the next call; this makes it.


/// What follows from the answer to the last call, outside the sequence: a
/// key put is armed in the wheel, a key deleted leaves it (a delete that
/// failed is noted; the key fires again and is collected then), a document
/// written is remembered.


/// Write the document at a new version, conditionally on `cond`, the
/// version loaded: the rows the step changed appended, or the whole
/// document.


// ---------------------------------------------------------------------------
// The steps, run
// ---------------------------------------------------------------------------

/// A map with `k` removed and put back is the map with `k` set.
pub proof fn lemma_remove_insert<K, V>(m: Map<K, V>, k: K, v: V)
    ensures
        m.remove(k).insert(k, v) == m.insert(k, v),
{
    assert(m.remove(k).insert(k, v) =~= m.insert(k, v));
}

impl State {
    /// The slot of `name`, taken out of the table; empty when it had none.
    pub fn slot_take(&mut self, name: &str) -> (r: Slot)
        ensures
            r.deep_view() == spec_slot_of(old(self).deep_view(), name@),
            final(self).deep_view() == spec_without_slot(old(self).deep_view(), name@),
    {
        let key = text(name);
        match self.flights.slots.remove(&key) {
            Some(slot) => slot,
            None => {
                let r = Slot { busy: None, queue: Vec::new() };
                proof {
                    assert(r.queue.deep_view() =~= Seq::<QueuedSpec>::empty());
                }
                r
            },
        }
    }

    pub fn slot_put(&mut self, name: &str, slot: Slot)
        ensures
            final(self).deep_view() == spec_with_slot(old(self).deep_view(), name@, slot.deep_view()),
    {
        self.flights.slots.insert(text(name), slot);
    }

    pub fn inflight(&mut self, f: Flight)
        ensures
            final(self).deep_view() == spec_inflight(old(self).deep_view(), f.deep_view()),
    {
        let id = f.id;
        self.flights.inflight.insert(id, f);
    }

    /// Run `work` on `target`, after whatever is on it already.
    pub fn submit(&mut self, target: Target, work: Work, firing: Option<Firing>, debug: bool)
        ensures
            final(self).deep_view() == spec_submit(old(self).deep_view(), target.deep_view(), work.deep_view(), firing.deep_view(), debug),
    {
        proof {
            reveal(spec_submit);
        }
        let name = target.name();
        if let Work::Sweep { now, .. } = &work {
            let flight = self.next_flight;
            self.note(Note::SweepBegin { flight, target: copy_string(&name), now: *now });
        }
        let ghost s1 = self.deep_view();
        let mut slot = self.slot_take(name.as_str());
        if slot.busy.is_some() {
            let ghost q0 = slot.queue.deep_view();
            let ghost w = QueuedSpec::Work { target: target.deep_view(), work: work.deep_view(), firing: firing.deep_view(), debug };
            slot.queue.push(Queued::Work { target, work, firing, debug });
            proof {
                assert(slot.queue.deep_view() =~= q0.push(w));
            }
            self.slot_put(name.as_str(), slot);
            proof {
                lemma_remove_insert(s1.flights.slots, name@, self.flights.slots.deep_view()[name@]);
            }
            return;
        }
        self.slot_put(name.as_str(), slot);
        proof {
            lemma_remove_insert(s1.flights.slots, name@, self.flights.slots.deep_view()[name@]);
        }
        self.start(target, work, firing, debug);
    }

    fn start(&mut self, target: Target, work: Work, firing: Option<Firing>, debug: bool)
        ensures
            final(self).deep_view() == spec_start(old(self).deep_view(), target.deep_view(), work.deep_view(), firing.deep_view(), debug),
    {
        proof {
            reveal(spec_start);
        }
        let id = self.next_flight;
        self.next_flight = self.next_flight.wrapping_add(1);
        let name = target.name();
        let ghost s1 = self.deep_view();
        let mut slot = self.slot_take(name.as_str());
        slot.busy = Some(id);
        self.slot_put(name.as_str(), slot);
        proof {
            lemma_remove_insert(s1.flights.slots, name@, self.flights.slots.deep_view()[name@]);
        }
        let f = Flight { id, target, work, attempt: 0, phase: Phase::Idle, firing, debug, idle: false };
        self.begin(f);
    }

    /// The slot of `name` is free: whatever waits on it goes next.
    pub fn release(&mut self, name: &str)
        ensures
            final(self).deep_view() == spec_release(old(self).deep_view(), name@),
    {
        proof {
            reveal(spec_release);
        }
        let key = text(name);
        if !self.flights.slots.contains(&key) {
            return;
        }
        let ghost s0 = self.deep_view();
        let mut slot = self.slot_take(name);
        slot.busy = None;
        if slot.queue.len() == 0 {
            return;
        }
        let ghost q0 = slot.queue.deep_view();
        let first = slot.queue.remove(0);
        proof {
            assert(first.deep_view() == q0[0]);
            assert(slot.queue.deep_view() =~= q0.drop_first());
        }
        match first {
            Queued::Work { target, work, firing, debug } => {
                self.slot_put(name, slot);
                proof {
                    lemma_remove_insert(s0.flights.slots, name@, self.flights.slots.deep_view()[name@]);
                    assert(self.deep_view() == spec_with_slot(s0, name@, SlotSpec { busy: None, queue: q0.drop_first() }));
                }
                self.start(target, work, firing, debug);
            },
            Queued::Waiter(fid) => {
                slot.busy = Some(fid);
                self.slot_put(name, slot);
                proof {
                    lemma_remove_insert(s0.flights.slots, name@, self.flights.slots.deep_view()[name@]);
                    assert(self.deep_view() == spec_with_slot(s0, name@, SlotSpec { busy: Some(fid), queue: q0.drop_first() }));
                }
                self.resume(fid);
            },
        }
    }

    /// A flight waiting on a slot has it: go on where it stopped.
    fn resume(&mut self, fid: FlightId)
        ensures
            final(self).deep_view() == spec_resume(old(self).deep_view(), fid),
    {
        proof {
            reveal(spec_resume);
        }
        let ghost s0 = self.deep_view();
        match self.flights.inflight.remove(&fid) {
            Some(f) => {
                let ghost f0 = f.deep_view();
                let Flight { id, target, work, attempt, phase, firing, debug, idle } = f;
                match phase {
                    Phase::FireWaitingOrigin(ctx) => {
                        let f = Flight { id, target, work, attempt, phase: Phase::Idle, firing, debug, idle };
                        proof {
                            assert(f.deep_view() == (FlightSpec { phase: PhaseSpec::Idle, ..f0 }));
                        }
                        self.fire_load_origin(f, ctx);
                    },
                    phase => {
                        let f = Flight { id, target, work, attempt, phase, firing, debug, idle };
                        proof {
                            assert(f.deep_view() == f0);
                        }
                        self.inflight(f);
                    },
                }
            },
            None => {
                proof {
                    assert(s0.flights.inflight.remove(fid) =~= s0.flights.inflight);
                }
            },
        }
    }

    /// Start, or start over after a lost race.
    pub fn begin(&mut self, f: Flight)
        ensures
            final(self).deep_view() == spec_begin(old(self).deep_view(), f.deep_view()),
    {
        proof {
            reveal(spec_begin);
        }
        let Flight { id, target, work, attempt, phase: _, firing, debug, idle } = f;
        match &work {
            Work::Fire { schedule, .. } => {
                let key = self.keys.sched_key(schedule.as_str());
                let op = self.store(StoreReq::Get { key }, Owner::Flight(id));
                let f = Flight { id, target, work, attempt, phase: Phase::FireLoadingSchedule { op }, firing, debug, idle };
                self.inflight(f);
            },
            _ => {
                let (op, revalidating) = match &target {
                    Target::Origin(o) => self.load_origin(id, o.as_str()),
                    Target::Schedule(sid) => {
                        let key = self.keys.sched_key(sid.as_str());
                        (self.store(StoreReq::Get { key }, Owner::Flight(id)), None)
                    },
                };
                let f = Flight { id, target, work, attempt, phase: Phase::Loading { op, revalidating }, firing, debug, idle };
                self.inflight(f);
            },
        }
    }

    fn retry(&mut self, f: Flight)
        ensures
            final(self).deep_view() == spec_retry(old(self).deep_view(), f.deep_view()),
    {
        proof {
            reveal(spec_retry);
        }
        let mut f = f;
        f.attempt = f.attempt.wrapping_add(1);
        if f.attempt > self.flights.max_retries {
            self.note(Note::Commit(CommitOutcome::Exhausted));
            let what = match &f.target {
                Target::Origin(_) => "document",
                Target::Schedule(_) => "schedule",
            };
            self.fail(f, concat("too many races on the ", what));
        } else {
            self.begin(f);
        }
    }

    /// A store call a flight waited on has its answer.
    pub fn flight_completed(&mut self, fid: FlightId, op: OpId, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_flight_completed(old(self).deep_view(), fid, op, outcome),
    {
        proof {
            reveal(spec_flight_completed);
        }
        let ghost s0 = old(self).deep_view();
        let f = match self.flights.inflight.remove(&fid) {
            Some(f) => f,
            None => {
                proof {
                    assert(s0.flights.inflight.remove(fid) =~= s0.flights.inflight);
                }
                return;
            },
        };
        let waits = match f.phase.expects() {
            Some(o) => o == op,
            None => false,
        };
        if !waits {
            self.inflight(f);
            return;
        }
        let Flight { id, target, work, attempt, phase, firing, debug, idle } = f;
        let f = Flight { id, target, work, attempt, phase: Phase::Idle, firing, debug, idle };
        self.answered_phase(fid, f, phase, outcome);
    }

    /// The phase the flight was in says what the answer is for.
    fn answered_phase(&mut self, fid: FlightId, f: Flight, phase: Phase, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_answered_phase(old(self).deep_view(), fid, f.deep_view(), phase.deep_view(), outcome),
    {
        proof {
            reveal(spec_answered_phase);
        }
        match phase {
            Phase::Loading { revalidating, .. } => self.answered_loading(f, revalidating, outcome),
            Phase::Origin { commit, done } => self.answered_origin(fid, f, commit, done, outcome),
            Phase::Schedule { commit, done } => self.answered_schedule(fid, f, commit, done, outcome),
            Phase::FireLoadingSchedule { .. } => self.answered_fire_loading_schedule(f, outcome),
            Phase::FireLoadingOrigin { revalidating, ctx, .. } => self.answered_fire_loading_origin(f, revalidating, ctx, outcome),
            Phase::FireIdle { commit } => self.answered_fire_idle(fid, f, commit, outcome),
            Phase::FireOrigin { commit, ctx, t } => self.answered_fire_origin(fid, f, commit, ctx, t, outcome),
            Phase::FireSchedule { commit } => self.answered_fire_schedule(fid, f, commit, outcome),
            _ => self.fail(f, text("an answer the flight did not wait for")),
        }
    }

    fn answered_loading(&mut self, f: Flight, revalidating: Option<Cached>, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_answered_loading(old(self).deep_view(), f.deep_view(), revalidating.deep_view(), outcome),
    {
        proof {
            reveal(spec_answered_loading);
        }
        match &f.target {
            Target::Origin(origin) => {
                let origin = copy_string(origin);
                match self.loaded_origin(origin.as_str(), revalidating, outcome) {
                    Ok(w) => self.run_origin(f, w),
                    Err(e) => self.fail(f, e),
                }
            },
            Target::Schedule(sid) => {
                let sid = copy_string(sid);
                match self.loaded_schedule(sid.as_str(), outcome) {
                    Ok(w) => self.run_schedule(f, w),
                    Err(e) => self.fail(f, e),
                }
            },
        }
    }

    fn answered_origin(&mut self, fid: FlightId, f: Flight, mut commit: Committing, done: Done, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_answered_origin(old(self).deep_view(), fid, f.deep_view(), commit.deep_view(), done.deep_view(), outcome),
    {
        proof {
            reveal(spec_answered_origin);
        }
        match self.commit_advance(fid, &mut commit, Some(outcome)) {
            Progress::Issued => {
                let f = Flight { phase: Phase::Origin { commit, done }, ..f };
                self.inflight(f);
            },
            Progress::Done(fired) => self.committed(f, done, fired),
            Progress::Failed(e) => self.commit_failed(f, e),
        }
    }

    fn answered_schedule(&mut self, fid: FlightId, f: Flight, mut commit: Committing, done: Done, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_answered_schedule(old(self).deep_view(), fid, f.deep_view(), commit.deep_view(), done.deep_view(), outcome),
    {
        proof {
            reveal(spec_answered_schedule);
        }
        match self.commit_advance(fid, &mut commit, Some(outcome)) {
            Progress::Issued => {
                let f = Flight { phase: Phase::Schedule { commit, done }, ..f };
                self.inflight(f);
            },
            Progress::Done(fired) => self.committed(f, done, fired),
            Progress::Failed(e) => self.commit_failed(f, e),
        }
    }

    fn answered_fire_loading_schedule(&mut self, f: Flight, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_answered_fire_loading_schedule(old(self).deep_view(), f.deep_view(), outcome),
    {
        proof {
            reveal(spec_answered_fire_loading_schedule);
        }
        match &f.work {
            Work::Fire { schedule, .. } => {
                let sid = copy_string(schedule);
                match self.loaded_schedule(sid.as_str(), outcome) {
                    Ok(ws) => self.fire_decide(f, ws),
                    Err(e) => self.fail(f, e),
                }
            },
            _ => self.fail(f, text("not a fire")),
        }
    }

    fn answered_fire_loading_origin(&mut self, f: Flight, revalidating: Option<Cached>, ctx: FireCtx, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_answered_fire_loading_origin(old(self).deep_view(), f.deep_view(), revalidating.deep_view(), ctx.deep_view(), outcome),
    {
        proof {
            reveal(spec_answered_fire_loading_origin);
        }
        match self.loaded_origin(ctx.origin.as_str(), revalidating, outcome) {
            Ok(wo) => self.fire_run(f, ctx, wo),
            Err(e) => {
                self.release(ctx.origin.as_str());
                self.fail(f, e);
            },
        }
    }

    fn answered_fire_idle(&mut self, fid: FlightId, f: Flight, mut commit: Committing, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_answered_fire_idle(old(self).deep_view(), fid, f.deep_view(), commit.deep_view(), outcome),
    {
        proof {
            reveal(spec_answered_fire_idle);
        }
        match self.commit_advance(fid, &mut commit, Some(outcome)) {
            Progress::Issued => {
                let f = Flight { phase: Phase::FireIdle { commit }, ..f };
                self.inflight(f);
            },
            Progress::Done(fired) => {
                self.note(Note::SweepEnd { flight: fid, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                self.finish(f, Ok(fired));
            },
            Progress::Failed(e) => {
                self.note(Note::SweepEnd { flight: fid, committed: false });
                self.commit_failed(f, e);
            },
        }
    }

    fn answered_fire_origin(&mut self, fid: FlightId, f: Flight, mut commit: Committing, ctx: FireCtx, t: u64, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_answered_fire_origin(old(self).deep_view(), fid, f.deep_view(), commit.deep_view(), ctx.deep_view(), t, outcome),
    {
        proof {
            reveal(spec_answered_fire_origin);
        }
        match self.commit_advance(fid, &mut commit, Some(outcome)) {
            Progress::Issued => {
                let f = Flight { phase: Phase::FireOrigin { commit, ctx, t }, ..f };
                self.inflight(f);
            },
            Progress::Done(_) => {
                self.note(Note::FireEnd { flight: fid, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                self.release(ctx.origin.as_str());
                self.fire_advance(f, ctx, t);
            },
            Progress::Failed(e) => {
                self.note(Note::FireEnd { flight: fid, committed: false });
                self.forget(ctx.origin.as_str());
                self.release(ctx.origin.as_str());
                self.commit_failed(f, e);
            },
        }
    }

    fn answered_fire_schedule(&mut self, fid: FlightId, f: Flight, mut commit: Committing, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_answered_fire_schedule(old(self).deep_view(), fid, f.deep_view(), commit.deep_view(), outcome),
    {
        proof {
            reveal(spec_answered_fire_schedule);
        }
        match self.commit_advance(fid, &mut commit, Some(outcome)) {
            Progress::Issued => {
                let f = Flight { phase: Phase::FireSchedule { commit }, ..f };
                self.inflight(f);
            },
            Progress::Done(fired) => {
                self.note(Note::AdvanceEnd { flight: fid, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                self.finish(f, Ok(fired));
            },
            Progress::Failed(e) => {
                self.note(Note::AdvanceEnd { flight: fid, committed: false });
                self.commit_failed(f, e);
            },
        }
    }

    // -----------------------------------------------------------------------
    // Loading
    // -----------------------------------------------------------------------

    /// Ask for a workflow document: revalidated against the store when
    /// the cache holds a version, read in full otherwise.
    pub fn load_origin(&mut self, fid: FlightId, origin: &str) -> (r: (OpId, Option<Cached>))
        ensures
            ({
                let (s, op, c) = spec_load_origin(old(self).deep_view(), fid, origin@);
                final(self).deep_view() == s && r.0 == op && r.1.deep_view() == c
            }),
    {
        proof {
            reveal(spec_load_origin);
        }
        let key = self.keys.doc_key(origin);
        match self.cache.get(origin) {
            Some(c) => {
                let etag = Etag(copy_string(&c.etag.0));
                (self.store(StoreReq::GetIfNoneMatch { key, etag }, Owner::Flight(fid)), Some(c))
            },
            None => {
                self.note(Note::Cache(CacheResult::Miss));
                (self.store(StoreReq::Get { key }, Owner::Flight(fid)), None)
            },
        }
    }

    /// The store answered a load of `origin`. Cache bookkeeping is on the
    /// fleet's time.
    fn loaded_origin(&mut self, origin: &str, revalidating: Option<Cached>, outcome: StoreRes) -> (r: Result<Working, String>)
        ensures
            (final(self).deep_view(), r.deep_view()) == spec_loaded_origin(old(self).deep_view(), origin@, revalidating.deep_view(), outcome),
    {
        proof {
            reveal(spec_loaded_origin);
        }
        let now = self.now();
        let key = self.keys.doc_key(origin);
        let target = text(origin);
        match revalidating {
            Some(c) => match outcome {
                StoreRes::GetIfNoneMatch { result: Ok(Read::NotModified) } => {
                    self.note(Note::Cache(CacheResult::Revalidated));
                    let Cached { loaded, etag, filled_at: _ } = c;
                    self.remember(origin, Cached { loaded: loaded.copy(), etag: Etag(copy_string(&etag.0)), filled_at: now });
                    Ok(Working { target, key, loaded, etag: Some(etag) })
                },
                StoreRes::GetIfNoneMatch { result: Ok(Read::Absent) } => {
                    self.note(Note::Cache(CacheResult::Absent));
                    self.forget(origin);
                    Ok(Working { target, key, loaded: Loaded::empty_workflow(text(origin)), etag: None })
                },
                StoreRes::GetIfNoneMatch { result: Ok(Read::Body(bytes, etag)) } => {
                    self.note(Note::Cache(CacheResult::Refreshed));
                    match document::decode_workflow(bytes.as_slice()) {
                        Ok(loaded) => {
                            self.remember(origin, Cached { loaded: loaded.copy(), etag: Etag(copy_string(&etag.0)), filled_at: now });
                            Ok(Working { target, key, loaded, etag: Some(etag) })
                        },
                        Err(e) => Err(e),
                    }
                },
                StoreRes::GetIfNoneMatch { result: Err(e) } => Err(error_text(&e)),
                _ => Err(error_text(&unexpected())),
            },
            None => match outcome {
                StoreRes::Get { result: Ok(None) } => Ok(Working { target, key, loaded: Loaded::empty_workflow(text(origin)), etag: None }),
                StoreRes::Get { result: Ok(Some((bytes, etag))) } => match document::decode_workflow(bytes.as_slice()) {
                    Ok(loaded) => {
                        self.remember(origin, Cached { loaded: loaded.copy(), etag: Etag(copy_string(&etag.0)), filled_at: now });
                        Ok(Working { target, key, loaded, etag: Some(etag) })
                    },
                    Err(e) => Err(e),
                },
                StoreRes::Get { result: Err(e) } => Err(error_text(&e)),
                _ => Err(error_text(&unexpected())),
            },
        }
    }

    // -----------------------------------------------------------------------
    // The step
    // -----------------------------------------------------------------------

    /// Run the flight's step on a workflow document and start its commit.
    fn run_origin(&mut self, f: Flight, w: Working)
        ensures
            final(self).deep_view() == spec_run_origin(old(self).deep_view(), f.deep_view(), w.deep_view()),
    {
        proof {
            reveal(spec_run_origin);
        }
        let (mut commit, done) = self.decide(&f.work, w);
        match self.commit_advance(f.id, &mut commit, None) {
            Progress::Issued => {
                let f = Flight { phase: Phase::Origin { commit, done }, ..f };
                self.inflight(f);
            },
            Progress::Done(fired) => self.committed(f, done, fired),
            Progress::Failed(e) => self.commit_failed(f, e),
        }
    }

    /// The step: `verified::flight::decide`, the concrete model's step on
    /// the document, decided no earlier than the last step on the
    /// document. A request is `handle`; a due key is `sweep`, every due
    /// step on the document up to `SWEEP_STEPS`. A lost race runs this
    /// again on what it re-read.
    pub fn decide(&mut self, work: &Work, w: Working) -> (r: (Committing, Done))
        ensures
            ({
                let (s, commit, done) = spec_decide(old(self).deep_view(), work.deep_view(), w.deep_view());
                final(self).deep_view() == s && r.0.deep_view() == commit && r.1.deep_view() == done
            }),
    {
        proof {
            reveal(spec_decide);
        }
        let now = document::clamp_now(document::loaded_committed_at(&w.loaded), work.now());
        let job = match work {
            Work::Request { req, .. } => Job::Request(copy(req)),
            Work::Sweep { .. } => Job::Sweep,
            Work::Fire { .. } => Job::Fire,
        };
        let Decided { doc: after, response, born: _, notes } = flight::decide(job, document::loaded_body(&w.loaded), now, self.cfg.retry_timeout, SWEEP_STEPS);
        let why = match work {
            Work::Request { req, kind, .. } => match &response {
                Some(r) => {
                    let status = crate::reason::status_of(r);
                    if status >= 400 { Some(crate::reason::reason_for(kind.as_str(), req, status, &after)) } else { None }
                },
                None => None,
            },
            _ => None,
        };
        let outbox = dispatches(&after, &notes);
        let deadline = document::deadline(&after);
        let (fired, is_sweep) = match work {
            Work::Sweep { fired, .. } => (copy_fired(fired), true),
            _ => (None, false),
        };
        let commit = self.commit_new(w, after, deadline, now, fired);
        let did = is_sweep && commit.seq.changed;
        (commit, Done { response, why, outbox, did })
    }

    fn send_all(&mut self, outbox: Vec<(String, Message)>)
        ensures
            final(self).deep_view() == spec_send_all(old(self).deep_view(), outbox.deep_view()),
    {
        let ghost ob = outbox.deep_view();
        let ghost s0 = old(self).deep_view();
        let mut i: usize = 0;
        proof {
            assert(ob.skip(0) =~= ob);
        }
        while i < outbox.len()
            invariant
                i <= outbox.len(),
                ob == outbox.deep_view(),
                spec_send_all(s0, ob) == spec_send_all(self.deep_view(), ob.skip(i as int)),
            decreases outbox.len() - i,
        {
            proof {
                assert(ob.skip(i as int).drop_first() =~= ob.skip(i as int + 1));
                assert(ob.skip(i as int)[0] == ob[i as int]);
            }
            let address = copy_string(&outbox[i].0);
            let message = copy(&outbox[i].1);
            self.send(address, message);
            i += 1;
        }
        proof {
            assert(ob.skip(i as int) =~= Seq::<(Seq<char>, MessageSpec)>::empty());
        }
    }

    /// A committed step: the messages out, the answer back.
    pub fn committed(&mut self, f: Flight, done: Done, fired: Fired)
        ensures
            final(self).deep_view() == spec_committed(old(self).deep_view(), f.deep_view(), done.deep_view(), fired),
    {
        proof {
            reveal(spec_committed);
        }
        self.note(Note::Commit(CommitOutcome::Committed));
        let Done { response, why, outbox, did } = done;
        self.send_all(outbox);
        let mut f = f;
        match &f.work {
            Work::Request { id, kind, corr, action_kind, now, stage: Stage::Detached { then, check }, .. } => {
                match (response, check) {
                    (Some(Response::Promise(inner)), Some(check)) => {
                        let work = Work::Request { id: *id, kind: copy_string(kind), corr: copy_string(corr), req: copy(check), action_kind: copy(action_kind), now: *now, stage: Stage::Check { inner: Some(inner) } };
                        let then = then.copy();
                        let debug = f.debug;
                        self.submit(then, work, None, debug);
                    },
                    _ => {
                        let id = *id;
                        self.emit(Effect::Reply { id, response: Err(text("no answer")) });
                    },
                }
            },
            Work::Request { id, kind, corr, action_kind, stage: Stage::Check { inner }, .. } => {
                let response = match (response, inner) {
                    (Some(Response::Status(st)), Some(inner)) => {
                        let action = if st.status == 200 { Some(TaskFenceInnerRes::Create(copy(inner))) } else { None };
                        let response = Response::TaskFence(TaskFenceRes { status: st.status, action });
                        Ok(Answer::Step { kind: copy_string(kind), corr: copy_string(corr), action_kind: copy(action_kind), response, why })
                    },
                    _ => Err(text("no answer")),
                };
                let id = *id;
                self.emit(Effect::Reply { id, response });
            },
            Work::Request { id, kind, corr, action_kind, stage: Stage::Whole, .. } => {
                let response = match response {
                    Some(response) => Ok(Answer::Step { kind: copy_string(kind), corr: copy_string(corr), action_kind: copy(action_kind), response, why }),
                    None => Err(text("no answer")),
                };
                let id = *id;
                self.emit(Effect::Reply { id, response });
            },
            Work::Sweep { .. } => {
                self.note(Note::Sweep(if did { SweepOutcome::Fired } else { SweepOutcome::Idle }));
                let flight = f.id;
                self.note(Note::SweepEnd { flight, committed: true });
            },
            Work::Fire { .. } => {},
        }
        f.idle = !did;
        self.finish(f, Ok(fired));
    }

    /// The commit's store call failed: a lost race re-decides, anything
    /// else ends the flight with nothing cached.
    pub fn commit_failed(&mut self, f: Flight, e: StoreError)
        ensures
            final(self).deep_view() == spec_commit_failed(old(self).deep_view(), f.deep_view(), e.deep_view()),
    {
        proof {
            reveal(spec_commit_failed);
        }
        if let Target::Origin(o) = &f.target {
            let o = copy_string(o);
            self.forget(o.as_str());
        }
        match e {
            StoreError::PreconditionFailed => {
                self.note(Note::Commit(CommitOutcome::Raced));
                let attempt = f.attempt;
                self.note(Note::Raced { target: f.target.name(), attempt });
                self.retry(f);
            },
            e => {
                self.note(Note::Commit(CommitOutcome::Failed));
                self.fail(f, error_text(&e));
            },
        }
    }

    /// The flight ends without a commit.
    pub fn fail(&mut self, f: Flight, e: String)
        ensures
            final(self).deep_view() == spec_fail(old(self).deep_view(), f.deep_view(), e@),
    {
        proof {
            reveal(spec_fail);
        }
        match &f.work {
            Work::Request { id, .. } => {
                let id = *id;
                self.emit(Effect::Reply { id, response: Err(copy_string(&e)) });
            },
            Work::Sweep { .. } => {
                self.note(Note::Sweep(SweepOutcome::Failed));
                let flight = f.id;
                self.note(Note::SweepEnd { flight, committed: false });
            },
            Work::Fire { .. } => {},
        }
        self.finish(f, Err(e));
    }

    /// The flight is over: its slot goes to the next, and the key that
    /// fired it hears how it went.
    pub fn finish(&mut self, f: Flight, r: Result<Fired, String>)
        ensures
            final(self).deep_view() == spec_finish(old(self).deep_view(), f.deep_view(), r.deep_view()),
    {
        proof {
            reveal(spec_finish);
        }
        let name = f.target.name();
        self.release(name.as_str());
        let Flight { id: _, target: _, work, attempt: _, phase: _, firing, debug, idle } = f;
        if let Some(firing) = firing {
            let now = self.now();
            self.timer_fired(firing, now, r);
        }
        if debug {
            self.debug_flight_done(&work, idle);
        }
    }

    pub fn send(&mut self, address: String, message: Message)
        ensures
            final(self).deep_view() == spec_emit(old(self).deep_view(), EffectSpec::Send { address: address@, message: message.deep_view() }),
    {
        self.emit(Effect::Send { address, message });
    }

    // -----------------------------------------------------------------------
    // The commit
    // -----------------------------------------------------------------------

    /// The decisions before the first store call: whether the document
    /// changed, and the verified sequence, planned from the document's
    /// nearest deadline. `fired` is the key whose firing this is.
    pub fn commit_new(&mut self, w: Working, after: DocumentBody, deadline: Option<u64>, now: u64, fired: Option<FiredKey>) -> (c: Committing)
        ensures
            (final(self).deep_view(), c.deep_view()) == spec_commit_new(old(self).deep_view(), w.deep_view(), after@, crate::concrete::document::nat_v(deadline), now, fired.deep_view()),
    {
        proof {
            reveal(spec_commit_new);
        }
        let changed_any = document::changed(&document::loaded_body(&w.loaded), &after);
        let etag: Option<String> = match &w.etag {
            Some(e) => Some(copy_string(&e.0)),
            None => None,
        };
        let token = self.token();
        let etag_ref: Option<&String> = match &etag {
            Some(e) => Some(e),
            None => None,
        };
        let seq = Sequence::new(&self.node.core, w.target.as_str(), etag_ref, deadline, changed_any, fired, token);
        let after = advance_stored(&w.loaded.document, after, now);
        Committing { w, after, now, seq, issued: None }
    }

    /// Drive a commit: `answer` is the store's answer to the call the
    /// commit waits on, if it waits on one. The wheel and the cache follow
    /// the answer; the sequence decides the next call; this makes it.
    /// Returns with that call issued, or the commit over.
    #[verifier::rlimit(40)]
    pub fn commit_advance(&mut self, fid: FlightId, c: &mut Committing, answer: Option<StoreRes>) -> (p: Progress)
        ensures
            (final(self).deep_view(), final(c).deep_view(), p.deep_view()) == spec_commit_advance(old(self).deep_view(), fid, old(c).deep_view(), answer),
    {
        proof {
            reveal(spec_commit_advance);
        }
        let issued = take_opt(&mut c.issued);
        if let Some(issued) = issued {
            self.answered(c, issued, &answer);
        }
        let answer_ref: Option<&StoreRes> = match &answer {
            Some(o) => Some(o),
            None => None,
        };
        let outcome = c.seq.advance(&mut self.node.core, answer_ref);
        match outcome {
            Outcome::Act(Act::PutKey(key)) => {
                let by = copy_string(&self.cfg.node_id);
                let name = self.key_name(&key, by.as_str());
                let op = self.store(StoreReq::Put { key: copy_string(&name), body: Vec::new() }, Owner::Flight(fid));
                c.issued = Some(Issued::Key { op, key, name, arm: true });
                Progress::Issued
            },
            Outcome::Act(Act::Write { cond, idle }) => {
                self.issue_write(fid, c, cond, idle);
                Progress::Issued
            },
            Outcome::Act(Act::DeleteKey { key, by }) => {
                let name = self.key_name(&key, by.as_str());
                let op = self.store(StoreReq::Del { key: copy_string(&name) }, Owner::Flight(fid));
                c.issued = Some(Issued::Key { op, key, name, arm: false });
                Progress::Issued
            },
            Outcome::Act(Act::Done { deleted }) => Progress::Done(if deleted { Fired::Deleted } else { Fired::Kept }),
            Outcome::Failed(Some(e)) => Progress::Failed(e),
            Outcome::Failed(None) => Progress::Failed(unexpected()),
        }
    }

    /// What follows from the answer to the last call, outside the
    /// sequence: a key put is armed in the wheel, a key deleted leaves it
    /// (a delete that failed is noted; the key fires again and is collected
    /// then), a document written is remembered.
    fn answered(&mut self, c: &mut Committing, issued: Issued, answer: &Option<StoreRes>)
        ensures
            (final(self).deep_view(), final(c).deep_view()) == spec_answered(old(self).deep_view(), old(c).deep_view(), issued.deep_view(), *answer),
    {
        proof {
            reveal(spec_answered);
        }
        match issued {
            Issued::Key { key, name, arm, .. } => match answer {
                Some(StoreRes::Put { result: Ok(()) }) | Some(StoreRes::Del { result: Ok(()) }) => {
                    if arm {
                        self.timers.wheel.arm(key.at, name);
                    } else {
                        self.timers.wheel.disarm(key.at, name.as_str());
                    }
                },
                Some(StoreRes::Put { result: Err(e) }) | Some(StoreRes::Del { result: Err(e) }) => {
                    if !arm {
                        self.note(Note::KeyNotDeleted { key: name, error: error_text(e) });
                    }
                },
                _ => {},
            },
            Issued::Write { mode, change_count, bytes, len, .. } => match answer {
                Some(StoreRes::PutIfMatch { result: Ok(etag) })
                | Some(StoreRes::PutIfNoneMatch { result: Ok(etag) })
                | Some(StoreRes::AppIfMatch { result: Ok(etag) }) => {
                    self.note(Note::DocumentWrite { mode, bytes: len });
                    if stored_is_workflow(&c.after) {
                        let filled_at = self.now();
                        let target = copy_string(&c.w.target);
                        let cached = Cached {
                            loaded: Loaded {
                                document: clone_stored(&c.after),
                                change_count,
                                bytes,
                            },
                            etag: Etag(copy_string(&etag.0)),
                            filled_at,
                        };
                        self.remember(target.as_str(), cached);
                    }
                    c.w.etag = Some(Etag(copy_string(&etag.0)));
                },
                _ => {},
            },
        }
    }

    /// Write the document at a new version, conditionally on `cond`, the
    /// version loaded: the rows the step changed appended, or the whole
    /// document.
    fn issue_write(&mut self, fid: FlightId, c: &mut Committing, cond: Option<String>, _idle: bool)
        ensures
            (final(self).deep_view(), final(c).deep_view()) == spec_issue_write(old(self).deep_view(), fid, old(c).deep_view(), cond.deep_view(), _idle),
    {
        proof {
            reveal(spec_issue_write);
        }
        let (call, mode, change_count, bytes) = match cond {
            None => {
                let after = stored_body(&c.after);
                let body = document::encode(&c.after);
                let n = body_len(&after);
                let b = body.len() as u64;
                (StoreReq::PutIfNoneMatch { key: copy_string(&c.w.key), body }, WriteMode::Create, n, b)
            },
            Some(etag) => {
                let etag = Etag(etag);
                let before = document::loaded_body(&c.w.loaded);
                let after = stored_body(&c.after);
                let (delta, changed) = document::encode_delta(&c.w.loaded.document, &c.after);
                // a row gone — a schedule deleted — cannot be appended; the
                // document is rewritten without it
                let removed = document::removed_any(&before, &after);
                let after_len = body_len(&after);
                let stale_after = c.w.loaded.change_count.saturating_add(changed).saturating_sub(after_len);
                let append = document::loaded_version(&c.w.loaded) > 0 && !removed && self.cfg.appendable && self.cfg.compact > 0 && stale_after < self.cfg.compact as usize;
                if append {
                    let n = c.w.loaded.change_count.saturating_add(changed);
                    let b = c.w.loaded.bytes.saturating_add(delta.len() as u64);
                    (StoreReq::AppIfMatch { key: copy_string(&c.w.key), offset: c.w.loaded.bytes, body: delta, etag }, WriteMode::Append, n, b)
                } else {
                    let body = document::encode(&c.after);
                    let b = body.len() as u64;
                    (StoreReq::PutIfMatch { key: copy_string(&c.w.key), body, etag }, WriteMode::Rewrite, after_len, b)
                }
            },
        };
        let len = match &call {
            StoreReq::PutIfNoneMatch { body, .. } | StoreReq::AppIfMatch { body, .. } | StoreReq::PutIfMatch { body, .. } => body.len(),
            _ => 0,
        };
        let op = self.store(call, Owner::Flight(fid));
        c.issued = Some(Issued::Write { op, mode, change_count, bytes, len });
    }
}

/// `Option::take`, stated.
pub fn take_opt<T>(o: &mut Option<T>) -> (r: Option<T>)
    ensures
        r == *old(o),
        *final(o) is None,
{
    let mut taken: Option<T> = None;
    core::mem::swap(&mut taken, o);
    taken
}

pub fn copy_fired(f: &Option<FiredKey>) -> (r: Option<FiredKey>)
    ensures
        r.deep_view() == f.deep_view(),
{
    match f {
        Some(k) => Some(FiredKey { key: crate::verified::node::clone_key(&k.key), by: copy_string(&k.by) }),
        None => None,
    }
}

} // verus!
