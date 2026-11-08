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

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use echod_abstract::trusted::copy;
use echod_concrete::{
    advance_stored, body_len, clone_stored, peek, stored_body, stored_is_workflow, DocumentBody,
    Outbound, StoredDocument,
};

use crate::verified::flight::{self, Act, Decided, FiredKey, Job, Outcome, Sequence};
use crate::verified::node::Key;
use crate::verified::table::Table;
use crate::verified::text::{concat, copy_string, text};
use crate::verified::{Request, Response};

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
use echod_concrete::node::{
    notes_v, spec_body_deadline, spec_workflow_map, DocumentBodyV, NoteV, ScheduleDocumentV,
    StoredDocumentV, WorkflowDocumentV,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::store::{EtagSpec, StoreErrorSpec, StoreReqSpec};
#[cfg(verus_keep_ghost)]
use echod_types::spec::AResponse;

verus! {

// ---------------------------------------------------------------------------
// What a flight is
// ---------------------------------------------------------------------------

/// What a flight does.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Work {
    Request { id: RequestId, kind: String, corr: String, req: Request, action_kind: Option<String>, now: u64 },
    /// `fired` is the key whose firing this is; none for a sweep or a fire
    /// a test asked for.
    Sweep { fired: Option<FiredKey>, now: u64 },
    Fire { schedule: String, fired: Option<FiredKey>, now: u64 },
}

#[cfg(verus_keep_ghost)]
pub ghost enum WorkSpec {
    Request { id: RequestId, kind: Seq<char>, corr: Seq<char>, req: Request, action_kind: Option<Seq<char>>, now: u64 },
    Sweep { fired: Option<AFired>, now: u64 },
    Fire { schedule: Seq<char>, fired: Option<AFired>, now: u64 },
}

#[cfg(verus_keep_ghost)]
impl DeepView for Work {
    type V = WorkSpec;
    open spec fn deep_view(&self) -> WorkSpec {
        match self {
            Work::Request { id, kind, corr, req, action_kind, now } => WorkSpec::Request {
                id: *id, kind: kind@, corr: corr@, req: *req, action_kind: action_kind.deep_view(), now: *now,
            },
            Work::Sweep { fired, now } => WorkSpec::Sweep { fired: fired.deep_view(), now: *now },
            Work::Fire { schedule, fired, now } => WorkSpec::Fire { schedule: schedule@, fired: fired.deep_view(), now: *now },
        }
    }
}

#[cfg(verus_keep_ghost)]
impl WorkSpec {
    pub open spec fn now(self) -> u64 {
        match self {
            WorkSpec::Request { now, .. } | WorkSpec::Sweep { now, .. } | WorkSpec::Fire { now, .. } => now,
        }
    }

    pub open spec fn is_sweep(self) -> bool {
        self is Sweep
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

/// The key that fired a flight, for the timers when it ends.
#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
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
#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
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
#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Committing {
    pub w: Working,
    /// The document as the step left it.
    pub after: StoredDocument,
    pub now: u64,
    pub seq: Sequence,
    pub issued: Option<Issued>,
}

/// The call made for the sequence's last act, with what the answer needs.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Issued {
    /// A key put or deleted: the wheel follows the answer.
    Key { op: OpId, key: Key, name: String, arm: bool },
    /// The document written: the cache follows the answer.
    Write { op: OpId, mode: WriteMode, change_count: usize, bytes: u64, len: usize },
}

#[cfg(verus_keep_ghost)]
pub ghost enum IssuedSpec {
    Key { op: OpId, key: AKey, name: Seq<char>, arm: bool },
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

#[cfg(verus_keep_ghost)]
impl CommittingSpec {
    /// The store call the commit waits on.
    pub open spec fn expects(self) -> Option<OpId> {
        match self.issued {
            Some(IssuedSpec::Key { op, .. }) | Some(IssuedSpec::Write { op, .. }) => Some(op),
            None => None,
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
pub ghost enum ProgressSpec {
    Issued,
    Done(Fired),
    Failed(StoreErrorSpec),
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

/// What a committed step answers with.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Done {
    pub response: Option<Response>,
    /// Why the request was refused, in the protocol's words, if it was.
    pub why: Option<String>,
    /// What the step tells workers once its write lands.
    pub outbox: Vec<(String, Message)>,
    pub did: bool,
}

#[cfg(verus_keep_ghost)]
pub ghost struct DoneSpec {
    pub response: Option<Response>,
    pub why: Option<Seq<char>>,
    pub outbox: Seq<(Seq<char>, MessageSpec)>,
    pub did: bool,
}

#[cfg(verus_keep_ghost)]
impl DeepView for Done {
    type V = DoneSpec;

    open spec fn deep_view(&self) -> DoneSpec {
        DoneSpec {
            response: match &self.response {
                Some(response) => Some(*response),
                None => None,
            },
            why: self.why.deep_view(),
            outbox: self.outbox.deep_view(),
            did: self.did,
        }
    }
}

/// A fire past its decision: the schedule as loaded and as advanced, the
/// occurrence due, and the origin it is born in.
#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct FireCtx {
    pub ws: Working,
    pub row: crate::verified::Schedule,
    pub advanced: DocumentBody,
    pub pending: echod_concrete::Pending,
    pub t1: u64,
    pub origin: String,
    pub next: u64,
}

#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Phase {
    Idle,
    Loading { op: OpId, revalidating: Option<Cached> },
    Origin { commit: Committing, done: Done },
    Schedule { commit: Committing, done: Done },
    FireLoadingSchedule { op: OpId },
    FireWaitingOrigin(FireCtx),
    FireLoadingOrigin { op: OpId, revalidating: Option<Cached>, ctx: FireCtx },
    FireIdle { commit: Committing },
    FireOrigin { commit: Committing, ctx: FireCtx, t: u64, outbox: Vec<(String, Message)> },
    FireSchedule { commit: Committing },
}

#[cfg(verus_keep_ghost)]
pub ghost enum PhaseSpec {
    Idle,
    Loading { op: OpId, revalidating: Option<CachedSpec> },
    Origin { commit: CommittingSpec, done: DoneSpec },
    Schedule { commit: CommittingSpec, done: DoneSpec },
    FireLoadingSchedule { op: OpId },
    FireWaitingOrigin(FireCtxSpec),
    FireLoadingOrigin { op: OpId, revalidating: Option<CachedSpec>, ctx: FireCtxSpec },
    FireIdle { commit: CommittingSpec },
    FireOrigin { commit: CommittingSpec, ctx: FireCtxSpec, t: u64, outbox: Seq<(Seq<char>, MessageSpec)> },
    FireSchedule { commit: CommittingSpec },
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
            Phase::FireOrigin { commit, ctx, t, outbox } => PhaseSpec::FireOrigin { commit: commit.deep_view(), ctx: ctx.deep_view(), t: *t, outbox: outbox.deep_view() },
            Phase::FireSchedule { commit } => PhaseSpec::FireSchedule { commit: commit.deep_view() },
        }
    }
}

#[cfg(verus_keep_ghost)]
impl PhaseSpec {
    /// The store call the flight waits on.
    pub open spec fn expects(self) -> Option<OpId> {
        match self {
            PhaseSpec::Idle | PhaseSpec::FireWaitingOrigin(_) => None,
            PhaseSpec::Loading { op, .. } | PhaseSpec::FireLoadingSchedule { op } | PhaseSpec::FireLoadingOrigin { op, .. } => Some(op),
            PhaseSpec::Origin { commit, .. } | PhaseSpec::FireOrigin { commit, .. } => commit.expects(),
            PhaseSpec::Schedule { commit, .. } | PhaseSpec::FireIdle { commit } | PhaseSpec::FireSchedule { commit } => commit.expects(),
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

#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
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

#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Queued {
    Work { target: Target, work: Work, firing: Option<Firing>, debug: bool },
    Waiter(FlightId),
}

#[cfg(verus_keep_ghost)]
pub ghost enum QueuedSpec {
    Work { target: TargetSpec, work: WorkSpec, firing: Option<FiringSpec>, debug: bool },
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
#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Slot {
    pub busy: Option<FlightId>,
    pub queue: Vec<Queued>,
}

#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Flights {
    pub slots: Table<String, Slot>,
    pub inflight: Table<FlightId, Flight>,
    pub max_retries: u32,
}

pub open spec fn spec_flights_new() -> FlightsSpec {
    FlightsSpec { slots: Map::empty(), inflight: Map::empty(), max_retries: 8 }
}

impl Flights {
    pub fn new() -> (r: Flights)
        ensures
            r.deep_view() == spec_flights_new(),
    {
        Flights { slots: Table::new(), inflight: Table::new(), max_retries: 8 }
    }
}

pub open spec fn spec_empty_slot() -> SlotSpec {
    SlotSpec { busy: None, queue: Seq::empty() }
}

/// The slot of `name`, or an empty one.
pub open spec fn spec_slot_of(s: S, name: Seq<char>) -> SlotSpec {
    if s.flights.slots.contains_key(name) { s.flights.slots[name] } else { spec_empty_slot() }
}

pub open spec fn spec_with_slot(s: S, name: Seq<char>, slot: SlotSpec) -> S {
    S { flights: FlightsSpec { slots: s.flights.slots.insert(name, slot), ..s.flights }, ..s }
}

pub open spec fn spec_without_slot(s: S, name: Seq<char>) -> S {
    S { flights: FlightsSpec { slots: s.flights.slots.remove(name), ..s.flights }, ..s }
}

/// `f` in flight.
pub open spec fn spec_inflight(s: S, f: FlightSpec) -> S {
    S { flights: FlightsSpec { inflight: s.flights.inflight.insert(f.id, f), ..s.flights }, ..s }
}

pub open spec fn spec_take_flight(s: S, fid: FlightId) -> S {
    S { flights: FlightsSpec { inflight: s.flights.inflight.remove(fid), ..s.flights }, ..s }
}

// ---------------------------------------------------------------------------
// What a step's notes say to whom
// ---------------------------------------------------------------------------

/// An `Execute` goes to the address the task's promise is targeted at; an
/// `Unblock` to the listener's.
pub open spec fn spec_dispatch(doc: DocumentBodyV, n: NoteV) -> Option<(Seq<char>, MessageSpec)> {
    match n {
        NoteV::Execute { id, version } => {
            if spec_workflow_map(doc).contains_key(id) {
                match crate::reason::spec_target_of(spec_workflow_map(doc)[id].promise.tags@) {
                    Some(address) => Some((address, MessageSpec::Execute { task_id: id, version })),
                    None => None,
                }
            } else {
                None
            }
        },
        NoteV::Unblock { address, promise } => Some((address, MessageSpec::Unblock(promise))),
    }
}

pub open spec fn spec_dispatches(doc: DocumentBodyV, notes: Seq<NoteV>) -> Seq<(Seq<char>, MessageSpec)>
    decreases notes.len(),
{
    if notes.len() == 0 {
        Seq::empty()
    } else {
        let front = spec_dispatches(doc, notes.drop_last());
        match spec_dispatch(doc, notes.last()) {
            Some(m) => front.push(m),
            None => front,
        }
    }
}

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
            echod_concrete::lemma_outbound_view(&notes@[i as int]);
        }
        match &notes[i] {
            Outbound::Execute { id, version } => {
                match peek(doc, id) {
                    Some(obj) => {
                        proof {
                            echod_concrete::lemma_obj_view(&obj);
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
        echod_concrete::lemma_doc_view(d);
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
#[verifier::opaque]
pub open spec fn spec_submit(s: S, target: TargetSpec, work: WorkSpec, firing: Option<FiringSpec>, debug: bool) -> S {
    let name = crate::target::spec_name(target);
    let s = match work {
        WorkSpec::Sweep { now, .. } => spec_note(s, NoteSpec::SweepBegin { flight: s.next_flight, target: name, now }),
        _ => s,
    };
    let slot = spec_slot_of(s, name);
    if slot.busy is Some {
        spec_with_slot(s, name, SlotSpec { queue: slot.queue.push(QueuedSpec::Work { target, work, firing, debug }), ..slot })
    } else {
        spec_start(spec_with_slot(s, name, slot), target, work, firing, debug)
    }
}

#[verifier::opaque]
pub open spec fn spec_start(s: S, target: TargetSpec, work: WorkSpec, firing: Option<FiringSpec>, debug: bool) -> S {
    let id = s.next_flight;
    let name = crate::target::spec_name(target);
    let slot = spec_slot_of(s, name);
    let s = spec_with_slot(S { next_flight: id.wrapping_add(1), ..s }, name, SlotSpec { busy: Some(id), ..slot });
    spec_begin(s, FlightSpec { id, target, work, attempt: 0, phase: PhaseSpec::Idle, firing, debug, idle: false })
}

/// The slot of `name` is free: whatever waits on it goes next.
#[verifier::opaque]
pub open spec fn spec_release(s: S, name: Seq<char>) -> S {
    if !s.flights.slots.contains_key(name) {
        s
    } else {
        let slot = s.flights.slots[name];
        if slot.queue.len() == 0 {
            spec_without_slot(s, name)
        } else {
            let rest = slot.queue.drop_first();
            match slot.queue[0] {
                QueuedSpec::Work { target, work, firing, debug } => {
                    spec_start(spec_with_slot(s, name, SlotSpec { busy: None, queue: rest }), target, work, firing, debug)
                },
                QueuedSpec::Waiter(fid) => spec_resume(spec_with_slot(s, name, SlotSpec { busy: Some(fid), queue: rest }), fid),
            }
        }
    }
}

/// A flight waiting on a slot has it: go on where it stopped.
#[verifier::opaque]
pub open spec fn spec_resume(s: S, fid: FlightId) -> S {
    if s.flights.inflight.contains_key(fid) {
        let f = s.flights.inflight[fid];
        let s = spec_take_flight(s, fid);
        match f.phase {
            PhaseSpec::FireWaitingOrigin(ctx) => crate::handler_sched::spec_fire_load_origin(s, FlightSpec { phase: PhaseSpec::Idle, ..f }, ctx),
            _ => spec_inflight(s, f),
        }
    } else {
        s
    }
}

/// Start, or start over after a lost race.
#[verifier::opaque]
pub open spec fn spec_begin(s: S, f: FlightSpec) -> S {
    match f.work {
        WorkSpec::Fire { schedule, .. } => {
            let (s, op) = spec_store(s, StoreReqSpec::Get { key: spec_sched_key(s.keys.prefix, schedule) }, Owner::Flight(f.id));
            spec_inflight(s, FlightSpec { phase: PhaseSpec::FireLoadingSchedule { op }, ..f })
        },
        _ => match f.target {
            TargetSpec::Origin(o) => {
                let (s, op, revalidating) = spec_load_origin(s, f.id, o);
                spec_inflight(s, FlightSpec { phase: PhaseSpec::Loading { op, revalidating }, ..f })
            },
            TargetSpec::Schedule(id) => {
                let (s, op) = spec_store(s, StoreReqSpec::Get { key: spec_sched_key(s.keys.prefix, id) }, Owner::Flight(f.id));
                spec_inflight(s, FlightSpec { phase: PhaseSpec::Loading { op, revalidating: None }, ..f })
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn spec_retry(s: S, f: FlightSpec) -> S {
    let f = FlightSpec { attempt: f.attempt.wrapping_add(1), ..f };
    if f.attempt > s.flights.max_retries {
        let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Exhausted));
        let what = match f.target {
            TargetSpec::Origin(_) => "document"@,
            TargetSpec::Schedule(_) => "schedule"@,
        };
        spec_fail(s, f, "too many races on the "@ + what)
    } else {
        spec_begin(s, f)
    }
}

/// A store call a flight waited on has its answer.
#[verifier::opaque]
pub open spec fn spec_flight_completed(s: S, fid: FlightId, op: OpId, outcome: StoreRes) -> S {
    if !s.flights.inflight.contains_key(fid) {
        s
    } else {
        let f = s.flights.inflight[fid];
        let s = spec_take_flight(s, fid);
        if f.phase.expects() != Some(op) {
            spec_inflight(s, f)
        } else {
            spec_answered_phase(s, fid, FlightSpec { phase: PhaseSpec::Idle, ..f }, f.phase, outcome)
        }
    }
}

/// The phase the flight was in says what the answer is for.
#[verifier::opaque]
pub open spec fn spec_answered_phase(s: S, fid: FlightId, f0: FlightSpec, phase: PhaseSpec, outcome: StoreRes) -> S {
    match phase {
        PhaseSpec::Loading { revalidating, .. } => spec_answered_loading(s, f0, revalidating, outcome),
        PhaseSpec::Origin { commit, done } => spec_answered_origin(s, fid, f0, commit, done, outcome),
        PhaseSpec::Schedule { commit, done } => spec_answered_schedule(s, fid, f0, commit, done, outcome),
        PhaseSpec::FireLoadingSchedule { .. } => spec_answered_fire_loading_schedule(s, f0, outcome),
        PhaseSpec::FireLoadingOrigin { revalidating, ctx, .. } => spec_answered_fire_loading_origin(s, f0, revalidating, ctx, outcome),
        PhaseSpec::FireIdle { commit } => spec_answered_fire_idle(s, fid, f0, commit, outcome),
        PhaseSpec::FireOrigin { commit, ctx, t, outbox } => spec_answered_fire_origin(s, fid, f0, commit, ctx, t, outbox, outcome),
        PhaseSpec::FireSchedule { commit } => spec_answered_fire_schedule(s, fid, f0, commit, outcome),
        _ => spec_fail(s, f0, "an answer the flight did not wait for"@),
    }
}

#[verifier::opaque]
pub open spec fn spec_answered_loading(s: S, f0: FlightSpec, revalidating: Option<CachedSpec>, outcome: StoreRes) -> S {
    match f0.target {
        TargetSpec::Origin(origin) => {
            let (s, r) = spec_loaded_origin(s, origin, revalidating, outcome);
            match r {
                Ok(w) => spec_run_origin(s, f0, w),
                Err(e) => spec_fail(s, f0, e),
            }
        },
        TargetSpec::Schedule(id) => {
            let (s, r) = crate::handler_sched::spec_loaded_schedule(s, id, outcome);
            match r {
                Ok(w) => crate::handler_sched::spec_run_schedule(s, f0, w),
                Err(e) => spec_fail(s, f0, e),
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn spec_answered_origin(s: S, fid: FlightId, f0: FlightSpec, commit: CommittingSpec, done: DoneSpec, outcome: StoreRes) -> S {
    let (s, commit, p) = spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::Origin { commit, done }, ..f0 }),
        ProgressSpec::Done(fired) => spec_committed(s, f0, done, fired),
        ProgressSpec::Failed(e) => spec_commit_failed(s, f0, e),
    }
}

#[verifier::opaque]
pub open spec fn spec_answered_schedule(s: S, fid: FlightId, f0: FlightSpec, commit: CommittingSpec, done: DoneSpec, outcome: StoreRes) -> S {
    let (s, commit, p) = spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::Schedule { commit, done }, ..f0 }),
        ProgressSpec::Done(fired) => spec_committed(s, f0, done, fired),
        ProgressSpec::Failed(e) => spec_commit_failed(s, f0, e),
    }
}

#[verifier::opaque]
pub open spec fn spec_answered_fire_loading_schedule(s: S, f0: FlightSpec, outcome: StoreRes) -> S {
    match f0.work {
        WorkSpec::Fire { schedule, .. } => {
            let (s, r) = crate::handler_sched::spec_loaded_schedule(s, schedule, outcome);
            match r {
                Ok(ws) => crate::handler_sched::spec_fire_decide(s, f0, ws),
                Err(e) => spec_fail(s, f0, e),
            }
        },
        _ => spec_fail(s, f0, "not a fire"@),
    }
}

#[verifier::opaque]
pub open spec fn spec_answered_fire_loading_origin(s: S, f0: FlightSpec, revalidating: Option<CachedSpec>, ctx: FireCtxSpec, outcome: StoreRes) -> S {
    let (s, r) = spec_loaded_origin(s, ctx.origin, revalidating, outcome);
    match r {
        Ok(wo) => crate::handler_sched::spec_fire_run(s, f0, ctx, wo),
        Err(e) => spec_fail(spec_release(s, ctx.origin), f0, e),
    }
}

#[verifier::opaque]
pub open spec fn spec_answered_fire_idle(s: S, fid: FlightId, f0: FlightSpec, commit: CommittingSpec, outcome: StoreRes) -> S {
    let (s, commit, p) = spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::FireIdle { commit }, ..f0 }),
        ProgressSpec::Done(fired) => {
            let s = spec_note(s, NoteSpec::SweepEnd { flight: fid, committed: true });
            let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Committed));
            spec_finish(s, f0, Ok(fired))
        },
        ProgressSpec::Failed(e) => {
            let s = spec_note(s, NoteSpec::SweepEnd { flight: fid, committed: false });
            spec_commit_failed(s, f0, e)
        },
    }
}

#[verifier::opaque]
pub open spec fn spec_answered_fire_origin(
    s: S,
    fid: FlightId,
    f0: FlightSpec,
    commit: CommittingSpec,
    ctx: FireCtxSpec,
    t: u64,
    outbox: Seq<(Seq<char>, MessageSpec)>,
    outcome: StoreRes,
) -> S {
    let (s, commit, p) = spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::FireOrigin { commit, ctx, t, outbox }, ..f0 }),
        ProgressSpec::Done(_) => {
            let s = spec_note(s, NoteSpec::FireEnd { flight: fid, committed: true });
            let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Committed));
            let s = spec_send_all(s, outbox);
            let s = spec_release(s, ctx.origin);
            crate::handler_sched::spec_fire_advance(s, f0, ctx, t)
        },
        ProgressSpec::Failed(e) => {
            let s = spec_note(s, NoteSpec::FireEnd { flight: fid, committed: false });
            let s = spec_forget_origin(s, ctx.origin);
            let s = spec_release(s, ctx.origin);
            spec_commit_failed(s, f0, e)
        },
    }
}

#[verifier::opaque]
pub open spec fn spec_answered_fire_schedule(s: S, fid: FlightId, f0: FlightSpec, commit: CommittingSpec, outcome: StoreRes) -> S {
    let (s, commit, p) = spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::FireSchedule { commit }, ..f0 }),
        ProgressSpec::Done(fired) => {
            let s = spec_note(s, NoteSpec::AdvanceEnd { flight: fid, committed: true });
            let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Committed));
            spec_finish(s, f0, Ok(fired))
        },
        ProgressSpec::Failed(e) => {
            let s = spec_note(s, NoteSpec::AdvanceEnd { flight: fid, committed: false });
            spec_commit_failed(s, f0, e)
        },
    }
}

/// Ask for a workflow document: revalidated against the store when the
/// cache holds a version, read in full otherwise.
#[verifier::opaque]
pub open spec fn spec_load_origin(s: S, fid: FlightId, origin: Seq<char>) -> (S, OpId, Option<CachedSpec>) {
    let key = spec_doc_key(s.keys.prefix, origin);
    let (cache, hit) = crate::cache::spec_get(s.cache, origin);
    let s = S { cache, ..s };
    match hit {
        Some(c) => {
            let (s, op) = spec_store(s, StoreReqSpec::GetIfNoneMatch { key, etag: c.etag }, Owner::Flight(fid));
            (s, op, Some(c))
        },
        None => {
            let s = spec_note(s, NoteSpec::Cache(CacheResult::Miss));
            let (s, op) = spec_store(s, StoreReqSpec::Get { key }, Owner::Flight(fid));
            (s, op, None)
        },
    }
}

pub open spec fn spec_working(origin: Seq<char>, key: Seq<char>, loaded: LoadedSpec, etag: Option<EtagSpec>) -> WorkingSpec {
    WorkingSpec { target: origin, key, loaded, etag }
}

/// The store answered a load of `origin`. Cache bookkeeping is on the
/// fleet's time.
#[verifier::opaque]
pub open spec fn spec_loaded_origin(s: S, origin: Seq<char>, revalidating: Option<CachedSpec>, outcome: StoreRes) -> (S, Result<WorkingSpec, Seq<char>>) {
    let now = spec_now(s);
    let key = spec_doc_key(s.keys.prefix, origin);
    match revalidating {
        Some(c) => match outcome {
            StoreRes::GetIfNoneMatch { result: Ok(Read::NotModified) } => {
                let s = spec_note(s, NoteSpec::Cache(CacheResult::Revalidated));
                let s = spec_remember(s, origin, CachedSpec { filled_at: now, ..c });
                (s, Ok(spec_working(origin, key, c.loaded, Some(c.etag))))
            },
            StoreRes::GetIfNoneMatch { result: Ok(Read::Absent) } => {
                let s = spec_note(s, NoteSpec::Cache(CacheResult::Absent));
                let s = spec_forget_origin(s, origin);
                (s, Ok(spec_working(origin, key, document::spec_empty_workflow(origin), None)))
            },
            StoreRes::GetIfNoneMatch { result: Ok(Read::Body(bytes, etag)) } => {
                let s = spec_note(s, NoteSpec::Cache(CacheResult::Refreshed));
                match document::spec_decode_workflow(bytes@) {
                    Ok(loaded) => {
                        let s = spec_remember(s, origin, CachedSpec { loaded, etag: etag.deep_view(), filled_at: now });
                        (s, Ok(spec_working(origin, key, loaded, Some(etag.deep_view()))))
                    },
                    Err(e) => (s, Err(e)),
                }
            },
            StoreRes::GetIfNoneMatch { result: Err(e) } => (s, Err(spec_error_text(e.deep_view()))),
            _ => (s, Err(spec_error_text(spec_unexpected()))),
        },
        None => match outcome {
            StoreRes::Get { result: Ok(None) } => (s, Ok(spec_working(origin, key, document::spec_empty_workflow(origin), None))),
            StoreRes::Get { result: Ok(Some((bytes, etag))) } => match document::spec_decode_workflow(bytes@) {
                Ok(loaded) => {
                    let s = spec_remember(s, origin, CachedSpec { loaded, etag: etag.deep_view(), filled_at: now });
                    (s, Ok(spec_working(origin, key, loaded, Some(etag.deep_view()))))
                },
                Err(e) => (s, Err(e)),
            },
            StoreRes::Get { result: Err(e) } => (s, Err(spec_error_text(e.deep_view()))),
            _ => (s, Err(spec_error_text(spec_unexpected()))),
        },
    }
}

/// Run the flight's step on a workflow document and start its commit.
#[verifier::opaque]
pub open spec fn spec_run_origin(s: S, f: FlightSpec, w: WorkingSpec) -> S {
    let (s, commit, done) = spec_decide(s, f.work, w);
    let (s, commit, p) = spec_commit_advance(s, f.id, commit, None);
    match p {
        ProgressSpec::Issued => spec_inflight(s, FlightSpec { phase: PhaseSpec::Origin { commit, done }, ..f }),
        ProgressSpec::Done(fired) => spec_committed(s, f, done, fired),
        ProgressSpec::Failed(e) => spec_commit_failed(s, f, e),
    }
}

/// The step: the concrete model's, on the document, decided no earlier
/// than the last step on it.
#[verifier::opaque]
pub open spec fn spec_decide(s: S, work: WorkSpec, w: WorkingSpec) -> (S, CommittingSpec, DoneSpec) {
    let now = document::spec_clamp_now(document::spec_loaded_committed_at(w.loaded), work.now());
    let job = match work {
        WorkSpec::Request { req, .. } => AJob::Request(req),
        WorkSpec::Sweep { .. } => AJob::Sweep,
        WorkSpec::Fire { .. } => AJob::Fire,
    };
    let (after, response, _born, notes) = spec_step(job, document::spec_loaded_body(w.loaded), now, s.cfg.retry_timeout);
    let why = match work {
        WorkSpec::Request { req, kind, .. } => match response {
            Some(r) => {
                let status = crate::reason::spec_status_of(r@);
                if status >= 400 { Some(crate::reason::spec_reason_for(kind, req, status, after)) } else { None }
            },
            None => None,
        },
        _ => None,
    };
    let outbox = spec_dispatches(after, notes);
    let deadline = spec_body_deadline(after);
    let fired = match work {
        WorkSpec::Sweep { fired, .. } => fired,
        _ => None,
    };
    let (s, commit) = spec_commit_new(s, w, after, deadline, now, fired);
    let did = work.is_sweep() && commit.seq.changed;
    (s, commit, DoneSpec { response, why, outbox, did })
}

pub open spec fn spec_send_all(s: S, outbox: Seq<(Seq<char>, MessageSpec)>) -> S
    decreases outbox.len(),
{
    if outbox.len() == 0 {
        s
    } else {
        spec_send_all(spec_emit(s, EffectSpec::Send { address: outbox[0].0, message: outbox[0].1 }), outbox.drop_first())
    }
}

/// A committed step: the messages out, the answer back.
#[verifier::opaque]
pub open spec fn spec_committed(s: S, f: FlightSpec, done: DoneSpec, fired: Fired) -> S {
    let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Committed));
    let s = spec_send_all(s, done.outbox);
    let s = match f.work {
        WorkSpec::Request { id, kind, corr, action_kind, .. } => {
            let response = match done.response {
                Some(response) => Ok(AnswerSpec::Step { kind, corr, action_kind, response, why: done.why }),
                None => Err("no answer"@),
            };
            spec_emit(s, EffectSpec::Reply { id, response })
        },
        WorkSpec::Sweep { .. } => {
            let s = spec_note(s, NoteSpec::Sweep(if done.did { SweepOutcome::Fired } else { SweepOutcome::Idle }));
            spec_note(s, NoteSpec::SweepEnd { flight: f.id, committed: true })
        },
        WorkSpec::Fire { .. } => s,
    };
    spec_finish(s, FlightSpec { idle: !done.did, ..f }, Ok(fired))
}

/// The commit's store call failed: a lost race re-decides, anything else
/// ends the flight with nothing cached.
#[verifier::opaque]
pub open spec fn spec_commit_failed(s: S, f: FlightSpec, e: StoreErrorSpec) -> S {
    let s = match f.target {
        TargetSpec::Origin(o) => spec_forget_origin(s, o),
        _ => s,
    };
    match e {
        StoreErrorSpec::PreconditionFailed => {
            let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Raced));
            let s = spec_note(s, NoteSpec::Raced { target: crate::target::spec_name(f.target), attempt: f.attempt });
            spec_retry(s, f)
        },
        _ => {
            let s = spec_note(s, NoteSpec::Commit(CommitOutcome::Failed));
            spec_fail(s, f, spec_error_text(e))
        },
    }
}

/// The flight ends without a commit.
#[verifier::opaque]
pub open spec fn spec_fail(s: S, f: FlightSpec, e: Seq<char>) -> S {
    let s = match f.work {
        WorkSpec::Request { id, .. } => spec_emit(s, EffectSpec::Reply { id, response: Err(e) }),
        WorkSpec::Sweep { .. } => {
            let s = spec_note(s, NoteSpec::Sweep(SweepOutcome::Failed));
            spec_note(s, NoteSpec::SweepEnd { flight: f.id, committed: false })
        },
        WorkSpec::Fire { .. } => s,
    };
    spec_finish(s, f, Err(e))
}

/// The flight is over: its slot goes to the next, and the key that fired
/// it hears how it went.
#[verifier::opaque]
pub open spec fn spec_finish(s: S, f: FlightSpec, r: Result<Fired, Seq<char>>) -> S {
    let s = spec_release(s, crate::target::spec_name(f.target));
    let s = match f.firing {
        Some(firing) => crate::handler_timers::spec_timer_fired(s, firing, spec_now(s), r),
        None => s,
    };
    if f.debug { crate::debug::spec_debug_flight_done(s, f.work, f.idle) } else { s }
}

/// The decisions before the first store call: whether the document
/// changed, and the verified sequence, planned from the document's nearest
/// deadline. `fired` is the key whose firing this is.
#[verifier::opaque]
pub open spec fn spec_commit_new(s: S, w: WorkingSpec, after: DocumentBodyV, deadline: Option<nat>, now: u64, fired: Option<AFired>) -> (S, CommittingSpec) {
    let changed_any = document::spec_loaded_body(w.loaded) != after;
    let etag = match w.etag {
        Some(e) => Some(e.0),
        None => None,
    };
    let (s, token) = spec_token(s);
    let seq = spec_new(s.node.core, w.target, etag, deadline, changed_any, fired, token as nat);
    let after = echod_concrete::node::spec_advance_stored(w.loaded.document, after, now);
    (s, CommittingSpec { w, after, now, seq, issued: None })
}

/// Drive a commit: `answer` is the store's answer to the call the commit
/// waits on, if it waits on one. The wheel and the cache follow the
/// answer; the sequence decides the next call; this makes it.
#[verifier::opaque]
pub open spec fn spec_commit_advance(s: S, fid: FlightId, c: CommittingSpec, answer: Option<StoreRes>) -> (S, CommittingSpec, ProgressSpec) {
    let (s, c) = match c.issued {
        Some(issued) => spec_answered(s, CommittingSpec { issued: None, ..c }, issued, answer),
        None => (s, c),
    };
    let (seq, core, outcome) = spec_advance(c.seq, s.node.core, answer_v(c.seq.step, answer));
    let s = S { node: NodeSpec { core, ..s.node }, ..s };
    let c = CommittingSpec { seq, ..c };
    match outcome {
        AOutcome::Act(AAct::PutKey(key)) => {
            let name = spec_key_name(s, key, s.cfg.node_id);
            let (s, op) = spec_store(s, StoreReqSpec::Put { key: name, body: Seq::empty() }, Owner::Flight(fid));
            (s, CommittingSpec { issued: Some(IssuedSpec::Key { op, key, name, arm: true }), ..c }, ProgressSpec::Issued)
        },
        AOutcome::Act(AAct::Write { cond, idle }) => {
            let (s, c) = spec_issue_write(s, fid, c, cond, idle);
            (s, c, ProgressSpec::Issued)
        },
        AOutcome::Act(AAct::DeleteKey { key, by }) => {
            let name = spec_key_name(s, key, by);
            let (s, op) = spec_store(s, StoreReqSpec::Del { key: name }, Owner::Flight(fid));
            (s, CommittingSpec { issued: Some(IssuedSpec::Key { op, key, name, arm: false }), ..c }, ProgressSpec::Issued)
        },
        AOutcome::Act(AAct::Done { deleted }) => (s, c, ProgressSpec::Done(if deleted { Fired::Deleted } else { Fired::Kept })),
        AOutcome::Failed(Some(e)) => (s, c, ProgressSpec::Failed(e.deep_view())),
        AOutcome::Failed(None) => (s, c, ProgressSpec::Failed(spec_unexpected())),
    }
}

/// What follows from the answer to the last call, outside the sequence: a
/// key put is armed in the wheel, a key deleted leaves it (a delete that
/// failed is noted; the key fires again and is collected then), a document
/// written is remembered.
#[verifier::opaque]
pub open spec fn spec_answered(s: S, c: CommittingSpec, issued: IssuedSpec, answer: Option<StoreRes>) -> (S, CommittingSpec) {
    match issued {
        IssuedSpec::Key { key, name, arm, .. } => match answer {
            Some(StoreRes::Put { result: Ok(()) }) | Some(StoreRes::Del { result: Ok(()) }) => {
                let armed = if arm {
                    crate::state_timers::spec_arm(s.timers.wheel.armed, key.at as u64, name)
                } else {
                    crate::state_timers::spec_disarm(s.timers.wheel.armed, key.at as u64, name)
                };
                (S { timers: TimersSpec { wheel: TimerWheelSpec { armed }, ..s.timers }, ..s }, c)
            },
            Some(StoreRes::Put { result: Err(e) }) | Some(StoreRes::Del { result: Err(e) }) => {
                if arm { (s, c) } else { (spec_note(s, NoteSpec::KeyNotDeleted { key: name, error: spec_error_text(e.deep_view()) }), c) }
            },
            _ => (s, c),
        },
        IssuedSpec::Write { mode, change_count, bytes, len, .. } => match answer {
            Some(StoreRes::PutIfMatch { result: Ok(etag) })
            | Some(StoreRes::PutIfNoneMatch { result: Ok(etag) })
            | Some(StoreRes::AppIfMatch { result: Ok(etag) }) => {
                let s = spec_note(s, NoteSpec::DocumentWrite { mode, bytes: len });
                let s = if c.after is Workflow {
                    spec_remember(s, c.w.target, CachedSpec {
                        loaded: LoadedSpec {
                            document: c.after,
                            change_count: change_count,
                            bytes,
                        },
                        etag: etag.deep_view(),
                        filled_at: spec_now(s),
                    })
                } else {
                    s
                };
                (s, CommittingSpec { w: WorkingSpec { etag: Some(etag.deep_view()), ..c.w }, ..c })
            },
            _ => (s, c),
        },
    }
}

/// Write the document at a new version, conditionally on `cond`, the
/// version loaded: the rows the step changed appended, or the whole
/// document.
#[verifier::opaque]
pub open spec fn spec_issue_write(s: S, fid: FlightId, c: CommittingSpec, cond: Option<Seq<char>>, idle: bool) -> (S, CommittingSpec) {
    let (call, mode, change_count, bytes) = match cond {
        None => {
            let after = echod_concrete::node::spec_stored_body(c.after);
            let body = document::spec_encode(c.after);
            (StoreReqSpec::PutIfNoneMatch { key: c.w.key, body }, WriteMode::Create, echod_concrete::node::spec_body_len(after) as usize, body.len() as u64)
        },
        Some(etag) => {
            let etag = EtagSpec(etag);
            let after = echod_concrete::node::spec_stored_body(c.after);
            let (delta, changed) = document::spec_encode_delta(c.w.loaded.document, c.after);
            let removed = document::spec_removed_any(document::spec_loaded_body(c.w.loaded), after);
            let after_len = echod_concrete::node::spec_body_len(after) as usize;
            let stale_after = c.w.loaded.change_count.saturating_add(changed).saturating_sub(after_len);
            let append = document::spec_loaded_version(c.w.loaded) > 0 && !removed && s.cfg.appendable && s.cfg.compact > 0 && stale_after < s.cfg.compact as usize;
            if append {
                let n = c.w.loaded.change_count.saturating_add(changed);
                let b = c.w.loaded.bytes.saturating_add(delta.len() as u64);
                (StoreReqSpec::AppIfMatch { key: c.w.key, offset: c.w.loaded.bytes, body: delta, etag }, WriteMode::Append, n, b)
            } else {
                let body = document::spec_encode(c.after);
                (StoreReqSpec::PutIfMatch { key: c.w.key, body, etag }, WriteMode::Rewrite, after_len, body.len() as u64)
            }
        },
    };
    let len = match call {
        StoreReqSpec::PutIfNoneMatch { body, .. } | StoreReqSpec::AppIfMatch { body, .. } | StoreReqSpec::PutIfMatch { body, .. } => body.len() as usize,
        _ => 0usize,
    };
    let (s, op) = spec_store(s, call, Owner::Flight(fid));
    (s, CommittingSpec { issued: Some(IssuedSpec::Write { op, mode, change_count, bytes, len }), ..c })
}

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
            Phase::FireOrigin { commit, ctx, t, outbox } => self.answered_fire_origin(fid, f, commit, ctx, t, outbox, outcome),
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

    fn answered_fire_origin(
        &mut self,
        fid: FlightId,
        f: Flight,
        mut commit: Committing,
        ctx: FireCtx,
        t: u64,
        outbox: Vec<(String, Message)>,
        outcome: StoreRes,
    )
        ensures
            final(self).deep_view() == spec_answered_fire_origin(
                old(self).deep_view(),
                fid,
                f.deep_view(),
                commit.deep_view(),
                ctx.deep_view(),
                t,
                outbox.deep_view(),
                outcome,
            ),
    {
        proof {
            reveal(spec_answered_fire_origin);
        }
        match self.commit_advance(fid, &mut commit, Some(outcome)) {
            Progress::Issued => {
                let f = Flight { phase: Phase::FireOrigin { commit, ctx, t, outbox }, ..f };
                self.inflight(f);
            },
            Progress::Done(_) => {
                self.note(Note::FireEnd { flight: fid, committed: true });
                self.note(Note::Commit(CommitOutcome::Committed));
                self.send_all(outbox);
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

    /// The step: `verified::flight::decide`, the concrete model's transition
    /// on the document, decided no earlier than the last transition on it.
    /// A lost race recomputes the transition on the reloaded document.
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
        let Decided { doc: after, response, born: _, notes } = flight::decide(job, document::loaded_body(&w.loaded), now, self.cfg.retry_timeout);
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

    pub(crate) fn send_all(&mut self, outbox: Vec<(String, Message)>)
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
            Work::Request { id, kind, corr, action_kind, .. } => {
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
            (final(self).deep_view(), c.deep_view()) == spec_commit_new(old(self).deep_view(), w.deep_view(), after@, echod_concrete::node::nat_v(deadline), now, fired.deep_view()),
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
