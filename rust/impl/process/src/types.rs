//! The vocabulary the core is written in: what it is told, what it answers
//! with, and the shapes those two carry.
//!
//! Everything here is data. `Event` is the only way in, `Effect` the only
//! way out. A store call goes out as an `Effect::Store` under an `OpId`
//! and its answer comes back as `Event::Completed` under the same id; the
//! core keeps, per id, which machine is waiting for it. No decision is made
//! in this file: that is `State` in the crate root and the machines beside
//! it.
//!
//! Each type views as its `…Spec`: a string as its characters, a vector as
//! a sequence, a record of the models as its own view.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use echod_types::{PromiseRecord, Request, Response, Schedule};

use crate::target::Target;

pub use crate::concrete::{Etag, Read, StoreCall, StoreError, StoreOutcome};
pub use crate::verified::flight::FiredKey;

#[cfg(verus_keep_ghost)]
use echod_types::{PromiseRecordSpec, ScheduleSpec, AResponse};
#[cfg(verus_keep_ghost)]
use rover_concrete_spec::store::{StoreCallSpec, StoreErrorSpec};
#[cfg(verus_keep_ghost)]
use rover_concrete_spec::node::DocV;
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;

verus! {

/// Names a store call the executor was asked to make.
pub type OpId = u64;
/// Names a request the executor handed in and wants an answer to.
pub type RequestId = u64;
/// Names one step on one document, from its start to its answer.
pub type FlightId = u64;

/// What a node pushes to a worker: a task to run, or a promise a listener
/// waited on, settled. The concrete model's `Outbound`, addressed.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Message {
    Execute { task_id: String, version: u64 },
    Unblock(PromiseRecord),
}

#[cfg(verus_keep_ghost)]
pub ghost enum MessageSpec {
    Execute { task_id: Seq<char>, version: u64 },
    Unblock(PromiseRecordSpec),
}

#[cfg(verus_keep_ghost)]
impl DeepView for Message {
    type V = MessageSpec;
    open spec fn deep_view(&self) -> MessageSpec {
        match self {
            Message::Execute { task_id, version } => MessageSpec::Execute { task_id: task_id@, version: *version },
            Message::Unblock(r) => MessageSpec::Unblock(r.deep_view()),
        }
    }
}

// ---------------------------------------------------------------------------
// In
// ---------------------------------------------------------------------------

/// A request the runtime has already accepted. The core never sees an
/// envelope, a header, or a parse error.
#[make_spec_type]
pub struct Call {
    pub id: RequestId,
    pub kind: String,
    pub corr: String,
    pub target: Target,
    pub request: Request,
    pub action_kind: Option<String>,
    /// The instant the runtime offers. When `pinned`, the step is decided
    /// at this instant as given: a debug request named it. Otherwise the
    /// step is decided at this instant or the latest announcement,
    /// whichever is later.
    pub now: u64,
    pub pinned: bool,
    /// A second request, on another document, once the first has committed.
    pub then: Option<(Target, Request)>,
}

/// A debug operation the runtime has already accepted.
pub enum DebugCall {
    Reset { id: RequestId, kind: String, corr: String },
    Snap { id: RequestId, kind: String, corr: String },
    Tick { id: RequestId, kind: String, corr: String, time: u64 },
}

#[cfg(verus_keep_ghost)]
pub ghost enum DebugCallSpec {
    Reset { id: RequestId, kind: Seq<char>, corr: Seq<char> },
    Snap { id: RequestId, kind: Seq<char>, corr: Seq<char> },
    Tick { id: RequestId, kind: Seq<char>, corr: Seq<char>, time: u64 },
}

#[cfg(verus_keep_ghost)]
impl DeepView for DebugCall {
    type V = DebugCallSpec;
    open spec fn deep_view(&self) -> DebugCallSpec {
        match self {
            DebugCall::Reset { id, kind, corr } => DebugCallSpec::Reset { id: *id, kind: kind@, corr: corr@ },
            DebugCall::Snap { id, kind, corr } => DebugCallSpec::Snap { id: *id, kind: kind@, corr: corr@ },
            DebugCall::Tick { id, kind, corr, time } => DebugCallSpec::Tick { id: *id, kind: kind@, corr: corr@, time: *time },
        }
    }
}

/// Which loop a physical wake was armed for. The runtime sleeps, then hands
/// this back as `Event::Due`. The keys themselves stay in the wheel: one
/// wake can owe several of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum Armed {
    /// The heartbeat interval.
    Heartbeat,
    /// The wheel: a deadline falling due, or a bucket listing.
    Wheel,
}

#[cfg(verus_keep_ghost)]
impl DeepView for Armed {
    type V = Armed;
    open spec fn deep_view(&self) -> Armed {
        *self
    }
}

/// What the core is told. Every event carries the node's clock as the
/// executor read it when the event happened; the core never reads a clock.
#[allow(inconsistent_fields)]
pub enum Event {
    /// The node starts. `loops` says whether it keeps itself going: the
    /// heartbeat and the timers. Without them it answers requests and does
    /// nothing on its own.
    Start { clock: u64, loops: bool },
    /// A request came in; the answer goes out as `Effect::Reply` under `id`.
    /// `clock` is the node's clock. `call.now` is the instant the step is
    /// decided at, which a debug request may set ahead of that clock.
    Request { clock: u64, call: Call },
    /// A debug operation, already checked. Answered only in debug mode,
    /// which the runtime decides before it asks.
    Debug { clock: u64, call: DebugCall },
    /// A store call the core issued has an answer.
    Completed { op: OpId, outcome: StoreOutcome, clock: u64 },
    /// The runtime slept until a loop this process armed, and that instant
    /// has come. `armed` is the loop the sleep was for. A late wake still
    /// runs the other loop when its time has come.
    Due { clock: u64, armed: Armed },
    /// The node stops: it withdraws its announcement and runs no loop.
    Stop { clock: u64 },
}

#[allow(inconsistent_fields)]
#[cfg(verus_keep_ghost)]
pub ghost enum EventSpec {
    Start { clock: u64, loops: bool },
    Request { clock: u64, call: CallSpec },
    Debug { clock: u64, call: DebugCallSpec },
    Completed { op: OpId, outcome: StoreOutcome, clock: u64 },
    Due { clock: u64, armed: Armed },
    Stop { clock: u64 },
}

#[cfg(verus_keep_ghost)]
impl DeepView for Event {
    type V = EventSpec;
    open spec fn deep_view(&self) -> EventSpec {
        match self {
            Event::Start { clock, loops } => EventSpec::Start { clock: *clock, loops: *loops },
            Event::Request { clock, call } => EventSpec::Request { clock: *clock, call: call.deep_view() },
            Event::Debug { clock, call } => EventSpec::Debug { clock: *clock, call: call.deep_view() },
            Event::Completed { op, outcome, clock } => EventSpec::Completed { op: *op, outcome: *outcome, clock: *clock },
            Event::Due { clock, armed } => EventSpec::Due { clock: *clock, armed: *armed },
            Event::Stop { clock } => EventSpec::Stop { clock: *clock },
        }
    }
}

// ---------------------------------------------------------------------------
// Out
// ---------------------------------------------------------------------------

/// What a client is told. The runtime turns it into the protocol's envelope.
pub enum Answer {
    /// A document step.
    Step { kind: String, corr: String, action_kind: Option<String>, response: Response, why: Option<String> },
    /// A debug operation.
    Debug { kind: String, corr: String, status: u16, body: DebugBody },
}

#[cfg(verus_keep_ghost)]
pub ghost enum AnswerSpec {
    Step { kind: Seq<char>, corr: Seq<char>, action_kind: Option<Seq<char>>, response: AResponse, why: Option<Seq<char>> },
    Debug { kind: Seq<char>, corr: Seq<char>, status: u16, body: DebugBodySpec },
}

#[cfg(verus_keep_ghost)]
impl DeepView for Answer {
    type V = AnswerSpec;
    open spec fn deep_view(&self) -> AnswerSpec {
        match self {
            Answer::Step { kind, corr, action_kind, response, why } => AnswerSpec::Step {
                kind: kind@, corr: corr@, action_kind: action_kind.deep_view(), response: response.deep_view(), why: why.deep_view(),
            },
            Answer::Debug { kind, corr, status, body } => AnswerSpec::Debug { kind: kind@, corr: corr@, status: *status, body: body.deep_view() },
        }
    }
}

/// The body of a debug answer, before it is an envelope.
pub enum DebugBody {
    /// `{}`.
    Object,
    /// `[]`.
    List,
    /// A short refusal.
    Message(String),
    /// The documents a `debug.snap` read: every origin's, and every schedule.
    Snap { origins: Vec<crate::concrete::Doc>, schedules: Vec<Schedule> },
}

#[cfg(verus_keep_ghost)]
pub ghost enum DebugBodySpec {
    Object,
    List,
    Message(Seq<char>),
    Snap { origins: Seq<DocV>, schedules: Seq<ScheduleSpec> },
}

#[cfg(verus_keep_ghost)]
impl DeepView for DebugBody {
    type V = DebugBodySpec;
    open spec fn deep_view(&self) -> DebugBodySpec {
        match self {
            DebugBody::Object => DebugBodySpec::Object,
            DebugBody::List => DebugBodySpec::List,
            DebugBody::Message(s) => DebugBodySpec::Message(s@),
            DebugBody::Snap { origins, schedules } => DebugBodySpec::Snap { origins: origins.deep_view(), schedules: schedules.deep_view() },
        }
    }
}

/// What the core asks the executor to do.
pub enum Effect {
    /// Make this call on the store and answer with `Event::Completed { op }`.
    Store { op: OpId, call: StoreCall },
    /// Answer the request handed in under `id`. `Err` is a 503: the node
    /// could not serve it.
    Reply { id: RequestId, response: Result<Answer, String> },
    /// Push a message to a worker. At most once; nothing is reported back.
    Send { address: String, message: Message },
    /// Send `Event::Due` for `armed` once `after_ms` have passed, replacing
    /// any wake asked for before.
    Wake { after_ms: u64, armed: Armed },
    /// Something happened that an operator, a log or a simulation may want
    /// to know. Nothing depends on it.
    Note(Note),
}

#[cfg(verus_keep_ghost)]
pub ghost enum EffectSpec {
    Store { op: OpId, call: StoreCallSpec },
    Reply { id: RequestId, response: Result<AnswerSpec, Seq<char>> },
    Send { address: Seq<char>, message: MessageSpec },
    Wake { after_ms: u64, armed: Armed },
    Note(NoteSpec),
}

#[cfg(verus_keep_ghost)]
impl DeepView for Effect {
    type V = EffectSpec;
    open spec fn deep_view(&self) -> EffectSpec {
        match self {
            Effect::Store { op, call } => EffectSpec::Store { op: *op, call: call.deep_view() },
            Effect::Reply { id, response } => EffectSpec::Reply { id: *id, response: response.deep_view() },
            Effect::Send { address, message } => EffectSpec::Send { address: address@, message: message.deep_view() },
            Effect::Wake { after_ms, armed } => EffectSpec::Wake { after_ms: *after_ms, armed: *armed },
            Effect::Note(n) => EffectSpec::Note(n.deep_view()),
        }
    }
}

/// What became of the key that fired a sweep.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum Fired {
    /// Deleted from the bucket.
    Deleted,
    /// Still in the bucket: the delete failed. It fires again.
    Kept,
}

#[cfg(verus_keep_ghost)]
impl DeepView for Fired {
    type V = Fired;
    open spec fn deep_view(&self) -> Fired {
        *self
    }
}

// ---------------------------------------------------------------------------
// Notes: the closed sets an operator sees
// ---------------------------------------------------------------------------

/// How a document was written.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural)]
pub enum WriteMode { Create, Rewrite, Append }

/// How an attempt to commit a step ended.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural)]
pub enum CommitOutcome { Committed, Raced, Failed, Exhausted }

/// What a document load cost.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural)]
pub enum CacheResult { Revalidated, Refreshed, Absent, Miss }

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural)]
pub enum ConfigWrite { Written, Conflict, Failed }

/// What a timer key names.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural)]
pub enum TimerKind { Origin, Schedule }

/// What became of a key fired from the wheel.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural)]
pub enum FireOutcome { Deleted, Kept, Failed, Deferred }

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural)]
pub enum SweepOutcome { Fired, Idle, Failed }

// A label is its own view.
#[cfg(verus_keep_ghost)]
impl DeepView for WriteMode {
    type V = WriteMode;
    open spec fn deep_view(&self) -> WriteMode {
        *self
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for CommitOutcome {
    type V = CommitOutcome;
    open spec fn deep_view(&self) -> CommitOutcome {
        *self
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for CacheResult {
    type V = CacheResult;
    open spec fn deep_view(&self) -> CacheResult {
        *self
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for ConfigWrite {
    type V = ConfigWrite;
    open spec fn deep_view(&self) -> ConfigWrite {
        *self
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for TimerKind {
    type V = TimerKind;
    open spec fn deep_view(&self) -> TimerKind {
        *self
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for FireOutcome {
    type V = FireOutcome;
    open spec fn deep_view(&self) -> FireOutcome {
        *self
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for SweepOutcome {
    type V = SweepOutcome;
    open spec fn deep_view(&self) -> SweepOutcome {
        *self
    }
}


/// What the core reports as it goes. The counted ones carry a value from a
/// closed set, never a name a client or the bucket supplied; the observed
/// ones carry what a simulation needs to account for a step no client
/// sees; the logged ones carry what a log line wants.
pub enum Note {
    // counted
    DocumentWrite { mode: WriteMode, bytes: usize },
    Commit(CommitOutcome),
    Cache(CacheResult),
    MembershipRefresh { ok: bool },
    ConfigurationChange,
    ConfigurationWrite(ConfigWrite),
    TimerFire { kind: TimerKind, outcome: FireOutcome, lag_ms: u64 },
    TimerListing { ok: bool },
    Sweep(SweepOutcome),
    // observed: the internal steps, each as a span over its commit
    /// A sweep of `target` at `now` starts.
    SweepBegin { flight: FlightId, target: String, now: u64 },
    SweepEnd { flight: FlightId, committed: bool },
    /// A schedule fires on `origin` at `now`: the row as loaded, the
    /// occurrence, the promise it expands to, the run after. The first
    /// half of a fire.
    FireBegin { flight: FlightId, origin: String, now: u64, row: Box<Schedule>, at: u64, promise_id: String, next: u64 },
    FireEnd { flight: FlightId, committed: bool },
    /// The second half: the schedule advanced past the occurrence at `at`
    /// to `next`, on its own document.
    AdvanceBegin { flight: FlightId, schedule: String, now: u64, at: u64, next: u64 },
    AdvanceEnd { flight: FlightId, committed: bool },
    // logged
    ConfigurationRead { epoch: u64, members: Vec<String> },
    ConfigurationWritten { epoch: u64, members: Vec<String> },
    TimersLoaded { deadlines: usize, wheel: usize, epoch: u64 },
    BucketLoaded { bucket: u64, deadlines: usize },
    Raced { target: String, attempt: u32 },
    KeyNotDeleted { key: String, error: String },
    KeyUnparseable { key: String },
    FireFailed { key: String, error: String },
    RefreshFailed { error: String },
    ListingFailed { error: String },
    MessageUndeliverable { address: String },
}

#[cfg(verus_keep_ghost)]
pub ghost enum NoteSpec {
    DocumentWrite { mode: WriteMode, bytes: usize },
    Commit(CommitOutcome),
    Cache(CacheResult),
    MembershipRefresh { ok: bool },
    ConfigurationChange,
    ConfigurationWrite(ConfigWrite),
    TimerFire { kind: TimerKind, outcome: FireOutcome, lag_ms: u64 },
    TimerListing { ok: bool },
    Sweep(SweepOutcome),
    SweepBegin { flight: FlightId, target: Seq<char>, now: u64 },
    SweepEnd { flight: FlightId, committed: bool },
    FireBegin { flight: FlightId, origin: Seq<char>, now: u64, row: ScheduleSpec, at: u64, promise_id: Seq<char>, next: u64 },
    FireEnd { flight: FlightId, committed: bool },
    AdvanceBegin { flight: FlightId, schedule: Seq<char>, now: u64, at: u64, next: u64 },
    AdvanceEnd { flight: FlightId, committed: bool },
    ConfigurationRead { epoch: u64, members: Seq<Seq<char>> },
    ConfigurationWritten { epoch: u64, members: Seq<Seq<char>> },
    TimersLoaded { deadlines: usize, wheel: usize, epoch: u64 },
    BucketLoaded { bucket: u64, deadlines: usize },
    Raced { target: Seq<char>, attempt: u32 },
    KeyNotDeleted { key: Seq<char>, error: Seq<char> },
    KeyUnparseable { key: Seq<char> },
    FireFailed { key: Seq<char>, error: Seq<char> },
    RefreshFailed { error: Seq<char> },
    ListingFailed { error: Seq<char> },
    MessageUndeliverable { address: Seq<char> },
}

#[cfg(verus_keep_ghost)]
impl DeepView for Note {
    type V = NoteSpec;
    open spec fn deep_view(&self) -> NoteSpec {
        match self {
            Note::DocumentWrite { mode, bytes } => NoteSpec::DocumentWrite { mode: *mode, bytes: *bytes },
            Note::Commit(o) => NoteSpec::Commit(*o),
            Note::Cache(r) => NoteSpec::Cache(*r),
            Note::MembershipRefresh { ok } => NoteSpec::MembershipRefresh { ok: *ok },
            Note::ConfigurationChange => NoteSpec::ConfigurationChange,
            Note::ConfigurationWrite(w) => NoteSpec::ConfigurationWrite(*w),
            Note::TimerFire { kind, outcome, lag_ms } => NoteSpec::TimerFire { kind: *kind, outcome: *outcome, lag_ms: *lag_ms },
            Note::TimerListing { ok } => NoteSpec::TimerListing { ok: *ok },
            Note::Sweep(o) => NoteSpec::Sweep(*o),
            Note::SweepBegin { flight, target, now } => NoteSpec::SweepBegin { flight: *flight, target: target@, now: *now },
            Note::SweepEnd { flight, committed } => NoteSpec::SweepEnd { flight: *flight, committed: *committed },
            Note::FireBegin { flight, origin, now, row, at, promise_id, next } => NoteSpec::FireBegin {
                flight: *flight, origin: origin@, now: *now, row: row.deep_view(), at: *at, promise_id: promise_id@, next: *next,
            },
            Note::FireEnd { flight, committed } => NoteSpec::FireEnd { flight: *flight, committed: *committed },
            Note::AdvanceBegin { flight, schedule, now, at, next } => NoteSpec::AdvanceBegin { flight: *flight, schedule: schedule@, now: *now, at: *at, next: *next },
            Note::AdvanceEnd { flight, committed } => NoteSpec::AdvanceEnd { flight: *flight, committed: *committed },
            Note::ConfigurationRead { epoch, members } => NoteSpec::ConfigurationRead { epoch: *epoch, members: members.deep_view() },
            Note::ConfigurationWritten { epoch, members } => NoteSpec::ConfigurationWritten { epoch: *epoch, members: members.deep_view() },
            Note::TimersLoaded { deadlines, wheel, epoch } => NoteSpec::TimersLoaded { deadlines: *deadlines, wheel: *wheel, epoch: *epoch },
            Note::BucketLoaded { bucket, deadlines } => NoteSpec::BucketLoaded { bucket: *bucket, deadlines: *deadlines },
            Note::Raced { target, attempt } => NoteSpec::Raced { target: target@, attempt: *attempt },
            Note::KeyNotDeleted { key, error } => NoteSpec::KeyNotDeleted { key: key@, error: error@ },
            Note::KeyUnparseable { key } => NoteSpec::KeyUnparseable { key: key@ },
            Note::FireFailed { key, error } => NoteSpec::FireFailed { key: key@, error: error@ },
            Note::RefreshFailed { error } => NoteSpec::RefreshFailed { error: error@ },
            Note::ListingFailed { error } => NoteSpec::ListingFailed { error: error@ },
            Note::MessageUndeliverable { address } => NoteSpec::MessageUndeliverable { address: address@ },
        }
    }
}

/// The text a store error carries, as `Display` writes it.
pub open spec fn spec_error_text(e: StoreErrorSpec) -> Seq<char> {
    match e {
        StoreErrorSpec::PreconditionFailed => "precondition failed"@,
        StoreErrorSpec::Unavailable(m) => "store unavailable: "@ + m,
    }
}

/// `e.to_string()`.
pub fn error_text(e: &StoreError) -> (r: String)
    ensures
        r@ == spec_error_text(e.deep_view()),
{
    match e {
        StoreError::PreconditionFailed => crate::verified::text::text("precondition failed"),
        StoreError::Unavailable(m) => crate::verified::text::concat("store unavailable: ", m.as_str()),
    }
}

/// The store answered with a shape the call cannot have.
pub fn unexpected() -> (r: StoreError)
    ensures
        r.deep_view() == spec_unexpected(),
{
    StoreError::Unavailable(crate::verified::text::text("the store answered something else"))
}

pub open spec fn spec_unexpected() -> StoreErrorSpec {
    StoreErrorSpec::Unavailable("the store answered something else"@)
}

} // verus!

/// An enum whose variants are a label's values, written in lower case.
macro_rules! label {
    ($name:ident { $($variant:ident => $text:literal),+ $(,)? }) => {
        impl $name {
            pub fn as_str(self) -> &'static str {
                match self { $(Self::$variant => $text),+ }
            }
        }
    };
}

label! { WriteMode { Create => "create", Rewrite => "rewrite", Append => "append" } }
label! { CommitOutcome { Committed => "committed", Raced => "raced", Failed => "failed", Exhausted => "exhausted" } }
label! { CacheResult { Revalidated => "revalidated", Refreshed => "refreshed", Absent => "absent", Miss => "miss" } }
label! { ConfigWrite { Written => "written", Conflict => "conflict", Failed => "failed" } }
label! { TimerKind { Origin => "origin", Schedule => "schedule" } }
label! { FireOutcome { Deleted => "deleted", Kept => "kept", Failed => "failed", Deferred => "deferred" } }
label! { SweepOutcome { Fired => "fired", Idle => "idle", Failed => "failed" } }
