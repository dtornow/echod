//! The vocabulary the core is written in: what it is told, what it answers
//! with, and the shapes those two carry.
//!
//! Everything here is data. Operational work enters as `Event`; startup is
//! inferred from the first delivered event, and shutdown belongs to the
//! shell. `Effect` is the only way out. A `StoreReq` goes out as an
//! `Effect::Store` under an `OpId`
//! and its answer comes back as `Event::Store` under the same id; the
//! core keeps, per id, which machine is waiting for it. No decision is made
//! in this file: that is `State` in the crate root and the machines beside
//! it.
//!
//! Each type views as its `…Spec`: a string as its characters, a vector as
//! a sequence, a record of the models as its own view.


use vstd::prelude::*;

use echod_types::{PromiseRecord, Request, Response, Schedule};

use crate::target::Target;

pub use crate::concrete::{Etag, Read, StoreError, StoreReq, StoreRes};
pub use crate::verified::flight::FiredKey;

#[cfg(verus_keep_ghost)]
use echod_types::{PromiseRecordSpec, ScheduleSpec, AResponse};
#[cfg(verus_keep_ghost)]
use crate::concrete::store::{StoreErrorSpec, StoreReqSpec};
#[cfg(verus_keep_ghost)]
use crate::concrete::document::DocumentBodyV;
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;

pub use echod_types::ProductionArmed as Armed;
pub use echod_types::ProductionFired as Fired;
pub use echod_types::ProductionWriteMode as WriteMode;
pub use echod_types::ProductionCommitOutcome as CommitOutcome;
pub use echod_types::ProductionCacheResult as CacheResult;
pub use echod_types::ProductionConfigWrite as ConfigWrite;
pub use echod_types::ProductionTimerKind as TimerKind;
pub use echod_types::ProductionFireOutcome as FireOutcome;
pub use echod_types::ProductionSweepOutcome as SweepOutcome;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionMessageV as MessageSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionDebugCallV as DebugCallSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionRequestEventV as RequestEventSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionEventV as EventSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionAnswerV as AnswerSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionDebugBodyV as DebugBodySpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionEffectV as EffectSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionNoteV as NoteSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionCallV as CallSpec;

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_types_spec_error_text as spec_error_text,
    production_types_spec_unexpected as spec_unexpected,
};

verus! {
#[cfg(verus_keep_ghost)]
impl DeepView for Call {
    type V = CallSpec;
    open spec fn deep_view(&self) -> CallSpec {
        CallSpec {
            id: self.id.deep_view(),
            kind: self.kind.deep_view(),
            corr: self.corr.deep_view(),
            target: self.target.deep_view(),
            request: self.request.deep_view(),
            action_kind: self.action_kind.deep_view(),
            now: self.now.deep_view(),
            pinned: self.pinned.deep_view(),
            then: self.then.deep_view(),
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Call {
    type V = CallSpec;
    open spec fn view(&self) -> CallSpec { self.deep_view() }
}


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
#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq)]
pub enum DebugCall {
    Reset { id: RequestId, kind: String, corr: String },
    Snap { id: RequestId, kind: String, corr: String },
    Tick { id: RequestId, kind: String, corr: String, time: u64 },
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

/// A request already admitted by the impure shell.
#[derive(Debug, PartialEq, Eq)]
pub enum RequestEvent {
    Protocol(Call),
    Debug(DebugCall),
}



#[cfg(verus_keep_ghost)]
impl DeepView for RequestEvent {
    type V = RequestEventSpec;
    open spec fn deep_view(&self) -> RequestEventSpec {
        match self {
            RequestEvent::Protocol(call) => RequestEventSpec::Protocol(call.deep_view()),
            RequestEvent::Debug(call) => RequestEventSpec::Debug(call.deep_view()),
        }
    }
}

/// Which loop a physical wake was armed for. The runtime sleeps, then hands
/// this back as `Event::Wake`. The keys themselves stay in the wheel: one
/// wake can owe several of them.




/// What the core is told. Every event carries the node's clock as the
/// executor read it when the event happened; the core never reads a clock.
#[allow(inconsistent_fields)]
#[derive(Debug, PartialEq, Eq)]
pub enum Event {
    /// A protocol or debug request came in; the answer goes out as
    /// `Effect::Reply`. The runtime has already admitted and decoded it.
    Request { clock: u64, request: RequestEvent },
    /// A store call the core issued has an answer.
    Store { op: OpId, response: StoreRes, clock: u64 },
    /// The runtime slept until a loop this process armed, and that instant
    /// has come. `armed` is the loop the sleep was for. A late wake still
    /// runs the other loop when its time has come.
    Wake { clock: u64, armed: Armed },
}



#[cfg(verus_keep_ghost)]
impl DeepView for Event {
    type V = EventSpec;
    open spec fn deep_view(&self) -> EventSpec {
        match self {
            Event::Request { clock, request } => EventSpec::Request { clock: *clock, request: request.deep_view() },
            Event::Store { op, response, clock } => EventSpec::Store { op: *op, response: *response, clock: *clock },
            Event::Wake { clock, armed } => EventSpec::Wake { clock: *clock, armed: *armed },
        }
    }
}

// ---------------------------------------------------------------------------
// Out
// ---------------------------------------------------------------------------

/// What a client is told. The runtime turns it into the protocol's envelope.
#[derive(PartialEq, Eq)]
pub enum Answer {
    /// A document step.
    Step { kind: String, corr: String, action_kind: Option<String>, response: Response, why: Option<String> },
    /// A debug operation.
    Debug { kind: String, corr: String, status: u16, body: DebugBody },
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
#[derive(PartialEq, Eq)]
pub enum DebugBody {
    /// `{}`.
    Object,
    /// `[]`.
    List,
    /// A short refusal.
    Message(String),
    /// The documents a `debug.snap` read: every origin's, and every schedule.
    Snap { origins: Vec<crate::concrete::DocumentBody>, schedules: Vec<Schedule> },
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
#[derive(PartialEq, Eq)]
pub enum Effect {
    /// Answer the request handed in under `id`. `Err` is a 503: the node
    /// could not serve it.
    Reply { id: RequestId, response: Result<Answer, String> },
    /// Make this call on the store and answer with `Event::Store { op }`.
    Store { op: OpId, request: StoreReq },
    /// Send `Event::Wake` for `armed` once `after_ms` have passed, replacing
    /// any wake asked for before.
    Wake { after_ms: u64, armed: Armed },
    /// Push a message to a worker. At most once; nothing is reported back.
    Send { address: String, message: Message },
    /// Something happened that an operator, a log or a simulation may want
    /// to know. Nothing depends on it.
    Note(Note),
}



#[cfg(verus_keep_ghost)]
impl DeepView for Effect {
    type V = EffectSpec;
    open spec fn deep_view(&self) -> EffectSpec {
        match self {
            Effect::Store { op, request } => EffectSpec::Store { op: *op, request: request.deep_view() },
            Effect::Reply { id, response } => EffectSpec::Reply { id: *id, response: response.deep_view() },
            Effect::Send { address, message } => EffectSpec::Send { address: address@, message: message.deep_view() },
            Effect::Wake { after_ms, armed } => EffectSpec::Wake { after_ms: *after_ms, armed: *armed },
            Effect::Note(n) => EffectSpec::Note(n.deep_view()),
        }
    }
}

/// What became of the key that fired a sweep.




// ---------------------------------------------------------------------------
// Notes: the closed sets an operator sees
// ---------------------------------------------------------------------------

/// How a document was written.


/// How an attempt to commit a step ended.


/// What a document load cost.




/// What a timer key names.


/// What became of a key fired from the wheel.




// A label is its own view.















/// What the core reports as it goes. The counted ones carry a value from a
/// closed set, never a name a client or the bucket supplied; the observed
/// ones carry what a simulation needs to account for a step no client
/// sees; the logged ones carry what a log line wants.
pub use echod_concrete_spec::state::ProductionNoteData as Note;

/// The text a store error carries, as `Display` writes it.


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



} // verus!
