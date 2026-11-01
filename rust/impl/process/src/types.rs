//! The vocabulary the core is written in: what it is told, what it answers
//! with, and the shapes those two carry.
//!
//! Everything here is data. `Event` is the only way in, `Effect` the only
//! way out. A store call goes out as an `Effect::Store` under an `OpId`
//! and its answer comes back as `Event::Completed` under the same id; the
//! core keeps, per id, which machine is waiting for it. No decision is made
//! in this file: that is `State` in the crate root and the machines beside
//! it.

use std::fmt;

use echod_kernel::node::Key;
use resonate_core::types::{Message, RequestEnvelope, ResponseEnvelope};
use resonate_core::Unavailable;

/// Names a store call the executor was asked to make.
pub type OpId = u64;
/// Names a request the executor handed in and wants an answer to.
pub type RequestId = u64;
/// Names one step on one document, from its start to its answer.
pub type FlightId = u64;

/// A version of an object in the store, as the store names it.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Etag(pub String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StoreError {
    /// A conditional write found the object at another version.
    PreconditionFailed,
    /// The store did not answer, or answered with an error: the effect of
    /// a write is unknown.
    Unavailable(String),
}

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StoreError::PreconditionFailed => f.write_str("precondition failed"),
            StoreError::Unavailable(m) => write!(f, "store unavailable: {m}"),
        }
    }
}

impl std::error::Error for StoreError {}

/// What a conditional read answered.
#[derive(Debug, Clone)]
pub enum Read {
    Body(Vec<u8>, Etag),
    NotModified,
    Absent,
}

// ---------------------------------------------------------------------------
// In
// ---------------------------------------------------------------------------

/// What the core is told. Every event carries the node's clock as the
/// executor read it when the event happened; the core never reads a clock.
pub enum Event {
    /// The node starts. `loops` says whether it keeps itself going: the
    /// heartbeat and the timers. Without them it answers requests and does
    /// nothing on its own.
    Start { clock: u64, loops: bool },
    /// A request came in; the answer goes out as `Effect::Reply` under `id`.
    Request { id: RequestId, envelope: RequestEnvelope, clock: u64 },
    /// A store call the core issued has an answer.
    Completed { op: OpId, outcome: StoreOutcome, clock: u64 },
    /// Time passed: the wake the core asked for, or any other moment the
    /// executor chooses to let the core look at the clock.
    Tick { clock: u64 },
    /// The node stops: it withdraws its announcement and runs no loop.
    Stop { clock: u64 },
}

/// A call on the store, as the executor makes it.
#[derive(Debug, Clone)]
pub enum StoreCall {
    Get { key: String },
    GetIfNoneMatch { key: String, etag: Etag },
    PutIfMatch { key: String, body: Vec<u8>, etag: Etag },
    PutIfNoneMatch { key: String, body: Vec<u8> },
    AppendIfMatch { key: String, offset: u64, body: Vec<u8>, etag: Etag },
    Put { key: String, body: Vec<u8> },
    Delete { key: String },
    List { prefix: String, max_keys: usize },
    ListPrefixes { prefix: String },
}

impl StoreCall {
    pub fn key(&self) -> &str {
        match self {
            StoreCall::Get { key }
            | StoreCall::GetIfNoneMatch { key, .. }
            | StoreCall::PutIfMatch { key, .. }
            | StoreCall::PutIfNoneMatch { key, .. }
            | StoreCall::AppendIfMatch { key, .. }
            | StoreCall::Put { key, .. }
            | StoreCall::Delete { key } => key,
            StoreCall::List { prefix, .. } | StoreCall::ListPrefixes { prefix } => prefix,
        }
    }
}

/// What a store call answered.
#[derive(Debug, Clone)]
pub enum StoreOutcome {
    /// `Get`: the object and its version, or nothing.
    Got(Option<(Vec<u8>, Etag)>),
    /// `GetIfNoneMatch`.
    Read(Read),
    /// A conditional write landed at this version.
    Written(Etag),
    /// `Put` or `Delete` landed.
    Done,
    /// `List` or `ListPrefixes`.
    Listed(Vec<String>),
    Failed(StoreError),
}

// ---------------------------------------------------------------------------
// Out
// ---------------------------------------------------------------------------

/// What the core asks the executor to do.
pub enum Effect {
    /// Make this call on the store and answer with `Event::Completed { op }`.
    Store { op: OpId, call: StoreCall },
    /// Answer the request handed in under `id`. `Err` is a 503: the node
    /// could not serve it.
    Reply { id: RequestId, response: Result<ResponseEnvelope, Unavailable> },
    /// Push a message to a worker. At most once; nothing is reported back.
    Send { address: String, message: Message },
    /// Send `Event::Tick` once `after_ms` have passed, replacing any wake
    /// asked for before.
    Wake { after_ms: u64 },
    /// Something happened that an operator, a log or a simulation may want
    /// to know. Nothing depends on it.
    Note(Note),
}

/// What became of the key that fired a sweep.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fired {
    /// Deleted from the bucket.
    Deleted,
    /// Still in the bucket: the delete failed. It fires again.
    Kept,
}

/// The key that fired a sweep, and the node that armed it.
#[derive(Debug, Clone)]
pub struct FiredKey {
    pub key: Key,
    pub by: String,
}

// ---------------------------------------------------------------------------
// Notes: the closed sets an operator sees
// ---------------------------------------------------------------------------

/// An enum whose variants are a label's values, written in lower case.
macro_rules! label {
    ($(#[$m:meta])* $name:ident { $($variant:ident => $text:literal),+ $(,)? }) => {
        $(#[$m])*
        #[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
        pub enum $name { $($variant),+ }

        impl $name {
            pub fn as_str(self) -> &'static str {
                match self { $(Self::$variant => $text),+ }
            }
        }
    };
}

label! {
    /// How a document was written.
    WriteMode { Create => "create", Rewrite => "rewrite", Append => "append" }
}

label! {
    /// How an attempt to commit a step ended.
    CommitOutcome { Committed => "committed", Raced => "raced", Failed => "failed", Exhausted => "exhausted" }
}

label! {
    /// What a document load cost.
    CacheResult { Revalidated => "revalidated", Refreshed => "refreshed", Absent => "absent", Miss => "miss" }
}

label! {
    ConfigWrite { Written => "written", Conflict => "conflict", Failed => "failed" }
}

label! {
    /// What a timer key names.
    TimerKind { Origin => "origin", Schedule => "schedule" }
}

label! {
    /// What became of a key fired from the wheel.
    FireOutcome { Deleted => "deleted", Kept => "kept", Failed => "failed", Deferred => "deferred" }
}

label! {
    SweepOutcome { Fired => "fired", Idle => "idle", Failed => "failed" }
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
    FireBegin { flight: FlightId, origin: String, now: u64, row: Box<echod_kernel::Schedule>, at: u64, promise_id: String, next: u64 },
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
