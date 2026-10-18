//! The vocabulary: rows, records, requests, responses, configuration.
//!
//! Every exec type here has an abstract twin (`A…`) reached through `View`.
//! The abstract twins are what the machine and the catalogue are stated
//! over: strings become `Seq<char>`, `u64` becomes `nat`, vectors become
//! `Seq`. Equality on them is structural, which is what a property needs.
//!
//! serde derives are present only under plain cargo: `cfg_attr(not(
//! verus_keep_ghost), …)` keeps the generated impls out of the verifier.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Bounds
// ---------------------------------------------------------------------------

/// Every instant and every duration the kernel adds is at most this, so a sum
/// of two never leaves `u64`. 2^62 milliseconds is 146 million years.
pub const MAX_TIME: u64 = 0x4000_0000_0000_0000;

// ---------------------------------------------------------------------------
// Enumerations
// ---------------------------------------------------------------------------

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(not(verus_keep_ghost), serde(rename_all = "snake_case"))]
#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub enum PromiseState {
    Pending,
    Resolved,
    Rejected,
    RejectedCanceled,
    RejectedTimedout,
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(not(verus_keep_ghost), serde(rename_all = "snake_case"))]
#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub enum TaskState {
    Pending,
    Acquired,
    Suspended,
    Halted,
    Fulfilled,
}

impl PromiseState {
    /// The states a client may settle a promise to.
    pub open spec fn spec_settable(self) -> bool {
        self == PromiseState::Resolved || self == PromiseState::Rejected
            || self == PromiseState::RejectedCanceled
    }

    pub fn settable(self) -> (r: bool)
        ensures r == self.spec_settable(),
    {
        self == PromiseState::Resolved || self == PromiseState::Rejected
            || self == PromiseState::RejectedCanceled
    }
}

// ---------------------------------------------------------------------------
// Values and tags
// ---------------------------------------------------------------------------

/// Tags, as the protocol carries them: ordered pairs, first match wins.
pub type Tags = Vec<(String, String)>;
pub type ATags = Seq<(Seq<char>, Seq<char>)>;

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[derive(Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub struct Value {
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Vec::is_empty"))]
    pub headers: Tags,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub data: Option<String>,
}

pub struct AValue {
    pub headers: ATags,
    pub data: Option<Seq<char>>,
}

impl View for Value {
    type V = AValue;
    open spec fn view(&self) -> AValue {
        AValue { headers: self.headers.deep_view(), data: self.data.deep_view() }
    }
}

impl AValue {
    pub open spec fn empty() -> AValue {
        AValue { headers: Seq::empty(), data: None }
    }
    pub open spec fn is_empty(self) -> bool {
        self.data is None && self.headers.len() == 0
    }
}

impl Value {
    pub fn empty() -> (v: Value)
        ensures v@ == AValue::empty(),
    {
        let v = Value { headers: Vec::new(), data: None };
        assert(v@.headers =~= Seq::empty());
        v
    }
}

// ---------------------------------------------------------------------------
// The row: a promise and the task that executes it
// ---------------------------------------------------------------------------

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]

#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub struct Task {
    pub state: TaskState,
    pub version: u64,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub ttl: Option<u64>,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub pid: Option<String>,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub lease_timeout_at: Option<u64>,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub retry_timeout_at: Option<u64>,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Vec::is_empty"))]
    pub resumes: Vec<String>,
}

pub struct ATask {
    pub state: TaskState,
    pub version: nat,
    pub ttl: Option<nat>,
    pub pid: Option<Seq<char>>,
    pub lease_timeout_at: Option<nat>,
    pub retry_timeout_at: Option<nat>,
    pub resumes: Seq<Seq<char>>,
}

pub open spec fn opt_nat(o: Option<u64>) -> Option<nat> {
    match o {
        Some(x) => Some(x as nat),
        None => None,
    }
}

impl View for Task {
    type V = ATask;
    open spec fn view(&self) -> ATask {
        ATask {
            state: self.state,
            version: self.version as nat,
            ttl: opt_nat(self.ttl),
            pid: self.pid.deep_view(),
            lease_timeout_at: opt_nat(self.lease_timeout_at),
            retry_timeout_at: opt_nat(self.retry_timeout_at),
            resumes: self.resumes.deep_view(),
        }
    }
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]

#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub struct Promise {
    pub id: String,
    pub state: PromiseState,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Vec::is_empty"))]
    pub tags: Tags,
    #[cfg_attr(not(verus_keep_ghost), serde(default))]
    pub param: Value,
    #[cfg_attr(not(verus_keep_ghost), serde(default))]
    pub value: Value,
    pub timeout_at: u64,
    pub created_at: u64,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub settled_at: Option<u64>,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Vec::is_empty"))]
    pub callbacks: Vec<String>,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Vec::is_empty"))]
    pub listeners: Vec<String>,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub task: Option<Task>,
}

pub struct APromise {
    pub id: Seq<char>,
    pub state: PromiseState,
    pub tags: ATags,
    pub param: AValue,
    pub value: AValue,
    pub timeout_at: nat,
    pub created_at: nat,
    pub settled_at: Option<nat>,
    pub callbacks: Seq<Seq<char>>,
    pub listeners: Seq<Seq<char>>,
    pub task: Option<ATask>,
}

pub open spec fn opt_task(o: Option<Task>) -> Option<ATask> {
    match o {
        Some(t) => Some(t@),
        None => None,
    }
}

impl View for Promise {
    type V = APromise;
    open spec fn view(&self) -> APromise {
        APromise {
            id: self.id@,
            state: self.state,
            tags: self.tags.deep_view(),
            param: self.param@,
            value: self.value@,
            timeout_at: self.timeout_at as nat,
            created_at: self.created_at as nat,
            settled_at: opt_nat(self.settled_at),
            callbacks: self.callbacks.deep_view(),
            listeners: self.listeners.deep_view(),
            task: opt_task(self.task),
        }
    }
}

// ---------------------------------------------------------------------------
// Schedules
// ---------------------------------------------------------------------------

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]

#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub struct Schedule {
    pub id: String,
    pub cron: String,
    pub promise_id: String,
    pub promise_timeout: u64,
    #[cfg_attr(not(verus_keep_ghost), serde(default))]
    pub promise_param: Value,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Vec::is_empty"))]
    pub promise_tags: Tags,
    pub next_run_at: u64,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub last_run_at: Option<u64>,
    pub created_at: u64,
}

pub struct ASchedule {
    pub id: Seq<char>,
    pub cron: Seq<char>,
    pub promise_id: Seq<char>,
    pub promise_timeout: nat,
    pub promise_param: AValue,
    pub promise_tags: ATags,
    pub next_run_at: nat,
    pub last_run_at: Option<nat>,
    pub created_at: nat,
}

impl View for Schedule {
    type V = ASchedule;
    open spec fn view(&self) -> ASchedule {
        ASchedule {
            id: self.id@,
            cron: self.cron@,
            promise_id: self.promise_id@,
            promise_timeout: self.promise_timeout as nat,
            promise_param: self.promise_param@,
            promise_tags: self.promise_tags.deep_view(),
            next_run_at: self.next_run_at as nat,
            last_run_at: opt_nat(self.last_run_at),
            created_at: self.created_at as nat,
        }
    }
}

// ---------------------------------------------------------------------------
// Records: what a response carries
// ---------------------------------------------------------------------------

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]

#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub struct PromiseRecord {
    pub id: String,
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
}

pub struct APromiseRecord {
    pub id: Seq<char>,
    pub state: PromiseState,
    pub param: AValue,
    pub value: AValue,
    pub tags: ATags,
    pub timeout_at: nat,
    pub created_at: nat,
    pub settled_at: Option<nat>,
}

impl View for PromiseRecord {
    type V = APromiseRecord;
    open spec fn view(&self) -> APromiseRecord {
        APromiseRecord {
            id: self.id@,
            state: self.state,
            param: self.param@,
            value: self.value@,
            tags: self.tags.deep_view(),
            timeout_at: self.timeout_at as nat,
            created_at: self.created_at as nat,
            settled_at: opt_nat(self.settled_at),
        }
    }
}

impl APromise {
    /// `PromiseObject.toRecord`.
    pub open spec fn to_record(self) -> APromiseRecord {
        APromiseRecord {
            id: self.id,
            state: self.state,
            param: self.param,
            value: self.value,
            tags: self.tags,
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
        }
    }
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]

#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub struct TaskRecord {
    pub id: String,
    pub state: TaskState,
    pub version: u64,
    pub resumes: u64,
    pub ttl: Option<u64>,
    pub pid: Option<String>,
}

pub struct ATaskRecord {
    pub id: Seq<char>,
    pub state: TaskState,
    pub version: nat,
    pub resumes: nat,
    pub ttl: Option<nat>,
    pub pid: Option<Seq<char>>,
}

impl View for TaskRecord {
    type V = ATaskRecord;
    open spec fn view(&self) -> ATaskRecord {
        ATaskRecord {
            id: self.id@,
            state: self.state,
            version: self.version as nat,
            resumes: self.resumes as nat,
            ttl: opt_nat(self.ttl),
            pid: self.pid.deep_view(),
        }
    }
}

impl ATask {
    /// `TaskObject.toRecord`.
    pub open spec fn to_record(self, id: Seq<char>) -> ATaskRecord {
        ATaskRecord {
            id: id,
            state: self.state,
            version: self.version,
            resumes: self.resumes.len(),
            ttl: self.ttl,
            pid: self.pid,
        }
    }
}

// ---------------------------------------------------------------------------
// Messages and the outbox
// ---------------------------------------------------------------------------

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]

#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub enum Message {
    Execute { task_id: String, version: u64 },
    Unblock(PromiseRecord),
}

pub enum AMessage {
    Execute { task_id: Seq<char>, version: nat },
    Unblock(APromiseRecord),
}

impl View for Message {
    type V = AMessage;
    open spec fn view(&self) -> AMessage {
        match self {
            Message::Execute { task_id, version } => AMessage::Execute {
                task_id: task_id@,
                version: *version as nat,
            },
            Message::Unblock(r) => AMessage::Unblock(r@),
        }
    }
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]

#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub struct OutboxEntry {
    pub address: String,
    pub message: Message,
}

pub struct AOutboxEntry {
    pub address: Seq<char>,
    pub message: AMessage,
}

impl View for OutboxEntry {
    type V = AOutboxEntry;
    open spec fn view(&self) -> AOutboxEntry {
        AOutboxEntry { address: self.address@, message: self.message@ }
    }
}

/// `OutboxKey`: one `execute` per task, one `unblock` per promise and address.
pub enum OutboxKey {
    Execute(Seq<char>),
    Notify(Seq<char>, Seq<char>),
}

impl AOutboxEntry {
    pub open spec fn key(self) -> OutboxKey {
        match self.message {
            AMessage::Execute { task_id, .. } => OutboxKey::Execute(task_id),
            AMessage::Unblock(r) => OutboxKey::Notify(r.id, self.address),
        }
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// The operator's dials. Not state: no step writes it.
#[derive(Clone, Copy)]
pub struct Config {
    /// How long the server waits before re-offering a task nobody has claimed.
    pub retry_timeout: u64,
    /// Rewrite an origin's object once it carries this many stale rows.
    /// `0` rewrites on every write, which is what general-purpose S3 needs.
    pub compact: u32,
}

impl Config {
    pub open spec fn wf(self) -> bool {
        0 < self.retry_timeout <= MAX_TIME
    }
}

// ---------------------------------------------------------------------------
// Requests
// ---------------------------------------------------------------------------

pub struct PromiseGetReq { pub id: String }

pub struct PromiseCreateReq {
    pub id: String,
    pub timeout_at: u64,
    pub param: Value,
    pub tags: Tags,
}


pub struct APromiseCreateReq {
    pub id: Seq<char>,
    pub timeout_at: nat,
    pub param: AValue,
    pub tags: ATags,
}

impl View for PromiseCreateReq {
    type V = APromiseCreateReq;
    open spec fn view(&self) -> APromiseCreateReq {
        APromiseCreateReq {
            id: self.id@,
            timeout_at: self.timeout_at as nat,
            param: self.param@,
            tags: self.tags.deep_view(),
        }
    }
}

pub struct PromiseSettleReq {
    pub id: String,
    pub state: PromiseState,
    pub value: Value,
}

pub struct PromiseRegisterCallbackReq { pub awaited: String, pub awaiter: String }

pub struct PromiseRegisterListenerReq { pub awaited: String, pub address: String }

pub struct ScheduleGetReq { pub id: String }

pub struct ScheduleCreateReq {
    pub id: String,
    pub cron: String,
    pub promise_id: String,
    pub promise_timeout: u64,
    pub promise_param: Value,
    pub promise_tags: Tags,
    /// `nextCron cron now`, computed by the caller's cron engine.
    pub next_run_at: u64,
}

pub struct ScheduleDeleteReq { pub id: String }

pub struct TaskGetReq { pub id: String }

pub struct TaskCreateReq { pub pid: String, pub ttl: u64, pub action: PromiseCreateReq }

pub struct TaskAcquireReq { pub id: String, pub version: u64, pub pid: String, pub ttl: u64 }

pub enum TaskFenceAction {
    Create(PromiseCreateReq),
    Settle(PromiseSettleReq),
}

pub struct TaskFenceReq { pub id: String, pub version: u64, pub action: TaskFenceAction }

pub struct TaskRef { pub id: String, pub version: u64 }

pub struct TaskHeartbeatReq { pub pid: String, pub tasks: Vec<TaskRef> }

pub struct TaskSuspendReq {
    pub id: String,
    pub version: u64,
    pub actions: Vec<PromiseRegisterCallbackReq>,
}

pub struct TaskFulfillReq { pub id: String, pub version: u64, pub action: PromiseSettleReq }

pub struct TaskReleaseReq { pub id: String, pub version: u64 }

pub struct TaskHaltReq { pub id: String }

pub struct TaskContinueReq { pub id: String }

// Internal steps.

pub struct PromiseTimeoutReq { pub id: String }

pub struct TaskLeaseTimeoutReq { pub id: String }

pub struct TaskRetryTimeoutReq { pub id: String }

/// One due occurrence of a schedule: the instant, and the promise id the
/// schedule's template expands to at that instant (`expand`).
pub struct Occurrence { pub at: u64, pub promise_id: String }

/// A schedule's occurrences coming due. The cron arithmetic (`occurrences`,
/// `nextCron`) is the caller's: the kernel takes its results and holds them
/// to the order the machine assumes.
pub struct ScheduleTimeoutReq {
    pub schedule: String,
    pub occurrences: Vec<Occurrence>,
    /// `nextCron cron last` for the last occurrence; unused when none.
    pub next_run_at: u64,
}

// ---------------------------------------------------------------------------
// Responses
// ---------------------------------------------------------------------------

pub struct PromiseRes { pub status: u16, pub promise: Option<PromiseRecord> }

pub struct ScheduleRes { pub status: u16, pub schedule: Option<Schedule> }

pub struct StatusRes { pub status: u16 }

pub struct TaskGetRes { pub status: u16, pub task: Option<TaskRecord> }

pub struct TaskClaimRes {
    pub status: u16,
    pub task: Option<TaskRecord>,
    pub promise: Option<PromiseRecord>,
}

pub enum TaskFenceInnerRes {
    Create(PromiseRes),
    Settle(PromiseRes),
}

pub struct TaskFenceRes { pub status: u16, pub action: Option<TaskFenceInnerRes> }

} // verus!
