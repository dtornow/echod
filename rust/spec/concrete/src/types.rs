//! The document vocabulary: rows, the outbox, configuration, identifiers.
//!
//! Records, requests, and responses are `echod_alphabet`, re-exported below.
//!
//! Every exec type with a string or a list in it has an abstract twin,
//! `make_spec_type`'s `…Spec`, named `A…` here, reached through `View`:
//! strings become `Seq<char>`, vectors become `Seq`, numbers stay `u64`.
//! The machine and the catalogue are stated over the twins, whose equality
//! is structural, which is what a property needs. Enums view as themselves.
//!
//! serde derives are present only under plain cargo: `cfg_attr(not(
//! verus_keep_ghost), …)` keeps the generated impls out of the verifier.

use vstd::contrib::{make_spec_type, self_view};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Bounds
// ---------------------------------------------------------------------------

/// Every instant and every duration the kernel adds is at most this, so a sum
/// of two never leaves `u64`. 2^62 milliseconds is 146 million years.
pub const MAX_TIME: u64 = 0x4000_0000_0000_0000;

/// The last version a task can take: an acquire at it is refused (409), as
/// the protocol's servers refuse one at their own door. The wire carries a
/// version as a `u32`; the kernel's `u64` never exceeds it.
pub const MAX_VERSION: u64 = u32::MAX as u64;

// The records, requests, and responses live in `echod_alphabet`.
// Re-exported so the catalogue still names them as `crate::types::…`.
pub use echod_alphabet::*;


// ---------------------------------------------------------------------------
// The row: a promise and the task that executes it
// ---------------------------------------------------------------------------

#[make_spec_type]
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

#[cfg(verus_keep_ghost)]
pub type ATask = TaskSpec;

#[make_spec_type]
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

#[cfg(verus_keep_ghost)]
pub type APromise = PromiseSpec;


#[cfg(verus_keep_ghost)]
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


#[cfg(verus_keep_ghost)]
impl ATask {
    /// `TaskObject.toRecord`.
    pub open spec fn to_record(self, id: Seq<char>) -> ATaskRecord {
        ATaskRecord {
            id: id,
            state: self.state,
            version: self.version,
            resumes: if self.resumes.len() > u64::MAX { u64::MAX } else { self.resumes.len() as u64 },
            ttl: self.ttl,
            pid: self.pid,
        }
    }
}

// ---------------------------------------------------------------------------
// Messages and the outbox
// ---------------------------------------------------------------------------

// `make_spec_type` on an enum with payloads trips the field accessors Verus
// generates for every enum (they come out twice), so this one twin is by
// hand, in the macro's shape: `DeepView` to the spec enum, `View` the same.
#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub enum Message {
    Execute { task_id: String, version: u64 },
    Unblock(PromiseRecord),
}

#[cfg(verus_keep_ghost)]
pub enum MessageSpec {
    Execute { task_id: Seq<char>, version: u64 },
    Unblock(PromiseRecordSpec),
}

#[cfg(verus_keep_ghost)]
pub type AMessage = MessageSpec;

#[cfg(verus_keep_ghost)]
impl DeepView for Message {
    type V = MessageSpec;
    open spec fn deep_view(&self) -> MessageSpec {
        match self {
            Message::Execute { task_id, version } => MessageSpec::Execute { task_id: task_id.deep_view(), version: *version },
            Message::Unblock(r) => MessageSpec::Unblock(r.deep_view()),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for Message {
    type V = MessageSpec;
    open spec fn view(&self) -> MessageSpec {
        self.deep_view()
    }
}

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub struct OutboxEntry {
    pub address: String,
    pub message: Message,
}

#[cfg(verus_keep_ghost)]
pub type AOutboxEntry = OutboxEntrySpec;

/// `OutboxKey`: one `execute` per task, one `unblock` per promise and address.
pub enum OutboxKey {
    Execute(Seq<char>),
    Notify(Seq<char>, Seq<char>),
}

#[cfg(verus_keep_ghost)]
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


// Internal steps.

pub struct PromiseTimeoutReq { pub id: String }

pub struct TaskLeaseTimeoutReq { pub id: String }

pub struct TaskRetryTimeoutReq { pub id: String }

/// One due occurrence of a schedule: the instant, and the promise id the
/// schedule's template expands to at that instant (`expand`).
#[make_spec_type]
pub struct Occurrence { pub at: u64, pub promise_id: String }

#[cfg(verus_keep_ghost)]
pub type AOccurrence = OccurrenceSpec;

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
// Identifiers, and the three string primitives the kernel trusts
// ---------------------------------------------------------------------------
//
// An id is `origin:suffix`; the origin is everything before the first `:`.
// `same_origin`, `str_eq` and `parse_nat` are `external_body`: their bodies
// are ordinary Rust and their `ensures` are assumed, not proved. With
// `clone_string` they are the whole of the kernel's trusted computing base
// beyond vstd.

/// Everything before the first `:`, or the whole string if there is none.
pub open spec fn origin(s: Seq<char>) -> Seq<char>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == ':' {
        Seq::empty()
    } else {
        seq![s[0]] + origin(s.drop_first())
    }
}

pub open spec fn same_origin_spec(a: Seq<char>, b: Seq<char>) -> bool {
    origin(a) == origin(b)
}

/// Do two ids share an origin?
#[verifier::external_body]
pub fn same_origin(a: &String, b: &String) -> (r: bool)
    ensures r == same_origin_spec(a@, b@),
{
    a.split(':').next() == b.split(':').next()
}

/// `str == str`, with its meaning stated.
/// `String::clone`, with its meaning stated.
#[verifier::external_body]
pub fn clone_string(s: &String) -> (r: String)
    ensures r@ == s@,
{
    s.clone()
}

#[verifier::external_body]
pub fn str_eq(a: &str, b: &str) -> (r: bool)
    ensures r == (a@ == b@),
{
    a == b
}

/// `parseNat` of the specification, saturating at `MAX_TIME`.
pub uninterp spec fn spec_parse_nat(s: Seq<char>) -> nat;

#[verifier::external_body]
pub fn parse_nat(s: &String) -> (r: u64)
    ensures
        r as nat == spec_parse_nat(s@),
        r <= MAX_TIME,
{
    let mut acc: u64 = 0;
    for c in s.chars() {
        let d = (c as u32).wrapping_sub('0' as u32) as u64;
        acc = acc.saturating_mul(10).saturating_add(d);
        if acc > MAX_TIME {
            return MAX_TIME;
        }
    }
    acc
}

} // verus!
