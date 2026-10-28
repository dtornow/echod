//! Protocol vocabulary from `01-protocol/types.lean`.
//!
//! `Text` is UTF-8 bytes. The Lean model treats strings opaquely except for
//! equality, origin equality, and five ASCII tag names, so bytes retain all
//! semantically relevant information without requiring an unverified string
//! primitive.

use vstd::contrib::{make_spec_type, self_view};
use vstd::prelude::*;

verus! {

pub const MAX_TIME: u64 = 0x3fff_ffff_ffff_ffff;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Default, PartialEq, Eq))]
pub struct Text {
    pub bytes: Vec<u8>,
}

#[cfg(verus_keep_ghost)]
pub type AText = TextSpec;

impl Text {
    pub fn empty() -> Text {
        Text { bytes: Vec::new() }
    }

    pub fn dup(&self) -> (r: Text)
        ensures r@ == self@,
    {
        let mut bytes = Vec::new();
        let mut i: usize = 0;
        while i < self.bytes.len()
            invariant
                i <= self.bytes@.len(),
                bytes@ == self.bytes@.take(i as int),
            decreases self.bytes@.len() - i,
        {
            bytes.push(self.bytes[i]);
            i += 1;
        }
        assert(self.bytes@.take(self.bytes@.len() as int) =~= self.bytes@);
        Text { bytes }
    }
}

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Default, PartialEq, Eq))]
pub struct Ident {
    pub origin: Text,
    pub suffix: Text,
}

#[cfg(verus_keep_ghost)]
pub type AIdent = IdentSpec;

impl Ident {
    pub fn dup(&self) -> (r: Ident)
        ensures r@ == self@,
    {
        Ident { origin: self.origin.dup(), suffix: self.suffix.dup() }
    }

    pub fn same_origin(&self, other: &Ident) -> bool {
        self.origin.bytes == other.origin.bytes
    }
}

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Tag {
    pub key: Text,
    pub value: Text,
}

#[cfg(verus_keep_ghost)]
pub type ATag = TagSpec;

pub type Tags = Vec<Tag>;
#[cfg(verus_keep_ghost)]
pub type ATags = Seq<ATag>;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Default, PartialEq, Eq))]
pub struct Value {
    pub headers: Tags,
    pub data: Option<Text>,
}

#[cfg(verus_keep_ghost)]
pub type AValue = ValueSpec;

impl Value {
    pub fn empty() -> Value {
        Value { headers: Vec::new(), data: None }
    }

    pub fn dup(&self) -> Value {
        Value {
            headers: dup_tags(&self.headers),
            data: match &self.data { Some(x) => Some(x.dup()), None => None },
        }
    }
}

#[self_view]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum PromiseState {
    Pending,
    Resolved,
    Rejected,
    RejectedCanceled,
    RejectedTimedout,
}

impl PromiseState {
    pub fn settable(self) -> bool {
        self == PromiseState::Resolved
            || self == PromiseState::Rejected
            || self == PromiseState::RejectedCanceled
    }
}

#[self_view]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum TaskState {
    Pending,
    Acquired,
    Suspended,
    Halted,
    Fulfilled,
}

#[self_view]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum OType {
    Internal,
    External,
    Runnable,
}

impl OType {
    pub fn awaitable(self) -> bool {
        self != OType::Internal
    }
}

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct PromiseRecord {
    pub id: Ident,
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
}

#[cfg(verus_keep_ghost)]
pub type APromiseRecord = PromiseRecordSpec;

impl PromiseRecord {
    pub fn dup(&self) -> PromiseRecord {
        PromiseRecord {
            id: self.id.dup(), state: self.state, param: self.param.dup(),
            value: self.value.dup(), tags: dup_tags(&self.tags),
            timeout_at: self.timeout_at, created_at: self.created_at,
            settled_at: self.settled_at,
        }
    }
}

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct TaskRecord {
    pub id: Ident,
    pub state: TaskState,
    pub version: u64,
    pub resumes: u64,
    pub ttl: Option<u64>,
    pub pid: Option<Text>,
}

#[cfg(verus_keep_ghost)]
pub type ATaskRecord = TaskRecordSpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Schedule {
    pub id: Ident,
    pub cron: Text,
    pub promise_id: Ident,
    pub promise_timeout: u64,
    pub promise_param: Value,
    pub promise_tags: Tags,
    pub next_run_at: u64,
    pub last_run_at: Option<u64>,
    pub created_at: u64,
}

#[cfg(verus_keep_ghost)]
pub type ASchedule = ScheduleSpec;

impl Schedule {
    pub fn dup(&self) -> Schedule {
        Schedule {
            id: self.id.dup(), cron: self.cron.dup(),
            promise_id: self.promise_id.dup(),
            promise_timeout: self.promise_timeout,
            promise_param: self.promise_param.dup(),
            promise_tags: dup_tags(&self.promise_tags),
            next_run_at: self.next_run_at, last_run_at: self.last_run_at,
            created_at: self.created_at,
        }
    }
}

// Requests -----------------------------------------------------------------

#[make_spec_type] pub struct PromiseGetReq { pub id: Ident }
#[make_spec_type] pub struct PromiseCreateReq {
    pub id: Ident, pub timeout_at: u64, pub param: Value, pub tags: Tags,
}
#[make_spec_type] pub struct PromiseSettleReq {
    pub id: Ident, pub state: PromiseState, pub value: Value,
}
#[make_spec_type] pub struct PromiseRegisterCallbackReq {
    pub awaited: Ident, pub awaiter: Ident,
}
#[make_spec_type] pub struct PromiseRegisterListenerReq {
    pub awaited: Ident, pub address: Text,
}
#[make_spec_type] pub struct PromiseSearchReq {
    pub state: Option<PromiseState>, pub tags: Tags,
    pub limit: Option<u64>, pub cursor: Option<Text>,
}
#[make_spec_type] pub struct ScheduleGetReq { pub id: Ident }
#[make_spec_type] pub struct ScheduleCreateReq {
    pub id: Ident, pub cron: Text, pub promise_id: Ident,
    pub promise_timeout: u64, pub promise_param: Value, pub promise_tags: Tags,
    /// Executable witness for Lean's opaque `nextCron cron now`.
    pub next_run_at: u64,
}
#[make_spec_type] pub struct ScheduleDeleteReq { pub id: Ident }
#[make_spec_type] pub struct ScheduleSearchReq {
    pub limit: Option<u64>, pub cursor: Option<Text>,
}
#[make_spec_type] pub struct TaskGetReq { pub id: Ident }
#[make_spec_type] pub struct TaskCreateReq {
    pub pid: Text, pub ttl: u64, pub action: PromiseCreateReq,
}
#[make_spec_type] pub struct TaskAcquireReq {
    pub id: Ident, pub version: u64, pub pid: Text, pub ttl: u64,
}

pub enum TaskFenceAction {
    Create(PromiseCreateReq),
    Settle(PromiseSettleReq),
}

pub struct TaskFenceReq {
    pub id: Ident,
    pub version: u64,
    pub action: TaskFenceAction,
}

#[make_spec_type] pub struct TaskRef { pub id: Ident, pub version: u64 }
#[make_spec_type] pub struct TaskHeartbeatReq { pub pid: Text, pub tasks: Vec<TaskRef> }
#[make_spec_type] pub struct TaskSuspendReq {
    pub id: Ident, pub version: u64, pub actions: Vec<PromiseRegisterCallbackReq>,
}
#[make_spec_type] pub struct TaskFulfillReq {
    pub id: Ident, pub version: u64, pub action: PromiseSettleReq,
}
#[make_spec_type] pub struct TaskReleaseReq { pub id: Ident, pub version: u64 }
#[make_spec_type] pub struct TaskHaltReq { pub id: Ident }
#[make_spec_type] pub struct TaskContinueReq { pub id: Ident }
#[make_spec_type] pub struct TaskSearchReq {
    pub state: Option<TaskState>, pub limit: Option<u64>, pub cursor: Option<Text>,
}

#[make_spec_type] pub struct PromiseTimeoutReq { pub id: Ident }
#[make_spec_type] pub struct TaskLeaseTimeoutReq { pub id: Ident }
#[make_spec_type] pub struct TaskRetryTimeoutReq { pub id: Ident }

#[make_spec_type]
pub struct Occurrence {
    pub at: u64,
    /// Executable witness for Lean's opaque `expand template schedule at`.
    pub promise_id: Ident,
}

pub struct ScheduleTimeoutReq {
    pub schedule: Ident,
    /// Executable witness for Lean's opaque `occurrences`, in Lean list order.
    pub occurrences: Vec<Occurrence>,
    /// `nextCron cron last`, used only when `occurrences` is nonempty.
    pub next_run_at: u64,
}

#[make_spec_type]
pub struct ResumeReq {
    pub awaited: Text,
    pub awaiter: Text,
}

#[self_view]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum ResumeOutcome {
    Resumed,
    Buffered,
    Duplicate,
    Expired,
    Fulfilled,
    Absent,
}

#[make_spec_type]
pub struct ResumeRes {
    pub outcome: ResumeOutcome,
}

// Responses ----------------------------------------------------------------

#[make_spec_type]
pub struct PromiseRes { pub status: u16, pub promise: Option<PromiseRecord> }
pub type PromiseGetRes = PromiseRes;
pub type PromiseCreateRes = PromiseRes;
pub type PromiseSettleRes = PromiseRes;
pub type PromiseRegisterCallbackRes = PromiseRes;
pub type PromiseRegisterListenerRes = PromiseRes;

#[make_spec_type]
pub struct PromiseSearchRes {
    pub status: u16, pub promises: Vec<PromiseRecord>, pub cursor: Option<Text>,
}

#[make_spec_type]
pub struct ScheduleRes { pub status: u16, pub schedule: Option<Schedule> }
pub type ScheduleGetRes = ScheduleRes;
pub type ScheduleCreateRes = ScheduleRes;

#[make_spec_type]
pub struct ScheduleDeleteRes { pub status: u16 }

#[make_spec_type]
pub struct ScheduleSearchRes {
    pub status: u16, pub schedules: Vec<Schedule>, pub cursor: Option<Text>,
}

#[make_spec_type]
pub struct TaskGetRes { pub status: u16, pub task: Option<TaskRecord> }

#[make_spec_type]
pub struct TaskClaimRes {
    pub status: u16, pub task: Option<TaskRecord>,
    pub promise: Option<PromiseRecord>, pub preload: Vec<PromiseRecord>,
}
pub type TaskCreateRes = TaskClaimRes;
pub type TaskAcquireRes = TaskClaimRes;

pub enum TaskFenceInnerRes {
    Create(PromiseCreateRes),
    Settle(PromiseSettleRes),
}
pub struct TaskFenceRes {
    pub status: u16,
    pub action: Option<TaskFenceInnerRes>,
    pub preload: Vec<PromiseRecord>,
}

#[make_spec_type]
pub struct StatusRes { pub status: u16 }
pub type TaskHeartbeatRes = StatusRes;
pub type TaskReleaseRes = StatusRes;
pub type TaskHaltRes = StatusRes;
pub type TaskContinueRes = StatusRes;

#[make_spec_type]
pub struct TaskSuspendRes {
    pub status: u16, pub preload: Vec<PromiseRecord>,
}

#[make_spec_type]
pub struct TaskFulfillRes { pub status: u16, pub promise: Option<PromiseRecord> }

#[make_spec_type]
pub struct TaskSearchRes {
    pub status: u16, pub tasks: Vec<TaskRecord>, pub cursor: Option<Text>,
}

// Ordered-list helpers ------------------------------------------------------

pub fn dup_tags(tags: &Tags) -> Tags {
    let mut out = Vec::new();
    let mut i: usize = 0;
    while i < tags.len()
        decreases tags@.len() - i,
    {
        out.push(Tag { key: tags[i].key.dup(), value: tags[i].value.dup() });
        i += 1;
    }
    out
}

pub fn ident_eq(a: &Ident, b: &Ident) -> bool {
    a.origin.bytes == b.origin.bytes && a.suffix.bytes == b.suffix.bytes
}

pub fn text_eq(a: &Text, b: &Text) -> bool {
    a.bytes == b.bytes
}

fn ascii_true(x: &Text) -> bool {
    x.bytes.len() == 4 && x.bytes[0] == 116 && x.bytes[1] == 114
        && x.bytes[2] == 117 && x.bytes[3] == 101
}

fn ascii_global(x: &Text) -> bool {
    x.bytes.len() == 6 && x.bytes[0] == 103 && x.bytes[1] == 108
        && x.bytes[2] == 111 && x.bytes[3] == 98 && x.bytes[4] == 97
        && x.bytes[5] == 108
}

fn key_prefix(x: &Text) -> bool {
    x.bytes.len() >= 9 && x.bytes[0] == 114 && x.bytes[1] == 101
        && x.bytes[2] == 115 && x.bytes[3] == 111 && x.bytes[4] == 110
        && x.bytes[5] == 97 && x.bytes[6] == 116 && x.bytes[7] == 101
        && x.bytes[8] == 58
}

fn key_target(x: &Text) -> bool {
    key_prefix(x) && x.bytes.len() == 15 && x.bytes[9] == 116
        && x.bytes[10] == 97 && x.bytes[11] == 114 && x.bytes[12] == 103
        && x.bytes[13] == 101 && x.bytes[14] == 116
}

fn key_scope(x: &Text) -> bool {
    key_prefix(x) && x.bytes.len() == 14 && x.bytes[9] == 115
        && x.bytes[10] == 99 && x.bytes[11] == 111 && x.bytes[12] == 112
        && x.bytes[13] == 101
}

fn key_external(x: &Text) -> bool {
    key_prefix(x) && x.bytes.len() == 17 && x.bytes[9] == 101
        && x.bytes[10] == 120 && x.bytes[11] == 116 && x.bytes[12] == 101
        && x.bytes[13] == 114 && x.bytes[14] == 110 && x.bytes[15] == 97
        && x.bytes[16] == 108
}

fn key_timer(x: &Text) -> bool {
    key_prefix(x) && x.bytes.len() == 14 && x.bytes[9] == 116
        && x.bytes[10] == 105 && x.bytes[11] == 109 && x.bytes[12] == 101
        && x.bytes[13] == 114
}

fn key_delay(x: &Text) -> bool {
    key_prefix(x) && x.bytes.len() == 14 && x.bytes[9] == 100
        && x.bytes[10] == 101 && x.bytes[11] == 108 && x.bytes[12] == 97
        && x.bytes[13] == 121
}

/// First matching tag, exactly Lean's `List.find?`.
pub fn tag_value(tags: &Tags, which: u8) -> Option<Text> {
    let mut i: usize = 0;
    while i < tags.len()
        decreases tags@.len() - i,
    {
        let yes = match which {
            0 => key_target(&tags[i].key),
            1 => key_scope(&tags[i].key),
            2 => key_external(&tags[i].key),
            3 => key_timer(&tags[i].key),
            _ => key_delay(&tags[i].key),
        };
        if yes {
            return Some(tags[i].value.dup());
        }
        i += 1;
    }
    None
}

pub fn tags_is_timer(tags: &Tags) -> bool {
    match tag_value(tags, 3) { Some(v) => ascii_true(&v), None => false }
}

pub fn tags_has_target(tags: &Tags) -> bool {
    match tag_value(tags, 0) { Some(_) => true, None => false }
}

pub fn tags_timer_targeted(tags: &Tags) -> bool {
    tags_is_timer(tags) && tags_has_target(tags)
}

pub fn tags_otype(tags: &Tags) -> OType {
    if tags_has_target(tags) {
        OType::Runnable
    } else {
        let global = match tag_value(tags, 1) { Some(v) => ascii_global(&v), None => false };
        let external = match tag_value(tags, 2) { Some(v) => ascii_true(&v), None => false };
        if global || external || tags_is_timer(tags) { OType::External } else { OType::Internal }
    }
}

/// Lean's decimal fold on the executable `u64` domain. Overflow saturates;
/// callers cap all instants at `MAX_TIME`, so this is exact inside that door.
pub fn parse_nat_bounded(x: &Text) -> u64 {
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < x.bytes.len()
        decreases x.bytes@.len() - i,
    {
        let b = x.bytes[i];
        let d = if b >= 48 { (b - 48) as u64 } else { 0 };
        if acc > MAX_TIME / 10 {
            return MAX_TIME;
        }
        acc = acc * 10;
        if d > MAX_TIME - acc {
            return MAX_TIME;
        }
        acc = acc + d;
        i += 1;
    }
    acc
}

} // verus!
