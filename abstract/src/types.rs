//! Protocol vocabulary from `01-protocol/types.lean`.
//!
//! `Text` is a vector of Unicode scalar values. This matches the kernel's
//! `Seq<char>` view directly; encoding belongs to the wire boundary.

use vstd::contrib::{make_spec_type, self_view};
use vstd::prelude::*;
use vstd::string::StrSliceExecFns;

verus! {

pub const MAX_TIME: u64 = 0x4000_0000_0000_0000;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Default, PartialEq, Eq))]
pub struct Text {
    pub chars: Vec<char>,
}

#[cfg(verus_keep_ghost)]
pub type AText = TextSpec;

impl Text {
    pub fn empty() -> (r: Text)
        ensures r@ == (AText { chars: Seq::empty() }),
    {
        let r = Text { chars: Vec::new() };
        assert(r@.chars =~= Seq::<char>::empty());
        assert(r@ == (AText { chars: Seq::empty() }));
        r
    }

    pub fn dup(&self) -> (r: Text)
        ensures r@ == self@,
    {
        let mut chars = Vec::new();
        let mut i: usize = 0;
        while i < self.chars.len()
            invariant
                i <= self.chars@.len(),
                chars@ == self.chars@.take(i as int),
            decreases self.chars@.len() - i,
        {
            chars.push(self.chars[i]);
            i += 1;
        }
        assert(self.chars@.take(self.chars@.len() as int) =~= self.chars@);
        Text { chars }
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

    pub fn same_origin(&self, other: &Ident) -> (r: bool)
        ensures r == (self@.origin == other@.origin),
    {
        text_eq(&self.origin, &other.origin)
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
    pub fn empty() -> (r: Value)
        ensures r@ == (AValue {
            headers: Seq::empty(),
            data: None,
        }),
    {
        let r = Value { headers: Vec::new(), data: None };
        assert(r@.headers =~= Seq::<ATag>::empty());
        assert(r@.data is None);
        assert(r@ == (AValue { headers: Seq::empty(), data: None }));
        r
    }

    pub fn dup(&self) -> (r: Value)
        ensures r@ == self@,
    {
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
    pub fn settable(self) -> (r: bool)
        ensures
            r == (self == PromiseState::Resolved
                || self == PromiseState::Rejected
                || self == PromiseState::RejectedCanceled),
    {
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
    pub fn awaitable(self) -> (r: bool)
        ensures r == (self != OType::Internal),
    {
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
    pub fn dup(&self) -> (r: PromiseRecord)
        ensures r@ == self@,
    {
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
    pub fn dup(&self) -> (r: Schedule)
        ensures r@ == self@,
    {
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
#[cfg(verus_keep_ghost)]
pub type APromiseGetReq = PromiseGetReqSpec;
#[make_spec_type] pub struct PromiseCreateReq {
    pub id: Ident, pub timeout_at: u64, pub param: Value, pub tags: Tags,
}
#[cfg(verus_keep_ghost)]
pub type APromiseCreateReq = PromiseCreateReqSpec;
#[make_spec_type] pub struct PromiseSettleReq {
    pub id: Ident, pub state: PromiseState, pub value: Value,
}
#[cfg(verus_keep_ghost)]
pub type APromiseSettleReq = PromiseSettleReqSpec;
#[make_spec_type] pub struct PromiseRegisterCallbackReq {
    pub awaited: Ident, pub awaiter: Ident,
}
#[make_spec_type] pub struct PromiseRegisterListenerReq {
    pub awaited: Ident, pub address: Text,
}
#[cfg(verus_keep_ghost)]
pub type APromiseRegisterCallbackReq = PromiseRegisterCallbackReqSpec;
#[cfg(verus_keep_ghost)]
pub type APromiseRegisterListenerReq = PromiseRegisterListenerReqSpec;
#[make_spec_type] pub struct PromiseSearchReq {
    pub state: Option<PromiseState>, pub tags: Tags,
    pub limit: Option<u64>, pub cursor: Option<Text>,
}
#[cfg(verus_keep_ghost)]
pub type APromiseSearchReq = PromiseSearchReqSpec;
#[make_spec_type] pub struct ScheduleGetReq { pub id: Ident }
#[cfg(verus_keep_ghost)]
pub type AScheduleGetReq = ScheduleGetReqSpec;
#[make_spec_type] pub struct ScheduleCreateReq {
    pub id: Ident, pub cron: Text, pub promise_id: Ident,
    pub promise_timeout: u64, pub promise_param: Value, pub promise_tags: Tags,
    /// Executable witness for Lean's opaque `nextCron cron now`.
    pub next_run_at: u64,
}
#[cfg(verus_keep_ghost)]
pub type AScheduleCreateReq = ScheduleCreateReqSpec;
#[make_spec_type] pub struct ScheduleDeleteReq { pub id: Ident }
#[cfg(verus_keep_ghost)]
pub type AScheduleDeleteReq = ScheduleDeleteReqSpec;
#[make_spec_type] pub struct ScheduleSearchReq {
    pub limit: Option<u64>, pub cursor: Option<Text>,
}
#[cfg(verus_keep_ghost)]
pub type AScheduleSearchReq = ScheduleSearchReqSpec;
#[make_spec_type] pub struct TaskGetReq { pub id: Ident }
#[cfg(verus_keep_ghost)]
pub type ATaskGetReq = TaskGetReqSpec;
#[make_spec_type] pub struct TaskCreateReq {
    pub pid: Text, pub ttl: u64, pub action: PromiseCreateReq,
}
#[cfg(verus_keep_ghost)]
pub type ATaskCreateReq = TaskCreateReqSpec;
#[make_spec_type] pub struct TaskAcquireReq {
    pub id: Ident, pub version: u64, pub pid: Text, pub ttl: u64,
}
#[cfg(verus_keep_ghost)]
pub type ATaskAcquireReq = TaskAcquireReqSpec;

pub enum TaskFenceAction {
    Create(PromiseCreateReq),
    Settle(PromiseSettleReq),
}

#[cfg(verus_keep_ghost)]
pub enum ATaskFenceAction {
    Create(APromiseCreateReq),
    Settle(APromiseSettleReq),
}

#[cfg(verus_keep_ghost)]
impl DeepView for TaskFenceAction {
    type V = ATaskFenceAction;

    open spec fn deep_view(&self) -> ATaskFenceAction {
        match self {
            TaskFenceAction::Create(req) => ATaskFenceAction::Create(req.deep_view()),
            TaskFenceAction::Settle(req) => ATaskFenceAction::Settle(req.deep_view()),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for TaskFenceAction {
    type V = ATaskFenceAction;
    open spec fn view(&self) -> ATaskFenceAction { self.deep_view() }
}

pub struct TaskFenceReq {
    pub id: Ident,
    pub version: u64,
    pub action: TaskFenceAction,
}

#[cfg(verus_keep_ghost)]
pub struct ATaskFenceReq {
    pub id: AIdent,
    pub version: u64,
    pub action: ATaskFenceAction,
}

#[cfg(verus_keep_ghost)]
impl DeepView for TaskFenceReq {
    type V = ATaskFenceReq;

    open spec fn deep_view(&self) -> ATaskFenceReq {
        ATaskFenceReq {
            id: self.id.deep_view(),
            version: self.version,
            action: self.action.deep_view(),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for TaskFenceReq {
    type V = ATaskFenceReq;
    open spec fn view(&self) -> ATaskFenceReq { self.deep_view() }
}

#[make_spec_type] pub struct TaskRef { pub id: Ident, pub version: u64 }
#[cfg(verus_keep_ghost)]
pub type ATaskRef = TaskRefSpec;
#[make_spec_type] pub struct TaskHeartbeatReq { pub pid: Text, pub tasks: Vec<TaskRef> }
#[cfg(verus_keep_ghost)]
pub type ATaskHeartbeatReq = TaskHeartbeatReqSpec;
#[make_spec_type] pub struct TaskSuspendReq {
    pub id: Ident, pub version: u64, pub actions: Vec<PromiseRegisterCallbackReq>,
}
#[cfg(verus_keep_ghost)]
pub type ATaskSuspendReq = TaskSuspendReqSpec;
#[make_spec_type] pub struct TaskFulfillReq {
    pub id: Ident, pub version: u64, pub action: PromiseSettleReq,
}
#[cfg(verus_keep_ghost)]
pub type ATaskFulfillReq = TaskFulfillReqSpec;
#[make_spec_type] pub struct TaskReleaseReq { pub id: Ident, pub version: u64 }
#[cfg(verus_keep_ghost)]
pub type ATaskReleaseReq = TaskReleaseReqSpec;
#[make_spec_type] pub struct TaskHaltReq { pub id: Ident }
#[cfg(verus_keep_ghost)]
pub type ATaskHaltReq = TaskHaltReqSpec;
#[make_spec_type] pub struct TaskContinueReq { pub id: Ident }
#[cfg(verus_keep_ghost)]
pub type ATaskContinueReq = TaskContinueReqSpec;
#[make_spec_type] pub struct TaskSearchReq {
    pub state: Option<TaskState>, pub limit: Option<u64>, pub cursor: Option<Text>,
}
#[cfg(verus_keep_ghost)]
pub type ATaskSearchReq = TaskSearchReqSpec;

#[make_spec_type] pub struct PromiseTimeoutReq { pub id: Ident }
#[make_spec_type] pub struct TaskLeaseTimeoutReq { pub id: Ident }
#[make_spec_type] pub struct TaskRetryTimeoutReq { pub id: Ident }

#[cfg(verus_keep_ghost)]
pub type APromiseTimeoutReq = PromiseTimeoutReqSpec;
#[cfg(verus_keep_ghost)]
pub type ATaskLeaseTimeoutReq = TaskLeaseTimeoutReqSpec;
#[cfg(verus_keep_ghost)]
pub type ATaskRetryTimeoutReq = TaskRetryTimeoutReqSpec;

/// `task.fence` with no action: the check alone. A fence whose create targets
/// another origin is two protocol steps, this one first and then the create,
/// so a fence that does not hold creates nothing, and one that lapses after
/// its check still creates.
#[make_spec_type] pub struct TaskFenceCheckReq { pub id: Ident, pub version: u64 }
#[cfg(verus_keep_ghost)]
pub type ATaskFenceCheckReq = TaskFenceCheckReqSpec;

#[make_spec_type]
pub struct Occurrence {
    pub at: u64,
    /// Executable witness for Lean's opaque `expand template schedule at`.
    pub promise_id: Ident,
}

/// A schedule fires one occurrence: its promise is created if absent. The
/// schedule itself is not touched; that is `ScheduleAdvanceReq`, a later step.
#[make_spec_type]
pub struct ScheduleFireReq {
    pub schedule: Ident,
    pub occurrence: Occurrence,
}

/// A schedule advances past an occurrence whose promise exists: `last_run_at`
/// becomes the occurrence, `next_run_at` the supplied `nextCron` witness.
#[make_spec_type]
pub struct ScheduleAdvanceReq {
    pub schedule: Ident,
    pub occurrence: Occurrence,
    /// `nextCron cron occurrence.at`, strictly after the occurrence.
    pub next_run_at: u64,
}

#[cfg(verus_keep_ghost)]
pub type AOccurrence = OccurrenceSpec;
#[cfg(verus_keep_ghost)]
pub type AScheduleFireReq = ScheduleFireReqSpec;
#[cfg(verus_keep_ghost)]
pub type AScheduleAdvanceReq = ScheduleAdvanceReqSpec;

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
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct PromiseRes { pub status: u16, pub promise: Option<PromiseRecord> }
#[cfg(verus_keep_ghost)]
pub type APromiseRes = PromiseResSpec;
pub type PromiseGetRes = PromiseRes;
pub type PromiseCreateRes = PromiseRes;
pub type PromiseSettleRes = PromiseRes;
pub type PromiseRegisterCallbackRes = PromiseRes;
pub type PromiseRegisterListenerRes = PromiseRes;

#[make_spec_type]
pub struct PromiseSearchRes {
    pub status: u16, pub promises: Vec<PromiseRecord>, pub cursor: Option<Text>,
}
#[cfg(verus_keep_ghost)]
pub type APromiseSearchRes = PromiseSearchResSpec;

#[make_spec_type]
pub struct ScheduleRes { pub status: u16, pub schedule: Option<Schedule> }
#[cfg(verus_keep_ghost)]
pub type AScheduleRes = ScheduleResSpec;
pub type ScheduleGetRes = ScheduleRes;
pub type ScheduleCreateRes = ScheduleRes;

#[make_spec_type]
pub struct ScheduleDeleteRes { pub status: u16 }
#[cfg(verus_keep_ghost)]
pub type AScheduleDeleteRes = ScheduleDeleteResSpec;

#[make_spec_type]
pub struct ScheduleSearchRes {
    pub status: u16, pub schedules: Vec<Schedule>, pub cursor: Option<Text>,
}
#[cfg(verus_keep_ghost)]
pub type AScheduleSearchRes = ScheduleSearchResSpec;

#[make_spec_type]
pub struct TaskGetRes { pub status: u16, pub task: Option<TaskRecord> }
#[cfg(verus_keep_ghost)]
pub type ATaskGetRes = TaskGetResSpec;

#[make_spec_type]
pub struct TaskClaimRes {
    pub status: u16, pub task: Option<TaskRecord>,
    pub promise: Option<PromiseRecord>, pub preload: Vec<PromiseRecord>,
}
#[cfg(verus_keep_ghost)]
pub type ATaskClaimRes = TaskClaimResSpec;
pub type TaskCreateRes = TaskClaimRes;
pub type TaskAcquireRes = TaskClaimRes;

pub enum TaskFenceInnerRes {
    Create(PromiseCreateRes),
    Settle(PromiseSettleRes),
}

#[cfg(verus_keep_ghost)]
pub enum ATaskFenceInnerRes {
    Create(APromiseRes),
    Settle(APromiseRes),
}

#[cfg(verus_keep_ghost)]
impl DeepView for TaskFenceInnerRes {
    type V = ATaskFenceInnerRes;

    open spec fn deep_view(&self) -> ATaskFenceInnerRes {
        match self {
            TaskFenceInnerRes::Create(res) => ATaskFenceInnerRes::Create(res.deep_view()),
            TaskFenceInnerRes::Settle(res) => ATaskFenceInnerRes::Settle(res.deep_view()),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for TaskFenceInnerRes {
    type V = ATaskFenceInnerRes;
    open spec fn view(&self) -> ATaskFenceInnerRes { self.deep_view() }
}

pub struct TaskFenceRes {
    pub status: u16,
    pub action: Option<TaskFenceInnerRes>,
    pub preload: Vec<PromiseRecord>,
}

#[cfg(verus_keep_ghost)]
pub struct ATaskFenceRes {
    pub status: u16,
    pub action: Option<ATaskFenceInnerRes>,
    pub preload: Seq<APromiseRecord>,
}

#[cfg(verus_keep_ghost)]
impl DeepView for TaskFenceRes {
    type V = ATaskFenceRes;

    open spec fn deep_view(&self) -> ATaskFenceRes {
        ATaskFenceRes {
            status: self.status,
            action: self.action.deep_view(),
            preload: self.preload.deep_view(),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for TaskFenceRes {
    type V = ATaskFenceRes;
    open spec fn view(&self) -> ATaskFenceRes { self.deep_view() }
}

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Copy, Debug, PartialEq, Eq))]
pub struct StatusRes { pub status: u16 }
#[cfg(verus_keep_ghost)]
pub type AStatusRes = StatusResSpec;
pub type TaskHeartbeatRes = StatusRes;
pub type TaskReleaseRes = StatusRes;
pub type TaskHaltRes = StatusRes;
pub type TaskContinueRes = StatusRes;

#[make_spec_type]
pub struct TaskSuspendRes {
    pub status: u16, pub preload: Vec<PromiseRecord>,
}
#[cfg(verus_keep_ghost)]
pub type ATaskSuspendRes = TaskSuspendResSpec;

#[make_spec_type]
pub struct TaskFulfillRes { pub status: u16, pub promise: Option<PromiseRecord> }
#[cfg(verus_keep_ghost)]
pub type ATaskFulfillRes = TaskFulfillResSpec;

#[make_spec_type]
pub struct TaskSearchRes {
    pub status: u16, pub tasks: Vec<TaskRecord>, pub cursor: Option<Text>,
}
#[cfg(verus_keep_ghost)]
pub type ATaskSearchRes = TaskSearchResSpec;

// Ordered-list helpers ------------------------------------------------------

pub fn dup_tags(tags: &Tags) -> (r: Tags)
    ensures r.deep_view() == tags.deep_view(),
{
    let mut out = Vec::new();
    let mut i: usize = 0;
    while i < tags.len()
        invariant
            i <= tags@.len(),
            out.deep_view() == tags.deep_view().take(i as int),
        decreases tags@.len() - i,
    {
        let next = Tag { key: tags[i].key.dup(), value: tags[i].value.dup() };
        assert(next@ == tags[i as int]@);
        let ghost before = out.deep_view();
        out.push(next);
        assert(out.deep_view() =~= before.push(tags.deep_view()[i as int]));
        assert(tags.deep_view().take(i as int + 1)
            =~= tags.deep_view().take(i as int).push(tags.deep_view()[i as int]));
        i += 1;
    }
    assert(tags.deep_view().take(tags@.len() as int) =~= tags.deep_view());
    out
}

pub fn ident_eq(a: &Ident, b: &Ident) -> (r: bool)
    ensures r == (a@ == b@),
{
    text_eq(&a.origin, &b.origin) && text_eq(&a.suffix, &b.suffix)
}

pub fn text_eq(a: &Text, b: &Text) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.chars.len() != b.chars.len() {
        proof {
            if a@ == b@ {
                assert(a@.chars == b@.chars);
                assert(a@.chars.len() == b@.chars.len());
                assert(false);
            }
        }
        return false;
    }
    let mut i: usize = 0;
    while i < a.chars.len()
        invariant
            a.chars@.len() == b.chars@.len(),
            i <= a.chars@.len(),
            forall|j: int| 0 <= j < i ==> a.chars@[j] == b.chars@[j],
        decreases a.chars@.len() - i,
    {
        if a.chars[i] != b.chars[i] {
            proof {
                if a@ == b@ {
                    assert(a@.chars == b@.chars);
                    assert(a@.chars[i as int] == b@.chars[i as int]);
                    assert(false);
                }
            }
            return false;
        }
        i += 1;
    }
    assert(a.chars@ =~= b.chars@);
    assert(a@.chars =~= b@.chars);
    assert(a@ == b@);
    true
}

pub open spec fn spec_ascii_true(x: AText) -> bool {
    x.chars =~= seq!['t','r','u','e']
}

pub open spec fn spec_ascii_global(x: AText) -> bool {
    x.chars =~= seq!['g','l','o','b','a','l']
}

pub open spec fn spec_tag_key(k: Seq<char>, which: u8) -> bool {
    match which {
        0 => k =~= seq!['r','e','s','o','n','a','t','e',':','t','a','r','g','e','t'],
        1 => k =~= seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e'],
        2 => k =~= seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l'],
        3 => k =~= seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r'],
        _ => k =~= seq!['r','e','s','o','n','a','t','e',':','d','e','l','a','y'],
    }
}

pub open spec fn spec_tag_value_at(
    tags: ATags, which: u8, start: nat,
) -> Option<AText>
    decreases tags.len() - start,
{
    if start >= tags.len() {
        None
    } else if spec_tag_key(tags[start as int].key.chars, which) {
        Some(tags[start as int].value)
    } else {
        spec_tag_value_at(tags, which, start + 1)
    }
}

pub open spec fn spec_tag_value(tags: ATags, which: u8) -> Option<AText> {
    spec_tag_value_at(tags, which, 0)
}

pub open spec fn spec_is_timer(tags: ATags) -> bool {
    match spec_tag_value(tags, 3) {
        Some(v) => spec_ascii_true(v),
        None => false,
    }
}

pub open spec fn spec_has_target(tags: ATags) -> bool {
    spec_tag_value(tags, 0) is Some
}

pub open spec fn spec_otype(tags: ATags) -> OType {
    if spec_has_target(tags) {
        OType::Runnable
    } else {
        let global = match spec_tag_value(tags, 1) {
            Some(v) => spec_ascii_global(v),
            None => false,
        };
        let external = match spec_tag_value(tags, 2) {
            Some(v) => spec_ascii_true(v),
            None => false,
        };
        if global || external || spec_is_timer(tags) {
            OType::External
        } else {
            OType::Internal
        }
    }
}

fn ascii_true(x: &Text) -> (r: bool)
    ensures r == spec_ascii_true(x@),
{
    x.chars.len() == 4 && x.chars[0] == 't' && x.chars[1] == 'r'
        && x.chars[2] == 'u' && x.chars[3] == 'e'
}

fn ascii_global(x: &Text) -> (r: bool)
    ensures r == spec_ascii_global(x@),
{
    x.chars.len() == 6 && x.chars[0] == 'g' && x.chars[1] == 'l'
        && x.chars[2] == 'o' && x.chars[3] == 'b' && x.chars[4] == 'a'
        && x.chars[5] == 'l'
}

pub open spec fn spec_key_prefix(k: Seq<char>) -> bool {
    k.len() >= 9
        && k[0] == 'r' && k[1] == 'e' && k[2] == 's'
        && k[3] == 'o' && k[4] == 'n' && k[5] == 'a'
        && k[6] == 't' && k[7] == 'e' && k[8] == ':'
}

fn key_prefix(x: &Text) -> (r: bool)
    ensures r == spec_key_prefix(x@.chars),
{
    x.chars.len() >= 9 && x.chars[0] == 'r' && x.chars[1] == 'e'
        && x.chars[2] == 's' && x.chars[3] == 'o' && x.chars[4] == 'n'
        && x.chars[5] == 'a' && x.chars[6] == 't' && x.chars[7] == 'e'
        && x.chars[8] == ':'
}

fn key_target(x: &Text) -> (r: bool)
    ensures r == spec_tag_key(x@.chars, 0),
{
    key_prefix(x) && x.chars.len() == 15 && x.chars[9] == 't'
        && x.chars[10] == 'a' && x.chars[11] == 'r' && x.chars[12] == 'g'
        && x.chars[13] == 'e' && x.chars[14] == 't'
}

fn key_scope(x: &Text) -> (r: bool)
    ensures r == spec_tag_key(x@.chars, 1),
{
    key_prefix(x) && x.chars.len() == 14 && x.chars[9] == 's'
        && x.chars[10] == 'c' && x.chars[11] == 'o' && x.chars[12] == 'p'
        && x.chars[13] == 'e'
}

fn key_external(x: &Text) -> (r: bool)
    ensures r == spec_tag_key(x@.chars, 2),
{
    key_prefix(x) && x.chars.len() == 17 && x.chars[9] == 'e'
        && x.chars[10] == 'x' && x.chars[11] == 't' && x.chars[12] == 'e'
        && x.chars[13] == 'r' && x.chars[14] == 'n' && x.chars[15] == 'a'
        && x.chars[16] == 'l'
}

fn key_timer(x: &Text) -> (r: bool)
    ensures r == spec_tag_key(x@.chars, 3),
{
    key_prefix(x) && x.chars.len() == 14 && x.chars[9] == 't'
        && x.chars[10] == 'i' && x.chars[11] == 'm' && x.chars[12] == 'e'
        && x.chars[13] == 'r'
}

fn key_delay(x: &Text) -> (r: bool)
    ensures r == spec_tag_key(x@.chars, 4),
{
    key_prefix(x) && x.chars.len() == 14 && x.chars[9] == 'd'
        && x.chars[10] == 'e' && x.chars[11] == 'l' && x.chars[12] == 'a'
        && x.chars[13] == 'y'
}

/// First matching tag, exactly Lean's `List.find?`.
pub fn tag_value(tags: &Tags, which: u8) -> (r: Option<Text>)
    ensures r.deep_view() == spec_tag_value(tags.deep_view(), which),
{
    let mut i: usize = 0;
    while i < tags.len()
        invariant
            i <= tags@.len(),
            spec_tag_value(tags.deep_view(), which)
                == spec_tag_value_at(tags.deep_view(), which, i as nat),
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
            let r = Some(tags[i].value.dup());
            assert(r.deep_view() == spec_tag_value_at(
                tags.deep_view(), which, i as nat,
            ));
            return r;
        }
        assert(spec_tag_value_at(tags.deep_view(), which, i as nat)
            == spec_tag_value_at(tags.deep_view(), which, i as nat + 1));
        i += 1;
    }
    assert(spec_tag_value_at(tags.deep_view(), which, i as nat) is None);
    None
}

pub fn tags_is_timer(tags: &Tags) -> (r: bool)
    ensures r == spec_is_timer(tags.deep_view()),
{
    match tag_value(tags, 3) { Some(v) => ascii_true(&v), None => false }
}

pub fn tags_has_target(tags: &Tags) -> (r: bool)
    ensures r == spec_has_target(tags.deep_view()),
{
    match tag_value(tags, 0) { Some(_) => true, None => false }
}

pub fn tags_timer_targeted(tags: &Tags) -> (r: bool)
    ensures
        r == (spec_is_timer(tags.deep_view())
            && spec_has_target(tags.deep_view())),
{
    tags_is_timer(tags) && tags_has_target(tags)
}

pub fn tags_otype(tags: &Tags) -> (r: OType)
    ensures r == spec_otype(tags.deep_view()),
{
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
pub open spec fn spec_digit(c: char) -> u64 {
    match c {
        '0' => 0, '1' => 1, '2' => 2, '3' => 3, '4' => 4,
        '5' => 5, '6' => 6, '7' => 7, '8' => 8, '9' => 9,
        _ => 0,
    }
}

pub open spec fn spec_parse_nat_at(chars: Seq<char>, start: nat, acc: u64) -> u64
    decreases chars.len() - start,
{
    if start >= chars.len() {
        acc
    } else {
        let d = spec_digit(chars[start as int]);
        if acc > MAX_TIME / 10 {
            MAX_TIME
        } else {
            let ten = (acc * 10) as u64;
            if d > MAX_TIME - ten {
                MAX_TIME
            } else {
                spec_parse_nat_at(chars, start + 1, (ten + d) as u64)
            }
        }
    }
}

pub open spec fn spec_parse_nat_bounded(x: AText) -> u64 {
    spec_parse_nat_at(x.chars, 0, 0)
}

pub fn parse_nat_bounded(x: &Text) -> (r: u64)
    ensures r == spec_parse_nat_bounded(x@),
{
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < x.chars.len()
        invariant
            i <= x.chars@.len(),
            spec_parse_nat_at(x@.chars, i as nat, acc)
                == spec_parse_nat_bounded(x@),
        decreases x.chars@.len() - i,
    {
        let d = match x.chars[i] {
            '0' => 0,
            '1' => 1,
            '2' => 2,
            '3' => 3,
            '4' => 4,
            '5' => 5,
            '6' => 6,
            '7' => 7,
            '8' => 8,
            '9' => 9,
            _ => 0,
        };
        if acc > MAX_TIME / 10 {
            assert(spec_parse_nat_at(x@.chars, i as nat, acc) == MAX_TIME);
            return MAX_TIME;
        }
        acc = acc * 10;
        if d > MAX_TIME - acc {
            assert(spec_parse_nat_at(x@.chars, i as nat, (acc / 10) as u64)
                == MAX_TIME);
            return MAX_TIME;
        }
        acc = acc + d;
        i += 1;
    }
    acc
}

// Literals ------------------------------------------------------------------

/// The `Text` of a literal's scalar values.
pub fn text_of_str(s: &str) -> (r: Text)
    ensures r@ == (AText { chars: s@ }),
{
    let n = s.unicode_len();
    let mut chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            chars@ == s@.take(i as int),
        decreases n - i,
    {
        let c = s.get_char(i);
        chars.push(c);
        assert(chars@ =~= s@.take(i as int + 1));
        i += 1;
    }
    assert(chars@ =~= s@);
    let r = Text { chars };
    assert(r@.chars =~= s@);
    r
}

/// `x` spells the literal `s`.
pub fn text_is(x: &Text, s: &str) -> (r: bool)
    ensures r == (x@.chars == s@),
{
    let n = s.unicode_len();
    if x.chars.len() != n {
        proof {
            if x@.chars == s@ {
                assert(x@.chars.len() == s@.len());
                assert(false);
            }
        }
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            x.chars@.len() == n,
            forall|j: int| 0 <= j < i ==> x.chars@[j] == s@[j],
        decreases n - i,
    {
        if x.chars[i] != s.get_char(i) {
            proof {
                if x@.chars == s@ {
                    assert(x@.chars[i as int] == s@[i as int]);
                    assert(false);
                }
            }
            return false;
        }
        i += 1;
    }
    assert(x@.chars =~= s@);
    true
}

/// `origin`, or `origin:suffix`: the id as the protocol spells it.
pub open spec fn spec_ident_text(id: AIdent) -> AText {
    if id.suffix.chars.len() == 0 {
        id.origin
    } else {
        AText { chars: id.origin.chars + seq![':'] + id.suffix.chars }
    }
}

pub fn ident_text(id: &Ident) -> (r: Text)
    ensures r@ == spec_ident_text(id@),
{
    if id.suffix.chars.len() == 0 {
        assert(id@.suffix.chars.len() == 0);
        return id.origin.dup();
    }
    assert(id@.suffix.chars.len() != 0);
    let mut chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < id.origin.chars.len()
        invariant
            i <= id.origin.chars@.len(),
            chars@ == id.origin.chars@.take(i as int),
        decreases id.origin.chars@.len() - i,
    {
        chars.push(id.origin.chars[i]);
        assert(chars@ =~= id.origin.chars@.take(i as int + 1));
        i += 1;
    }
    assert(chars@ =~= id.origin.chars@);
    chars.push(':');
    let ghost mid = chars@;
    assert(mid =~= id.origin.chars@ + seq![':']);
    let mut j: usize = 0;
    while j < id.suffix.chars.len()
        invariant
            j <= id.suffix.chars@.len(),
            chars@ == mid + id.suffix.chars@.take(j as int),
        decreases id.suffix.chars@.len() - j,
    {
        chars.push(id.suffix.chars[j]);
        assert(chars@ =~= mid + id.suffix.chars@.take(j as int + 1));
        j += 1;
    }
    assert(chars@ =~= id.origin.chars@ + seq![':'] + id.suffix.chars@);
    let r = Text { chars };
    assert(r@.chars =~= id@.origin.chars + seq![':'] + id@.suffix.chars);
    r
}

// Timer targets -------------------------------------------------------------

/// The tags without any `resonate:target`, in order.
pub open spec fn spec_without_target(tags: ATags) -> ATags
    decreases tags.len(),
{
    if tags.len() == 0 {
        Seq::empty()
    } else if spec_tag_key(tags[0].key.chars, 0) {
        spec_without_target(tags.drop_first())
    } else {
        seq![tags[0]] + spec_without_target(tags.drop_first())
    }
}

/// The wire's concession to the SDKs: a timer created with a target is
/// accepted as a timer alone. Every create normalizes its tags this way
/// before anything else looks at them.
pub open spec fn spec_strip_timer_target(tags: ATags) -> ATags {
    if spec_is_timer(tags) { spec_without_target(tags) } else { tags }
}

pub fn strip_timer_target(tags: Tags) -> (r: Tags)
    ensures r.deep_view() == spec_strip_timer_target(tags.deep_view()),
{
    if !tags_is_timer(&tags) {
        return tags;
    }
    let ghost s = tags.deep_view();
    let mut out: Tags = Vec::new();
    let mut i: usize = 0;
    assert(s.skip(0) =~= s);
    assert(out.deep_view() =~= Seq::<ATag>::empty());
    while i < tags.len()
        invariant
            i <= tags@.len(),
            s == tags.deep_view(),
            out.deep_view() + spec_without_target(s.skip(i as int))
                == spec_without_target(s),
        decreases tags@.len() - i,
    {
        let ghost rest = s.skip(i as int);
        assert(rest.len() > 0);
        assert(rest[0] == s[i as int]);
        assert(rest.drop_first() =~= s.skip(i as int + 1));
        if key_target(&tags[i].key) {
            assert(spec_without_target(rest)
                == spec_without_target(s.skip(i as int + 1)));
        } else {
            let next = Tag { key: tags[i].key.dup(), value: tags[i].value.dup() };
            assert(next@ == tags[i as int]@);
            let ghost before = out.deep_view();
            out.push(next);
            assert(out.deep_view() =~= before.push(s[i as int]));
            assert(spec_without_target(rest)
                == seq![s[i as int]] + spec_without_target(s.skip(i as int + 1)));
            assert(before.push(s[i as int]) + spec_without_target(s.skip(i as int + 1))
                =~= before + (seq![s[i as int]] + spec_without_target(s.skip(i as int + 1))));
        }
        i += 1;
    }
    assert(s.skip(s.len() as int) =~= Seq::<ATag>::empty());
    assert(out.deep_view() + Seq::<ATag>::empty() =~= out.deep_view());
    out
}

// Lineage -------------------------------------------------------------------

/// The keys a schedule's firing stamps; a template's own are dropped first.
pub open spec fn spec_stamped_key(k: Seq<char>) -> bool {
    ||| k == "resonate:schedule"@
    ||| k == "resonate:origin"@
    ||| k == "resonate:branch"@
    ||| k == "resonate:parent"@
    ||| k == "resonate:prefix"@
}

pub fn is_stamped_key(k: &Text) -> (r: bool)
    ensures r == spec_stamped_key(k@.chars),
{
    text_is(k, "resonate:schedule") || text_is(k, "resonate:origin")
        || text_is(k, "resonate:branch") || text_is(k, "resonate:parent")
        || text_is(k, "resonate:prefix")
}

/// The template without the stamped keys, in order.
pub open spec fn spec_strip_stamped(tags: ATags) -> ATags
    decreases tags.len(),
{
    if tags.len() == 0 {
        Seq::empty()
    } else if spec_stamped_key(tags[0].key.chars) {
        spec_strip_stamped(tags.drop_first())
    } else {
        seq![tags[0]] + spec_strip_stamped(tags.drop_first())
    }
}

/// What a firing stamps: the schedule, and the lineage, which for a root
/// promise is itself four times over.
pub open spec fn spec_lineage(sid: AIdent, pid: AIdent) -> ATags {
    let s = spec_ident_text(sid);
    let p = spec_ident_text(pid);
    seq![
        ATag { key: AText { chars: "resonate:schedule"@ }, value: s },
        ATag { key: AText { chars: "resonate:origin"@ }, value: p },
        ATag { key: AText { chars: "resonate:branch"@ }, value: p },
        ATag { key: AText { chars: "resonate:parent"@ }, value: p },
        ATag { key: AText { chars: "resonate:prefix"@ }, value: p },
    ]
}

/// The tags of the promise schedule `sid` fires at `pid`: the template
/// stripped, then the stamp.
pub open spec fn spec_stamp(tags: ATags, sid: AIdent, pid: AIdent) -> ATags {
    spec_strip_stamped(tags) + spec_lineage(sid, pid)
}

fn lineage(sid: &Ident, pid: &Ident) -> (r: Tags)
    ensures r.deep_view() == spec_lineage(sid@, pid@),
{
    let s = ident_text(sid);
    let p = ident_text(pid);
    let mut out: Tags = Vec::new();
    let t0 = Tag { key: text_of_str("resonate:schedule"), value: s };
    let t1 = Tag { key: text_of_str("resonate:origin"), value: p.dup() };
    let t2 = Tag { key: text_of_str("resonate:branch"), value: p.dup() };
    let t3 = Tag { key: text_of_str("resonate:parent"), value: p.dup() };
    let t4 = Tag { key: text_of_str("resonate:prefix"), value: p };
    assert(t0@ == spec_lineage(sid@, pid@)[0]);
    assert(t1@ == spec_lineage(sid@, pid@)[1]);
    assert(t2@ == spec_lineage(sid@, pid@)[2]);
    assert(t3@ == spec_lineage(sid@, pid@)[3]);
    assert(t4@ == spec_lineage(sid@, pid@)[4]);
    out.push(t0);
    out.push(t1);
    out.push(t2);
    out.push(t3);
    out.push(t4);
    assert(out.deep_view() =~= spec_lineage(sid@, pid@));
    out
}

pub fn stamp_tags(tags: &Tags, sid: &Ident, pid: &Ident) -> (r: Tags)
    ensures r.deep_view() == spec_stamp(tags.deep_view(), sid@, pid@),
{
    let ghost s = tags.deep_view();
    let mut out: Tags = Vec::new();
    let mut i: usize = 0;
    assert(s.skip(0) =~= s);
    assert(out.deep_view() =~= Seq::<ATag>::empty());
    while i < tags.len()
        invariant
            i <= tags@.len(),
            s == tags.deep_view(),
            out.deep_view() + spec_strip_stamped(s.skip(i as int))
                == spec_strip_stamped(s),
        decreases tags@.len() - i,
    {
        let ghost rest = s.skip(i as int);
        assert(rest.len() > 0);
        assert(rest[0] == s[i as int]);
        assert(rest.drop_first() =~= s.skip(i as int + 1));
        if is_stamped_key(&tags[i].key) {
            assert(spec_strip_stamped(rest)
                == spec_strip_stamped(s.skip(i as int + 1)));
        } else {
            let next = Tag { key: tags[i].key.dup(), value: tags[i].value.dup() };
            assert(next@ == tags[i as int]@);
            let ghost before = out.deep_view();
            out.push(next);
            assert(out.deep_view() =~= before.push(s[i as int]));
            assert(spec_strip_stamped(rest)
                == seq![s[i as int]] + spec_strip_stamped(s.skip(i as int + 1)));
            assert(before.push(s[i as int]) + spec_strip_stamped(s.skip(i as int + 1))
                =~= before + (seq![s[i as int]] + spec_strip_stamped(s.skip(i as int + 1))));
        }
        i += 1;
    }
    assert(s.skip(s.len() as int) =~= Seq::<ATag>::empty());
    assert(out.deep_view() =~= spec_strip_stamped(s));
    let ghost stripped = out.deep_view();
    let more = lineage(sid, pid);
    let ghost lin = more.deep_view();
    let mut k: usize = 0;
    while k < more.len()
        invariant
            k <= more@.len(),
            lin == more.deep_view(),
            out.deep_view() == stripped + lin.take(k as int),
        decreases more@.len() - k,
    {
        let next = Tag { key: more[k].key.dup(), value: more[k].value.dup() };
        assert(next@ == more[k as int]@);
        let ghost before = out.deep_view();
        out.push(next);
        assert(out.deep_view() =~= before.push(lin[k as int]));
        assert(stripped + lin.take(k as int + 1)
            =~= (stripped + lin.take(k as int)).push(lin[k as int]));
        k += 1;
    }
    assert(lin.take(lin.len() as int) =~= lin);
    out
}

// The retry grid ------------------------------------------------------------

/// The anchored retry grid: the first point `due + k * t` strictly after
/// `now`, or `due` itself while it is still ahead. A node that dispatches
/// late does not shift the grid; the task keeps the cadence it was given.
pub open spec fn spec_next_offer(due: u64, now: u64, t: u64) -> u64 {
    if t == 0 || now < due {
        due
    } else {
        let next = due + t * ((now - due) / (t as int) + 1);
        if next > u64::MAX { u64::MAX } else { next as u64 }
    }
}

pub fn next_offer(due: u64, now: u64, t: u64) -> (r: u64)
    ensures r == spec_next_offer(due, now, t),
{
    if t == 0 || now < due {
        return due;
    }
    let x = now - due;
    let q = x / t;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, t as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(x as int, t as int);
        assert(t * q <= x);
        assert(t * (q + 1) == t * q + t) by (nonlinear_arith);
    }
    let base = due + t * q;
    if t <= u64::MAX - base {
        base + t
    } else {
        u64::MAX
    }
}

} // verus!
