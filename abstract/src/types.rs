//! Protocol vocabulary from `01-protocol/types.lean`.
//!
//! `Text` is a vector of Unicode scalar values. This matches the kernel's
//! `Seq<char>` view directly; encoding belongs to the wire boundary.

use vstd::contrib::{make_spec_type, self_view};
use vstd::prelude::*;

verus! {

pub const MAX_TIME: u64 = 0x3fff_ffff_ffff_ffff;

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

#[make_spec_type]
pub struct Occurrence {
    pub at: u64,
    /// Executable witness for Lean's opaque `expand template schedule at`.
    pub promise_id: Ident,
}

#[make_spec_type]
pub struct ScheduleTimeoutReq {
    pub schedule: Ident,
    /// Executable witness for Lean's opaque `occurrences`, in Lean list order.
    pub occurrences: Vec<Occurrence>,
    /// `nextCron cron last`, used only when `occurrences` is nonempty.
    pub next_run_at: u64,
}

#[cfg(verus_keep_ghost)]
pub type AOccurrence = OccurrenceSpec;
#[cfg(verus_keep_ghost)]
pub type AScheduleTimeoutReq = ScheduleTimeoutReqSpec;

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

} // verus!
