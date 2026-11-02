//! The types the specifications and the implementation share: records,
//! requests, and responses.
//!
//! A record is what a response shows. A request is what `handle` takes and
//! what a trace names. The document row, with its callbacks, listeners, and
//! task, stays in the concrete specification; a record is that row with
//! those fields left off.
//!
//! Every type with a string or a list has a twin, `make_spec_type`'s
//! `…Spec`, named `A…` here, reached through `View`.

use vstd::contrib::{make_spec_type, self_view};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Enumerations
// ---------------------------------------------------------------------------

#[self_view]
#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(not(verus_keep_ghost), serde(rename_all = "snake_case"))]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Structural, Debug)]
pub enum PromiseState {
    Pending,
    Resolved,
    Rejected,
    RejectedCanceled,
    RejectedTimedout,
}

#[self_view]
#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(not(verus_keep_ghost), serde(rename_all = "snake_case"))]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Structural, Debug)]
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

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Value {
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Vec::is_empty"))]
    pub headers: Tags,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub data: Option<String>,
}

#[cfg(verus_keep_ghost)]
pub type AValue = ValueSpec;

#[cfg(verus_keep_ghost)]
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
// Schedules
// ---------------------------------------------------------------------------

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
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

#[cfg(verus_keep_ghost)]
pub type ASchedule = ScheduleSpec;

// ---------------------------------------------------------------------------
// Records: what a response carries
// ---------------------------------------------------------------------------

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
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

#[cfg(verus_keep_ghost)]
pub type APromiseRecord = PromiseRecordSpec;
#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskRecord {
    pub id: String,
    pub state: TaskState,
    pub version: u64,
    pub resumes: u64,
    pub ttl: Option<u64>,
    pub pid: Option<String>,
}

#[cfg(verus_keep_ghost)]
pub type ATaskRecord = TaskRecordSpec;
// ---------------------------------------------------------------------------
// Requests
// ---------------------------------------------------------------------------

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseGetReq { pub id: String }

#[cfg(verus_keep_ghost)]
pub type APromiseGetReq = PromiseGetReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseCreateReq {
    pub id: String,
    pub timeout_at: u64,
    pub param: Value,
    pub tags: Tags,
}

#[cfg(verus_keep_ghost)]
pub type APromiseCreateReq = PromiseCreateReqSpec;


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseSettleReq {
    pub id: String,
    pub state: PromiseState,
    pub value: Value,
}

#[cfg(verus_keep_ghost)]
pub type APromiseSettleReq = PromiseSettleReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseRegisterCallbackReq { pub awaited: String, pub awaiter: String }

#[cfg(verus_keep_ghost)]
pub type APromiseRegisterCallbackReq = PromiseRegisterCallbackReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseRegisterListenerReq { pub awaited: String, pub address: String }

#[cfg(verus_keep_ghost)]
pub type APromiseRegisterListenerReq = PromiseRegisterListenerReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ScheduleGetReq { pub id: String }

#[cfg(verus_keep_ghost)]
pub type AScheduleGetReq = ScheduleGetReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
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

#[cfg(verus_keep_ghost)]
pub type AScheduleCreateReq = ScheduleCreateReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ScheduleDeleteReq { pub id: String }

#[cfg(verus_keep_ghost)]
pub type AScheduleDeleteReq = ScheduleDeleteReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskGetReq { pub id: String }

#[cfg(verus_keep_ghost)]
pub type ATaskGetReq = TaskGetReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskCreateReq { pub pid: String, pub ttl: u64, pub action: PromiseCreateReq }

#[cfg(verus_keep_ghost)]
pub type ATaskCreateReq = TaskCreateReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskAcquireReq { pub id: String, pub version: u64, pub pid: String, pub ttl: u64 }

#[cfg(verus_keep_ghost)]
pub type ATaskAcquireReq = TaskAcquireReqSpec;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
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
            TaskFenceAction::Create(c) => ATaskFenceAction::Create(c.deep_view()),
            TaskFenceAction::Settle(c) => ATaskFenceAction::Settle(c.deep_view()),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for TaskFenceAction {
    type V = ATaskFenceAction;
    open spec fn view(&self) -> ATaskFenceAction { self.deep_view() }
}

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskFenceReq { pub id: String, pub version: u64, pub action: TaskFenceAction }

#[cfg(verus_keep_ghost)]
pub type ATaskFenceReq = TaskFenceReqSpec;

/// `task.fence` with no action: the check alone (`task_fence_check`).
#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskFenceCheckReq { pub id: String, pub version: u64 }

#[cfg(verus_keep_ghost)]
pub type ATaskFenceCheckReq = TaskFenceCheckReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskRef { pub id: String, pub version: u64 }

#[cfg(verus_keep_ghost)]
pub type ATaskRef = TaskRefSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskHeartbeatReq { pub pid: String, pub tasks: Vec<TaskRef> }

#[cfg(verus_keep_ghost)]
pub type ATaskHeartbeatReq = TaskHeartbeatReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskSuspendReq {
    pub id: String,
    pub version: u64,
    pub actions: Vec<PromiseRegisterCallbackReq>,
}

#[cfg(verus_keep_ghost)]
pub type ATaskSuspendReq = TaskSuspendReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskFulfillReq { pub id: String, pub version: u64, pub action: PromiseSettleReq }

#[cfg(verus_keep_ghost)]
pub type ATaskFulfillReq = TaskFulfillReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskReleaseReq { pub id: String, pub version: u64 }

#[cfg(verus_keep_ghost)]
pub type ATaskReleaseReq = TaskReleaseReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskHaltReq { pub id: String }

#[cfg(verus_keep_ghost)]
pub type ATaskHaltReq = TaskHaltReqSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskContinueReq { pub id: String }

#[cfg(verus_keep_ghost)]
pub type ATaskContinueReq = TaskContinueReqSpec;
/// Any request: what the system model carries into a step, and what `handle`
/// dispatches on.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Request {
    PromiseGet(PromiseGetReq),
    PromiseCreate(PromiseCreateReq),
    PromiseSettle(PromiseSettleReq),
    PromiseRegisterCallback(PromiseRegisterCallbackReq),
    PromiseRegisterListener(PromiseRegisterListenerReq),
    ScheduleGet(ScheduleGetReq),
    ScheduleCreate(ScheduleCreateReq),
    ScheduleDelete(ScheduleDeleteReq),
    TaskGet(TaskGetReq),
    TaskCreate(TaskCreateReq),
    TaskAcquire(TaskAcquireReq),
    TaskFulfill(TaskFulfillReq),
    TaskRelease(TaskReleaseReq),
    TaskHalt(TaskHaltReq),
    TaskContinue(TaskContinueReq),
    TaskFence(TaskFenceReq),
    TaskFenceCheck(TaskFenceCheckReq),
    TaskHeartbeat(TaskHeartbeatReq),
    TaskSuspend(TaskSuspendReq),
}

#[cfg(verus_keep_ghost)]
pub enum ARequest {
    PromiseGet(APromiseGetReq),
    PromiseCreate(APromiseCreateReq),
    PromiseSettle(APromiseSettleReq),
    PromiseRegisterCallback(APromiseRegisterCallbackReq),
    PromiseRegisterListener(APromiseRegisterListenerReq),
    ScheduleGet(AScheduleGetReq),
    ScheduleCreate(AScheduleCreateReq),
    ScheduleDelete(AScheduleDeleteReq),
    TaskGet(ATaskGetReq),
    TaskCreate(ATaskCreateReq),
    TaskAcquire(ATaskAcquireReq),
    TaskFulfill(ATaskFulfillReq),
    TaskRelease(ATaskReleaseReq),
    TaskHalt(ATaskHaltReq),
    TaskContinue(ATaskContinueReq),
    TaskFence(ATaskFenceReq),
    TaskFenceCheck(ATaskFenceCheckReq),
    TaskHeartbeat(ATaskHeartbeatReq),
    TaskSuspend(ATaskSuspendReq),
}

#[cfg(verus_keep_ghost)]
impl View for Request {
    type V = ARequest;
    open spec fn view(&self) -> ARequest {
        match self {
            Request::PromiseGet(r) => ARequest::PromiseGet(r@),
            Request::PromiseCreate(r) => ARequest::PromiseCreate(r@),
            Request::PromiseSettle(r) => ARequest::PromiseSettle(r@),
            Request::PromiseRegisterCallback(r) => ARequest::PromiseRegisterCallback(r@),
            Request::PromiseRegisterListener(r) => ARequest::PromiseRegisterListener(r@),
            Request::ScheduleGet(r) => ARequest::ScheduleGet(r@),
            Request::ScheduleCreate(r) => ARequest::ScheduleCreate(r@),
            Request::ScheduleDelete(r) => ARequest::ScheduleDelete(r@),
            Request::TaskGet(r) => ARequest::TaskGet(r@),
            Request::TaskCreate(r) => ARequest::TaskCreate(r@),
            Request::TaskAcquire(r) => ARequest::TaskAcquire(r@),
            Request::TaskFulfill(r) => ARequest::TaskFulfill(r@),
            Request::TaskRelease(r) => ARequest::TaskRelease(r@),
            Request::TaskHalt(r) => ARequest::TaskHalt(r@),
            Request::TaskContinue(r) => ARequest::TaskContinue(r@),
            Request::TaskFence(r) => ARequest::TaskFence(r@),
            Request::TaskFenceCheck(r) => ARequest::TaskFenceCheck(r@),
            Request::TaskHeartbeat(r) => ARequest::TaskHeartbeat(r@),
            Request::TaskSuspend(r) => ARequest::TaskSuspend(r@),
        }
    }
}

// ---------------------------------------------------------------------------
// Responses
// ---------------------------------------------------------------------------

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseRes { pub status: u16, pub promise: Option<PromiseRecord> }

#[cfg(verus_keep_ghost)]
pub type APromiseRes = PromiseResSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ScheduleRes { pub status: u16, pub schedule: Option<Schedule> }

#[cfg(verus_keep_ghost)]
pub type AScheduleRes = ScheduleResSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct StatusRes { pub status: u16 }

#[cfg(verus_keep_ghost)]
pub type AStatusRes = StatusResSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskGetRes { pub status: u16, pub task: Option<TaskRecord> }

#[cfg(verus_keep_ghost)]
pub type ATaskGetRes = TaskGetResSpec;

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskClaimRes {
    pub status: u16,
    pub task: Option<TaskRecord>,
    pub promise: Option<PromiseRecord>,
}

#[cfg(verus_keep_ghost)]
pub type ATaskClaimRes = TaskClaimResSpec;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum TaskFenceInnerRes {
    Create(PromiseRes),
    Settle(PromiseRes),
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
            TaskFenceInnerRes::Create(r) => ATaskFenceInnerRes::Create(r.deep_view()),
            TaskFenceInnerRes::Settle(r) => ATaskFenceInnerRes::Settle(r.deep_view()),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for TaskFenceInnerRes {
    type V = ATaskFenceInnerRes;
    open spec fn view(&self) -> ATaskFenceInnerRes { self.deep_view() }
}

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskFenceRes { pub status: u16, pub action: Option<TaskFenceInnerRes> }

#[cfg(verus_keep_ghost)]
pub type ATaskFenceRes = TaskFenceResSpec;

/// Any response: what `handle` answers, and what the system model records.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Response {
    Promise(PromiseRes),
    Schedule(ScheduleRes),
    Status(StatusRes),
    TaskGet(TaskGetRes),
    TaskClaim(TaskClaimRes),
    TaskFence(TaskFenceRes),
}

#[cfg(verus_keep_ghost)]
pub enum AResponse {
    Promise(APromiseRes),
    Schedule(AScheduleRes),
    Status(AStatusRes),
    TaskGet(ATaskGetRes),
    TaskClaim(ATaskClaimRes),
    TaskFence(ATaskFenceRes),
}

#[cfg(verus_keep_ghost)]
impl View for Response {
    type V = AResponse;
    open spec fn view(&self) -> AResponse {
        match self {
            Response::Promise(r) => AResponse::Promise(r@),
            Response::Schedule(r) => AResponse::Schedule(r@),
            Response::Status(r) => AResponse::Status(r@),
            Response::TaskGet(r) => AResponse::TaskGet(r@),
            Response::TaskClaim(r) => AResponse::TaskClaim(r@),
            Response::TaskFence(r) => AResponse::TaskFence(r@),
        }
    }
}

impl Response {
    pub open spec fn status(self) -> u16 {
        match self {
            Response::Promise(r) => r.status,
            Response::Schedule(r) => r.status,
            Response::Status(r) => r.status,
            Response::TaskGet(r) => r.status,
            Response::TaskClaim(r) => r.status,
            Response::TaskFence(r) => r.status,
        }
    }
}

#[cfg(verus_keep_ghost)]
impl AResponse {
    pub open spec fn status(self) -> u16 {
        match self {
            AResponse::Promise(r) => r.status,
            AResponse::Schedule(r) => r.status,
            AResponse::Status(r) => r.status,
            AResponse::TaskGet(r) => r.status,
            AResponse::TaskClaim(r) => r.status,
            AResponse::TaskFence(r) => r.status,
        }
    }
}

pub fn clone_tags(t: &Tags) -> (r: Tags)
    ensures r.deep_view() == t.deep_view(),
{
    let ghost s = t.deep_view();
    let mut r: Tags = Vec::new();
    let mut i: usize = 0;
    assert(r.deep_view() =~= s.take(0));
    while i < t.len()
        invariant
            i <= t@.len(),
            s == t.deep_view(),
            r.deep_view() == s.take(i as int),
        decreases t@.len() - i,
    {
        let ghost before = r.deep_view();
        r.push((t[i].0.clone(), t[i].1.clone()));
        assert(r.deep_view() =~= before.push(s[i as int]));
        assert(s.take(i as int + 1) =~= s.take(i as int).push(s[i as int]));
        i += 1;
    }
    assert(s.take(t@.len() as int) =~= s);
    r
}

impl Schedule {
    pub fn dup(&self) -> (r: Schedule)
        ensures r@ == self@,
    {
        Schedule {
            id: self.id.clone(),
            cron: self.cron.clone(),
            promise_id: self.promise_id.clone(),
            promise_timeout: self.promise_timeout,
            promise_param: self.promise_param.dup(),
            promise_tags: clone_tags(&self.promise_tags),
            next_run_at: self.next_run_at,
            last_run_at: self.last_run_at,
            created_at: self.created_at,
        }
    }
}

impl Value {
    pub fn dup(&self) -> (r: Value)
        ensures r@ == self@,
    {
        Value {
            headers: clone_tags(&self.headers),
            data: match &self.data {
                Some(d) => Some(d.clone()),
                None => None,
            },
        }
    }
}

} // verus!
