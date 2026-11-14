//! The types the specifications and the implementation share: records,
//! requests, and responses.
//!
//! A record is what a response shows. A request is what `handle` takes and
//! what a trace names. The document row, with its callbacks, listeners, and
//! task, stays in the concrete specification; a record is that row with
//! those fields left off.
//!
//! Every type with a string or a list has a twin, `make_spec_type`'s
//! `…Spec`. Those views are named `A…` in `spec`, and re-exported here.

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
/// The view is `spec::ATags`.
pub type Tags = Vec<(String, String)>;

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

impl Value {
    pub fn empty() -> (v: Value)
        ensures v@ == AValue::empty(),
    {
        let v = Value { headers: Vec::new(), data: None };
        assert(v@.headers =~= Seq::empty());
        v
    }

    /// The empty value, as a specification names it. Both models create
    /// promises with this one value.
    pub open spec fn spec_empty() -> Value {
        choose|v: Value| v@ == AValue::empty()
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

// ---------------------------------------------------------------------------
// Requests
// ---------------------------------------------------------------------------

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseGetReq { pub id: String }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseCreateReq {
    pub id: String,
    pub timeout_at: u64,
    pub param: Value,
    pub tags: Tags,
}



#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseSettleReq {
    pub id: String,
    pub state: PromiseState,
    pub value: Value,
}


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseRegisterCallbackReq { pub awaited: String, pub awaiter: String }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseRegisterListenerReq { pub awaited: String, pub address: String }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ScheduleGetReq { pub id: String }


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


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ScheduleDeleteReq { pub id: String }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskGetReq { pub id: String }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskCreateReq { pub pid: String, pub ttl: u64, pub action: PromiseCreateReq }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskAcquireReq { pub id: String, pub version: u64, pub pid: String, pub ttl: u64 }


#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum TaskFenceAction {
    Create(PromiseCreateReq),
    Settle(PromiseSettleReq),
}

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskFenceReq { pub id: String, pub version: u64, pub action: TaskFenceAction }


/// `task.fence` with no action: the check alone (`task_fence_check`).
#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskFenceCheckReq { pub id: String, pub version: u64 }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskRef { pub id: String, pub version: u64 }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskHeartbeatReq { pub pid: String, pub tasks: Vec<TaskRef> }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskSuspendReq {
    pub id: String,
    pub version: u64,
    pub actions: Vec<PromiseRegisterCallbackReq>,
}


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskFulfillReq { pub id: String, pub version: u64, pub action: PromiseSettleReq }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskReleaseReq { pub id: String, pub version: u64 }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskHaltReq { pub id: String }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskContinueReq { pub id: String }

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

// ---------------------------------------------------------------------------
// Responses
// ---------------------------------------------------------------------------

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct PromiseRes { pub status: u16, pub promise: Option<PromiseRecord> }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ScheduleRes { pub status: u16, pub schedule: Option<Schedule> }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct StatusRes { pub status: u16 }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskGetRes { pub status: u16, pub task: Option<TaskRecord> }


#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskClaimRes {
    pub status: u16,
    pub task: Option<TaskRecord>,
    pub promise: Option<PromiseRecord>,
}


#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum TaskFenceInnerRes {
    Create(PromiseRes),
    Settle(PromiseRes),
}

#[make_spec_type]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TaskFenceRes { pub status: u16, pub action: Option<TaskFenceInnerRes> }


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

/// The origin of an id: everything before the first `:`.
#[verifier::external_body]
pub fn origin_of<'a>(id: &'a str) -> (r: &'a str)
    ensures r@ == origin(id@),
{
    id.split_once(':').map(|(o, _)| o).unwrap_or(id)
}

/// Do two ids share an origin?
#[verifier::external_body]
pub fn same_origin(a: &String, b: &String) -> (r: bool)
    ensures r == same_origin_spec(a@, b@),
{
    origin_of(a) == origin_of(b)
}

} // verus!

#[cfg(verus_keep_ghost)]
pub mod spec;

#[cfg(verus_keep_ghost)]
pub use spec::*;
