//! The view of every type in this crate.
//!
//! `make_spec_type` writes `…Spec` next to the executable type. A string
//! views as `Seq<char>` and a `Vec` as `Seq`. The `A…` names here are those
//! views. Abstract and concrete specifications import them from this module.
//!
//! `Request`, `Response`, and the two fence enums are written out. Their
//! payloads are views, which `make_spec_type` does not wrap.

use vstd::prelude::*;

verus! {

use super::{
    PromiseCreateReqSpec, PromiseGetReqSpec, PromiseRecordSpec, PromiseRegisterCallbackReqSpec,
    PromiseRegisterListenerReqSpec, PromiseResSpec, PromiseSettleReqSpec, Request, Response,
    ScheduleCreateReqSpec, ScheduleDeleteReqSpec, ScheduleGetReqSpec, ScheduleResSpec, ScheduleSpec,
    StatusResSpec, TaskAcquireReqSpec, TaskClaimResSpec, TaskContinueReqSpec, TaskCreateReqSpec,
    TaskFenceAction, TaskFenceCheckReqSpec, TaskFenceInnerRes, TaskFenceReqSpec, TaskFenceResSpec,
    TaskFulfillReqSpec, TaskGetReqSpec, TaskGetResSpec, TaskHaltReqSpec, TaskHeartbeatReqSpec,
    TaskRecordSpec, TaskRefSpec, TaskReleaseReqSpec, TaskSuspendReqSpec, ValueSpec,
};

// ---------------------------------------------------------------------------
// Generated views
// ---------------------------------------------------------------------------

/// Tags, first match wins, as a sequence of pairs.
pub type ATags = Seq<(Seq<char>, Seq<char>)>;

pub type AValue = ValueSpec;
pub type ASchedule = ScheduleSpec;
pub type APromiseRecord = PromiseRecordSpec;
pub type ATaskRecord = TaskRecordSpec;

pub type APromiseGetReq = PromiseGetReqSpec;
pub type APromiseCreateReq = PromiseCreateReqSpec;
pub type APromiseSettleReq = PromiseSettleReqSpec;
pub type APromiseRegisterCallbackReq = PromiseRegisterCallbackReqSpec;
pub type APromiseRegisterListenerReq = PromiseRegisterListenerReqSpec;

pub type AScheduleGetReq = ScheduleGetReqSpec;
pub type AScheduleCreateReq = ScheduleCreateReqSpec;
pub type AScheduleDeleteReq = ScheduleDeleteReqSpec;

pub type ATaskGetReq = TaskGetReqSpec;
pub type ATaskCreateReq = TaskCreateReqSpec;
pub type ATaskAcquireReq = TaskAcquireReqSpec;
pub type ATaskFenceReq = TaskFenceReqSpec;
pub type ATaskFenceCheckReq = TaskFenceCheckReqSpec;
pub type ATaskRef = TaskRefSpec;
pub type ATaskHeartbeatReq = TaskHeartbeatReqSpec;
pub type ATaskSuspendReq = TaskSuspendReqSpec;
pub type ATaskFulfillReq = TaskFulfillReqSpec;
pub type ATaskReleaseReq = TaskReleaseReqSpec;
pub type ATaskHaltReq = TaskHaltReqSpec;
pub type ATaskContinueReq = TaskContinueReqSpec;

pub type APromiseRes = PromiseResSpec;
pub type AScheduleRes = ScheduleResSpec;
pub type AStatusRes = StatusResSpec;
pub type ATaskGetRes = TaskGetResSpec;
pub type ATaskClaimRes = TaskClaimResSpec;
pub type ATaskFenceRes = TaskFenceResSpec;

impl AValue {
    pub open spec fn empty() -> AValue {
        AValue { headers: Seq::empty(), data: None }
    }

    pub open spec fn is_empty(self) -> bool {
        self.data is None && self.headers.len() == 0
    }
}

// ---------------------------------------------------------------------------
// Enums whose payloads are views
// ---------------------------------------------------------------------------

pub enum ATaskFenceAction {
    Create(APromiseCreateReq),
    Settle(APromiseSettleReq),
}

impl DeepView for TaskFenceAction {
    type V = ATaskFenceAction;
    open spec fn deep_view(&self) -> ATaskFenceAction {
        match self {
            TaskFenceAction::Create(c) => ATaskFenceAction::Create(c.deep_view()),
            TaskFenceAction::Settle(c) => ATaskFenceAction::Settle(c.deep_view()),
        }
    }
}

impl View for TaskFenceAction {
    type V = ATaskFenceAction;
    open spec fn view(&self) -> ATaskFenceAction {
        self.deep_view()
    }
}

pub enum ATaskFenceInnerRes {
    Create(APromiseRes),
    Settle(APromiseRes),
}

impl DeepView for TaskFenceInnerRes {
    type V = ATaskFenceInnerRes;
    open spec fn deep_view(&self) -> ATaskFenceInnerRes {
        match self {
            TaskFenceInnerRes::Create(r) => ATaskFenceInnerRes::Create(r.deep_view()),
            TaskFenceInnerRes::Settle(r) => ATaskFenceInnerRes::Settle(r.deep_view()),
        }
    }
}

impl View for TaskFenceInnerRes {
    type V = ATaskFenceInnerRes;
    open spec fn view(&self) -> ATaskFenceInnerRes {
        self.deep_view()
    }
}

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

pub enum AResponse {
    Promise(APromiseRes),
    Schedule(AScheduleRes),
    Status(AStatusRes),
    TaskGet(ATaskGetRes),
    TaskClaim(ATaskClaimRes),
    TaskFence(ATaskFenceRes),
}

/// A request is a value the models take as it is: its deep view is itself.
impl DeepView for Request {
    type V = Request;
    open spec fn deep_view(&self) -> Request {
        *self
    }
}

impl DeepView for Response {
    type V = AResponse;
    open spec fn deep_view(&self) -> AResponse {
        self.view()
    }
}

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

} // verus!
