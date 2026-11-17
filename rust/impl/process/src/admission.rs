use vstd::prelude::*;
use crate::Target;
use crate::keys::origin_of;
use crate::verified::runtime::copy;
use crate::verified::text::text;
use crate::verified::node::str_eq;
use echod_types::{Request, TaskFenceAction, TaskFenceCheckReq, MAX_TIME};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::handler::{production_normalize_admission, production_request_target};

verus! {
pub fn route(request: &Request) -> (result: Option<Target>)
    ensures result.deep_view() == production_request_target(*request),
{
    let (id, schedule): (&str, bool) = match request {
        Request::PromiseGet(q) => (q.id.as_str(), false),
        Request::PromiseCreate(q) => (q.id.as_str(), false),
        Request::PromiseSettle(q) => (q.id.as_str(), false),
        Request::PromiseRegisterCallback(q) => (q.awaited.as_str(), false),
        Request::PromiseRegisterListener(q) => (q.awaited.as_str(), false),
        Request::TaskGet(q) => (q.id.as_str(), false),
        Request::TaskCreate(q) => (q.action.id.as_str(), false),
        Request::TaskAcquire(q) => (q.id.as_str(), false),
        Request::TaskFulfill(q) => (q.id.as_str(), false),
        Request::TaskRelease(q) => (q.id.as_str(), false),
        Request::TaskHalt(q) => (q.id.as_str(), false),
        Request::TaskContinue(q) => (q.id.as_str(), false),
        Request::TaskFence(q) => (q.id.as_str(), false),
        Request::TaskFenceCheck(q) => (q.id.as_str(), false),
        Request::TaskSuspend(q) => (q.id.as_str(), false),
        Request::TaskHeartbeat(q) => {
            if q.tasks.is_empty() { return None; }
            (q.tasks[0].id.as_str(), false)
        },
        Request::ScheduleGet(q) => (q.id.as_str(), true),
        Request::ScheduleCreate(q) => (q.id.as_str(), true),
        Request::ScheduleDelete(q) => (q.id.as_str(), true),
    };
    let name = if schedule { id } else { origin_of(id) };
    if name.is_empty() { None }
    else if schedule { Some(Target::Schedule(text(name))) }
    else { Some(Target::Origin(text(name))) }
}

pub fn normalize(target: Target, request: Request) -> (result: (Target, Request, Option<(Target, Request)>))
    ensures
        result.deep_view() == production_normalize_admission(target.deep_view(), request),
{
    if let Request::TaskFence(q) = &request {
        if let TaskFenceAction::Create(create) = &q.action {
            let destination = origin_of(&create.id);
            let source = origin_of(&q.id);
            if create.timeout_at <= MAX_TIME && !str_eq(destination, source) {
                return (
                    Target::Origin(text(destination)), Request::PromiseCreate(copy(create)),
                    Some((Target::Origin(text(source)), Request::TaskFenceCheck(TaskFenceCheckReq { id: copy(&q.id), version: q.version }))),
                );
            }
        }
    }
    (target, request, None)
}
}
