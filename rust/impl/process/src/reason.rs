//! Why a request was refused, in the words the reference server uses.
//!
//! The handler proves the status. Where one status has several causes, the
//! words come from the document the step left, which the refusing checks
//! did not change. The runtime puts the words in the envelope.

use echod_concrete::{peek, Doc, Obj};

use crate::verified as rows;

/// What a status says when nothing more is known of why.
pub fn reason(status: u16) -> &'static str {
    match status {
        400 => "Bad request",
        403 => "Forbidden",
        404 => "Not found",
        409 => "Conflict",
        422 => "Unprocessable",
        _ => "Error",
    }
}

/// The status a response carries.
pub fn status_of(r: &rows::Response) -> u16 {
    match r {
        rows::Response::Promise(p) => p.status,
        rows::Response::Schedule(c) => c.status,
        rows::Response::Status(st) => st.status,
        rows::Response::TaskGet(g) => g.status,
        rows::Response::TaskClaim(c) => c.status,
        rows::Response::TaskFence(f) => f.status,
    }
}

fn object(doc: &Doc, id: &str) -> Option<Obj> {
    peek(doc, &id.to_string())
}

/// The address the `resonate:target` tag names, if one does.
pub fn target_of(tags: &rows::Tags) -> Option<&str> {
    tags.iter().find(|(k, _)| k == "resonate:target").map(|(_, v)| v.as_str())
}

pub fn reason_for(kind: &str, req: &rows::Request, status: u16, doc: &Doc) -> String {
    let text = match (kind, status) {
        ("promise.get" | "promise.settle", 404) => "Promise not found",
        ("promise.register_callback" | "promise.register_listener", 404) => "Awaited promise not found",
        ("promise.register_callback", 422) => match req {
            rows::Request::PromiseRegisterCallback(c) => match object(doc, &c.awaiter) {
                None => "Awaiter promise not found",
                Some(w) if target_of(&w.promise.tags).is_none() => "Awaiter promise has no resonate:target tag",
                Some(_) => "Awaited promise is not awaitable",
            },
            _ => "Awaited promise is not awaitable",
        },
        ("promise.register_listener", 422) => "Awaited promise is not awaitable",
        ("task.get" | "task.acquire" | "task.release" | "task.fulfill" | "task.suspend" | "task.fence" | "task.halt" | "task.continue", 404) => "Task not found",
        ("task.create", 409) => "Already exists",
        ("task.create", 422) => "The promise does not have a resonate:target tag",
        ("task.acquire", 409) => match req {
            rows::Request::TaskAcquire(a) => match object(doc, &a.id).and_then(|o| o.task) {
                Some(t) if t.state == rows::TaskState::Pending => "Version mismatch",
                _ => "Task is not pending",
            },
            _ => "Task is not pending",
        },
        ("task.release" | "task.fulfill", 409) => "Task version mismatch or invalid state",
        ("task.suspend", 409) => "Task is not acquired or version mismatch",
        ("task.suspend", 422) => match req {
            rows::Request::TaskSuspend(q) if q.actions.iter().any(|a| object(doc, &a.awaited).is_none()) => "Awaited promise not found",
            _ => "Awaited promise is not awaitable",
        },
        ("task.fence", 409) => "Version mismatch",
        ("task.halt", 409) => "Task is fulfilled",
        ("task.continue", 409) => "Task is not halted",
        ("schedule.get" | "schedule.delete", 404) => "Schedule not found",
        _ => reason(status),
    };
    text.to_string()
}
