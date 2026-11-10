//! Why a request was refused, in the words the reference server uses.
//!
//! The handler proves the status. Where one status has several causes, the
//! words come from the document the step left, which the refusing checks
//! did not change. The runtime puts the words in the envelope.

use vstd::prelude::*;

use crate::concrete::{peek, Doc, Obj};
use echod_types::Tags;
#[cfg(verus_keep_ghost)]
use crate::concrete::document::lemma_obj_view;
use echod_types::{Request, Response, TaskState};

use crate::verified::node::str_eq;
use crate::verified::text::text;

#[cfg(verus_keep_ghost)]
use rover_concrete_spec::node::{spec_origin_map, DocV};
#[cfg(verus_keep_ghost)]
use echod_types::AResponse;

verus! {

/// What a status says when nothing more is known of why.
pub open spec fn spec_reason(status: u16) -> Seq<char> {
    if status == 400 { "Bad request"@ }
    else if status == 403 { "Forbidden"@ }
    else if status == 404 { "Not found"@ }
    else if status == 409 { "Conflict"@ }
    else if status == 422 { "Unprocessable"@ }
    else { "Error"@ }
}

pub fn reason(status: u16) -> (r: &'static str)
    ensures
        r@ == spec_reason(status),
{
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
pub open spec fn spec_status_of(r: AResponse) -> u16 {
    match r {
        AResponse::Promise(p) => p.status,
        AResponse::Schedule(c) => c.status,
        AResponse::Status(st) => st.status,
        AResponse::TaskGet(g) => g.status,
        AResponse::TaskClaim(c) => c.status,
        AResponse::TaskFence(f) => f.status,
    }
}

pub fn status_of(r: &Response) -> (s: u16)
    ensures
        s == spec_status_of(r@),
{
    match r {
        Response::Promise(p) => p.status,
        Response::Schedule(c) => c.status,
        Response::Status(st) => st.status,
        Response::TaskGet(g) => g.status,
        Response::TaskClaim(c) => c.status,
        Response::TaskFence(f) => f.status,
    }
}

/// The address the `resonate:target` tag names, if one does: the first
/// such tag.
pub open spec fn spec_target_of(tags: Seq<(String, String)>) -> Option<Seq<char>>
    decreases tags.len(),
{
    if tags.len() == 0 {
        None
    } else if tags[0].0@ == "resonate:target"@ {
        Some(tags[0].1@)
    } else {
        spec_target_of(tags.drop_first())
    }
}

proof fn lemma_target_of_step(tags: Seq<(String, String)>, i: int)
    requires
        0 <= i <= tags.len(),
        forall|j: int| 0 <= j < i ==> (#[trigger] tags[j]).0@ != "resonate:target"@,
    ensures
        spec_target_of(tags) == spec_target_of(tags.skip(i)),
    decreases i,
{
    if i == 0 {
        assert(tags.skip(0) =~= tags);
    } else {
        lemma_target_of_step(tags, i - 1);
        assert(tags.skip(i - 1).drop_first() =~= tags.skip(i));
        assert(tags.skip(i - 1)[0] == tags[i - 1]);
    }
}

pub fn target_of(tags: &Tags) -> (r: Option<String>)
    ensures
        r.deep_view() == spec_target_of(tags@),
{
    let mut i = 0;
    while i < tags.len()
        invariant
            i <= tags.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] tags@[j]).0@ != "resonate:target"@,
        decreases tags.len() - i,
    {
        if str_eq(tags[i].0.as_str(), "resonate:target") {
            proof {
                lemma_target_of_step(tags@, i as int);
                assert(tags@.skip(i as int)[0] == tags@[i as int]);
            }
            return Some(crate::verified::text::copy_string(&tags[i].1));
        }
        i += 1;
    }
    proof {
        lemma_target_of_step(tags@, i as int);
        assert(tags@.skip(i as int).len() == 0);
    }
    None
}

/// `map[id]`, if the document holds it.
pub open spec fn spec_object(
    doc: DocV,
    id: Seq<char>,
) -> Option<rover_concrete_spec::node::ObjV> {
    if spec_origin_map(doc).contains_key(id) { Some(spec_origin_map(doc)[id]) } else { None }
}

fn object(doc: &Doc, id: &String) -> (r: Option<Obj>)
    ensures
        match r {
            Some(o) => spec_object(doc@, id@) == Some(o@),
            None => spec_object(doc@, id@) is None,
        },
{
    peek(doc, id)
}

/// Does any action await a promise the document does not hold?
pub open spec fn spec_any_missing(doc: DocV, actions: Seq<echod_types::PromiseRegisterCallbackReq>) -> bool
    decreases actions.len(),
{
    if actions.len() == 0 {
        false
    } else if spec_object(doc, actions[0].awaited@) is None {
        true
    } else {
        spec_any_missing(doc, actions.drop_first())
    }
}

proof fn lemma_any_missing_step(doc: DocV, actions: Seq<echod_types::PromiseRegisterCallbackReq>, i: int)
    requires
        0 <= i <= actions.len(),
        forall|j: int| 0 <= j < i ==> spec_object(doc, (#[trigger] actions[j]).awaited@) is Some,
    ensures
        spec_any_missing(doc, actions) == spec_any_missing(doc, actions.skip(i)),
    decreases i,
{
    if i == 0 {
        assert(actions.skip(0) =~= actions);
    } else {
        lemma_any_missing_step(doc, actions, i - 1);
        assert(actions.skip(i - 1).drop_first() =~= actions.skip(i));
        assert(actions.skip(i - 1)[0] == actions[i - 1]);
    }
}

fn any_missing(doc: &Doc, actions: &Vec<echod_types::PromiseRegisterCallbackReq>) -> (r: bool)
    ensures
        r == spec_any_missing(doc@, actions@),
{
    let mut i = 0;
    while i < actions.len()
        invariant
            i <= actions.len(),
            forall|j: int| 0 <= j < i ==> spec_object(doc@, (#[trigger] actions@[j]).awaited@) is Some,
        decreases actions.len() - i,
    {
        if object(doc, &actions[i].awaited).is_none() {
            proof {
                lemma_any_missing_step(doc@, actions@, i as int);
                assert(actions@.skip(i as int)[0] == actions@[i as int]);
            }
            return true;
        }
        i += 1;
    }
    proof {
        lemma_any_missing_step(doc@, actions@, i as int);
        assert(actions@.skip(i as int).len() == 0);
    }
    false
}

/// The words for `status` on `kind`, read off the document where the
/// status has several causes.
pub open spec fn spec_reason_for(kind: Seq<char>, req: Request, status: u16, doc: DocV) -> Seq<char> {
    if (kind == "promise.get"@ || kind == "promise.settle"@) && status == 404 {
        "Promise not found"@
    } else if (kind == "promise.register_callback"@ || kind == "promise.register_listener"@) && status == 404 {
        "Awaited promise not found"@
    } else if kind == "promise.register_callback"@ && status == 422 {
        match req {
            Request::PromiseRegisterCallback(c) => match spec_object(doc, c.awaiter@) {
                None => "Awaiter promise not found"@,
                Some(w) => if spec_target_of(w.promise.tags@) is None { "Awaiter promise has no resonate:target tag"@ } else { "Awaited promise is not awaitable"@ },
            },
            _ => "Awaited promise is not awaitable"@,
        }
    } else if kind == "promise.register_listener"@ && status == 422 {
        "Awaited promise is not awaitable"@
    } else if (kind == "task.get"@ || kind == "task.acquire"@ || kind == "task.release"@ || kind == "task.fulfill"@ || kind == "task.suspend"@ || kind == "task.fence"@ || kind == "task.halt"@ || kind == "task.continue"@) && status == 404 {
        "Task not found"@
    } else if kind == "task.create"@ && status == 409 {
        "Already exists"@
    } else if kind == "task.create"@ && status == 422 {
        "The promise does not have a resonate:target tag"@
    } else if kind == "task.acquire"@ && status == 409 {
        match req {
            Request::TaskAcquire(a) => match spec_object(doc, a.id@) {
                Some(o) => match o.task {
                    Some(t) => if t.state == TaskState::Pending { "Version mismatch"@ } else { "Task is not pending"@ },
                    None => "Task is not pending"@,
                },
                None => "Task is not pending"@,
            },
            _ => "Task is not pending"@,
        }
    } else if (kind == "task.release"@ || kind == "task.fulfill"@) && status == 409 {
        "Task version mismatch or invalid state"@
    } else if kind == "task.suspend"@ && status == 409 {
        "Task is not acquired or version mismatch"@
    } else if kind == "task.suspend"@ && status == 422 {
        match req {
            Request::TaskSuspend(q) => if spec_any_missing(doc, q.actions@) { "Awaited promise not found"@ } else { "Awaited promise is not awaitable"@ },
            _ => "Awaited promise is not awaitable"@,
        }
    } else if kind == "task.fence"@ && status == 409 {
        "Version mismatch"@
    } else if kind == "task.halt"@ && status == 409 {
        "Task is fulfilled"@
    } else if kind == "task.continue"@ && status == 409 {
        "Task is not halted"@
    } else if (kind == "schedule.get"@ || kind == "schedule.delete"@) && status == 404 {
        "Schedule not found"@
    } else {
        spec_reason(status)
    }
}

pub fn reason_for(kind: &str, req: &Request, status: u16, doc: &Doc) -> (r: String)
    ensures
        r@ == spec_reason_for(kind@, *req, status, doc@),
{
    let is = |k: &str| -> (b: bool) ensures b == (kind@ == k@) { str_eq(kind, k) };
    let words: &str = if (is("promise.get") || is("promise.settle")) && status == 404 {
        "Promise not found"
    } else if (is("promise.register_callback") || is("promise.register_listener")) && status == 404 {
        "Awaited promise not found"
    } else if is("promise.register_callback") && status == 422 {
        match req {
            Request::PromiseRegisterCallback(c) => match object(doc, &c.awaiter) {
                None => "Awaiter promise not found",
                Some(w) => {
                    proof {
                        lemma_obj_view(&w);
                    }
                    if target_of(&w.promise.tags).is_none() { "Awaiter promise has no resonate:target tag" } else { "Awaited promise is not awaitable" }
                },
            },
            _ => "Awaited promise is not awaitable",
        }
    } else if is("promise.register_listener") && status == 422 {
        "Awaited promise is not awaitable"
    } else if (is("task.get") || is("task.acquire") || is("task.release") || is("task.fulfill") || is("task.suspend") || is("task.fence") || is("task.halt") || is("task.continue")) && status == 404 {
        "Task not found"
    } else if is("task.create") && status == 409 {
        "Already exists"
    } else if is("task.create") && status == 422 {
        "The promise does not have a resonate:target tag"
    } else if is("task.acquire") && status == 409 {
        match req {
            Request::TaskAcquire(a) => match object(doc, &a.id) {
                Some(o) => {
                    proof {
                        lemma_obj_view(&o);
                    }
                    match &o.task {
                        Some(t) => if t.state == TaskState::Pending { "Version mismatch" } else { "Task is not pending" },
                        None => "Task is not pending",
                    }
                },
                None => "Task is not pending",
            },
            _ => "Task is not pending",
        }
    } else if (is("task.release") || is("task.fulfill")) && status == 409 {
        "Task version mismatch or invalid state"
    } else if is("task.suspend") && status == 409 {
        "Task is not acquired or version mismatch"
    } else if is("task.suspend") && status == 422 {
        match req {
            Request::TaskSuspend(q) => if any_missing(doc, &q.actions) { "Awaited promise not found" } else { "Awaited promise is not awaitable" },
            _ => "Awaited promise is not awaitable",
        }
    } else if is("task.fence") && status == 409 {
        "Version mismatch"
    } else if is("task.halt") && status == 409 {
        "Task is fulfilled"
    } else if is("task.continue") && status == 409 {
        "Task is not halted"
    } else if (is("schedule.get") || is("schedule.delete")) && status == 404 {
        "Schedule not found"
    } else {
        reason(status)
    };
    text(words)
}

} // verus!
