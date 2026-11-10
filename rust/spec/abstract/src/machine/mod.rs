//! Mathematical state and transitions of the Resonate abstract protocol.
//! Executable records, stores, and handlers live in `echod-abstract-exec`.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;
use echod_types::{PromiseRecord, PromiseRes, PromiseState, Request, Response, Schedule, ScheduleRes, StatusRes, Tags, TaskClaimRes, TaskFenceInnerRes, TaskFenceRes, TaskGetRes, TaskRecord, TaskState, Value};
use super::trusted::*;
use super::view::*;

pub mod external;
pub mod internal;
pub use external::*;
pub use internal::*;

verus! {

pub type Id = String;
pub type Time = u64;

/// What the service sends on its protocol boundary.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Dispatch {
    Execute { id: Id, version: u64 },
    Unblock { address: String, promise: PromiseRecord },
}

/// Passive configuration read by the transition relation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ServerConfig {
    pub retry_timeout: Time,
}

impl Default for ServerConfig {
    fn default() -> Self { ServerConfig { retry_timeout: 5_000 } }
}

/// 503, shaped like the concrete node's `spec_unavailable`.
pub open spec fn spec_unavailable(request: Request) -> Response {
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => {
            spec_promise_res(503, None)
        },
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => spec_schedule_res(503, None),
        Request::ScheduleDelete(_) | Request::TaskRelease(_) | Request::TaskHalt(_)
        | Request::TaskContinue(_) | Request::TaskHeartbeat(_) | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => spec_status_res(503),
        Request::TaskGet(_) => spec_task_get_res(503, None),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => spec_claim_res(503, None, None),
        Request::TaskFulfill(_) => spec_promise_res(503, None),
        Request::TaskFence(_) => spec_fence_res(503, None),
    }
}

/// Tags are their strings.
pub proof fn lemma_tags_ext(a: Tags, b: Tags)
    requires
        a.deep_view() == b.deep_view(),
    ensures
        a == b,
{
    let av = a@;
    let bv = b@;
    assert(a.deep_view().len() == av.len());
    assert(b.deep_view().len() == bv.len());
    assert forall|i: int| 0 <= i < av.len() implies #[trigger] av[i] == bv[i] by {
        assert(a.deep_view()[i] == av[i].deep_view());
        assert(b.deep_view()[i] == bv[i].deep_view());
        axiom_string_ext(av[i].0, bv[i].0);
        axiom_string_ext(av[i].1, bv[i].1);
    };
    assert(av =~= bv);
    axiom_vec_ext(a, b);
}

/// A value is its view.
pub proof fn lemma_value_ext(a: Value, b: Value)
    requires
        a@ == b@,
    ensures
        a == b,
{
    assert(a@.headers == a.headers.deep_view());
    assert(b@.headers == b.headers.deep_view());
    lemma_tags_ext(a.headers, b.headers);
    match (a.data, b.data) {
        (Some(x), Some(y)) => {
            assert(x@ == y@);
            axiom_string_ext(x, y);
        },
        (None, None) => {},
        _ => {
            assert(false);
        },
    }
}

/// A schedule is its view.
pub proof fn lemma_schedule_ext(a: Schedule, b: Schedule)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_string_ext(a.id, b.id);
    axiom_string_ext(a.cron, b.cron);
    axiom_string_ext(a.promise_id, b.promise_id);
    lemma_value_ext(a.promise_param, b.promise_param);
    lemma_tags_ext(a.promise_tags, b.promise_tags);
}

/// A stored schedule reads back as itself.
pub proof fn lemma_schedule_value(c: Schedule)
    ensures
        spec_schedule_value(super::view::schedule_v(c)) == c,
{
    lemma_string_of(c.id);
    lemma_string_of(c.cron);
    lemma_string_of(c.promise_id);
}

/// A string is the chosen string of its characters.
pub proof fn lemma_string_of(s: String)
    ensures
        spec_string(s@) == s,
{
    reveal(spec_string);
    axiom_string_ext(spec_string(s@), s);
}

// ------------------------------------------------------------- property 1

/// created_at <= timeout_at, and if settled, created_at <= settled_at <= timeout_at.
pub open spec fn times_ok(created_at: Time, settled_at: Option<Time>, timeout_at: Time) -> bool {
    created_at <= timeout_at && match settled_at {
        Some(t) => created_at <= t && t <= timeout_at,
        None => true,
    }
}

/// Every promise record in a response has the property.
pub open spec fn response_ok(r: Response) -> bool {
    match r {
        Response::Promise(p) => match p.promise {
            Some(rec) => times_ok(rec.created_at, rec.settled_at, rec.timeout_at),
            None => true,
        },
        Response::TaskClaim(c) => match c.promise {
            Some(rec) => times_ok(rec.created_at, rec.settled_at, rec.timeout_at),
            None => true,
        },
        Response::TaskFence(f) => match f.action {
            Some(TaskFenceInnerRes::Create(p)) | Some(TaskFenceInnerRes::Settle(p)) => match p.promise {
                Some(rec) => times_ok(rec.created_at, rec.settled_at, rec.timeout_at),
                None => true,
            },
            None => true,
        },
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// Tags, as a specification
// ---------------------------------------------------------------------------

pub open spec fn tag_target() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 't', 'a', 'r', 'g', 'e', 't']
}

pub open spec fn tag_timer() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 't', 'i', 'm', 'e', 'r']
}

pub open spec fn tag_external() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 'e', 'x', 't', 'e', 'r', 'n', 'a', 'l']
}

pub open spec fn tag_scope() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 's', 'c', 'o', 'p', 'e']
}

pub open spec fn tag_global() -> Seq<char> {
    seq!['g', 'l', 'o', 'b', 'a', 'l']
}

pub open spec fn tag_delay() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 'd', 'e', 'l', 'a', 'y']
}

pub open spec fn tag_true() -> Seq<char> {
    seq!['t', 'r', 'u', 'e']
}

pub open spec fn spec_first(tags: echod_types::Tags, key: Seq<char>, i: int) -> Option<Seq<char>>
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() {
        None
    } else if tags@[i].0@ == key {
        Some(tags@[i].1@)
    } else {
        spec_first(tags, key, i + 1)
    }
}

pub open spec fn spec_has_key(tags: echod_types::Tags, key: Seq<char>) -> bool {
    spec_first(tags, key, 0) is Some
}

pub open spec fn spec_is_timer(tags: echod_types::Tags) -> bool {
    spec_first(tags, tag_timer(), 0) == Some(tag_true())
}

pub open spec fn spec_is_external_tag(tags: echod_types::Tags) -> bool {
    spec_first(tags, tag_external(), 0) == Some(tag_true())
}

pub open spec fn spec_has_target(tags: echod_types::Tags) -> bool {
    spec_has_key(tags, tag_target())
}

pub open spec fn spec_parse_acc(s: Seq<char>, acc: u64) -> Option<u64>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(acc)
    } else if s[0] < '0' || s[0] > '9' {
        None
    } else {
        let d = (s[0] as u64) - ('0' as u64);
        if acc > (u64::MAX - d) / 10 {
            None
        } else {
            spec_parse_acc(s.drop_first(), (acc * 10 + d) as u64)
        }
    }
}

pub open spec fn spec_parse_u64(s: Seq<char>) -> Option<u64> {
    if s.len() == 0 {
        None
    } else {
        spec_parse_acc(s, 0)
    }
}

pub open spec fn spec_delay(tags: echod_types::Tags) -> Option<u64> {
    match spec_first(tags, tag_delay(), 0) {
        Some(text) => spec_parse_u64(text),
        None => None,
    }
}

pub open spec fn spec_is_global(tags: echod_types::Tags) -> bool {
    spec_first(tags, tag_scope(), 0) == Some(tag_global())
}

pub open spec fn spec_external(p: PromiseV) -> bool {
    spec_has_target(p.tags) || spec_is_global(p.tags) || spec_is_external_tag(p.tags) || spec_is_timer(p.tags)
}

/// Opaque: the choice is read through the string lemmas alone.
#[verifier::opaque]
pub open spec fn spec_string(chars: Seq<char>) -> String {
    choose|s: String| s@ == chars
}

pub open spec fn spec_opt_string(o: Option<Seq<char>>) -> Option<String> {
    match o {
        Some(s) => Some(spec_string(s)),
        None => None,
    }
}

pub open spec fn spec_empty_value() -> Value {
    Value::spec_empty()
}

// ---------------------------------------------------------------------------
// Records, as a specification
// ---------------------------------------------------------------------------

pub open spec fn spec_project_promise(p: PromiseV, now: Time) -> PromiseV {
    if p.state == PromiseState::Pending && now >= p.timeout_at {
        PromiseV {
            state: if spec_is_timer(p.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
            settled_at: Some(p.timeout_at),
            ..p
        }
    } else {
        p
    }
}

pub open spec fn spec_fulfill(t: TaskV) -> TaskV {
    TaskV {
        state: TaskState::Fulfilled,
        pid: None,
        ttl: None,
        acquired_at: 0,
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_project_task(t: TaskV, promise: PromiseV) -> TaskV {
    if promise.state != PromiseState::Pending && t.state != TaskState::Fulfilled {
        spec_fulfill(t)
    } else {
        t
    }
}

pub open spec fn spec_acquire(t: TaskV, version: u64, pid: Seq<char>, ttl: Time, now: Time) -> TaskV {
    TaskV {
        state: TaskState::Acquired,
        version,
        pid: Some(pid),
        ttl: Some(ttl),
        acquired_at: now,
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_unlease(t: TaskV, state: TaskState, retry: Option<Time>) -> TaskV {
    TaskV {
        state,
        pid: None,
        ttl: None,
        acquired_at: 0,
        retry_timeout_at: retry,
        ..t
    }
}

pub open spec fn spec_lease_at(t: TaskV) -> Time {
    match t.ttl {
        Some(ttl) => sat_add(t.acquired_at, ttl),
        None => t.acquired_at,
    }
}

pub open spec fn spec_resumes(n: nat) -> u64 {
    if n > u64::MAX as nat { u64::MAX } else { n as u64 }
}

pub open spec fn spec_promise_record(id: String, p: PromiseV) -> PromiseRecord {
    PromiseRecord {
        id,
        state: p.state,
        param: p.param,
        value: p.value,
        tags: p.tags,
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    }
}

pub open spec fn spec_task_record(id: String, t: TaskV) -> TaskRecord {
    TaskRecord {
        id,
        state: t.state,
        version: t.version,
        resumes: spec_resumes(t.resumes.len()),
        ttl: t.ttl,
        pid: spec_opt_string(t.pid),
    }
}

pub open spec fn spec_schedule_value(c: ScheduleV) -> Schedule {
    Schedule {
        id: spec_string(c.id),
        cron: spec_string(c.cron),
        promise_id: spec_string(c.promise_id),
        promise_timeout: c.promise_timeout,
        promise_param: c.promise_param,
        promise_tags: c.promise_tags,
        next_run_at: c.next_run_at,
        last_run_at: c.last_run_at,
        created_at: c.created_at,
    }
}

/// Lean's `newObject`. `at` is the birth instant, `now` is the clock.
pub open spec fn spec_new_object(
    timeout_at: Time,
    at: Time,
    now: Time,
    param: Value,
    tags: echod_types::Tags,
    runnable: bool,
) -> (PromiseV, Option<TaskV>) {
    let live_now = timeout_at > now;
    let live_at = timeout_at > at;
    let state = if live_now {
        PromiseState::Pending
    } else if spec_is_timer(tags) {
        PromiseState::Resolved
    } else {
        PromiseState::RejectedTimedout
    };
    let promise = PromiseV {
        state,
        value: spec_empty_value(),
        param,
        timeout_at,
        created_at: if live_at { at } else { timeout_at },
        settled_at: if live_now { None } else { Some(timeout_at) },
        tags,
        callbacks: Set::empty(),
        listeners: Set::empty(),
    };
    let due = match spec_delay(tags) {
        Some(d) => if d > at { d } else { at },
        None => at,
    };
    let task = if runnable {
        Some(TaskV {
            state: if live_now { TaskState::Pending } else { TaskState::Fulfilled },
            version: 0,
            pid: None,
            ttl: None,
            acquired_at: 0,
            retry_timeout_at: if live_now { Some(due) } else { None },
            resumes: Seq::empty(),
        })
    } else {
        None
    };
    (promise, task)
}

pub open spec fn spec_settle(
    s: StoreV,
    id: Seq<char>,
    state: PromiseState,
    value: Value,
    at: Time,
) -> StoreV {
    if !s.promises.contains_key(id) {
        s
    } else {
        let q = PromiseV { state, value, settled_at: Some(at), ..s.promises[id] };
        let tasks = if s.tasks.contains_key(id) && s.tasks[id].state != TaskState::Fulfilled {
            s.tasks.insert(id, spec_fulfill(s.tasks[id]))
        } else {
            s.tasks
        };
        StoreV { promises: s.promises.insert(id, q), tasks, ..s }
    }
}

pub open spec fn spec_out(resp: Response, next: StoreV) -> Seq<OutV> {
    seq![OutV { resp, next, work: Seq::empty(), send: Seq::empty() }]
}

pub open spec fn spec_promise_res(status: u16, promise: Option<PromiseRecord>) -> Response {
    Response::Promise(PromiseRes { status, promise })
}

pub open spec fn spec_schedule_res(status: u16, schedule: Option<Schedule>) -> Response {
    Response::Schedule(ScheduleRes { status, schedule })
}

pub open spec fn spec_status_res(status: u16) -> Response {
    Response::Status(StatusRes { status })
}

pub open spec fn spec_task_get_res(status: u16, task: Option<TaskRecord>) -> Response {
    Response::TaskGet(TaskGetRes { status, task })
}

pub open spec fn spec_claim_res(status: u16, task: Option<TaskRecord>, promise: Option<PromiseRecord>) -> Response {
    Response::TaskClaim(TaskClaimRes { status, task, promise })
}

pub open spec fn spec_fence_res(status: u16, action: Option<TaskFenceInnerRes>) -> Response {
    Response::TaskFence(TaskFenceRes { status, action })
}


} // verus!
