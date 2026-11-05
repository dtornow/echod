//! The Resonate server protocol, written in Verus: this is the code the checker
//! runs, and the code the proofs are about. It follows the Lean specification
//! of `resonatehq/resonate` (`spec/spec/02-abstract/{external,internal}.lean`),
//! the whole of it: promises, callbacks, listeners, tasks with their leases,
//! resumes and redispatch, halt and continue, and schedules. It began as a port
//! of the C# specification. A fence that names another origin is refused,
//! as the Lean specification refuses it.
//!
//! How the Lean specification's shape becomes a checker model:
//! - Time is the system's clock, `now`, which the checker keeps and passes to
//!   every step. The spec reads it and never moves it.
//! - The state is the three maps. A read projects: a pending promise past its
//!   deadline is settled at that deadline, and the task of a settled promise
//!   is fulfilled. The deadline step writes that projection back.
//! - A timeout runs one queued occurrence, or one step whose handler changes
//!   something. The handler is the guard. An object offers its deadline, each
//!   callback, each listener, its lease, and its retry; a schedule offers its
//!   next run. Nothing is armed in advance.
//! - The only queue is the occurrence list. A schedule step records one run
//!   and appends that occurrence; a later step creates the promise.
//!   `next_run_at` is `nextCron cron now`, computed in the handler.
//! - A lease timeout offers the task again at `now`. A retry offers it again
//!   at `now + retry_timeout` (Lean's `processLeaseTimeout` and
//!   `processRetryTimeout`). The dial is `ServerConfig::retry_timeout`.
//! - Lean's `nextCron` and `expand` are trusted (`trusted.rs`): the cron
//!   engine of the reference server.
//! - Indefinite failures need no duplicated outcomes: an unanswered call is
//!   already "maybe".
//! - Clock and version arithmetic saturates instead of overflowing.
//! - Not ported: the searches (501 in Lean), `preload`, and `task.poll`.
//! - A heartbeat's tasks share an origin. A promise is awaitable unless it is
//!   internal: a target, `resonate:scope=global`, `resonate:external=true`, or
//!   a timer. A listener or a callback on one that is not is 422.
//!
//! What Verus checks here: no panics and no overflow anywhere, and the
//! properties stated as `ensures` (see `promise_create`). What it trusts:
//! `trusted.rs`. The handlers are the protocol.
//!
//! `external` is the request handlers and `handler`, the match over requests.
//! `internal` is one handler per work item and `process_work`, the match over
//! work. `model` is the process that calls them. Below each handler file's
//! executable code is the same step as a specification (`spec_*`).

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_rover::Sched;

use echod_types::{
    PromiseRecord, PromiseRes, PromiseState, Request, Response, Schedule, ScheduleRes, StatusRes, Tags,
    TaskClaimRes, TaskFenceInnerRes, TaskFenceRes, TaskGetRes, TaskRecord, TaskState, Value,
};

use super::trusted::*;

/// The first value of `key`, which is how a tag list is read.
fn tag<'a>(tags: &'a Tags, key: &str) -> Option<&'a str> {
    tags.iter().find(|(k, _)| k == key).map(|(_, v)| v.as_str())
}

// The tag readers are plain Rust; Verus sees their signatures alone.
verus! {

#[verifier::external_body]
fn has_target(tags: &Tags) -> bool {
    tag(tags, "resonate:target").is_some()
}

#[verifier::external_body]
fn is_timer(tags: &Tags) -> bool {
    tag(tags, "resonate:timer") == Some("true")
}

#[verifier::external_body]
fn is_external_tag(tags: &Tags) -> bool {
    tag(tags, "resonate:external") == Some("true")
}

#[verifier::external_body]
fn is_global(tags: &Tags) -> bool {
    tag(tags, "resonate:scope") == Some("global")
}

/// `resonate:delay`, when it is a number of milliseconds.
#[verifier::external_body]
fn delay_of(tags: &Tags) -> Option<u64> {
    tag(tags, "resonate:delay").and_then(|d| d.parse().ok())
}

} // verus!
#[cfg(verus_keep_ghost)]
use super::view::{
    all_in_origin, distinct, group_views, lift_dispatch, outs_v, sat_add, sends, strs, works,
    Chars, DispatchV, InOutV, InternalV, OutV, PromiseV, ScheduleV, StoreV, TaskV,
};

pub mod external;
pub mod internal;

pub use external::*;
pub use internal::*;

verus! {

pub type Id = String;

pub type Time = u64;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Promise {
    pub state: PromiseState,
    pub value: Value,
    pub param: Value,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    pub tags: Tags,
    /// Awaiter ids to resume when this promise settles.
    pub callbacks: PSet,
    /// Addresses to send an `unblock` to when this promise settles.
    pub listeners: PSet,
}

impl Promise {
    /// Awaitable: Lean's `otype.awaitable`, everything but an internal promise.
    pub fn external(&self) -> bool {
        has_target(&self.tags)
            || is_global(&self.tags)
            || is_external_tag(&self.tags)
            || is_timer(&self.tags)
    }

    /// The promise as a read at `now` sees it. A pending promise past its
    /// deadline is settled at the deadline.
    pub(crate) fn project(&self, now: Time) -> (r: Promise) {
        if self.state == PromiseState::Pending && now >= self.timeout_at {
            let mut q = copy(self);
            q.state = if is_timer(&self.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
            q.settled_at = Some(self.timeout_at);
            q
        } else {
            copy(self)
        }
    }

    pub(crate) fn to_record(&self, id: &Id) -> (r: PromiseRecord)
        ensures
            r.state == self.state,
            r.timeout_at == self.timeout_at,
            r.created_at == self.created_at,
            r.settled_at == self.settled_at,
    {
        PromiseRecord {
            id: id.clone(),
            state: self.state,
            param: self.param.dup(),
            value: self.value.dup(),
            tags: echod_types::clone_tags(&self.tags),
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Task {
    pub state: TaskState,
    pub version: u64,
    pub pid: Option<String>,
    pub ttl: Option<Time>,
    /// When the lease started (or was last extended); its end is `acquired_at + ttl`.
    pub acquired_at: Time,
    /// When a pending task is next offered to a worker (Lean's `retryTimeoutAt`).
    pub retry_timeout_at: Option<Time>,
    /// The awaited promises that settled since the task last ran (Lean's `resumes`).
    pub resumes: Vec<Id>,
}

impl Task {
    fn fulfill(&mut self)

    {
        self.state = TaskState::Fulfilled;
        self.pid = None;
        self.ttl = None;
        self.acquired_at = 0;
        self.retry_timeout_at = None;
        self.resumes = Vec::new();
        proof {
            broadcast use group_views;
        }
    }

    fn acquire(&mut self, version: u64, pid: String, ttl: Time, now: Time)

    {
        self.state = TaskState::Acquired;
        self.version = version;
        self.pid = Some(pid);
        self.ttl = Some(ttl);
        self.acquired_at = now;
        self.retry_timeout_at = None;
        self.resumes = Vec::new();
        proof {
            broadcast use group_views;
        }
    }

    /// Lean's `unlease`: `state`, no lease, next offer at `retry`.
    fn unlease(&mut self, state: TaskState, retry: Option<Time>)

    {
        self.state = state;
        self.pid = None;
        self.ttl = None;
        self.acquired_at = 0;
        self.retry_timeout_at = retry;
    }

    pub fn lease_timeout_at(&self) -> (r: Time)

    {
        match self.ttl {
            Some(ttl) => self.acquired_at.saturating_add(ttl),
            None => self.acquired_at,
        }
    }

    /// The task as its promise reads. A settled promise fulfills the task.
    pub(crate) fn project(&self, promise: &Promise) -> (r: Task) {
        if promise.state != PromiseState::Pending && self.state != TaskState::Fulfilled {
            let mut u = copy(self);
            u.fulfill();
            u
        } else {
            copy(self)
        }
    }

    pub(crate) fn to_record(&self, id: &Id) -> (r: TaskRecord) {
        let resumes: u64 = if self.resumes.len() as u64 > u64::MAX { u64::MAX } else { self.resumes.len() as u64 };
        TaskRecord { id: id.clone(), state: self.state, version: self.version, resumes, ttl: self.ttl, pid: copy(&self.pid) }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Store {
    pub promises: PMap<Promise>,
    pub tasks: PMap<Task>,
    pub schedules: PMap<Schedule>,
}

/// Lean's `newObject`. `at` is when the promise is created: the clock for a
/// request, the occurrence instant for a schedule. A deadline already past
/// `now` is born settled. `runnable` adds the task, offered at `at` or at
/// its delay.
fn new_object(timeout_at: Time, at: Time, now: Time, param: &Value, tags: &Tags, runnable: bool) -> (born: (Promise, Option<Task>))
    ensures
        promise_ok(born.0),
        born.0.timeout_at == timeout_at,
{
    let live_now = timeout_at > now;
    let live_at = timeout_at > at;
    let state = if live_now {
        PromiseState::Pending
    } else if is_timer(tags) {
        PromiseState::Resolved
    } else {
        PromiseState::RejectedTimedout
    };
    let promise = Promise {
        state,
        value: Value::empty(),
        param: param.dup(),
        timeout_at,
        created_at: if live_at { at } else { timeout_at },
        settled_at: if live_now { None } else { Some(timeout_at) },
        tags: echod_types::clone_tags(tags),
        callbacks: PSet::empty(),
        listeners: PSet::empty(),
    };
    let task = if runnable {
        let due = match delay_of(tags) {
            Some(d) => if d > at { d } else { at },
            None => at,
        };
        let task_state = if live_now { TaskState::Pending } else { TaskState::Fulfilled };
        let retry_timeout_at = if live_now { Some(due) } else { None };
        Some(Task { state: task_state, version: 0, pid: None, ttl: None, acquired_at: 0, retry_timeout_at, resumes: Vec::new() })
    } else {
        None
    };
    proof {
        assert(promise.created_at <= timeout_at);
        assert(promise.settled_at == if live_now { None } else { Some(timeout_at) });
        assert(promise_ok(promise));
    }
    (promise, task)
}

fn copy_store(s: &Store) -> (r: Store)
    ensures
        r.promises@ == s.promises@,
        r.tasks@ == s.tasks@,
        r.schedules@ == s.schedules@,
        r@ == s@,
{
    Store { promises: s.promises.copy(), tasks: s.tasks.copy(), schedules: s.schedules.copy() }
}

/// What the server sends on its own.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Dispatch {
    /// A worker should run this task at this version.
    Execute { id: Id, version: u64 },
    /// A listener's promise has settled.
    Unblock { address: String, promise: PromiseRecord },
}

pub(crate) fn promise_res(status: u16, promise: Option<PromiseRecord>) -> Response {
    Response::Promise(PromiseRes { status, promise })
}

pub(crate) fn schedule_res(status: u16, schedule: Option<Schedule>) -> Response {
    Response::Schedule(ScheduleRes { status, schedule })
}

fn status_res(status: u16) -> Response {
    Response::Status(StatusRes { status })
}

pub(crate) fn task_get_res(status: u16, task: Option<TaskRecord>) -> Response {
    Response::TaskGet(TaskGetRes { status, task })
}

fn claim_res(status: u16, task: Option<TaskRecord>, promise: Option<PromiseRecord>) -> Response {
    Response::TaskClaim(TaskClaimRes { status, task, promise })
}

fn fence_res(status: u16, action: Option<TaskFenceInnerRes>) -> Response {
    Response::TaskFence(TaskFenceRes { status, action })
}

/// The reply when a request is shed or the store does not answer. The shape
/// follows the request, and the status is 503.
pub(crate) fn unavailable(request: &Request) -> (response: Response) {
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => {
            promise_res(503, None)
        },
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => schedule_res(503, None),
        Request::ScheduleDelete(_) | Request::TaskRelease(_) | Request::TaskHalt(_)
        | Request::TaskContinue(_) | Request::TaskHeartbeat(_) | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => status_res(503),
        Request::TaskGet(_) => task_get_res(503, None),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => claim_res(503, None, None),
        Request::TaskFulfill(_) => promise_res(503, None),
        Request::TaskFence(_) => fence_res(503, None),
    }
}

// ------------------------------------------------------------------ outcomes

/// One due item. A timeout runs exactly one. The schedule item appends an
/// `Occurrence` to the queue; that is the only work a step starts.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Work {
    PromiseTimeout(Id),
    Callback { awaited: Id, awaiter: Id },
    Listener { awaited: Id, address: String },
    TaskLeaseTimeout(Id),
    TaskRetryTimeout(Id),
    /// Record the run and queue its occurrence. `promise` is the id that
    /// occurrence will create, so the step's footprint can name it.
    ScheduleTimeout { id: Id, promise: Id },
    /// A promise to create as of `at`, queued by the schedule item.
    Occurrence { promise: Id, at: Time, timeout: Time, param: Value, tags: Tags },
}

/// One possible effect of a request: the response, the next state, the work it
/// starts, the dispatches it sends. As `echod_rover::ExternalOutcome`.
pub struct Out {
    pub resp: Response,
    pub next: Store,
    pub work: Vec<Work>,
    pub send: Vec<Dispatch>,
    /// What this outcome does, for coverage. Changes nothing.
    pub marks: Vec<&'static str>,
}

/// The effect of one work item. As `echod_rover::InternalOutcome`. `not_due`
/// means the handler did nothing, so the step is not a timeout choice.
pub struct InOut {
    pub next: Store,
    pub work: Vec<Work>,
    pub send: Vec<Dispatch>,
    pub marks: Vec<&'static str>,
    pub not_due: bool,
}

/// The server's dial: how long a pending task waits before it is offered
/// again (Lean's `ServerConfig.retryTimeout`). A schedule is due at its
/// `next_run_at`.
pub struct ServerConfig {
    pub retry_timeout: Time,
}

fn one(o: Out) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0] == o,
        outs_v(r@) == seq![o@],
{
    let mut v = Vec::new();
    v.push(o);
    proof {
        broadcast use group_views;
    }
    v
}

/// A mark: the name of a branch of the spec, for coverage. Every mark goes
/// through `mk` with a string literal, so a test can list them from this module.
pub(crate) fn mk(name: &'static str) -> &'static str {
    name
}

fn marked(name: &'static str) -> Vec<&'static str> {
    let mut v = Vec::new();
    v.push(name);
    v
}

pub(crate) fn status(resp: Response, mark: &'static str, s: &Store) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0].resp == resp,
        r[0].next.promises@ == s.promises@,
        r[0].next.tasks@ == s.tasks@,
        r[0].next.schedules@ == s.schedules@,

{
    broadcast use group_views;
    one(Out { resp, next: copy_store(s), work: Vec::new(), send: Vec::new(), marks: marked(mark) })
}

pub(crate) fn echo(res: Response, mark: &'static str, s: &Store) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0].resp == res,
        r[0].next.promises@ == s.promises@,
        r[0].next.tasks@ == s.tasks@,
        r[0].next.schedules@ == s.schedules@,

{
    broadcast use group_views;
    one(Out { resp: res, next: copy_store(s), work: Vec::new(), send: Vec::new(), marks: marked(mark) })
}

/// Settles `id` and fulfills its task, if any.
fn settle(s: &mut Store, id: &Id, state: PromiseState, value: &Value, at: Time)

{
    broadcast use group_views;
    let ghost s0 = *s;

    match s.promises.get(id) {
        Some(p) => {
            let mut q = copy(p);
            q.state = state;
            q.value = value.dup();
            q.settled_at = Some(at);
            assert(q@ == (PromiseV { state, value: *value, settled_at: Some(at), ..s0@.promises[id@] }));
            s.promises.insert(id.clone(), q);
            assert(s.promises@ == s0.promises@.insert(id@, q));
            assert(s.promises@.map_values(|p: Promise| p@) == s0.promises@.map_values(|p: Promise| p@).insert(id@, q@));
        },
        None => {},
    }

    assert(s@.tasks == s0@.tasks);
    match s.tasks.get(id) {
        Some(t) => {
            if t.state != TaskState::Fulfilled {
                let mut u = copy(t);
                u.fulfill();
                s.tasks.insert(id.clone(), u);

            }
        },
        None => {},
    }

}

fn contains(ids: &Vec<Id>, id: &Id) -> (r: bool)
    ensures
        r == strs(ids@).contains(id@),
{
    let mut i = 0;
    while i < ids.len()
        invariant
            i <= ids.len(),
            forall|j: int| 0 <= j < i ==> strs(ids@)[j] != id@,
        decreases ids.len() - i,
    {
        if ids[i] == *id {
            assert(strs(ids@)[i as int] == id@);
            return true;
        }
        i += 1;
    }
    false
}

// ------------------------------------------------------------- property 1

/// created_at <= timeout_at, and if settled, created_at <= settled_at <= timeout_at.
pub open spec fn times_ok(created_at: Time, settled_at: Option<Time>, timeout_at: Time) -> bool {
    created_at <= timeout_at && match settled_at {
        Some(t) => created_at <= t && t <= timeout_at,
        None => true,
    }
}

pub open spec fn promise_ok(p: Promise) -> bool {
    times_ok(p.created_at, p.settled_at, p.timeout_at)
}

pub open spec fn server_ok(s: Store) -> bool {
    forall|k: Seq<char>| #[trigger] s.promises@.contains_key(k) ==> promise_ok(s.promises@[k])
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
