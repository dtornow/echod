//! The Resonate server protocol, written in Verus: this is the code the checker
//! runs, and the code the proofs are about. It follows the Lean specification
//! of `resonatehq/resonate` (`spec/spec/02-abstract/{external,internal}.lean`),
//! the whole of it: promises, callbacks, listeners, tasks with their leases,
//! resumes and redispatch, halt and continue, and schedules. It began as a port
//! of the C# specification, and keeps that spec's one
//! liberty: a fence may create a promise in another origin (a detached
//! workflow), which the Lean specification refuses.
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
//! - A task's offers are on a grid anchored at the instant it came to be
//!   pending (Lean's `nextOffer`). The dial is `Resonate::retry_timeout`.
//! - Lean's `nextCron` and `expand` are trusted (`collections.rs`): the cron
//!   engine of the reference server.
//! - Indefinite failures need no duplicated outcomes: an unanswered call is
//!   already "maybe".
//! - Clock and version arithmetic saturates instead of overflowing.
//! - Not ported: the searches (501 in Lean), `preload`, and `task.poll`.
//! - The reference server's wire rules, which the Lean specification leaves to
//!   the protocol layer, are here too, as 400s: a delay needs a target and
//!   ends before the deadline, a task.create's action carries no delay, a
//!   schedule's id has no `:` and its promises a target, a heartbeat's tasks
//!   share an origin.
//!
//! The detached create: a fence whose create targets another origin runs the
//! create first, as a request of its own in that origin, and then the fence's
//! check on the task. A stale fence still leaves the promise created, and
//! answers its 409.
//!
//! What Verus checks here: no panics and no overflow anywhere, and the
//! properties stated as `ensures` (see `promise_create`). What it trusts:
//! `collections.rs`. The handlers are the protocol.
//!
//! `external` is the request handlers. `internal` is one handler per due item.
//! `system` is the match: a request calls `run`, a due item calls `run_work`.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_rover::Sched;

use echod_types::{PromiseRecord, PromiseRes, PromiseState, Response, Schedule, ScheduleRes, StatusRes, Tags, TaskClaimRes, TaskFenceInnerRes, TaskFenceRes, TaskGetRes, TaskRecord, TaskState, Value};

use super::collections::*;

/// The first value of `key`, which is how a tag list is read.
fn tag<'a>(tags: &'a Tags, key: &str) -> Option<&'a str> {
    tags.iter().find(|(k, _)| k == key).map(|(_, v)| v.as_str())
}

fn has_target(tags: &Tags) -> bool {
    tag(tags, "resonate:target").is_some()
}

fn is_timer(tags: &Tags) -> bool {
    tag(tags, "resonate:timer") == Some("true")
}

fn is_external_tag(tags: &Tags) -> bool {
    tag(tags, "resonate:external") == Some("true")
}

/// `resonate:delay`, when it is a number of milliseconds.
fn delay_of(tags: &Tags) -> Option<u64> {
    tag(tags, "resonate:delay").and_then(|d| d.parse().ok())
}
#[cfg(verus_keep_ghost)]
use super::spec::{Chars, DispatchV, InternalV, PromiseV, ServerV, TaskV, all_in_origin, distinct, group_views, outs_v, sat_add, sends, strs, works};


mod external;
mod internal;
mod system;

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
    pub fn external(&self) -> (r: bool)
        ensures
            r == (has_target(&self.tags) || is_external_tag(&self.tags) || is_timer(&self.tags)),

    {
        has_target(&self.tags) || is_external_tag(&self.tags) || is_timer(&self.tags)
    }

    /// Stored state is pending. A read past the deadline is settled; see
    /// `project_promise`.
    pub fn live(&self) -> (r: bool)
        ensures
            r == (self.state == PromiseState::Pending),

    {
        match self.state {
            PromiseState::Pending => true,
            _ => false,
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
    pub retry_at: Option<Time>,
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
        self.retry_at = None;
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
        self.retry_at = None;
        self.resumes = Vec::new();
        proof {
            broadcast use group_views;
        }
    }

    /// Back to pending, to be offered again at `at`.
    fn release(&mut self, at: Time)
        
    {
        self.state = TaskState::Pending;
        self.pid = None;
        self.ttl = None;
        self.acquired_at = 0;
        self.retry_at = Some(at);
    }

    pub fn lease_expires(&self) -> (r: Time)
        
    {
        match self.ttl {
            Some(ttl) => self.acquired_at.saturating_add(ttl),
            None => self.acquired_at,
        }
    }
}

/// The promise as a read at `now` sees it. A pending promise past its deadline
/// is settled at the deadline. Callbacks and listeners stay until their steps.
fn project_promise(p: &Promise, now: Time) -> (r: Promise) {
    if p.state == PromiseState::Pending && now >= p.timeout_at {
        let mut q = copy(p);
        q.state = if is_timer(&p.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
        q.settled_at = Some(p.timeout_at);
        q
    } else {
        copy(p)
    }
}

/// The task as its promise reads. A settled promise fulfills the task.
fn project_task(promise: &Promise, t: &Task) -> (r: Task) {
    if promise.state != PromiseState::Pending && t.state != TaskState::Fulfilled {
        let mut u = copy(t);
        u.fulfill();
        u
    } else {
        copy(t)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Server {
    pub promises: PMap<Promise>,
    pub tasks: PMap<Task>,
    pub schedules: PMap<Schedule>,
}

fn copy_server(s: &Server) -> (r: Server)
    ensures
        r.promises@ == s.promises@,
        r.tasks@ == s.tasks@,
        r.schedules@ == s.schedules@,
        r@ == s@,
{
    Server { promises: s.promises.copy(), tasks: s.tasks.copy(), schedules: s.schedules.copy() }
}

/// What the server sends on its own.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Dispatch {
    /// A worker should run this task at this version.
    Execute { id: Id, version: u64 },
    /// A listener's promise has settled.
    Unblock { address: String, promise: PromiseRecord },
}

fn promise_res(status: u16, promise: Option<PromiseRecord>) -> Response {
    Response::Promise(PromiseRes { status, promise })
}

fn schedule_res(status: u16, schedule: Option<Schedule>) -> Response {
    Response::Schedule(ScheduleRes { status, schedule })
}

fn status_res(status: u16) -> Response {
    Response::Status(StatusRes { status })
}

fn task_get_res(status: u16, task: Option<TaskRecord>) -> Response {
    Response::TaskGet(TaskGetRes { status, task })
}

fn claim_res(status: u16, task: Option<TaskRecord>, promise: Option<PromiseRecord>) -> Response {
    Response::TaskClaim(TaskClaimRes { status, task, promise })
}

fn fence_res(status: u16, action: Option<TaskFenceInnerRes>) -> Response {
    Response::TaskFence(TaskFenceRes { status, action })
}

fn prec(id: &Id, p: &Promise) -> (r: PromiseRecord)
    ensures
        r.state == p.state,
        r.timeout_at == p.timeout_at,
        r.created_at == p.created_at,
        r.settled_at == p.settled_at,

{
    PromiseRecord {
        id: id.clone(),
        state: p.state,
        param: p.param.dup(),
        value: p.value.dup(),
        tags: echod_types::clone_tags(&p.tags),
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    }
}

fn trec(id: &Id, t: &Task) -> (r: TaskRecord)
    
{
    let resumes: u64 = if t.resumes.len() as u64 > u64::MAX { u64::MAX } else { t.resumes.len() as u64 };
    TaskRecord { id: id.clone(), state: t.state, version: t.version, resumes, ttl: t.ttl, pid: copy(&t.pid) }
}

// ------------------------------------------------------------------ outcomes

/// One due item. A timeout runs exactly one. The schedule item appends an
/// `Occurrence` to the queue; that is the only work a step starts.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Work {
    PromiseTimeout(Id),
    Callback { awaited: Id, awaiter: Id },
    Listener { awaited: Id, address: String },
    Lease(Id),
    Retry(Id),
    /// Record the run and queue its occurrence. `promise` is the id that
    /// occurrence will create, so the step's footprint can name it.
    Schedule { id: Id, promise: Id },
    /// A promise to create as of `at`, queued by the schedule item.
    Occurrence { promise: Id, at: Time, timeout: Time, param: Value, tags: Tags },
}

/// One possible effect of a request: the response, the next state, the work it
/// starts, the dispatches it sends. As `echod_rover::ExternalOutcome`.
pub struct Out {
    pub resp: Response,
    pub next: Server,
    pub work: Vec<Work>,
    pub send: Vec<Dispatch>,
    /// What this outcome does, for coverage. Changes nothing.
    pub marks: Vec<&'static str>,
}

/// The effect of internal work. As `echod_rover::InternalOutcome`; `pending`
/// says the work cannot run yet (a fire before its instant) and stays as it is.
pub struct InOut {
    pub next: Server,
    pub work: Vec<Work>,
    pub send: Vec<Dispatch>,
    pub marks: Vec<&'static str>,
    pub pending: bool,
}

/// The server's dial: how long a pending task waits before it is offered
/// again (Lean's `ServerConfig.retryTimeout`). A schedule is due at its
/// `next_run_at`. `fire_within` is kept so a caller can still name a sweep
/// bound; the due item does not read it.
pub struct Resonate {
    pub retry_timeout: Time,
    pub fire_within: Time,
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
fn mk(name: &'static str) -> &'static str {
    name
}

fn marked(name: &'static str) -> Vec<&'static str> {
    let mut v = Vec::new();
    v.push(name);
    v
}

fn status(resp: Response, mark: &'static str, s: &Server) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0].resp == resp,
        r[0].next.promises@ == s.promises@,
        r[0].next.tasks@ == s.tasks@,
        r[0].next.schedules@ == s.schedules@,

{
    broadcast use group_views;
    one(Out { resp, next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: marked(mark) })
}

fn echo(res: Response, mark: &'static str, s: &Server) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0].resp == res,
        r[0].next.promises@ == s.promises@,
        r[0].next.tasks@ == s.tasks@,
        r[0].next.schedules@ == s.schedules@,

{
    broadcast use group_views;
    one(Out { resp: res, next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: marked(mark) })
}

/// Lean's `nextOffer`: the first instant on the grid `due + k·T` strictly
/// after `now`. Anchored at `due`, so it does not depend on when the retry
/// step ran; a server late to it re-offers the task once and lands on the
/// same grid. `T = 0` would give `due` itself (and a step forever enabled);
/// the model treats it as 1.
fn next_offer(due: Time, now: Time, t: Time) -> (r: Time)
    
{
    let t = if t == 0 { 1 } else { t };
    if now < due {
        due
    } else {
        let k = (now - due) / t;
        due.saturating_add(t.saturating_mul(k.saturating_add(1)))
    }
}

/// Settles `id` and fulfills its task, if any.
fn settle(s: &mut Server, id: &Id, state: PromiseState, value: &Value, at: Time)
    
{
    broadcast use group_views;
    let ghost s0 = *s;

    match s.promises.get(id) {
        Some(p) => {
            let mut q = copy(p);
            q.state = state;
            q.value = value.dup();
            q.settled_at = Some(at);
            assert(q@ == (PromiseV { state, value: value@, settled_at: Some(at), ..s0@.promises[id@] }));
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

pub open spec fn server_ok(s: Server) -> bool {
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

} // verus!
