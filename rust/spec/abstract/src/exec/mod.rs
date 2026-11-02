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
//! - Lean projects a promise past its deadline on every read. Here the deadline
//!   is a timer step that settles it, so a pending promise is always live and
//!   there is no projection. The two agree on everything a client can see.
//! - Lean projects a promise past its deadline on every read, and a lease past
//!   its end (`TaskObject.lapse`): the task is pending again. Here both are
//!   timer steps at the instant, so a pending promise is always live and an
//!   acquired task always holds its lease, and there is no projection. The two
//!   agree on everything a client can see.
//! - Lean's other internal steps are enabled by the state (a callback on a
//!   settled promise, a retry due) and fired by a fair scheduler. Here each is
//!   work the step that enables it starts: a timer at the instant it falls due,
//!   or "later" when it is due at once. A step is "process these objects":
//!   whatever is due on them happens, in the order Lean's steps would be
//!   enabled (a deadline before the resumes it fires, a resume before the
//!   redispatch it arms). What a step writes never depends on when it ran: a
//!   task's offers are on a grid anchored at the instant it came to be pending
//!   (Lean's `nextOffer`), a resume at the awaited promise's settlement.
//! - A schedule's occurrence is a step, not a projection: it creates a
//!   promise, as of the occurrence's instant. Lean's fair scheduler fires it
//!   some time from `nextRunAt` on, so a client may read the schedule not yet
//!   advanced and the occurrence absent. Here the fire is work due at
//!   `nextRunAt` and owed `fire_within` later: "later" work from the instant,
//!   and a timer at the bound. With `fire_within` zero it is a timer at the
//!   instant, exact, and one step, as Lean's `processSchedule` is. A server
//!   that sweeps its schedules every so often is given its sweep as the
//!   bound, and fires in the two commits such a server makes, the occurrence
//!   first and the run recorded after (`Step::Advance`), the second owed by
//!   the same bound: a client may see the occurrence while the schedule still
//!   expects it, which Lean's one step never shows.
//! - The model's two dials: the redispatch cadence
//!   (`ServerConfig.retryTimeout`), `Resonate::retry_timeout`, and
//!   `Resonate::fire_within`.
//! - Lean's `nextCron`, `occurrences` and `expand` are opaque. Here they are
//!   trusted (`collections.rs`): the cron engine of the reference server.
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
//! `external` is the request handlers. `internal` is the timeout handlers:
//! a deadline, a lease, a callback, a retry, listeners, and a schedule's fire.
//! `system` is the match. A request calls `run`. One armed step calls `run_timeout`.

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

    /// Pending and before its deadline. The deadline is a timer that fires first
    /// at its instant, so a pending promise is always live.
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

/// Internal work: the objects a step processes, or a schedule's occurrence.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Step {
    /// Process these objects: whatever is due on them happens.
    Objects(Vec<Id>),
    /// Fire the occurrence of `schedule` at `at`, which creates `promise`
    /// (`expand` of its template), and arm the next.
    Fire { schedule: Id, at: Time, promise: Id },
    /// Record the run at `at` on `schedule`, whose occurrence is `promise`,
    /// and arm the next: the second half of a fire that a sweeping server
    /// commits apart from the first.
    Advance { schedule: Id, at: Time, promise: Id },
}

/// An internal step, as the checker schedules it. `On`: the server processes
/// these objects and does whatever is due on them (a promise past its deadline
/// times out, a task past its lease is reclaimed, a suspended task whose
/// awaited promise settled resumes, a pending task due for a retry is
/// dispatched, a settled promise's listeners are told). What is due is read
/// from the state and the clock, not from the step. `Fire`: a schedule's
/// occurrence; `Advance`: its run recorded, when a sweeping server commits
/// that apart. The ids of `On` are as the step that started it named them:
/// a settled promise before the awaiter it resumes.
///
/// The step names every object it may touch, so its footprint is exact.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Internal {
    On(Vec<Id>),
    Fire { schedule: Id, at: Time, promise: Id },
    Advance { schedule: Id, at: Time, promise: Id },
}

/// Internal work to start, and when it runs. As `echod_rover::Sched`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Work {
    Later(Step),
    Timer(Time, Step),
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

/// The server, with its dials: how long a pending task waits before it is
/// offered to a worker again (Lean's `ServerConfig.retryTimeout`), and how
/// long after a schedule's `nextRunAt` the occurrence is owed. Zero: it fires
/// at the instant. A server that gets to its schedules by a sweep fires within
/// the sweep's period; Lean's fair scheduler, within any bound at all.
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

fn ids1(a: &Id) -> (r: Vec<Id>)
    ensures
        strs(r@) == seq![a@],
{
    broadcast use group_views;
    let mut v = Vec::new();
    v.push(a.clone());
    v
}

fn ids2(a: &Id, b: &Id) -> (r: Vec<Id>)
    ensures
        strs(r@) == seq![a@, b@],
{
    broadcast use group_views;
    let mut v = Vec::new();
    v.push(a.clone());
    v.push(b.clone());
    v
}

/// Work on one object at `at`.
fn at(t: Time, id: &Id) -> (r: Work)
    
{
    Work::Timer(t, Step::Objects(ids1(id)))
}

fn copy_step(s: &Step) -> (r: Step)
    ensures
        r@ == s@,
{
    match s {
        Step::Objects(ids) => Step::Objects(ids.clone()),
        Step::Fire { schedule, at, promise } => Step::Fire { schedule: schedule.clone(), at: *at, promise: promise.clone() },
        Step::Advance { schedule, at, promise } => Step::Advance { schedule: schedule.clone(), at: *at, promise: promise.clone() },
    }
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

/// The work a settled promise starts: one resume per stored callback (the
/// awaited promise and its awaiter), and its listeners' unblocks.
fn settled_work(p: &Promise, awaited: &Id) -> (r: Vec<Work>)
    
{
    broadcast use group_views;
    let awaiters = p.callbacks.to_vec();
    let ghost cs = pset_seq(p.callbacks@);
    assert(strs(awaiters@).len() == awaiters@.len());
    let mut out = Vec::new();
    let mut i = 0;
    while i < awaiters.len()
        invariant
            i <= awaiters.len(),
            strs(awaiters@) == cs,
        decreases awaiters.len() - i,
    {
        let ghost before = works(out@);
        let w = Work::Later(Step::Objects(ids2(awaited, &awaiters[i])));

        out.push(w);
        proof {
            assert(works(out@) == before.push(w@));
            assert(cs.take(i + 1) =~= cs.take(i as int).push(cs[i as int]));

        }
        i += 1;
    }
    proof {
        assert(cs.take(awaiters.len() as int) =~= cs);
    }
    let ls = p.listeners.to_vec();
    assert(strs(ls@).len() == ls@.len());
    if ls.len() > 0 {
        out.push(Work::Later(Step::Objects(ids1(awaited))));
    }
    out
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

fn push_all(out: &mut Vec<Work>, more: &Vec<Work>)
    ensures
        works(final(out)@) == works(old(out)@) + works(more@),
{
    broadcast use group_views;
    let mut j = 0;
    while j < more.len()
        invariant
            j <= more.len(),
            works(out@) == works(old(out)@) + works(more@).take(j as int),
        decreases more.len() - j,
    {
        let ghost before = works(out@);
        let w = copy(&more[j]);
        out.push(w);
        proof {
            assert(works(out@) == before.push(w@));
            assert(works(more@).take(j + 1) =~= works(more@).take(j as int).push(more@[j as int]@));
        }
        j += 1;
    }
    proof {
        assert(works(more@).take(more.len() as int) =~= works(more@));
    }
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
