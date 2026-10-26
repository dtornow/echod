//! The Resonate server protocol, written in Verus: this is the code the checker
//! runs, and the code the proofs are about. It follows the Lean specification
//! of `resonatehq/resonate` (`spec/spec/02-abstract/{external,internal}.lean`),
//! the whole of it: promises, callbacks, listeners, tasks with their leases,
//! resumes and redispatch, halt and continue, and schedules. It began as a port
//! of the C# spec (resonatehq/resonate-accordant), and keeps that spec's one
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
//! `collections.rs`.

use vstd::prelude::*;

use crate::collections::*;
use crate::spec::MAX_VERSION;

verus! {

pub type Id = String;

pub type Time = u64;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum PState {
    Pending,
    Resolved,
    Rejected,
    Canceled,
    TimedOut,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum TState {
    Pending,
    Acquired,
    Suspended,
    Halted,
    Fulfilled,
}

/// The tags a promise carries, as the protocol reads them: `resonate:target`
/// (a task runs it), `resonate:external` or `resonate:scope: global` (awaitable
/// from outside), `resonate:timer` (resolves at its deadline), `resonate:delay`
/// (its task is first dispatched no earlier than this).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Tags {
    pub target: bool,
    pub external: bool,
    pub timer: bool,
    pub delay: Option<Time>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Promise {
    pub state: PState,
    pub value: Option<String>,
    pub param: Option<String>,
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
            r == (self.tags.target || self.tags.external || self.tags.timer),
    {
        self.tags.target || self.tags.external || self.tags.timer
    }

    /// Pending and before its deadline. The deadline is a timer that fires first
    /// at its instant, so a pending promise is always live.
    pub fn live(&self) -> (r: bool)
        ensures
            r == (self.state == PState::Pending),
    {
        match self.state {
            PState::Pending => true,
            _ => false,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Task {
    pub state: TState,
    pub version: u32,
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
    fn fulfill(&mut self) {
        self.state = TState::Fulfilled;
        self.pid = None;
        self.ttl = None;
        self.acquired_at = 0;
        self.retry_at = None;
        self.resumes = Vec::new();
    }

    fn acquire(&mut self, version: u32, pid: String, ttl: Time, now: Time) {
        self.state = TState::Acquired;
        self.version = version;
        self.pid = Some(pid);
        self.ttl = Some(ttl);
        self.acquired_at = now;
        self.retry_at = None;
        self.resumes = Vec::new();
    }

    /// Back to pending, to be offered again at `at`.
    fn release(&mut self, at: Time) {
        self.state = TState::Pending;
        self.pid = None;
        self.ttl = None;
        self.acquired_at = 0;
        self.retry_at = Some(at);
    }

    pub fn lease_expires(&self) -> Time {
        match self.ttl {
            Some(ttl) => self.acquired_at.saturating_add(ttl),
            None => self.acquired_at,
        }
    }
}

/// A schedule: a cron, and the promise each occurrence creates. Also its own
/// record in a response.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Schedule {
    pub id: Id,
    pub cron: String,
    /// A template for the occurrence's promise id: `{{.id}}` is the schedule's
    /// id, `{{.timestamp}}` the occurrence's instant.
    pub promise_id: String,
    pub promise_timeout: Time,
    pub promise_param: Option<String>,
    pub promise_tags: Tags,
    pub created_at: Time,
    pub next_run_at: Time,
    pub last_run_at: Option<Time>,
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
{
    Server { promises: s.promises.copy(), tasks: s.tasks.copy(), schedules: s.schedules.copy() }
}

// ---------------------------------------------------------------- requests

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Create {
    pub id: Id,
    pub timeout_at: Time,
    pub data: Option<String>,
    pub tags: Tags,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Settle {
    pub id: Id,
    pub state: String,
    pub data: Option<String>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Fenced {
    Create(Create),
    Settle(Settle),
}

impl Fenced {
    pub fn target(&self) -> &Id {
        match self {
            Fenced::Create(c) => &c.id,
            Fenced::Settle(s) => &s.id,
        }
    }
}

/// A task a heartbeat keeps: its id and the version the worker holds.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct TaskRef {
    pub id: Id,
    pub version: u32,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ScheduleCreate {
    pub id: Id,
    pub cron: String,
    pub promise_id: String,
    pub promise_timeout: Time,
    pub promise_param: Option<String>,
    pub promise_tags: Tags,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Request {
    CreatePromise(Create),
    GetPromise(Id),
    SettlePromise(Settle),
    RegisterCallback { awaited: Id, awaiter: Id },
    RegisterListener { awaited: Id, address: String },
    GetTask(Id),
    /// Create a promise and acquire its task in one step: the caller runs it.
    CreateTask { pid: String, ttl: Time, action: Create },
    AcquireTask { id: Id, version: u32, pid: String, ttl: Time },
    ReleaseTask { id: Id, version: u32 },
    FulfillTask { id: Id, version: u32, state: String, data: Option<String> },
    HeartbeatTask { pid: String, tasks: Vec<TaskRef> },
    SuspendTask { id: Id, version: u32, awaited: Vec<Id> },
    FenceTask { id: Id, version: u32, action: Fenced },
    HaltTask(Id),
    ContinueTask(Id),
    CreateSchedule(ScheduleCreate),
    GetSchedule(Id),
    DeleteSchedule(Id),
}

// --------------------------------------------------------------- responses

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct PromiseRec {
    pub id: Id,
    pub state: PState,
    pub param: Option<String>,
    pub value: Option<String>,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    pub tags: Tags,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct TaskRec {
    pub id: Id,
    pub state: TState,
    pub version: u32,
    pub pid: Option<String>,
    pub ttl: Option<Time>,
    /// How many awaited promises settled since the task last ran.
    pub resumes: u32,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Response {
    /// A status with no body we check.
    Status(u16),
    Promise(PromiseRec),
    Task(TaskRec),
    /// `task.create` and `task.acquire`: the promise and the task.
    Both(PromiseRec, TaskRec),
    Schedule(Schedule),
}

/// What the server sends on its own.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Dispatch {
    /// A worker should run this task at this version.
    Execute { id: Id, version: u32 },
    /// A listener's promise has settled.
    Unblock { address: String, promise: PromiseRec },
}

impl Response {
    pub fn status(&self) -> u16 {
        match self {
            Response::Status(s) => *s,
            _ => 200,
        }
    }
}

fn prec(id: &Id, p: &Promise) -> (r: PromiseRec)
    ensures
        r.state == p.state,
        r.timeout_at == p.timeout_at,
        r.created_at == p.created_at,
        r.settled_at == p.settled_at,
{
    PromiseRec {
        id: id.clone(),
        state: p.state,
        param: copy(&p.param),
        value: copy(&p.value),
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
        tags: p.tags,
    }
}

fn trec(id: &Id, t: &Task) -> TaskRec {
    let resumes: u32 = if t.resumes.len() > u32::MAX as usize { u32::MAX } else { t.resumes.len() as u32 };
    TaskRec { id: id.clone(), state: t.state, version: t.version, pid: copy(&t.pid), ttl: t.ttl, resumes }
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
/// that apart. The ids of `On` are sorted and distinct, so two steps on the
/// same objects are the same step.
///
/// The step names every object it may touch, so its footprint is exact.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Internal {
    On(Vec<Id>),
    Fire { schedule: Id, at: Time, promise: Id },
    Advance { schedule: Id, at: Time, promise: Id },
}

/// Internal work to start, and when it runs. As `accordant::Sched`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Work {
    Later(Step),
    Timer(Time, Step),
}

/// One possible effect of a request: the response, the next state, the work it
/// starts, the dispatches it sends. As `accordant::ExternalOutcome`.
pub struct Out {
    pub resp: Response,
    pub next: Server,
    pub work: Vec<Work>,
    pub send: Vec<Dispatch>,
    /// What this outcome does, for coverage. Changes nothing.
    pub marks: Vec<&'static str>,
}

/// The effect of internal work. As `accordant::InternalOutcome`; `pending`
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
{
    let mut v = Vec::new();
    v.push(o);
    v
}

/// A mark: the name of a branch of the spec, for coverage. Every mark goes
/// through `mk` with a string literal, so a test can list them from this file.
fn mk(name: &'static str) -> &'static str {
    name
}

fn marked(name: &'static str) -> Vec<&'static str> {
    let mut v = Vec::new();
    v.push(name);
    v
}

fn status(code: u16, mark: &'static str, s: &Server) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0].resp == Response::Status(code),
        r[0].next.promises@ == s.promises@,
        r[0].next.tasks@ == s.tasks@,
        r[0].next.schedules@ == s.schedules@,
{
    one(Out { resp: Response::Status(code), next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: marked(mark) })
}

fn echo(res: Response, mark: &'static str, s: &Server) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0].resp == res,
        r[0].next.promises@ == s.promises@,
        r[0].next.tasks@ == s.tasks@,
        r[0].next.schedules@ == s.schedules@,
{
    one(Out { resp: res, next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: marked(mark) })
}

fn ids1(a: &Id) -> Vec<Id> {
    let mut v = Vec::new();
    v.push(a.clone());
    v
}

fn ids2(a: &Id, b: &Id) -> Vec<Id> {
    let mut v = Vec::new();
    v.push(a.clone());
    v.push(b.clone());
    v
}

/// Work on one object at `at`.
fn at(t: Time, id: &Id) -> Work {
    Work::Timer(t, Step::Objects(ids1(id)))
}

fn copy_step(s: &Step) -> Step {
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
fn next_offer(due: Time, now: Time, t: Time) -> Time {
    let t = if t == 0 { 1 } else { t };
    if now < due {
        due
    } else {
        let k = (now - due) / t;
        due.saturating_add(t.saturating_mul(k.saturating_add(1)))
    }
}

/// Settles `id` and fulfills its task, if any.
fn settle(s: &mut Server, id: &Id, state: PState, value: Option<String>, at: Time) {
    match s.promises.get(id) {
        Some(p) => {
            let mut q = copy(p);
            q.state = state;
            q.value = value;
            q.settled_at = Some(at);
            s.promises.insert(id.clone(), q);
        },
        None => {},
    }
    match s.tasks.get(id) {
        Some(t) => {
            if t.state != TState::Fulfilled {
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
fn settled_work(p: &Promise, awaited: &Id) -> Vec<Work> {
    let awaiters = p.callbacks.to_vec();
    let mut out = Vec::new();
    let mut i = 0;
    while i < awaiters.len()
        invariant
            i <= awaiters.len(),
        decreases awaiters.len() - i,
    {
        out.push(Work::Later(Step::Objects(ids2(awaited, &awaiters[i]))));
        i += 1;
    }
    if p.listeners.to_vec().len() > 0 {
        out.push(Work::Later(Step::Objects(ids1(awaited))));
    }
    out
}

fn contains(ids: &Vec<Id>, id: &Id) -> bool {
    let mut i = 0;
    while i < ids.len()
        invariant
            i <= ids.len(),
        decreases ids.len() - i,
    {
        if ids[i] == *id {
            return true;
        }
        i += 1;
    }
    false
}

fn push_all(out: &mut Vec<Work>, more: &Vec<Work>) {
    let mut j = 0;
    while j < more.len()
        invariant
            j <= more.len(),
        decreases more.len() - j,
    {
        out.push(more[j].clone());
        j += 1;
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
        Response::Promise(p) => times_ok(p.created_at, p.settled_at, p.timeout_at),
        Response::Both(p, _) => times_ok(p.created_at, p.settled_at, p.timeout_at),
        _ => true,
    }
}

// --------------------------------------------------------------- handlers

impl Resonate {
    /// Property 1: every promise `promise_create` creates has it, every
    /// response has it if the state had it, and every promise that had it keeps it.
    ///
    /// Frame: it touches only the promise and task it creates. Every other
    /// promise and task is as it was, schedules are as they were, and an
    /// existing id changes nothing.
    ///
    /// `fenced`: the create is a fence's action (for the marks). `now` is the
    /// instant the promise is created at: the clock, or an occurrence's instant
    /// for a schedule's fire.
    pub fn promise_create(&self, req: &Create, fenced: bool, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            forall|i: int|
                0 <= i < outs.len() ==> {
                    &&& (server_ok(*s) ==> server_ok(#[trigger] outs[i].next))
                    &&& (server_ok(*s) ==> response_ok(outs[i].resp))
                    &&& (!s.promises@.contains_key(req.id@) && outs[i].next.promises@.contains_key(req.id@)
                        ==> promise_ok(outs[i].next.promises@[req.id@]))
                    // the frame
                    &&& outs[i].next.promises@.remove(req.id@) == s.promises@.remove(req.id@)
                    &&& outs[i].next.tasks@.remove(req.id@) == s.tasks@.remove(req.id@)
                    &&& outs[i].next.schedules@ == s.schedules@
                    &&& (s.promises@.contains_key(req.id@) ==> outs[i].next.promises@ == s.promises@
                        && outs[i].next.tasks@ == s.tasks@)
                },
    {
        if req.tags.timer && req.tags.target {
            return status(400, mk("create: timer with target (400)"), s);
        }
        match req.tags.delay {
            Some(d) => {
                if d >= req.timeout_at {
                    return status(400, mk("create: delay past the deadline (400)"), s);
                }
                if !req.tags.target {
                    return status(400, mk("create: delay without a target (400)"), s);
                }
            },
            None => {},
        }
        match s.promises.get(&req.id) {
            Some(p) => {
                proof {
                    if server_ok(*s) {
                        assert(promise_ok(s.promises@[req.id@]));
                    }
                }
                return echo(Response::Promise(prec(&req.id, p)), mk("create: id exists (echo)"), s);
            },
            None => {},
        }
        let live = req.timeout_at > now;
        let born = if live {
            PState::Pending
        } else if req.tags.timer {
            PState::Resolved
        } else {
            PState::TimedOut
        };
        let p = Promise {
            state: born,
            value: None,
            param: copy(&req.data),
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: req.tags,
            callbacks: PSet::empty(),
            listeners: PSet::empty(),
        };
        let rec = prec(&req.id, &p);
        let mut n = copy_server(s);
        n.promises.insert(req.id.clone(), p);
        let mut work = Vec::new();
        if live {
            work.push(at(req.timeout_at, &req.id));
        }
        if req.tags.target {
            // A live targeted promise's task is runnable: offered to a worker
            // at once, or at its delay.
            let due = match req.tags.delay {
                Some(d) => if d > now { d } else { now },
                None => now,
            };
            let state = if live { TState::Pending } else { TState::Fulfilled };
            let retry_at = if live { Some(due) } else { None };
            let task = Task { state, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at, resumes: Vec::new() };
            n.tasks.insert(req.id.clone(), task);
            if live {
                work.push(at(due, &req.id));
            }
        }
        proof {
            if server_ok(*s) {
                assert forall|k: Seq<char>| #[trigger] n.promises@.contains_key(k) implies promise_ok(
                    n.promises@[k],
                ) by {
                    if k != req.id@ {
                        assert(s.promises@.contains_key(k));
                    }
                }
            }
        }
        proof {
            assert(n.promises@.remove(req.id@) =~= s.promises@.remove(req.id@));
            assert(n.tasks@.remove(req.id@) =~= s.tasks@.remove(req.id@));
        }
        let mut marks = Vec::new();
        marks.push(match (fenced, live) {
            (false, true) => mk("promise created"),
            (false, false) => mk("promise created past its deadline"),
            (true, true) => mk("fence: promise created"),
            (true, false) => mk("fence: promise created past its deadline"),
        });
        if live && req.tags.target {
            marks.push(mk("task created pending"));
        }
        one(Out { resp: Response::Promise(rec), next: n, work, send: Vec::new(), marks })
    }

    fn promise_settle(&self, req: &Settle, fenced: bool, s: &Server, now: Time) -> Vec<Out> {
        let state = match settable(&req.state) {
            Some(st) => st,
            None => return status(400, mk("settle: not a settled state (400)"), s),
        };
        let p = match s.promises.get(&req.id) {
            Some(p) => p,
            None => return status(404, mk("settle: no such promise (404)"), s),
        };
        if !p.live() {
            return echo(Response::Promise(prec(&req.id, p)), mk("settle: already settled (echo)"), s);
        }
        let work = settled_work(p, &req.id);
        let mut n = copy_server(s);
        settle(&mut n, &req.id, state, copy(&req.data), now);
        let res = match n.promises.get(&req.id) {
            Some(q) => Response::Promise(prec(&req.id, q)),
            None => Response::Status(500),  // unreachable: the promise exists
        };
        let mut marks = Vec::new();
        marks.push(if fenced { mk("fence: promise settled") } else { mk("promise settled") });
        if work.len() > 0 {
            marks.push(mk("settled with callbacks or listeners"));
        }
        one(Out { resp: res, next: n, work, send: Vec::new(), marks })
    }

    /// The checks every task.* mutation shares: exists, acquired, own promise live,
    /// version matches. `Ok` is the task.
    fn held<'a>(&self, s: &'a Server, id: &Id, version: u32) -> Result<&'a Task, u16> {
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return Err(404),
        };
        let live = match s.promises.get(id) {
            Some(p) => p.live(),
            None => false,  // unreachable: a task's promise exists
        };
        if t.state != TState::Acquired || !live || t.version != version {
            return Err(409);
        }
        Ok(t)
    }

    fn task_create(&self, pid: &String, ttl: Time, req: &Create, s: &Server, now: Time) -> Vec<Out> {
        if !req.tags.target || req.tags.timer {
            return status(400, mk("task.create: not runnable, or a timer (400)"), s);
        }
        match req.tags.delay {
            Some(_) => return status(400, mk("task.create: action with a delay (400)"), s),
            None => {},
        }
        match s.promises.get(&req.id) {
            Some(p) => {
                if !p.tags.target {
                    return status(422, mk("task.create: promise exists, not a target (422)"), s);
                }
                let t = match s.tasks.get(&req.id) {
                    Some(t) => t,
                    None => return status(409, mk("task.create: target without a task (409)"), s),  // unreachable
                };
                return match t.state {
                    TState::Fulfilled => echo(Response::Both(prec(&req.id, p), trec(&req.id, t)), mk("task.create: task done (echo)"), s),
                    TState::Pending => {
                        if t.version >= MAX_VERSION {
                            return status(409, mk("task.create: version at its cap (409)"), s);
                        }
                        let mut n = copy_server(s);
                        let mut u = copy(t);
                        u.acquire(t.version + 1, pid.clone(), ttl, now);
                        let rec = Response::Both(prec(&req.id, p), trec(&req.id, &u));
                        n.tasks.insert(req.id.clone(), u);
                        let mut work = Vec::new();
                        work.push(at(now.saturating_add(ttl), &req.id));
                        one(Out { resp: rec, next: n, work, send: Vec::new(), marks: marked(mk("task.create: pending task acquired")) })
                    },
                    _ => status(409, mk("task.create: task held, suspended or halted (409)"), s),
                };
            },
            None => {},
        }
        let live = req.timeout_at > now;
        let p = Promise {
            state: if live { PState::Pending } else { PState::TimedOut },
            value: None,
            param: copy(&req.data),
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: req.tags,
            callbacks: PSet::empty(),
            listeners: PSet::empty(),
        };
        let mut t = Task { state: TState::Fulfilled, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Vec::new() };
        let mut work = Vec::new();
        if live {
            // Acquired by the caller right away: nothing to dispatch.
            t.acquire(1, pid.clone(), ttl, now);
            work.push(at(req.timeout_at, &req.id));
            work.push(at(now.saturating_add(ttl), &req.id));
        }
        let res = Response::Both(prec(&req.id, &p), trec(&req.id, &t));
        let mut n = copy_server(s);
        n.promises.insert(req.id.clone(), p);
        n.tasks.insert(req.id.clone(), t);
        let mark = if live { mk("task created") } else { mk("task created past its deadline") };
        one(Out { resp: res, next: n, work, send: Vec::new(), marks: marked(mark) })
    }

    fn task_suspend(&self, id: &Id, version: u32, ids: &Vec<Id>, s: &Server) -> Vec<Out> {
        if ids.len() == 0 || contains(ids, id) {
            return status(400, mk("suspend: no awaited, or itself (400)"), s);
        }
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
            decreases ids.len() - i,
        {
            let mut j = i + 1;
            while j < ids.len()
                invariant
                    i < j <= ids.len(),
                decreases ids.len() - j,
            {
                if ids[i] == ids[j] {
                    return status(400, mk("suspend: awaited twice (400)"), s);
                }
                j += 1;
            }
            if !same_origin(&ids[i], id) {
                return status(400, mk("suspend: awaited in another origin (400)"), s);
            }
            i += 1;
        }
        let t = match self.held(s, id, version) {
            Err(code) => return status(code, if code == 404 { mk("suspend: no such task (404)") } else { mk("suspend: not held (409)") }, s),
            Ok(t) => t,
        };
        let mut settled = false;
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
            decreases ids.len() - i,
        {
            match s.promises.get(&ids[i]) {
                None => return status(422, mk("suspend: awaited missing (422)"), s),
                Some(p) => {
                    if !p.external() {
                        return status(422, mk("suspend: awaited not external (422)"), s);
                    }
                    settled = settled || !p.live();
                },
            }
            i += 1;
        }
        let mut n = copy_server(s);
        let mut u = copy(t);
        if settled {
            // The task stays acquired and runs on; what it was told has been seen.
            u.resumes = Vec::new();
            n.tasks.insert(id.clone(), u);
            return one(Out { resp: Response::Status(300), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("suspend: awaited already settled (300)")) });
        }
        u.state = TState::Suspended;
        u.pid = None;
        u.ttl = None;
        u.acquired_at = 0;
        u.retry_at = None;
        u.resumes = Vec::new();
        n.tasks.insert(id.clone(), u);
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
            decreases ids.len() - i,
        {
            match n.promises.get(&ids[i]) {
                Some(p) => {
                    let mut q = copy(p);
                    q.callbacks.insert(id.clone());
                    n.promises.insert(ids[i].clone(), q);
                },
                None => {},
            }
            i += 1;
        }
        one(Out { resp: Response::Status(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task suspended")) })
    }

    fn task_fence(&self, id: &Id, version: u32, action: &Fenced, s: &Server, now: Time) -> Vec<Out> {
        if *action.target() == *id {
            return status(400, mk("fence: targets its own task (400)"), s);
        }
        // The wire rules on the action come before the fence's check, as the
        // reference server's validators do.
        match action {
            Fenced::Create(c) => match c.tags.delay {
                Some(d) => {
                    if d >= c.timeout_at {
                        return status(400, mk("create: delay past the deadline (400)"), s);
                    }
                    if !c.tags.target {
                        return status(400, mk("create: delay without a target (400)"), s);
                    }
                },
                None => {},
            },
            Fenced::Settle(_) => {},
        }
        match action {
            Fenced::Settle(st) => {
                if !same_origin(&st.id, id) {
                    return status(400, mk("fence: settle in another origin (400)"), s);  // only a create may cross origins
                }
            },
            Fenced::Create(c) => {
                if !same_origin(&c.id, id) {
                    return self.detached_create(id, version, c, s, now);
                }
            },
        }
        match self.held(s, id, version) {
            Err(code) => return status(code, if code == 404 { mk("fence: no such task (404)") } else { mk("fence: not held, or stale version (409)") }, s),
            Ok(_) => {},
        }
        match action {
            Fenced::Create(c) => self.promise_create(c, true, s, now),
            Fenced::Settle(st) => self.promise_settle(st, true, s, now),
        }
    }

    /// A fence that creates a promise in another origin: a detached workflow.
    /// The create goes first, as a request of its own in its origin; then the
    /// fence's check on the task decides the answer. A stale fence still
    /// leaves the promise created.
    fn detached_create(&self, id: &Id, version: u32, c: &Create, s: &Server, now: Time) -> Vec<Out> {
        let mut outs = self.promise_create(c, true, s, now);
        if outs.len() != 1 {
            return outs;  // unreachable: a create has one outcome
        }
        let o = outs.pop().unwrap();
        let mut marks = o.marks;
        match self.held(&o.next, id, version) {
            Err(code) => {
                marks.push(if code == 404 { mk("fence: detached create, no such task (404)") } else { mk("fence: detached create, not held (409)") });
                one(Out { resp: Response::Status(code), next: o.next, work: o.work, send: o.send, marks })
            },
            Ok(_) => {
                marks.push(mk("fence: detached create"));
                one(Out { resp: o.resp, next: o.next, work: o.work, send: o.send, marks })
            },
        }
    }

    fn task_heartbeat(&self, pid: &String, refs: &Vec<TaskRef>, s: &Server, now: Time) -> Vec<Out> {
        let mut i = 1;
        while i < refs.len()
            invariant
                1 <= i,
            decreases refs.len() - i,
        {
            if !same_origin(&refs[i].id, &refs[0].id) {
                return status(400, mk("heartbeat: tasks in several origins (400)"), s);
            }
            i += 1;
        }
        let mut n = copy_server(s);
        let mut work = Vec::new();
        let mut extended = false;
        let mut i = 0;
        while i < refs.len()
            invariant
                i <= refs.len(),
            decreases refs.len() - i,
        {
            let r = &refs[i];
            match self.held(s, &r.id, r.version) {
                Ok(t) => {
                    let mine = match &t.pid {
                        Some(holder) => *holder == *pid,
                        None => false,
                    };
                    if mine {
                        let mut u = copy(t);
                        u.acquired_at = now;
                        let expires = u.lease_expires();
                        n.tasks.insert(r.id.clone(), u);
                        work.push(at(expires, &r.id));
                        extended = true;
                    }
                },
                Err(_) => {},
            }
            i += 1;
        }
        // Always 200: a heartbeat says nothing about what it kept.
        let mark = if extended { mk("lease extended") } else { mk("heartbeat: nothing held by this worker") };
        one(Out { resp: Response::Status(200), next: n, work, send: Vec::new(), marks: marked(mark) })
    }

    fn schedule_create(&self, req: &ScheduleCreate, s: &Server, now: Time) -> Vec<Out> {
        if has_colon(&req.id) {
            return status(400, mk("schedule: id with a colon (400)"), s);
        }
        if !req.promise_tags.target {
            return status(400, mk("schedule: promises without a target (400)"), s);
        }
        if req.promise_tags.timer && req.promise_tags.target {
            return status(400, mk("schedule: timer with target (400)"), s);
        }
        if !cron_valid(&req.cron) {
            return status(400, mk("schedule: invalid cron (400)"), s);
        }
        match s.schedules.get(&req.id) {
            Some(c) => return echo(Response::Schedule(copy(c)), mk("schedule: id exists (echo)"), s),
            None => {},
        }
        let next = next_cron(&req.cron, now);
        let c = Schedule {
            id: req.id.clone(),
            cron: req.cron.clone(),
            promise_id: req.promise_id.clone(),
            promise_timeout: req.promise_timeout,
            promise_param: copy(&req.promise_param),
            promise_tags: req.promise_tags,
            created_at: now,
            next_run_at: next,
            last_run_at: None,
        };
        let rec = Response::Schedule(copy(&c));
        let mut n = copy_server(s);
        n.schedules.insert(req.id.clone(), c);
        let mut work = Vec::new();
        self.arm_fire(&mut work, &req.id, next, &req.promise_id);
        one(Out { resp: rec, next: n, work, send: Vec::new(), marks: marked(mk("schedule created")) })
    }

    /// A request takes effect in `s` at time `now`: every allowed outcome.
    pub fn external(&self, op: &Request, s: &Server, now: Time) -> Vec<Out> {
        match op {
            Request::CreatePromise(c) => self.promise_create(c, false, s, now),
            Request::GetPromise(id) => match s.promises.get(id) {
                None => status(404, mk("get promise: none (404)"), s),
                Some(p) => echo(Response::Promise(prec(id, p)), mk("get promise"), s),
            },
            Request::SettlePromise(st) => self.promise_settle(st, false, s, now),
            Request::RegisterCallback { awaited, awaiter } => {
                if *awaited == *awaiter || !same_origin(awaited, awaiter) {
                    return status(400, mk("callback: itself or another origin (400)"), s);
                }
                let p = match s.promises.get(awaited) {
                    Some(p) => p,
                    None => return status(404, mk("callback: no awaited promise (404)"), s),
                };
                let w = match s.promises.get(awaiter) {
                    Some(w) => w,
                    None => return status(422, mk("callback: no awaiter promise (422)"), s),
                };
                if !s.tasks.contains_key(awaiter) || !p.external() {
                    return status(422, mk("callback: awaiter no task, or awaited not external (422)"), s);
                }
                let res = Response::Promise(prec(awaited, p));
                if !p.live() || !w.live() {
                    return echo(res, mk("callback: one of them settled (echo)"), s);
                }
                let mut n = copy_server(s);
                let mut q = copy(p);
                q.callbacks.insert(awaiter.clone());
                n.promises.insert(awaited.clone(), q);
                one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("callback registered")) })
            },
            Request::RegisterListener { awaited, address } => {
                if !address_valid(address) {
                    return status(400, mk("listener: bad address (400)"), s);
                }
                let p = match s.promises.get(awaited) {
                    None => return status(404, mk("listener: no such promise (404)"), s),
                    Some(p) => p,
                };
                if !p.external() {
                    return status(422, mk("listener: promise not external (422)"), s);
                }
                let res = Response::Promise(prec(awaited, p));
                if !p.live() {
                    return echo(res, mk("listener: promise settled (echo)"), s);
                }
                let mut n = copy_server(s);
                let mut q = copy(p);
                q.listeners.insert(address.clone());
                n.promises.insert(awaited.clone(), q);
                one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("listener registered")) })
            },
            Request::GetTask(id) => match s.tasks.get(id) {
                None => status(404, mk("get task: none (404)"), s),
                Some(t) => echo(Response::Task(trec(id, t)), mk("get task"), s),
            },
            Request::CreateTask { pid, ttl, action } => self.task_create(pid, *ttl, action, s, now),
            Request::AcquireTask { id, version, pid, ttl } => {
                let t = match s.tasks.get(id) {
                    Some(t) => t,
                    None => return status(404, mk("acquire: no such task (404)"), s),
                };
                let p = match s.promises.get(id) {
                    Some(p) => p,
                    None => return status(404, mk("acquire: no such task (404)"), s),  // unreachable
                };
                if t.state != TState::Pending || !p.live() || t.version != *version || t.version >= MAX_VERSION {
                    return status(409, mk("acquire: not pending, or stale version (409)"), s);
                }
                let mut n = copy_server(s);
                let mut u = copy(t);
                u.acquire(t.version + 1, pid.clone(), *ttl, now);
                let rec = Response::Both(prec(id, p), trec(id, &u));
                n.tasks.insert(id.clone(), u);
                let mut work = Vec::new();
                work.push(at(now.saturating_add(*ttl), id));
                one(Out { resp: rec, next: n, work, send: Vec::new(), marks: marked(mk("task acquired")) })
            },
            Request::ReleaseTask { id, version } => match self.held(s, id, *version) {
                Err(code) => status(code, if code == 404 { mk("release: no such task (404)") } else { mk("release: not held (409)") }, s),
                Ok(t) => {
                    let mut n = copy_server(s);
                    let mut u = copy(t);
                    u.release(now);
                    n.tasks.insert(id.clone(), u);
                    let mut work = Vec::new();
                    work.push(at(now, id));
                    one(Out { resp: Response::Status(200), next: n, work, send: Vec::new(), marks: marked(mk("task released")) })
                },
            },
            Request::FulfillTask { id, version, state, data } => {
                let st = match settable(state) {
                    Some(st) => st,
                    None => return status(400, mk("fulfill: not a settled state (400)"), s),
                };
                match self.held(s, id, *version) {
                    Err(code) => return status(code, if code == 404 { mk("fulfill: no such task (404)") } else { mk("fulfill: not held (409)") }, s),
                    Ok(_) => {},
                }
                let work = match s.promises.get(id) {
                    Some(p) => settled_work(p, id),
                    None => Vec::new(),
                };
                let mut n = copy_server(s);
                settle(&mut n, id, st, copy(data), now);
                let res = match n.promises.get(id) {
                    Some(q) => Response::Promise(prec(id, q)),
                    None => Response::Status(500),  // unreachable: held checked the promise
                };
                one(Out { resp: res, next: n, work, send: Vec::new(), marks: marked(mk("task fulfilled")) })
            },
            Request::HeartbeatTask { pid, tasks } => self.task_heartbeat(pid, tasks, s, now),
            Request::SuspendTask { id, version, awaited } => self.task_suspend(id, *version, awaited, s),
            Request::FenceTask { id, version, action } => self.task_fence(id, *version, action, s, now),
            Request::HaltTask(id) => {
                let t = match s.tasks.get(id) {
                    Some(t) => t,
                    None => return status(404, mk("halt: no such task (404)"), s),
                };
                match t.state {
                    TState::Fulfilled => status(409, mk("halt: task done (409)"), s),
                    TState::Halted => status(200, mk("halt: already halted (echo)"), s),
                    _ => {
                        let mut n = copy_server(s);
                        let mut u = copy(t);
                        u.state = TState::Halted;
                        u.pid = None;
                        u.ttl = None;
                        u.acquired_at = 0;
                        u.retry_at = None;
                        n.tasks.insert(id.clone(), u);
                        one(Out { resp: Response::Status(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task halted")) })
                    },
                }
            },
            Request::ContinueTask(id) => {
                let t = match s.tasks.get(id) {
                    Some(t) => t,
                    None => return status(404, mk("continue: no such task (404)"), s),
                };
                let live = match s.promises.get(id) {
                    Some(p) => p.live(),
                    None => false,
                };
                if t.state != TState::Halted || !live {
                    return status(409, mk("continue: not halted (409)"), s);
                }
                let mut n = copy_server(s);
                let mut u = copy(t);
                u.state = TState::Pending;
                u.retry_at = Some(now);
                n.tasks.insert(id.clone(), u);
                let mut work = Vec::new();
                work.push(at(now, id));
                one(Out { resp: Response::Status(200), next: n, work, send: Vec::new(), marks: marked(mk("task continued")) })
            },
            Request::CreateSchedule(c) => self.schedule_create(c, s, now),
            Request::GetSchedule(id) => match s.schedules.get(id) {
                None => status(404, mk("get schedule: none (404)"), s),
                Some(c) => echo(Response::Schedule(copy(c)), mk("get schedule"), s),
            },
            Request::DeleteSchedule(id) => match s.schedules.get(id) {
                None => status(404, mk("delete schedule: none (404)"), s),
                Some(_) => {
                    let mut n = copy_server(s);
                    n.schedules.remove(id);
                    one(Out { resp: Response::Status(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("schedule deleted")) })
                },
            },
        }
    }

    /// A suspended task resumes when a promise it awaits has settled; any
    /// other task is told, when it next runs (Lean's `resumeOne`). The
    /// callback is spent either way.
    fn resume(&self, n: &mut Server, awaited: &Id, awaiter: &Id, now: Time, marks: &mut Vec<&'static str>) {
        // the resumed task's first offer: when the awaited settled (Lean's `since`)
        let since = match n.promises.get(awaited) {
            Some(p) => match p.settled_at {
                Some(t) => t,
                None => now,
            },
            None => now,
        };
        match n.promises.get(awaited) {
            Some(p) => {
                let mut q = copy(p);
                q.callbacks.remove(awaiter);
                n.promises.insert(awaited.clone(), q);
            },
            None => {},
        }
        match n.tasks.get(awaiter) {
            Some(t) => {
                match t.state {
                    TState::Suspended => {
                        let mut u = copy(t);
                        u.state = TState::Pending;
                        u.resumes = ids1(awaited);
                        u.retry_at = Some(since);
                        n.tasks.insert(awaiter.clone(), u);
                        marks.push(mk("task resumed"));
                    },
                    TState::Fulfilled => {},
                    _ => {
                        if !contains(&t.resumes, awaited) {
                            let mut u = copy(t);
                            u.resumes.push(awaited.clone());
                            n.tasks.insert(awaiter.clone(), u);
                            marks.push(mk("resume noted on a running task"));
                        }
                    },
                }
            },
            None => {},
        }
    }

    /// Internal work on `ids` runs in `s` at time `now`: whatever is due on
    /// them happens, in the order the Lean specification's steps become
    /// enabled: a promise past its deadline settles; a callback on a settled
    /// promise resumes its awaiter; a lease past its end is reclaimed; a
    /// settled promise's listeners are told; a pending task whose retry is due
    /// is offered to a worker, and the next retry armed.
    pub fn internal(&self, ids: &Vec<Id>, s: &Server, now: Time) -> InOut {
        let mut n = copy_server(s);
        let mut work = Vec::new();
        let mut send = Vec::new();
        let mut marks = Vec::new();
        // A promise past its deadline times out (a timer promise resolves).
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
            decreases ids.len() - i,
        {
            let id = &ids[i];
            match s.promises.get(id) {
                Some(p) => {
                    if p.live() && now >= p.timeout_at {
                        let state = if p.tags.timer { PState::Resolved } else { PState::TimedOut };
                        marks.push(if p.tags.timer { mk("timer promise resolved") } else { mk("promise timed out") });
                        let r = settled_work(p, id);
                        settle(&mut n, id, state, None, p.timeout_at);
                        push_all(&mut work, &r);
                    }
                },
                None => {},
            }
            i += 1;
        }
        // A callback on a settled promise is spent: its awaiter resumes.
        let mut a = 0;
        while a < ids.len()
            invariant
                a <= ids.len(),
            decreases ids.len() - a,
        {
            let mut w = 0;
            while w < ids.len()
                invariant
                    w <= ids.len(),
                    a < ids.len(),
                decreases ids.len() - w,
            {
                let awaited = &ids[a];
                let awaiter = &ids[w];
                let due = match n.promises.get(awaited) {
                    Some(p) => !p.live() && p.callbacks.contains(awaiter),
                    None => false,
                };
                if due {
                    self.resume(&mut n, awaited, awaiter, now, &mut marks);
                }
                w += 1;
            }
            a += 1;
        }
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
            decreases ids.len() - i,
        {
            let id = &ids[i];
            // A task past its lease is reclaimed, offered again from the
            // lease's end on (Lean's `TaskObject.lapse`).
            match n.tasks.get(id) {
                Some(t) => {
                    if t.state == TState::Acquired && now >= t.lease_expires() {
                        let mut u = copy(t);
                        u.release(t.lease_expires());
                        n.tasks.insert(id.clone(), u);
                        marks.push(mk("lease expired"));
                    }
                },
                None => {},
            }
            // A settled promise's listeners are told, once.
            match n.promises.get(id) {
                Some(p) => {
                    if !p.live() {
                        let addrs = p.listeners.to_vec();
                        if addrs.len() > 0 {
                            let rec = prec(id, p);
                            let mut j = 0;
                            while j < addrs.len()
                                invariant
                                    j <= addrs.len(),
                                decreases addrs.len() - j,
                            {
                                send.push(Dispatch::Unblock { address: addrs[j].clone(), promise: rec.clone() });
                                j += 1;
                            }
                            let mut q = copy(p);
                            q.listeners = PSet::empty();
                            n.promises.insert(id.clone(), q);
                            marks.push(mk("listeners told"));
                        }
                    }
                },
                None => {},
            }
            // A pending task whose retry is due is offered to a worker, and
            // the next offer armed. Not once its promise is settled: the task
            // is done.
            let live = match n.promises.get(id) {
                Some(p) => p.live(),
                None => false,
            };
            match n.tasks.get(id) {
                Some(t) => {
                    let due = match t.retry_at {
                        Some(r) => r <= now,
                        None => false,
                    };
                    if t.state == TState::Pending && due && live {
                        let mut u = copy(t);
                        let again = match t.retry_at {
                            Some(r) => next_offer(r, now, self.retry_timeout),
                            None => now.saturating_add(self.retry_timeout),
                        };
                        u.retry_at = Some(again);
                        let version = u.version;
                        n.tasks.insert(id.clone(), u);
                        send.push(Dispatch::Execute { id: id.clone(), version });
                        work.push(at(again, id));
                        marks.push(mk("task dispatched"));
                    }
                },
                None => {},
            }
            i += 1;
        }
        InOut { next: n, work, send, marks, pending: false }
    }

    /// The work that fires `schedule`'s occurrence at `at`: later, from `at`
    /// on, and a timer at `at + fire_within`, by which it is owed. Whichever
    /// runs first fires it; the other finds the schedule moved on and does
    /// nothing. With `fire_within` zero, the timer alone.
    fn arm_fire(&self, work: &mut Vec<Work>, schedule: &Id, at_: Time, template: &String) {
        let step = Step::Fire { schedule: schedule.clone(), at: at_, promise: expand(template, schedule, at_) };
        if self.fire_within > 0 {
            work.push(Work::Later(copy_step(&step)));
        }
        work.push(Work::Timer(at_.saturating_add(self.fire_within), step));
    }

    /// A schedule's occurrence at `at` fires, from `at` on: the promise it
    /// names is created, if absent, as of `at`; the schedule records the run
    /// and arms the next, at once when fires are exact, else by a step of its
    /// own (`advance`) owed within the window. The clock may be past `at`
    /// (the server got to it late, or jumped over several occurrences): a
    /// promise whose deadline has passed by `now` is born settled, as Lean's
    /// read-time projection would show it, and starts nothing. A schedule
    /// that is gone, or no longer expects this occurrence, fires nothing;
    /// before its instant it cannot fire yet.
    pub fn fire(&self, schedule: &Id, at_: Time, promise: &Id, s: &Server, now: Time) -> InOut {
        let c = match s.schedules.get(schedule) {
            Some(c) => c,
            None => return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: false },
        };
        // Not this occurrence: the schedule moved on, or was deleted and
        // created again under another template (same template: the same
        // occurrence, and this work does what the new schedule's would).
        if c.next_run_at != at_ || expand(&c.promise_id, schedule, at_) != *promise {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: false };
        }
        if now < at_ {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: true };
        }
        let mut marks = Vec::new();
        let mut work = Vec::new();
        let mut n = copy_server(s);
        if s.promises.contains_key(promise) {
            marks.push(mk("schedule: occurrence exists"));
        } else {
            let timeout_at = at_.saturating_add(c.promise_timeout);
            let tags = c.promise_tags;
            // Born live at `at`, or settled at its deadline: the deadline is
            // `at` itself when the timeout is zero, else before `now`.
            let live_now = timeout_at > now;
            let live_at = timeout_at > at_;
            let born = if live_now { PState::Pending } else if tags.timer { PState::Resolved } else { PState::TimedOut };
            let p = Promise {
                state: born,
                value: None,
                param: copy(&c.promise_param),
                timeout_at,
                created_at: if live_at { at_ } else { timeout_at },
                settled_at: if live_now { None } else { Some(timeout_at) },
                tags,
                callbacks: PSet::empty(),
                listeners: PSet::empty(),
            };
            n.promises.insert(promise.clone(), p);
            if live_now {
                work.push(at(timeout_at, promise));
            }
            if tags.target && !tags.timer {
                let due = match tags.delay {
                    Some(d) => if d > at_ { d } else { at_ },
                    None => at_,
                };
                let state = if live_now { TState::Pending } else { TState::Fulfilled };
                let retry_at = if live_now { Some(due) } else { None };
                n.tasks.insert(promise.clone(), Task { state, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at, resumes: Vec::new() });
                if live_now {
                    work.push(at(due, promise));
                }
            }
            marks.push(if live_now { mk("schedule fired") } else { mk("schedule fired past the occurrence's deadline") });
        }
        if self.fire_within == 0 {
            Resonate::record_run(&mut n, c, schedule, at_);
            self.arm_fire(&mut work, schedule, next_cron(&c.cron, at_), &c.promise_id);
        } else {
            let step = Step::Advance { schedule: schedule.clone(), at: at_, promise: promise.clone() };
            work.push(Work::Later(copy_step(&step)));
            work.push(Work::Timer(at_.saturating_add(self.fire_within), step));
        }
        InOut { next: n, work, send: Vec::new(), marks, pending: false }
    }

    /// The schedule records its run at `at` and arms the next.
    fn record_run(n: &mut Server, c: &Schedule, schedule: &Id, at_: Time) {
        let mut d = copy(c);
        d.last_run_at = Some(at_);
        d.next_run_at = next_cron(&c.cron, at_);
        n.schedules.insert(schedule.clone(), d);
    }

    /// The second half of a sweeping server's fire: the run at `at` recorded
    /// on `schedule` and the next occurrence armed. A schedule that is gone,
    /// or has moved on (the fire refired and advanced already), is left as it
    /// is.
    pub fn advance(&self, schedule: &Id, at_: Time, promise: &Id, s: &Server, now: Time) -> InOut {
        let c = match s.schedules.get(schedule) {
            Some(c) => c,
            None => return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: false },
        };
        if c.next_run_at != at_ || expand(&c.promise_id, schedule, at_) != *promise {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: false };
        }
        if now < at_ {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: true };
        }
        let mut n = copy_server(s);
        let mut work = Vec::new();
        Resonate::record_run(&mut n, c, schedule, at_);
        self.arm_fire(&mut work, schedule, next_cron(&c.cron, at_), &c.promise_id);
        InOut { next: n, work, send: Vec::new(), marks: marked(mk("schedule advanced")), pending: false }
    }
}

} // verus!
