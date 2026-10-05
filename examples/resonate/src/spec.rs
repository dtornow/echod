//! The Resonate server protocol, ported from resonatehq/resonate-accordant
//! (`Spec/State.cs`, `Spec/ExternalSteps.cs`, `Spec/InternalSteps.cs`,
//! `Spec/Harness.cs`), written in Verus: this is the code the checker runs, and
//! the code the proofs are about.
//!
//! Differences from the C# spec, all deliberate:
//! - Time is `Server::now`, as `ServerState.Now`, moved only by `AdvanceClock`
//!   (the C# driver also sets it on every request, with `resonate:debug_time`).
//! - A promise's deadline is a timer step that settles it, so there is no
//!   `Project(now)` read-time projection anywhere.
//! - A lease expiry is scheduled when the lease starts (`after` its end), not a
//!   trigger re-derived on every clock advance.
//! - Internal steps carry no kind: a step is "process these objects", and what is
//!   due on them comes from the state and the clock.
//! - Indefinite failures need no duplicated outcomes: an unanswered call is
//!   already "maybe".
//! - Not ported: `task.poll`, an optional capability in the C# spec (off unless
//!   `RESONATE_CAPS` declares `poll`).
//! - The only request that may cross origins is a fence that creates a promise
//!   in another origin: a detached workflow. A cross-origin fence-settle is 400
//!   (the C# spec and the server allow it; the Lean spec refuses every
//!   cross-origin fence, the detached create included).
//! - Clock and version arithmetic saturates instead of overflowing.
//! - Not ported: the `egress` capability (retry timeouts) and `debug.messages`.
//!
//! What Verus checks here: no panics and no overflow anywhere, and the
//! properties stated as `ensures` (see `promise_create`). What it trusts:
//! `collections.rs`.

use vstd::prelude::*;

use crate::collections::*;

verus! {

pub type Id = String;

pub type Time = u64;

pub const TASK_CREATE_TTL: Time = 3_600_000;

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
    Fulfilled,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Promise {
    pub state: PState,
    pub value: Option<String>,
    pub param: Option<String>,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    pub target: bool,
    pub external_tag: bool,
    pub timer_tag: bool,
    /// Awaiter ids to resume when this promise settles.
    pub callbacks: PSet,
}

impl Promise {
    pub fn external(&self) -> (r: bool)
        ensures
            r == (self.target || self.external_tag || self.timer_tag),
    {
        self.target || self.external_tag || self.timer_tag
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
    pub acquired_at: Time,
}

impl Task {
    fn fulfill(&mut self) {
        self.state = TState::Fulfilled;
        self.pid = None;
        self.ttl = None;
    }

    fn acquire(&mut self, version: u32, pid: String, ttl: Time, now: Time) {
        self.state = TState::Acquired;
        self.version = version;
        self.pid = Some(pid);
        self.ttl = Some(ttl);
        self.acquired_at = now;
    }

    pub fn lease_expires(&self) -> Time {
        match self.ttl {
            Some(ttl) => self.acquired_at.saturating_add(ttl),
            None => self.acquired_at,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Server {
    /// The server's clock.
    pub now: Time,
    pub promises: PMap<Promise>,
    pub tasks: PMap<Task>,
}

fn copy_server(s: &Server) -> (r: Server)
    ensures
        r.now == s.now,
        r.promises@ == s.promises@,
        r.tasks@ == s.tasks@,
{
    Server { now: s.now, promises: s.promises.copy(), tasks: s.tasks.copy() }
}

// ---------------------------------------------------------------- requests

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Create {
    pub id: Id,
    pub timeout_at: Time,
    pub data: Option<String>,
    pub external: bool,
    pub target: bool,
    pub timer: bool,
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

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Request {
    /// The driver moves the server's clock (`debug.tick`). Due timers and lease
    /// expiries run right after, before anything else.
    AdvanceClock(Time),
    CreatePromise(Create),
    GetPromise(Id),
    SettlePromise(Settle),
    RegisterCallback { awaited: Id, awaiter: Id },
    RegisterListener { awaited: Id, address: String },
    GetTask(Id),
    CreateTask { id: Id, timeout_at: Time, data: Option<String>, target: bool },
    AcquireTask { id: Id, version: u32, pid: String, ttl: Time },
    ReleaseTask { id: Id, version: u32 },
    FulfillTask { id: Id, version: u32, state: String, data: Option<String> },
    HeartbeatTask { id: Id, version: u32, pid: String },
    SuspendTask { id: Id, version: u32, awaited: Vec<Id> },
    FenceTask { id: Id, version: u32, action: Fenced },
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

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Tags {
    pub target: bool,
    pub external: bool,
    pub timer: bool,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct TaskRec {
    pub id: Id,
    pub state: TState,
    pub version: u32,
    pub pid: Option<String>,
    pub ttl: Option<Time>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Response {
    /// A status with no body we check.
    Status(u16),
    Promise(PromiseRec),
    Task(TaskRec),
    /// `task.create` on a fresh id: both records.
    Created(PromiseRec, TaskRec),
}

/// What the server sends on its own.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Dispatch {
    /// A worker should run this task at this version.
    Execute { id: Id, version: u32 },
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
        tags: Tags { target: p.target, external: p.external_tag, timer: p.timer_tag },
    }
}

fn trec(id: &Id, t: &Task) -> TaskRec {
    TaskRec { id: id.clone(), state: t.state, version: t.version, pid: copy(&t.pid), ttl: t.ttl }
}

// ------------------------------------------------------------------ outcomes

/// Internal work to start: the objects it processes, and when it runs. As
/// `accordant::Sched`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Work {
    Later(Vec<Id>),
    Timer(Time, Vec<Id>),
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

/// The effect of internal work. As `accordant::InternalOutcome`.
pub struct InOut {
    pub next: Server,
    pub work: Vec<Work>,
    pub send: Vec<Dispatch>,
    pub marks: Vec<&'static str>,
}

pub struct Resonate;

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
        r[0].next.now == s.now,
{
    one(Out { resp: Response::Status(code), next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: marked(mark) })
}

fn echo(res: Response, mark: &'static str, s: &Server) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0].resp == res,
        r[0].next.promises@ == s.promises@,
        r[0].next.tasks@ == s.tasks@,
        r[0].next.now == s.now,
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

/// One resume per stored callback: process the awaited promise and its awaiter.
fn resumes(p: &Promise, awaited: &Id) -> Vec<Work> {
    let awaiters = p.callbacks.to_vec();
    let mut out = Vec::new();
    let mut i = 0;
    while i < awaiters.len()
        invariant
            i <= awaiters.len(),
        decreases awaiters.len() - i,
    {
        out.push(Work::Later(ids2(awaited, &awaiters[i])));
        i += 1;
    }
    out
}

fn fireable(s: &Server, awaited: &Id, awaiter: &Id) -> bool {
    let has_callback = match s.promises.get(awaited) {
        Some(p) => p.callbacks.contains(awaiter),
        None => false,
    };
    let suspended = match s.tasks.get(awaiter) {
        Some(t) => t.state == TState::Suspended,
        None => false,
    };
    let live = match s.promises.get(awaiter) {
        Some(p) => p.live(),
        None => false,
    };
    has_callback && suspended && live
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
        Response::Created(p, _) => times_ok(p.created_at, p.settled_at, p.timeout_at),
        _ => true,
    }
}

// --------------------------------------------------------------- handlers

impl Resonate {
    /// Property 1: every promise `promise_create` creates has it, every
    /// response has it if the state had it, and every promise that had it keeps it.
    ///
    /// Frame: it touches only the promise and task it creates. Every other
    /// promise and task is as it was, an existing id changes nothing, and the
    /// clock doesn't move.
    pub fn promise_create(&self, req: &Create, fenced: bool, s: &Server) -> (outs: Vec<Out>)
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
                    &&& (s.promises@.contains_key(req.id@) ==> outs[i].next.promises@ == s.promises@
                        && outs[i].next.tasks@ == s.tasks@)
                    &&& outs[i].next.now == s.now
                },
    {
        let now = s.now;
        if req.timer && req.target {
            return status(400, mk("create: timer with target (400)"), s);  // P-02
        }
        match s.promises.get(&req.id) {
            Some(p) => {
                // P-02: re-create echoes
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
        } else if req.timer {
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
            target: req.target,
            external_tag: req.external,
            timer_tag: req.timer,
            callbacks: PSet::empty(),
        };
        let rec = prec(&req.id, &p);
        let mut n = copy_server(s);
        n.promises.insert(req.id.clone(), p);
        if req.target {
            let state = if live { TState::Pending } else { TState::Fulfilled };
            let task = Task { state, version: 0, pid: None, ttl: None, acquired_at: 0 };
            n.tasks.insert(req.id.clone(), task);
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
        let mut send = Vec::new();
        // A live targeted promise's task is runnable: the server dispatches it.
        if live && req.target {
            send.push(Dispatch::Execute { id: req.id.clone(), version: 0 });
        }
        let mut work = Vec::new();
        if live {
            work.push(Work::Timer(req.timeout_at, ids1(&req.id)));
        }
        let mut marks = Vec::new();
        marks.push(match (fenced, live) {
            (false, true) => mk("promise created"),
            (false, false) => mk("promise created past its deadline"),
            (true, true) => mk("fence: promise created"),
            (true, false) => mk("fence: promise created past its deadline"),
        });
        if live && req.target {
            marks.push(mk("task dispatched"));
        }
        one(Out { resp: Response::Promise(rec), next: n, work, send, marks })
    }

    fn promise_settle(&self, req: &Settle, fenced: bool, s: &Server) -> Vec<Out> {
        let now = s.now;
        let state = match settable(&req.state) {
            Some(st) => st,
            None => return status(400, mk("settle: not a settled state (400)"), s),  // P-03
        };
        let p = match s.promises.get(&req.id) {
            Some(p) => p,
            None => return status(404, mk("settle: no such promise (404)"), s),
        };
        if !p.live() {
            return echo(Response::Promise(prec(&req.id, p)), mk("settle: already settled (echo)"), s);  // P-03
        }
        let work = resumes(p, &req.id);
        let mut n = copy_server(s);
        settle(&mut n, &req.id, state, copy(&req.data), now);
        let res = match n.promises.get(&req.id) {
            Some(q) => Response::Promise(prec(&req.id, q)),
            None => Response::Status(500),  // unreachable: the promise exists
        };
        let mut marks = Vec::new();
        marks.push(if fenced { mk("fence: promise settled") } else { mk("promise settled") });
        if work.len() > 0 {
            marks.push(mk("resume armed"));
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

    fn task_create(&self, id: &Id, timeout_at: Time, data: &Option<String>, target: bool, s: &Server) -> Vec<Out> {
        let now = s.now;
        if !target {
            return status(400, mk("task.create: not a target (400)"), s);  // T-02
        }
        match s.promises.get(id) {
            Some(p) => {
                if !p.target {
                    return status(422, mk("task.create: promise exists, not a target (422)"), s);
                }
                let t = match s.tasks.get(id) {
                    Some(t) => t,
                    None => return status(500, mk("task.create: target without a task (500)"), s),  // unreachable
                };
                return match t.state {
                    TState::Fulfilled => echo(Response::Task(trec(id, t)), mk("task.create: task done (echo)"), s),
                    TState::Pending => {
                        let mut n = copy_server(s);
                        let mut u = copy(t);
                        u.acquire(t.version.saturating_add(1), worker_self(), TASK_CREATE_TTL, now);
                        let rec = trec(id, &u);
                        n.tasks.insert(id.clone(), u);
                        let mut work = Vec::new();
                        work.push(Work::Timer(now.saturating_add(TASK_CREATE_TTL), ids1(id)));
                        one(Out { resp: Response::Task(rec), next: n, work, send: Vec::new(), marks: marked(mk("task.create: pending task acquired")) })
                    },
                    _ => status(409, mk("task.create: task held (409)"), s),
                };
            },
            None => {},
        }
        let p = Promise {
            state: PState::Pending,
            value: None,
            param: copy(data),
            timeout_at,
            created_at: now,
            settled_at: None,
            target: true,
            external_tag: false,
            timer_tag: false,
            callbacks: PSet::empty(),
        };
        // Acquired by the caller right away: nothing to dispatch.
        let mut t = Task { state: TState::Pending, version: 0, pid: None, ttl: None, acquired_at: 0 };
        t.acquire(1, worker_self(), TASK_CREATE_TTL, now);
        let res = Response::Created(prec(id, &p), trec(id, &t));
        let mut n = copy_server(s);
        n.promises.insert(id.clone(), p);
        n.tasks.insert(id.clone(), t);
        let mut work = Vec::new();
        work.push(Work::Timer(timeout_at, ids1(id)));
        work.push(Work::Timer(now.saturating_add(TASK_CREATE_TTL), ids1(id)));
        one(Out { resp: res, next: n, work, send: Vec::new(), marks: marked(mk("task created")) })
    }

    fn task_suspend(&self, id: &Id, version: u32, ids: &Vec<Id>, s: &Server) -> Vec<Out> {
        if ids.len() == 0 || contains(ids, id) {
            return status(400, mk("suspend: no awaited, or itself (400)"), s);  // T-06
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
        match self.held(s, id, version) {
            Err(code) => return status(code, if code == 404 { mk("suspend: no such task (404)") } else { mk("suspend: not held (409)") }, s),
            Ok(_) => {},
        }
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
        if settled {
            return status(300, mk("suspend: awaited already settled (300)"), s);  // task stays acquired
        }
        let mut n = copy_server(s);
        match s.tasks.get(id) {
            Some(t) => {
                let mut u = copy(t);
                u.state = TState::Suspended;
                u.pid = None;
                u.ttl = None;
                n.tasks.insert(id.clone(), u);
            },
            None => {},
        }
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

    /// A request takes effect in `s`: every allowed outcome.
    pub fn external(&self, op: &Request, s: &Server) -> Vec<Out> {
        let now = s.now;
        match op {
            Request::AdvanceClock(t) => {
                let mut n = copy_server(s);
                n.now = if *t > now { *t } else { now };
                let mark = if *t > now { mk("clock moved") } else { mk("clock unchanged") };
                one(Out { resp: Response::Status(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mark) })
            },
            Request::CreatePromise(c) => self.promise_create(c, false, s),
            Request::GetPromise(id) => match s.promises.get(id) {
                None => status(404, mk("get promise: none (404)"), s),
                Some(p) => echo(Response::Promise(prec(id, p)), mk("get promise"), s),
            },
            Request::SettlePromise(st) => self.promise_settle(st, false, s),
            Request::RegisterCallback { awaited, awaiter } => {
                if *awaited == *awaiter || !same_origin(awaited, awaiter) {
                    return status(400, mk("callback: itself or another origin (400)"), s);  // P-04
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
                    return status(400, mk("listener: bad address (400)"), s);  // P-05
                }
                match s.promises.get(awaited) {
                    None => status(404, mk("listener: no such promise (404)"), s),
                    Some(p) => {
                        if !p.external() {
                            status(422, mk("listener: promise not external (422)"), s)
                        } else {
                            echo(Response::Promise(prec(awaited, p)), mk("listener registered"), s)
                        }
                    },
                }
            },
            Request::GetTask(id) => match s.tasks.get(id) {
                None => status(404, mk("get task: none (404)"), s),
                Some(t) => echo(Response::Task(trec(id, t)), mk("get task"), s),
            },
            Request::CreateTask { id, timeout_at, data, target } => self.task_create(id, *timeout_at, data, *target, s),
            Request::AcquireTask { id, version, pid, ttl } => {
                let t = match s.tasks.get(id) {
                    Some(t) => t,
                    None => return status(404, mk("acquire: no such task (404)"), s),
                };
                let live = match s.promises.get(id) {
                    Some(p) => p.live(),
                    None => false,
                };
                if t.state != TState::Pending || !live || t.version != *version {
                    return status(409, mk("acquire: not pending, or stale version (409)"), s);  // T-03
                }
                let mut n = copy_server(s);
                let mut u = copy(t);
                u.acquire(t.version.saturating_add(1), pid.clone(), *ttl, now);
                let rec = trec(id, &u);
                n.tasks.insert(id.clone(), u);
                let mut work = Vec::new();
                work.push(Work::Timer(now.saturating_add(*ttl), ids1(id)));
                one(Out { resp: Response::Task(rec), next: n, work, send: Vec::new(), marks: marked(mk("task acquired")) })
            },
            Request::ReleaseTask { id, version } => match self.held(s, id, *version) {
                Err(code) => status(code, if code == 404 { mk("release: no such task (404)") } else { mk("release: not held (409)") }, s),
                Ok(t) => {
                    let mut n = copy_server(s);
                    let mut u = copy(t);
                    u.state = TState::Pending;
                    u.pid = None;
                    u.ttl = None;
                    let version = u.version;
                    n.tasks.insert(id.clone(), u);
                    let mut send = Vec::new();
                    send.push(Dispatch::Execute { id: id.clone(), version });
                    let mut marks = Vec::new();
                    marks.push(mk("task released"));
                    marks.push(mk("task dispatched"));
                    one(Out { resp: Response::Status(200), next: n, work: Vec::new(), send, marks })
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
                    Some(p) => resumes(p, id),
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
            Request::HeartbeatTask { id, version, pid } => {
                let extends = match self.held(s, id, *version) {
                    Ok(t) => match &t.pid {
                        Some(holder) => *holder == *pid,
                        None => false,
                    },
                    Err(_) => false,
                };
                if !extends {
                    return status(200, mk("heartbeat: not held by this worker"), s);  // T-05: always 200
                }
                let mut n = copy_server(s);
                match s.tasks.get(id) {
                    Some(t) => {
                        let mut u = copy(t);
                        u.acquired_at = now;
                        let expires = u.lease_expires();
                        n.tasks.insert(id.clone(), u);
                        let mut work = Vec::new();
                        work.push(Work::Timer(expires, ids1(id)));
                        one(Out { resp: Response::Status(200), next: n, work, send: Vec::new(), marks: marked(mk("lease extended")) })
                    },
                    None => status(200, mk("heartbeat: not held by this worker"), s),
                }
            },
            Request::SuspendTask { id, version, awaited } => self.task_suspend(id, *version, awaited, s),
            Request::FenceTask { id, version, action } => {
                if *action.target() == *id {
                    return status(400, mk("fence: targets its own task (400)"), s);  // T-04
                }
                match action {
                    Fenced::Settle(st) => {
                        if !same_origin(&st.id, id) {
                            return status(400, mk("fence: settle in another origin (400)"), s);  // only a create may cross origins
                        }
                    },
                    Fenced::Create(_) => {},
                }
                match self.held(s, id, *version) {
                    Err(code) => return status(code, if code == 404 { mk("fence: no such task (404)") } else { mk("fence: not held, or stale version (409)") }, s),
                    Ok(_) => {},
                }
                match action {
                    Fenced::Create(c) => self.promise_create(c, true, s),
                    Fenced::Settle(st) => self.promise_settle(st, true, s),
                }
            },
        }
    }

    /// Internal work on `ids` runs in `s`: whatever is due on them happens.
    pub fn internal(&self, ids: &Vec<Id>, s: &Server) -> InOut {
        let now = s.now;
        let mut n = copy_server(s);
        let mut work = Vec::new();
        let mut send = Vec::new();
        let mut marks = Vec::new();
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
            decreases ids.len() - i,
        {
            let id = &ids[i];
            // A promise past its deadline times out (a timer promise resolves).
            match s.promises.get(id) {
                Some(p) => {
                    if p.live() && now >= p.timeout_at {
                        let state = if p.timer_tag { PState::Resolved } else { PState::TimedOut };
                        marks.push(if p.timer_tag { mk("timer promise resolved") } else { mk("promise timed out") });
                        let r = resumes(p, id);
                        settle(&mut n, id, state, None, p.timeout_at);
                        let mut j = 0;
                        while j < r.len()
                            invariant
                                j <= r.len(),
                            decreases r.len() - j,
                        {
                            work.push(r[j].clone());
                            j += 1;
                        }
                    }
                },
                None => {},
            }
            // A task past its lease is reclaimed.
            match n.tasks.get(id) {
                Some(t) => {
                    if t.state == TState::Acquired && now >= t.lease_expires() {
                        let mut u = copy(t);
                        u.state = TState::Pending;
                        u.pid = None;
                        u.ttl = None;
                        let version = u.version;
                        n.tasks.insert(id.clone(), u);
                        send.push(Dispatch::Execute { id: id.clone(), version });
                        marks.push(mk("lease expired"));
                    }
                },
                None => {},
            }
            i += 1;
        }
        // A suspended task resumes when a promise it awaits has settled.
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
                let settled = match n.promises.get(awaited) {
                    Some(p) => !p.live(),
                    None => false,
                };
                if settled && fireable(&n, awaited, awaiter) {
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
                            let mut u = copy(t);
                            u.state = TState::Pending;
                            let version = u.version;
                            n.tasks.insert(awaiter.clone(), u);
                            send.push(Dispatch::Execute { id: awaiter.clone(), version });
                            marks.push(mk("task resumed"));
                        },
                        None => {},
                    }
                }
                w += 1;
            }
            a += 1;
        }
        InOut { next: n, work, send, marks }
    }
}

} // verus!
