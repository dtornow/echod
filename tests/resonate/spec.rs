//! The Resonate server protocol, ported from resonatehq/resonate-accordant
//! (`Spec/State.cs`, `Spec/ExternalSteps.cs`, `Spec/InternalSteps.cs`, `Spec/Harness.cs`).
//!
//! Differences from the C# spec, all deliberate:
//! - Time is the checker's clock, not `ServerState.Now`; `AdvanceClock` is `tick`.
//! - A promise's deadline is a timer step that settles it, so there is no
//!   `Project(now)` read-time projection anywhere.
//! - A lease expiry is a timer installed when the lease starts, not a trigger
//!   re-derived on every clock advance.
//! - Indefinite failures need no duplicated outcomes: an unanswered call is
//!   already "maybe".
//! - `PollTask` past its limit claims some subset of size `limit` (the C# spec
//!   checks only the count and keeps the state unchanged).
//! - The only request that may cross origins is a fence that creates a promise
//!   in another origin: a detached workflow. A cross-origin fence-settle is 400
//!   (the C# spec and the server allow it; the Lean spec refuses every
//!   cross-origin fence, the detached create included).
//! - Not ported: the `egress` capability (retry timeouts) and `debug.messages`.

use std::collections::BTreeSet;

use accordant::{Fairness, Footprint, HashedMap, Model, Outcome, Partitioned, Succ, Time, Touches};

pub type Id = String;

pub const TASK_CREATE_TTL: Time = 3_600_000;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum PState {
    Pending,
    Resolved,
    Rejected,
    Canceled,
    TimedOut,
}

impl PState {
    /// The states a client may settle a promise to.
    pub fn settable(s: &str) -> Option<PState> {
        match s {
            "resolved" => Some(PState::Resolved),
            "rejected" => Some(PState::Rejected),
            "rejected_canceled" => Some(PState::Canceled),
            _ => None,
        }
    }
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
    pub callbacks: BTreeSet<Id>,
}

impl Promise {
    pub fn external(&self) -> bool {
        self.target || self.external_tag || self.timer_tag
    }

    /// Pending and before its deadline. The deadline is a timer that fires first
    /// at its instant, so a pending promise is always live.
    pub fn live(&self) -> bool {
        self.state == PState::Pending
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

    fn acquire(&mut self, version: u32, pid: &str, ttl: Time, now: Time) {
        self.state = TState::Acquired;
        self.version = version;
        self.pid = Some(pid.to_string());
        self.ttl = Some(ttl);
        self.acquired_at = now;
    }

    fn lease_expires(&self) -> Time {
        self.acquired_at + self.ttl.unwrap_or(0)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Server {
    pub promises: HashedMap<Id, Promise>,
    pub tasks: HashedMap<Id, Task>,
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
    fn target(&self) -> &Id {
        match self {
            Fenced::Create(c) => &c.id,
            Fenced::Settle(s) => &s.id,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Request {
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
    PollTask { pid: String, ttl: Time, limit: usize },
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
    /// (target, external, timer) tags.
    pub tags: (bool, bool, bool),
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
    /// `task.poll`: claimed tasks, ordered by id.
    Claimed(Vec<TaskRec>),
}

impl Response {
    pub fn status(&self) -> u16 {
        match self {
            Response::Status(s) => *s,
            _ => 200,
        }
    }
}

fn prec(id: &str, p: &Promise) -> PromiseRec {
    PromiseRec {
        id: id.to_string(),
        state: p.state,
        param: p.param.clone(),
        value: p.value.clone(),
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
        tags: (p.target, p.external_tag, p.timer_tag),
    }
}

fn trec(id: &str, t: &Task) -> TaskRec {
    TaskRec { id: id.to_string(), state: t.state, version: t.version, pid: t.pid.clone(), ttl: t.ttl }
}

// ------------------------------------------------------------------- steps

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Internal {
    /// A promise's deadline.
    Timeout(Id),
    /// A lease ends; the server may reclaim the task any time after.
    Lease { id: Id, expires: Time },
    /// Resume `awaiter` because `awaited` settled.
    Resume { awaited: Id, awaiter: Id },
}

// -------------------------------------------------------------------- spec

pub struct Resonate;

type Outcomes = Vec<Outcome<Resonate>>;

fn status(code: u16, s: &Server) -> Outcomes {
    vec![Outcome::same(Response::Status(code), s)]
}

fn echo(resp: Response, s: &Server) -> Outcomes {
    vec![Outcome::same(resp, s)]
}

fn origin(id: &str) -> &str {
    id.split_once(':').map_or(id, |(o, _)| o)
}

/// Any absolute URL: a scheme, a colon, and a non-empty rest with no whitespace.
/// Stands in for C#'s `Uri.TryCreate(.., Absolute)` plus its scheme regex.
fn address_valid(addr: &str) -> bool {
    let a = addr.trim();
    let Some((scheme, rest)) = a.split_once(':') else { return false };
    let mut cs = scheme.chars();
    cs.next().is_some_and(|c| c.is_ascii_alphabetic())
        && cs.all(|c| c.is_ascii_alphanumeric() || "+.-".contains(c))
        && !rest.is_empty()
        && !rest.chars().any(char::is_whitespace)
}

/// Settles `id` and fulfills its task, if any.
fn settle(s: &mut Server, id: &str, state: PState, value: Option<String>, at: Time) {
    s.promises.update(id, |p| {
        p.state = state;
        p.value = value;
        p.settled_at = Some(at);
    });
    s.tasks.update(id, |t| {
        if t.state != TState::Fulfilled {
            t.fulfill()
        }
    });
}

/// One resume per stored callback; each checks for itself whether it can fire.
fn resumes(p: &Promise, awaited: &str) -> Vec<Internal> {
    p.callbacks
        .iter()
        .map(|a| Internal::Resume { awaited: awaited.to_string(), awaiter: a.clone() })
        .collect()
}

fn with_spawns(mut o: Outcome<Resonate>, steps: Vec<Internal>) -> Outcome<Resonate> {
    for st in steps {
        o = o.spawn(st);
    }
    o
}

fn fireable(s: &Server, awaited: &str, awaiter: &str) -> bool {
    s.promises.get(awaited).is_some_and(|p| p.callbacks.contains(awaiter))
        && s.tasks.get(awaiter).is_some_and(|t| t.state == TState::Suspended)
        && s.promises.get(awaiter).is_some_and(Promise::live)
}

impl Resonate {
    fn promise_create(&self, req: &Create, s: &Server, now: Time) -> Outcomes {
        if req.timer && req.target {
            return status(400, s); // P-02: timer with target is malformed
        }
        if let Some(p) = s.promises.get(&req.id) {
            return echo(Response::Promise(prec(&req.id, p)), s); // P-02: re-create echoes
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
            param: req.data.clone(),
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: (!live).then_some(req.timeout_at),
            target: req.target,
            external_tag: req.external,
            timer_tag: req.timer,
            callbacks: BTreeSet::new(),
        };
        let mut n = s.clone();
        n.promises.insert(req.id.clone(), p.clone());
        if req.target {
            let state = if live { TState::Pending } else { TState::Fulfilled };
            n.tasks.insert(req.id.clone(), Task { state, version: 0, pid: None, ttl: None, acquired_at: 0 });
        }
        let o = Outcome::new(Response::Promise(prec(&req.id, &p)), n);
        vec![if live { o.timer(req.timeout_at, Internal::Timeout(req.id.clone())) } else { o }]
    }

    fn promise_settle(&self, req: &Settle, s: &Server, now: Time) -> Outcomes {
        let Some(state) = PState::settable(&req.state) else {
            return status(400, s); // P-03
        };
        let Some(p) = s.promises.get(&req.id) else {
            return status(404, s);
        };
        if !p.live() {
            return echo(Response::Promise(prec(&req.id, p)), s); // P-03: not settleable
        }
        let mut n = s.clone();
        settle(&mut n, &req.id, state, req.data.clone(), now);
        let rec = prec(&req.id, &n.promises[&req.id]);
        vec![with_spawns(Outcome::new(Response::Promise(rec), n), resumes(p, &req.id))]
    }

    /// The checks every task.* mutation shares: exists, acquired, own promise live,
    /// version matches. `Ok` is the task.
    fn held<'a>(&self, s: &'a Server, id: &str, version: u32) -> Result<&'a Task, u16> {
        let t = s.tasks.get(id).ok_or(404u16)?;
        if t.state != TState::Acquired || !s.promises[id].live() || t.version != version {
            return Err(409);
        }
        Ok(t)
    }

    fn task_create(&self, id: &Id, timeout_at: Time, data: &Option<String>, target: bool, s: &Server, now: Time) -> Outcomes {
        if !target {
            return status(400, s); // T-02
        }
        if let Some(p) = s.promises.get(id) {
            if !p.target {
                return status(422, s);
            }
            let t = &s.tasks[id];
            return match t.state {
                TState::Fulfilled => echo(Response::Task(trec(id, t)), s),
                TState::Pending => {
                    let mut n = s.clone();
                    n.tasks.update(id, |t| t.acquire(t.version + 1, "worker-self", TASK_CREATE_TTL, now));
                    let rec = trec(id, &n.tasks[id]);
                    let lease = Internal::Lease { id: id.clone(), expires: now + TASK_CREATE_TTL };
                    vec![Outcome::new(Response::Task(rec), n).timer(now + TASK_CREATE_TTL, lease)]
                }
                _ => status(409, s),
            };
        }
        let p = Promise {
            state: PState::Pending,
            value: None,
            param: data.clone(),
            timeout_at,
            created_at: now,
            settled_at: None,
            target: true,
            external_tag: false,
            timer_tag: false,
            callbacks: BTreeSet::new(),
        };
        let mut t = Task { state: TState::Pending, version: 0, pid: None, ttl: None, acquired_at: 0 };
        t.acquire(1, "worker-self", TASK_CREATE_TTL, now);
        let mut n = s.clone();
        n.promises.insert(id.clone(), p.clone());
        n.tasks.insert(id.clone(), t.clone());
        let lease = Internal::Lease { id: id.clone(), expires: now + TASK_CREATE_TTL };
        vec![Outcome::new(Response::Created(prec(id, &p), trec(id, &t)), n)
            .timer(timeout_at, Internal::Timeout(id.clone()))
            .timer(now + TASK_CREATE_TTL, lease)]
    }

    fn task_suspend(&self, id: &Id, version: u32, ids: &[Id], s: &Server) -> Outcomes {
        if ids.is_empty() || ids.contains(id) || ids.iter().collect::<BTreeSet<_>>().len() != ids.len() {
            return status(400, s); // T-06: empty, self, or duplicate
        }
        if ids.iter().any(|a| origin(a) != origin(id)) {
            return status(400, s);
        }
        if let Err(code) = self.held(s, id, version) {
            return status(code, s);
        }
        let mut settled = false;
        for a in ids {
            match s.promises.get(a) {
                None => return status(422, s),
                Some(p) if !p.external() => return status(422, s),
                Some(p) => settled |= !p.live(),
            }
        }
        if settled {
            return status(300, s); // resume now; task stays acquired
        }
        let mut n = s.clone();
        n.tasks.update(id, |t| {
            t.state = TState::Suspended;
            t.pid = None;
            t.ttl = None;
        });
        for a in ids {
            n.promises.update(a, |p| {
                p.callbacks.insert(id.clone());
            });
        }
        vec![Outcome::new(Response::Status(200), n)]
    }

    fn claimable(&self, s: &Server, now: Time) -> Vec<Id> {
        s.tasks
            .iter()
            .filter(|(id, t)| {
                let Some(p) = s.promises.get(*id) else { return false };
                p.target
                    && p.live()
                    && match t.state {
                        TState::Pending => true,
                        TState::Acquired => now >= t.lease_expires(),
                        TState::Suspended => s.promises.iter().any(|(_, q)| q.callbacks.contains(*id) && !q.live()),
                        TState::Fulfilled => false,
                    }
            })
            .map(|(id, _)| id.clone())
            .collect()
    }

    fn task_poll(&self, pid: &str, ttl: Time, limit: usize, s: &Server, now: Time) -> Outcomes {
        let claimable = self.claimable(s, now);
        combinations(&claimable, limit.min(claimable.len()))
            .into_iter()
            .map(|claim| {
                let mut n = s.clone();
                let mut recs = Vec::new();
                let mut leases = Vec::new();
                for id in &claim {
                    n.tasks.update(id, |t| t.acquire(t.version + 1, pid, ttl, now));
                    recs.push(trec(id, &n.tasks[id]));
                    leases.push(Internal::Lease { id: id.clone(), expires: now + ttl });
                    let holders: Vec<Id> =
                        n.promises.iter().filter(|(_, p)| p.callbacks.contains(id)).map(|(k, _)| k.clone()).collect();
                    for h in holders {
                        n.promises.update(&h, |p| {
                            p.callbacks.remove(id);
                        });
                    }
                }
                let mut o = Outcome::new(Response::Claimed(recs), n);
                for l in leases {
                    o = o.timer(now + ttl, l);
                }
                o
            })
            .collect()
    }
}

fn combinations(items: &[Id], k: usize) -> Vec<Vec<Id>> {
    if k == 0 {
        return vec![vec![]];
    }
    let mut out = Vec::new();
    for (i, x) in items.iter().enumerate() {
        for mut rest in combinations(&items[i + 1..], k - 1) {
            rest.insert(0, x.clone());
            out.push(rest);
        }
    }
    out
}

impl Model for Resonate {
    type State = Server;
    type External = Request;
    type Response = Response;
    type Internal = Internal;

    fn external(&self, op: &Request, s: &Server, now: Time) -> Outcomes {
        match op {
            Request::CreatePromise(c) => self.promise_create(c, s, now),
            Request::GetPromise(id) => match s.promises.get(id) {
                None => status(404, s),
                Some(p) => echo(Response::Promise(prec(id, p)), s),
            },
            Request::SettlePromise(st) => self.promise_settle(st, s, now),

            Request::RegisterCallback { awaited, awaiter } => {
                if awaited == awaiter || origin(awaited) != origin(awaiter) {
                    return status(400, s); // P-04
                }
                let Some(p) = s.promises.get(awaited) else { return status(404, s) };
                let Some(w) = s.promises.get(awaiter) else { return status(422, s) };
                if !s.tasks.contains_key(awaiter) || !p.external() {
                    return status(422, s);
                }
                let resp = Response::Promise(prec(awaited, p));
                if !p.live() || !w.live() {
                    return echo(resp, s);
                }
                let mut n = s.clone();
                n.promises.update(awaited, |p| {
                    p.callbacks.insert(awaiter.clone());
                });
                vec![Outcome::new(resp, n)]
            }

            Request::RegisterListener { awaited, address } => {
                if !address_valid(address) {
                    return status(400, s); // P-05
                }
                match s.promises.get(awaited) {
                    None => status(404, s),
                    Some(p) if !p.external() => status(422, s),
                    Some(p) => echo(Response::Promise(prec(awaited, p)), s),
                }
            }

            Request::GetTask(id) => match s.tasks.get(id) {
                None => status(404, s),
                Some(t) => echo(Response::Task(trec(id, t)), s),
            },

            Request::CreateTask { id, timeout_at, data, target } => self.task_create(id, *timeout_at, data, *target, s, now),

            Request::AcquireTask { id, version, pid, ttl } => {
                let Some(t) = s.tasks.get(id) else { return status(404, s) };
                if t.state != TState::Pending || !s.promises[id].live() || t.version != *version {
                    return status(409, s); // T-03
                }
                let mut n = s.clone();
                n.tasks.update(id, |t| t.acquire(t.version + 1, pid, *ttl, now));
                let rec = trec(id, &n.tasks[id]);
                let lease = Internal::Lease { id: id.clone(), expires: now + ttl };
                vec![Outcome::new(Response::Task(rec), n).timer(now + ttl, lease)]
            }

            Request::ReleaseTask { id, version } => match self.held(s, id, *version) {
                Err(code) => status(code, s),
                Ok(_) => {
                    let mut n = s.clone();
                    n.tasks.update(id, |t| {
                        t.state = TState::Pending;
                        t.pid = None;
                        t.ttl = None;
                    });
                    vec![Outcome::new(Response::Status(200), n)]
                }
            },

            Request::FulfillTask { id, version, state, data } => {
                let Some(st) = PState::settable(state) else { return status(400, s) };
                if let Err(code) = self.held(s, id, *version) {
                    return status(code, s);
                }
                let mut n = s.clone();
                settle(&mut n, id, st, data.clone(), now);
                let rec = prec(id, &n.promises[id]);
                vec![with_spawns(Outcome::new(Response::Promise(rec), n), resumes(&s.promises[id], id))]
            }

            Request::HeartbeatTask { id, version, pid } => {
                let extends = self.held(s, id, *version).is_ok_and(|t| t.pid.as_deref() == Some(pid.as_str()));
                if !extends {
                    return status(200, s); // T-05: always 200
                }
                let mut n = s.clone();
                n.tasks.update(id, |t| t.acquired_at = now);
                let expires = n.tasks[id].lease_expires();
                vec![Outcome::new(Response::Status(200), n).timer(expires, Internal::Lease { id: id.clone(), expires })]
            }

            Request::SuspendTask { id, version, awaited } => self.task_suspend(id, *version, awaited, s),

            Request::FenceTask { id, version, action } => {
                if action.target() == id {
                    return status(400, s); // T-04
                }
                if let Fenced::Settle(st) = action {
                    if origin(&st.id) != origin(id) {
                        return status(400, s); // only a create, a detached promise, may cross origins
                    }
                }
                if let Err(code) = self.held(s, id, *version) {
                    return status(code, s);
                }
                match action {
                    Fenced::Create(c) => self.promise_create(c, s, now),
                    Fenced::Settle(st) => self.promise_settle(st, s, now),
                }
            }

            Request::PollTask { pid, ttl, limit } => self.task_poll(pid, *ttl, *limit, s, now),
        }
    }

    fn internal(&self, req: &Internal, s: &Server, _now: Time) -> Vec<Succ<Self>> {
        match req {
            Internal::Timeout(id) => {
                let p = &s.promises[id];
                if !p.live() {
                    return vec![Succ::same(s)];
                }
                let state = if p.timer_tag { PState::Resolved } else { PState::TimedOut };
                let mut n = s.clone();
                settle(&mut n, id, state, None, p.timeout_at);
                let mut succ = Succ::new(n);
                for r in resumes(p, id) {
                    succ = succ.spawn(r);
                }
                vec![succ]
            }
            Internal::Lease { id, expires } => {
                let t = &s.tasks[id];
                if t.state != TState::Acquired || t.lease_expires() != *expires {
                    return vec![Succ::same(s)]; // released, fulfilled, or extended
                }
                let mut n = s.clone();
                n.tasks.update(id, |t| {
                    t.state = TState::Pending;
                    t.pid = None;
                    t.ttl = None;
                });
                vec![Succ::new(n)]
            }
            Internal::Resume { awaited, awaiter } => {
                if !fireable(s, awaited, awaiter) {
                    return vec![Succ::same(s)];
                }
                let mut n = s.clone();
                n.promises.update(awaited, |p| {
                    p.callbacks.remove(awaiter);
                });
                n.tasks.update(awaiter, |t| t.state = TState::Pending);
                vec![Succ::new(n)]
            }
        }
    }

    fn fairness(&self, step: &Internal) -> Fairness {
        match step {
            Internal::Timeout(_) => Fairness::Eventually { within: Some(0) },
            Internal::Lease { .. } | Internal::Resume { .. } => Fairness::Eventually { within: None },
        }
    }

}

impl Footprint for Resonate {
    type Key = Id;

    fn external_touches(&self, op: &Request) -> Touches<Id> {
        let ks = |v: &[&Id]| Touches::Only(v.iter().map(|k| (*k).clone()).collect());
        match op {
            Request::CreatePromise(c) => ks(&[&c.id]),
            Request::SettlePromise(st) => ks(&[&st.id]),
            Request::GetPromise(id)
            | Request::GetTask(id)
            | Request::CreateTask { id, .. }
            | Request::AcquireTask { id, .. }
            | Request::ReleaseTask { id, .. }
            | Request::FulfillTask { id, .. }
            | Request::HeartbeatTask { id, .. } => ks(&[id]),
            // A request refused for crossing origins is refused on the ids alone and
            // reads nothing, so its footprint stays in one origin.
            Request::RegisterCallback { awaited, awaiter } if origin(awaited) != origin(awaiter) => ks(&[awaited]),
            Request::RegisterCallback { awaited, awaiter } => ks(&[awaited, awaiter]),
            Request::RegisterListener { awaited, .. } => ks(&[awaited]),
            Request::SuspendTask { id, awaited, .. } if awaited.iter().any(|a| origin(a) != origin(id)) => ks(&[id]),
            Request::SuspendTask { id, awaited, .. } => {
                let mut v: Vec<&Id> = awaited.iter().collect();
                v.push(id);
                ks(&v)
            }
            Request::FenceTask { id, action: Fenced::Settle(st), .. } if origin(&st.id) != origin(id) => ks(&[id]),
            // A detached create: the one request that spans two origins.
            Request::FenceTask { id, action, .. } => ks(&[id, action.target()]),
            Request::PollTask { .. } => Touches::Everything,
        }
    }

    fn internal_touches(&self, step: &Internal) -> Touches<Id> {
        match step {
            Internal::Timeout(id) | Internal::Lease { id, .. } => Touches::one(id.clone()),
            Internal::Resume { awaited, awaiter } => Touches::Only(vec![awaited.clone(), awaiter.clone()]),
        }
    }
}

impl Partitioned for Resonate {
    type Group = String;

    /// Ids of different origins never interact, except through a detached create
    /// (`FenceTask` creating in another origin) and `PollTask`. Their footprints
    /// span origins and merge the partitions; the checker splits them again once
    /// the candidates are independent.
    fn group(&self, id: &Id) -> String {
        origin(id).to_string()
    }

    fn restrict(&self, s: &Server, keep: &dyn Fn(&Id) -> bool) -> Server {
        let mine = |k: &Id| keep(&origin(k).to_string());
        Server {
            promises: s.promises.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
            tasks: s.tasks.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
        }
    }

    fn join(&self, a: &Server, b: &Server) -> Server {
        let mut n = a.clone();
        for (k, v) in b.promises.iter() {
            n.promises.insert(k.clone(), v.clone());
        }
        for (k, v) in b.tasks.iter() {
            n.tasks.insert(k.clone(), v.clone());
        }
        n
    }
}
