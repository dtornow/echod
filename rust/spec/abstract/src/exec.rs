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
//! What Verus checks here: no panics and no overflow anywhere; that every
//! handler computes its twin in `spec.rs` (the `ensures` naming a `*_v`); and
//! the properties stated as `ensures` besides (see `promise_create`). What it
//! trusts: `collections.rs`.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_rover::Sched;

use echod_types::{PromiseCreateReq, PromiseRecord, PromiseRes, PromiseSettleReq, PromiseState, Request, Response, Schedule, ScheduleCreateReq, ScheduleRes, StatusRes, Tags, TaskClaimRes, TaskFenceAction, TaskFenceCheckReq, TaskFenceInnerRes, TaskFenceRes, TaskGetRes, TaskRecord, TaskRef, TaskState, TaskSuspendReq, Value};

use super::collections::*;
use super::spec::MAX_VERSION;

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
use super::spec::{Chars, DispatchV, InternalV, PromiseV, ResponseV, ServerV, TaskV, acquired_v, advance_v, all_external, all_in_origin, all_present, any_settled, arm_fire_v, at_v, deadlines_fold, distinct, due_fold, echo_v, ext, external_v, fenced_target, fire_v, fulfilled_v, group_views, held_v, later2_v, lease_expires_v, live_v, next_offer_v, on_v, one_origin, one_v, ostr, outs_v, prec_v, promise_create_v, promise_register_callback_v, promise_register_listener_v, promise_settle_v, record_run_v, released_v, resume_v, resumes_fold, resumes_inner, sat_add, schedule_create_v, schedule_delete_v, sends, settle_v, settled_work_v, status_v, strs, task_acquire_v, task_continue_v, task_create_v, task_fence_detached_v, task_fence_v, task_fulfill_v, task_halt_v, task_heartbeat_fold, task_heartbeat_v, task_release_v, task_suspend_v, trec_v, with_callbacks, works};

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
            r == external_v(self@),
    {
        has_target(&self.tags) || is_external_tag(&self.tags) || is_timer(&self.tags)
    }

    /// Pending and before its deadline. The deadline is a timer that fires first
    /// at its instant, so a pending promise is always live.
    pub fn live(&self) -> (r: bool)
        ensures
            r == (self.state == PromiseState::Pending),
            r == live_v(self@),
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
        ensures
            final(self)@ == fulfilled_v(old(self)@),
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
        ensures
            final(self)@ == acquired_v(old(self)@, version, pid@, ttl, now),
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
        ensures
            final(self)@ == released_v(old(self)@, at),
    {
        self.state = TaskState::Pending;
        self.pid = None;
        self.ttl = None;
        self.acquired_at = 0;
        self.retry_at = Some(at);
    }

    pub fn lease_expires(&self) -> (r: Time)
        ensures
            r == lease_expires_v(self@),
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
        r@ == prec_v(id@, p@),
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
    ensures
        r@ == trec_v(id@, t@),
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
/// through `mk` with a string literal, so a test can list them from this file.
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
        outs_v(r@) == echo_v(resp@, s@),
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
        outs_v(r@) == echo_v(res@, s@),
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
    ensures
        r@ == at_v(t, id@),
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
    ensures
        r == next_offer_v(due, now, t),
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
    ensures
        final(s)@ == settle_v(old(s)@, id@, state, value@, at),
{
    broadcast use group_views;
    let ghost s0 = *s;
    let ghost twin = settle_v(s0@, id@, state, ostr(value), at);
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
            assert(s@.promises == twin.promises);
        },
        None => {
            assert(s@.promises == twin.promises);
        },
    }
    assert(s@.promises == twin.promises);
    assert(s@.tasks == s0@.tasks);
    match s.tasks.get(id) {
        Some(t) => {
            if t.state != TaskState::Fulfilled {
                let mut u = copy(t);
                u.fulfill();
                s.tasks.insert(id.clone(), u);
                assert(s@.tasks == twin.tasks);
            }
        },
        None => {},
    }
    assert(s@.tasks == twin.tasks);
    assert(s@.schedules == twin.schedules);
    assert(s@.promises == twin.promises);
}

/// The work a settled promise starts: one resume per stored callback (the
/// awaited promise and its awaiter), and its listeners' unblocks.
fn settled_work(p: &Promise, awaited: &Id) -> (r: Vec<Work>)
    ensures
        works(r@) == settled_work_v(p@, awaited@),
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
            works(out@) == cs.take(i as int).map_values(|w: Chars| later2_v(awaited@, w)),
        decreases awaiters.len() - i,
    {
        let ghost before = works(out@);
        let w = Work::Later(Step::Objects(ids2(awaited, &awaiters[i])));
        assert(w@ == later2_v(awaited@, cs[i as int]));
        out.push(w);
        proof {
            assert(works(out@) == before.push(w@));
            assert(cs.take(i + 1) =~= cs.take(i as int).push(cs[i as int]));
            assert(cs.take(i + 1).map_values(|w: Chars| later2_v(awaited@, w)) == cs.take(i as int).map_values(|w: Chars| later2_v(awaited@, w)).push(later2_v(awaited@, cs[i as int])));
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
    pub fn promise_create(&self, req: &PromiseCreateReq, fenced: bool, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == promise_create_v(req@, s@, now),
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
        broadcast use group_views;
        if is_timer(&req.tags) && has_target(&req.tags) {
            return status(promise_res(400, None), mk("create: timer with target (400)"), s);
        }
        if let Some(d) = delay_of(&req.tags) {
            if d >= req.timeout_at {
                return status(promise_res(400, None), mk("create: delay past the deadline (400)"), s);
            }
            if !has_target(&req.tags) {
                return status(promise_res(400, None), mk("create: delay without a target (400)"), s);
            }
        }
        match s.promises.get(&req.id) {
            Some(p) => {
                proof {
                    if server_ok(*s) {
                        assert(promise_ok(s.promises@[req.id@]));
                    }
                }
                return echo(promise_res(200, Some(prec(&req.id, p))), mk("create: id exists (echo)"), s);
            },
            None => {},
        }
        let live = req.timeout_at > now;
        let born = if live {
            PromiseState::Pending
        } else if is_timer(&req.tags) {
            PromiseState::Resolved
        } else {
            PromiseState::RejectedTimedout
        };
        let p = Promise {
            state: born,
            value: Value::empty(),
            param: req.param.dup(),
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: echod_types::clone_tags(&req.tags),
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
        if has_target(&req.tags) {
            // A live targeted promise's task is runnable: offered to a worker
            // at once, or at its delay.
            let due = match delay_of(&req.tags) {
                Some(d) => if d > now { d } else { now },
                None => now,
            };
            let state = if live { TaskState::Pending } else { TaskState::Fulfilled };
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
        let ghost twin = promise_create_v(req@, s@, now);
        let mut marks = Vec::new();
        marks.push(match (fenced, live) {
            (false, true) => mk("promise created"),
            (false, false) => mk("promise created past its deadline"),
            (true, true) => mk("fence: promise created"),
            (true, false) => mk("fence: promise created past its deadline"),
        });
        if live && has_target(&req.tags) {
            marks.push(mk("task created pending"));
        }
        let outs = one(Out { resp: promise_res(200, Some(rec)), next: n, work, send: Vec::new(), marks });
        proof {
            assert(outs_v(outs@) == twin);
        }
        outs
    }

    fn promise_settle(&self, req: &PromiseSettleReq, fenced: bool, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == promise_settle_v(req@, s@, now),
    {
        broadcast use group_views;
        if !req.state.settable() {
            return status(promise_res(400, None), mk("settle: not a settled state (400)"), s);
        }
        let p = match s.promises.get(&req.id) {
            Some(p) => p,
            None => return status(promise_res(404, None), mk("settle: no such promise (404)"), s),
        };
        if !p.live() {
            return echo(promise_res(200, Some(prec(&req.id, p))), mk("settle: already settled (echo)"), s);
        }
        let work = settled_work(p, &req.id);
        let mut n = copy_server(s);
        settle(&mut n, &req.id, req.state, &req.value, now);
        let res = match n.promises.get(&req.id) {
            Some(q) => promise_res(200, Some(prec(&req.id, q))),
            None => promise_res(500, None), // unreachable: the promise exists
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
    fn held<'a>(&self, s: &'a Server, id: &Id, version: u64) -> (r: Result<&'a Task, u16>)
        ensures
            match r {
                Ok(t) => held_v(s@, id@, version) == Ok::<TaskV, u16>(t@),
                Err(code) => held_v(s@, id@, version) == Err::<TaskV, u16>(code),
            },
    {
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => {
                assert(!s@.tasks.contains_key(id@));
                assert(held_v(s@, id@, version) == Err::<TaskV, u16>(404));
                return Err(404);
            },
        };
        assert(s@.tasks.contains_key(id@));
        assert(s@.tasks[id@] == t@);
        let live = match s.promises.get(id) {
            Some(p) => p.live(),
            None => false,  // unreachable: a task's promise exists
        };
        assert(live == (s@.promises.contains_key(id@) && live_v(s@.promises[id@])));
        if t.state != TaskState::Acquired || !live || t.version != version {
            assert(held_v(s@, id@, version) == Err::<TaskV, u16>(409));
            return Err(409);
        }
        assert(held_v(s@, id@, version) == Ok::<TaskV, u16>(t@));
        Ok(t)
    }

    fn task_create(&self, pid: &String, ttl: Time, req: &PromiseCreateReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_create_v(pid@, ttl, req@, s@, now),
    {
        broadcast use group_views;
        if !has_target(&req.tags) || is_timer(&req.tags) {
            return status(claim_res(400, None, None), mk("task.create: not runnable, or a timer (400)"), s);
        }
        if delay_of(&req.tags).is_some() {
            return status(claim_res(400, None, None), mk("task.create: action with a delay (400)"), s);
        }
        match s.promises.get(&req.id) {
            Some(p) => {
                if !has_target(&p.tags) {
                    return status(claim_res(422, None, None), mk("task.create: promise exists, not a target (422)"), s);
                }
                let t = match s.tasks.get(&req.id) {
                    Some(t) => t,
                    None => return status(claim_res(409, None, None), mk("task.create: target without a task (409)"), s),  // unreachable
                };
                return match t.state {
                    TaskState::Fulfilled => echo(claim_res(200, Some(trec(&req.id, t)), Some(prec(&req.id, p))), mk("task.create: task done (echo)"), s),
                    TaskState::Pending => {
                        if t.version >= MAX_VERSION as u64 {
                            return status(claim_res(409, None, None), mk("task.create: version at its cap (409)"), s);
                        }
                        let mut n = copy_server(s);
                        let mut u = copy(t);
                        u.acquire(t.version + 1, pid.clone(), ttl, now);
                        let rec = claim_res(200, Some(trec(&req.id, &u)), Some(prec(&req.id, p)));
                        n.tasks.insert(req.id.clone(), u);
                        let mut work = Vec::new();
                        work.push(at(now.saturating_add(ttl), &req.id));
                        assert(works(work@) == seq![at_v(sat_add(now, ttl), req.id@)]);
                        assert(n@ == (ServerV { tasks: s@.tasks.insert(req.id@, u@), ..s@ }));
                        one(Out { resp: rec, next: n, work, send: Vec::new(), marks: marked(mk("task.create: pending task acquired")) })
                    },
                    _ => status(claim_res(409, None, None), mk("task.create: task held, suspended or halted (409)"), s),
                };
            },
            None => {},
        }
        let live = req.timeout_at > now;
        let p = Promise {
            state: if live { PromiseState::Pending } else { PromiseState::RejectedTimedout },
            value: Value::empty(),
            param: req.param.dup(),
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: echod_types::clone_tags(&req.tags),
            callbacks: PSet::empty(),
            listeners: PSet::empty(),
        };
        let mut t = Task { state: TaskState::Fulfilled, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Vec::new() };
        let mut work = Vec::new();
        if live {
            // Acquired by the caller right away: nothing to dispatch.
            t.acquire(1, pid.clone(), ttl, now);
            work.push(at(req.timeout_at, &req.id));
            work.push(at(now.saturating_add(ttl), &req.id));
        }
        assert(works(work@) == (if live { seq![at_v(req.timeout_at, req.id@), at_v(sat_add(now, ttl), req.id@)] } else { Seq::<Sched<InternalV>>::empty() }));
        let res = claim_res(200, Some(trec(&req.id, &t)), Some(prec(&req.id, &p)));
        let ghost pv = p@;
        let ghost tv = t@;
        let mut n = copy_server(s);
        n.promises.insert(req.id.clone(), p);
        n.tasks.insert(req.id.clone(), t);
        assert(n@ == (ServerV { promises: s@.promises.insert(req.id@, pv), tasks: s@.tasks.insert(req.id@, tv), ..s@ }));
        let mark = if live { mk("task created") } else { mk("task created past its deadline") };
        one(Out { resp: res, next: n, work, send: Vec::new(), marks: marked(mark) })
    }

    fn task_suspend(&self, req: &TaskSuspendReq, s: &Server) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_suspend_v(req.id@, req.version, strs(req.actions@.map(|a: echod_types::PromiseRegisterCallbackReq| a.awaited)), s@),
    {
        broadcast use group_views;
        let id = &req.id;
        let version = req.version;
        let ids: Vec<Id> = req.actions.iter().map(|a| a.awaited.clone()).collect();
        let ghost idv = strs(ids@);
        assert(idv.len() == ids@.len());
        if ids.len() == 0 || contains(&ids, id) {
            return status(status_res(400), mk("suspend: no awaited, or itself (400)"), s);
        }
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
                forall|a: int, b: int| 0 <= a < b < idv.len() && a < i ==> idv[a] != idv[b],
                forall|a: int| 0 <= a < i ==> origin(#[trigger] idv[a]) == origin(id@),
            decreases ids.len() - i,
        {
            let mut j = i + 1;
            while j < ids.len()
                invariant
                    i < j <= ids.len(),
                    idv == strs(ids@),
                    forall|b: int| i < b < j ==> idv[i as int] != idv[b],
                decreases ids.len() - j,
            {
                if ids[i] == ids[j] {
                    assert(idv[i as int] == ids@[i as int]@);
                    assert(idv[j as int] == ids@[j as int]@);
                    assert(idv[i as int] == idv[j as int]);
                    assert(!distinct(idv));
                    return status(status_res(400), mk("suspend: awaited twice (400)"), s);
                }
                j += 1;
            }
            if !same_origin(&ids[i], id) {
                assert(idv[i as int] == ids@[i as int]@);
                assert(origin(idv[i as int]) != origin(id@));
                assert(!all_in_origin(idv, id@));
                return status(status_res(400), mk("suspend: awaited in another origin (400)"), s);
            }
            i += 1;
        }
        assert(distinct(idv));
        assert(all_in_origin(idv, id@));
        let t = match self.held(s, id, version) {
            Err(code) => return status(status_res(code), if code == 404 { mk("suspend: no such task (404)") } else { mk("suspend: not held (409)") }, s),
            Ok(t) => t,
        };
        let mut settled = false;
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
                idv.len() > 0 && !idv.contains(id@) && distinct(idv) && all_in_origin(idv, id@),
                held_v(s@, id@, version) == Ok::<TaskV, u16>(t@),
                forall|a: int| 0 <= a < i ==> s@.promises.contains_key(#[trigger] idv[a]),
                forall|a: int| 0 <= a < i ==> external_v(s@.promises[#[trigger] idv[a]]),
                settled == any_settled(idv.take(i as int), s@),
            decreases ids.len() - i,
        {
            assert(idv[i as int] == ids@[i as int]@);
            match s.promises.get(&ids[i]) {
                None => {
                    assert(!s@.promises.contains_key(idv[i as int]));
                    assert(!all_present(idv, s@));
                    return status(status_res(422), mk("suspend: awaited missing (422)"), s);
                },
                Some(p) => {
                    assert(s@.promises[idv[i as int]] == p@);
                    if !p.external() {
                        assert(!external_v(s@.promises[idv[i as int]]));
                        assert(!all_external(idv, s@));
                        return status(status_res(422), mk("suspend: awaited not external (422)"), s);
                    }
                    let ghost was = settled;
                    settled = settled || !p.live();
                    proof {
                        assert(idv.take(i + 1) =~= idv.take(i as int).push(idv[i as int]));
                        if settled {
                            if was {
                                let k = choose|k: int| 0 <= k < idv.take(i as int).len() && !live_v(s@.promises[#[trigger] idv.take(i as int)[k]]);
                                assert(idv.take(i + 1)[k] == idv[k]);
                                assert(!live_v(s@.promises[idv.take(i + 1)[k]]));
                            } else {
                                assert(!live_v(s@.promises[idv.take(i + 1)[i as int]]));
                            }
                        } else {
                            assert forall|k: int| 0 <= k < idv.take(i + 1).len() implies live_v(s@.promises[#[trigger] idv.take(i + 1)[k]]) by {
                                if k < i {
                                    assert(idv.take(i as int)[k] == idv[k]);
                                }
                            }
                        }
                    }
                },
            }
            i += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        let mut n = copy_server(s);
        let mut u = copy(t);
        assert(all_present(idv, s@));
        assert(all_external(idv, s@));
        assert(settled == any_settled(idv, s@));
        if settled {
            // The task stays acquired and runs on; what it was told has been seen.
            u.resumes = Vec::new();
            assert(u@ == (TaskV { resumes: Seq::empty(), ..t@ }));
            n.tasks.insert(id.clone(), u);
            assert(n@ == (ServerV { tasks: s@.tasks.insert(id@, TaskV { resumes: Seq::empty(), ..t@ }), ..s@ }));
            let r = one(Out { resp: status_res(300), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("suspend: awaited already settled (300)")) });
            assert(outs_v(r@) == one_v(ResponseV::Status(300), ServerV { tasks: s@.tasks.insert(id@, TaskV { resumes: Seq::empty(), ..t@ }), ..s@ }, Seq::empty(), Seq::empty()));
            return r;
        }
        u.state = TaskState::Suspended;
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
                idv == strs(ids@),
                n@.promises == with_callbacks(s@.promises, idv.take(i as int), id@),
                n@.tasks == s@.tasks.insert(id@, TaskV { state: TaskState::Suspended, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Seq::empty(), ..t@ }),
                n@.schedules == s@.schedules,
            decreases ids.len() - i,
        {
            proof {
                assert(idv.take(i + 1) =~= idv.take(i as int).push(idv[i as int]));
                assert(idv.take(i + 1).drop_last() =~= idv.take(i as int));
            }
            assert(idv[i as int] == ids@[i as int]@);
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
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        assert(n@ == (ServerV { promises: with_callbacks(s@.promises, idv, id@), tasks: s@.tasks.insert(id@, TaskV { state: TaskState::Suspended, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Seq::empty(), ..t@ }), ..s@ }));
        let r = one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task suspended")) });
        assert(outs_v(r@) == one_v(ResponseV::Status(200), n@, Seq::empty(), Seq::empty()));
        r
    }

    fn task_fence(&self, req: &echod_types::TaskFenceReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_fence_v(req.id@, req.version, req.action@, s@, now),
    {
        broadcast use group_views;
        let id = &req.id;
        let version = req.version;
        let target = match &req.action {
            TaskFenceAction::Create(c) => &c.id,
            TaskFenceAction::Settle(st) => &st.id,
        };
        if target == id {
            return status(fence_res(400, None), mk("fence: targets its own task (400)"), s);
        }
        match &req.action {
            TaskFenceAction::Settle(st) => {
                if !same_origin(&st.id, id) {
                    return status(fence_res(400, None), mk("fence: settle in another origin (400)"), s);
                }
            },
            TaskFenceAction::Create(c) => {
                if !same_origin(&c.id, id) {
                    return self.task_fence_detached(id, version, c, s, now);
                }
            },
        }
        match self.held(s, id, version) {
            Err(code) => return status(fence_res(code, None), if code == 404 { mk("fence: no such task (404)") } else { mk("fence: not held, or stale version (409)") }, s),
            Ok(_) => {},
        }
        let create = matches!(req.action, TaskFenceAction::Create(_));
        let inner = match &req.action {
            TaskFenceAction::Create(c) => self.promise_create(c, true, s, now),
            TaskFenceAction::Settle(st) => self.promise_settle(st, true, s, now),
        };
        self.wrap_fence(inner, create)
    }

    /// The action's promise response, inside a fence that held.
    fn wrap_fence(&self, mut outs: Vec<Out>, create: bool) -> (r: Vec<Out>) {
        if outs.len() == 1 {
            let o = outs.remove(0);
            let Out { resp, next, work, send, marks } = o;
            let resp = match resp {
                Response::Promise(p) => {
                    let action = if create { TaskFenceInnerRes::Create(p) } else { TaskFenceInnerRes::Settle(p) };
                    fence_res(200, Some(action))
                },
                other => other,
            };
            return one(Out { resp, next, work, send, marks });
        }
        outs
    }

    /// A fence that creates a promise in another origin: a detached workflow.
    /// The create goes first, as a request of its own in its origin; then the
    /// fence's check on the task decides the answer. A stale fence still
    /// leaves the promise created.
    fn task_fence_detached(&self, id: &Id, version: u64, c: &PromiseCreateReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_fence_detached_v(id@, version, c@, s@, now),
    {
        broadcast use group_views;
        let mut outs = self.promise_create(c, true, s, now);
        assert(outs.len() == 1) by {
            assert(outs_v(outs@).len() == promise_create_v(c@, s@, now).len());
            assert(promise_create_v(c@, s@, now).len() == 1);
        }
        if outs.len() != 1 {
            return outs;  // unreachable: a create has one outcome
        }
        let o = outs.pop().unwrap();
        let ghost ov = o@;
        assert(ov == promise_create_v(c@, s@, now)[0]);
        let Out { resp, next, work, send, mut marks } = o;
        assert(next@ == ov.next);
        assert(works(work@) == ov.work);
        assert(sends(send@) == ov.send);
        let inner = match resp {
            Response::Promise(p) => p,
            other => return one(Out { resp: other, next, work, send, marks }),
        };
        match self.held(&next, id, version) {
            Err(code) => {
                marks.push(if code == 404 { mk("fence: detached create, no such task (404)") } else { mk("fence: detached create, not held (409)") });
                let r = one(Out { resp: fence_res(code, None), next, work, send, marks });
                assert(outs_v(r@) == one_v(ResponseV::Status(code), ov.next, ov.work, ov.send));
                r
            },
            Ok(_) => {
                marks.push(mk("fence: detached create"));
                let r = one(Out { resp: fence_res(200, Some(TaskFenceInnerRes::Create(inner))), next, work, send, marks });
                assert(outs_v(r@) == one_v(ov.resp, ov.next, ov.work, ov.send));
                r
            },
        }
    }

    fn task_heartbeat(&self, pid: &String, refs: &Vec<TaskRef>, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_heartbeat_v(pid@, refs@.map_values(|r: TaskRef| r@), s@, now),
    {
        broadcast use group_views;
        let ghost rv = refs@.map_values(|r: TaskRef| r@);
        let mut i = 1;
        while i < refs.len()
            invariant
                1 <= i,
                rv == refs@.map_values(|r: TaskRef| r@),
                forall|j: int| 1 <= j < i ==> origin(#[trigger] rv[j].id) == origin(rv[0].id),
            decreases refs.len() - i,
        {
            if !same_origin(&refs[i].id, &refs[0].id) {
                assert(rv[i as int] == refs@[i as int]@);
                assert(rv[0] == refs@[0]@);
                assert(origin(rv[i as int].id) != origin(rv[0].id));
                assert(!one_origin(rv));
                return status(status_res(400), mk("heartbeat: tasks in several origins (400)"), s);
            }
            i += 1;
        }
        assert(one_origin(rv));
        let mut n = copy_server(s);
        let mut work = Vec::new();
        let mut extended = false;
        let mut i = 0;
        while i < refs.len()
            invariant
                i <= refs.len(),
                rv == refs@.map_values(|r: TaskRef| r@),
                task_heartbeat_fold(pid@, rv.take(i as int), s@, s@, Seq::empty(), false, now) == (n@, works(work@), extended),
            decreases refs.len() - i,
        {
            proof {
                assert(rv.take(i + 1) =~= rv.take(i as int).push(rv[i as int]));
                assert(rv.take(i + 1).drop_last() =~= rv.take(i as int));
            }
            let r = &refs[i];
            assert(rv[i as int] == r@);
            let ghost (n1v, work1v, ext1v) = task_heartbeat_fold(pid@, rv.take(i as int), s@, s@, Seq::empty(), false, now);
            match self.held(s, &r.id, r.version) {
                Ok(t) => {
                    let mine = match &t.pid {
                        Some(holder) => *holder == *pid,
                        None => false,
                    };
                    assert(mine == (t@.pid is Some && t@.pid.unwrap() == pid@));
                    if mine {
                        let mut u = copy(t);
                        u.acquired_at = now;
                        assert(u@ == (TaskV { acquired_at: now, ..t@ }));
                        let expires = u.lease_expires();
                        assert(n@ == n1v);
                        assert(n@.tasks == n1v.tasks);
                        let ghost nt = n.tasks@;
                        n.tasks.insert(r.id.clone(), u);
                        assert(n.tasks@ == nt.insert(r.id@, u));
                        assert(n.tasks@.map_values(|t: Task| t@) == nt.map_values(|t: Task| t@).insert(r.id@, u@));
                        assert(n@.tasks == n1v.tasks.insert(r@.id, u@));
                        assert(n@.promises == n1v.promises);
                        assert(n@.schedules == n1v.schedules);
                        let ghost before = works(work@);
                        let w = at(expires, &r.id);
                        work.push(w);
                        assert(works(work@) == before.push(w@));
                        extended = true;
                        assert(n@ == (ServerV { tasks: n1v.tasks.insert(r@.id, u@), ..n1v }));
                    }
                },
                Err(_) => {},
            }
            i += 1;
        }
        proof {
            assert(rv.take(refs.len() as int) =~= rv);
        }
        // Always 200: a heartbeat says nothing about what it kept.
        let mark = if extended { mk("lease extended") } else { mk("heartbeat: nothing held by this worker") };
        one(Out { resp: status_res(200), next: n, work, send: Vec::new(), marks: marked(mark) })
    }

    fn schedule_create(&self, req: &ScheduleCreateReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == schedule_create_v(*self, req@, s@, now),
    {
        broadcast use group_views;
        if has_colon(&req.id) {
            return status(schedule_res(400, None), mk("schedule: id with a colon (400)"), s);
        }
        if !has_target(&req.promise_tags) {
            return status(schedule_res(400, None), mk("schedule: promises without a target (400)"), s);
        }
        if is_timer(&req.promise_tags) && has_target(&req.promise_tags) {
            return status(schedule_res(400, None), mk("schedule: timer with target (400)"), s);
        }
        if !cron_valid(&req.cron) || req.next_run_at < now {
            return status(schedule_res(400, None), mk("schedule: invalid cron (400)"), s);
        }
        match s.schedules.get(&req.id) {
            Some(c) => return echo(schedule_res(200, Some(c.dup())), mk("schedule: id exists (echo)"), s),
            None => {},
        }
        let c = Schedule {
            id: req.id.clone(),
            cron: req.cron.clone(),
            promise_id: req.promise_id.clone(),
            promise_timeout: req.promise_timeout,
            promise_param: req.promise_param.dup(),
            promise_tags: echod_types::clone_tags(&req.promise_tags),
            created_at: now,
            next_run_at: req.next_run_at,
            last_run_at: None,
        };
        let rec = schedule_res(200, Some(c.dup()));
        let mut n = copy_server(s);
        n.schedules.insert(req.id.clone(), c);
        let mut work = Vec::new();
        self.arm_fire(&mut work, &req.id, req.next_run_at, &req.promise_id);
        one(Out { resp: rec, next: n, work, send: Vec::new(), marks: marked(mk("schedule created")) })
    }

    /// `task.fence` with no action: the check alone, after a detached create.
    fn task_fence_check(&self, req: &TaskFenceCheckReq, s: &Server) -> (outs: Vec<Out>) {
        match self.held(s, &req.id, req.version) {
            Err(code) => status(status_res(code), if code == 404 { mk("fence: no such task (404)") } else { mk("fence: not held, or stale version (409)") }, s),
            Ok(_) => status(status_res(200), mk("fence check"), s),
        }
    }

    /// A request takes effect in `s` at time `now`: every allowed outcome.
    pub fn request(&self, op: &Request, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == ext(*self, op@, s@, now),
    {
        broadcast use group_views;
        match op {
            Request::PromiseCreate(c) => self.promise_create(c, false, s, now),
            Request::PromiseGet(q) => match s.promises.get(&q.id) {
                None => status(promise_res(404, None), mk("get promise: none (404)"), s),
                Some(p) => echo(promise_res(200, Some(prec(&q.id, p))), mk("get promise"), s),
            },
            Request::PromiseSettle(st) => self.promise_settle(st, false, s, now),
            Request::PromiseRegisterCallback(q) => self.promise_register_callback(&q.awaited, &q.awaiter, s),
            Request::PromiseRegisterListener(q) => self.promise_register_listener(&q.awaited, &q.address, s),
            Request::TaskGet(q) => match s.tasks.get(&q.id) {
                None => status(task_get_res(404, None), mk("get task: none (404)"), s),
                Some(t) => echo(task_get_res(200, Some(trec(&q.id, t))), mk("get task"), s),
            },
            Request::TaskCreate(q) => self.task_create(&q.pid, q.ttl, &q.action, s, now),
            Request::TaskAcquire(q) => self.task_acquire(&q.id, q.version, &q.pid, q.ttl, s, now),
            Request::TaskRelease(q) => self.task_release(&q.id, q.version, s, now),
            Request::TaskFulfill(q) => self.task_fulfill(&q.id, q.version, &q.action, s, now),
            Request::TaskHeartbeat(q) => self.task_heartbeat(&q.pid, &q.tasks, s, now),
            Request::TaskSuspend(q) => self.task_suspend(q, s),
            Request::TaskFence(q) => self.task_fence(q, s, now),
            Request::TaskFenceCheck(q) => self.task_fence_check(q, s),
            Request::TaskHalt(q) => self.task_halt(&q.id, s),
            Request::TaskContinue(q) => self.task_continue(&q.id, s, now),
            Request::ScheduleCreate(c) => self.schedule_create(c, s, now),
            Request::ScheduleGet(q) => match s.schedules.get(&q.id) {
                None => status(schedule_res(404, None), mk("get schedule: none (404)"), s),
                Some(c) => echo(schedule_res(200, Some(c.dup())), mk("get schedule"), s),
            },
            Request::ScheduleDelete(q) => self.schedule_delete(&q.id, s),
        }
    }

    fn promise_register_callback(&self, awaited: &Id, awaiter: &Id, s: &Server) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == promise_register_callback_v(awaited@, awaiter@, s@),
    {
        broadcast use group_views;
        if *awaited == *awaiter || !same_origin(awaited, awaiter) {
            return status(promise_res(400, None), mk("callback: itself or another origin (400)"), s);
        }
        let p = match s.promises.get(awaited) {
            Some(p) => p,
            None => return status(promise_res(404, None), mk("callback: no awaited promise (404)"), s),
        };
        let w = match s.promises.get(awaiter) {
            Some(w) => w,
            None => return status(promise_res(422, None), mk("callback: no awaiter promise (422)"), s),
        };
        if !s.tasks.contains_key(awaiter) || !p.external() {
            return status(promise_res(422, None), mk("callback: awaiter no task, or awaited not external (422)"), s);
        }
        let res = promise_res(200, Some(prec(awaited, p)));
        if !p.live() || !w.live() {
            return echo(res, mk("callback: one of them settled (echo)"), s);
        }
        let mut n = copy_server(s);
        let mut q = copy(p);
        q.callbacks.insert(awaiter.clone());
        n.promises.insert(awaited.clone(), q);
        one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("callback registered")) })
    }

    fn promise_register_listener(&self, awaited: &Id, address: &String, s: &Server) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == promise_register_listener_v(awaited@, address@, s@),
    {
        broadcast use group_views;
        if !address_valid(address) {
            return status(promise_res(400, None), mk("listener: bad address (400)"), s);
        }
        let p = match s.promises.get(awaited) {
            None => return status(promise_res(404, None), mk("listener: no such promise (404)"), s),
            Some(p) => p,
        };
        if !p.external() {
            return status(promise_res(422, None), mk("listener: promise not external (422)"), s);
        }
        let res = promise_res(200, Some(prec(awaited, p)));
        if !p.live() {
            return echo(res, mk("listener: promise settled (echo)"), s);
        }
        let mut n = copy_server(s);
        let mut q = copy(p);
        q.listeners.insert(address.clone());
        n.promises.insert(awaited.clone(), q);
        one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("listener registered")) })
    }

    fn task_acquire(&self, id: &Id, version: u64, pid: &String, ttl: Time, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_acquire_v(id@, version, pid@, ttl, s@, now),
    {
        broadcast use group_views;
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return status(claim_res(404, None, None), mk("acquire: no such task (404)"), s),
        };
        let p = match s.promises.get(id) {
            Some(p) => p,
            None => return status(claim_res(404, None, None), mk("acquire: no such task (404)"), s),  // unreachable
        };
        if t.state != TaskState::Pending || !p.live() || t.version != version || t.version >= MAX_VERSION as u64 {
            return status(claim_res(409, None, None), mk("acquire: not pending, or stale version (409)"), s);
        }
        let mut n = copy_server(s);
        let mut u = copy(t);
        u.acquire(t.version + 1, pid.clone(), ttl, now);
        let rec = claim_res(200, Some(trec(id, &u)), Some(prec(id, p)));
        n.tasks.insert(id.clone(), u);
        let mut work = Vec::new();
        work.push(at(now.saturating_add(ttl), id));
        one(Out { resp: rec, next: n, work, send: Vec::new(), marks: marked(mk("task acquired")) })
    }

    fn task_release(&self, id: &Id, version: u64, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_release_v(id@, version, s@, now),
    {
        broadcast use group_views;
        match self.held(s, id, version) {
            Err(code) => status(status_res(code), if code == 404 { mk("release: no such task (404)") } else { mk("release: not held (409)") }, s),
            Ok(t) => {
                let mut n = copy_server(s);
                let mut u = copy(t);
                u.release(now);
                n.tasks.insert(id.clone(), u);
                let mut work = Vec::new();
                work.push(at(now, id));
                one(Out { resp: status_res(200), next: n, work, send: Vec::new(), marks: marked(mk("task released")) })
            },
        }
    }

    fn task_fulfill(&self, id: &Id, version: u64, action: &PromiseSettleReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_fulfill_v(id@, version, action@, s@, now),
    {
        broadcast use group_views;
        if !action.state.settable() {
            return status(promise_res(400, None), mk("fulfill: not a settled state (400)"), s);
        }
        match self.held(s, id, version) {
            Err(code) => return status(promise_res(code, None), if code == 404 { mk("fulfill: no such task (404)") } else { mk("fulfill: not held (409)") }, s),
            Ok(_) => {},
        }
        let work = match s.promises.get(id) {
            Some(p) => settled_work(p, id),
            None => Vec::new(),
        };
        let mut n = copy_server(s);
        settle(&mut n, id, action.state, &action.value, now);
        let res = match n.promises.get(id) {
            Some(q) => promise_res(200, Some(prec(id, q))),
            None => promise_res(500, None), // unreachable: held checked the promise
        };
        one(Out { resp: res, next: n, work, send: Vec::new(), marks: marked(mk("task fulfilled")) })
    }

    fn task_halt(&self, id: &Id, s: &Server) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_halt_v(id@, s@),
    {
        broadcast use group_views;
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return status(status_res(404), mk("halt: no such task (404)"), s),
        };
        match t.state {
            TaskState::Fulfilled => status(status_res(409), mk("halt: task done (409)"), s),
            TaskState::Halted => status(status_res(200), mk("halt: already halted (echo)"), s),
            _ => {
                let mut n = copy_server(s);
                let mut u = copy(t);
                u.state = TaskState::Halted;
                u.pid = None;
                u.ttl = None;
                u.acquired_at = 0;
                u.retry_at = None;
                n.tasks.insert(id.clone(), u);
                one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task halted")) })
            },
        }
    }

    fn task_continue(&self, id: &Id, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == task_continue_v(id@, s@, now),
    {
        broadcast use group_views;
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return status(status_res(404), mk("continue: no such task (404)"), s),
        };
        let live = match s.promises.get(id) {
            Some(p) => p.live(),
            None => false,
        };
        if t.state != TaskState::Halted || !live {
            return status(status_res(409), mk("continue: not halted (409)"), s);
        }
        let mut n = copy_server(s);
        let mut u = copy(t);
        u.state = TaskState::Pending;
        u.retry_at = Some(now);
        n.tasks.insert(id.clone(), u);
        let mut work = Vec::new();
        work.push(at(now, id));
        one(Out { resp: status_res(200), next: n, work, send: Vec::new(), marks: marked(mk("task continued")) })
    }

    fn schedule_delete(&self, id: &Id, s: &Server) -> (outs: Vec<Out>)
        ensures
            outs_v(outs@) == schedule_delete_v(id@, s@),
    {
        broadcast use group_views;
        match s.schedules.get(id) {
            None => status(status_res(404), mk("delete schedule: none (404)"), s),
            Some(_) => {
                let mut n = copy_server(s);
                n.schedules.remove(id);
                one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("schedule deleted")) })
            },
        }
    }

    /// A suspended task resumes when a promise it awaits has settled; any
    /// other task is told, when it next runs (Lean's `resumeOne`). The
    /// callback is spent either way.
    fn resume(&self, n: &mut Server, awaited: &Id, awaiter: &Id, now: Time, marks: &mut Vec<&'static str>)
        ensures
            final(n)@ == resume_v(old(n)@, awaited@, awaiter@, now),
    {
        broadcast use group_views;
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
                    TaskState::Suspended => {
                        let mut u = copy(t);
                        u.state = TaskState::Pending;
                        u.resumes = ids1(awaited);
                        u.retry_at = Some(since);
                        n.tasks.insert(awaiter.clone(), u);
                        marks.push(mk("task resumed"));
                    },
                    TaskState::Fulfilled => {},
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
    pub fn objects(&self, ids: &Vec<Id>, s: &Server, now: Time) -> (r: InOut)
        ensures
            r@ == on_v(*self, strs(ids@), s@, now),
    {
        broadcast use group_views;
        let ghost idv = strs(ids@);
        let mut n = copy_server(s);
        let mut work = Vec::new();
        let mut send = Vec::new();
        let mut marks = Vec::new();
        // A promise past its deadline times out (a timer promise resolves).
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
                deadlines_fold(idv.take(i as int), s@, Seq::empty(), now) == (n@, works(work@)),
            decreases ids.len() - i,
        {
            proof {
                assert(idv.take(i + 1) =~= idv.take(i as int).push(idv[i as int]));
                assert(idv.take(i + 1).drop_last() =~= idv.take(i as int));
            }
            let id = &ids[i];
            let found = match n.promises.get(id) {
                Some(p) => Some(copy(p)),
                None => None,
            };
            match found {
                Some(p) => {
                    if p.live() && now >= p.timeout_at {
                        let timer = is_timer(&p.tags);
                        let state = if timer { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
                        marks.push(if timer { mk("timer promise resolved") } else { mk("promise timed out") });
                        let r = settled_work(&p, id);
                        let empty = Value::empty();
                        settle(&mut n, id, state, &empty, p.timeout_at);
                        push_all(&mut work, &r);
                    }
                },
                None => {},
            }
            i += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        let ghost n1 = n@;
        let ghost work1 = works(work@);
        // A callback on a settled promise is spent: its awaiter resumes.
        let mut a = 0;
        while a < ids.len()
            invariant
                a <= ids.len(),
                idv == strs(ids@),
                works(work@) == work1,
                n@ == resumes_fold(idv.take(a as int), idv, n1, now),
            decreases ids.len() - a,
        {
            proof {
                assert(idv.take(a + 1) =~= idv.take(a as int).push(idv[a as int]));
                assert(idv.take(a + 1).drop_last() =~= idv.take(a as int));
            }
            let ghost na = n@;
            let mut w = 0;
            while w < ids.len()
                invariant
                    w <= ids.len(),
                    a < ids.len(),
                    idv == strs(ids@),
                    works(work@) == work1,
                    n@ == resumes_inner(idv[a as int], idv.take(w as int), na, now),
                decreases ids.len() - w,
            {
                proof {
                    assert(idv.take(w + 1) =~= idv.take(w as int).push(idv[w as int]));
                    assert(idv.take(w + 1).drop_last() =~= idv.take(w as int));
                }
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
            proof {
                assert(idv.take(ids.len() as int) =~= idv);
            }
            a += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        let ghost n2 = n@;
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
                due_fold(*self, idv.take(i as int), n2, work1, Seq::empty(), now) == (n@, works(work@), sends(send@)),
            decreases ids.len() - i,
        {
            proof {
                assert(idv.take(i + 1) =~= idv.take(i as int).push(idv[i as int]));
                assert(idv.take(i + 1).drop_last() =~= idv.take(i as int));
            }
            let ghost (n1v, work1v, send1v) = due_fold(*self, idv.take(i as int), n2, work1, Seq::empty(), now);
            let id = &ids[i];
            assert(idv[i as int] == id@);
            let ghost tasks2 = if n1v.tasks.contains_key(id@) && n1v.tasks[id@].state == TaskState::Acquired && now >= lease_expires_v(n1v.tasks[id@]) {
                n1v.tasks.insert(id@, released_v(n1v.tasks[id@], lease_expires_v(n1v.tasks[id@])))
            } else {
                n1v.tasks
            };
            let ghost n2v = ServerV { tasks: tasks2, ..n1v };
            // A task past its lease is reclaimed, offered again from the
            // lease's end on (Lean's `TaskObject.lapse`).
            assert(n@ == n1v);
            match n.tasks.get(id) {
                Some(t) => {
                    if t.state == TaskState::Acquired && now >= t.lease_expires() {
                        let mut u = copy(t);
                        u.release(t.lease_expires());
                        assert(u@ == released_v(n1v.tasks[id@], lease_expires_v(n1v.tasks[id@])));
                        let ghost nt = n.tasks@;
                        n.tasks.insert(id.clone(), u);
                        assert(n.tasks@ == nt.insert(id@, u));
                        assert(n@.tasks == n1v.tasks.insert(id@, u@));
                        assert(n@.tasks == tasks2);
                        marks.push(mk("lease expired"));
                    } else {
                        assert(n@.tasks == tasks2);
                    }
                },
                None => {
                    assert(n@.tasks == tasks2);
                },
            }
            assert(n@.promises == n2v.promises);
            assert(n@ == n2v);
            let ghost told = n2v.promises.contains_key(id@) && !live_v(n2v.promises[id@]) && n2v.promises[id@].listeners.len() > 0;
            let ghost (n3v, send3v) = if told {
                let p = n2v.promises[id@];
                let rec = prec_v(id@, p);
                let unblocks = pset_seq(p.listeners).map_values(|a: Chars| DispatchV::Unblock { address: a, promise: rec });
                (ServerV { promises: n2v.promises.insert(id@, PromiseV { listeners: Set::empty(), ..p }), ..n2v }, send1v + unblocks)
            } else {
                (n2v, send1v)
            };
            // A settled promise's listeners are told, once.
            let found = match n.promises.get(id) {
                Some(p) => Some(copy(p)),
                None => None,
            };
            match found {
                Some(p) => {
                    if !p.live() {
                        let addrs = p.listeners.to_vec();
                        assert(strs(addrs@).len() == addrs@.len());
                        proof {
                            axiom_pset_seq(p.listeners@);
                        }
                        assert(pset_seq(p.listeners@).len() == p.listeners@.len());
                        assert(addrs@.len() == p@.listeners.len());
                        if addrs.len() > 0 {
                            let rec = prec(id, &p);
                            let ghost ls = pset_seq(p.listeners@);
                            let ghost send0 = sends(send@);
                            let mut j = 0;
                            while j < addrs.len()
                                invariant
                                    j <= addrs.len(),
                                    strs(addrs@) == ls,
                                    rec@ == prec_v(id@, p@),
                                    sends(send@) == send0 + ls.take(j as int).map_values(|a: Chars| DispatchV::Unblock { address: a, promise: rec@ }),
                                decreases addrs.len() - j,
                            {
                                let ghost before = sends(send@);
                                let d = Dispatch::Unblock { address: addrs[j].clone(), promise: copy(&rec) };
                                assert(ls[j as int] == addrs@[j as int]@);
                                assert(d@ == (DispatchV::Unblock { address: ls[j as int], promise: rec@ }));
                                send.push(d);
                                proof {
                                    assert(sends(send@) == before.push(d@));
                                    assert(ls.take(j + 1) =~= ls.take(j as int).push(ls[j as int]));
                                    let g = |a: Chars| DispatchV::Unblock { address: a, promise: rec@ };
                                    assert(ls.take(j + 1).map_values(g) == ls.take(j as int).map_values(g).push(g(ls[j as int])));
                                    assert(send0 + ls.take(j as int).map_values(g).push(g(ls[j as int])) =~= (send0 + ls.take(j as int).map_values(g)).push(g(ls[j as int])));
                                }
                                j += 1;
                            }
                            proof {
                                assert(ls.take(addrs.len() as int) =~= ls);
                            }
                            let mut q = copy(&p);
                            q.listeners = PSet::empty();
                            assert(q@ == (PromiseV { listeners: Set::empty(), ..n2v.promises[id@] }));
                            assert(n@ == n2v);
                            let ghost np = n.promises@;
                            n.promises.insert(id.clone(), q);
                            assert(n.promises@ == np.insert(id@, q));
                            assert(np.map_values(|p: Promise| p@) == n2v.promises);
                            assert(n.promises@.map_values(|p: Promise| p@) == np.map_values(|p: Promise| p@).insert(id@, q@));
                            marks.push(mk("listeners told"));
                            assert(told);
                            assert(n@.promises == n2v.promises.insert(id@, PromiseV { listeners: Set::empty(), ..n2v.promises[id@] }));
                            assert(n@ == n3v);
                            assert(sends(send@) == send3v);
                        } else {
                            assert(!told);
                        }
                    } else {
                        assert(!told);
                    }
                },
                None => {
                    assert(!told);
                },
            }
            assert(n@ == n3v);
            assert(sends(send@) == send3v);
            let ghost livev = n3v.promises.contains_key(id@) && live_v(n3v.promises[id@]);
            let ghost retryv = n3v.tasks.contains_key(id@) && {
                let t = n3v.tasks[id@];
                t.state == TaskState::Pending && t.retry_at is Some && t.retry_at.unwrap() <= now && livev
            };
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
                    if t.state == TaskState::Pending && due && live {
                        let mut u = copy(t);
                        let again = match t.retry_at {
                            Some(r) => next_offer(r, now, self.retry_timeout),
                            None => now.saturating_add(self.retry_timeout),
                        };
                        u.retry_at = Some(again);
                        let version = u.version;
                        assert(u@ == (TaskV { retry_at: Some(next_offer_v(n3v.tasks[id@].retry_at.unwrap(), now, self.retry_timeout)), ..n3v.tasks[id@] }));
                        n.tasks.insert(id.clone(), u);
                        assert(n@.tasks == n3v.tasks.insert(id@, u@));
                        let ghost before_s = sends(send@);
                        let ghost before_w = works(work@);
                        let d = Dispatch::Execute { id: id.clone(), version };
                        send.push(d);
                        let w = at(again, id);
                        work.push(w);
                        assert(sends(send@) == before_s.push(d@));
                        assert(works(work@) == before_w.push(w@));
                        marks.push(mk("task dispatched"));
                        assert(retryv);
                    }
                },
                None => {},
            }
            assert(retryv ==> n@ == (ServerV { tasks: n3v.tasks.insert(id@, TaskV { retry_at: Some(next_offer_v(n3v.tasks[id@].retry_at.unwrap(), now, self.retry_timeout)), ..n3v.tasks[id@] }), ..n3v }));
            assert(!retryv ==> n@ == n3v);
            i += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        InOut { next: n, work, send, marks, pending: false }
    }

    /// The work that fires `schedule`'s occurrence at `at`: later, from `at`
    /// on, and a timer at `at + fire_within`, by which it is owed. Whichever
    /// runs first fires it; the other finds the schedule moved on and does
    /// nothing. With `fire_within` zero, the timer alone.
    fn arm_fire(&self, work: &mut Vec<Work>, schedule: &Id, at_: Time, template: &String)
        ensures
            works(final(work)@) == works(old(work)@) + arm_fire_v(*self, schedule@, at_, template@),
    {
        broadcast use group_views;
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
    pub fn fire(&self, schedule: &Id, at_: Time, promise: &Id, s: &Server, now: Time) -> (r: InOut)
        ensures
            r@ == fire_v(*self, schedule@, at_, promise@, s@, now),
    {
        broadcast use group_views;
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
        let ghost cv = c@;
        assert(s@.schedules[schedule@] == cv);
        let mut marks = Vec::new();
        let mut work = Vec::new();
        let mut n = copy_server(s);
        if s.promises.contains_key(promise) {
            marks.push(mk("schedule: occurrence exists"));
            assert(n@ == s@);
            assert(works(work@) == Seq::<Sched<InternalV>>::empty());
        } else {
            let timeout_at = at_.saturating_add(c.promise_timeout);
            let tags = echod_types::clone_tags(&c.promise_tags);
            let timer = is_timer(&tags);
            let target = has_target(&tags);
            let delay = delay_of(&tags);
            // Born live at `at`, or settled at its deadline: the deadline is
            // `at` itself when the timeout is zero, else before `now`.
            let live_now = timeout_at > now;
            let live_at = timeout_at > at_;
            let born = if live_now { PromiseState::Pending } else if timer { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
            let p = Promise {
                state: born,
                value: Value::empty(),
                param: c.promise_param.dup(),
                timeout_at,
                created_at: if live_at { at_ } else { timeout_at },
                settled_at: if live_now { None } else { Some(timeout_at) },
                tags: echod_types::clone_tags(&tags),
                callbacks: PSet::empty(),
                listeners: PSet::empty(),
            };
            n.promises.insert(promise.clone(), p);
            if live_now {
                work.push(at(timeout_at, promise));
            }
            if target && !timer {
                let due = match delay {
                    Some(d) => if d > at_ { d } else { at_ },
                    None => at_,
                };
                let state = if live_now { TaskState::Pending } else { TaskState::Fulfilled };
                let retry_at = if live_now { Some(due) } else { None };
                n.tasks.insert(promise.clone(), Task { state, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at, resumes: Vec::new() });
                if live_now {
                    work.push(at(due, promise));
                }
            }
            marks.push(if live_now { mk("schedule fired") } else { mk("schedule fired past the occurrence's deadline") });
            assert(n@.promises == s@.promises.insert(promise@, p@));
            assert(n@.schedules == s@.schedules);
            assert(works(work@) == (if live_now { seq![at_v(timeout_at, promise@)] } else { Seq::<Sched<InternalV>>::empty() }) + (if target && !timer && live_now { seq![at_v(match delay { Some(d) => if d > at_ { d } else { at_ }, None => at_ }, promise@)] } else { Seq::<Sched<InternalV>>::empty() }));
        }
        let ghost n1v = n@;
        let ghost work1v = works(work@);
        if self.fire_within == 0 {
            Resonate::record_run(&mut n, c, schedule, at_);
            assert(n@ == (ServerV { schedules: n1v.schedules.insert(schedule@, record_run_v(cv, at_)), ..n1v }));
            self.arm_fire(&mut work, schedule, next_cron(&c.cron, at_), &c.promise_id);
            assert(works(work@) == work1v + arm_fire_v(*self, schedule@, record_run_v(cv, at_).next_run_at, cv.promise_id));
        } else {
            let step = Step::Advance { schedule: schedule.clone(), at: at_, promise: promise.clone() };
            let ghost sv = step@;
            work.push(Work::Later(copy_step(&step)));
            work.push(Work::Timer(at_.saturating_add(self.fire_within), step));
            assert(works(work@) == work1v + seq![Sched::Later(sv), Sched::Timer(sat_add(at_, self.fire_within), sv)]) by {
                assert(works(work@) =~= work1v + seq![Sched::Later(sv), Sched::Timer(sat_add(at_, self.fire_within), sv)]);
            }
        }
        InOut { next: n, work, send: Vec::new(), marks, pending: false }
    }

    /// The schedule records its run at `at` and arms the next.
    fn record_run(n: &mut Server, c: &Schedule, schedule: &Id, at_: Time)
        ensures
            final(n)@ == (ServerV { schedules: old(n)@.schedules.insert(schedule@, record_run_v(c@, at_)), ..old(n)@ }),
    {
        broadcast use group_views;
        let mut d = copy(c);
        d.last_run_at = Some(at_);
        d.next_run_at = next_cron(&c.cron, at_);
        n.schedules.insert(schedule.clone(), d);
    }

    /// The second half of a sweeping server's fire: the run at `at` recorded
    /// on `schedule` and the next occurrence armed. A schedule that is gone,
    /// or has moved on (the fire refired and advanced already), is left as it
    /// is.
    pub fn advance(&self, schedule: &Id, at_: Time, promise: &Id, s: &Server, now: Time) -> (r: InOut)
        ensures
            r@ == advance_v(*self, schedule@, at_, promise@, s@, now),
    {
        broadcast use group_views;
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
