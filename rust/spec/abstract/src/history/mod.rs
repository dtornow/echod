//! Adapter from the protocol model to the client-history checker.
//!
//! This module converts handler outcomes to checker outcomes, declares
//! coverage marks, and suggests requests worth trying next. None of it
//! decides protocol behavior.

use vstd::prelude::*;

use echod_rover::{
    Action, Explore, ExternalOutcome, InternalOutcome, Model, Sched, Time,
};
use echod_types::{
    PromiseCreateReq, PromiseGetReq, PromiseRegisterCallbackReq, PromiseRegisterListenerReq,
    PromiseSettleReq, PromiseState, Request, Response, ScheduleCreateReq, ScheduleDeleteReq,
    ScheduleGetReq, Tags, TaskAcquireReq, TaskContinueReq, TaskCreateReq, TaskFenceAction,
    TaskFenceReq, TaskFulfillReq, TaskGetReq, TaskHaltReq, TaskHeartbeatReq, TaskRef,
    TaskReleaseReq, TaskState, TaskSuspendReq, Value,
};

mod footprint;

pub use footprint::{next_cron, Key};

use super::machine::*;
use footprint::origin;
#[cfg(verus_keep_ghost)]
use super::view::{as_sched, group_views, sched_v, works};

/// Every mark the spec can put on an outcome, so a coverage report can show
/// the ones no run reached. `resonate_marks.rs` checks it against `machine`.
pub const MARKS: &[&str] = &[
    "acquire: no such task (404)",
    "acquire: not pending, or stale version (409)",
    "callback registered",
    "callback: awaiter not runnable, or awaited not awaitable (422)",
    "callback: itself or another origin (400)",
    "callback: no awaited promise (404)",
    "callback: no awaiter promise (422)",
    "callback: one of them settled (echo)",
    "continue: no such task (404)",
    "continue: not halted (409)",
    "create: id exists (echo)",
    "create: timer with target (400)",
    "delete schedule: none (404)",
    "fence check",
    "fence: create in another origin (400)",
    "fence: no such task (404)",
    "fence: not held, or stale version (409)",
    "fence: promise created",
    "fence: promise created past its deadline",
    "fence: promise settled",
    "fence: settle in another origin (400)",
    "fence: targets its own task (400)",
    "fulfill: no such task (404)",
    "fulfill: not a settled state (400)",
    "fulfill: not held (409)",
    "get promise",
    "get promise: none (404)",
    "get schedule",
    "get schedule: none (404)",
    "get task",
    "get task: none (404)",
    "halt: already halted (echo)",
    "halt: no such task (404)",
    "halt: task done (409)",
    "heartbeat: nothing held by this worker",
    "heartbeat: tasks in several origins (400)",
    "lease expired",
    "lease extended",
    "listener registered",
    "listener: no such promise (404)",
    "listener: promise not awaitable (422)",
    "listener: promise settled (echo)",
    "listeners told",
    "promise created",
    "promise created past its deadline",
    "promise settled",
    "promise timed out",
    "release: no such task (404)",
    "release: not held (409)",
    "resume noted on a running task",
    "schedule created",
    "schedule deleted",
    "schedule fired",
    "schedule fired past the occurrence's deadline",
    "schedule advanced",
    "schedule: id exists (echo)",
    "schedule: occurrence exists",
    "schedule: timer with target (400)",
    "settle: already settled (echo)",
    "settle: no such promise (404)",
    "settle: not a settled state (400)",
    "settled with callbacks or listeners",
    "suspend: awaited already settled (300)",
    "suspend: awaited in another origin (400)",
    "suspend: awaited missing (422)",
    "suspend: awaited not awaitable (422)",
    "suspend: awaited twice (400)",
    "suspend: no awaited, or itself (400)",
    "suspend: no such task (404)",
    "suspend: not held (409)",
    "task acquired",
    "task continued",
    "task created",
    "task created past its deadline",
    "task created pending",
    "task dispatched",
    "task fulfilled",
    "task halted",
    "task released",
    "task resumed",
    "task suspended",
    "task.create: not runnable, or a timer (400)",
    "task.create: pending task acquired",
    "task.create: promise exists, not a target (422)",
    "task.create: target without a task (409)",
    "task.create: task done (echo)",
    "task.create: task held, suspended or halted (409)",
    "timer promise resolved",
];

/// No tags at all: an internal promise.
pub fn plain() -> Tags {
    Vec::new()
}

fn target_tags() -> Tags {
    vec![("resonate:target".into(), "sim://worker".into())]
}

fn create(id: &Id, timeout_at: Time) -> PromiseCreateReq {
    PromiseCreateReq { id: id.clone(), timeout_at, param: Value::empty(), tags: plain() }
}

fn targeted(id: &Id, timeout_at: Time) -> PromiseCreateReq {
    PromiseCreateReq { id: id.clone(), timeout_at, param: Value::empty(), tags: target_tags() }
}

fn settle(id: &Id) -> PromiseSettleReq {
    PromiseSettleReq { id: id.clone(), state: PromiseState::Resolved, value: Value { headers: Vec::new(), data: Some("v".into()) } }
}

/// A schedule whose occurrences are tasks in the origin its id names:
/// `sa` fires into `a`. (A schedule's id has no `:`, so it cannot carry an
/// origin of its own the way a promise id does.)
fn schedule(id: &Id, cron: &str, timeout: Time, now: Time) -> ScheduleCreateReq {
    let into = id.strip_prefix('s').unwrap_or(id);
    let cron = cron.to_string();
    ScheduleCreateReq {
        id: id.clone(),
        cron: cron.clone(),
        promise_id: format!("{into}:{{{{.id}}}}.{{{{.timestamp}}}}"),
        promise_timeout: timeout,
        promise_param: Value::empty(),
        promise_tags: target_tags(),
        next_run_at: next_cron(&cron, now),
    }
}

fn heartbeat(pid: &str, refs: &[(&Id, u64)]) -> Request {
    Request::TaskHeartbeat(TaskHeartbeatReq { pid: pid.into(), tasks: refs.iter().map(|(id, v)| TaskRef { id: (*id).clone(), version: *v }).collect() })
}

fn suspend(id: &Id, version: u64, awaited: &Id) -> Request {
    Request::TaskSuspend(TaskSuspendReq { id: id.clone(), version, actions: vec![PromiseRegisterCallbackReq { awaited: awaited.clone(), awaiter: id.clone() }] })
}

impl Explore for ServerConfig {
    /// Actions that reach the edges of what the state allows: fences and
    /// heartbeats at the current version and a stale one, the clock moved to
    /// just before and exactly at each deadline, promises settled while a task
    /// awaits them, settles and creates repeated, halts and continues in every
    /// task state, schedules fired and deleted.
    fn suggest(&self, s: &Store, now: Time) -> Vec<(Action<Request>, &'static str)> {
        let mut out = Vec::new();
        let mut push = |a, why| out.push((a, why));
        let siblings = |id: &Id| -> Vec<&Id> { s.promises.iter().map(|(k, _)| k).filter(|k| *k != id && origin(k) == origin(id)).collect() };
        let mut held: Vec<(&Id, u64)> = Vec::new();
        for (id, t) in s.tasks.iter() {
            let v = t.version;
            match t.state {
                TaskState::Acquired => {
                    held.push((id, v));
                    let pid = t.pid.clone().unwrap_or_default();
                    let fresh = format!("{}:child{}", origin(id), v);
                    push(Action::Request(Request::TaskFence(TaskFenceReq { id: id.clone(), version: v, action: TaskFenceAction::Create(create(&fresh, now + 50)) })), "fence a create at the held version");
                    push(Action::Request(Request::TaskFence(TaskFenceReq { id: id.clone(), version: v.wrapping_sub(1), action: TaskFenceAction::Create(create(&fresh, now + 50)) })), "fence at a stale version");
                    push(Action::Request(Request::TaskFence(TaskFenceReq { id: id.clone(), version: v, action: TaskFenceAction::Create(targeted(&format!("elsewhere:{id}"), now + 50)) })), "fence a create in another origin");
                    push(Action::Request(Request::TaskFence(TaskFenceReq { id: id.clone(), version: v.wrapping_sub(1), action: TaskFenceAction::Create(create(&format!("elsewhere:{id}.stale"), now + 50)) })), "fence a create in another origin at a stale version");
                    for p in siblings(id) {
                        push(Action::Request(Request::TaskFence(TaskFenceReq { id: id.clone(), version: v, action: TaskFenceAction::Settle(settle(p)) })), "fence a settle at the held version");
                        push(Action::Request(suspend(id, v, p)), "suspend on a promise");
                        push(Action::Request(Request::PromiseRegisterCallback(PromiseRegisterCallbackReq { awaited: p.clone(), awaiter: id.clone() })), "register a callback");
                    }
                    push(Action::Request(heartbeat(&pid, &[(id, v)])), "heartbeat the held task");
                    push(Action::Request(heartbeat("intruder", &[(id, v)])), "heartbeat as another worker");
                    push(Action::Request(Request::TaskFulfill(TaskFulfillReq { id: id.clone(), version: v, action: settle(id) })), "fulfill at the held version");
                    push(Action::Request(Request::TaskFulfill(TaskFulfillReq { id: id.clone(), version: v.wrapping_sub(1), action: settle(id) })), "fulfill at a stale version");
                    push(Action::Request(Request::TaskRelease(TaskReleaseReq { id: id.clone(), version: v })), "release the held task");
                    push(Action::Request(Request::TaskHalt(TaskHaltReq { id: id.clone() })), "halt the held task");
                    // Only a lease that ends before its promise's deadline can
                    // expire: at the deadline the task is done.
                    let end = t.lease_timeout_at();
                    if s.promises.get(id).is_some_and(|p| end < p.timeout_at) {
                        push(Action::Clock(end.saturating_sub(1)), "clock to just before a lease ends");
                        push(Action::Clock(end), "clock to a lease end");
                    }
                }
                TaskState::Pending => {
                    push(Action::Request(Request::TaskAcquire(TaskAcquireReq { id: id.clone(), version: v, pid: "w1".into(), ttl: 10 })), "acquire a pending task");
                    push(Action::Request(Request::TaskAcquire(TaskAcquireReq { id: id.clone(), version: v.wrapping_sub(1), pid: "w1".into(), ttl: 10 })), "acquire at a stale version");
                    push(Action::Request(Request::TaskCreate(TaskCreateReq { pid: "w2".into(), ttl: 20, action: targeted(id, now + 50) })), "task.create a pending task");
                    push(Action::Request(Request::TaskHalt(TaskHaltReq { id: id.clone() })), "halt a pending task");
                    push(Action::Request(Request::TaskContinue(TaskContinueReq { id: id.clone() })), "continue a pending task");
                    if let Some(r) = t.retry_timeout_at {
                        if r > now && s.promises.get(id).is_some_and(|p| r < p.timeout_at) {
                            push(Action::Clock(r), "clock to a redispatch");
                        }
                    }
                }
                TaskState::Suspended => {
                    push(Action::Request(Request::TaskAcquire(TaskAcquireReq { id: id.clone(), version: v, pid: "w1".into(), ttl: 10 })), "acquire a suspended task");
                    push(Action::Request(Request::TaskHalt(TaskHaltReq { id: id.clone() })), "halt a suspended task");
                }
                TaskState::Halted => {
                    push(Action::Request(Request::TaskContinue(TaskContinueReq { id: id.clone() })), "continue a halted task");
                    push(Action::Request(Request::TaskHalt(TaskHaltReq { id: id.clone() })), "halt a halted task");
                    push(Action::Request(Request::TaskAcquire(TaskAcquireReq { id: id.clone(), version: v, pid: "w1".into(), ttl: 10 })), "acquire a halted task");
                    push(Action::Request(Request::TaskCreate(TaskCreateReq { pid: "w2".into(), ttl: 20, action: targeted(id, now + 50) })), "task.create a halted task");
                }
                TaskState::Fulfilled => {
                    push(Action::Request(Request::TaskFulfill(TaskFulfillReq { id: id.clone(), version: v, action: settle(id) })), "fulfill a fulfilled task");
                    push(Action::Request(Request::TaskHalt(TaskHaltReq { id: id.clone() })), "halt a fulfilled task");
                    push(Action::Request(Request::TaskCreate(TaskCreateReq { pid: "w2".into(), ttl: 20, action: targeted(id, now + 50) })), "task.create a fulfilled task");
                }
            }
        }
        for (i, a) in held.iter().enumerate() {
            if let Some(b) = held[i + 1..].iter().find(|b| origin(b.0) == origin(a.0)) {
                let pid = s.tasks.get(a.0).and_then(|t| t.pid.clone()).unwrap_or_default();
                push(Action::Request(heartbeat(&pid, &[*a, *b])), "heartbeat two tasks at once");
                break;
            }
        }
        if let (Some(a), Some(b)) = (held.iter().find(|t| origin(t.0) == "a"), held.iter().find(|t| origin(t.0) == "b")) {
            push(Action::Request(heartbeat("w1", &[*a, *b])), "heartbeat across origins");
        }
        for (id, p) in s.promises.iter() {
            if p.state == PromiseState::Pending {
                if p.callbacks.iter().next().is_some() {
                    push(Action::Request(Request::PromiseSettle(settle(id))), "settle a promise a task awaits");
                } else {
                    push(Action::Request(Request::PromiseSettle(settle(id))), "settle a pending promise");
                }
                if p.listeners.iter().next().is_some() {
                    push(Action::Request(Request::PromiseSettle(settle(id))), "settle a promise a listener awaits");
                }
                push(Action::Request(Request::PromiseRegisterListener(PromiseRegisterListenerReq { awaited: id.clone(), address: format!("http://listener/{}", p.listeners.iter().count()) })), "register a listener");
                push(Action::Clock(p.timeout_at.saturating_sub(1)), "clock to just before a promise deadline");
                push(Action::Clock(p.timeout_at), "clock to a promise deadline");
            } else {
                push(Action::Request(Request::PromiseSettle(settle(id))), "settle a settled promise");
                push(Action::Request(Request::PromiseCreate(create(id, p.timeout_at))), "create a settled promise again");
                push(Action::Request(Request::PromiseRegisterListener(PromiseRegisterListenerReq { awaited: id.clone(), address: "http://listener/late".into() })), "register a listener on a settled promise");
            }
        }
        for (id, c) in s.schedules.iter() {
            push(Action::Request(Request::ScheduleGet(ScheduleGetReq { id: id.clone() })), "get a schedule");
            push(Action::Request(Request::ScheduleDelete(ScheduleDeleteReq { id: id.clone() })), "delete a schedule");
            push(Action::Request(Request::ScheduleCreate(schedule(id, "* * * * * *", 10, now))), "create a schedule again");
            push(Action::Clock(c.next_run_at.saturating_sub(1)), "clock to just before a schedule runs");
            push(Action::Clock(c.next_run_at), "clock to a schedule's run");
        }
        for id in SCHEDULES {
            let id = id.to_string();
            if !s.schedules.contains_key(&id) {
                push(Action::Request(Request::ScheduleCreate(schedule(&id, "* * * * * *", 1_500, now))), "create a schedule");
                push(Action::Request(Request::ScheduleGet(ScheduleGetReq { id: id.clone() })), "get a missing schedule");
                push(Action::Request(Request::ScheduleDelete(ScheduleDeleteReq { id })), "delete a missing schedule");
            }
        }
        for id in IDS {
            let id = id.to_string();
            if !s.promises.contains_key(&id) {
                push(Action::Request(Request::TaskCreate(TaskCreateReq { pid: "w2".into(), ttl: 20, action: targeted(&id, now + 50) })), "task.create a fresh id");
                push(Action::Request(Request::TaskCreate(TaskCreateReq { pid: "w2".into(), ttl: 20, action: targeted(&id, now) })), "task.create past its deadline");
                let mut delayed = targeted(&id, now + 50);
                delayed.tags.push(("resonate:delay".into(), (now + 20).to_string()));
                push(Action::Request(Request::PromiseCreate(delayed)), "create a delayed task");
            }
        }
        out
    }

    fn arbitrary(&self, _s: &Store, now: Time, pick: &mut dyn FnMut(usize) -> usize) -> Action<Request> {
        random_action(pick, now)
    }

    /// Read everything, delete every schedule (or it fires forever), move the
    /// clock past every deadline, so every timer must have fired and every
    /// task is done, and read again.
    fn finish(&self, s: &Store, now: Time) -> Vec<Action<Request>> {
        let reads = || {
            IDS.iter()
                .flat_map(|id| [Request::TaskGet(TaskGetReq { id: id.to_string() }), Request::PromiseGet(PromiseGetReq { id: id.to_string() })])
                .chain(SCHEDULES.iter().map(|id| Request::ScheduleGet(ScheduleGetReq { id: id.to_string() })))
                .map(Action::Request)
        };
        let deletes = s.schedules.iter().map(|(id, _)| Action::Request(Request::ScheduleDelete(ScheduleDeleteReq { id: id.clone() })));
        let mut last = now;
        for (_, p) in s.promises.iter() {
            last = last.max(p.timeout_at);
        }
        for (_, t) in s.tasks.iter() {
            last = last.max(t.lease_timeout_at()).max(t.retry_timeout_at.unwrap_or(0));
        }
        reads().chain(deletes).chain([Action::Clock(last + 1)]).chain(reads()).collect()
    }
}

/// The ids random requests use.
pub const IDS: &[&str] = &["a:1", "a:2", "a:3", "b:1", "b:2"];

/// The schedule ids random requests use: `sa` fires into origin `a`.
pub const SCHEDULES: &[&str] = &["sa", "sb"];

/// A clock move, or a request from a small pool of ids, versions and times;
/// `pick(n)` chooses among `n`. `clock`: the system's clock.
fn picked_tags(pick: &mut dyn FnMut(usize) -> usize, clock: Time) -> Tags {
    let mut tags = Vec::new();
    if pick(2) == 0 {
        tags.push(("resonate:target".into(), "sim://worker".into()));
    }
    if pick(2) == 0 {
        tags.push(("resonate:external".into(), "true".into()));
    }
    if pick(4) == 0 {
        tags.push(("resonate:timer".into(), "true".into()));
    }
    if pick(4) == 0 {
        tags.push(("resonate:delay".into(), (clock + pick(30) as Time).to_string()));
    }
    tags
}

fn random_action(pick: &mut dyn FnMut(usize) -> usize, clock: Time) -> Action<Request> {
    let id = IDS[pick(IDS.len())].to_string();
    let other = IDS[pick(IDS.len())].to_string();
    let version = pick(3) as u64;
    let t = clock + pick(40) as Time;
    let ttl = 1 + pick(20) as Time;
    let born = |id: String, tags: Tags| PromiseCreateReq { id, timeout_at: t, param: Value::empty(), tags };
    let done = |id: String| PromiseSettleReq { id, state: PromiseState::Resolved, value: Value::empty() };
    let req = match pick(20) {
        0 => return Action::Clock(clock + pick(30) as Time),
        1 => Request::PromiseCreate(born(id, picked_tags(pick, clock))),
        2 => Request::PromiseSettle(done(id)),
        3 => Request::PromiseRegisterCallback(PromiseRegisterCallbackReq { awaited: id, awaiter: other }),
        4 => {
            let mut tags = plain();
            if pick(4) != 0 {
                tags.push(("resonate:target".into(), "sim://worker".into()));
            }
            Request::TaskCreate(TaskCreateReq { pid: "w1".into(), ttl, action: born(id, tags) })
        }
        5 => Request::TaskAcquire(TaskAcquireReq { id, version, pid: "w1".into(), ttl }),
        6 => Request::TaskRelease(TaskReleaseReq { id, version }),
        7 => Request::TaskFulfill(TaskFulfillReq { id: id.clone(), version, action: done(id) }),
        8 => Request::TaskHeartbeat(TaskHeartbeatReq { pid: "w1".into(), tasks: vec![TaskRef { id, version }] }),
        9 => Request::TaskSuspend(TaskSuspendReq { id: id.clone(), version, actions: vec![PromiseRegisterCallbackReq { awaited: other, awaiter: id }] }),
        10 => Request::TaskFence(TaskFenceReq { id, version, action: TaskFenceAction::Create(born(other, picked_tags(pick, clock))) }),
        11 => Request::TaskFence(TaskFenceReq { id, version, action: TaskFenceAction::Settle(done(other)) }),
        12 => Request::TaskGet(TaskGetReq { id }),
        13 => Request::TaskHalt(TaskHaltReq { id }),
        14 => Request::TaskContinue(TaskContinueReq { id }),
        15 => Request::PromiseRegisterListener(PromiseRegisterListenerReq { awaited: id, address: ["http://listener/1", "poll://w1", "not a url"][pick(3)].into() }),
        16 => {
            let sid = SCHEDULES[pick(SCHEDULES.len())].to_string();
            let cron = ["* * * * * *", "*/5 * * * * *", "0 * * * * *", "* * * * *", "bogus"][pick(5)];
            let mut c = schedule(&sid, cron, pick(3000) as Time, clock);
            c.promise_tags = picked_tags(pick, clock);
            if pick(6) != 0 && !c.promise_tags.iter().any(|(k, _)| k == "resonate:target") {
                c.promise_tags.push(("resonate:target".into(), "sim://worker".into()));
            }
            Request::ScheduleCreate(c)
        }
        17 => Request::ScheduleGet(ScheduleGetReq { id: SCHEDULES[pick(SCHEDULES.len())].to_string() }),
        18 => Request::ScheduleDelete(ScheduleDeleteReq { id: SCHEDULES[pick(SCHEDULES.len())].to_string() }),
        _ => Request::PromiseGet(PromiseGetReq { id }),
    };
    Action::Request(req)
}

verus! {

fn sched(work: Work) -> (scheduled: Sched<Work>)
    ensures
        sched_v(scheduled) == as_sched(work),
{
    match &work {
        Work::Occurrence { at, .. } => Sched::Timer(*at, work),
        _ => Sched::Later(work),
    }
}

fn items(mut work: Vec<Work>) -> (scheduled: Vec<Sched<Work>>)
    ensures
        scheduled@.map_values(|item: Sched<Work>| sched_v(item)) == works(work@),
{
    let ghost all = work@;
    let mut scheduled: Vec<Sched<Work>> = Vec::new();
    while !work.is_empty()
        invariant
            scheduled@.len() + work@.len() == all.len(),
            work@ == all.skip(scheduled@.len() as int),
            scheduled@.map_values(|item: Sched<Work>| sched_v(item))
                == works(all.take(scheduled@.len() as int)),
        decreases work@.len(),
    {
        broadcast use group_views;
        let ghost k = scheduled@.len() as int;
        let item = work.remove(0);
        assert(all.skip(k).remove(0) =~= all.skip(k + 1));
        assert(all.take(k + 1) =~= all.take(k).push(all[k]));
        scheduled.push(sched(item));
    }
    assert(all.take(all.len() as int) =~= all);
    scheduled
}

impl Model for ServerConfig {
    type State = Store;
    type External = Request;
    type Response = Response;
    type Internal = Work;
    type Dispatch = Dispatch;

    fn external(
        &self,
        request: &Request,
        state: &Store,
        now: Time,
    ) -> (results: Vec<ExternalOutcome<Self>>) {
        let mut outcomes = self.handler(request, state, now);
        let mut results: Vec<ExternalOutcome<ServerConfig>> = Vec::new();
        while !outcomes.is_empty()
            decreases outcomes@.len(),
        {
            let outcome = outcomes.remove(0);
            let Out { resp, next, work, send, marks } = outcome;
            results.push(ExternalOutcome {
                next,
                resp,
                work: items(work),
                send,
                marks,
            });
        }
        results
    }

    fn internal(
        &self,
        work: &Work,
        state: &Store,
        now: Time,
    ) -> (results: Vec<InternalOutcome<Self>>) {
        let outcome = self.process_work(work, state, now);
        let mut results: Vec<InternalOutcome<ServerConfig>> = Vec::new();
        if outcome.not_due {
            return results;
        }
        let InOut { next, work, send, marks, not_due: _ } = outcome;
        results.push(InternalOutcome {
            next,
            work: items(work),
            send,
            marks,
        });
        results
    }

    fn due(&self, state: &Store, now: Time) -> (work: Vec<Sched<Work>>) {
        footprint::timeout_work(self, state, now)
    }
}

} // verus!
