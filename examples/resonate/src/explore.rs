//! Testing glue, outside Verus: the list of the spec's marks, and requests
//! worth trying next (suggestions). Neither decides what the server does: the
//! spec marks its own branches (`mk` in `spec.rs`); suggestions are
//! requests built from the state, and the spec decides what they do.

use accordant::{Action, Explore, Time};

use crate::model::origin;
use crate::spec::*;

/// Every mark the spec can put on an outcome, so a coverage report can show
/// the ones no run reached. `tests/marks.rs` checks it against `spec.rs`.
pub const MARKS: &[&str] = &[
    "acquire: no such task (404)",
    "acquire: not pending, or stale version (409)",
    "callback registered",
    "callback: awaiter no task, or awaited not external (422)",
    "callback: itself or another origin (400)",
    "callback: no awaited promise (404)",
    "callback: no awaiter promise (422)",
    "callback: one of them settled (echo)",
    "continue: no such task (404)",
    "continue: not halted (409)",
    "create: delay past the deadline (400)",
    "create: delay without a target (400)",
    "create: id exists (echo)",
    "create: timer with target (400)",
    "delete schedule: none (404)",
    "fence: detached create",
    "fence: detached create, no such task (404)",
    "fence: detached create, not held (409)",
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
    "listener: bad address (400)",
    "listener: no such promise (404)",
    "listener: promise not external (422)",
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
    "schedule: id exists (echo)",
    "schedule: id with a colon (400)",
    "schedule: invalid cron (400)",
    "schedule: occurrence exists",
    "schedule: promises without a target (400)",
    "schedule: timer with target (400)",
    "settle: already settled (echo)",
    "settle: no such promise (404)",
    "settle: not a settled state (400)",
    "settled with callbacks or listeners",
    "suspend: awaited already settled (300)",
    "suspend: awaited in another origin (400)",
    "suspend: awaited missing (422)",
    "suspend: awaited not external (422)",
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
    "task.create: action with a delay (400)",
    "task.create: not runnable, or a timer (400)",
    "task.create: pending task acquired",
    "task.create: promise exists, not a target (422)",
    "task.create: target without a task (409)",
    "task.create: task done (echo)",
    "task.create: task held, suspended or halted (409)",
    "timer promise resolved",
];

/// No tags at all: an internal promise.
pub const PLAIN: Tags = Tags { target: false, external: false, timer: false, delay: None };

/// A promise the suggestions settle or create with.
fn create(id: &Id, timeout_at: Time) -> Create {
    Create { id: id.clone(), timeout_at, data: None, tags: PLAIN }
}

fn targeted(id: &Id, timeout_at: Time) -> Create {
    Create { id: id.clone(), timeout_at, data: None, tags: Tags { target: true, ..PLAIN } }
}

fn settle(id: &Id) -> Settle {
    Settle { id: id.clone(), state: "resolved".into(), data: Some("v".into()) }
}

/// A schedule whose occurrences are tasks in the origin its id names:
/// `sa` fires into `a`. (A schedule's id has no `:`, so it cannot carry an
/// origin of its own the way a promise id does.)
fn schedule(id: &Id, cron: &str, timeout: Time) -> ScheduleCreate {
    let into = id.strip_prefix('s').unwrap_or(id);
    ScheduleCreate { id: id.clone(), cron: cron.into(), promise_id: format!("{into}:{{{{.id}}}}.{{{{.timestamp}}}}"), promise_timeout: timeout, promise_param: None, promise_tags: Tags { target: true, ..PLAIN } }
}

fn heartbeat(pid: &str, refs: &[(&Id, u32)]) -> Request {
    Request::HeartbeatTask { pid: pid.into(), tasks: refs.iter().map(|(id, v)| TaskRef { id: (*id).clone(), version: *v }).collect() }
}

impl Explore for Resonate {
    /// Actions that reach the edges of what the state allows: fences and
    /// heartbeats at the current version and a stale one, the clock moved to
    /// just before and exactly at each deadline, promises settled while a task
    /// awaits them, settles and creates repeated, halts and continues in every
    /// task state, schedules fired and deleted.
    fn suggest(&self, s: &Server, now: Time) -> Vec<(Action<Request>, &'static str)> {
        let mut out = Vec::new();
        let mut push = |a, why| out.push((a, why));
        let siblings = |id: &Id| -> Vec<&Id> { s.promises.iter().map(|(k, _)| k).filter(|k| *k != id && origin(k) == origin(id)).collect() };
        let mut held: Vec<(&Id, u32)> = Vec::new();
        for (id, t) in s.tasks.iter() {
            let v = t.version;
            match t.state {
                TState::Acquired => {
                    held.push((id, v));
                    let pid = t.pid.clone().unwrap_or_default();
                    let fresh = format!("{}:child{}", origin(id), v);
                    push(Action::Request(Request::FenceTask { id: id.clone(), version: v, action: Fenced::Create(create(&fresh, now + 50)) }), "fence a create at the held version");
                    push(Action::Request(Request::FenceTask { id: id.clone(), version: v.wrapping_sub(1), action: Fenced::Create(create(&fresh, now + 50)) }), "fence at a stale version");
                    push(Action::Request(Request::FenceTask { id: id.clone(), version: v, action: Fenced::Create(targeted(&format!("elsewhere:{id}"), now + 50)) }), "fence a detached create");
                    push(Action::Request(Request::FenceTask { id: id.clone(), version: v.wrapping_sub(1), action: Fenced::Create(create(&format!("elsewhere:{id}.stale"), now + 50)) }), "fence a detached create at a stale version");
                    for p in siblings(id) {
                        push(Action::Request(Request::FenceTask { id: id.clone(), version: v, action: Fenced::Settle(settle(p)) }), "fence a settle at the held version");
                        push(Action::Request(Request::SuspendTask { id: id.clone(), version: v, awaited: vec![p.clone()] }), "suspend on a promise");
                        push(Action::Request(Request::RegisterCallback { awaited: p.clone(), awaiter: id.clone() }), "register a callback");
                    }
                    push(Action::Request(heartbeat(&pid, &[(id, v)])), "heartbeat the held task");
                    push(Action::Request(heartbeat("intruder", &[(id, v)])), "heartbeat as another worker");
                    push(Action::Request(Request::FulfillTask { id: id.clone(), version: v, state: "resolved".into(), data: None }), "fulfill at the held version");
                    push(Action::Request(Request::FulfillTask { id: id.clone(), version: v.wrapping_sub(1), state: "resolved".into(), data: None }), "fulfill at a stale version");
                    push(Action::Request(Request::ReleaseTask { id: id.clone(), version: v }), "release the held task");
                    push(Action::Request(Request::HaltTask(id.clone())), "halt the held task");
                    // Only a lease that ends before its promise's deadline can
                    // expire: at the deadline the task is done.
                    let end = t.lease_expires();
                    if s.promises.get(id).is_some_and(|p| end < p.timeout_at) {
                        push(Action::Clock(end.saturating_sub(1)), "clock to just before a lease ends");
                        push(Action::Clock(end), "clock to a lease end");
                    }
                }
                TState::Pending => {
                    push(Action::Request(Request::AcquireTask { id: id.clone(), version: v, pid: "w1".into(), ttl: 10 }), "acquire a pending task");
                    push(Action::Request(Request::AcquireTask { id: id.clone(), version: v.wrapping_sub(1), pid: "w1".into(), ttl: 10 }), "acquire at a stale version");
                    push(Action::Request(Request::CreateTask { pid: "w2".into(), ttl: 20, action: targeted(id, now + 50) }), "task.create a pending task");
                    push(Action::Request(Request::HaltTask(id.clone())), "halt a pending task");
                    push(Action::Request(Request::ContinueTask(id.clone())), "continue a pending task");
                    if let Some(r) = t.retry_at {
                        if r > now && s.promises.get(id).is_some_and(|p| r < p.timeout_at) {
                            push(Action::Clock(r), "clock to a redispatch");
                        }
                    }
                }
                TState::Suspended => {
                    push(Action::Request(Request::AcquireTask { id: id.clone(), version: v, pid: "w1".into(), ttl: 10 }), "acquire a suspended task");
                    push(Action::Request(Request::HaltTask(id.clone())), "halt a suspended task");
                }
                TState::Halted => {
                    push(Action::Request(Request::ContinueTask(id.clone())), "continue a halted task");
                    push(Action::Request(Request::HaltTask(id.clone())), "halt a halted task");
                    push(Action::Request(Request::AcquireTask { id: id.clone(), version: v, pid: "w1".into(), ttl: 10 }), "acquire a halted task");
                    push(Action::Request(Request::CreateTask { pid: "w2".into(), ttl: 20, action: targeted(id, now + 50) }), "task.create a halted task");
                }
                TState::Fulfilled => {
                    push(Action::Request(Request::FulfillTask { id: id.clone(), version: v, state: "resolved".into(), data: None }), "fulfill a fulfilled task");
                    push(Action::Request(Request::HaltTask(id.clone())), "halt a fulfilled task");
                    push(Action::Request(Request::CreateTask { pid: "w2".into(), ttl: 20, action: targeted(id, now + 50) }), "task.create a fulfilled task");
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
            if p.state == PState::Pending {
                if p.callbacks.iter().next().is_some() {
                    push(Action::Request(Request::SettlePromise(settle(id))), "settle a promise a task awaits");
                } else {
                    push(Action::Request(Request::SettlePromise(settle(id))), "settle a pending promise");
                }
                if p.listeners.iter().next().is_some() {
                    push(Action::Request(Request::SettlePromise(settle(id))), "settle a promise a listener awaits");
                }
                push(Action::Request(Request::RegisterListener { awaited: id.clone(), address: format!("http://listener/{}", p.listeners.iter().count()) }), "register a listener");
                push(Action::Clock(p.timeout_at.saturating_sub(1)), "clock to just before a promise deadline");
                push(Action::Clock(p.timeout_at), "clock to a promise deadline");
            } else {
                push(Action::Request(Request::SettlePromise(settle(id))), "settle a settled promise");
                push(Action::Request(Request::CreatePromise(create(id, p.timeout_at))), "create a settled promise again");
                push(Action::Request(Request::RegisterListener { awaited: id.clone(), address: "http://listener/late".into() }), "register a listener on a settled promise");
            }
        }
        for (id, c) in s.schedules.iter() {
            push(Action::Request(Request::GetSchedule(id.clone())), "get a schedule");
            push(Action::Request(Request::DeleteSchedule(id.clone())), "delete a schedule");
            push(Action::Request(Request::CreateSchedule(schedule(id, "* * * * * *", 10))), "create a schedule again");
            push(Action::Clock(c.next_run_at.saturating_sub(1)), "clock to just before a schedule runs");
            push(Action::Clock(c.next_run_at), "clock to a schedule's run");
        }
        for id in SCHEDULES {
            let id = id.to_string();
            if !s.schedules.contains_key(&id) {
                push(Action::Request(Request::CreateSchedule(schedule(&id, "* * * * * *", 1_500))), "create a schedule");
                push(Action::Request(Request::GetSchedule(id.clone())), "get a missing schedule");
                push(Action::Request(Request::DeleteSchedule(id)), "delete a missing schedule");
            }
        }
        for id in IDS {
            let id = id.to_string();
            if !s.promises.contains_key(&id) {
                push(Action::Request(Request::CreateTask { pid: "w2".into(), ttl: 20, action: targeted(&id, now + 50) }), "task.create a fresh id");
                push(Action::Request(Request::CreateTask { pid: "w2".into(), ttl: 20, action: targeted(&id, now) }), "task.create past its deadline");
                push(Action::Request(Request::CreatePromise(Create { id, timeout_at: now + 50, data: None, tags: Tags { target: true, delay: Some(now + 20), ..PLAIN } })), "create a delayed task");
            }
        }
        out
    }

    fn arbitrary(&self, _s: &Server, now: Time, pick: &mut dyn FnMut(usize) -> usize) -> Action<Request> {
        random_action(pick, now)
    }

    /// Read everything, delete every schedule (or it fires forever), move the
    /// clock past every deadline, so every timer must have fired and every
    /// task is done, and read again.
    fn finish(&self, s: &Server, now: Time) -> Vec<Action<Request>> {
        let reads = || {
            IDS.iter()
                .flat_map(|id| [Request::GetTask(id.to_string()), Request::GetPromise(id.to_string())])
                .chain(SCHEDULES.iter().map(|id| Request::GetSchedule(id.to_string())))
                .map(Action::Request)
        };
        let deletes = s.schedules.iter().map(|(id, _)| Action::Request(Request::DeleteSchedule(id.clone())));
        let mut last = now;
        for (_, p) in s.promises.iter() {
            last = last.max(p.timeout_at);
        }
        for (_, t) in s.tasks.iter() {
            last = last.max(t.lease_expires()).max(t.retry_at.unwrap_or(0));
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
fn random_action(pick: &mut dyn FnMut(usize) -> usize, clock: Time) -> Action<Request> {
    let id = IDS[pick(IDS.len())].to_string();
    let other = IDS[pick(IDS.len())].to_string();
    let version = pick(3) as u32;
    let t = clock + pick(40) as Time;
    let ttl = 1 + pick(20) as Time;
    let tags = |pick: &mut dyn FnMut(usize) -> usize| Tags { target: pick(2) == 0, external: pick(2) == 0, timer: pick(4) == 0, delay: if pick(4) == 0 { Some(clock + pick(30) as Time) } else { None } };
    let create = |id: Id, tags: Tags| Create { id, timeout_at: t, data: None, tags };
    let settle = |id: Id| Settle { id, state: "resolved".into(), data: None };
    let req = match pick(20) {
        0 => return Action::Clock(clock + pick(30) as Time),
        1 => Request::CreatePromise(create(id, tags(pick))),
        2 => Request::SettlePromise(settle(id)),
        3 => Request::RegisterCallback { awaited: id, awaiter: other },
        4 => Request::CreateTask { pid: "w1".into(), ttl, action: create(id, Tags { target: pick(4) != 0, ..PLAIN }) },
        5 => Request::AcquireTask { id, version, pid: "w1".into(), ttl },
        6 => Request::ReleaseTask { id, version },
        7 => Request::FulfillTask { id, version, state: "resolved".into(), data: None },
        8 => Request::HeartbeatTask { pid: "w1".into(), tasks: vec![TaskRef { id, version }] },
        9 => Request::SuspendTask { id, version, awaited: vec![other] },
        10 => Request::FenceTask { id, version, action: Fenced::Create(create(other, tags(pick))) },
        11 => Request::FenceTask { id, version, action: Fenced::Settle(settle(other)) },
        12 => Request::GetTask(id),
        13 => Request::HaltTask(id),
        14 => Request::ContinueTask(id),
        15 => Request::RegisterListener { awaited: id, address: ["http://listener/1", "poll://w1", "not a url"][pick(3)].into() },
        16 => {
            let sid = SCHEDULES[pick(SCHEDULES.len())].to_string();
            let cron = ["* * * * * *", "*/5 * * * * *", "0 * * * * *", "* * * * *", "bogus"][pick(5)];
            let mut c = schedule(&sid, cron, pick(3000) as Time);
            c.promise_tags = Tags { target: pick(6) != 0, ..tags(pick) };
            Request::CreateSchedule(c)
        }
        17 => Request::GetSchedule(SCHEDULES[pick(SCHEDULES.len())].to_string()),
        18 => Request::DeleteSchedule(SCHEDULES[pick(SCHEDULES.len())].to_string()),
        _ => Request::GetPromise(id),
    };
    Action::Request(req)
}
