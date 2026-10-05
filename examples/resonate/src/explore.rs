//! Testing glue, outside Verus: the list of the spec's marks, and requests
//! worth trying next (suggestions). Neither decides what the server does: the
//! spec marks its own branches (`mk` in `spec.rs`); suggestions are
//! requests built from the state, and the spec decides what they do.

use accordant::{Explore, Time};

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
    "clock moved",
    "clock unchanged",
    "create: id exists (echo)",
    "create: timer with target (400)",
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
    "get task",
    "get task: none (404)",
    "heartbeat: not held by this worker",
    "lease expired",
    "lease extended",
    "listener registered",
    "listener: bad address (400)",
    "listener: no such promise (404)",
    "listener: promise not external (422)",
    "promise created",
    "promise created past its deadline",
    "promise settled",
    "promise timed out",
    "release: no such task (404)",
    "release: not held (409)",
    "resume armed",
    "settle: already settled (echo)",
    "settle: no such promise (404)",
    "settle: not a settled state (400)",
    "suspend: awaited already settled (300)",
    "suspend: awaited in another origin (400)",
    "suspend: awaited missing (422)",
    "suspend: awaited not external (422)",
    "suspend: awaited twice (400)",
    "suspend: no awaited, or itself (400)",
    "suspend: no such task (404)",
    "suspend: not held (409)",
    "task acquired",
    "task created",
    "task dispatched",
    "task fulfilled",
    "task released",
    "task resumed",
    "task suspended",
    "task.create: not a target (400)",
    "task.create: pending task acquired",
    "task.create: promise exists, not a target (422)",
    "task.create: target without a task (500)",
    "task.create: task done (echo)",
    "task.create: task held (409)",
    "timer promise resolved",
];

/// A promise the suggestions settle or create with.
fn create(id: &Id, timeout_at: Time) -> Create {
    Create { id: id.clone(), timeout_at, data: None, external: false, target: false, timer: false }
}

fn settle(id: &Id) -> Settle {
    Settle { id: id.clone(), state: "resolved".into(), data: Some("v".into()) }
}

impl Explore for Resonate {
    /// Requests that reach the edges of what the state allows: fences and
    /// heartbeats at the current version and a stale one, the clock moved to
    /// just before and exactly at each deadline, promises settled while a task
    /// awaits them, settles and creates repeated.
    fn suggest(&self, s: &Server) -> Vec<(Request, &'static str)> {
        let mut out = Vec::new();
        let mut push = |r, why| out.push((r, why));
        let now = s.now;
        let siblings = |id: &Id| -> Vec<&Id> { s.promises.iter().map(|(k, _)| k).filter(|k| *k != id && origin(k) == origin(id)).collect() };
        for (id, t) in s.tasks.iter() {
            let v = t.version;
            match t.state {
                TState::Acquired => {
                    let pid = t.pid.clone().unwrap_or_default();
                    let fresh = format!("{}:child{}", origin(id), v);
                    push(Request::FenceTask { id: id.clone(), version: v, action: Fenced::Create(create(&fresh, now + 50)) }, "fence a create at the held version");
                    push(Request::FenceTask { id: id.clone(), version: v.wrapping_sub(1), action: Fenced::Create(create(&fresh, now + 50)) }, "fence at a stale version");
                    push(Request::FenceTask { id: id.clone(), version: v, action: Fenced::Create(create(&format!("elsewhere:{id}"), now + 50)) }, "fence a detached create");
                    for p in siblings(id) {
                        push(Request::FenceTask { id: id.clone(), version: v, action: Fenced::Settle(settle(p)) }, "fence a settle at the held version");
                        push(Request::SuspendTask { id: id.clone(), version: v, awaited: vec![p.clone()] }, "suspend on a promise");
                        push(Request::RegisterCallback { awaited: p.clone(), awaiter: id.clone() }, "register a callback");
                    }
                    push(Request::HeartbeatTask { id: id.clone(), version: v, pid: pid.clone() }, "heartbeat the held task");
                    push(Request::HeartbeatTask { id: id.clone(), version: v, pid: "intruder".into() }, "heartbeat as another worker");
                    push(Request::FulfillTask { id: id.clone(), version: v, state: "resolved".into(), data: None }, "fulfill at the held version");
                    push(Request::FulfillTask { id: id.clone(), version: v.wrapping_sub(1), state: "resolved".into(), data: None }, "fulfill at a stale version");
                    push(Request::ReleaseTask { id: id.clone(), version: v }, "release the held task");
                    // Only a lease that ends before its promise's deadline can
                    // expire: at the deadline the task is done.
                    let end = t.lease_expires();
                    if s.promises.get(id).is_some_and(|p| end < p.timeout_at) {
                        push(Request::AdvanceClock(end.saturating_sub(1)), "clock to just before a lease ends");
                        push(Request::AdvanceClock(end), "clock to a lease end");
                    }
                }
                TState::Pending => {
                    push(Request::AcquireTask { id: id.clone(), version: v, pid: "w1".into(), ttl: 10 }, "acquire a pending task");
                    push(Request::AcquireTask { id: id.clone(), version: v.wrapping_sub(1), pid: "w1".into(), ttl: 10 }, "acquire at a stale version");
                }
                TState::Suspended => {
                    push(Request::AcquireTask { id: id.clone(), version: v, pid: "w1".into(), ttl: 10 }, "acquire a suspended task");
                }
                TState::Fulfilled => {
                    push(Request::FulfillTask { id: id.clone(), version: v, state: "resolved".into(), data: None }, "fulfill a fulfilled task");
                }
            }
        }
        for (id, p) in s.promises.iter() {
            if p.state == PState::Pending {
                if p.callbacks.iter().next().is_some() {
                    push(Request::SettlePromise(settle(id)), "settle a promise a task awaits");
                } else {
                    push(Request::SettlePromise(settle(id)), "settle a pending promise");
                }
                push(Request::AdvanceClock(p.timeout_at.saturating_sub(1)), "clock to just before a promise deadline");
                push(Request::AdvanceClock(p.timeout_at), "clock to a promise deadline");
            } else {
                push(Request::SettlePromise(settle(id)), "settle a settled promise");
                push(Request::CreatePromise(create(id, p.timeout_at)), "create a settled promise again");
            }
        }
        out
    }
}

/// The ids [`arbitrary`] chooses from.
pub const IDS: &[&str] = &["a:1", "a:2", "a:3", "b:1", "b:2"];

/// A request from a small pool of ids, versions and times, what a fuzzer knows
/// without a model; `pick(n)` chooses among `n`. `clock`: the latest time the
/// clock was moved to.
pub fn arbitrary(pick: &mut impl FnMut(usize) -> usize, clock: Time) -> Request {
    let id = IDS[pick(IDS.len())].to_string();
    let other = IDS[pick(IDS.len())].to_string();
    let version = pick(3) as u32;
    let t = clock + pick(40) as Time;
    let ttl = 1 + pick(20) as Time;
    let create = |id: Id| Create { id, timeout_at: t, data: None, external: false, target: false, timer: false };
    let settle = |id: Id| Settle { id, state: "resolved".into(), data: None };
    match pick(14) {
        0 => Request::AdvanceClock(clock + pick(30) as Time),
        1 => Request::CreatePromise(create(id)),
        2 => Request::SettlePromise(settle(id)),
        3 => Request::RegisterCallback { awaited: id, awaiter: other },
        4 => Request::CreateTask { id, timeout_at: t, data: None, target: true },
        5 => Request::AcquireTask { id, version, pid: "w1".into(), ttl },
        6 => Request::ReleaseTask { id, version },
        7 => Request::FulfillTask { id, version, state: "resolved".into(), data: None },
        8 => Request::HeartbeatTask { id, version, pid: "w1".into() },
        9 => Request::SuspendTask { id, version, awaited: vec![other] },
        10 => Request::FenceTask { id, version, action: Fenced::Create(create(other)) },
        11 => Request::FenceTask { id, version, action: Fenced::Settle(settle(other)) },
        12 => Request::GetTask(id),
        _ => Request::GetPromise(id),
    }
}
