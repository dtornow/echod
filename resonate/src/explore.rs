//! Testing glue, outside Verus: names for what a step did (marks) and requests
//! worth trying next (suggestions). Neither decides what the server does: marks
//! are read off a step's request, response and state change; suggestions are
//! requests built from the state, and the spec decides what they do.

use accordant::{Explore, ExternalOutcome, InternalOutcome, Marks, Time};

use crate::model::origin;
use crate::spec::*;

/// What a request got back: its kind and status.
const STATUS: &[&str] = &[
    "clock 200",
    "promise.create 200",
    "promise.create 400",
    "promise.get 200",
    "promise.get 404",
    "promise.settle 200",
    "promise.settle 400",
    "promise.settle 404",
    "promise.callback 200",
    "promise.callback 400",
    "promise.callback 404",
    "promise.callback 422",
    "promise.listener 200",
    "promise.listener 400",
    "promise.listener 404",
    "promise.listener 422",
    "task.get 200",
    "task.get 404",
    "task.create 200",
    "task.create 400",
    "task.create 409",
    "task.create 422",
    "task.acquire 200",
    "task.acquire 404",
    "task.acquire 409",
    "task.release 200",
    "task.release 404",
    "task.release 409",
    "task.fulfill 200",
    "task.fulfill 400",
    "task.fulfill 404",
    "task.fulfill 409",
    "task.heartbeat 200",
    "task.suspend 200",
    "task.suspend 300",
    "task.suspend 400",
    "task.suspend 404",
    "task.suspend 409",
    "task.suspend 422",
    "task.fence 200",
    "task.fence 400",
    "task.fence 404",
    "task.fence 409",
    "task.poll 200",
];

/// What a step did to the state.
const EFFECT: &[&str] = &[
    "promise created",
    "promise created by a fence (detached)",
    "promise settled by a client",
    "promise settled by a fence",
    "promise timed out",
    "timer promise resolved",
    "callback registered",
    "task created",
    "task created already acquired",
    "task acquired",
    "task released",
    "task fulfilled",
    "task suspended",
    "task resumed",
    "suspended task claimed by poll",
    "pending task claimed by poll",
    "lease extended",
    "lease expired",
    "task dispatched",
    "poll claimed nothing",
    "clock moved",
];

fn kind(req: &Request) -> &'static str {
    match req {
        Request::AdvanceClock(_) => "clock",
        Request::CreatePromise(_) => "promise.create",
        Request::GetPromise(_) => "promise.get",
        Request::SettlePromise(_) => "promise.settle",
        Request::RegisterCallback { .. } => "promise.callback",
        Request::RegisterListener { .. } => "promise.listener",
        Request::GetTask(_) => "task.get",
        Request::CreateTask { .. } => "task.create",
        Request::AcquireTask { .. } => "task.acquire",
        Request::ReleaseTask { .. } => "task.release",
        Request::FulfillTask { .. } => "task.fulfill",
        Request::HeartbeatTask { .. } => "task.heartbeat",
        Request::SuspendTask { .. } => "task.suspend",
        Request::FenceTask { .. } => "task.fence",
        Request::PollTask { .. } => "task.poll",
    }
}

fn named(table: &'static [&'static str], name: &str) -> Option<&'static str> {
    table.iter().copied().find(|m| *m == name)
}

/// The marks of a state change; `fenced`: the change came through a fence.
fn effects(before: &Server, after: &Server, fenced: bool, out: &mut Vec<&'static str>) {
    if after.now > before.now {
        out.push("clock moved");
    }
    for (id, q) in after.promises.iter() {
        match before.promises.get(id) {
            None if fenced => out.push("promise created by a fence (detached)"),
            None => out.push("promise created"),
            Some(p) => {
                if p.state == PState::Pending && q.state != PState::Pending {
                    out.push(match q.state {
                        PState::TimedOut => "promise timed out",
                        PState::Resolved if p.timer_tag && q.settled_at == Some(p.timeout_at) => "timer promise resolved",
                        _ if fenced => "promise settled by a fence",
                        _ => "promise settled by a client",
                    });
                }
                if q.callbacks.iter().any(|c| !p.callbacks.contains(c)) {
                    out.push("callback registered");
                }
            }
        }
    }
    for (id, u) in after.tasks.iter() {
        let Some(t) = before.tasks.get(id) else {
            out.push(if u.state == TState::Acquired { "task created already acquired" } else { "task created" });
            continue;
        };
        use TState::*;
        match (t.state, u.state) {
            (Pending, Acquired) => out.push("task acquired"),
            (Acquired, Pending) if after.now >= t.lease_expires() && before.now == after.now => out.push("lease expired"),
            (Acquired, Pending) => out.push("task released"),
            (Acquired, Suspended) => out.push("task suspended"),
            (Suspended, Pending) => out.push("task resumed"),
            (Suspended, Acquired) => out.push("suspended task claimed by poll"),
            (Acquired, Acquired) if u.acquired_at != t.acquired_at || u.version != t.version => out.push("lease extended"),
            (a, Fulfilled) if a != Fulfilled => out.push("task fulfilled"),
            _ => {}
        }
    }
}

impl Marks for Resonate {
    fn all_marks(&self) -> Vec<&'static str> {
        STATUS.iter().chain(EFFECT).copied().collect()
    }

    fn external_marks(&self, req: &Request, before: &Server, out: &ExternalOutcome<Self>) -> Vec<&'static str> {
        let mut m = Vec::new();
        m.extend(named(STATUS, &format!("{} {}", kind(req), out.resp.status())));
        effects(before, &out.next, matches!(req, Request::FenceTask { .. }), &mut m);
        if let Request::PollTask { .. } = req {
            match &out.resp {
                Response::Claimed(ts) if ts.is_empty() => m.push("poll claimed nothing"),
                Response::Claimed(ts) => {
                    if ts.iter().any(|t| before.tasks.get(&t.id).is_some_and(|b| b.state == TState::Pending)) {
                        m.push("pending task claimed by poll");
                    }
                }
                _ => {}
            }
            // A poll that claims a pending task goes through `task acquired`;
            // name it once, as the poll.
            m.retain(|x| *x != "task acquired");
        }
        if !out.send.is_empty() {
            m.push("task dispatched");
        }
        m.sort();
        m.dedup();
        m
    }

    fn internal_marks(&self, _ids: &crate::Internal, before: &Server, out: &InternalOutcome<Self>) -> Vec<&'static str> {
        let mut m = Vec::new();
        effects(before, &out.next, false, &mut m);
        if !out.send.is_empty() {
            m.push("task dispatched");
        }
        m.sort();
        m.dedup();
        m
    }
}

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
                    push(Request::PollTask { pid: "w2".into(), ttl: 10, limit: 1 }, "poll while a task is pending");
                }
                TState::Suspended => {
                    push(Request::PollTask { pid: "w2".into(), ttl: 10, limit: 1 }, "poll while a task is suspended");
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
    match pick(15) {
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
        13 => Request::GetPromise(id),
        _ => Request::PollTask { pid: "w2".into(), ttl, limit: 2 },
    }
}
