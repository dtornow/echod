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

    fn arbitrary(&self, s: &Server, pick: &mut dyn FnMut(usize) -> usize) -> Request {
        random_request(pick, s.now)
    }

    /// What a worker and its clients would send: an operation only if its
    /// operands exist, the operands read from the state, and a task acquired
    /// at the version an `execute` offered it, which may have gone stale.
    fn informed(&self, s: &Server, inbox: &mut Vec<Dispatch>, pick: &mut dyn FnMut(usize) -> usize) -> Option<Request> {
        Some(informed_request(s, inbox, pick))
    }

    /// Read everything, move the clock past every deadline (the longest is a
    /// task.create lease), so every timer must have fired, and read again.
    fn finish(&self, s: &Server) -> Vec<Request> {
        let reads = || IDS.iter().flat_map(|id| [Request::GetTask(id.to_string()), Request::GetPromise(id.to_string())]);
        reads().chain([Request::AdvanceClock(s.now + TASK_CREATE_TTL + 1)]).chain(reads()).collect()
    }
}

/// The ids random requests use.
pub const IDS: &[&str] = &["a:1", "a:2", "a:3", "b:1", "b:2"];

/// A request from a small pool of ids, versions and times; `pick(n)` chooses
/// among `n`. `clock`: the server's clock.
fn random_request(pick: &mut dyn FnMut(usize) -> usize, clock: Time) -> Request {
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

/// One of `v`, or `None` if it is empty.
fn one_of<T: Clone>(pick: &mut dyn FnMut(usize) -> usize, v: &[T]) -> Option<T> {
    (!v.is_empty()).then(|| v[pick(v.len())].clone())
}

/// `v`, or one beside it a fifth of the time: a stale or future version, which
/// the server must refuse.
fn skew(pick: &mut dyn FnMut(usize) -> usize, v: u32) -> u32 {
    match pick(10) {
        0 => v.wrapping_sub(1),
        1 => v.wrapping_add(1),
        _ => v,
    }
}

/// A settle state: the three the protocol has, and now and then one it refuses.
fn settle_state(pick: &mut dyn FnMut(usize) -> usize) -> String {
    ["resolved", "rejected", "rejected_canceled", "resolved", "rejected", "pending"][pick(6)].into()
}

/// An id in `origin` no promise has yet: the next of the pool, then numbered.
fn fresh(s: &Server, origin: &str) -> Id {
    let taken = |id: &str| s.promises.get(&id.to_string()).is_some();
    IDS.iter()
        .map(|id| id.to_string())
        .filter(|id| crate::model::origin(id) == origin)
        .chain((1..).map(|n| format!("{origin}:{n}")))
        .find(|id| !taken(id))
        .expect("numbered ids never run out")
}

/// A promise to create in `origin`: new two times in three, internal,
/// external, a timer or a task's target, with its deadline a little ahead (now
/// and then already past).
fn creation(s: &Server, origin: &str, existing: &[Id], pick: &mut dyn FnMut(usize) -> usize) -> Create {
    let id = match pick(3) {
        0 => one_of(pick, existing).unwrap_or_else(|| fresh(s, origin)),
        _ => fresh(s, origin),
    };
    let timeout_at = if pick(8) == 0 { s.now } else { s.now + 1 + pick(60) as Time };
    let (external, timer, target) = match pick(8) {
        0 | 1 => (true, false, false),
        2 | 3 => (false, true, false),
        4 => (false, false, true),
        5 => (false, true, true),
        _ => (false, false, false),
    };
    Create { id, timeout_at, data: None, external, target, timer }
}

/// The request [`Explore::informed`] sends: an eligible operation, picked
/// uniformly, with operands from the state.
fn informed_request(s: &Server, inbox: &mut Vec<Dispatch>, pick: &mut dyn FnMut(usize) -> usize) -> Request {
    let mut promises: Vec<(&Id, &Promise)> = s.promises.iter().collect();
    promises.sort_by(|a, b| a.0.cmp(b.0));
    let mut tasks: Vec<(&Id, &Task)> = s.tasks.iter().collect();
    tasks.sort_by(|a, b| a.0.cmp(b.0));
    let all: Vec<Id> = promises.iter().map(|(id, _)| (*id).clone()).collect();
    let pending: Vec<Id> = promises.iter().filter(|(_, p)| p.live()).map(|(id, _)| (*id).clone()).collect();
    let in_state = |st: TState| -> Vec<(Id, u32, Option<String>)> {
        tasks.iter().filter(|(_, t)| t.state == st).map(|(id, t)| ((*id).clone(), t.version, t.pid.clone())).collect()
    };
    let acquired = in_state(TState::Acquired);
    let waiting: Vec<_> = in_state(TState::Pending).into_iter().chain(in_state(TState::Suspended)).collect();
    let task_ids: Vec<Id> = tasks.iter().map(|(id, _)| (*id).clone()).collect();
    // Promises in the same origin as `id`, other than it.
    let siblings = |id: &Id| -> Vec<Id> { all.iter().filter(|p| *p != id && origin(p) == origin(id)).cloned().collect() };
    // The origins in use. A new one stands for a new root workflow: what it
    // creates stays in it, so the checker's partitions stay small however
    // long the run.
    let origins: Vec<String> = {
        let mut o: Vec<String> = IDS.iter().copied().chain(all.iter().map(|id| id.as_str())).map(|id| origin(id).to_string()).collect();
        o.sort();
        o.dedup();
        o
    };
    let new_origin = format!("o{}", origins.len());
    let root = |pick: &mut dyn FnMut(usize) -> usize| -> String {
        if pick(2) == 0 { new_origin.clone() } else { origins[pick(origins.len())].clone() }
    };

    let mut ops = vec!["clock", "create", "task.create"];
    if !all.is_empty() {
        ops.extend(["get", "settle", "listener"]);
    }
    if !task_ids.is_empty() {
        ops.extend(["get task", "callback"]);
    }
    if !waiting.is_empty() || !inbox.is_empty() {
        ops.push("acquire");
    }
    if !acquired.is_empty() {
        ops.extend(["release", "fulfill", "heartbeat", "suspend", "fence"]);
    }
    match ops[pick(ops.len())] {
        "clock" => {
            // To a deadline or a lease end, where something falls due, or a
            // little ahead.
            let mut due: Vec<Time> = promises.iter().filter(|(_, p)| p.live()).map(|(_, p)| p.timeout_at).collect();
            due.extend(tasks.iter().filter(|(_, t)| t.state == TState::Acquired).map(|(_, t)| t.lease_expires()));
            due.retain(|&t| t >= s.now);
            match one_of(pick, &due) {
                Some(t) if pick(2) == 0 => Request::AdvanceClock(t),
                _ => Request::AdvanceClock(s.now + pick(30) as Time),
            }
        }
        "create" => {
            let o = root(pick);
            Request::CreatePromise(creation(s, &o, &all, pick))
        }
        "task.create" => {
            let o = root(pick);
            let id = if pick(3) == 0 { one_of(pick, &all).unwrap_or_else(|| fresh(s, &o)) } else { fresh(s, &o) };
            Request::CreateTask { id, timeout_at: s.now + 1 + pick(60) as Time, data: None, target: pick(8) != 0 }
        }
        "get" => Request::GetPromise(one_of(pick, &all).expect("eligible")),
        "get task" => Request::GetTask(one_of(pick, &task_ids).expect("eligible")),
        "settle" => {
            // A pending promise mostly; a settled one must answer the same.
            let id = if pick(4) != 0 { one_of(pick, &pending) } else { None }.unwrap_or_else(|| one_of(pick, &all).expect("eligible"));
            Request::SettlePromise(Settle { id, state: settle_state(pick), data: Some("v".into()) })
        }
        "listener" => {
            // Now and then a bad address, or a promise that doesn't exist.
            let address = if pick(8) == 0 { "not an address".into() } else { "http://w1".into() };
            let awaited = if pick(8) == 0 { fresh(s, &root(pick)) } else { one_of(pick, &all).expect("eligible") };
            Request::RegisterListener { awaited, address }
        }
        "callback" => {
            // A task awaits a promise in its origin; one a task could await
            // (external, pending) when there is one.
            let awaiter = one_of(pick, &task_ids).expect("eligible");
            let sib = siblings(&awaiter);
            let live_external: Vec<Id> =
                sib.iter().filter(|p| s.promises.get(p).is_some_and(|q| q.live() && q.external())).cloned().collect();
            let awaited = if pick(4) != 0 { one_of(pick, &live_external) } else { None }
                .or_else(|| one_of(pick, &sib))
                .unwrap_or_else(|| fresh(s, origin(&awaiter)));
            Request::RegisterCallback { awaited, awaiter }
        }
        "acquire" => {
            // What a worker does: take an offer it was sent, at the version
            // offered. An offer still current is the worker doing its job; one
            // gone stale the server must refuse.
            let current = |d: &Dispatch| match d {
                Dispatch::Execute { id, version } => waiting.iter().any(|(w, v, _)| w == id && v == version),
            };
            let fresh_offer = inbox.iter().position(current);
            let offer = match fresh_offer {
                Some(i) if pick(3) != 0 => Some(inbox.remove(i)),
                _ if !inbox.is_empty() && (waiting.is_empty() || pick(2) == 0) => Some(inbox.remove(pick(inbox.len()))),
                _ => None,
            };
            let (id, version) = match offer {
                Some(Dispatch::Execute { id, version }) => (id, version),
                None => {
                    let (id, v, _) = one_of(pick, &waiting).expect("eligible");
                    (id, skew(pick, v))
                }
            };
            Request::AcquireTask { id, version, pid: "w1".into(), ttl: 1 + pick(20) as Time }
        }
        op => {
            let (id, v, pid) = one_of(pick, &acquired).expect("eligible");
            let version = skew(pick, v);
            match op {
                "release" => Request::ReleaseTask { id, version },
                "fulfill" => Request::FulfillTask { id, version, state: settle_state(pick), data: None },
                "heartbeat" => {
                    let pid = if pick(5) == 0 { "intruder".into() } else { pid.unwrap_or_default() };
                    Request::HeartbeatTask { id, version, pid }
                }
                "suspend" => {
                    // One or two promises in its origin, pending or settled
                    // (which the server answers with a redirect), now and then
                    // the same one twice.
                    let sib = siblings(&id);
                    let first = one_of(pick, &sib).unwrap_or_else(|| fresh(s, origin(&id)));
                    let mut awaited = vec![first.clone()];
                    match pick(4) {
                        0 => awaited.push(first),
                        1 => awaited.extend(one_of(pick, &sib).filter(|p| *p != first)),
                        _ => {}
                    }
                    Request::SuspendTask { id, version, awaited }
                }
                _ => {
                    // A child in its origin, a detached one elsewhere, or a
                    // settle of a sibling.
                    let sib: Vec<Id> = siblings(&id).into_iter().filter(|p| pending.contains(p)).collect();
                    let action = match one_of(pick, &sib) {
                        Some(p) if pick(3) == 0 => Fenced::Settle(Settle { id: p, state: settle_state(pick), data: Some("v".into()) }),
                        _ => {
                            let o = if pick(5) == 0 { root(pick) } else { origin(&id).to_string() };
                            let mut c = creation(s, &o, &siblings(&id), pick);
                            c.target = false;
                            Fenced::Create(c)
                        }
                    };
                    Request::FenceTask { id, version, action }
                }
            }
        }
    }
}
