//! The requests a run issues, and how they are generated.
//!
//! Every request kind the server serves, as the model types it
//! (`resonate::Request`), over a small space of ids so that operations
//! collide: a few origins, a few promises per origin, one child each.
//! Versions and pids are drawn from what the client has seen, so that fenced
//! operations sometimes carry the right version and sometimes not.

use std::collections::{BTreeMap, BTreeSet};

use resonate::{Create, Fenced, Request, ScheduleCreate, Settle, Tags, TaskRef};
use serde_json::Value;

use crate::rng::Rng;

/// The worker every task is dispatched to, and every listener listens at.
pub const WORKER: &str = "sim://worker";

/// The schedule ids a run uses (a schedule's id has no `:`).
pub const SCHEDULES: [&str; 3] = ["s0", "s1", "s2"];

/// The document a request is about, for routing: an origin, or a schedule.
pub fn target_of(req: &Request) -> String {
    let origin = |id: &str| echod_logic::keys::origin_of(id).to_string();
    match req {
        Request::CreatePromise(c) => origin(&c.id),
        Request::GetPromise(id) | Request::GetTask(id) | Request::HaltTask(id) | Request::ContinueTask(id) => origin(id),
        Request::SettlePromise(s) => origin(&s.id),
        Request::RegisterCallback { awaited, .. } | Request::RegisterListener { awaited, .. } => origin(awaited),
        Request::CreateTask { action, .. } => origin(&action.id),
        Request::AcquireTask { id, .. } | Request::ReleaseTask { id, .. } | Request::FulfillTask { id, .. } | Request::SuspendTask { id, .. } | Request::FenceTask { id, .. } => origin(id),
        Request::HeartbeatTask { tasks, .. } => tasks.first().map(|t| origin(&t.id)).unwrap_or_default(),
        Request::CreateSchedule(c) => format!("sched:{}", c.id),
        Request::GetSchedule(id) | Request::DeleteSchedule(id) => format!("sched:{id}"),
    }
}

/// What a client has learned, to draw plausible versions and pids from.
#[derive(Default)]
pub struct Seen {
    pub versions: BTreeMap<String, u32>,
    /// Promises seen with tags that make them awaitable.
    pub external: BTreeSet<String>,
}

impl Seen {
    pub fn note(&mut self, data: &Value) {
        if let Some(t) = data.get("task") {
            if let (Some(id), Some(v)) = (t.get("id").and_then(Value::as_str), t.get("version").and_then(Value::as_u64)) {
                self.versions.insert(id.to_string(), v as u32);
            }
        }
        if let Some(p) = data.get("promise") {
            if let (Some(id), Some(tags)) = (p.get("id").and_then(Value::as_str), p.get("tags")) {
                // A promise created with a target is born with a task at version 0.
                if tags.get("resonate:target").is_some() && !self.versions.contains_key(id) {
                    self.versions.insert(id.to_string(), 0);
                }
                let external = tags.get("resonate:target").is_some()
                    || tags.get("resonate:scope").and_then(Value::as_str) == Some("global")
                    || tags.get("resonate:external").and_then(Value::as_str) == Some("true")
                    || tags.get("resonate:timer").and_then(Value::as_str) == Some("true");
                if external {
                    self.external.insert(id.to_string());
                }
            }
        }
    }
}

pub struct Generator {
    pub origins: u64,
    pub promises_per_origin: u64,
    /// Whether clients create, read and delete schedules at all. Off while
    /// the rest of the protocol is being squared with the model: a schedule's
    /// occurrence is the one step a client cannot read off the clock.
    pub schedules: bool,
    /// Promise timeouts fall within `now + 1 ..= now + timeout_ms`.
    pub timeout_ms: u64,
    /// Task leases fall within `1 ..= ttl_ms`.
    pub ttl_ms: u64,
}

const PLAIN: Tags = Tags { target: false, external: false, timer: false, delay: None };

impl Generator {
    fn id(&self, rng: &mut Rng) -> String {
        format!("o{}:{}", rng.below(self.origins), 1 + rng.below(self.promises_per_origin))
    }

    /// Every id a run may name: the promises, their children, and the
    /// schedules' ids. What the finishing reads read.
    pub fn ids(&self) -> Vec<String> {
        let mut v = Vec::new();
        for o in 0..self.origins {
            for p in 1..=self.promises_per_origin {
                v.push(format!("o{o}:{p}"));
                v.push(format!("o{o}:{p}.1"));
            }
        }
        v
    }

    /// Another promise of the same origin the client has seen as awaitable,
    /// if it has; else any other promise of the origin.
    fn awaitable_sibling(&self, id: &str, seen: &Seen, rng: &mut Rng) -> String {
        let origin = echod_logic::keys::origin_of(id);
        let known: Vec<&String> = seen.external.iter().filter(|p| p.as_str() != id && echod_logic::keys::origin_of(p) == origin).collect();
        if !known.is_empty() && rng.percent(80) {
            return (*rng.pick(&known)).clone();
        }
        self.sibling(id, rng)
    }

    /// Another promise of the same origin, never `id` itself.
    fn sibling(&self, id: &str, rng: &mut Rng) -> String {
        let origin = echod_logic::keys::origin_of(id);
        for _ in 0..8 {
            let s = format!("{}:{}", origin, 1 + rng.below(self.promises_per_origin));
            if s != id {
                return s;
            }
        }
        format!("{origin}:{}", self.promises_per_origin + 1)
    }

    /// A task to operate on: one the client has seen, mostly.
    fn task_id(&self, seen: &Seen, rng: &mut Rng) -> String {
        let known: Vec<&String> = seen.versions.keys().collect();
        if !known.is_empty() && rng.percent(75) {
            return (*rng.pick(&known)).clone();
        }
        self.id(rng)
    }

    /// A target when runnable, else half the time; else external, mostly;
    /// a timer now and then, never with a target (echod would drop the
    /// target, a concession the model does not make).
    fn tags(&self, rng: &mut Rng, runnable: bool) -> Tags {
        let target = runnable || rng.percent(50);
        let external = !target && rng.percent(70);
        let timer = !target && rng.percent(10);
        Tags { target, external, timer, delay: None }
    }

    fn version(&self, id: &str, seen: &Seen, rng: &mut Rng) -> u32 {
        match seen.versions.get(id) {
            Some(v) if rng.percent(80) => *v,
            _ => rng.below(3) as u32,
        }
    }

    fn settle_state(rng: &mut Rng) -> String {
        match rng.below(3) {
            0 => "resolved",
            1 => "rejected",
            _ => "rejected_canceled",
        }
        .to_string()
    }

    /// A schedule: a few ids, firing every few seconds into one origin, so
    /// that fires and client requests collide on the origin's document.
    fn schedule(&self, rng: &mut Rng) -> Request {
        let id = (*rng.pick(&SCHEDULES)).to_string();
        match rng.below(10) {
            0..=2 => Request::GetSchedule(id),
            3..=7 => {
                let cron = (*rng.pick(&["*/2 * * * * *", "*/3 * * * * *", "*/5 * * * * *"])).to_string();
                let promise_id = format!("o{}:{id}-{{{{.timestamp}}}}", rng.below(self.origins));
                let promise_timeout = rng.range(1, self.timeout_ms);
                // the protocol requires a target on a schedule's promise
                Request::CreateSchedule(ScheduleCreate { id, cron, promise_id, promise_timeout, promise_param: None, promise_tags: self.tags(rng, true) })
            }
            _ => Request::DeleteSchedule(id),
        }
    }

    pub fn next(&self, rng: &mut Rng, seen: &Seen, now: u64) -> Request {
        if self.schedules && rng.percent(4) {
            return self.schedule(rng);
        }
        let roll = rng.below(100);
        let id = if roll >= 46 { self.task_id(seen, rng) } else { self.id(rng) };
        let pid = format!("p{}", rng.below(3));
        let ttl = rng.range(self.ttl_ms / 4, self.ttl_ms);
        let timeout_at = now + rng.range(1, self.timeout_ms);
        let data = Some(format!("d{}", rng.below(4)));
        match roll {
            0..=11 => Request::GetPromise(id),
            12..=27 => Request::CreatePromise(Create { id, timeout_at, data, tags: self.tags(rng, false) }),
            28..=35 => Request::SettlePromise(Settle { id, state: Self::settle_state(rng), data }),
            36..=40 => {
                let awaited = self.awaitable_sibling(&id, seen, rng);
                Request::RegisterCallback { awaited, awaiter: id }
            }
            41..=45 => Request::RegisterListener { awaited: id, address: WORKER.to_string() },
            46..=51 => Request::GetTask(id),
            52..=58 => Request::CreateTask { pid, ttl, action: Create { id, timeout_at, data: None, tags: self.tags(rng, true) } },
            59..=68 => {
                let version = self.version(&id, seen, rng);
                Request::AcquireTask { id, version, pid, ttl }
            }
            69..=74 => {
                let version = self.version(&id, seen, rng);
                Request::FulfillTask { id, version, state: Self::settle_state(rng), data }
            }
            75..=77 => {
                let version = self.version(&id, seen, rng);
                Request::ReleaseTask { id, version }
            }
            78..=80 => {
                let version = self.version(&id, seen, rng);
                Request::HeartbeatTask { pid, tasks: vec![TaskRef { id, version }] }
            }
            81..=85 => {
                let version = self.version(&id, seen, rng);
                let awaited = vec![self.awaitable_sibling(&id, seen, rng)];
                Request::SuspendTask { id, version, awaited }
            }
            86..=90 => {
                let version = self.version(&id, seen, rng);
                let child = format!("{id}.1");
                Request::FenceTask { id, version, action: Fenced::Create(Create { id: child, timeout_at, data: None, tags: self.tags(rng, false) }) }
            }
            91..=94 => {
                let version = self.version(&id, seen, rng);
                let target = if rng.percent(50) { format!("{id}.1") } else { self.sibling(&id, rng) };
                Request::FenceTask { id, version, action: Fenced::Settle(Settle { id: target, state: Self::settle_state(rng), data }) }
            }
            95..=97 => Request::HaltTask(id),
            _ => Request::ContinueTask(id),
        }
    }
}

/// `PLAIN`, for callers building tags of their own.
pub fn plain() -> Tags {
    PLAIN
}
