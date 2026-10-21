//! The requests a run issues, and how they are generated.
//!
//! Every request kind the server serves, over a small space of ids so that
//! operations collide: a few origins, a few promises per origin, one child
//! each. Versions and pids are drawn from what the client has seen, so that
//! fenced operations sometimes carry the right version and sometimes not.

use std::collections::BTreeMap;

use echod_kernel as k;
use serde::Serialize;
use serde_json::{json, Value};

use crate::rng::Rng;

/// The worker every task is dispatched to, and every listener listens at.
pub const WORKER: &str = "sim://worker";

/// A schedule's row, as a history entry carries it: the kernel's record,
/// shown by its id.
#[derive(Clone, Serialize)]
pub struct Row(pub k::Schedule);

impl std::fmt::Debug for Row {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Schedule({})", self.0.id)
    }
}

#[derive(Clone, Debug, Serialize)]
pub enum Op {
    PromiseGet { id: String },
    PromiseCreate { id: String, timeout_at: u64, tags: BTreeMap<String, String>, data: String },
    PromiseSettle { id: String, state: k::PromiseState, data: String },
    RegisterCallback { awaited: String, awaiter: String },
    RegisterListener { awaited: String, address: String },
    TaskGet { id: String },
    TaskCreate { pid: String, ttl: u64, id: String, timeout_at: u64, tags: BTreeMap<String, String> },
    TaskAcquire { id: String, version: u64, pid: String, ttl: u64 },
    TaskFulfill { id: String, version: u64, state: k::PromiseState, data: String },
    TaskRelease { id: String, version: u64 },
    TaskHeartbeat { pid: String, tasks: Vec<(String, u64)> },
    TaskSuspend { id: String, version: u64, awaited: Vec<String> },
    TaskFenceCreate { id: String, version: u64, child: String, timeout_at: u64, tags: BTreeMap<String, String> },
    TaskFenceSettle { id: String, version: u64, target: String, state: k::PromiseState, data: String },
    TaskHalt { id: String },
    TaskContinue { id: String },
    ScheduleGet { id: String },
    ScheduleCreate { id: String, cron: String, promise_id: String, promise_timeout: u64, tags: BTreeMap<String, String> },
    ScheduleDelete { id: String },
    /// The internal step a timer fires: not a client's, recorded by the observer.
    Sweep,
    /// A schedule's fire on the occurrence's origin: the row as the node
    /// loaded it, the occurrence, the promise, the run after. Recorded by
    /// the observer.
    Fire { schedule: Row, at: u64, promise_id: String, next: u64 },
    /// The fire's second half, on the schedule's document. Recorded by the
    /// observer.
    Advance { id: String, at: u64, next: u64 },
}

impl Op {
    pub fn kind(&self) -> &'static str {
        match self {
            Op::PromiseGet { .. } => "promise.get",
            Op::PromiseCreate { .. } => "promise.create",
            Op::PromiseSettle { .. } => "promise.settle",
            Op::RegisterCallback { .. } => "promise.register_callback",
            Op::RegisterListener { .. } => "promise.register_listener",
            Op::TaskGet { .. } => "task.get",
            Op::TaskCreate { .. } => "task.create",
            Op::TaskAcquire { .. } => "task.acquire",
            Op::TaskFulfill { .. } => "task.fulfill",
            Op::TaskRelease { .. } => "task.release",
            Op::TaskHeartbeat { .. } => "task.heartbeat",
            Op::TaskSuspend { .. } => "task.suspend",
            Op::TaskFenceCreate { .. } | Op::TaskFenceSettle { .. } => "task.fence",
            Op::TaskHalt { .. } => "task.halt",
            Op::TaskContinue { .. } => "task.continue",
            Op::ScheduleGet { .. } => "schedule.get",
            Op::ScheduleCreate { .. } => "schedule.create",
            Op::ScheduleDelete { .. } => "schedule.delete",
            Op::Sweep => "sweep",
            Op::Fire { .. } => "fire",
            Op::Advance { .. } => "advance",
        }
    }

    /// The origin the operation is about.
    pub fn origin(&self) -> String {
        let id = match self {
            Op::PromiseGet { id }
            | Op::PromiseCreate { id, .. }
            | Op::PromiseSettle { id, .. }
            | Op::TaskGet { id }
            | Op::TaskCreate { id, .. }
            | Op::TaskAcquire { id, .. }
            | Op::TaskFulfill { id, .. }
            | Op::TaskRelease { id, .. }
            | Op::TaskSuspend { id, .. }
            | Op::TaskFenceCreate { id, .. }
            | Op::TaskFenceSettle { id, .. }
            | Op::TaskHalt { id }
            | Op::TaskContinue { id } => id.clone(),
            Op::RegisterCallback { awaited, .. } | Op::RegisterListener { awaited, .. } => awaited.clone(),
            Op::TaskHeartbeat { tasks, .. } => tasks[0].0.clone(),
            Op::ScheduleGet { id } | Op::ScheduleCreate { id, .. } | Op::ScheduleDelete { id } | Op::Advance { id, .. } => return format!("sched:{id}"),
            Op::Fire { promise_id, .. } => promise_id.clone(),
            Op::Sweep => String::new(),
        };
        echod_server::keys::origin_of(&id).to_string()
    }

    fn state_str(s: k::PromiseState) -> &'static str {
        match s {
            k::PromiseState::Resolved => "resolved",
            k::PromiseState::Rejected => "rejected",
            _ => "rejected_canceled",
        }
    }

    /// The request's `data` on the wire.
    pub fn data(&self) -> Value {
        match self {
            Op::PromiseGet { id } => json!({ "id": id }),
            Op::PromiseCreate { id, timeout_at, tags, data } => json!({ "id": id, "timeoutAt": timeout_at, "tags": tags, "param": { "data": data } }),
            Op::PromiseSettle { id, state, data } => json!({ "id": id, "state": Self::state_str(*state), "value": { "data": data } }),
            Op::RegisterCallback { awaited, awaiter } => json!({ "awaited": awaited, "awaiter": awaiter }),
            Op::RegisterListener { awaited, address } => json!({ "awaited": awaited, "address": address }),
            Op::TaskGet { id } => json!({ "id": id }),
            Op::TaskCreate { pid, ttl, id, timeout_at, tags } => {
                json!({ "pid": pid, "ttl": ttl, "action": { "kind": "promise.create", "head": {}, "data": { "id": id, "timeoutAt": timeout_at, "tags": tags } } })
            }
            Op::TaskAcquire { id, version, pid, ttl } => json!({ "id": id, "version": version, "pid": pid, "ttl": ttl }),
            Op::TaskFulfill { id, version, state, data } => {
                json!({ "id": id, "version": version, "action": { "kind": "promise.settle", "head": {}, "data": { "id": id, "state": Self::state_str(*state), "value": { "data": data } } } })
            }
            Op::TaskRelease { id, version } => json!({ "id": id, "version": version }),
            Op::TaskHeartbeat { pid, tasks } => json!({ "pid": pid, "tasks": tasks.iter().map(|(id, v)| json!({ "id": id, "version": v })).collect::<Vec<_>>() }),
            Op::TaskSuspend { id, version, awaited } => json!({
                "id": id, "version": version,
                "actions": awaited.iter().map(|a| json!({ "kind": "promise.register_callback", "head": {}, "data": { "awaited": a, "awaiter": id } })).collect::<Vec<_>>()
            }),
            Op::TaskFenceCreate { id, version, child, timeout_at, tags } => {
                json!({ "id": id, "version": version, "action": { "kind": "promise.create", "head": {}, "data": { "id": child, "timeoutAt": timeout_at, "tags": tags } } })
            }
            Op::TaskFenceSettle { id, version, target, state, data } => {
                json!({ "id": id, "version": version, "action": { "kind": "promise.settle", "head": {}, "data": { "id": target, "state": Self::state_str(*state), "value": { "data": data } } } })
            }
            Op::TaskHalt { id } | Op::TaskContinue { id } => json!({ "id": id }),
            Op::ScheduleGet { id } | Op::ScheduleDelete { id } => json!({ "id": id }),
            Op::ScheduleCreate { id, cron, promise_id, promise_timeout, tags } => {
                json!({ "id": id, "cron": cron, "promiseId": promise_id, "promiseTimeout": promise_timeout, "promiseTags": tags })
            }
            Op::Sweep | Op::Fire { .. } | Op::Advance { .. } => json!({}),
        }
    }
}

/// What a client has learned, to draw plausible versions and pids from.
#[derive(Default)]
pub struct Seen {
    pub versions: BTreeMap<String, u64>,
    /// Promises seen with tags that make them awaitable.
    pub external: std::collections::BTreeSet<String>,
}

impl Seen {
    pub fn note(&mut self, data: &Value) {
        if let Some(t) = data.get("task") {
            if let (Some(id), Some(v)) = (t.get("id").and_then(Value::as_str), t.get("version").and_then(Value::as_u64)) {
                self.versions.insert(id.to_string(), v);
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
    /// Promise timeouts fall within `now + 1 ..= now + timeout_ms`.
    pub timeout_ms: u64,
    /// Task leases fall within `1 ..= ttl_ms`.
    pub ttl_ms: u64,
}

impl Generator {
    fn id(&self, rng: &mut Rng) -> String {
        format!("o{}:{}", rng.below(self.origins), 1 + rng.below(self.promises_per_origin))
    }

    /// Another promise of the same origin the client has seen as awaitable,
    /// if it has; else any other promise of the origin.
    fn awaitable_sibling(&self, id: &str, seen: &Seen, rng: &mut Rng) -> String {
        let origin = echod_server::keys::origin_of(id);
        let known: Vec<&String> = seen.external.iter().filter(|p| p.as_str() != id && echod_server::keys::origin_of(p) == origin).collect();
        if !known.is_empty() && rng.percent(80) {
            return (*rng.pick(&known)).clone();
        }
        self.sibling(id, rng)
    }

    /// Another promise of the same origin, never `id` itself.
    fn sibling(&self, id: &str, rng: &mut Rng) -> String {
        let origin = echod_server::keys::origin_of(id);
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

    fn tags(&self, rng: &mut Rng, runnable: bool) -> BTreeMap<String, String> {
        let mut t = BTreeMap::new();
        if runnable || rng.percent(50) {
            t.insert("resonate:target".into(), WORKER.into());
        } else if rng.percent(70) {
            t.insert("resonate:scope".into(), "global".into());
        }
        if !runnable && rng.percent(10) {
            t.insert("resonate:timer".into(), "true".into());
        }
        t
    }

    fn version(&self, id: &str, seen: &Seen, rng: &mut Rng) -> u64 {
        match seen.versions.get(id) {
            Some(v) if rng.percent(80) => *v,
            _ => rng.below(3),
        }
    }

    fn settle_state(rng: &mut Rng) -> k::PromiseState {
        match rng.below(3) {
            0 => k::PromiseState::Resolved,
            1 => k::PromiseState::Rejected,
            _ => k::PromiseState::RejectedCanceled,
        }
    }

    /// A schedule: a few ids, firing every few seconds into one origin, so
    /// that fires and client requests collide on the origin's document.
    fn schedule(&self, rng: &mut Rng) -> Op {
        let id = format!("s{}", rng.below(3));
        match rng.below(10) {
            0..=2 => Op::ScheduleGet { id },
            3..=7 => {
                let cron = (*rng.pick(&["*/2 * * * * *", "*/3 * * * * *", "*/5 * * * * *"])).to_string();
                let promise_id = format!("o{}:{id}-{{{{.timestamp}}}}", rng.below(self.origins));
                let promise_timeout = rng.range(1, self.timeout_ms);
                // the protocol requires a target on a schedule's promise
                Op::ScheduleCreate { id, cron, promise_id, promise_timeout, tags: self.tags(rng, true) }
            }
            _ => Op::ScheduleDelete { id },
        }
    }

    pub fn next(&self, rng: &mut Rng, seen: &Seen, now: u64) -> Op {
        if rng.percent(4) {
            return self.schedule(rng);
        }
        let roll = rng.below(100);
        let id = if roll >= 46 { self.task_id(seen, rng) } else { self.id(rng) };
        let pid = format!("p{}", rng.below(3));
        let ttl = rng.range(self.ttl_ms / 4, self.ttl_ms);
        let timeout_at = now + rng.range(1, self.timeout_ms);
        let data = format!("d{}", rng.below(4));
        match roll {
            0..=11 => Op::PromiseGet { id },
            12..=27 => Op::PromiseCreate { id: id.clone(), timeout_at, tags: self.tags(rng, false), data },
            28..=35 => Op::PromiseSettle { id, state: Self::settle_state(rng), data },
            36..=40 => {
                let awaited = self.awaitable_sibling(&id, seen, rng);
                Op::RegisterCallback { awaited, awaiter: id }
            }
            41..=45 => Op::RegisterListener { awaited: id, address: WORKER.to_string() },
            46..=51 => Op::TaskGet { id },
            52..=58 => Op::TaskCreate { pid, ttl, id, timeout_at, tags: self.tags(rng, true) },
            59..=68 => {
                let version = self.version(&id, seen, rng);
                Op::TaskAcquire { id, version, pid, ttl }
            }
            69..=74 => {
                let version = self.version(&id, seen, rng);
                Op::TaskFulfill { id, version, state: Self::settle_state(rng), data }
            }
            75..=77 => {
                let version = self.version(&id, seen, rng);
                Op::TaskRelease { id, version }
            }
            78..=80 => {
                let version = self.version(&id, seen, rng);
                Op::TaskHeartbeat { pid, tasks: vec![(id, version)] }
            }
            81..=85 => {
                let version = self.version(&id, seen, rng);
                let awaited = vec![self.awaitable_sibling(&id, seen, rng)];
                Op::TaskSuspend { id, version, awaited }
            }
            86..=90 => {
                let version = self.version(&id, seen, rng);
                let child = format!("{id}.1");
                Op::TaskFenceCreate { id, version, child, timeout_at, tags: self.tags(rng, false) }
            }
            91..=94 => {
                let version = self.version(&id, seen, rng);
                let target = if rng.percent(50) { format!("{id}.1") } else { self.sibling(&id, rng) };
                Op::TaskFenceSettle { id, version, target, state: Self::settle_state(rng), data }
            }
            95..=97 => Op::TaskHalt { id },
            _ => Op::TaskContinue { id },
        }
    }
}
