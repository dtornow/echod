//! The request stream: what the reference's own differential issues, over
//! the same ids, so the two runs explore the same corner of the protocol.
//!
//! Adapted from `impl/server/core/diff/port.rs` in `resonatehq/resonate`
//! (Apache-2.0): the same operation mix, the same id pools, the same way
//! of steering towards the operations not yet covered. The search
//! operations are left out: echod does not serve them, and says so with a
//! 403 that the reference does not give. The planner reads the reference's
//! snapshot after every step instead of an in-process model, so this
//! harness needs nothing of the reference but its HTTP port.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use echod_sim::rng::Rng;
use serde_json::{json, Value};

/// The worker every task is dispatched to, and every listener listens at:
/// the harness's sink.
pub struct Ids<'a> {
    pub worker: &'a str,
}

pub const PID: &str = "diff-pid";
pub const TTL: i64 = 60_000;

/// Every operation that must answer 2xx at least once before a run may
/// stop.
pub const ALL_OPS: &[&str] = &[
    "promise.create",
    "promise.get",
    "promise.settle",
    "promise.register_callback",
    "promise.register_listener",
    "task.create",
    "task.get",
    "task.acquire",
    "task.release",
    "task.fulfill",
    "task.suspend",
    "task.fence",
    "task.heartbeat",
    "task.halt",
    "task.continue",
    "schedule.create",
    "schedule.get",
    "schedule.delete",
    "debug.tick",
];

/// What the planner knows of the state: the reference's last snapshot,
/// plus the schedules, which the snapshot does not carry.
#[derive(Default, Clone)]
pub struct Model {
    /// id -> (state, tags, timeout_at)
    pub promises: BTreeMap<String, (String, BTreeMap<String, String>, i64)>,
    /// id -> (state, version)
    pub tasks: BTreeMap<String, (String, i64)>,
    pub schedules: BTreeSet<String>,
}

impl Model {
    /// Take the reference's snapshot on.
    pub fn read(&mut self, snap: &Value) {
        self.promises.clear();
        self.tasks.clear();
        if let Some(ps) = snap["promises"].as_array() {
            for p in ps {
                let id = p["id"].as_str().unwrap_or_default().to_string();
                let state = p["state"].as_str().unwrap_or_default().to_string();
                let tags: BTreeMap<String, String> = p["tags"].as_object().map(|m| m.iter().filter_map(|(k, v)| v.as_str().map(|s| (k.clone(), s.to_string()))).collect()).unwrap_or_default();
                let timeout = p["timeoutAt"].as_i64().unwrap_or(0);
                self.promises.insert(id, (state, tags, timeout));
            }
        }
        if let Some(ts) = snap["tasks"].as_array() {
            for t in ts {
                let id = t["id"].as_str().unwrap_or_default().to_string();
                let state = t["state"].as_str().unwrap_or_default().to_string();
                let version = t["version"].as_i64().unwrap_or(0);
                self.tasks.insert(id, (state, version));
            }
        }
    }

    /// A schedule request answered 200: the set moved.
    pub fn schedule_answered(&mut self, kind: &str, data: &Value) {
        match kind {
            "schedule.create" => {
                if let Some(id) = data["schedule"]["id"].as_str() {
                    self.schedules.insert(id.to_string());
                }
            }
            "schedule.delete" => {
                // the id is in the request, which the caller passes as data here
                if let Some(id) = data["id"].as_str() {
                    self.schedules.remove(id);
                }
            }
            _ => {}
        }
    }

    pub fn reset(&mut self) {
        *self = Model::default();
    }

    fn all_promise_ids(&self) -> Vec<String> {
        self.promises.keys().cloned().collect()
    }
    fn pending_promise_ids(&self) -> Vec<String> {
        self.promises.iter().filter(|(_, (s, _, _))| s == "pending").map(|(id, _)| id.clone()).collect()
    }
    /// Pending, and external: no target, but awaitable.
    fn external_pending_promise_ids(&self) -> Vec<String> {
        self.promises
            .iter()
            .filter(|(_, (s, tags, _))| s == "pending" && !tags.contains_key("resonate:target") && (tags.get("resonate:external").map(String::as_str) == Some("true") || tags.get("resonate:scope").map(String::as_str) == Some("global") || tags.get("resonate:timer").map(String::as_str) == Some("true")))
            .map(|(id, _)| id.clone())
            .collect()
    }
    fn has_pending_promises(&self) -> bool {
        !self.pending_promise_ids().is_empty()
    }
    fn has_pending_promises_with_target(&self) -> bool {
        self.promises.values().any(|(s, tags, _)| s == "pending" && tags.contains_key("resonate:target"))
    }
    fn tasks_by_state(&self, state: &str) -> Vec<(String, i64)> {
        self.tasks.iter().filter(|(_, (s, _))| s == state).map(|(id, (_, v))| (id.clone(), *v)).collect()
    }
    fn has_tasks_in_state(&self, state: &str) -> bool {
        !self.tasks_by_state(state).is_empty()
    }
    fn has_schedules(&self) -> bool {
        !self.schedules.is_empty()
    }
    fn schedule_ids(&self) -> Vec<String> {
        self.schedules.iter().cloned().collect()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Op {
    PromiseCreate,
    PromiseGet,
    PromiseSettle,
    PromiseRegisterCallback,
    PromiseRegisterListener,
    TaskCreate,
    TaskGet,
    TaskAcquire,
    TaskRelease,
    TaskFulfill,
    TaskSuspend,
    TaskFence,
    TaskHeartbeat,
    TaskHalt,
    TaskContinue,
    ScheduleCreate,
    ScheduleGet,
    ScheduleDelete,
    DebugTick,
}

fn pick<T: Clone>(rng: &mut Rng, v: &[T]) -> Option<T> {
    if v.is_empty() {
        None
    } else {
        Some(rng.pick(v).clone())
    }
}

fn chance(rng: &mut Rng, n: u64) -> u64 {
    rng.below(n)
}

pub fn pick_op(rng: &mut Rng, m: &Model, covered: &HashMap<String, usize>) -> Op {
    let uncovered = |kind: &str| !covered.contains_key(kind);
    let has_acquired = m.has_tasks_in_state("acquired");
    let has_pending_t = m.has_tasks_in_state("pending");
    let has_suspended = m.has_tasks_in_state("suspended");
    let has_halted = m.has_tasks_in_state("halted");
    let has_pending_p = m.has_pending_promises();
    let has_pending_p_with_target = m.has_pending_promises_with_target();
    let has_schedules = m.has_schedules();

    if uncovered("task.suspend") && has_acquired && has_pending_p_with_target {
        return Op::TaskSuspend;
    }
    if uncovered("task.continue") && has_halted {
        return Op::TaskContinue;
    }
    if uncovered("task.release") && has_acquired {
        return Op::TaskRelease;
    }
    if uncovered("task.fulfill") && has_acquired {
        return Op::TaskFulfill;
    }
    if uncovered("task.halt") && (has_acquired || has_pending_t || has_suspended) {
        return Op::TaskHalt;
    }
    if uncovered("task.acquire") && has_pending_t {
        return Op::TaskAcquire;
    }
    if uncovered("promise.register_callback") && has_pending_p_with_target && (has_acquired || has_pending_t) {
        return Op::PromiseRegisterCallback;
    }
    if uncovered("promise.register_listener") && has_pending_p {
        return Op::PromiseRegisterListener;
    }
    if uncovered("schedule.delete") && has_schedules {
        return Op::ScheduleDelete;
    }
    if uncovered("task.fence") && has_acquired {
        return Op::TaskFence;
    }

    // The reference's mix, with the search slots given to the reads.
    match chance(rng, 100) {
        0..=14 => Op::PromiseCreate,
        15..=19 => Op::PromiseGet,
        20..=24 => Op::PromiseSettle,
        25..=27 => Op::PromiseRegisterCallback,
        28..=29 => Op::PromiseRegisterListener,
        30..=31 => Op::PromiseGet,
        32..=39 => Op::TaskCreate,
        40..=41 => Op::TaskGet,
        42..=44 => Op::TaskAcquire,
        45..=47 => Op::TaskRelease,
        48..=52 => Op::TaskFulfill,
        53..=57 => Op::TaskSuspend,
        58..=60 => Op::TaskFence,
        61..=63 => Op::TaskHeartbeat,
        64..=66 => Op::TaskHalt,
        67..=69 => Op::TaskContinue,
        70..=71 => Op::TaskGet,
        72..=77 => Op::ScheduleCreate,
        78..=80 => Op::ScheduleGet,
        81..=83 => Op::ScheduleDelete,
        84..=85 => Op::ScheduleGet,
        _ => Op::DebugTick,
    }
}

/// The request for `op`: its kind and data, and the instant the run is at
/// afterwards (a tick moves it).
pub fn build(op: Op, rng: &mut Rng, m: &Model, now: i64, ids: &Ids) -> (&'static str, Value, i64) {
    let worker = ids.worker;
    match op {
        Op::PromiseCreate => {
            let all = m.all_promise_ids();
            let id = pick(rng, &all).unwrap_or_else(|| random_promise_id(rng));
            let timeout_at = now + rng.range(30_000, 299_999) as i64;
            let tags = match chance(rng, 6) {
                0..=2 => json!({ "resonate:external": "true" }),
                3 => json!({ "resonate:timer": "true" }),
                _ => json!({}),
            };
            ("promise.create", json!({ "id": id, "timeoutAt": timeout_at, "param": {}, "tags": tags }), now)
        }
        Op::PromiseGet => {
            let all = m.all_promise_ids();
            let id = pick(rng, &all).unwrap_or_else(|| random_promise_id(rng));
            ("promise.get", json!({ "id": id }), now)
        }
        Op::PromiseSettle => {
            let pending = m.pending_promise_ids();
            let id = pick(rng, &pending).unwrap_or_else(|| random_promise_id(rng));
            let state = if rng.percent(50) { "resolved" } else { "rejected" };
            ("promise.settle", json!({ "id": id, "state": state, "value": {} }), now)
        }
        Op::PromiseRegisterCallback => {
            let acquired = m.tasks_by_state("acquired");
            let pending_t = m.tasks_by_state("pending");
            let awaiter = pick(rng, &acquired).or_else(|| pick(rng, &pending_t)).map(|(id, _)| id).unwrap_or_else(|| random_task_id(rng));
            let awaited = pick_awaited(rng, m, &awaiter);
            ("promise.register_callback", json!({ "awaited": awaited, "awaiter": awaiter }), now)
        }
        Op::PromiseRegisterListener => {
            let pending = m.pending_promise_ids();
            let id = pick(rng, &pending).unwrap_or_else(|| random_promise_id(rng));
            ("promise.register_listener", json!({ "awaited": id, "address": worker }), now)
        }
        Op::TaskCreate => {
            let id = task_id(chance(rng, 8));
            let timeout_at = now + rng.range(60_000, 599_999) as i64;
            (
                "task.create",
                json!({
                    "pid": PID,
                    "ttl": TTL,
                    "action": { "kind": "promise.create", "head": {}, "data": { "id": id, "timeoutAt": timeout_at, "param": {}, "tags": { "resonate:target": worker } } }
                }),
                now,
            )
        }
        Op::TaskGet => {
            let mut all = m.tasks_by_state("acquired");
            all.extend(m.tasks_by_state("pending"));
            all.extend(m.tasks_by_state("suspended"));
            all.extend(m.tasks_by_state("halted"));
            let id = pick(rng, &all).map(|(id, _)| id).unwrap_or_else(|| random_task_id(rng));
            ("task.get", json!({ "id": id }), now)
        }
        Op::TaskAcquire => {
            let pending = m.tasks_by_state("pending");
            let (id, version) = pick(rng, &pending).unwrap_or_else(|| (random_task_id(rng), 0));
            ("task.acquire", json!({ "id": id, "version": version, "pid": PID, "ttl": TTL }), now)
        }
        Op::TaskRelease => {
            let acquired = m.tasks_by_state("acquired");
            let (id, version) = pick(rng, &acquired).unwrap_or_else(|| (random_task_id(rng), 1));
            ("task.release", json!({ "id": id, "version": version }), now)
        }
        Op::TaskFulfill => {
            let acquired = m.tasks_by_state("acquired");
            let (id, version) = pick(rng, &acquired).unwrap_or_else(|| (random_task_id(rng), 1));
            let state = if rng.percent(50) { "resolved" } else { "rejected" };
            (
                "task.fulfill",
                json!({ "id": id, "version": version, "action": { "kind": "promise.settle", "head": {}, "data": { "id": id, "state": state, "value": {} } } }),
                now,
            )
        }
        Op::TaskSuspend => {
            let acquired = m.tasks_by_state("acquired");
            let (task_id, version) = pick(rng, &acquired).unwrap_or_else(|| (random_task_id(rng), 1));
            let awaited = pick_awaited(rng, m, &task_id);
            (
                "task.suspend",
                json!({ "id": task_id, "version": version, "actions": [{ "kind": "promise.register_callback", "head": {}, "data": { "awaited": awaited, "awaiter": task_id } }] }),
                now,
            )
        }
        Op::TaskFence => {
            let acquired = m.tasks_by_state("acquired");
            let (task_id, version) = pick(rng, &acquired).unwrap_or_else(|| (random_task_id(rng), 1));
            let task_origin = task_id.split(':').next().unwrap_or("").to_string();
            // same origin only: a settle shares the task's origin, and so does
            // a create. A create in another origin (a detached workflow) is
            // where the two servers part by design: the reference allows a
            // root id alone and checks the fence first, echod allows any id
            // and creates first (BACKLOG, "Detached creates").
            let pending_p: Vec<String> = m.pending_promise_ids().into_iter().filter(|p| p.split(':').next().unwrap_or("") == task_origin).collect();
            let do_settle = !pending_p.is_empty() && chance(rng, 4) != 0;
            if !do_settle {
                let new_promise_id = match chance(rng, 8) {
                    0..=4 => format!("{task_origin}:p{}", chance(rng, 8)),
                    _ => format!("{task_origin}:q{}", chance(rng, 8)),
                };
                let timeout_at = now + rng.range(30_000, 299_999) as i64;
                (
                    "task.fence",
                    json!({ "id": task_id, "version": version, "action": { "kind": "promise.create", "head": {}, "data": { "id": new_promise_id, "timeoutAt": timeout_at, "param": {}, "tags": {} } } }),
                    now,
                )
            } else {
                let pid = pick(rng, &pending_p).unwrap_or_else(|| random_promise_id(rng));
                let state = if rng.percent(50) { "resolved" } else { "rejected" };
                (
                    "task.fence",
                    json!({ "id": task_id, "version": version, "action": { "kind": "promise.settle", "head": {}, "data": { "id": pid, "state": state, "value": {} } } }),
                    now,
                )
            }
        }
        Op::TaskHeartbeat => {
            let mut acquired = m.tasks_by_state("acquired");
            let take = acquired.len().min(3);
            for i in 0..take {
                let j = i + rng.below((acquired.len() - i) as u64) as usize;
                acquired.swap(i, j);
            }
            let mut tasks: Vec<Value> = Vec::new();
            for (id, version) in acquired.into_iter().take(3) {
                let v = if chance(rng, 4) == 0 { version - 1 } else { version };
                tasks.push(json!({ "id": id, "version": v }));
            }
            if tasks.is_empty() {
                tasks.push(json!({ "id": random_task_id(rng), "version": chance(rng, 3) }));
            }
            let pid = if chance(rng, 7) == 0 { "wrong-pid" } else { PID };
            ("task.heartbeat", json!({ "pid": pid, "tasks": tasks }), now)
        }
        Op::TaskHalt => {
            let mut all = m.tasks_by_state("acquired");
            all.extend(m.tasks_by_state("suspended"));
            all.extend(m.tasks_by_state("pending"));
            let id = pick(rng, &all).map(|(id, _)| id).unwrap_or_else(|| random_task_id(rng));
            ("task.halt", json!({ "id": id }), now)
        }
        Op::TaskContinue => {
            let halted = m.tasks_by_state("halted");
            let id = pick(rng, &halted).map(|(id, _)| id).unwrap_or_else(|| random_task_id(rng));
            ("task.continue", json!({ "id": id }), now)
        }
        Op::ScheduleCreate => {
            let id = schedule_id(chance(rng, 4));
            let promise_timeout = now + rng.range(60_000, 599_999) as i64;
            (
                "schedule.create",
                json!({ "id": id, "cron": "* * * * *", "promiseId": "sched-promise-{{.id}}-{{.timestamp}}", "promiseTimeout": promise_timeout, "promiseParam": {}, "promiseTags": { "resonate:target": worker } }),
                now,
            )
        }
        Op::ScheduleGet => {
            let s = m.schedule_ids();
            let id = pick(rng, &s).unwrap_or_else(|| random_schedule_id(rng));
            ("schedule.get", json!({ "id": id }), now)
        }
        Op::ScheduleDelete => {
            let s = m.schedule_ids();
            let id = pick(rng, &s).unwrap_or_else(|| random_schedule_id(rng));
            ("schedule.delete", json!({ "id": id }), now)
        }
        Op::DebugTick => {
            let new_now = now + rng.range(0, 49_999) as i64;
            ("debug.tick", json!({ "time": new_now }), new_now)
        }
    }
}

/// An awaited promise for a callback or a suspend: mostly awaitable, one
/// time in four whatever is pending, so the 422 stays covered.
fn pick_awaited(rng: &mut Rng, m: &Model, awaiter: &str) -> String {
    if chance(rng, 4) != 0 {
        let external = m.external_pending_promise_ids();
        if let Some(id) = external.iter().find(|p| p.as_str() != awaiter) {
            return id.clone();
        }
    }
    m.pending_promise_ids().iter().find(|p| p.as_str() != awaiter).cloned().unwrap_or_else(|| promise_id_different_from(rng, awaiter))
}

// Ids share the origin "diff", so a task promise and a plain promise pass
// the origin rule of callbacks, suspends and fences.
fn promise_id(n: u64) -> String {
    format!("diff:p{n}")
}
fn task_id(n: u64) -> String {
    format!("diff:t{n}")
}
fn schedule_id(n: u64) -> String {
    format!("s{n}")
}
fn random_promise_id(rng: &mut Rng) -> String {
    promise_id(chance(rng, 8))
}
fn random_task_id(rng: &mut Rng) -> String {
    task_id(chance(rng, 8))
}
fn random_schedule_id(rng: &mut Rng) -> String {
    schedule_id(chance(rng, 4))
}
fn promise_id_different_from(rng: &mut Rng, other: &str) -> String {
    let n = chance(rng, 8);
    let candidate = promise_id(n);
    if candidate == other {
        promise_id((n + 1) % 8)
    } else {
        candidate
    }
}
