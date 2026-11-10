//! The requests a run issues, and how they are generated.
//!
//! Every request kind the server serves, as the model types it
//! (`echod_abstract::Request`), over a small space of ids so that operations
//! collide: a few origins, a few promises per origin, one child each.
//! Versions and pids are drawn from what the client has seen, so that fenced
//! operations sometimes carry the right version and sometimes not.

use std::collections::{BTreeMap, BTreeSet};

use echod_types::Response;
use echod_types::{
    PromiseCreateReq, PromiseGetReq, PromiseRegisterCallbackReq, PromiseRegisterListenerReq,
    PromiseSettleReq, PromiseState, Request, ScheduleCreateReq, ScheduleDeleteReq, ScheduleGetReq,
    Tags, TaskAcquireReq, TaskContinueReq, TaskCreateReq, TaskFenceAction, TaskFenceReq,
    TaskFulfillReq, TaskGetReq, TaskHaltReq, TaskHeartbeatReq, TaskRef, TaskReleaseReq,
    TaskSuspendReq, Value,
};

use crate::rng::Rng;

/// The worker every task is dispatched to, and every listener listens at.
pub const WORKER: &str = "sim://worker";

/// The schedule ids a run uses (a schedule's id has no `:`).
pub const SCHEDULES: [&str; 3] = ["s0", "s1", "s2"];

/// The document a request is about, for routing: an origin, or a schedule.
pub fn target_of(req: &Request) -> String {
    let origin = |id: &str| echod_logic::keys::origin_of(id).to_string();
    match req {
        Request::PromiseCreate(c) => origin(&c.id),
        Request::PromiseGet(q) => origin(&q.id),
        Request::PromiseSettle(s) => origin(&s.id),
        Request::PromiseRegisterCallback(c) => origin(&c.awaited),
        Request::PromiseRegisterListener(c) => origin(&c.awaited),
        Request::TaskGet(q) => origin(&q.id),
        Request::TaskCreate(t) => origin(&t.action.id),
        Request::TaskAcquire(t) => origin(&t.id),
        Request::TaskRelease(t) => origin(&t.id),
        Request::TaskFulfill(t) => origin(&t.id),
        Request::TaskSuspend(t) => origin(&t.id),
        Request::TaskFence(t) => origin(&t.id),
        Request::TaskFenceCheck(t) => origin(&t.id),
        Request::TaskHalt(t) => origin(&t.id),
        Request::TaskContinue(t) => origin(&t.id),
        Request::TaskHeartbeat(h) => h.tasks.first().map(|t| origin(&t.id)).unwrap_or_default(),
        Request::ScheduleCreate(c) => format!("sched:{}", c.id),
        Request::ScheduleGet(q) => format!("sched:{}", q.id),
        Request::ScheduleDelete(q) => format!("sched:{}", q.id),
    }
}

/// What a client has learned, to draw plausible versions and pids from.
#[derive(Default)]
pub struct Seen {
    pub versions: BTreeMap<String, u64>,
    /// Promises seen with tags that make them awaitable.
    pub external: BTreeSet<String>,
}

impl Seen {
    pub fn note(&mut self, response: &Response) {
        let (task, promise) = match response {
            Response::Promise(r) => (None, r.promise.as_ref()),
            Response::TaskGet(r) => (r.task.as_ref(), None),
            Response::TaskClaim(r) => (r.task.as_ref(), r.promise.as_ref()),
            _ => (None, None),
        };
        if let Some(task) = task {
            self.versions.insert(task.id.clone(), task.version);
        }
        if let Some(promise) = promise {
            let tag = |name: &str| {
                promise
                    .tags
                    .iter()
                    .find(|(key, _)| key == name)
                    .map(|(_, value)| value.as_str())
            };
            if tag("resonate:target").is_some() && !self.versions.contains_key(&promise.id) {
                self.versions.insert(promise.id.clone(), 0);
            }
            if tag("resonate:target").is_some()
                || tag("resonate:scope") == Some("global")
                || tag("resonate:external") == Some("true")
                || tag("resonate:timer") == Some("true")
            {
                self.external.insert(promise.id.clone());
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

fn value(data: Option<String>) -> Value {
    Value {
        headers: Vec::new(),
        data,
    }
}

impl Generator {
    fn id(&self, rng: &mut Rng) -> String {
        format!(
            "o{}:{}",
            rng.below(self.origins),
            1 + rng.below(self.promises_per_origin)
        )
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
        let known: Vec<&String> = seen
            .external
            .iter()
            .filter(|p| p.as_str() != id && echod_logic::keys::origin_of(p) == origin)
            .collect();
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
        let mut tags = Vec::new();
        let target = runnable || rng.percent(50);
        let external = !target && rng.percent(70);
        let timer = !target && rng.percent(10);
        if target {
            tags.push(("resonate:target".into(), WORKER.into()));
        }
        if external {
            tags.push(("resonate:external".into(), "true".into()));
        }
        if timer {
            tags.push(("resonate:timer".into(), "true".into()));
        }
        tags.sort();
        tags
    }

    fn version(&self, id: &str, seen: &Seen, rng: &mut Rng) -> u64 {
        match seen.versions.get(id) {
            Some(v) if rng.percent(80) => *v,
            _ => rng.below(3),
        }
    }

    fn settle_state(rng: &mut Rng) -> PromiseState {
        match rng.below(3) {
            0 => PromiseState::Resolved,
            1 => PromiseState::Rejected,
            _ => PromiseState::RejectedCanceled,
        }
    }

    fn create(
        &self,
        id: String,
        timeout_at: u64,
        data: Option<String>,
        tags: Tags,
    ) -> PromiseCreateReq {
        PromiseCreateReq {
            id,
            timeout_at,
            param: value(data),
            tags,
        }
    }

    fn settle(&self, id: String, state: PromiseState, data: Option<String>) -> PromiseSettleReq {
        PromiseSettleReq {
            id,
            state,
            value: value(data),
        }
    }

    /// A schedule: a few ids, firing every few seconds into one origin, so
    /// that fires and client requests collide on the origin's document.
    fn schedule(&self, rng: &mut Rng, now: u64) -> Request {
        let id = (*rng.pick(&SCHEDULES)).to_string();
        match rng.below(10) {
            0..=2 => Request::ScheduleGet(ScheduleGetReq { id }),
            3..=7 => {
                let cron =
                    (*rng.pick(&["*/2 * * * * *", "*/3 * * * * *", "*/5 * * * * *"])).to_string();
                let promise_id = format!("o{}:{id}-{{{{.timestamp}}}}", rng.below(self.origins));
                let promise_timeout = rng.range(1, self.timeout_ms);
                let next_run_at = echod_cron::next_run_at(&cron, now);
                Request::ScheduleCreate(ScheduleCreateReq {
                    id,
                    cron,
                    promise_id,
                    promise_timeout,
                    promise_param: value(None),
                    promise_tags: self.tags(rng, true),
                    next_run_at,
                })
            }
            _ => Request::ScheduleDelete(ScheduleDeleteReq { id }),
        }
    }

    pub fn next(&self, rng: &mut Rng, seen: &Seen, now: u64) -> Request {
        if self.schedules && rng.percent(4) {
            return self.schedule(rng, now);
        }
        let roll = rng.below(100);
        let id = if roll >= 46 {
            self.task_id(seen, rng)
        } else {
            self.id(rng)
        };
        let pid = format!("p{}", rng.below(3));
        let ttl = rng.range(self.ttl_ms / 4, self.ttl_ms);
        let timeout_at = now + rng.range(1, self.timeout_ms);
        let data = Some(format!("d{}", rng.below(4)));
        match roll {
            0..=11 => Request::PromiseGet(PromiseGetReq { id }),
            12..=27 => {
                Request::PromiseCreate(self.create(id, timeout_at, data, self.tags(rng, false)))
            }
            28..=35 => Request::PromiseSettle(self.settle(id, Self::settle_state(rng), data)),
            36..=40 => {
                let awaited = self.awaitable_sibling(&id, seen, rng);
                Request::PromiseRegisterCallback(PromiseRegisterCallbackReq {
                    awaited,
                    awaiter: id,
                })
            }
            41..=45 => Request::PromiseRegisterListener(PromiseRegisterListenerReq {
                awaited: id,
                address: WORKER.to_string(),
            }),
            46..=51 => Request::TaskGet(TaskGetReq { id }),
            52..=58 => Request::TaskCreate(TaskCreateReq {
                pid,
                ttl,
                action: self.create(id, timeout_at, None, self.tags(rng, true)),
            }),
            59..=68 => {
                let version = self.version(&id, seen, rng);
                Request::TaskAcquire(TaskAcquireReq {
                    id,
                    version,
                    pid,
                    ttl,
                })
            }
            69..=74 => {
                let version = self.version(&id, seen, rng);
                Request::TaskFulfill(TaskFulfillReq {
                    id: id.clone(),
                    version,
                    action: self.settle(id, Self::settle_state(rng), data),
                })
            }
            75..=77 => {
                let version = self.version(&id, seen, rng);
                Request::TaskRelease(TaskReleaseReq { id, version })
            }
            78..=80 => {
                let version = self.version(&id, seen, rng);
                Request::TaskHeartbeat(TaskHeartbeatReq {
                    pid,
                    tasks: vec![TaskRef { id, version }],
                })
            }
            81..=85 => {
                let version = self.version(&id, seen, rng);
                let awaited = self.awaitable_sibling(&id, seen, rng);
                Request::TaskSuspend(TaskSuspendReq {
                    id: id.clone(),
                    version,
                    actions: vec![PromiseRegisterCallbackReq {
                        awaited,
                        awaiter: id,
                    }],
                })
            }
            86..=90 => {
                let version = self.version(&id, seen, rng);
                let child = format!("{id}.1");
                Request::TaskFence(TaskFenceReq {
                    id,
                    version,
                    action: TaskFenceAction::Create(self.create(
                        child,
                        timeout_at,
                        None,
                        self.tags(rng, false),
                    )),
                })
            }
            91..=94 => {
                let version = self.version(&id, seen, rng);
                let target = if rng.percent(50) {
                    format!("{id}.1")
                } else {
                    self.sibling(&id, rng)
                };
                Request::TaskFence(TaskFenceReq {
                    id,
                    version,
                    action: TaskFenceAction::Settle(self.settle(
                        target,
                        Self::settle_state(rng),
                        data,
                    )),
                })
            }
            95..=97 => Request::TaskHalt(TaskHaltReq { id }),
            _ => Request::TaskContinue(TaskContinueReq { id }),
        }
    }
}

/// No tags: an internal promise.
pub fn plain() -> Tags {
    Vec::new()
}
