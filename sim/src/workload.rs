//! Abstract-model requests and their deterministic generator.

use std::collections::{BTreeMap, BTreeSet};

use echod_abstract::{
    ExternalAction, PromiseCreateReq, PromiseGetReq, PromiseRegisterCallbackReq,
    PromiseRegisterListenerReq, PromiseSettleReq, PromiseState, ScheduleCreateReq,
    ScheduleDeleteReq, ScheduleGetReq, Tag, Tags, TaskAcquireReq, TaskContinueReq, TaskCreateReq,
    TaskFenceAction, TaskFenceReq, TaskFulfillReq, TaskGetReq, TaskHaltReq, TaskHeartbeatReq,
    TaskRef, TaskReleaseReq, TaskSuspendReq, Text, Value as AValue,
};
use serde_json::Value;

use crate::rng::Rng;
use crate::wire::{ident, ident_string, text};

/// The worker every task is dispatched to, and every listener listens at.
pub const WORKER: &str = "sim://worker";

/// The schedule ids a run uses (a schedule's id has no `:`).
pub const SCHEDULES: [&str; 3] = ["s0", "s1", "s2"];

/// The document a request is about, for routing: an origin, or a schedule.
pub fn target_of(req: &ExternalAction) -> String {
    let origin = |id| echod_logic::keys::origin_of(&ident_string(id)).to_string();
    match req {
        ExternalAction::PromiseCreate(c) => origin(&c.id),
        ExternalAction::PromiseGet(q) => origin(&q.id),
        ExternalAction::PromiseSettle(q) => origin(&q.id),
        ExternalAction::PromiseRegisterCallback(q) => origin(&q.awaited),
        ExternalAction::PromiseRegisterListener(q) => origin(&q.awaited),
        ExternalAction::TaskGet(q) => origin(&q.id),
        ExternalAction::TaskCreate(q) => origin(&q.action.id),
        ExternalAction::TaskAcquire(q) => origin(&q.id),
        ExternalAction::TaskFence(q) => origin(&q.id),
        ExternalAction::TaskHeartbeat(q) => {
            q.tasks.first().map(|t| origin(&t.id)).unwrap_or_default()
        }
        ExternalAction::TaskSuspend(q) => origin(&q.id),
        ExternalAction::TaskFulfill(q) => origin(&q.id),
        ExternalAction::TaskRelease(q) => origin(&q.id),
        ExternalAction::TaskHalt(q) => origin(&q.id),
        ExternalAction::TaskContinue(q) => origin(&q.id),
        ExternalAction::TaskFenceCheck(q) => origin(&q.id),
        ExternalAction::ScheduleCreate(q) => format!("sched:{}", ident_string(&q.id)),
        ExternalAction::ScheduleGet(q) => format!("sched:{}", ident_string(&q.id)),
        ExternalAction::ScheduleDelete(q) => format!("sched:{}", ident_string(&q.id)),
        ExternalAction::PromiseSearch(_)
        | ExternalAction::ScheduleSearch(_)
        | ExternalAction::TaskSearch(_) => String::new(),
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
            if let (Some(id), Some(v)) = (
                t.get("id").and_then(Value::as_str),
                t.get("version").and_then(Value::as_u64),
            ) {
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
        let target = runnable || rng.percent(50);
        let external = !target && rng.percent(70);
        let timer = !target && rng.percent(10);
        let mut tags = Vec::new();
        if target {
            tags.push(Tag {
                key: text("resonate:target"),
                value: text(WORKER),
            });
        }
        if external {
            tags.push(Tag {
                key: text("resonate:external"),
                value: text("true"),
            });
        }
        if timer {
            tags.push(Tag {
                key: text("resonate:timer"),
                value: text("true"),
            });
        }
        tags
    }

    fn version(&self, id: &str, seen: &Seen, rng: &mut Rng) -> u32 {
        match seen.versions.get(id) {
            Some(v) if rng.percent(80) => *v,
            _ => rng.below(3) as u32,
        }
    }

    fn settle_state(rng: &mut Rng) -> PromiseState {
        match rng.below(3) {
            0 => PromiseState::Resolved,
            1 => PromiseState::Rejected,
            _ => PromiseState::RejectedCanceled,
        }
    }

    /// A schedule: a few ids, firing every few seconds into one origin, so
    /// that fires and client requests collide on the origin's document.
    fn schedule(&self, rng: &mut Rng, now: u64) -> ExternalAction {
        let id = (*rng.pick(&SCHEDULES)).to_string();
        match rng.below(10) {
            0..=2 => ExternalAction::ScheduleGet(ScheduleGetReq { id: ident(&id) }),
            3..=7 => {
                let cron =
                    (*rng.pick(&["*/2 * * * * *", "*/3 * * * * *", "*/5 * * * * *"])).to_string();
                let promise_id = format!("o{}:{id}-{{{{.timestamp}}}}", rng.below(self.origins));
                let promise_timeout = rng.range(1, self.timeout_ms);
                let next_run_at = resonate_core::util::compute_next_cron(&cron, now as i64)
                    .max(now.saturating_add(1) as i64) as u64;
                ExternalAction::ScheduleCreate(ScheduleCreateReq {
                    id: ident(&id),
                    cron: text(&cron),
                    promise_id: ident(&promise_id),
                    promise_timeout,
                    promise_param: AValue::empty(),
                    promise_tags: self.tags(rng, true),
                    next_run_at,
                })
            }
            _ => ExternalAction::ScheduleDelete(ScheduleDeleteReq { id: ident(&id) }),
        }
    }

    pub fn next(&self, rng: &mut Rng, seen: &Seen, now: u64) -> ExternalAction {
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
        let data = Some(text(&format!("d{}", rng.below(4))));
        let value = || AValue {
            headers: Vec::new(),
            data: data.as_ref().map(Text::dup),
        };
        let create = |id: &str, tags| PromiseCreateReq {
            id: ident(id),
            timeout_at,
            param: value(),
            tags,
        };
        match roll {
            0..=11 => ExternalAction::PromiseGet(PromiseGetReq { id: ident(&id) }),
            12..=27 => ExternalAction::PromiseCreate(create(&id, self.tags(rng, false))),
            28..=35 => ExternalAction::PromiseSettle(PromiseSettleReq {
                id: ident(&id),
                state: Self::settle_state(rng),
                value: value(),
            }),
            36..=40 => {
                let awaited = self.awaitable_sibling(&id, seen, rng);
                ExternalAction::PromiseRegisterCallback(PromiseRegisterCallbackReq {
                    awaited: ident(&awaited),
                    awaiter: ident(&id),
                })
            }
            41..=45 => ExternalAction::PromiseRegisterListener(PromiseRegisterListenerReq {
                awaited: ident(&id),
                address: text(WORKER),
            }),
            46..=51 => ExternalAction::TaskGet(TaskGetReq { id: ident(&id) }),
            52..=58 => ExternalAction::TaskCreate(TaskCreateReq {
                pid: text(&pid),
                ttl,
                action: PromiseCreateReq {
                    id: ident(&id),
                    timeout_at,
                    param: AValue::empty(),
                    tags: self.tags(rng, true),
                },
            }),
            59..=68 => {
                let version = self.version(&id, seen, rng);
                ExternalAction::TaskAcquire(TaskAcquireReq {
                    id: ident(&id),
                    version: version as u64,
                    pid: text(&pid),
                    ttl,
                })
            }
            69..=74 => {
                let version = self.version(&id, seen, rng);
                ExternalAction::TaskFulfill(TaskFulfillReq {
                    id: ident(&id),
                    version: version as u64,
                    action: PromiseSettleReq {
                        id: ident(&id),
                        state: Self::settle_state(rng),
                        value: value(),
                    },
                })
            }
            75..=77 => {
                let version = self.version(&id, seen, rng);
                ExternalAction::TaskRelease(TaskReleaseReq {
                    id: ident(&id),
                    version: version as u64,
                })
            }
            78..=80 => {
                let version = self.version(&id, seen, rng);
                ExternalAction::TaskHeartbeat(TaskHeartbeatReq {
                    pid: text(&pid),
                    tasks: vec![TaskRef {
                        id: ident(&id),
                        version: version as u64,
                    }],
                })
            }
            81..=85 => {
                let version = self.version(&id, seen, rng);
                let awaited = vec![self.awaitable_sibling(&id, seen, rng)];
                ExternalAction::TaskSuspend(TaskSuspendReq {
                    id: ident(&id),
                    version: version as u64,
                    actions: awaited
                        .into_iter()
                        .map(|a| PromiseRegisterCallbackReq {
                            awaited: ident(&a),
                            awaiter: ident(&id),
                        })
                        .collect(),
                })
            }
            86..=90 => {
                let version = self.version(&id, seen, rng);
                let child = format!("{id}.1");
                ExternalAction::TaskFence(TaskFenceReq {
                    id: ident(&id),
                    version: version as u64,
                    action: TaskFenceAction::Create(PromiseCreateReq {
                        id: ident(&child),
                        timeout_at,
                        param: AValue::empty(),
                        tags: self.tags(rng, false),
                    }),
                })
            }
            91..=94 => {
                let version = self.version(&id, seen, rng);
                let target = if rng.percent(50) {
                    format!("{id}.1")
                } else {
                    self.sibling(&id, rng)
                };
                ExternalAction::TaskFence(TaskFenceReq {
                    id: ident(&id),
                    version: version as u64,
                    action: TaskFenceAction::Settle(PromiseSettleReq {
                        id: ident(&target),
                        state: Self::settle_state(rng),
                        value: value(),
                    }),
                })
            }
            95..=97 => ExternalAction::TaskHalt(TaskHaltReq { id: ident(&id) }),
            _ => ExternalAction::TaskContinue(TaskContinueReq { id: ident(&id) }),
        }
    }
}

/// `PLAIN`, for callers building tags of their own.
pub fn plain() -> Tags {
    Vec::new()
}
