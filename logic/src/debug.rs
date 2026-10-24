//! The debug operations: what a test that owns the clock asks of a node.
//!
//! Answered only when the node runs in debug mode, and one at a time.
//! `debug.reset` empties the bucket of documents and keys and forgets
//! everything the node held of them. `debug.snap` reads every document and
//! renders the protocol's `Snapshot`: promises, tasks, callbacks,
//! listeners, and the deadlines they owe. `debug.tick` moves the clock to
//! `time`: every origin is swept at that instant and every schedule due
//! fires, again and again until none is due, as the timers would have
//! done had the clock passed through every instant on the way. Each is a
//! machine over store calls like everything else here; the sweeps and
//! fires are ordinary flights that report back when they end.

use std::collections::{HashSet, VecDeque};

use echod_kernel::{self as k, Promise};
use resonate_core::types::{RequestEnvelope, ResponseEnvelope};
use serde_json::{json, Value};

use crate::dispatch::Target;
use crate::doc;
use crate::flight::Work;
use crate::types::*;
use crate::{Owner, State};

enum Op {
    Reset { id: RequestId, kind: String, corr: String, phase: Reset },
    Snap { id: RequestId, kind: String, corr: String, phase: Snap },
    Tick { id: RequestId, kind: String, corr: String, time: u64, phase: Tick },
}

enum Reset {
    Listing { op: OpId },
    Deleting { pending: HashSet<OpId> },
}

enum Snap {
    Listing { op: OpId },
    Reading { pending: HashSet<OpId>, promises: Vec<Promise> },
}

enum Tick {
    /// The documents there are: origins and schedules, two listings.
    Listing { ops: HashSet<OpId>, origins: Vec<String>, schedules: Vec<String> },
    /// Every origin swept at `time`.
    Sweeping { outstanding: usize, schedules: Vec<String> },
    /// Every schedule fired until nothing is due.
    Firing { outstanding: usize },
}

#[derive(Default)]
pub(crate) struct Debug {
    current: Option<Op>,
    queue: VecDeque<(RequestId, RequestEnvelope)>,
}

impl State {
    /// A `debug.*` request, in debug mode.
    pub(crate) fn debug_request(&mut self, id: RequestId, envelope: RequestEnvelope) {
        if self.debug.current.is_some() {
            self.debug.queue.push_back((id, envelope));
            return;
        }
        let (kind, corr) = (envelope.kind.clone(), envelope.head.corr_id.clone());
        match kind.as_str() {
            "debug.reset" => {
                let op = self.store(StoreCall::List { prefix: self.cfg.prefix.clone(), max_keys: usize::MAX }, Owner::Debug);
                self.debug.current = Some(Op::Reset { id, kind, corr, phase: Reset::Listing { op } });
            }
            "debug.snap" => {
                let prefix = format!("{}wf/", self.keys_prefix());
                let op = self.store(StoreCall::List { prefix, max_keys: usize::MAX }, Owner::Debug);
                self.debug.current = Some(Op::Snap { id, kind, corr, phase: Snap::Listing { op } });
            }
            "debug.tick" => {
                let Some(time) = envelope.data.get("time").and_then(|v| v.as_i64()) else {
                    return self.debug_reply(id, ResponseEnvelope::error(kind, corr, 400, "Missing or invalid 'time' field"));
                };
                if envelope.head.debug_time.is_some_and(|t| t != time) {
                    return self.debug_reply(id, ResponseEnvelope::error(kind, corr, 400, "resonate:debug_time must equal data.time"));
                }
                let time = time.max(0) as u64;
                let mut ops = HashSet::new();
                ops.insert(self.store(StoreCall::List { prefix: format!("{}wf/", self.keys_prefix()), max_keys: usize::MAX }, Owner::Debug));
                ops.insert(self.store(StoreCall::List { prefix: format!("{}sched/", self.keys_prefix()), max_keys: usize::MAX }, Owner::Debug));
                self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Listing { ops, origins: Vec::new(), schedules: Vec::new() } });
            }
            _ => self.debug_reply(id, ResponseEnvelope::error(kind, corr, 400, "Unknown debug operation")),
        }
    }

    fn keys_prefix(&self) -> String {
        let p = &self.cfg.prefix;
        if p.is_empty() || p.ends_with('/') {
            p.clone()
        } else {
            format!("{p}/")
        }
    }

    /// Answer, and start the next debug request waiting.
    fn debug_reply(&mut self, id: RequestId, response: ResponseEnvelope) {
        self.emit(Effect::Reply { id, response: Ok(response) });
        if let Some((id, envelope)) = self.debug.queue.pop_front() {
            self.debug_request(id, envelope);
        }
    }

    fn debug_fail(&mut self, id: RequestId, kind: String, corr: String, e: StoreError) {
        self.debug.current = None;
        self.debug_reply(id, ResponseEnvelope::error(kind, corr, 503, &e.to_string()));
    }

    pub(crate) fn debug_completed(&mut self, op: OpId, outcome: StoreOutcome) {
        let Some(current) = self.debug.current.take() else { return };
        let expected = match &current {
            Op::Reset { phase: Reset::Listing { op: o }, .. } | Op::Snap { phase: Snap::Listing { op: o }, .. } => *o == op,
            Op::Reset { phase: Reset::Deleting { pending }, .. } | Op::Snap { phase: Snap::Reading { pending, .. }, .. } => pending.contains(&op),
            Op::Tick { phase: Tick::Listing { ops, .. }, .. } => ops.contains(&op),
            Op::Tick { .. } => false,
        };
        if !expected {
            self.debug.current = Some(current);
            return;
        }
        match current {
            Op::Reset { id, kind, corr, phase } => match (phase, outcome) {
                (Reset::Listing { .. }, StoreOutcome::Listed(keys)) => {
                    let mut pending = HashSet::new();
                    for key in keys {
                        if matches!(self.keys.class_of(&key), Some("wf") | Some("sched") | Some("t")) {
                            pending.insert(self.store(StoreCall::Delete { key }, Owner::Debug));
                        }
                    }
                    if pending.is_empty() {
                        self.debug_reset_done(id, kind, corr);
                    } else {
                        self.debug.current = Some(Op::Reset { id, kind, corr, phase: Reset::Deleting { pending } });
                    }
                }
                (Reset::Deleting { mut pending }, StoreOutcome::Done) => {
                    pending.remove(&op);
                    if pending.is_empty() {
                        self.debug_reset_done(id, kind, corr);
                    } else {
                        self.debug.current = Some(Op::Reset { id, kind, corr, phase: Reset::Deleting { pending } });
                    }
                }
                (_, StoreOutcome::Failed(e)) => self.debug_fail(id, kind, corr, e),
                _ => self.debug_fail(id, kind, corr, unexpected()),
            },
            Op::Snap { id, kind, corr, phase } => match (phase, outcome) {
                (Snap::Listing { .. }, StoreOutcome::Listed(keys)) => {
                    let mut pending = HashSet::new();
                    for key in keys {
                        pending.insert(self.store(StoreCall::Get { key }, Owner::Debug));
                    }
                    if pending.is_empty() {
                        self.debug_reply(id, ResponseEnvelope::new(kind, corr, 200, snapshot(&[])));
                    } else {
                        self.debug.current = Some(Op::Snap { id, kind, corr, phase: Snap::Reading { pending, promises: Vec::new() } });
                    }
                }
                (Snap::Reading { mut pending, mut promises }, StoreOutcome::Got(got)) => {
                    pending.remove(&op);
                    if let Some((bytes, _)) = got {
                        match doc::decode::<Promise>(&bytes) {
                            Ok(loaded) => promises.extend(loaded.rows),
                            Err(e) => return self.debug_fail(id, kind, corr, StoreError::Unavailable(e)),
                        }
                    }
                    if pending.is_empty() {
                        self.debug_reply(id, ResponseEnvelope::new(kind, corr, 200, snapshot(&promises)));
                    } else {
                        self.debug.current = Some(Op::Snap { id, kind, corr, phase: Snap::Reading { pending, promises } });
                    }
                }
                (_, StoreOutcome::Failed(e)) => self.debug_fail(id, kind, corr, e),
                _ => self.debug_fail(id, kind, corr, unexpected()),
            },
            Op::Tick { id, kind, corr, time, phase } => match (phase, outcome) {
                (Tick::Listing { mut ops, mut origins, mut schedules }, StoreOutcome::Listed(keys)) => {
                    ops.remove(&op);
                    for key in keys {
                        match self.keys.class_of(&key) {
                            Some("wf") => {
                                if let Some(o) = key.rsplit('/').next().and_then(crate::keys::decode_key) {
                                    origins.push(o);
                                }
                            }
                            Some("sched") => {
                                if let Some(s) = key.rsplit('/').next().and_then(crate::keys::decode_key) {
                                    schedules.push(s);
                                }
                            }
                            _ => {}
                        }
                    }
                    if !ops.is_empty() {
                        self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Listing { ops, origins, schedules } });
                        return;
                    }
                    // every origin swept at `time`; the flights report back
                    let outstanding = origins.len();
                    self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Sweeping { outstanding, schedules } });
                    for o in origins {
                        self.submit(Target::Origin(o), Work::Sweep { fired: None, now: time }, None, true);
                    }
                    if outstanding == 0 {
                        self.debug_tick_advance(None);
                    }
                }
                (_, StoreOutcome::Failed(e)) => self.debug_fail(id, kind, corr, e),
                _ => self.debug_fail(id, kind, corr, unexpected()),
            },
        }
    }

    fn debug_reset_done(&mut self, id: RequestId, kind: String, corr: String) {
        // nothing of the documents is held any more: not the cache, not the
        // core's versions and keys, not the wheel
        self.cache = crate::cache::MemoryCache::new(self.cfg.cache_entries, self.cfg.cache_bytes);
        let (epoch, members, last_read, read_any) = (self.core.epoch, self.core.members.clone(), self.core.last_read, self.core.read_any);
        self.core = echod_kernel::node::NodeCore::new(self.cfg.node_id.clone(), self.cfg.node_ttl_ms);
        if read_any {
            self.core.read_config(last_read, epoch, members);
        }
        self.timers.wheel = crate::timers::TimerWheel::new();
        self.debug_reply(id, ResponseEnvelope::new(kind, corr, 200, json!({})));
    }

    /// A flight the tick started has ended: a sweep, or a fire that fired
    /// (`idle` false) or found nothing due (`idle` true).
    pub(crate) fn debug_flight_done(&mut self, work: &Work, idle: bool) {
        let fired_schedule = match work {
            Work::Fire { schedule, .. } if !idle => Some(schedule.clone()),
            _ => None,
        };
        self.debug_tick_advance(fired_schedule);
    }

    /// One flight fewer outstanding; a schedule that fired is fired again,
    /// since the next occurrence may be due too.
    fn debug_tick_advance(&mut self, refire: Option<String>) {
        let Some(Op::Tick { id, kind, corr, time, phase }) = self.debug.current.take() else { return };
        match phase {
            Tick::Sweeping { outstanding, schedules } => {
                let outstanding = outstanding.saturating_sub(if refire.is_none() && outstanding > 0 { 1 } else { 0 });
                if outstanding > 0 {
                    self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Sweeping { outstanding, schedules } });
                    return;
                }
                let outstanding = schedules.len();
                self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Firing { outstanding } });
                for s in schedules {
                    self.submit(Target::Schedule(s.clone()), Work::Fire { schedule: s, fired: None, now: time }, None, true);
                }
                if outstanding == 0 {
                    self.debug_tick_advance(None);
                }
            }
            Tick::Firing { outstanding } => {
                if let Some(s) = refire {
                    self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Firing { outstanding } });
                    self.submit(Target::Schedule(s.clone()), Work::Fire { schedule: s, fired: None, now: time }, None, true);
                    return;
                }
                let outstanding = outstanding.saturating_sub(1);
                if outstanding > 0 {
                    self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Firing { outstanding } });
                    return;
                }
                self.debug_reply(id, ResponseEnvelope::new(kind, corr, 200, Value::Array(Vec::new())));
            }
            Tick::Listing { .. } => {
                self.debug.current = Some(Op::Tick { id, kind, corr, time, phase });
            }
        }
    }
}

/// The protocol's `Snapshot` of a set of promise rows: the records, the
/// callbacks and listeners they hold, their tasks, and the deadlines they
/// owe. Messages are never queued here: they are routed as they arise.
fn snapshot(promises: &[Promise]) -> Value {
    let mut promises: Vec<&Promise> = promises.iter().collect();
    promises.sort_by(|a, b| a.id.cmp(&b.id));
    let records: Vec<Value> = promises.iter().map(|p| serde_json::to_value(crate::wire::promise_record(p)).unwrap_or(Value::Null)).collect();
    let mut callbacks: Vec<Value> = Vec::new();
    let mut listeners: Vec<Value> = Vec::new();
    let mut tasks: Vec<Value> = Vec::new();
    let mut promise_timeouts: Vec<Value> = Vec::new();
    let mut task_timeouts: Vec<Value> = Vec::new();
    for p in &promises {
        for awaiter in &p.callbacks {
            callbacks.push(json!({ "awaiter": awaiter, "awaited": p.id }));
        }
        for address in &p.listeners {
            listeners.push(json!({ "id": p.id, "address": address }));
        }
        if p.state == k::PromiseState::Pending && echod_kernel::tags::exec_otype(&p.tags) != echod_kernel::tags::OType::Internal {
            promise_timeouts.push(json!({ "id": p.id, "timeout": p.timeout_at }));
        }
        if let Some(t) = &p.task {
            let record = k::TaskRecord { id: p.id.clone(), state: t.state, version: t.version, resumes: t.resumes.len() as u64, ttl: t.ttl, pid: t.pid.clone() };
            tasks.push(serde_json::to_value(crate::wire::task_out(&record)).unwrap_or(Value::Null));
            if let Some(at) = t.lease_timeout_at {
                task_timeouts.push(json!({ "id": p.id, "type": 1, "timeout": at }));
            }
            if let Some(at) = t.retry_timeout_at {
                task_timeouts.push(json!({ "id": p.id, "type": 0, "timeout": at }));
            }
        }
    }
    json!({
        "promises": records,
        "promiseTimeouts": promise_timeouts,
        "callbacks": callbacks,
        "listeners": listeners,
        "tasks": tasks,
        "taskTimeouts": task_timeouts,
        "messages": [],
    })
}

fn unexpected() -> StoreError {
    StoreError::Unavailable("the store answered something else".into())
}
