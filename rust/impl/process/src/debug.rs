//! The debug operations: what a test that owns the clock asks of a node.
//!
//! Answered one at a time, and only when the runtime has already accepted
//! the operation. `debug.reset` empties the bucket of documents and keys
//! and forgets everything the node held of them. `debug.snap` reads every
//! document. `debug.tick` moves the work to `time`: every origin is swept
//! at that instant and every schedule due fires, again and again until
//! none is due, as the timers would have done had the clock passed through
//! every instant on the way. Each is a machine over store calls like
//! everything else here; the sweeps and fires are ordinary flights that
//! report back when they end. The runtime turns the answer into the
//! protocol's snapshot.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::verified::{self as rows, Promise, Schedule};

use crate::doc;
use crate::handler_docs::Work;
use crate::target::Target;
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
    /// The listings out (origins and schedules), the document reads out
    /// (`true` marks a schedule's), and the rows read so far.
    Gathering { ops: HashSet<OpId>, pending: HashMap<OpId, bool>, promises: Vec<Promise>, schedules: Vec<Schedule> },
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
    queue: VecDeque<DebugCall>,
}

impl State {
    /// A debug operation the runtime has already accepted.
    pub(crate) fn debug_begin(&mut self, call: DebugCall) {
        if self.debug.current.is_some() {
            self.debug.queue.push_back(call);
            return;
        }
        self.debug_start(call);
    }

    fn debug_start(&mut self, call: DebugCall) {
        match call {
            DebugCall::Reset { id, kind, corr } => {
                let op = self.store(StoreCall::List { prefix: self.cfg.prefix.clone(), max_keys: usize::MAX }, Owner::Debug);
                self.debug.current = Some(Op::Reset { id, kind, corr, phase: Reset::Listing { op } });
            }
            DebugCall::Snap { id, kind, corr } => {
                let mut ops = HashSet::new();
                ops.insert(self.store(StoreCall::List { prefix: format!("{}wf/", self.keys_prefix()), max_keys: usize::MAX }, Owner::Debug));
                ops.insert(self.store(StoreCall::List { prefix: format!("{}sched/", self.keys_prefix()), max_keys: usize::MAX }, Owner::Debug));
                self.debug.current = Some(Op::Snap { id, kind, corr, phase: Snap::Gathering { ops, pending: HashMap::new(), promises: Vec::new(), schedules: Vec::new() } });
            }
            DebugCall::Tick { id, kind, corr, time } => {
                let mut ops = HashSet::new();
                ops.insert(self.store(StoreCall::List { prefix: format!("{}wf/", self.keys_prefix()), max_keys: usize::MAX }, Owner::Debug));
                ops.insert(self.store(StoreCall::List { prefix: format!("{}sched/", self.keys_prefix()), max_keys: usize::MAX }, Owner::Debug));
                self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Listing { ops, origins: Vec::new(), schedules: Vec::new() } });
            }
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

    /// Answer, and start the next debug operation waiting.
    fn debug_reply(&mut self, id: RequestId, kind: String, corr: String, status: u16, body: DebugBody) {
        self.emit(Effect::Reply { id, response: Ok(Answer::Debug { kind, corr, status, body }) });
        if let Some(call) = self.debug.queue.pop_front() {
            self.debug_start(call);
        }
    }

    fn debug_fail(&mut self, id: RequestId, kind: String, corr: String, e: StoreError) {
        self.debug.current = None;
        self.debug_reply(id, kind, corr, 503, DebugBody::Message(e.to_string()));
    }

    pub(crate) fn debug_completed(&mut self, op: OpId, outcome: StoreOutcome) {
        let Some(current) = self.debug.current.take() else { return };
        let expected = match &current {
            Op::Reset { phase: Reset::Listing { op: o }, .. } => *o == op,
            Op::Snap { phase: Snap::Gathering { ops, pending, .. }, .. } => ops.contains(&op) || pending.contains_key(&op),
            Op::Reset { phase: Reset::Deleting { pending }, .. } => pending.contains(&op),
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
                (Snap::Gathering { mut ops, mut pending, mut promises, mut schedules }, outcome) => {
                    match outcome {
                        StoreOutcome::Listed(keys) => {
                            ops.remove(&op);
                            for key in keys {
                                let schedule = self.keys.class_of(&key) == Some("sched");
                                pending.insert(self.store(StoreCall::Get { key }, Owner::Debug), schedule);
                            }
                        }
                        StoreOutcome::Got(got) => {
                            let schedule = pending.remove(&op).unwrap_or(false);
                            if let Some((bytes, _)) = got {
                                if schedule {
                                    match doc::decode::<Schedule>(&bytes) {
                                        Ok(loaded) => schedules.extend(loaded.rows),
                                        Err(e) => return self.debug_fail(id, kind, corr, StoreError::Unavailable(e)),
                                    }
                                } else {
                                    match doc::decode::<Promise>(&bytes) {
                                        Ok(loaded) => promises.extend(loaded.rows),
                                        Err(e) => return self.debug_fail(id, kind, corr, StoreError::Unavailable(e)),
                                    }
                                }
                            }
                        }
                        StoreOutcome::Failed(e) => return self.debug_fail(id, kind, corr, e),
                        _ => return self.debug_fail(id, kind, corr, unexpected()),
                    }
                    if ops.is_empty() && pending.is_empty() {
                        self.debug_reply(id, kind, corr, 200, DebugBody::Snap { promises, schedules });
                    } else {
                        self.debug.current = Some(Op::Snap { id, kind, corr, phase: Snap::Gathering { ops, pending, promises, schedules } });
                    }
                }
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
        let (epoch, members, last_read, read_any) = (self.node.core.epoch, self.node.core.members.clone(), self.node.core.last_read, self.node.core.read_any);
        self.node.core = rows::node::NodeCore::new(self.cfg.node_id.clone(), self.cfg.node_ttl_ms);
        if read_any {
            self.node.core.read_config(last_read, epoch, members);
        }
        self.timers.wheel = crate::state_timers::TimerWheel::new();
        self.debug_reply(id, kind, corr, 200, DebugBody::Object);
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
                self.debug_reply(id, kind, corr, 200, DebugBody::List);
            }
            Tick::Listing { .. } => {
                self.debug.current = Some(Op::Tick { id, kind, corr, time, phase });
            }
        }
    }
}

fn unexpected() -> StoreError {
    StoreError::Unavailable("the store answered something else".into())
}
