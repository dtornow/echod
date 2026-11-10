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

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use crate::concrete::Doc;

use crate::verified::node::{str_eq, NodeCore};
use crate::verified::table::Table;
use crate::verified::text::{concat, copy_string};
use crate::verified::Schedule;

use crate::cache::Cache;
use crate::doc;
use crate::handler_docs::{take_opt, Work};
use crate::state::{Owner, State};
use crate::state_node::copy_members;
use crate::state_timers::TimerWheel;
use crate::target::Target;
use crate::types::*;

#[cfg(verus_keep_ghost)]
use crate::cache::spec_new;
#[cfg(verus_keep_ghost)]
use crate::handler_docs::*;
#[cfg(verus_keep_ghost)]
use crate::keys::*;
#[cfg(verus_keep_ghost)]
use crate::state::*;
#[cfg(verus_keep_ghost)]
use crate::state_node::NodeSpec;
#[cfg(verus_keep_ghost)]
use crate::state_timers::{TimerWheelSpec, TimersSpec};
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;
#[cfg(verus_keep_ghost)]
use crate::verified::node_spec::{spec_read_config, ANode};
#[cfg(verus_keep_ghost)]
use crate::verified::ScheduleSpec;
#[cfg(verus_keep_ghost)]
use rover_concrete_spec::node::DocV;
#[cfg(verus_keep_ghost)]
use rover_concrete_spec::store::{StoreCallSpec, StoreErrorSpec};

verus! {

#[allow(inconsistent_fields)]
pub enum Op {
    Reset { id: RequestId, kind: String, corr: String, phase: Reset },
    Snap { id: RequestId, kind: String, corr: String, phase: Snap },
    Tick { id: RequestId, kind: String, corr: String, time: u64, phase: Tick },
}

#[allow(inconsistent_fields)]
#[cfg(verus_keep_ghost)]
pub ghost enum OpSpec {
    Reset { id: RequestId, kind: Seq<char>, corr: Seq<char>, phase: ResetSpec },
    Snap { id: RequestId, kind: Seq<char>, corr: Seq<char>, phase: SnapSpec },
    Tick { id: RequestId, kind: Seq<char>, corr: Seq<char>, time: u64, phase: TickSpec },
}

#[cfg(verus_keep_ghost)]
impl DeepView for Op {
    type V = OpSpec;
    open spec fn deep_view(&self) -> OpSpec {
        match self {
            Op::Reset { id, kind, corr, phase } => OpSpec::Reset { id: *id, kind: kind@, corr: corr@, phase: phase.deep_view() },
            Op::Snap { id, kind, corr, phase } => OpSpec::Snap { id: *id, kind: kind@, corr: corr@, phase: phase.deep_view() },
            Op::Tick { id, kind, corr, time, phase } => OpSpec::Tick { id: *id, kind: kind@, corr: corr@, time: *time, phase: phase.deep_view() },
        }
    }
}

pub enum Reset {
    Listing { op: OpId },
    Deleting { pending: Table<OpId, bool> },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ResetSpec {
    Listing { op: OpId },
    Deleting { pending: Map<OpId, bool> },
}

#[cfg(verus_keep_ghost)]
impl DeepView for Reset {
    type V = ResetSpec;
    open spec fn deep_view(&self) -> ResetSpec {
        match self {
            Reset::Listing { op } => ResetSpec::Listing { op: *op },
            Reset::Deleting { pending } => ResetSpec::Deleting { pending: pending.deep_view() },
        }
    }
}

pub enum Snap {
    /// The listings out (origins and schedules), the document reads out
    /// (`true` marks a schedule's), and the documents read so far.
    Gathering { ops: Table<OpId, bool>, pending: Table<OpId, bool>, origins: Vec<Doc>, schedules: Vec<Schedule> },
}

#[cfg(verus_keep_ghost)]
pub ghost enum SnapSpec {
    Gathering { ops: Map<OpId, bool>, pending: Map<OpId, bool>, origins: Seq<DocV>, schedules: Seq<ScheduleSpec> },
}

#[cfg(verus_keep_ghost)]
impl DeepView for Snap {
    type V = SnapSpec;
    open spec fn deep_view(&self) -> SnapSpec {
        match self {
            Snap::Gathering { ops, pending, origins, schedules } => SnapSpec::Gathering { ops: ops.deep_view(), pending: pending.deep_view(), origins: origins.deep_view(), schedules: schedules.deep_view() },
        }
    }
}

pub enum Tick {
    /// The documents there are: origins and schedules, two listings.
    Listing { ops: Table<OpId, bool>, origins: Vec<String>, schedules: Vec<String> },
    /// Every origin swept at `time`.
    Sweeping { outstanding: usize, schedules: Vec<String> },
    /// Every schedule fired until nothing is due.
    Firing { outstanding: usize },
}

#[cfg(verus_keep_ghost)]
pub ghost enum TickSpec {
    Listing { ops: Map<OpId, bool>, origins: Seq<Seq<char>>, schedules: Seq<Seq<char>> },
    Sweeping { outstanding: usize, schedules: Seq<Seq<char>> },
    Firing { outstanding: usize },
}

#[cfg(verus_keep_ghost)]
impl DeepView for Tick {
    type V = TickSpec;
    open spec fn deep_view(&self) -> TickSpec {
        match self {
            Tick::Listing { ops, origins, schedules } => TickSpec::Listing { ops: ops.deep_view(), origins: origins.deep_view(), schedules: schedules.deep_view() },
            Tick::Sweeping { outstanding, schedules } => TickSpec::Sweeping { outstanding: *outstanding, schedules: schedules.deep_view() },
            Tick::Firing { outstanding } => TickSpec::Firing { outstanding: *outstanding },
        }
    }
}

#[make_spec_type]
pub struct Debug {
    pub current: Option<Op>,
    pub queue: Vec<DebugCall>,
}

pub open spec fn spec_debug_new() -> DebugSpec {
    DebugSpec { current: None, queue: Seq::empty() }
}

impl Debug {
    pub fn new() -> (r: Debug)
        ensures
            r.deep_view() == spec_debug_new(),
    {
        let r = Debug { current: None, queue: Vec::new() };
        proof {
            assert(r.queue.deep_view() =~= Seq::<DebugCallSpec>::empty());
        }
        r
    }
}

pub open spec fn spec_with_debug(s: S, d: DebugSpec) -> S {
    S { debug: d, ..s }
}

pub open spec fn spec_current(s: S, op: Option<OpSpec>) -> S {
    spec_with_debug(s, DebugSpec { current: op, ..s.debug })
}

// ---------------------------------------------------------------------------
// Stated
// ---------------------------------------------------------------------------

/// A debug operation the runtime has already accepted.
#[verifier::opaque]
pub open spec fn spec_debug_begin(s: S, call: DebugCallSpec) -> S {
    if s.debug.current is Some {
        spec_with_debug(s, DebugSpec { queue: s.debug.queue.push(call), ..s.debug })
    } else {
        spec_debug_start(s, call)
    }
}

/// The two listings a snapshot or a tick starts with: the origins, then
/// the schedules.
#[verifier::opaque]
pub open spec fn spec_list_docs(s: S) -> (S, Map<OpId, bool>) {
    let (s, op1) = spec_store(s, StoreCallSpec::List { prefix: s.keys.prefix + "wf/"@, max_keys: usize::MAX }, Owner::Debug);
    let (s, op2) = spec_store(s, StoreCallSpec::List { prefix: s.keys.prefix + "sched/"@, max_keys: usize::MAX }, Owner::Debug);
    (s, Map::<OpId, bool>::empty().insert(op1, true).insert(op2, true))
}

#[verifier::opaque]
pub open spec fn spec_debug_start(s: S, call: DebugCallSpec) -> S {
    match call {
        DebugCallSpec::Reset { id, kind, corr } => {
            let (s, op) = spec_store(s, StoreCallSpec::List { prefix: s.cfg.prefix, max_keys: usize::MAX }, Owner::Debug);
            spec_current(s, Some(OpSpec::Reset { id, kind, corr, phase: ResetSpec::Listing { op } }))
        },
        DebugCallSpec::Snap { id, kind, corr } => {
            let (s, ops) = spec_list_docs(s);
            spec_current(s, Some(OpSpec::Snap { id, kind, corr, phase: SnapSpec::Gathering { ops, pending: Map::empty(), origins: Seq::empty(), schedules: Seq::empty() } }))
        },
        DebugCallSpec::Tick { id, kind, corr, time } => {
            let (s, ops) = spec_list_docs(s);
            spec_current(s, Some(OpSpec::Tick { id, kind, corr, time, phase: TickSpec::Listing { ops, origins: Seq::empty(), schedules: Seq::empty() } }))
        },
    }
}

/// Answer, and start the next debug operation waiting.
#[verifier::opaque]
pub open spec fn spec_debug_reply(s: S, id: RequestId, kind: Seq<char>, corr: Seq<char>, status: u16, body: DebugBodySpec) -> S {
    let s = spec_emit(s, EffectSpec::Reply { id, response: Ok(AnswerSpec::Debug { kind, corr, status, body }) });
    if s.debug.queue.len() > 0 {
        let call = s.debug.queue[0];
        spec_debug_start(spec_with_debug(s, DebugSpec { queue: s.debug.queue.drop_first(), ..s.debug }), call)
    } else {
        s
    }
}

#[verifier::opaque]
pub open spec fn spec_debug_fail(s: S, id: RequestId, kind: Seq<char>, corr: Seq<char>, e: StoreErrorSpec) -> S {
    let s = spec_current(s, None);
    spec_debug_reply(s, id, kind, corr, 503, DebugBodySpec::Message(spec_error_text(e)))
}

/// Whether a key is one `debug.reset` deletes: a document, a schedule, a
/// timer.
pub open spec fn spec_resettable(class: Option<Seq<char>>) -> bool {
    match class {
        Some(c) => c == "wf"@ || c == "sched"@ || c == "t"@,
        None => false,
    }
}

/// A `Delete` for every resettable key; `pending` collects the ops.
pub open spec fn spec_delete_keys(s: S, keys: Seq<Seq<char>>, pending: Map<OpId, bool>) -> (S, Map<OpId, bool>)
    decreases keys.len(),
{
    if keys.len() == 0 {
        (s, pending)
    } else {
        let key = keys[0];
        let (s, pending) = if spec_resettable(spec_class_of(s.keys.prefix, key)) {
            let (s, op) = spec_store(s, StoreCallSpec::Delete { key }, Owner::Debug);
            (s, pending.insert(op, true))
        } else {
            (s, pending)
        };
        spec_delete_keys(s, keys.drop_first(), pending)
    }
}

/// A `Get` for every key listed, marked as a schedule's or not.
pub open spec fn spec_get_keys(s: S, keys: Seq<Seq<char>>, pending: Map<OpId, bool>) -> (S, Map<OpId, bool>)
    decreases keys.len(),
{
    if keys.len() == 0 {
        (s, pending)
    } else {
        let key = keys[0];
        let schedule = spec_class_of(s.keys.prefix, key) == Some("sched"@);
        let (s, op) = spec_store(s, StoreCallSpec::Get { key }, Owner::Debug);
        spec_get_keys(s, keys.drop_first(), pending.insert(op, schedule))
    }
}

/// The names a listing holds: origins and schedules, by class.
pub open spec fn spec_tick_names(prefix: Seq<char>, keys: Seq<Seq<char>>, origins: Seq<Seq<char>>, schedules: Seq<Seq<char>>) -> (Seq<Seq<char>>, Seq<Seq<char>>)
    decreases keys.len(),
{
    if keys.len() == 0 {
        (origins, schedules)
    } else {
        let key = keys[0];
        let class = spec_class_of(prefix, key);
        let name = spec_decode_key(spec_last_segment(key));
        let (origins, schedules) = if class == Some("wf"@) {
            match name {
                Some(o) => (origins.push(o), schedules),
                None => (origins, schedules),
            }
        } else if class == Some("sched"@) {
            match name {
                Some(sch) => (origins, schedules.push(sch)),
                None => (origins, schedules),
            }
        } else {
            (origins, schedules)
        };
        spec_tick_names(prefix, keys.drop_first(), origins, schedules)
    }
}

/// Every origin swept at `time`.
pub open spec fn spec_submit_sweeps(s: S, origins: Seq<Seq<char>>, time: u64) -> S
    decreases origins.len(),
{
    if origins.len() == 0 {
        s
    } else {
        let s = spec_submit(s, TargetSpec::Origin(origins[0]), WorkSpec::Sweep { fired: None, now: time }, None, true);
        spec_submit_sweeps(s, origins.drop_first(), time)
    }
}

/// Every schedule fired at `time`.
pub open spec fn spec_submit_fires(s: S, schedules: Seq<Seq<char>>, time: u64) -> S
    decreases schedules.len(),
{
    if schedules.len() == 0 {
        s
    } else {
        let s = spec_submit(s, TargetSpec::Schedule(schedules[0]), WorkSpec::Fire { schedule: schedules[0], fired: None, now: time }, None, true);
        spec_submit_fires(s, schedules.drop_first(), time)
    }
}

#[verifier::opaque]
pub open spec fn spec_debug_completed(s: S, op: OpId, outcome: StoreOutcome) -> S {
    match s.debug.current {
        None => s,
        Some(current) => {
            let expected = match current {
                OpSpec::Reset { phase: ResetSpec::Listing { op: o }, .. } => o == op,
                OpSpec::Snap { phase: SnapSpec::Gathering { ops, pending, .. }, .. } => ops.contains_key(op) || pending.contains_key(op),
                OpSpec::Reset { phase: ResetSpec::Deleting { pending }, .. } => pending.contains_key(op),
                OpSpec::Tick { phase: TickSpec::Listing { ops, .. }, .. } => ops.contains_key(op),
                OpSpec::Tick { .. } => false,
            };
            if !expected {
                s
            } else {
                let s = spec_current(s, None);
                match current {
                    OpSpec::Reset { id, kind, corr, phase } => match (phase, outcome) {
                        (ResetSpec::Listing { .. }, StoreOutcome::Listed(keys)) => {
                            let (s, pending) = spec_delete_keys(s, keys.deep_view(), Map::empty());
                            if pending =~= Map::<OpId, bool>::empty() {
                                spec_debug_reset_done(s, id, kind, corr)
                            } else {
                                spec_current(s, Some(OpSpec::Reset { id, kind, corr, phase: ResetSpec::Deleting { pending } }))
                            }
                        },
                        (ResetSpec::Deleting { pending }, StoreOutcome::Done) => {
                            let pending = pending.remove(op);
                            if pending =~= Map::<OpId, bool>::empty() {
                                spec_debug_reset_done(s, id, kind, corr)
                            } else {
                                spec_current(s, Some(OpSpec::Reset { id, kind, corr, phase: ResetSpec::Deleting { pending } }))
                            }
                        },
                        (_, StoreOutcome::Failed(e)) => spec_debug_fail(s, id, kind, corr, e.deep_view()),
                        _ => spec_debug_fail(s, id, kind, corr, spec_unexpected()),
                    },
                    OpSpec::Snap { id, kind, corr, phase: SnapSpec::Gathering { ops, pending, origins, schedules } } => {
                        let gathered: Result<(S, Map<OpId, bool>, Map<OpId, bool>, Seq<DocV>, Seq<ScheduleSpec>), StoreErrorSpec> = match outcome {
                            StoreOutcome::Listed(keys) => {
                                let ops = ops.remove(op);
                                let (s, pending) = spec_get_keys(s, keys.deep_view(), pending);
                                Ok((s, ops, pending, origins, schedules))
                            },
                            StoreOutcome::Got(got) => {
                                let schedule = if pending.contains_key(op) { pending[op] } else { false };
                                let pending = pending.remove(op);
                                match got {
                                    Some((bytes, _)) => {
                                        if schedule {
                                            match doc::spec_decode_schedule(bytes@) {
                                                Ok(loaded) => match loaded.doc {
                                                    DocV::Schedule(Some(row)) => Ok((s, ops, pending, origins, schedules.push(row.deep_view()))),
                                                    _ => Ok((s, ops, pending, origins, schedules)),
                                                },
                                                Err(e) => Err(StoreErrorSpec::Unavailable(e)),
                                            }
                                        } else {
                                            match doc::spec_decode_origin(bytes@) {
                                                Ok(loaded) => Ok((s, ops, pending, origins.push(loaded.doc), schedules)),
                                                Err(e) => Err(StoreErrorSpec::Unavailable(e)),
                                            }
                                        }
                                    },
                                    None => Ok((s, ops, pending, origins, schedules)),
                                }
                            },
                            StoreOutcome::Failed(e) => Err(e.deep_view()),
                            _ => Err(spec_unexpected()),
                        };
                        match gathered {
                            Err(e) => spec_debug_fail(s, id, kind, corr, e),
                            Ok((s, ops, pending, origins, schedules)) => {
                                if ops =~= Map::<OpId, bool>::empty() && pending =~= Map::<OpId, bool>::empty() {
                                    spec_debug_reply(s, id, kind, corr, 200, DebugBodySpec::Snap { origins, schedules })
                                } else {
                                    spec_current(s, Some(OpSpec::Snap { id, kind, corr, phase: SnapSpec::Gathering { ops, pending, origins, schedules } }))
                                }
                            },
                        }
                    },
                    OpSpec::Tick { id, kind, corr, time, phase } => match (phase, outcome) {
                        (TickSpec::Listing { ops, origins, schedules }, StoreOutcome::Listed(keys)) => {
                            let ops = ops.remove(op);
                            let (origins, schedules) = spec_tick_names(s.keys.prefix, keys.deep_view(), origins, schedules);
                            if !(ops =~= Map::<OpId, bool>::empty()) {
                                spec_current(s, Some(OpSpec::Tick { id, kind, corr, time, phase: TickSpec::Listing { ops, origins, schedules } }))
                            } else {
                                // every origin swept at `time`; the flights report back
                                let outstanding = origins.len() as usize;
                                if outstanding == 0 {
                                    spec_debug_tick_fire(s, id, kind, corr, time, schedules)
                                } else {
                                    let s = spec_current(s, Some(OpSpec::Tick { id, kind, corr, time, phase: TickSpec::Sweeping { outstanding, schedules } }));
                                    spec_submit_sweeps(s, origins, time)
                                }
                            }
                        },
                        (_, StoreOutcome::Failed(e)) => spec_debug_fail(s, id, kind, corr, e.deep_view()),
                        _ => spec_debug_fail(s, id, kind, corr, spec_unexpected()),
                    },
                }
            }
        },
    }
}

/// Nothing of the documents is held any more: not the cache, not the
/// core's versions and keys, not the wheel.
#[verifier::opaque]
pub open spec fn spec_debug_reset_done(s: S, id: RequestId, kind: Seq<char>, corr: Seq<char>) -> S {
    let old_core = s.node.core;
    let fresh = ANode {
        id: s.cfg.node_id, ttl: s.cfg.node_ttl_ms as nat, read_any: false, epoch: 0,
        members: Seq::empty(), last_read: 0, cache: Map::empty(), armed: Map::empty(),
    };
    let core = if old_core.read_any { spec_read_config(fresh, old_core.last_read, old_core.epoch, old_core.members) } else { fresh };
    let s = S {
        cache: spec_new(s.cfg.cache_entries, s.cfg.cache_bytes),
        node: NodeSpec { core, ..s.node },
        timers: TimersSpec { wheel: TimerWheelSpec { armed: Seq::empty() }, ..s.timers },
        ..s
    };
    spec_debug_reply(s, id, kind, corr, 200, DebugBodySpec::Object)
}

/// A flight the tick started has ended: a sweep, or a fire that fired
/// (`idle` false) or found nothing due (`idle` true).
#[verifier::opaque]
pub open spec fn spec_debug_flight_done(s: S, work: WorkSpec, idle: bool) -> S {
    let fired_schedule = match work {
        WorkSpec::Fire { schedule, .. } => if !idle { Some(schedule) } else { None },
        _ => None,
    };
    spec_debug_tick_advance(s, fired_schedule)
}

/// Every schedule fired at `time`; the tick ends when none is left.
#[verifier::opaque]
pub open spec fn spec_debug_tick_fire(s: S, id: RequestId, kind: Seq<char>, corr: Seq<char>, time: u64, schedules: Seq<Seq<char>>) -> S {
    let outstanding = schedules.len() as usize;
    if outstanding == 0 {
        spec_debug_reply(spec_current(s, None), id, kind, corr, 200, DebugBodySpec::List)
    } else {
        let s = spec_current(s, Some(OpSpec::Tick { id, kind, corr, time, phase: TickSpec::Firing { outstanding } }));
        spec_submit_fires(s, schedules, time)
    }
}

/// One flight fewer outstanding; a schedule that fired is fired again,
/// since the next occurrence may be due too.
#[verifier::opaque]
pub open spec fn spec_debug_tick_advance(s: S, refire: Option<Seq<char>>) -> S {
    match s.debug.current {
        Some(OpSpec::Tick { id, kind, corr, time, phase }) => {
            let s = spec_current(s, None);
            match phase {
                TickSpec::Sweeping { outstanding, schedules } => {
                    let outstanding = outstanding.saturating_sub(if refire is None && outstanding > 0 { 1 } else { 0 });
                    if outstanding > 0 {
                        spec_current(s, Some(OpSpec::Tick { id, kind, corr, time, phase: TickSpec::Sweeping { outstanding, schedules } }))
                    } else {
                        spec_debug_tick_fire(s, id, kind, corr, time, schedules)
                    }
                },
                TickSpec::Firing { outstanding } => match refire {
                    Some(sch) => {
                        let s = spec_current(s, Some(OpSpec::Tick { id, kind, corr, time, phase: TickSpec::Firing { outstanding } }));
                        spec_submit(s, TargetSpec::Schedule(sch), WorkSpec::Fire { schedule: sch, fired: None, now: time }, None, true)
                    },
                    None => {
                        let outstanding = outstanding.saturating_sub(1);
                        if outstanding > 0 {
                            spec_current(s, Some(OpSpec::Tick { id, kind, corr, time, phase: TickSpec::Firing { outstanding } }))
                        } else {
                            spec_debug_reply(s, id, kind, corr, 200, DebugBodySpec::List)
                        }
                    },
                },
                TickSpec::Listing { .. } => spec_current(s, Some(OpSpec::Tick { id, kind, corr, time, phase })),
            }
        },
        _ => spec_current(s, None),
    }
}

// ---------------------------------------------------------------------------
// Run
// ---------------------------------------------------------------------------

fn resettable(class: &Option<String>) -> (r: bool)
    ensures
        r == spec_resettable(class.deep_view()),
{
    match class {
        Some(c) => str_eq(c.as_str(), "wf") || str_eq(c.as_str(), "sched") || str_eq(c.as_str(), "t"),
        None => false,
    }
}

fn is_class(class: &Option<String>, lit: &str) -> (r: bool)
    ensures
        r == (class.deep_view() == Some(lit@)),
{
    match class {
        Some(c) => str_eq(c.as_str(), lit),
        None => false,
    }
}

impl State {
    /// A debug operation the runtime has already accepted.
    pub fn debug_begin(&mut self, call: DebugCall)
        ensures
            final(self).deep_view() == spec_debug_begin(old(self).deep_view(), call.deep_view()),
    {
        proof {
            reveal(spec_debug_begin);
        }
        if self.debug.current.is_some() {
            let ghost q = self.debug.queue.deep_view();
            let ghost c = call.deep_view();
            self.debug.queue.push(call);
            proof {
                assert(self.debug.queue.deep_view() =~= q.push(c));
            }
            return;
        }
        self.debug_start(call);
    }

    /// The two listings a snapshot or a tick starts with.
    fn list_docs(&mut self) -> (ops: Table<OpId, bool>)
        ensures
            (final(self).deep_view(), ops.deep_view()) == spec_list_docs(old(self).deep_view()),
    {
        proof {
            reveal(spec_list_docs);
        }
        let mut ops: Table<OpId, bool> = Table::new();
        let p1 = concat(self.keys.prefix.as_str(), "wf/");
        let op1 = self.store(StoreCall::List { prefix: p1, max_keys: usize::MAX }, Owner::Debug);
        ops.insert(op1, true);
        let p2 = concat(self.keys.prefix.as_str(), "sched/");
        let op2 = self.store(StoreCall::List { prefix: p2, max_keys: usize::MAX }, Owner::Debug);
        ops.insert(op2, true);
        ops
    }

    fn debug_start(&mut self, call: DebugCall)
        ensures
            final(self).deep_view() == spec_debug_start(old(self).deep_view(), call.deep_view()),
    {
        proof {
            reveal(spec_debug_start);
        }
        match call {
            DebugCall::Reset { id, kind, corr } => {
                let prefix = copy_string(&self.cfg.prefix);
                let op = self.store(StoreCall::List { prefix, max_keys: usize::MAX }, Owner::Debug);
                self.debug.current = Some(Op::Reset { id, kind, corr, phase: Reset::Listing { op } });
            },
            DebugCall::Snap { id, kind, corr } => {
                let ops = self.list_docs();
                let phase = Snap::Gathering { ops, pending: Table::new(), origins: Vec::new(), schedules: Vec::new() };
                proof {
                    assert(phase.deep_view()->Gathering_origins =~= Seq::<DocV>::empty());
                    assert(phase.deep_view()->Gathering_schedules =~= Seq::<ScheduleSpec>::empty());
                }
                self.debug.current = Some(Op::Snap { id, kind, corr, phase });
            },
            DebugCall::Tick { id, kind, corr, time } => {
                let ops = self.list_docs();
                let phase = Tick::Listing { ops, origins: Vec::new(), schedules: Vec::new() };
                proof {
                    assert(phase.deep_view()->Listing_origins =~= Seq::<Seq<char>>::empty());
                    assert(phase.deep_view()->Listing_schedules =~= Seq::<Seq<char>>::empty());
                }
                self.debug.current = Some(Op::Tick { id, kind, corr, time, phase });
            },
        }
    }

    /// Answer, and start the next debug operation waiting.
    fn debug_reply(&mut self, id: RequestId, kind: String, corr: String, status: u16, body: DebugBody)
        ensures
            final(self).deep_view() == spec_debug_reply(old(self).deep_view(), id, kind@, corr@, status, body.deep_view()),
    {
        proof {
            reveal(spec_debug_reply);
        }
        self.emit(Effect::Reply { id, response: Ok(Answer::Debug { kind, corr, status, body }) });
        if self.debug.queue.len() > 0 {
            let ghost q0 = self.debug.queue.deep_view();
            let call = self.debug.queue.remove(0);
            proof {
                assert(call.deep_view() == q0[0]);
                assert(self.debug.queue.deep_view() =~= q0.drop_first());
            }
            self.debug_start(call);
        }
    }

    fn debug_fail(&mut self, id: RequestId, kind: String, corr: String, e: StoreError)
        ensures
            final(self).deep_view() == spec_debug_fail(old(self).deep_view(), id, kind@, corr@, e.deep_view()),
    {
        proof {
            reveal(spec_debug_fail);
        }
        self.debug.current = None;
        self.debug_reply(id, kind, corr, 503, DebugBody::Message(error_text(&e)));
    }

    /// A `Delete` for every resettable key.
    fn delete_keys(&mut self, keys: &Vec<String>, pending: &mut Table<OpId, bool>)
        ensures
            (final(self).deep_view(), final(pending).deep_view()) == spec_delete_keys(old(self).deep_view(), keys.deep_view(), old(pending).deep_view()),
    {
        let ghost ks = keys.deep_view();
        let ghost s0 = old(self).deep_view();
        let ghost p0 = old(pending).deep_view();
        let mut i: usize = 0;
        proof {
            assert(ks.skip(0) =~= ks);
        }
        while i < keys.len()
            invariant
                i <= keys.len(),
                ks == keys.deep_view(),
                spec_delete_keys(s0, ks, p0) == spec_delete_keys(self.deep_view(), ks.skip(i as int), pending.deep_view()),
            decreases keys.len() - i,
        {
            proof {
                assert(ks.skip(i as int).drop_first() =~= ks.skip(i as int + 1));
                assert(ks.skip(i as int)[0] == ks[i as int]);
            }
            let key = copy_string(&keys[i]);
            if resettable(&self.keys.class_of(key.as_str())) {
                let op = self.store(StoreCall::Delete { key }, Owner::Debug);
                pending.insert(op, true);
            }
            i += 1;
        }
        proof {
            assert(ks.skip(i as int) =~= Seq::<Seq<char>>::empty());
        }
    }

    /// A `Get` for every key listed, marked as a schedule's or not.
    fn get_keys(&mut self, keys: &Vec<String>, pending: &mut Table<OpId, bool>)
        ensures
            (final(self).deep_view(), final(pending).deep_view()) == spec_get_keys(old(self).deep_view(), keys.deep_view(), old(pending).deep_view()),
    {
        let ghost ks = keys.deep_view();
        let ghost s0 = old(self).deep_view();
        let ghost p0 = old(pending).deep_view();
        let mut i: usize = 0;
        proof {
            assert(ks.skip(0) =~= ks);
        }
        while i < keys.len()
            invariant
                i <= keys.len(),
                ks == keys.deep_view(),
                spec_get_keys(s0, ks, p0) == spec_get_keys(self.deep_view(), ks.skip(i as int), pending.deep_view()),
            decreases keys.len() - i,
        {
            proof {
                assert(ks.skip(i as int).drop_first() =~= ks.skip(i as int + 1));
                assert(ks.skip(i as int)[0] == ks[i as int]);
            }
            let key = copy_string(&keys[i]);
            let schedule = is_class(&self.keys.class_of(key.as_str()), "sched");
            let op = self.store(StoreCall::Get { key }, Owner::Debug);
            pending.insert(op, schedule);
            i += 1;
        }
        proof {
            assert(ks.skip(i as int) =~= Seq::<Seq<char>>::empty());
        }
    }

    /// The names a listing holds: origins and schedules, by class.
    fn tick_names(&self, keys: &Vec<String>, origins: &mut Vec<String>, schedules: &mut Vec<String>)
        ensures
            (final(origins).deep_view(), final(schedules).deep_view()) == spec_tick_names(self.keys.prefix@, keys.deep_view(), old(origins).deep_view(), old(schedules).deep_view()),
    {
        let ghost ks = keys.deep_view();
        let ghost o0 = old(origins).deep_view();
        let ghost c0 = old(schedules).deep_view();
        let ghost prefix = self.keys.prefix@;
        let mut i: usize = 0;
        proof {
            assert(ks.skip(0) =~= ks);
        }
        while i < keys.len()
            invariant
                i <= keys.len(),
                ks == keys.deep_view(),
                prefix == self.keys.prefix@,
                spec_tick_names(prefix, ks, o0, c0) == spec_tick_names(prefix, ks.skip(i as int), origins.deep_view(), schedules.deep_view()),
            decreases keys.len() - i,
        {
            proof {
                assert(ks.skip(i as int).drop_first() =~= ks.skip(i as int + 1));
                assert(ks.skip(i as int)[0] == ks[i as int]);
            }
            let key = &keys[i];
            let class = self.keys.class_of(key.as_str());
            let name = crate::keys::decode_key(crate::keys::last_segment(key.as_str()).as_str());
            let ghost ov = origins.deep_view();
            let ghost cv = schedules.deep_view();
            if is_class(&class, "wf") {
                if let Some(o) = name {
                    let ghost n = o@;
                    origins.push(o);
                    proof {
                        assert(origins.deep_view() =~= ov.push(n));
                    }
                }
            } else if is_class(&class, "sched") {
                if let Some(sch) = name {
                    let ghost n = sch@;
                    schedules.push(sch);
                    proof {
                        assert(schedules.deep_view() =~= cv.push(n));
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(ks.skip(i as int) =~= Seq::<Seq<char>>::empty());
        }
    }

    /// Every origin swept at `time`.
    fn submit_sweeps(&mut self, origins: &Vec<String>, time: u64)
        ensures
            final(self).deep_view() == spec_submit_sweeps(old(self).deep_view(), origins.deep_view(), time),
    {
        let ghost os = origins.deep_view();
        let ghost s0 = old(self).deep_view();
        let mut i: usize = 0;
        proof {
            assert(os.skip(0) =~= os);
        }
        while i < origins.len()
            invariant
                i <= origins.len(),
                os == origins.deep_view(),
                spec_submit_sweeps(s0, os, time) == spec_submit_sweeps(self.deep_view(), os.skip(i as int), time),
            decreases origins.len() - i,
        {
            proof {
                assert(os.skip(i as int).drop_first() =~= os.skip(i as int + 1));
                assert(os.skip(i as int)[0] == os[i as int]);
            }
            let o = copy_string(&origins[i]);
            self.submit(Target::Origin(o), Work::Sweep { fired: None, now: time }, None, true);
            i += 1;
        }
        proof {
            assert(os.skip(i as int) =~= Seq::<Seq<char>>::empty());
        }
    }

    /// Every schedule fired at `time`.
    fn submit_fires(&mut self, schedules: &Vec<String>, time: u64)
        ensures
            final(self).deep_view() == spec_submit_fires(old(self).deep_view(), schedules.deep_view(), time),
    {
        let ghost ss = schedules.deep_view();
        let ghost s0 = old(self).deep_view();
        let mut i: usize = 0;
        proof {
            assert(ss.skip(0) =~= ss);
        }
        while i < schedules.len()
            invariant
                i <= schedules.len(),
                ss == schedules.deep_view(),
                spec_submit_fires(s0, ss, time) == spec_submit_fires(self.deep_view(), ss.skip(i as int), time),
            decreases schedules.len() - i,
        {
            proof {
                assert(ss.skip(i as int).drop_first() =~= ss.skip(i as int + 1));
                assert(ss.skip(i as int)[0] == ss[i as int]);
            }
            let sch = copy_string(&schedules[i]);
            self.submit(Target::Schedule(copy_string(&sch)), Work::Fire { schedule: sch, fired: None, now: time }, None, true);
            i += 1;
        }
        proof {
            assert(ss.skip(i as int) =~= Seq::<Seq<char>>::empty());
        }
    }

    pub fn debug_completed(&mut self, op: OpId, outcome: StoreOutcome)
        ensures
            final(self).deep_view() == spec_debug_completed(old(self).deep_view(), op, outcome),
    {
        proof {
            reveal(spec_debug_completed);
        }
        let current = match take_opt(&mut self.debug.current) {
            Some(c) => c,
            None => return,
        };
        let expected = match &current {
            Op::Reset { phase: Reset::Listing { op: o }, .. } => *o == op,
            Op::Snap { phase: Snap::Gathering { ops, pending, .. }, .. } => ops.contains(&op) || pending.contains(&op),
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
                    let mut pending: Table<OpId, bool> = Table::new();
                    self.delete_keys(&keys, &mut pending);
                    if pending.is_empty() {
                        self.debug_reset_done(id, kind, corr);
                    } else {
                        self.debug.current = Some(Op::Reset { id, kind, corr, phase: Reset::Deleting { pending } });
                    }
                },
                (Reset::Deleting { mut pending }, StoreOutcome::Done) => {
                    pending.remove(&op);
                    if pending.is_empty() {
                        self.debug_reset_done(id, kind, corr);
                    } else {
                        self.debug.current = Some(Op::Reset { id, kind, corr, phase: Reset::Deleting { pending } });
                    }
                },
                (_, StoreOutcome::Failed(e)) => self.debug_fail(id, kind, corr, e),
                _ => self.debug_fail(id, kind, corr, unexpected()),
            },
            Op::Snap { id, kind, corr, phase: Snap::Gathering { mut ops, mut pending, mut origins, mut schedules } } => {
                let failed: Option<StoreError> = match outcome {
                    StoreOutcome::Listed(keys) => {
                        ops.remove(&op);
                        self.get_keys(&keys, &mut pending);
                        None
                    },
                    StoreOutcome::Got(got) => {
                        let schedule = match pending.remove(&op) {
                            Some(b) => b,
                            None => false,
                        };
                        match got {
                            Some((bytes, _)) => {
                                if schedule {
                                    match doc::decode_schedule(bytes.as_slice()) {
                                        Ok(loaded) => {
                                            proof {
                                                crate::concrete::document::lemma_doc_view(&loaded.doc);
                                            }
                                            match loaded.doc {
                                                Doc::Schedule(Some(row)) => {
                                                    let ghost cv = schedules.deep_view();
                                                    let ghost rv = row.deep_view();
                                                    schedules.push(row);
                                                    proof {
                                                        assert(schedules.deep_view() =~= cv.push(rv));
                                                    }
                                                },
                                                _ => {},
                                            }
                                            None
                                        },
                                        Err(e) => Some(StoreError::Unavailable(e)),
                                    }
                                } else {
                                    match doc::decode_origin(bytes.as_slice()) {
                                        Ok(loaded) => {
                                            let ghost ov = origins.deep_view();
                                            let ghost dv = loaded.doc@;
                                            origins.push(loaded.doc);
                                            proof {
                                                assert(origins.deep_view() =~= ov.push(dv));
                                            }
                                            None
                                        },
                                        Err(e) => Some(StoreError::Unavailable(e)),
                                    }
                                }
                            },
                            None => None,
                        }
                    },
                    StoreOutcome::Failed(e) => Some(e),
                    _ => Some(unexpected()),
                };
                match failed {
                    Some(e) => self.debug_fail(id, kind, corr, e),
                    None => {
                        if ops.is_empty() && pending.is_empty() {
                            self.debug_reply(id, kind, corr, 200, DebugBody::Snap { origins, schedules });
                        } else {
                            self.debug.current = Some(Op::Snap { id, kind, corr, phase: Snap::Gathering { ops, pending, origins, schedules } });
                        }
                    },
                }
            },
            Op::Tick { id, kind, corr, time, phase } => match (phase, outcome) {
                (Tick::Listing { mut ops, mut origins, mut schedules }, StoreOutcome::Listed(keys)) => {
                    ops.remove(&op);
                    self.tick_names(&keys, &mut origins, &mut schedules);
                    if !ops.is_empty() {
                        self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Listing { ops, origins, schedules } });
                        return;
                    }
                    // every origin swept at `time`; the flights report back
                    let outstanding = origins.len();
                    if outstanding == 0 {
                        self.debug_tick_fire(id, kind, corr, time, schedules);
                    } else {
                        self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Sweeping { outstanding, schedules } });
                        self.submit_sweeps(&origins, time);
                    }
                },
                (_, StoreOutcome::Failed(e)) => self.debug_fail(id, kind, corr, e),
                _ => self.debug_fail(id, kind, corr, unexpected()),
            },
        }
    }

    fn debug_reset_done(&mut self, id: RequestId, kind: String, corr: String)
        ensures
            final(self).deep_view() == spec_debug_reset_done(old(self).deep_view(), id, kind@, corr@),
    {
        proof {
            reveal(spec_debug_reset_done);
        }
        // nothing of the documents is held any more: not the cache, not the
        // core's versions and keys, not the wheel
        self.cache = Cache::new(self.cfg.cache_entries, self.cfg.cache_bytes);
        let epoch = self.node.core.epoch;
        let members = copy_members(&self.node.core.members);
        let last_read = self.node.core.last_read;
        let read_any = self.node.core.read_any;
        self.node.core = NodeCore::new(copy_string(&self.cfg.node_id), self.cfg.node_ttl_ms);
        if read_any {
            self.node.core.read_config(last_read, epoch, members);
        }
        self.timers.wheel = TimerWheel::new();
        self.debug_reply(id, kind, corr, 200, DebugBody::Object);
    }

    /// A flight the tick started has ended: a sweep, or a fire that fired
    /// (`idle` false) or found nothing due (`idle` true).
    pub fn debug_flight_done(&mut self, work: &Work, idle: bool)
        ensures
            final(self).deep_view() == spec_debug_flight_done(old(self).deep_view(), work.deep_view(), idle),
    {
        proof {
            reveal(spec_debug_flight_done);
        }
        let fired_schedule = match work {
            Work::Fire { schedule, .. } => if !idle { Some(copy_string(schedule)) } else { None },
            _ => None,
        };
        self.debug_tick_advance(fired_schedule);
    }

    /// Every schedule fired at `time`; the tick ends when none is left.
    fn debug_tick_fire(&mut self, id: RequestId, kind: String, corr: String, time: u64, schedules: Vec<String>)
        ensures
            final(self).deep_view() == spec_debug_tick_fire(old(self).deep_view(), id, kind@, corr@, time, schedules.deep_view()),
    {
        proof {
            reveal(spec_debug_tick_fire);
        }
        let outstanding = schedules.len();
        if outstanding == 0 {
            self.debug.current = None;
            self.debug_reply(id, kind, corr, 200, DebugBody::List);
        } else {
            self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Firing { outstanding } });
            self.submit_fires(&schedules, time);
        }
    }

    /// One flight fewer outstanding; a schedule that fired is fired again,
    /// since the next occurrence may be due too.
    fn debug_tick_advance(&mut self, refire: Option<String>)
        ensures
            final(self).deep_view() == spec_debug_tick_advance(old(self).deep_view(), refire.deep_view()),
    {
        proof {
            reveal(spec_debug_tick_advance);
        }
        let (id, kind, corr, time, phase) = match take_opt(&mut self.debug.current) {
            Some(Op::Tick { id, kind, corr, time, phase }) => (id, kind, corr, time, phase),
            _ => return,
        };
        match phase {
            Tick::Sweeping { outstanding, schedules } => {
                let outstanding = outstanding.saturating_sub(if refire.is_none() && outstanding > 0 { 1 } else { 0 });
                if outstanding > 0 {
                    self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Sweeping { outstanding, schedules } });
                    return;
                }
                self.debug_tick_fire(id, kind, corr, time, schedules);
            },
            Tick::Firing { outstanding } => {
                if let Some(sch) = refire {
                    self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Firing { outstanding } });
                    self.submit(Target::Schedule(copy_string(&sch)), Work::Fire { schedule: sch, fired: None, now: time }, None, true);
                    return;
                }
                let outstanding = outstanding.saturating_sub(1);
                if outstanding > 0 {
                    self.debug.current = Some(Op::Tick { id, kind, corr, time, phase: Tick::Firing { outstanding } });
                    return;
                }
                self.debug_reply(id, kind, corr, 200, DebugBody::List);
            },
            phase => {
                self.debug.current = Some(Op::Tick { id, kind, corr, time, phase });
            },
        }
    }
}

} // verus!
