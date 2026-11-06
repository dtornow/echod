//! The one step. A request that came in from the network is above the line.
//! Below it, the runtime: a store answer, the heartbeat, the wheel, the
//! process starting or stopping.
//!
//! Theorem 1: `State::on_event` computes `spec_on_event`. Verus checks it
//! here, over every method the step reaches.

use vstd::prelude::*;

use crate::handler_docs::{Stage, Work};
use crate::state::{Owner, State};
use crate::types::*;

#[cfg(verus_keep_ghost)]
use crate::debug::*;
#[cfg(verus_keep_ghost)]
use crate::handler_docs::*;
#[cfg(verus_keep_ghost)]
use crate::handler_node::*;
#[cfg(verus_keep_ghost)]
use crate::handler_timers::*;
#[cfg(verus_keep_ghost)]
use crate::keys::*;
#[cfg(verus_keep_ghost)]
use crate::state::*;
#[cfg(verus_keep_ghost)]
use crate::state_node::MembersSpec;
#[cfg(verus_keep_ghost)]
use crate::state_timers::spec_next_wake;
#[cfg(verus_keep_ghost)]
use echod_concrete::store::StoreCallSpec;

verus! {

// ---------------------------------------------------------------------------
// Stated
// ---------------------------------------------------------------------------

/// An event in, the effects it calls for out: the step of the process.
#[verifier::opaque]
pub open spec fn spec_on_event(s: S, event: EventSpec) -> (S, Seq<EffectSpec>) {
    let s = match event {
        EventSpec::Request { clock, call } => spec_request(S { clock, ..s }, call),
        EventSpec::Debug { clock, call } => spec_debug_begin(S { clock, ..s }, call),
        EventSpec::Start { clock, loops } => {
            let s = S { clock, loops, ..s };
            spec_members_refresh(s, spec_now(s))
        },
        EventSpec::Completed { op, outcome, clock } => {
            let s = S { clock, ..s };
            let owner = if s.ops.contains_key(op) { Some(s.ops[op]) } else { None };
            let s = S { ops: s.ops.remove(op), ..s };
            match owner {
                Some(Owner::Flight(f)) => spec_flight_completed(s, f, op, outcome),
                Some(Owner::Members) => spec_members_completed(s, op, outcome),
                Some(Owner::Timers) => spec_timers_completed(s, op, outcome),
                Some(Owner::Debug) => spec_debug_completed(s, op, outcome),
                Some(Owner::Leaving) => S { stopped: true, ..s },
                _ => s,
            }
        },
        EventSpec::Due { clock, armed } => {
            let s = S { clock, last_wake: None, ..s };
            if s.loops && !s.stopping {
                let now = spec_now(s);
                match armed {
                    Armed::Heartbeat => spec_timers_run(spec_members_tick(s, now), now),
                    Armed::Wheel => spec_members_tick(spec_timers_run(s, now), now),
                }
            } else {
                s
            }
        },
        EventSpec::Stop { clock } => spec_stop(S { clock, ..s }),
    };
    let s = spec_schedule_wake(s);
    (S { out: Seq::empty(), ..s }, s.out)
}

#[verifier::opaque]
pub open spec fn spec_request(s: S, call: CallSpec) -> S {
    let now = if call.pinned || call.now > s.node.fleet_at { call.now } else { s.node.fleet_at };
    let stage = match call.then {
        Some((then, check)) => StageSpec::Detached { then, check: Some(check) },
        None => StageSpec::Whole,
    };
    let work = WorkSpec::Request { id: call.id, kind: call.kind, corr: call.corr, req: call.request, action_kind: call.action_kind, now, stage };
    spec_submit(s, call.target, work, None, false)
}

#[verifier::opaque]
pub open spec fn spec_stop(s: S) -> S {
    let s = S { stopping: true, loops: false, ..s };
    if s.node.members.refreshing() {
        spec_with_members(s, MembersSpec { leave_pending: true, ..s.node.members })
    } else {
        spec_leave(s)
    }
}

#[verifier::opaque]
pub open spec fn spec_leave(s: S) -> S {
    let key = spec_node_key(s.keys.prefix, s.cfg.node_id);
    spec_store(s, StoreCallSpec::Delete { key }, Owner::Leaving).0
}

/// Ask the runtime to sleep until the next heartbeat or the next time the
/// wheel wants to look, whichever comes first, and to say which.
#[verifier::opaque]
pub open spec fn spec_schedule_wake(s: S) -> S {
    if !s.loops || s.stopping {
        s
    } else {
        let now = spec_now(s);
        let heartbeat = match s.node.members.wake_at() {
            Some(at) => Some((at, Armed::Heartbeat)),
            None => None,
        };
        let timers = spec_next_wake(s.timers, now);
        let next = match (heartbeat, timers) {
            (Some((ha, hb)), Some((ta, tb))) => Some(if ha < ta { (ha, hb) } else { (ta, tb) }),
            (Some(h), None) => Some(h),
            (None, Some(t)) => Some(t),
            (None, None) => None,
        };
        let (s, moved) = spec_wake_moved(s, next);
        if moved {
            match next {
                Some((at, armed)) => {
                    let after = at.saturating_sub(now);
                    spec_emit(s, EffectSpec::Wake { after_ms: if after > 1 { after } else { 1 }, armed })
                },
                None => s,
            }
        } else {
            s
        }
    }
}

// ---------------------------------------------------------------------------
// Run
// ---------------------------------------------------------------------------

impl State {
    /// An event in, the effects it calls for out.
    pub fn on_event(&mut self, event: Event) -> (out: Vec<Effect>)
        ensures
            (final(self).deep_view(), out.deep_view()) == spec_on_event(old(self).deep_view(), event.deep_view()),
    {
        proof {
            reveal(spec_on_event);
        }
        match event {
            // -----------------------------------------------------------------
            // From the network, already admitted by the runtime.
            // -----------------------------------------------------------------
            Event::Request { clock, call } => {
                self.set_clock(clock);
                self.request(call);
            },
            Event::Debug { clock, call } => {
                self.set_clock(clock);
                self.debug_begin(call);
            },
            // -----------------------------------------------------------------
            // From the runtime, not the network.
            // -----------------------------------------------------------------
            Event::Start { clock, loops } => {
                self.set_clock(clock);
                self.loops = loops;
                let now = self.now();
                self.members_refresh(now);
            },
            Event::Completed { op, outcome, clock } => {
                self.set_clock(clock);
                match self.ops.remove(&op) {
                    Some(Owner::Flight(f)) => self.flight_completed(f, op, outcome),
                    Some(Owner::Members) => self.members_completed(op, outcome),
                    Some(Owner::Timers) => self.timers_completed(op, outcome),
                    Some(Owner::Debug) => self.debug_completed(op, outcome),
                    Some(Owner::Leaving) => self.mark_stopped(),
                    Some(Owner::Ignored) | None => {},
                }
            },
            Event::Due { clock, armed } => {
                self.set_clock(clock);
                // A wake that came early asks again below.
                self.clear_wake();
                if self.loops && !self.stopping {
                    let now = self.now();
                    // The loop the sleep was for, then the other one: a late
                    // wake may have overrun it. Each loop checks its own clock.
                    match armed {
                        Armed::Heartbeat => self.members_tick(now),
                        Armed::Wheel => self.timers_run(now),
                    }
                    match armed {
                        Armed::Heartbeat => self.timers_run(now),
                        Armed::Wheel => self.members_tick(now),
                    }
                }
            },
            Event::Stop { clock } => {
                self.set_clock(clock);
                self.stop();
            },
        }
        self.schedule_wake();
        self.take_out()
    }

    fn request(&mut self, call: Call)
        ensures
            final(self).deep_view() == spec_request(old(self).deep_view(), call.deep_view()),
    {
        proof {
            reveal(spec_request);
        }
        let Call { id, kind, corr, target, request, action_kind, now, pinned, then } = call;
        // The fleet's time, unless the request named its own instant.
        let now = if pinned || now > self.node.fleet_at { now } else { self.node.fleet_at };
        let stage = match then {
            Some((then, check)) => Stage::Detached { then, check: Some(check) },
            None => Stage::Whole,
        };
        let work = Work::Request { id, kind, corr, req: request, action_kind, now, stage };
        self.submit(target, work, None, false);
    }

    fn stop(&mut self)
        ensures
            final(self).deep_view() == spec_stop(old(self).deep_view()),
    {
        proof {
            reveal(spec_stop);
        }
        self.stopping = true;
        self.loops = false;
        // A refresh in flight finishes first, so the announcement it
        // writes does not outlive the withdrawal.
        if self.node.members.refreshing() {
            self.node.members.leave_pending = true;
        } else {
            self.leave();
        }
    }

    pub fn leave(&mut self)
        ensures
            final(self).deep_view() == spec_leave(old(self).deep_view()),
    {
        proof {
            reveal(spec_leave);
        }
        let key = self.keys.node_key(self.cfg.node_id.as_str());
        self.store(StoreCall::Delete { key }, Owner::Leaving);
    }

    /// Ask the runtime to sleep until the next heartbeat or the next time
    /// the wheel wants to look, whichever comes first, and to say which.
    fn schedule_wake(&mut self)
        ensures
            final(self).deep_view() == spec_schedule_wake(old(self).deep_view()),
    {
        proof {
            reveal(spec_schedule_wake);
        }
        if !self.loops || self.stopping {
            return;
        }
        let now = self.now();
        let heartbeat = match self.node.members.wake_at() {
            Some(at) => Some((at, Armed::Heartbeat)),
            None => None,
        };
        let timers = self.timers.next_wake(now);
        let next = match (heartbeat, timers) {
            (Some((ha, hb)), Some((ta, tb))) => Some(if ha < ta { (ha, hb) } else { (ta, tb) }),
            (Some(h), None) => Some(h),
            (None, Some(t)) => Some(t),
            (None, None) => None,
        };
        if self.wake_moved(next) {
            if let Some((at, armed)) = next {
                let after = at.saturating_sub(now);
                self.emit(Effect::Wake { after_ms: if after > 1 { after } else { 1 }, armed });
            }
        }
    }
}

} // verus!
