//! The one step. A request that came in from the network is above the line.
//! Below it, the runtime: a store answer, the heartbeat, or the wheel.
//!
//! Theorem 1: `State::on_event` computes `spec_on_event`. Verus checks it
//! here, over every method the step reaches.

use vstd::prelude::*;

use crate::handler_docs::Work;
use crate::state::{Owner, State};
use crate::types::*;
use echod_types::{Response, StatusRes};

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
use crate::state_timers::spec_next_wake;

verus! {

// ---------------------------------------------------------------------------
// Stated
// ---------------------------------------------------------------------------

/// An event in, the effects it calls for out: the step of the process.
#[verifier::opaque]
pub open spec fn spec_on_event(s: S, event: EventSpec) -> (S, Seq<EffectSpec>) {
    let clock = match event {
        EventSpec::Request { clock, .. }
        | EventSpec::Store { clock, .. }
        | EventSpec::Wake { clock, .. } => clock,
    };
    let s = S { clock, ..s };
    let s = if s.node.members.next_heartbeat is None
        && !s.node.members.refreshing()
    {
        spec_members_tick(s, spec_now(s))
    } else {
        s
    };
    let s = match event {
        EventSpec::Request { clock, request } => match request {
            RequestEventSpec::Protocol(call) => spec_request(s, call),
            RequestEventSpec::EmptyHeartbeat { id, kind, corr, action_kind } =>
                spec_emit(s, EffectSpec::Reply {
                    id,
                    response: Ok(AnswerSpec::Step {
                        kind,
                        corr,
                        action_kind,
                        response: Response::Status(StatusRes { status: 200 }),
                        why: None,
                    }),
                }),
            RequestEventSpec::Debug(call) => spec_debug_begin(s, call),
        },
        EventSpec::Store { op, response, .. } => {
            let owner = if s.ops.contains_key(op) { Some(s.ops[op]) } else { None };
            let s = S { ops: s.ops.remove(op), ..s };
            match owner {
                Some(Owner::Flight(f)) => spec_flight_completed(s, f, op, response),
                Some(Owner::Members) => spec_members_completed(s, op, response),
                Some(Owner::Timers) => spec_timers_completed(s, op, response),
                Some(Owner::Debug) => spec_debug_completed(s, op, response),
                _ => s,
            }
        },
        EventSpec::Wake { armed, .. } => {
            let s = S { last_wake: None, ..s };
            if s.loops {
                let now = spec_now(s);
                match armed {
                    Armed::Heartbeat => spec_timers_run(spec_members_tick(s, now), now),
                    Armed::Wheel => spec_members_tick(spec_timers_run(s, now), now),
                }
            } else {
                s
            }
        },
    };
    let s = spec_schedule_wake(s);
    (S { out: Seq::empty(), ..s }, s.out)
}

#[verifier::opaque]
pub open spec fn spec_request(s: S, call: CallSpec) -> S {
    let now = if call.pinned || call.now > s.node.fleet_at { call.now } else { s.node.fleet_at };
    let work = WorkSpec::Request { id: call.id, kind: call.kind, corr: call.corr, req: call.request, action_kind: call.action_kind, now };
    spec_submit(s, call.target, work, None, false)
}

/// Ask the runtime to sleep until the next heartbeat or the next time the
/// wheel wants to look, whichever comes first, and to say which.
#[verifier::opaque]
pub open spec fn spec_schedule_wake(s: S) -> S {
    if !s.loops {
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
        let clock = match &event {
            Event::Request { clock, .. }
            | Event::Store { clock, .. }
            | Event::Wake { clock, .. } => *clock,
        };
        self.set_clock(clock);
        if self.node.members.next_heartbeat.is_none()
            && !self.node.members.refreshing()
        {
            let now = self.now();
            self.members_tick(now);
        }
        match event {
            // -----------------------------------------------------------------
            // From the network, already admitted by the runtime.
            // -----------------------------------------------------------------
            Event::Request { request, .. } => {
                match request {
                    RequestEvent::Protocol(call) => self.request(call),
                    RequestEvent::EmptyHeartbeat { id, kind, corr, action_kind } =>
                        self.emit(Effect::Reply {
                            id,
                            response: Ok(Answer::Step {
                                kind,
                                corr,
                                action_kind,
                                response: Response::Status(StatusRes { status: 200 }),
                                why: None,
                            }),
                        }),
                    RequestEvent::Debug(call) => self.debug_begin(call),
                }
            },
            // -----------------------------------------------------------------
            // From the runtime, not the network.
            // -----------------------------------------------------------------
            Event::Store { op, response, .. } => {
                match self.ops.remove(&op) {
                    Some(Owner::Flight(f)) => self.flight_completed(f, op, response),
                    Some(Owner::Members) => self.members_completed(op, response),
                    Some(Owner::Timers) => self.timers_completed(op, response),
                    Some(Owner::Debug) => self.debug_completed(op, response),
                    Some(Owner::Ignored) | None => {},
                }
            },
            Event::Wake { armed, .. } => {
                // A wake that came early asks again below.
                self.clear_wake();
                if self.loops {
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
        let Call { id, kind, corr, target, request, action_kind, now, pinned } = call;
        // The fleet's time, unless the request named its own instant.
        let now = if pinned || now > self.node.fleet_at { now } else { self.node.fleet_at };
        let work = Work::Request { id, kind, corr, req: request, action_kind, now };
        self.submit(target, work, None, false);
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
        if !self.loops {
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
