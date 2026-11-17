//! The one step. A request that came in from the network is above the line.
//! Below it, the runtime: a store answer, the heartbeat, or the wheel.
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
use crate::state_timers::spec_next_wake;

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_handler_spec_on_event as spec_on_event,
    production_handler_spec_request as spec_request,
    production_handler_spec_schedule_wake as spec_schedule_wake,
};

verus! {

// ---------------------------------------------------------------------------
// Stated
// ---------------------------------------------------------------------------

/// An event in, the effects it calls for out: the step of the process.




/// Ask the runtime to sleep until the next heartbeat or the next time the
/// wheel wants to look, whichever comes first, and to say which.


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
