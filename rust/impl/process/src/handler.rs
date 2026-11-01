//! The one step. A request that came in from the network is above the line.
//! Below it, the runtime: a store answer, the heartbeat, a deadline, the
//! process starting or stopping.

use crate::handler_docs::{Stage, Work};
use crate::types::*;
use crate::verified::Request;
use crate::{Owner, State};

impl State {
    /// An event in, the effects it calls for out.
    pub fn on_event(&mut self, event: Event) -> Vec<Effect> {
        match event {
            // -----------------------------------------------------------------
            // From the network, already admitted by the runtime.
            // -----------------------------------------------------------------
            Event::Request { clock, call } => {
                self.set_clock(clock);
                self.request(call);
            }
            Event::Debug { clock, call } => {
                self.set_clock(clock);
                self.debug_begin(call);
            }

            // -----------------------------------------------------------------
            // From the runtime, not the network.
            // -----------------------------------------------------------------
            Event::Start { clock, loops } => {
                self.set_clock(clock);
                self.loops = loops;
                let now = self.now();
                self.members_refresh(now);
            }
            Event::Completed { op, outcome, clock } => {
                self.set_clock(clock);
                match self.ops.remove(&op) {
                    Some(Owner::Flight(f)) => self.flight_completed(f, op, outcome),
                    Some(Owner::Members) => self.members_completed(op, outcome),
                    Some(Owner::Timers) => self.timers_completed(op, outcome),
                    Some(Owner::Debug) => self.debug_completed(op, outcome),
                    Some(Owner::Leaving) => self.mark_stopped(),
                    Some(Owner::Ignored) | None => {}
                }
            }
            Event::Due { clock, armed: _ } => {
                self.set_clock(clock);
                // A wake that came early asks again below.
                self.clear_wake();
                if self.loops && !self.stopping {
                    let now = self.now();
                    // One physical wake. It was armed for the heartbeat or
                    // for one key, and a late one covers every deadline
                    // already due and the heartbeat if its interval has come.
                    self.members_tick(now);
                    self.timers_run(now);
                }
            }
            Event::Stop { clock } => {
                self.set_clock(clock);
                self.stop();
            }
        }
        self.schedule_wake();
        self.take_out()
    }

    fn request(&mut self, mut call: Call) {
        // The fleet's time, unless the request named its own instant.
        if !call.pinned {
            call.now = call.now.max(self.node.fleet_at);
        }
        // A schedule's next run is that instant, the same one the step uses.
        if let Request::ScheduleCreate(q) = &mut call.request {
            q.next_run_at = crate::cron::next_after(&q.cron, call.now as i64).max(call.now as i64 + 1) as u64;
        }
        let Call { id, kind, corr, target, request, action_kind, now, pinned: _, then } = call;
        let stage = match then {
            Some((then, check)) => Stage::Detached { then, check: Some(Box::new(check)) },
            None => Stage::Whole,
        };
        let work = Work::Request { id, kind, corr, req: request, action_kind, now, stage };
        self.submit(target, work, None, false);
    }

    fn stop(&mut self) {
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

    pub(crate) fn leave(&mut self) {
        let key = self.keys.node_key(&self.cfg.node_id);
        self.store(StoreCall::Delete { key }, Owner::Leaving);
    }

    /// Ask the runtime to sleep until the next heartbeat or the next key,
    /// whichever comes first, and to say which one it was.
    fn schedule_wake(&mut self) {
        if !self.loops || self.stopping {
            return;
        }
        let now = self.now();
        let heartbeat = self.node.members.wake_at().map(|at| (at, Armed::Heartbeat));
        let timers = self.timers.next_wake(now);
        let next = match (heartbeat, timers) {
            (Some((ha, hb)), Some((ta, tb))) => Some(if ha < ta { (ha, hb) } else { (ta, tb) }),
            (Some(h), None) => Some(h),
            (None, Some(t)) => Some(t),
            (None, None) => None,
        };
        if self.wake_moved(next.clone()) {
            if let Some((at, armed)) = next {
                self.emit(Effect::Wake { after_ms: at.saturating_sub(now).max(1), armed });
            }
        }
    }
}
