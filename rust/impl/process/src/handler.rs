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
    if event is Store && !s.ops.contains_key(event->Store_op) {
        (S { out: Seq::empty(), ..s }, s.out)
    } else {
        spec_on_known_event(s, event)
    }
}

pub open spec fn spec_dispatch_known_event(
    s: S,
    event: EventSpec,
) -> S {
    match event {
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
            let s = S {
                ops: s.ops.remove(op),
                store_requests: s.store_requests.remove(op),
                store_certificates:
                    s.store_certificates.remove(op),
                ..s
            };
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
    }
}

pub open spec fn spec_on_known_event(
    s: S,
    event: EventSpec,
) -> (S, Seq<EffectSpec>) {
    let before = s;
    let keys = s.keys;
    let clock = match event {
        EventSpec::Request { clock, .. }
        | EventSpec::Store { clock, .. }
        | EventSpec::Wake { clock, .. } => clock,
    };
    let s = S { clock, ..s };
    let s = if !(event is Store)
        && s.node.members.next_heartbeat is None
        && !s.node.members.refreshing()
    {
        spec_members_tick(s, spec_now(s))
    } else {
        s
    };
    let s = spec_dispatch_known_event(s, event);
    let s = spec_schedule_wake(s);
    let s = match event {
        EventSpec::Store { op, .. }
            if before.ops.contains_key(op)
                && before.ops[op] is Flight => {
            let freeze_before = S {
                ops: before.ops.remove(op),
                store_requests: before.store_requests.remove(op),
                store_certificates:
                    before.store_certificates.remove(op),
                ..before
            };
            spec_freeze_active_store_certificates(freeze_before, s)
        },
        _ => s,
    };
    let next_op =
        if s.next_op < before.next_op { before.next_op } else { s.next_op };
    (S { out: Seq::empty(), keys, next_op, ..s }, s.out)
}

/// Certificates are immutable for the lifetime of an operation. Event
/// handlers may consume one operation and issue fresh successors, but they
/// must never rewrite a certificate belonging to an operation that remains
/// active.
pub open spec fn spec_freeze_active_store_certificates(
    before: S,
    after: S,
) -> S {
    S {
        store_certificates: Map::new(
            after.ops.dom(),
            |op: u64|
                if before.store_certificates.contains_key(op) {
                    before.store_certificates[op]
                } else {
                    after.store_certificates[op]
                },
        ),
        ..after
    }
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
            final(self).keys.deep_view() == old(self).keys.deep_view(),
    {
        proof {
            reveal(spec_on_event);
        }
        let ghost before = self.deep_view();
        if let Event::Store { op, .. } = &event {
            if !self.ops.contains(op) {
                proof {
                    assert(event.deep_view() is Store);
                    assert(event.deep_view()->Store_op == *op);
                    assert(!before.ops.contains_key(*op));
                }
                return self.take_out();
            }
        }
        proof {
            match &event {
                Event::Store { op, .. } => {
                    assert(before.ops.contains_key(*op));
                    assert(event.deep_view()->Store_op == *op);
                },
                _ => {
                    assert(!(event.deep_view() is Store));
                },
            }
            assert(!(event.deep_view() is Store
                && !before.ops.contains_key(
                    event.deep_view()->Store_op,
                )));
        }
        self.on_known_event(event)
    }

    fn preserve_next_op_floor(&mut self, floor: OpId)
        ensures
            final(self).deep_view() == (S {
                next_op: if old(self).next_op < floor {
                    floor
                } else {
                    old(self).next_op
                },
                ..old(self).deep_view()
            }),
    {
        if self.next_op < floor {
            self.next_op = floor;
        }
    }

    #[verifier::rlimit(30)]
    #[verifier::spinoff_prover]
    fn on_known_event(&mut self, event: Event) -> (out: Vec<Effect>)
        ensures
            (final(self).deep_view(), out.deep_view())
                == spec_on_known_event(
                    old(self).deep_view(),
                    event.deep_view(),
                ),
            final(self).keys.deep_view()
                == old(self).keys.deep_view(),
    {
        proof {
            reveal(spec_on_known_event);
        }
        let ghost before = self.deep_view();
        let ghost event_v = event.deep_view();
        let freeze_flight = match &event {
            Event::Store { op, .. } => {
                matches!(self.ops.get(op), Some(Owner::Flight(_)))
            },
            _ => false,
        };
        proof {
            assert(freeze_flight == match event_v {
                EventSpec::Store { op, .. }
                    if before.ops.contains_key(op)
                        && before.ops[op] is Flight => true,
                _ => false,
            });
        }
        let ghost freeze_before = match event_v {
            EventSpec::Store { op, .. } => S {
                ops: before.ops.remove(op),
                store_requests: before.store_requests.remove(op),
                store_certificates: before.store_certificates.remove(op),
                ..before
            },
            _ => before,
        };
        let keys = self.keys.copy();
        let next_op = self.next_op;
        let clock = match &event {
            Event::Request { clock, .. }
            | Event::Store { clock, .. }
            | Event::Wake { clock, .. } => *clock,
        };
        self.set_clock(clock);
        proof {
            assert(self.keys.deep_view() == before.keys);
        }
        let is_store_event = matches!(&event, Event::Store { .. });
        if !is_store_event
            && self.node.members.next_heartbeat.is_none()
            && !self.node.members.refreshing()
        {
            let now = self.now();
            self.members_tick(now);
        }
        self.dispatch_known_event(event);
        self.schedule_wake();
        #[cfg(verus_keep_ghost)]
        if freeze_flight {
            self.freeze_active_store_certificates(Ghost(freeze_before));
        }
        self.preserve_next_op_floor(next_op);
        self.keys = keys;
        proof {
            assert(self.keys.deep_view() == before.keys);
            assert((
                S {
                    out: Seq::empty(),
                    keys: before.keys,
                    ..self.deep_view()
                },
                self.deep_view().out,
            ) == spec_on_known_event(before, event_v));
        }
        self.take_out()
    }

    #[verifier::spinoff_prover]
    fn dispatch_known_event(&mut self, event: Event)
        ensures
            final(self).deep_view()
                == spec_dispatch_known_event(
                    old(self).deep_view(),
                    event.deep_view(),
                ),
    {
        proof {
            reveal(spec_dispatch_known_event);
        }
        match event {
            Event::Request { request, .. } => match request {
                RequestEvent::Protocol(call) => self.request(call),
                RequestEvent::EmptyHeartbeat {
                    id,
                    kind,
                    corr,
                    action_kind,
                } => self.emit(Effect::Reply {
                    id,
                    response: Ok(Answer::Step {
                        kind,
                        corr,
                        action_kind,
                        response:
                            Response::Status(StatusRes { status: 200 }),
                        why: None,
                    }),
                }),
                RequestEvent::Debug(call) => self.debug_begin(call),
            },
            Event::Store { op, response, .. } => {
                #[cfg(verus_keep_ghost)]
                {
                    self.store_requests = StoreRequestHistory {
                        inner: Ghost(
                            self.store_requests.deep_view().remove(op),
                        ),
                    };
                    self.store_certificates = StoreCertificateHistory {
                        inner: Ghost(
                            self.store_certificates
                                .deep_view()
                                .remove(op),
                        ),
                    };
                }
                match self.ops.remove(&op) {
                    Some(Owner::Flight(f)) =>
                        self.flight_completed(f, op, response),
                    Some(Owner::Members) =>
                        self.members_completed(op, response),
                    Some(Owner::Timers) =>
                        self.timers_completed(op, response),
                    Some(Owner::Debug) =>
                        self.debug_completed(op, response),
                    Some(Owner::Ignored) | None => {},
                }
            },
            Event::Wake { armed, .. } => {
                self.clear_wake();
                if self.loops {
                    let now = self.now();
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
    }

    #[cfg(verus_keep_ghost)]
    fn freeze_active_store_certificates(
        &mut self,
        Ghost(before): Ghost<S>,
    )
        ensures
            final(self).deep_view()
                == spec_freeze_active_store_certificates(
                    before,
                    old(self).deep_view(),
                ),
    {
        let ghost after = self.deep_view();
        self.store_certificates = StoreCertificateHistory {
            inner: Ghost(Map::new(
                after.ops.dom(),
                |op: u64|
                    if before.store_certificates.contains_key(op) {
                        before.store_certificates[op]
                    } else {
                        after.store_certificates[op]
                    },
            )),
        };
        proof {
            reveal(spec_freeze_active_store_certificates);
        }
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
