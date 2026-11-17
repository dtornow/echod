//! Reconstruct production state from explicit inputs without executing effects.

use vstd::prelude::*;
use crate::{Config, State};
use crate::types::{Call, DebugCall, Effect, Event, RequestEvent};
use crate::verified::runtime::copy;
use crate::verified::text::copy_string;
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::handler::production_replay_state;
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::handler::production_handler_spec_on_event;

verus! {

pub fn copy_event(event: &Event) -> (result: Event)
    ensures result.deep_view() == event.deep_view(), result == *event,
{
    match event {
        Event::Store { op, response, clock } =>
            Event::Store { op: *op, response: copy(response), clock: *clock },
        Event::Wake { clock, armed } =>
            Event::Wake { clock: *clock, armed: *armed },
        Event::Request { clock, request } => {
            let request = match request {
                RequestEvent::Protocol(call) => {
                    let action_kind = match &call.action_kind {
                        Some(kind) => Some(copy_string(kind)),
                        None => None,
                    };
                    let then = match &call.then {
                        Some((target, request)) => Some((target.copy(), copy(request))),
                        None => None,
                    };
                    RequestEvent::Protocol(Call {
                        id: call.id,
                        kind: copy_string(&call.kind),
                        corr: copy_string(&call.corr),
                        target: call.target.copy(),
                        request: copy(&call.request),
                        action_kind,
                        now: call.now,
                        pinned: call.pinned,
                        then,
                    })
                },
                RequestEvent::Debug(call) => {
                    let call = match call {
                        DebugCall::Reset { id, kind, corr } => DebugCall::Reset {
                            id: *id, kind: copy_string(kind), corr: copy_string(corr),
                        },
                        DebugCall::Snap { id, kind, corr } => DebugCall::Snap {
                            id: *id, kind: copy_string(kind), corr: copy_string(corr),
                        },
                        DebugCall::Tick { id, kind, corr, time } => DebugCall::Tick {
                            id: *id, kind: copy_string(kind), corr: copy_string(corr), time: *time,
                        },
                    };
                    RequestEvent::Debug(call)
                },
            };
            Event::Request { clock: *clock, request }
        },
    }
}

pub fn replay(config: Config, loops: bool, events: &Vec<Event>) -> (state: State)
    ensures state.deep_view() == production_replay_state(config.deep_view(), loops, events.deep_view(), events.len() as nat),
{
    let ghost cfg = config.deep_view();
    let mut state = State::new(config);
    state.set_loops(loops);
    let mut i = 0usize;
    while i < events.len()
        invariant
            i <= events.len(),
            state.deep_view() == production_replay_state(cfg, loops, events.deep_view(), i as nat),
        decreases events.len() - i,
    {
        let event = copy_event(&events[i]);
        let _effects = state.on_event(event);
        i += 1;
    }
    state
}

pub fn replay_step(config: Config, loops: bool, events: &Vec<Event>, event: Event) -> (result: (State, Vec<Effect>))
    ensures
        (result.0.deep_view(), result.1.deep_view())
            == production_handler_spec_on_event(
                production_replay_state(config.deep_view(), loops, events.deep_view(), events.len() as nat),
                event.deep_view(),
            ),
{
    let mut state = replay(config, loops, events);
    let effects = state.on_event(event);
    (state, effects)
}

/// Equality compares complete input histories, not semantic state equivalence.
#[derive(Debug, PartialEq, Eq)]
pub struct ReplayBranch {
    config: Config,
    loops: bool,
    history: Vec<Event>,
}

#[cfg(verus_keep_ghost)]
impl View for ReplayBranch {
    type V = echod_concrete_spec::state::ProductionStateV;

    closed spec fn view(&self) -> Self::V {
        production_replay_state(self.config.deep_view(), self.loops, self.history.deep_view(), self.history.len() as nat)
    }
}

impl ReplayBranch {
    pub closed spec fn same_history(&self, other: Self) -> bool {
        self.config == other.config && self.loops == other.loops && self.history@ == other.history@
    }

    pub fn new(config: Config, loops: bool) -> (branch: Self)
        ensures branch@ == production_replay_state(config.deep_view(), loops, Seq::empty(), 0),
    {
        let branch = Self { config, loops, history: Vec::new() };
        proof { assert(branch.history.deep_view() =~= Seq::empty()); }
        branch
    }

    pub fn copy(&self) -> (branch: Self)
        ensures
            branch.same_history(*self),
            branch@ == self@,
    {
        let mut history = Vec::new();
        let mut i = 0;
        while i < self.history.len()
            invariant i <= self.history.len(), history@ == self.history@.take(i as int),
            decreases self.history.len() - i,
        {
            history.push(copy_event(&self.history[i]));
            i += 1;
            proof { assert(history@ =~= self.history@.take(i as int)); }
        }
        proof { assert(history@ =~= self.history@); }
        Self { config: copy(&self.config), loops: self.loops, history }
    }

    pub fn step(&self, event: &Event) -> (result: (Self, Vec<Effect>))
        ensures (result.0@, result.1.deep_view()) == production_handler_spec_on_event(self@, event.deep_view()),
    {
        let (_, effects) = replay_step(copy(&self.config), self.loops, &self.history, copy_event(event));
        let mut next = self.copy();
        next.history.push(copy_event(event));
        proof {
            assert(next.history.deep_view() =~= self.history.deep_view().push(event.deep_view()));
            assert(next.history.deep_view().take(self.history.len() as int) =~= self.history.deep_view());
            assert(self.history.deep_view().take(self.history.len() as int) =~= self.history.deep_view());
            echod_concrete_spec::property_proof::lemma_production_replay_prefix(
                self.config.deep_view(), self.loops, next.history.deep_view(),
                self.history.deep_view(), self.history.len() as nat,
            );
        }
        (next, effects)
    }
}

} // verus!

impl Clone for ReplayBranch {
    fn clone(&self) -> Self {
        self.copy()
    }
}
