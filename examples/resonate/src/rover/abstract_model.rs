//! The abstract Resonate Rover process.
//!
//! There is one real process containing the global Resonate state. Receiving
//! a call is one atomic linearization: the reference model chooses one allowed
//! outcome and emits its response and dispatches to Rover's outside endpoint.
//!
//! `on_event` and `spec_on_event` are intentionally written in parallel. The
//! former is the executable reference model used by trace search and replay;
//! the latter is the mathematical transition used by proofs. `RoverModel`'s
//! method contract is the obligation connecting them.
//!
//! This first layer covers atomic client calls and their immediate outputs.
//! Accordant's scheduled internal work is deliberately not lifted into Rover
//! yet; doing that requires making pending work part of the abstract process
//! state so append-only duplicate delivery cannot run one work item twice.

#[allow(unused_imports)] // specification-only names are erased by ordinary Rust
use accordant::rover::semantics::StepResultV;
use accordant::rover::{ProcessEvent, RoverModel, StepResult};
#[allow(unused_imports)] // specification-only names are erased by ordinary Rust
use accordant::semantics::ExternalOutcomeV;
use accordant::{ExternalOutcome, Model as AccordantModel, Time};
use vstd::prelude::*;

use crate::collections::{copy, PMap};
#[cfg(verus_keep_ghost)]
use crate::spec::{
    axiom_realised, lemma_server_ext, lift_server, DispatchV, InternalV, ResponseV, ServerV,
};
#[allow(unused_imports)] // Dispatch and Response also name specification types
use crate::{Dispatch, Resonate, Response, Server};

use super::{Call, Message, Output};

verus! {

/// The abstract world has one stateful service and one stateless outside
/// endpoint.
#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum Pid {
    Outside,
    Service,
}

/// The executable abstract reference model.
pub struct Model {
    pub logic: Resonate,
}

impl Default for Model {
    fn default() -> Self {
        Self { logic: Resonate { retry_timeout: 5_000, fire_within: 0 } }
    }
}

pub open spec fn empty_server_v() -> ServerV {
    ServerV {
        promises: Map::empty(),
        tasks: Map::empty(),
        schedules: Map::empty(),
    }
}

pub open spec fn spec_initial_state() -> Server {
    lift_server(empty_server_v())
}

fn initial_state() -> (state: Server)
    ensures
        state == spec_initial_state(),
{
    let state = Server {
        promises: PMap::empty(),
        tasks: PMap::empty(),
        schedules: PMap::empty(),
    };
    proof {
        broadcast use crate::spec::group_views;
        assert(state.promises@ == Map::empty());
        assert(state.tasks@ == Map::empty());
        assert(state.schedules@ == Map::empty());
        assert(state.promises@.map_values(|p: crate::Promise| p@) =~= Map::empty());
        assert(state.tasks@.map_values(|t: crate::Task| t@) =~= Map::empty());
        assert(state.schedules@.map_values(|s: crate::Schedule| s@) =~= Map::empty());
        axiom_realised(
            empty_server_v(),
            ResponseV::Status(0),
            InternalV::On(Seq::empty()),
            DispatchV::Execute {
                id: Seq::empty(),
                version: 0,
            },
        );
        assert(state@ == empty_server_v());
        lemma_server_ext(state, spec_initial_state());
    }
    state
}

/// One abstract outcome, as the specification sees it.
pub open spec fn spec_outcome(
    call: Call,
    outcome: ExternalOutcomeV<Server, Response, crate::Internal, Dispatch>,
) -> StepResultV<Server, Pid, Message> {
    StepResultV {
        state: outcome.next,
        send: seq![(
            Pid::Outside,
            Message::Output(Output::Response {
                client: call.client,
                id: call.id,
                response: outcome.resp,
            }),
        )] + outcome.send.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        )),
    }
}

/// Translate the Accordant reference model's executable outcome into Rover's
/// process result.
fn map_outcome(
    call: &Call,
    value: ExternalOutcome<Resonate>,
) -> (result: StepResult<Model>)
    ensures
        (StepResultV { state: result.state, send: result.send@ }) == spec_outcome(
            *call,
            ExternalOutcomeV {
                next: value.next,
                resp: value.resp,
                work: value.work@,
                send: value.send@,
            },
        ),
{
    let ExternalOutcome { next, resp, work: _, mut send, marks: _ } = value;
    let ghost dispatches = send@;
    let ghost response = resp;
    let ghost first = (
        Pid::Outside,
        Message::Output(Output::Response {
            client: call.client,
            id: call.id,
            response,
        }),
    );
    let mut effects = Vec::new();
    effects.push((
        Pid::Outside,
        Message::Output(Output::Response {
            client: copy(&call.client),
            id: call.id,
            response: resp,
        }),
    ));
    while !send.is_empty()
        invariant
            effects@.len() >= 1,
            effects@[0] == first,
            effects@.len() == 1 + dispatches.len() - send@.len(),
            send@ == dispatches.skip(dispatches.len() - send@.len()),
            effects@.skip(1) == dispatches
                .take(dispatches.len() - send@.len())
                .map_values(|dispatch: Dispatch| (
                    Pid::Outside,
                    Message::Output(Output::Dispatch(dispatch)),
                )),
        decreases send.len(),
    {
        let ghost k = effects@.len() as int - 1;
        assert(k == dispatches.len() - send@.len());
        assert(send@.len() > 0);
        assert(0 <= k < dispatches.len());
        let ghost before_effects = effects@;
        let dispatch = send.remove(0);
        proof {
            assert(dispatch == dispatches[k]);
            assert(dispatches.skip(k).remove(0) =~= dispatches.skip(k + 1));
            assert(dispatches.take(k + 1) =~= dispatches.take(k).push(dispatches[k]));
        }
        effects.push((
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        ));
        proof {
            assert(effects@ == before_effects.push((
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )));
            assert(effects@.skip(1) == before_effects.skip(1).push((
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )));
            assert(dispatches
                .take(k + 1)
                .map_values(|dispatch: Dispatch| (
                    Pid::Outside,
                    Message::Output(Output::Dispatch(dispatch)),
                )) =~= dispatches
                .take(k)
                .map_values(|dispatch: Dispatch| (
                    Pid::Outside,
                    Message::Output(Output::Dispatch(dispatch)),
                ))
                .push((
                    Pid::Outside,
                    Message::Output(Output::Dispatch(dispatches[k])),
                )));
            assert(effects@.skip(1) =~= dispatches
                .take(k + 1)
                .map_values(|dispatch: Dispatch| (
                    Pid::Outside,
                    Message::Output(Output::Dispatch(dispatch)),
                )));
        }
    }
    proof {
        assert(dispatches.take(dispatches.len() as int) =~= dispatches);
        assert(effects@.skip(1) =~= dispatches.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        )));
        assert(effects@ =~= seq![first] + dispatches.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        )));
    }
    StepResult { state: next, send: effects }
}

/// Translate every possible executable outcome, preserving its index.
fn outcomes(
    call: &Call,
    mut values: Vec<ExternalOutcome<Resonate>>,
) -> (results: Vec<StepResult<Model>>)
    ensures
        results@.len() == values@.len(),
        forall|i: int| 0 <= i < results@.len() ==> {
            let value = #[trigger] values@[i];
            (StepResultV { state: results@[i].state, send: results@[i].send@ }) == spec_outcome(
                *call,
                ExternalOutcomeV {
                    next: value.next,
                    resp: value.resp,
                    work: value.work@,
                    send: value.send@,
                },
            )
        },
{
    let ghost all = values@;
    let mut results: Vec<StepResult<Model>> = Vec::new();
    while !values.is_empty()
        invariant
            values@ == all.skip(results@.len() as int),
            results@.len() + values@.len() == all.len(),
            forall|i: int| 0 <= i < results@.len() ==> {
                let value = #[trigger] all[i];
                (StepResultV { state: results@[i].state, send: results@[i].send@ }) == spec_outcome(
                    *call,
                    ExternalOutcomeV {
                        next: value.next,
                        resp: value.resp,
                        work: value.work@,
                        send: value.send@,
                    },
                )
            },
        decreases values.len(),
    {
        let ghost i = results@.len() as int;
        let value = values.remove(0);
        assert(value == all[i]);
        results.push(map_outcome(call, value));
    }
    results
}

pub open spec fn spec_request_outcomes(
    model: Model,
    call: Call,
    state: Server,
) -> Seq<StepResultV<Server, Pid, Message>> {
    model
        .logic
        .spec_external(call.request, state, call.requested_at)
        .map_values(|outcome: ExternalOutcomeV<
            Server,
            Response,
            crate::Internal,
            Dispatch,
        >| spec_outcome(call, outcome))
}

fn request_outcomes(
    model: &Model,
    call: &Call,
    state: &Server,
) -> (results: Vec<StepResult<Model>>)
    ensures
        results@.map_values(|result: StepResult<Model>|
            StepResultV { state: result.state, send: result.send@ }
        ) == spec_request_outcomes(*model, *call, *state),
{
    let values =
        model.logic.external(&call.request, state, call.requested_at);
    let ghost executable = values@;
    let ghost specified =
        model.logic.spec_external(call.request, *state, call.requested_at);
    let results = outcomes(call, values);
    proof {
        assert(results@.len() == specified.len());
        assert forall|i: int| 0 <= i < results@.len() implies {
            let value = #[trigger] executable[i];
            (StepResultV {
                state: results@[i].state,
                send: results@[i].send@,
            }) == spec_outcome(
                *call,
                ExternalOutcomeV {
                    next: value.next,
                    resp: value.resp,
                    work: value.work@,
                    send: value.send@,
                },
            )
        } by {
        }
        assert forall|i: int| 0 <= i < results@.len() implies {
            let value = #[trigger] executable[i];
            ExternalOutcomeV {
                next: value.next,
                resp: value.resp,
                work: value.work@,
                send: value.send@,
            } == specified[i]
        } by {
        }
        let ghost actual = results@.map_values(|result: StepResult<Model>|
            StepResultV { state: result.state, send: result.send@ }
        );
        let ghost expected = specified.map_values(|value: ExternalOutcomeV<
            Server,
            Response,
            crate::Internal,
            Dispatch,
        >| spec_outcome(*call, value));
        assert(actual.len() == expected.len());
        assert forall|i: int| 0 <= i < actual.len() implies
            actual[i] == expected[i] by {
            let value = executable[i];
            let lifted = ExternalOutcomeV {
                next: value.next,
                resp: value.resp,
                work: value.work@,
                send: value.send@,
            };
            assert(actual[i] == spec_outcome(*call, lifted));
            assert(lifted == specified[i]);
            assert(expected[i] == spec_outcome(*call, specified[i]));
        }
        assert(actual =~= expected);
    }
    results
}

pub open spec fn spec_idle(state: Server) -> Seq<StepResultV<Server, Pid, Message>> {
    seq![StepResultV {
        state,
        send: Seq::empty(),
    }]
}

fn idle(state: &Server) -> (results: Vec<StepResult<Model>>)
    ensures
        results@.map_values(|result: StepResult<Model>|
            StepResultV { state: result.state, send: result.send@ }
        ) == spec_idle(*state),
{
    let mut results = Vec::new();
    results.push(StepResult {
        state: copy(state),
        send: Vec::new(),
    });
    results
}

impl RoverModel for Model {
    type Config = ();
    type Pid = Pid;
    type State = Server;
    type Message = Message;

    fn outside(&self) -> (outside: Pid) {
        Pid::Outside
    }

    fn initial(&self, _config: &()) -> (states: Vec<(Pid, Server)>) {
        vec![(Pid::Service, initial_state())]
    }

    fn injectable(&self, _config: &(), message: &Message) -> (injectable: bool) {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    fn on_event(
        &self,
        _config: &(),
        pid: &Pid,
        state: &Server,
        _now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (results: Vec<StepResult<Self>>) {
        match (pid, event) {
            (
                Pid::Service,
                ProcessEvent::Receive {
                    sender: Pid::Outside,
                    message: Message::Request(call),
                },
            ) => request_outcomes(self, call, state),
            _ => idle(state),
        }
    }

    open spec fn spec_outside(&self) -> Pid {
        Pid::Outside
    }

    open spec fn spec_initial(&self, _config: ()) -> Seq<(Pid, Server)> {
        seq![(Pid::Service, spec_initial_state())]
    }

    open spec fn spec_injectable(&self, _config: (), message: Message) -> bool {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    open spec fn spec_on_event(
        &self,
        _config: (),
        pid: Pid,
        state: Server,
        _now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<StepResultV<Server, Pid, Message>> {
        match (pid, event) {
            (
                Pid::Service,
                ProcessEvent::Receive {
                    sender: Pid::Outside,
                    message: Message::Request(call),
                },
            ) => spec_request_outcomes(*self, call, state),
            _ => spec_idle(state),
        }
    }
}

} // verus!
