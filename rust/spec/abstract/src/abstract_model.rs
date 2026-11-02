//! Complete one-process abstract Resonate model.
//!
//! Requests atomically run the complete Resonate handler. Timeout events run
//! any enabled internal item: promise deadlines, task leases, callbacks,
//! retries, listener notification, and schedule fire/advance work.

use vstd::prelude::*;

use echod_rover::certificate::trusted::copy;
#[allow(unused_imports)] // specification-only name is erased by ordinary Rust
use echod_rover::rover::semantics::{Label, StepResultV};
use echod_rover::rover::{Process, ProcessEvent, RoverModel, StepResult};
use echod_rover::{Sched, Time};

use echod_types::Response;

use super::exec::{Dispatch, InOut, Out, Resonate, Server, Work};
use super::protocol::{BoundaryEvent, Call, Message, Output};
#[cfg(verus_keep_ghost)]
use super::spec::{group_views, lemma_lift_dispatch, DispatchV, InOutV, OutV};
use super::spec::{InternalV, ServerV};

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum Pid {
    Outside,
    Service,
}

#[derive(Clone, PartialEq, Eq, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct State {
    pub server: Server,
    pub pending: Vec<Work>,
}

pub struct StateV {
    pub server: ServerV,
    pub pending: Seq<Sched<InternalV>>,
}

impl View for State {
    type V = StateV;

    open spec fn view(&self) -> StateV {
        StateV {
            server: self.server@,
            pending: self.pending@.map_values(|work: Work| work@),
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Model;

pub open spec fn empty_server() -> ServerV {
    ServerV {
        promises: Map::empty(),
        tasks: Map::empty(),
        schedules: Map::empty(),
    }
}

fn initial_server() -> (server: Server)
    ensures
        server@ == empty_server(),
{
    let server = Server {
        promises: super::collections::PMap::empty(),
        tasks: super::collections::PMap::empty(),
        schedules: super::collections::PMap::empty(),
    };
    proof {
        broadcast use group_views;
        assert(server.promises@.map_values(|p: super::exec::Promise| p@) =~= Map::empty());
        assert(server.tasks@.map_values(|t: super::exec::Task| t@) =~= Map::empty());
        assert(server.schedules@.map_values(|s: super::exec::Schedule| s@) =~= Map::empty());
    }
    server
}

pub open spec fn spec_send(
    call: Call,
    response: Response,
    dispatches: Seq<DispatchV>,
) -> Seq<(Pid, Message)> {
    seq![(
        Pid::Outside,
        Message::Output(Output::Response {
            client: call.client,
            id: call.id,
            response,
        }),
    )] + dispatches.map_values(|dispatch: DispatchV| (
        Pid::Outside,
        Message::Output(Output::Dispatch(
            super::spec::lift_dispatch(dispatch),
        )),
    ))
}

pub open spec fn spec_request_outcome(
    before: StateV,
    call: Call,
    outcome: OutV,
) -> StepResultV<StateV, Pid, Message> {
    StepResultV {
        state: StateV {
            server: outcome.next,
            pending: before.pending + outcome.work,
        },
        send: spec_send(call, outcome.resp, outcome.send),
    }
}

fn send(
    call: &Call,
    response: Response,
    mut dispatches: Vec<Dispatch>,
) -> (messages: Vec<(Pid, Message)>)
    ensures
        messages@ == spec_send(*call, response, dispatches@.map_values(|d: Dispatch| d@)),
{
    let ghost all = dispatches@;
    let ghost response_value = response;
    let mut messages = Vec::new();
    let first = (
        Pid::Outside,
        Message::Output(Output::Response {
            client: copy(&call.client),
            id: call.id,
            response,
        }),
    );
    messages.push(first);
    while !dispatches.is_empty()
        invariant
            messages@.len() >= 1,
            messages@[0] == first,
            messages@.len() + dispatches@.len() == 1 + all.len(),
            dispatches@ == all.skip(messages@.len() - 1),
            messages@.skip(1) == all
                .take(messages@.len() - 1)
                .map_values(|dispatch: Dispatch| (
                    Pid::Outside,
                    Message::Output(Output::Dispatch(dispatch)),
                )),
        decreases dispatches.len(),
    {
        let ghost i = messages@.len() as int - 1;
        assert(dispatches@.len() > 0);
        assert(i + dispatches@.len() == all.len());
        assert(0 <= i);
        assert(i < all.len());
        assert(0 <= i < all.len());
        let ghost before = messages@;
        let dispatch = dispatches.remove(0);
        assert(dispatch == all[i]);
        assert(all.skip(i).remove(0) =~= all.skip(i + 1));
        assert(all.take(i + 1) =~= all.take(i).push(all[i]));
        messages.push((
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        ));
        proof {
            assert(messages@ == before.push((
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )));
            assert(messages@.skip(1) == before.skip(1).push((
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )));
            assert(all.take(i + 1).map_values(|dispatch: Dispatch| (
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )) =~= all.take(i).map_values(|dispatch: Dispatch| (
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )).push((
                Pid::Outside,
                Message::Output(Output::Dispatch(all[i])),
            )));
            assert(messages@.skip(1) =~= all
                .take(i + 1)
                .map_values(|dispatch: Dispatch| (
                    Pid::Outside,
                    Message::Output(Output::Dispatch(dispatch)),
                )));
        }
    }
    proof {
        assert(all.take(all.len() as int) =~= all);
        assert(messages@.skip(1) =~= all.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        )));
        assert forall|i: int| 0 <= i < all.len() implies
            super::spec::lift_dispatch(all[i]@) == all[i] by {
            lemma_lift_dispatch(all[i]);
        }
        assert(all.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        )) =~= all.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(
                super::spec::lift_dispatch(dispatch@),
            )),
        )));
        assert(first == (
            Pid::Outside,
            Message::Output(Output::Response {
                client: call.client,
                id: call.id,
                response: response_value,
            }),
        ));
        assert(messages@ =~= seq![messages@[0]] + messages@.skip(1));
        assert(messages@ =~= spec_send(*call, response_value, all.map_values(|d: Dispatch| d@)));
    }
    messages
}

fn append_work(
    pending: &Vec<Work>,
    mut work: Vec<Work>,
) -> (result: Vec<Work>)
    ensures
        result@.map_values(|item: Work| item@)
            == pending@.map_values(|item: Work| item@)
                + work@.map_values(|item: Work| item@),
{
    let mut result = copy(pending);
    result.append(&mut work);
    result
}

fn request_outcome(
    before: &State,
    call: &Call,
    outcome: Out,
) -> (result: StepResult<Model>)
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_request_outcome(before@, *call, outcome@),
{
    let Out {
        resp,
        next,
        work,
        send: dispatches,
        marks: _,
    } = outcome;
    StepResult {
        state: State {
            server: next,
            pending: append_work(&before.pending, work),
        },
        send: send(call, resp, dispatches),
    }
}

fn run_results(
    config: &Resonate,
    state: &State,
    call: &Call,
    now: Time,
) -> (results: Vec<StepResult<Model>>)
{
    let mut outcomes = config.run(&call.request, &state.server, now);
    let ghost all = outcomes@;
    let mut results = Vec::new();
    while !outcomes.is_empty()
        invariant
            outcomes@ == all.skip(results@.len() as int),
            results@.len() + outcomes@.len() == all.len(),
            results@.map_values(|result: StepResult<Model>| StepResultV {
                state: result.state@,
                send: result.send@,
            }) == all.take(results@.len() as int)
                .map_values(|outcome: Out| spec_request_outcome(state@, *call, outcome@)),
        decreases outcomes.len(),
    {
        let ghost i = results@.len() as int;
        let ghost before = results@;
        let ghost actual_before = results@.map_values(|result: StepResult<Model>| StepResultV {
            state: result.state@,
            send: result.send@,
        });
        let outcome = outcomes.remove(0);
        assert(outcome == all[i]);
        assert(all.skip(i).remove(0) =~= all.skip(i + 1));
        assert(all.take(i + 1) =~= all.take(i).push(all[i]));
        results.push(request_outcome(state, call, outcome));
        proof {
            assert(results@ == before.push(results@[i]));
            assert(results@.map_values(|result: StepResult<Model>| StepResultV {
                state: result.state@,
                send: result.send@,
            }) == actual_before.push(StepResultV {
                state: results@[i].state@,
                send: results@[i].send@,
            }));
            assert(all.take(i + 1)
                .map_values(|outcome: Out| spec_request_outcome(state@, *call, outcome@))
                =~= all.take(i)
                    .map_values(|outcome: Out| spec_request_outcome(state@, *call, outcome@))
                    .push(spec_request_outcome(state@, *call, all[i]@)));
            assert(results@.map_values(|result: StepResult<Model>| StepResultV {
                state: result.state@,
                send: result.send@,
            }) =~= all.take(i + 1)
                .map_values(|outcome: Out| spec_request_outcome(state@, *call, outcome@)));
        }
    }
    results
}

pub open spec fn spec_ready(work: Sched<InternalV>, now: Time) -> bool {
    match work {
        Sched::Later(_) => true,
        Sched::Timer(at, _) => at <= now,
    }
}

fn ready(work: &Work, now: Time) -> (is_ready: bool)
    ensures
        is_ready == spec_ready(work@, now),
{
    match work {
        Work::Later(_) => true,
        Work::Timer(at, _) => *at <= now,
    }
}

pub open spec fn remove_at<T>(values: Seq<T>, i: int) -> Seq<T> {
    values.take(i) + values.skip(i + 1)
}

pub open spec fn spec_internal_result(
    before: StateV,
    i: int,
    outcome: InOutV,
) -> StepResultV<StateV, Pid, Message> {
    StepResultV {
        state: StateV {
            server: outcome.next,
            pending: remove_at(before.pending, i) + outcome.work,
        },
        send: outcome.send.map_values(|dispatch: DispatchV| (
            Pid::Outside,
            Message::Output(Output::Dispatch(
                super::spec::lift_dispatch(dispatch),
            )),
        )),
    }
}

fn internal_result(
    before: &State,
    i: usize,
    outcome: InOut,
) -> (result: StepResult<Model>)
    requires
        i < before.pending.len(),
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_internal_result(before@, i as int, outcome@),
{
    let ghost outv = outcome@;
    let InOut {
        next,
        mut work,
        send: mut dispatches,
        marks: _,
        pending: _,
    } = outcome;
    let mut pending = copy(&before.pending);
    pending.remove(i);
    pending.append(&mut work);
    let ghost all = dispatches@;
    let mut send = Vec::new();
    while !dispatches.is_empty()
        invariant
            send@.len() + dispatches@.len() == all.len(),
            dispatches@ == all.skip(send@.len() as int),
            send@ == all.take(send@.len() as int).map_values(|dispatch: Dispatch| (
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )),
        decreases dispatches.len(),
    {
        let ghost j = send@.len() as int;
        let dispatch = dispatches.remove(0);
        assert(dispatch == all[j]);
        assert(all.skip(j).remove(0) =~= all.skip(j + 1));
        assert(all.take(j + 1) =~= all.take(j).push(all[j]));
        send.push((
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        ));
    }
    proof {
        assert(pending@.map_values(|item: Work| item@)
            =~= remove_at(before@.pending, i as int) + outv.work);
        assert(all.take(all.len() as int) =~= all);
        assert forall|j: int| 0 <= j < outv.send.len() implies
            super::spec::lift_dispatch(outv.send[j]) == all[j] by {
            lemma_lift_dispatch(all[j]);
        }
        assert(send@ =~= outv.send.map_values(|dispatch: DispatchV| (
            Pid::Outside,
            Message::Output(Output::Dispatch(
                super::spec::lift_dispatch(dispatch),
            )),
        )));
    }
    StepResult {
        state: State {
            server: next,
            pending,
        },
        send,
    }
}

fn internal_results_from(
    config: &Resonate,
    state: &State,
    now: Time,
    i: usize,
) -> (results: Vec<StepResult<Model>>)
    requires
        i <= state.pending.len(),
    decreases state.pending.len() - i,
{
    if i == state.pending.len() {
        return Vec::new();
    }
    let work = &state.pending[i];
    let outcome = match work {
        Work::Later(step) | Work::Timer(_, step) => config.run_timeout(step, &state.server, now),
    };
    let is_ready = ready(work, now);
    let mut tail = internal_results_from(config, state, now, i + 1);
    if is_ready && !outcome.pending {
        let result = internal_result(state, i, outcome);
        let mut results = Vec::new();
        results.push(result);
        results.append(&mut tail);
        results
    } else {
        tail
    }
}

fn internal_results(
    config: &Resonate,
    state: &State,
    now: Time,
) -> (results: Vec<StepResult<Model>>)
{
    internal_results_from(config, state, now, 0)
}

pub open spec fn spec_idle(state: StateV) -> Seq<StepResultV<StateV, Pid, Message>> {
    seq![StepResultV {
        state,
        send: Seq::empty(),
    }]
}

fn idle(state: &State) -> (results: Vec<StepResult<Model>>)
    ensures
        results@.map_values(|result: StepResult<Model>| StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_idle(state@),
{
    vec![StepResult {
        state: copy(state),
        send: Vec::new(),
    }]
}

impl State {
    fn step(
        &self,
        config: &Resonate,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (results: Vec<StepResult<Model>>) {
        match event {
            ProcessEvent::Receive { sender: Pid::Outside, message: Message::Request(call) } => {
                run_results(config, self, call, now)
            }
            ProcessEvent::Timeout => {
                let results = internal_results(config, self, now);
                if results.is_empty() { idle(self) } else { results }
            }
            _ => idle(self),
        }
    }
}

impl Process<Resonate, Pid, Message> for State {
    fn on_event(
        &self,
        config: &Resonate,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (pairs: Vec<(State, Vec<(Pid, Message)>)>) {
        let mut results = self.step(config, now, event);
        let ghost n = results@.len() as int;
        let mut pairs: Vec<(State, Vec<(Pid, Message)>)> = Vec::new();
        while !results.is_empty()
            invariant
                pairs@.len() + results@.len() == n,
                results@.len() == n - pairs@.len(),
            decreases results@.len(),
        {
            let result = results.remove(0);
            pairs.push((result.state, result.send));
        }
        pairs
    }
}

impl RoverModel for Model {
    type Config = Resonate;
    type Pid = Pid;
    type StateV = StateV;
    type State = State;
    type Message = Message;
    type Boundary = BoundaryEvent;

    fn outside(&self) -> (outside: Pid) {
        Pid::Outside
    }

    fn initial(&self, _config: &Resonate) -> (states: Vec<(Pid, State)>) {
        let server = initial_server();
        let pending: Vec<Work> = Vec::new();
        let state = State {
            server,
            pending,
        };
        proof {
            assert(server@ == empty_server());
            assert(pending@.map_values(|work: Work| work@) =~= Seq::empty());
            assert(state@ == StateV {
                server: empty_server(),
                pending: Seq::empty(),
            });
        }
        let mut states = Vec::new();
        states.push((Pid::Service, state));
        proof {
            assert(states@.map_values(|entry: (Pid, State)| (entry.0, entry.1@))
                =~= seq![(
                    Pid::Service,
                    StateV {
                        server: empty_server(),
                        pending: Seq::empty(),
                    },
                )]);
        }
        states
    }

    fn injectable(&self, _config: &Resonate, message: &Message) -> (injectable: bool) {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    fn on_event(
        &self,
        config: &Resonate,
        pid: &Pid,
        state: &State,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (results: Vec<StepResult<Self>>) {
        match pid {
            Pid::Service => state.step(config, now, event),
            _ => idle(state),
        }
    }

    open spec fn spec_outside(&self) -> Pid {
        Pid::Outside
    }

    open spec fn spec_initial(&self, _config: Resonate) -> Seq<(Pid, StateV)> {
        seq![(
            Pid::Service,
            StateV {
                server: empty_server(),
                pending: Seq::empty(),
            },
        )]
    }

    open spec fn spec_injectable(&self, _config: Resonate, message: Message) -> bool {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    open spec fn spec_observe(
        &self,
        label: Label<Pid, Message>,
    ) -> Seq<BoundaryEvent> {
        match label {
            Label::Input {
                at,
                message: Message::Request(call),
                ..
            } => seq![BoundaryEvent::Input { at, call }],
            Label::Outside {
                at,
                message: Message::Output(output),
                ..
            } => seq![BoundaryEvent::Output { at, output }],
            _ => Seq::empty(),
        }
    }
}

} // verus!
