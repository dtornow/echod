//! One process. `handler` is one request, `run` puts its reply on the send
//! list, and `process_work` is one work item. A timeout runs one queued
//! occurrence or one step the handler will perform, or it does nothing.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use echod_rover::certificate::trusted::copy;
#[allow(unused_imports)] // specification-only name is erased by ordinary Rust
use echod_rover::rover::semantics::{Label, StepResultV};
use echod_rover::rover::{Process, ProcessEvent, RoverModel, StepResult};
use echod_rover::{Sched, Time};

use echod_types::{Request, Response};

use super::machine::{unavailable, Dispatch, InOut, Out, ServerConfig, Store, Work};
use super::protocol::{BoundaryEvent, Call, Message, Output};
#[cfg(verus_keep_ghost)]
use super::machine::{
    spec_body, spec_claim_res, spec_fence_res, spec_handler, spec_process_work, spec_promise_res,
    spec_schedule_res, spec_status_res, spec_task_get_res,
};
#[cfg(verus_keep_ghost)]
use super::trusted::{pset_seq, spec_expand};
#[cfg(verus_keep_ghost)]
use super::view::{group_views, lemma_lift_dispatch, lift_dispatch, spec_keys, DispatchV, InOutV, OutV};
use super::view::{InternalV, StoreV};

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum Pid {
    Outside,
    Service,
}

#[derive(Clone, PartialEq, Eq, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct State {
    pub store: Store,
    pub pending: Vec<Work>,
}

pub struct StateV {
    pub store: StoreV,
    pub pending: Seq<Sched<InternalV>>,
}

impl View for State {
    type V = StateV;

    open spec fn view(&self) -> StateV {
        StateV {
            store: self.store@,
            pending: self.pending@.map_values(|work: Work| super::view::as_sched(work)),
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Model;

pub open spec fn empty_store() -> StoreV {
    StoreV {
        promises: Map::empty(),
        tasks: Map::empty(),
        schedules: Map::empty(),
    }
}

fn initial_store() -> (server: Store)
    ensures
        server@ == empty_store(),
{
    let server = Store {
        promises: super::trusted::PMap::empty(),
        tasks: super::trusted::PMap::empty(),
        schedules: super::trusted::PMap::empty(),
    };
    proof {
        broadcast use group_views;
        assert(server.promises@.map_values(|p: super::machine::Promise| p@) =~= Map::empty());
        assert(server.tasks@.map_values(|t: super::machine::Task| t@) =~= Map::empty());
        assert(server.schedules@.map_values(|s: echod_types::Schedule| s@) =~= Map::empty());
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
            super::view::lift_dispatch(dispatch),
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
            store: outcome.next,
            pending: before.pending + outcome.work,
        },
        send: spec_send(call, outcome.resp, outcome.send),
    }
}

/// Lean's `runShed`: the state stays, and the client is told 503.
pub open spec fn spec_shed(before: StateV, call: Call) -> StepResultV<StateV, Pid, Message> {
    StepResultV {
        state: before,
        send: spec_send(call, spec_unavailable(call.request), Seq::empty()),
    }
}

/// Lean's `runLose`: the handler runs, and the client is told 503. Dispatches
/// the handler emitted are still sent.
pub open spec fn spec_lose(
    before: StateV,
    call: Call,
    outcome: OutV,
) -> StepResultV<StateV, Pid, Message> {
    StepResultV {
        state: StateV {
            store: outcome.next,
            pending: before.pending + outcome.work,
        },
        send: spec_send(call, spec_unavailable(call.request), outcome.send),
    }
}

pub open spec fn spec_losses(
    before: StateV,
    call: Call,
    outcomes: Seq<OutV>,
) -> Seq<StepResultV<StateV, Pid, Message>>
    decreases outcomes.len(),
{
    if outcomes.len() == 0 {
        Seq::empty()
    } else {
        seq![spec_lose(before, call, outcomes[0])] + spec_losses(before, call, outcomes.skip(1))
    }
}

/// A request's results end with the shed outcome.
pub proof fn lemma_shed_is_last(
    config: ServerConfig,
    state: StateV,
    now: Time,
    call: Call,
)
    ensures
        ({
            let event = ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            };
            let outcomes = Model.spec_on_event(config, Pid::Service, state, now, event);
            &&& outcomes.len() > 0
            &&& outcomes[outcomes.len() as int - 1] == spec_shed(state, call)
        }),
{
    let event = ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(call),
    };
    let outcomes = Model.spec_on_event(config, Pid::Service, state, now, event);
    let served = spec_run(config, state, call, now);
    let lost = spec_losses(state, call, spec_handler(config, call.request, state.store, now));
    let shed = seq![spec_shed(state, call)];
    assert(outcomes == served + lost + shed);
    let prefix = served + lost;
    vstd::seq::lemma_seq_add_len(prefix, shed);
    vstd::seq::lemma_seq_push_len(Seq::<StepResultV<StateV, Pid, Message>>::empty(), spec_shed(state, call));
    assert(shed.len() == 1);
    let j = prefix.len() as int;
    vstd::seq::lemma_seq_add_index2(prefix, shed, j);
    vstd::seq::lemma_seq_push_index_same(
        Seq::<StepResultV<StateV, Pid, Message>>::empty(),
        spec_shed(state, call),
        0,
    );
    assert(shed[0] == spec_shed(state, call));
    assert(outcomes[j] == spec_shed(state, call));
    assert(j == outcomes.len() as int - 1);
}

/// An empty-task heartbeat is served as 200 and leaves the state in place.
/// That result is the first request outcome.
pub proof fn lemma_empty_heartbeat_is_first(
    config: ServerConfig,
    state: StateV,
    now: Time,
    call: Call,
)
    requires
        match call.request {
            Request::TaskHeartbeat(q) => q.tasks@.len() == 0,
            _ => false,
        },
    ensures
        ({
            let event = ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            };
            let outcomes = Model.spec_on_event(config, Pid::Service, state, now, event);
            &&& outcomes.len() > 0
            &&& outcomes[0].state == state
            &&& outcomes[0].send == spec_send(
                call,
                Response::Status(echod_types::StatusRes { status: 200 }),
                Seq::empty(),
            )
        }),
{
    let event = ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(call),
    };
    let outcomes = Model.spec_on_event(config, Pid::Service, state, now, event);
    let handler = spec_handler(config, call.request, state.store, now);
    assert(handler.len() == 1);
    let outcome = handler[0];
    assert(outcome.resp == spec_status_res(200));
    assert(spec_status_res(200) == Response::Status(echod_types::StatusRes { status: 200 }));
    assert(outcome.work =~= Seq::empty());
    assert(outcome.send =~= Seq::empty());
    assert(outcome.next == state.store);
    let served = spec_run(config, state, call, now);
    assert(served.len() == 1);
    assert(served[0] == spec_request_outcome(state, call, outcome));
    assert(served[0].state == state);
    assert(served[0].send == spec_send(
        call,
        Response::Status(echod_types::StatusRes { status: 200 }),
        Seq::empty(),
    ));
    let lost = spec_losses(state, call, handler);
    let shed = seq![spec_shed(state, call)];
    assert(outcomes == served + lost + shed);
    vstd::seq::lemma_seq_add_index1(served, lost + shed, 0);
    assert(outcomes[0] == served[0]);
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
            super::view::lift_dispatch(all[i]@) == all[i] by {
            lemma_lift_dispatch(all[i]);
        }
        assert(all.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        )) =~= all.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(
                super::view::lift_dispatch(dispatch@),
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
        result@.map_values(|item: Work| super::view::as_sched(item))
            == pending@.map_values(|item: Work| super::view::as_sched(item))
                + work@.map_values(|item: Work| super::view::as_sched(item)),
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
            store: next,
            pending: append_work(&before.pending, work),
        },
        send: send(call, resp, dispatches),
    }
}

fn lose_outcome(
    before: &State,
    call: &Call,
    outcome: Out,
) -> (result: StepResult<Model>) {
    let Out {
        resp: _,
        next,
        work,
        send: dispatches,
        marks: _,
    } = outcome;
    StepResult {
        state: State {
            store: next,
            pending: append_work(&before.pending, work),
        },
        send: send(call, unavailable(&call.request), dispatches),
    }
}

fn shed_outcome(before: &State, call: &Call) -> (result: StepResult<Model>) {
    StepResult {
        state: copy(before),
        send: send(call, unavailable(&call.request), Vec::new()),
    }
}

fn run(
    config: &ServerConfig,
    state: &State,
    call: &Call,
    now: Time,
) -> (results: Vec<StepResult<Model>>)
{
    let mut outcomes = config.handler(&call.request, &state.store, now);
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
    let mut lost = config.handler(&call.request, &state.store, now);
    while !lost.is_empty()
        decreases lost.len(),
    {
        let outcome = lost.remove(0);
        results.push(lose_outcome(state, call, outcome));
    }
    results.push(shed_outcome(state, call));
    results
}

pub open spec fn spec_ready(work: InternalV, now: Time) -> bool {
    match work {
        InternalV::Occurrence { at, .. } => at <= now,
        _ => false,
    }
}

fn ready(work: &Work, now: Time) -> (is_ready: bool)
    ensures
        is_ready == spec_ready(work@, now),
{
    match work {
        Work::Occurrence { at, .. } => *at <= now,
        _ => false,
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
            store: outcome.next,
            pending: remove_at(before.pending, i) + outcome.work,
        },
        send: outcome.send.map_values(|dispatch: DispatchV| (
            Pid::Outside,
            Message::Output(Output::Dispatch(
                super::view::lift_dispatch(dispatch),
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
        not_due: _,
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
        assert(pending@.map_values(|item: Work| super::view::as_sched(item))
            =~= remove_at(before@.pending, i as int) + outv.work);
        assert(all.take(all.len() as int) =~= all);
        assert forall|j: int| 0 <= j < outv.send.len() implies
            super::view::lift_dispatch(outv.send[j]) == all[j] by {
            lemma_lift_dispatch(all[j]);
        }
        assert(send@ =~= outv.send.map_values(|dispatch: DispatchV| (
            Pid::Outside,
            Message::Output(Output::Dispatch(
                super::view::lift_dispatch(dispatch),
            )),
        )));
    }
    StepResult {
        state: State {
            store: next,
            pending,
        },
        send,
    }
}

fn run_timeout_from(
    config: &ServerConfig,
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
    let outcome = config.process_work(work, &state.store, now);
    let is_ready = ready(work, now);
    let mut tail = run_timeout_from(config, state, now, i + 1);
    if is_ready && !outcome.not_due {
        let result = internal_result(state, i, outcome);
        let mut results = Vec::new();
        results.push(result);
        results.append(&mut tail);
        results
    } else {
        tail
    }
}

fn due_result(before: &State, outcome: InOut) -> (result: StepResult<Model>) {
    let InOut { next, mut work, send: mut dispatches, marks: _, not_due: _ } = outcome;
    let mut pending = copy(&before.pending);
    pending.append(&mut work);
    let ghost all = dispatches@;
    let mut send = Vec::new();
    while !dispatches.is_empty()
        invariant
            send@.len() + dispatches@.len() == all.len(),
            dispatches@ == all.skip(send@.len() as int),
        decreases dispatches.len(),
    {
        let dispatch = dispatches.remove(0);
        send.push((Pid::Outside, Message::Output(Output::Dispatch(dispatch))));
    }
    StepResult { state: State { store: next, pending }, send }
}

fn run_timeout(
    config: &ServerConfig,
    state: &State,
    now: Time,
) -> (results: Vec<StepResult<Model>>)
{
    let mut results = run_timeout_from(config, state, now, 0);
    let due = super::footprint::timeout_work(config, &state.store, now);
    let n = due.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            due.len() == n,
        decreases n - i,
    {
        let outcome = config.process_work(due[i].req(), &state.store, now);
        if !outcome.not_due {
            results.push(due_result(state, outcome));
        }
        i += 1;
    }
    results
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
        config: &ServerConfig,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (results: Vec<StepResult<Model>>) {
        match event {
            ProcessEvent::Receive { sender: Pid::Outside, message: Message::Request(call) } => {
                run(config, self, call, now)
            }
            ProcessEvent::Timeout => {
                let results = run_timeout(config, self, now);
                if results.is_empty() { idle(self) } else { results }
            }
            _ => idle(self),
        }
    }
}

impl Process<ServerConfig, Pid, Message> for State {
    fn on_event(
        &self,
        config: &ServerConfig,
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
    type Config = ServerConfig;
    type Pid = Pid;
    type StateV = StateV;
    type State = State;
    type Message = Message;
    type Boundary = BoundaryEvent;

    fn outside(&self) -> (outside: Pid) {
        Pid::Outside
    }

    fn initial(&self, _config: &ServerConfig) -> (states: Vec<(Pid, State)>) {
        let server = initial_store();
        let pending: Vec<Work> = Vec::new();
        let state = State {
            store: server,
            pending,
        };
        proof {
            assert(server@ == empty_store());
            assert(pending@.map_values(|work: Work| super::view::as_sched(work)) =~= Seq::empty());
            assert(state@ == StateV {
                store: empty_store(),
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
                        store: empty_store(),
                        pending: Seq::empty(),
                    },
                )]);
        }
        states
    }

    fn injectable(&self, _config: &ServerConfig, message: &Message) -> (injectable: bool) {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    fn on_event(
        &self,
        config: &ServerConfig,
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

    open spec fn spec_initial(&self, _config: ServerConfig) -> Seq<(Pid, StateV)> {
        seq![(
            Pid::Service,
            StateV {
                store: empty_store(),
                pending: Seq::empty(),
            },
        )]
    }

    open spec fn spec_injectable(&self, _config: ServerConfig, message: Message) -> bool {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    /// One local step. `spec_step` is that transition. The `ensures` on
    /// `on_event` is the equality of the executable results with this function;
    /// that proof is not written yet.
    open spec fn spec_on_event(
        &self,
        config: ServerConfig,
        pid: Pid,
        state: StateV,
        now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<StepResultV<StateV, Pid, Message>> {
        spec_step(config, pid, state, now, event)
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

// ---------------------------------------------------------------------------
// The step, as a specification. `spec_step` is what
// `RoverModel::spec_on_event` returns. A request is served, lost, or shed, the
// three outcomes of the Lean step. A timeout is one ready queued occurrence, or
// one step derived from the three maps. Anything else leaves the state as it
// was. The executable `on_event` is obliged, by the trait, to return results
// whose views are exactly this sequence. That equality is not proved here.
// ---------------------------------------------------------------------------

pub open spec fn spec_run(config: ServerConfig, state: StateV, call: Call, now: Time) -> Seq<StepResultV<StateV, Pid, Message>> {
    spec_handler(config, call.request, state.store, now).map_values(|outcome: OutV|
        spec_request_outcome(state, call, outcome)
    )
}

pub open spec fn spec_due_result(before: StateV, outcome: InOutV) -> StepResultV<StateV, Pid, Message> {
    StepResultV {
        state: StateV { store: outcome.next, pending: before.pending + outcome.work },
        send: outcome.send.map_values(|dispatch: DispatchV| (
            Pid::Outside,
            Message::Output(Output::Dispatch(lift_dispatch(dispatch))),
        )),
    }
}

pub open spec fn spec_queue(config: ServerConfig, state: StateV, now: Time, i: int) -> Seq<StepResultV<StateV, Pid, Message>>
    decreases state.pending.len() - i,
{
    if i < 0 || i >= state.pending.len() {
        Seq::empty()
    } else {
        let work = spec_body(state.pending[i]);
        let outcome = spec_process_work(config, work, state.store, now);
        let tail = spec_queue(config, state, now, i + 1);
        if spec_ready(work, now) && !outcome.not_due {
            seq![spec_internal_result(state, i, outcome)] + tail
        } else {
            tail
        }
    }
}

pub open spec fn spec_keep(config: ServerConfig, state: StateV, now: Time, work: InternalV, rest: Seq<StepResultV<StateV, Pid, Message>>) -> Seq<StepResultV<StateV, Pid, Message>> {
    let outcome = spec_process_work(config, work, state.store, now);
    if outcome.not_due {
        rest
    } else {
        seq![spec_due_result(state, outcome)] + rest
    }
}

pub open spec fn spec_over_callbacks(
    config: ServerConfig,
    state: StateV,
    now: Time,
    awaited: Seq<char>,
    awaiters: Seq<Seq<char>>,
) -> Seq<StepResultV<StateV, Pid, Message>>
    decreases awaiters.len(),
{
    if awaiters.len() == 0 {
        Seq::empty()
    } else {
        spec_keep(
            config,
            state,
            now,
            InternalV::Callback { awaited, awaiter: awaiters[0] },
            Seq::empty(),
        ) + spec_over_callbacks(config, state, now, awaited, awaiters.drop_first())
    }
}

pub open spec fn spec_over_listeners(
    config: ServerConfig,
    state: StateV,
    now: Time,
    awaited: Seq<char>,
    addresses: Seq<Seq<char>>,
) -> Seq<StepResultV<StateV, Pid, Message>>
    decreases addresses.len(),
{
    if addresses.len() == 0 {
        Seq::empty()
    } else {
        spec_keep(
            config,
            state,
            now,
            InternalV::Listener { awaited, address: addresses[0] },
            Seq::empty(),
        ) + spec_over_listeners(config, state, now, awaited, addresses.drop_first())
    }
}

pub open spec fn spec_over_promises(config: ServerConfig, state: StateV, now: Time, keys: Seq<Seq<char>>) -> Seq<StepResultV<StateV, Pid, Message>>
    decreases keys.len(),
{
    if keys.len() == 0 {
        Seq::empty()
    } else {
        let id = keys[0];
        let p = state.store.promises[id];
        spec_keep(config, state, now, InternalV::PromiseTimeout(id), Seq::empty())
            + spec_over_callbacks(config, state, now, id, pset_seq(p.callbacks))
            + spec_over_listeners(config, state, now, id, pset_seq(p.listeners))
            + spec_over_promises(config, state, now, keys.drop_first())
    }
}

pub open spec fn spec_over_tasks(config: ServerConfig, state: StateV, now: Time, keys: Seq<Seq<char>>) -> Seq<StepResultV<StateV, Pid, Message>>
    decreases keys.len(),
{
    if keys.len() == 0 {
        Seq::empty()
    } else {
        let id = keys[0];
        let t = state.store.tasks[id];
        let lease = spec_keep(config, state, now, InternalV::TaskLeaseTimeout(id), Seq::empty());
        let retry = match t.retry_timeout_at {
            Some(_) => spec_keep(config, state, now, InternalV::TaskRetryTimeout(id), Seq::empty()),
            None => Seq::empty(),
        };
        lease + retry + spec_over_tasks(config, state, now, keys.drop_first())
    }
}

pub open spec fn spec_over_schedules(config: ServerConfig, state: StateV, now: Time, keys: Seq<Seq<char>>) -> Seq<StepResultV<StateV, Pid, Message>>
    decreases keys.len(),
{
    if keys.len() == 0 {
        Seq::empty()
    } else {
        let id = keys[0];
        let c = state.store.schedules[id];
        let promise = spec_expand(c.promise_id, id, c.next_run_at);
        spec_keep(config, state, now, InternalV::ScheduleTimeout { id, promise }, Seq::empty())
            + spec_over_schedules(config, state, now, keys.drop_first())
    }
}

pub open spec fn spec_derived(config: ServerConfig, state: StateV, now: Time) -> Seq<StepResultV<StateV, Pid, Message>> {
    spec_over_promises(config, state, now, spec_keys(state.store.promises))
        + spec_over_tasks(config, state, now, spec_keys(state.store.tasks))
        + spec_over_schedules(config, state, now, spec_keys(state.store.schedules))
}

pub open spec fn spec_run_timeout(config: ServerConfig, state: StateV, now: Time) -> Seq<StepResultV<StateV, Pid, Message>> {
    spec_queue(config, state, now, 0) + spec_derived(config, state, now)
}

/// 503, shaped like the concrete node's `spec_unavailable`.
pub open spec fn spec_unavailable(request: Request) -> Response {
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => {
            spec_promise_res(503, None)
        },
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => spec_schedule_res(503, None),
        Request::ScheduleDelete(_) | Request::TaskRelease(_) | Request::TaskHalt(_)
        | Request::TaskContinue(_) | Request::TaskHeartbeat(_) | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => spec_status_res(503),
        Request::TaskGet(_) => spec_task_get_res(503, None),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => spec_claim_res(503, None, None),
        Request::TaskFulfill(_) => spec_promise_res(503, None),
        Request::TaskFence(_) => spec_fence_res(503, None),
    }
}

pub open spec fn spec_service(config: ServerConfig, state: StateV, now: Time, event: ProcessEvent<Pid, Message>) -> Seq<StepResultV<StateV, Pid, Message>> {
    match event {
        ProcessEvent::Receive { sender: Pid::Outside, message: Message::Request(call) } => {
            let outcomes = spec_handler(config, call.request, state.store, now);
            spec_run(config, state, call, now) + spec_losses(state, call, outcomes) + seq![spec_shed(
                state,
                call,
            )]
        },
        ProcessEvent::Timeout => {
            let results = spec_run_timeout(config, state, now);
            if results.len() == 0 { spec_idle(state) } else { results }
        },
        _ => spec_idle(state),
    }
}

/// The results of one event at `pid`. A service runs the step. Any other
/// process leaves its state and sends nothing.
pub open spec fn spec_step(
    config: ServerConfig,
    pid: Pid,
    state: StateV,
    now: Time,
    event: ProcessEvent<Pid, Message>,
) -> Seq<StepResultV<StateV, Pid, Message>> {
    match pid {
        Pid::Service => spec_service(config, state, now, event),
        Pid::Outside => spec_idle(state),
    }
}

} // verus!
