//! One process. `handler` is one request, `run` puts its reply on the send
//! list, and `process_work` is one work item. A timeout runs one queued
//! occurrence or one step the handler will perform, or it does nothing.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use echod_rover::certificate::trusted::copy;
#[allow(unused_imports)] // specification-only name is erased by ordinary Rust
use echod_rover::rover::spec::{Label, StepResultV};
use echod_rover::rover::comm::ProcessEvent;
use echod_rover::rover::spec::{RoverModel, RoverProc};
use echod_rover::rover::test::{ProcResult, RoverExec, RoverProcExec};
use echod_rover::{Sched, Time};

use echod_types::{Request, Response};

use super::machine::{unavailable, Dispatch, InOut, Out, ServerConfig, Store, Work};
use super::protocol::{BoundaryEvent, Call, Message, Output};
#[cfg(verus_keep_ghost)]
pub use super::machine::spec_unavailable;
#[cfg(verus_keep_ghost)]
use super::machine::{spec_body, spec_handler, spec_process_work, spec_status_res};
#[cfg(verus_keep_ghost)]
use super::view::strs;
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

impl RoverProc for StateV {
    type Config = ServerConfig;
    type Pid = Pid;
    type Message = Message;

    open spec fn on_event(
        self,
        config: ServerConfig,
        now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<StepResultV<StateV, Pid, Message>> {
        spec_service(config, self, now, event)
    }
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

/// The mathematical Resonate Rover model, with no executable state.
pub struct Spec;

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
        assert(server.schedules@.map_values(|s: echod_types::Schedule| super::view::schedule_v(s)) =~= Map::empty());
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

/// The results of a step, as the trait reads them.
pub open spec fn results_v(results: Seq<ProcResult<State>>) -> Seq<StepResultV<StateV, Pid, Message>> {
    results.map_values(|result: ProcResult<State>| StepResultV {
        state: result.state@,
        send: result.send@,
    })
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

pub proof fn lemma_losses_map(before: StateV, call: Call, outcomes: Seq<OutV>)
    ensures
        spec_losses(before, call, outcomes) == outcomes.map_values(|o: OutV| spec_lose(before, call, o)),
    decreases outcomes.len(),
{
    if outcomes.len() == 0 {
        assert(spec_losses(before, call, outcomes) =~= outcomes.map_values(|o: OutV| spec_lose(before, call, o)));
    } else {
        lemma_losses_map(before, call, outcomes.skip(1));
        assert(spec_losses(before, call, outcomes) =~= outcomes.map_values(|o: OutV| spec_lose(before, call, o)));
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
            let outcomes = state.on_event(config, now, event);
            &&& outcomes.len() > 0
            &&& outcomes[outcomes.len() as int - 1] == spec_shed(state, call)
        }),
{
    let event = ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(call),
    };
    let outcomes = state.on_event(config, now, event);
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
            let outcomes = state.on_event(config, now, event);
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
    let outcomes = state.on_event(config, now, event);
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
) -> (result: ProcResult<State>)
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
    ProcResult {
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
) -> (result: ProcResult<State>)
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_lose(before@, *call, outcome@),
{
    let Out {
        resp: _,
        next,
        work,
        send: dispatches,
        marks: _,
    } = outcome;
    ProcResult {
        state: State {
            store: next,
            pending: append_work(&before.pending, work),
        },
        send: send(call, unavailable(&call.request), dispatches),
    }
}

fn shed_outcome(before: &State, call: &Call) -> (result: ProcResult<State>)
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_shed(before@, *call),
{
    let dispatches: Vec<Dispatch> = Vec::new();
    let result = ProcResult {
        state: copy(before),
        send: send(call, unavailable(&call.request), dispatches),
    };
    proof {
        assert(dispatches@.map_values(|d: Dispatch| d@) =~= Seq::<DispatchV>::empty());
    }
    result
}

pub open spec fn spec_request_result(state: StateV, call: Call, lost: bool, o: Out) -> StepResultV<StateV, Pid, Message> {
    if lost { spec_lose(state, call, o@) } else { spec_request_outcome(state, call, o@) }
}

/// `outcomes`, one result each: served, or lost. Every request step is the
/// served outcomes, then the lost ones.
fn request_results(
    state: &State,
    call: &Call,
    mut outcomes: Vec<Out>,
    lost: bool,
) -> (results: Vec<ProcResult<State>>)
    ensures
        results_v(results@) == if lost {
            spec_losses(state@, *call, outcomes@.map_values(|o: Out| o@))
        } else {
            outcomes@.map_values(|o: Out| o@).map_values(|o: OutV| spec_request_outcome(state@, *call, o))
        },
{
    let ghost all = outcomes@;
    let mut results: Vec<ProcResult<State>> = Vec::new();
    while !outcomes.is_empty()
        invariant
            outcomes@ == all.skip(results@.len() as int),
            results@.len() + outcomes@.len() == all.len(),
            results_v(results@) == all.take(results@.len() as int).map_values(|o: Out| spec_request_result(state@, *call, lost, o)),
        decreases outcomes.len(),
    {
        let ghost i = results@.len() as int;
        let ghost before = results@;
        let outcome = outcomes.remove(0);
        assert(outcome == all[i]);
        assert(all.skip(i).remove(0) =~= all.skip(i + 1));
        assert(all.take(i + 1) =~= all.take(i).push(all[i]));
        let result = if lost { lose_outcome(state, call, outcome) } else { request_outcome(state, call, outcome) };
        proof {
            assert((StepResultV { state: result.state@, send: result.send@ }) == spec_request_result(state@, *call, lost, all[i]));
        }
        results.push(result);
        proof {
            assert(results@ == before.push(result));
            assert(results_v(results@).len() == results_v(before).len() + 1);
            assert(results_v(results@)[i] == spec_request_result(state@, *call, lost, all[i]));
            assert forall|j: int| 0 <= j < i implies results_v(results@)[j] == results_v(before)[j] by {}
            assert(results_v(results@) =~= results_v(before).push(spec_request_result(state@, *call, lost, all[i])));
            assert(all.take(i).push(all[i]).map_values(|o: Out| spec_request_result(state@, *call, lost, o)) =~= all.take(i).map_values(|o: Out| spec_request_result(state@, *call, lost, o)).push(spec_request_result(state@, *call, lost, all[i])));
        }
    }
    proof {
        assert(all.take(all.len() as int) =~= all);
        if lost {
            lemma_losses_map(state@, *call, all.map_values(|o: Out| o@));
            assert(all.map_values(|o: Out| spec_request_result(state@, *call, lost, o)) =~= spec_losses(state@, *call, all.map_values(|o: Out| o@)));
        } else {
            assert(all.map_values(|o: Out| spec_request_result(state@, *call, lost, o)) =~= all.map_values(|o: Out| o@).map_values(|o: OutV| spec_request_outcome(state@, *call, o)));
        }
    }
    results
}

fn run(
    config: &ServerConfig,
    state: &State,
    call: &Call,
    now: Time,
) -> (results: Vec<ProcResult<State>>)
    ensures
        results_v(results@) == spec_run(*config, state@, *call, now)
            + spec_losses(state@, *call, spec_handler(*config, call.request, state@.store, now))
            + seq![spec_shed(state@, *call)],
{
    let served = config.handler(&call.request, &state.store, now);
    let mut results = request_results(state, call, served, false);
    let lost = config.handler(&call.request, &state.store, now);
    let mut losses = request_results(state, call, lost, true);
    let ghost served_v = results_v(results@);
    let ghost lost_v = results_v(losses@);
    results.append(&mut losses);
    let shed = shed_outcome(state, call);
    results.push(shed);
    proof {
        assert(results_v(results@) =~= served_v + lost_v + seq![spec_shed(state@, *call)]);
    }
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
) -> (result: ProcResult<State>)
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
    ProcResult {
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
) -> (results: Vec<ProcResult<State>>)
    requires
        i <= state.pending.len(),
    ensures
        results_v(results@) == spec_queue(*config, state@, now, i as int),
    decreases state.pending.len() - i,
{
    if i == state.pending.len() {
        let results: Vec<ProcResult<State>> = Vec::new();
        proof {
            assert(results_v(results@) =~= spec_queue(*config, state@, now, i as int));
        }
        return results;
    }
    let work = &state.pending[i];
    proof {
        assert(state@.pending[i as int] == super::view::as_sched(*work));
        assert(spec_body(super::view::as_sched(*work)) == work@);
    }
    let outcome = config.process_work(work, &state.store, now);
    let is_ready = ready(work, now);
    let mut tail = run_timeout_from(config, state, now, i + 1);
    if is_ready && !outcome.not_due {
        let result = internal_result(state, i, outcome);
        let mut results = Vec::new();
        results.push(result);
        let ghost tail_v = results_v(tail@);
        results.append(&mut tail);
        proof {
            assert(results_v(results@) =~= seq![spec_internal_result(state@, i as int, outcome@)] + tail_v);
        }
        results
    } else {
        tail
    }
}

fn due_result(before: &State, outcome: InOut) -> (result: ProcResult<State>)
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_due_result(before@, outcome@),
{
    let ghost outv = outcome@;
    let InOut { next, mut work, send: mut dispatches, marks: _, not_due: _ } = outcome;
    let mut pending = copy(&before.pending);
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
        send.push((Pid::Outside, Message::Output(Output::Dispatch(dispatch))));
    }
    proof {
        assert(pending@.map_values(|item: Work| super::view::as_sched(item)) =~= before@.pending + outv.work);
        assert(all.take(all.len() as int) =~= all);
        assert forall|j: int| 0 <= j < outv.send.len() implies lift_dispatch(outv.send[j]) == all[j] by {
            lemma_lift_dispatch(all[j]);
        }
        assert(send@ =~= outv.send.map_values(|dispatch: DispatchV| (
            Pid::Outside,
            Message::Output(Output::Dispatch(lift_dispatch(dispatch))),
        )));
    }
    ProcResult { state: State { store: next, pending }, send }
}

/// One derived step, kept when its handler would do something: `spec_keep`.
fn keep(config: &ServerConfig, state: &State, now: Time, work: Work) -> (results: Vec<ProcResult<State>>)
    ensures
        results_v(results@) == spec_keep(*config, state@, now, work@, Seq::empty()),
{
    let outcome = config.process_work(&work, &state.store, now);
    let mut results: Vec<ProcResult<State>> = Vec::new();
    if !outcome.not_due {
        results.push(due_result(state, outcome));
    }
    proof {
        assert(results_v(results@) =~= spec_keep(*config, state@, now, work@, Seq::empty()));
    }
    results
}

fn over_callbacks(
    config: &ServerConfig,
    state: &State,
    now: Time,
    awaited: &String,
    awaiters: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcResult<State>>)
    requires
        i <= awaiters.len(),
    ensures
        results_v(results@) == spec_over_callbacks(*config, state@, now, awaited@, strs(awaiters@).skip(i as int)),
    decreases awaiters.len() - i,
{
    broadcast use super::view::group_views;
    if i == awaiters.len() {
        let results: Vec<ProcResult<State>> = Vec::new();
        proof {
            assert(strs(awaiters@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let awaiter = copy(&awaiters[i]);
    let mut results = keep(config, state, now, Work::Callback { awaited: copy(awaited), awaiter });
    let ghost head = results_v(results@);
    let mut rest = over_callbacks(config, state, now, awaited, awaiters, i + 1);
    let ghost tail = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(strs(awaiters@).skip(i as int).drop_first() =~= strs(awaiters@).skip(i as int + 1));
        assert(strs(awaiters@).skip(i as int)[0] == awaiters@[i as int]@);
        assert(results_v(results@) =~= head + tail);
    }
    results
}

fn over_listeners(
    config: &ServerConfig,
    state: &State,
    now: Time,
    awaited: &String,
    addresses: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcResult<State>>)
    requires
        i <= addresses.len(),
    ensures
        results_v(results@) == spec_over_listeners(*config, state@, now, awaited@, strs(addresses@).skip(i as int)),
    decreases addresses.len() - i,
{
    broadcast use super::view::group_views;
    if i == addresses.len() {
        let results: Vec<ProcResult<State>> = Vec::new();
        proof {
            assert(strs(addresses@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let address = copy(&addresses[i]);
    let mut results = keep(config, state, now, Work::Listener { awaited: copy(awaited), address });
    let ghost head = results_v(results@);
    let mut rest = over_listeners(config, state, now, awaited, addresses, i + 1);
    let ghost tail = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(strs(addresses@).skip(i as int).drop_first() =~= strs(addresses@).skip(i as int + 1));
        assert(strs(addresses@).skip(i as int)[0] == addresses@[i as int]@);
        assert(results_v(results@) =~= head + tail);
    }
    results
}

fn over_promises(
    config: &ServerConfig,
    state: &State,
    now: Time,
    keys: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcResult<State>>)
    requires
        i <= keys.len(),
        forall|j: int| 0 <= j < keys.len() ==> state.store.promises@.contains_key(#[trigger] keys[j]@),
    ensures
        results_v(results@) == spec_over_promises(*config, state@, now, strs(keys@).skip(i as int)),
    decreases keys.len() - i,
{
    broadcast use super::view::group_views;
    if i == keys.len() {
        let results: Vec<ProcResult<State>> = Vec::new();
        proof {
            assert(strs(keys@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let id = &keys[i];
    let p = match state.store.promises.get(id) {
        Some(p) => p,
        None => {
            proof {
                assert(false);
            }
            vstd::pervasive::unreached()
        }
    };
    let mut results = keep(config, state, now, Work::PromiseTimeout(copy(id)));
    let ghost a = results_v(results@);
    let callbacks = p.callbacks.to_vec();
    let mut over_cb = over_callbacks(config, state, now, id, &callbacks, 0);
    let ghost b = results_v(over_cb@);
    let listeners = p.listeners.to_vec();
    let mut over_ls = over_listeners(config, state, now, id, &listeners, 0);
    let ghost c = results_v(over_ls@);
    let mut rest = over_promises(config, state, now, keys, i + 1);
    let ghost d = results_v(rest@);
    results.append(&mut over_cb);
    results.append(&mut over_ls);
    results.append(&mut rest);
    proof {
        assert(strs(keys@).skip(i as int).drop_first() =~= strs(keys@).skip(i as int + 1));
        assert(strs(keys@).skip(i as int)[0] == id@);
        assert(strs(callbacks@).skip(0) =~= pset_seq(p@.callbacks));
        assert(strs(listeners@).skip(0) =~= pset_seq(p@.listeners));
        assert(state@.store.promises[id@] == p@);
        assert(results_v(results@) =~= a + b + c + d);
    }
    results
}

fn over_tasks(
    config: &ServerConfig,
    state: &State,
    now: Time,
    keys: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcResult<State>>)
    requires
        i <= keys.len(),
        forall|j: int| 0 <= j < keys.len() ==> state.store.tasks@.contains_key(#[trigger] keys[j]@),
    ensures
        results_v(results@) == spec_over_tasks(*config, state@, now, strs(keys@).skip(i as int)),
    decreases keys.len() - i,
{
    broadcast use super::view::group_views;
    if i == keys.len() {
        let results: Vec<ProcResult<State>> = Vec::new();
        proof {
            assert(strs(keys@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let id = &keys[i];
    let t = match state.store.tasks.get(id) {
        Some(t) => t,
        None => {
            proof {
                assert(false);
            }
            vstd::pervasive::unreached()
        }
    };
    let mut results = keep(config, state, now, Work::TaskLeaseTimeout(copy(id)));
    let ghost lease = results_v(results@);
    let ghost retry: Seq<StepResultV<StateV, Pid, Message>>;
    match t.retry_timeout_at {
        Some(_) => {
            let mut again = keep(config, state, now, Work::TaskRetryTimeout(copy(id)));
            proof {
                retry = results_v(again@);
            }
            results.append(&mut again);
        }
        None => {
            proof {
                retry = Seq::empty();
            }
        }
    }
    let ghost sofar = results_v(results@);
    let mut rest = over_tasks(config, state, now, keys, i + 1);
    let ghost d = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(strs(keys@).skip(i as int).drop_first() =~= strs(keys@).skip(i as int + 1));
        assert(strs(keys@).skip(i as int)[0] == id@);
        assert(state@.store.tasks[id@] == t@);
        assert(sofar =~= lease + retry);
        assert(results_v(results@) =~= lease + retry + d);
    }
    results
}

fn over_schedules(
    config: &ServerConfig,
    state: &State,
    now: Time,
    keys: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcResult<State>>)
    requires
        i <= keys.len(),
        forall|j: int| 0 <= j < keys.len() ==> state.store.schedules@.contains_key(#[trigger] keys[j]@),
    ensures
        results_v(results@) == spec_over_schedules(*config, state@, now, strs(keys@).skip(i as int)),
    decreases keys.len() - i,
{
    broadcast use super::view::group_views;
    if i == keys.len() {
        let results: Vec<ProcResult<State>> = Vec::new();
        proof {
            assert(strs(keys@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let id = &keys[i];
    let c = match state.store.schedules.get(id) {
        Some(c) => c,
        None => {
            proof {
                assert(false);
            }
            vstd::pervasive::unreached()
        }
    };
    let promise = super::trusted::expand(&c.promise_id, id, c.next_run_at);
    let mut results = keep(config, state, now, Work::ScheduleTimeout { id: copy(id), promise });
    let ghost head = results_v(results@);
    let mut rest = over_schedules(config, state, now, keys, i + 1);
    let ghost tail = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(strs(keys@).skip(i as int).drop_first() =~= strs(keys@).skip(i as int + 1));
        assert(strs(keys@).skip(i as int)[0] == id@);
        assert(state@.store.schedules[id@] == super::view::schedule_v(*c));
        assert(results_v(results@) =~= head + tail);
    }
    results
}

/// The steps the three maps offer, in the order the specification walks
/// them: `spec_derived`.
fn derived(config: &ServerConfig, state: &State, now: Time) -> (results: Vec<ProcResult<State>>)
    ensures
        results_v(results@) == spec_derived(*config, state@, now),
{
    broadcast use super::view::group_views;
    let promises = state.store.promises.keys();
    let tasks = state.store.tasks.keys();
    let schedules = state.store.schedules.keys();
    let mut results = over_promises(config, state, now, &promises, 0);
    let ghost a = results_v(results@);
    let mut over_t = over_tasks(config, state, now, &tasks, 0);
    let ghost b = results_v(over_t@);
    let mut over_s = over_schedules(config, state, now, &schedules, 0);
    let ghost c = results_v(over_s@);
    results.append(&mut over_t);
    results.append(&mut over_s);
    proof {
        assert(strs(promises@).skip(0) =~= spec_keys(state@.store.promises));
        assert(strs(tasks@).skip(0) =~= spec_keys(state@.store.tasks));
        assert(strs(schedules@).skip(0) =~= spec_keys(state@.store.schedules));
        assert(results_v(results@) =~= a + b + c);
    }
    results
}

fn run_timeout(
    config: &ServerConfig,
    state: &State,
    now: Time,
) -> (results: Vec<ProcResult<State>>)
    ensures
        results_v(results@) == spec_run_timeout(*config, state@, now),
{
    let mut results = run_timeout_from(config, state, now, 0);
    let ghost queued = results_v(results@);
    let mut rest = derived(config, state, now);
    let ghost rest_v = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(results_v(results@) =~= queued + rest_v);
    }
    results
}

pub open spec fn spec_idle(state: StateV) -> Seq<StepResultV<StateV, Pid, Message>> {
    seq![StepResultV {
        state,
        send: Seq::empty(),
    }]
}

fn idle(state: &State) -> (results: Vec<ProcResult<State>>)
    ensures
        results_v(results@) == spec_idle(state@),
{
    let mut results: Vec<ProcResult<State>> = Vec::new();
    results.push(ProcResult {
        state: copy(state),
        send: Vec::new(),
    });
    proof {
        assert(results_v(results@) =~= spec_idle(state@));
    }
    results
}

impl State {
    /// One event at the service: `spec_service`.
    fn step(
        &self,
        config: &ServerConfig,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (results: Vec<ProcResult<State>>)
        ensures
            results_v(results@) == spec_service(*config, self@, now, *event),
    {
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

impl RoverProcExec for State {
    type Spec = StateV;

    fn on_event(
        &self,
        config: &ServerConfig,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (results: Vec<ProcResult<Self>>) {
        let results = self.step(config, now, event);
        proof {
            assert(results_v(results@) == self@.on_event(*config, now, *event));
        }
        results
    }
}

impl RoverExec for Model {
    type Model = Spec;
    type Proc = State;

    open spec fn model(&self) -> Spec {
        Spec
    }

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

}

impl RoverModel for Spec {
    type Config = ServerConfig;
    type Pid = Pid;
    type Proc = StateV;
    type Message = Message;
    type Boundary = BoundaryEvent;

    open spec fn outside(&self) -> Pid {
        Pid::Outside
    }

    open spec fn processes(&self, _config: ServerConfig) -> Seq<(Pid, StateV)> {
        seq![(
            Pid::Service,
            StateV {
                store: empty_store(),
                pending: Seq::empty(),
            },
        )]
    }

    open spec fn injectable(&self, _config: ServerConfig, message: Message) -> bool {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    open spec fn observe(
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
// The process step as a specification. `StateV::on_event` calls
// `spec_service`. A request is served, lost, or shed, the
// three outcomes of the Lean step. A timeout is one ready queued occurrence, or
// one step derived from the three maps. Anything else leaves the state as it
// was. `RoverProcExec::on_event` proves that its executable results have exactly
// the views in this sequence.
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

} // verus!
