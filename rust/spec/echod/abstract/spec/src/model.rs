//! Mathematical Echod abstract process.
//! The executable `echod_abstract_exec::Proc::on_event` realization lives in
//! `echod-abstract-exec`.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]
use vstd::prelude::*;
use rover_spec::rover::comm::{ProcessEvent, Sched, Time};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
use echod_types::{Request, Response};
use super::machine::*;
use super::protocol::{BoundaryEvent, Call, Message, Output};
#[cfg(verus_keep_ghost)]
use super::trusted::{pset_seq, spec_expand};
use super::view::*;

verus! {
#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum Pid {
    Outside,
    Service,
}

pub struct Proc {
    pub store: StoreV,
    pub pending: Seq<Sched<InternalV>>,
}

impl RoverSpec::Proc for Proc {
    type Config = ServerConfig;
    type Pid = Pid;
    type Message = Message;

    open spec fn on_event(
        self,
        config: ServerConfig,
        now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<StepResultV<Proc, Pid, Message>> {
        spec_service(config, self, now, event)
    }
}

/// The mathematical Echod abstract model, with no executable state.
pub struct Spec;

pub open spec fn empty_store() -> StoreV {
    StoreV {
        promises: Map::empty(),
        tasks: Map::empty(),
        schedules: Map::empty(),
    }
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
    before: Proc,
    call: Call,
    outcome: OutV,
) -> StepResultV<Proc, Pid, Message> {
    StepResultV {
        state: Proc {
            store: outcome.next,
            pending: before.pending + outcome.work,
        },
        send: spec_send(call, outcome.resp, outcome.send),
    }
}

/// Lean's `runShed`: the state stays, and the client is told 503.
pub open spec fn spec_shed(before: Proc, call: Call) -> StepResultV<Proc, Pid, Message> {
    StepResultV {
        state: before,
        send: spec_send(call, spec_unavailable(call.request), Seq::empty()),
    }
}

/// Lean's `runLose`: the handler runs, and the client is told 503. Dispatches
/// the handler emitted are still sent.
pub open spec fn spec_lose(
    before: Proc,
    call: Call,
    outcome: OutV,
) -> StepResultV<Proc, Pid, Message> {
    StepResultV {
        state: Proc {
            store: outcome.next,
            pending: before.pending + outcome.work,
        },
        send: spec_send(call, spec_unavailable(call.request), outcome.send),
    }
}

pub open spec fn spec_losses(
    before: Proc,
    call: Call,
    outcomes: Seq<OutV>,
) -> Seq<StepResultV<Proc, Pid, Message>>
    decreases outcomes.len(),
{
    if outcomes.len() == 0 {
        Seq::empty()
    } else {
        seq![spec_lose(before, call, outcomes[0])] + spec_losses(before, call, outcomes.skip(1))
    }
}

pub proof fn lemma_losses_map(before: Proc, call: Call, outcomes: Seq<OutV>)
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
    state: Proc,
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
    vstd::seq::lemma_seq_push_len(Seq::<StepResultV<Proc, Pid, Message>>::empty(), spec_shed(state, call));
    assert(shed.len() == 1);
    let j = prefix.len() as int;
    vstd::seq::lemma_seq_add_index2(prefix, shed, j);
    vstd::seq::lemma_seq_push_index_same(
        Seq::<StepResultV<Proc, Pid, Message>>::empty(),
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
    state: Proc,
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

pub open spec fn spec_ready(work: InternalV, now: Time) -> bool {
    match work {
        InternalV::Occurrence { at, .. } => at <= now,
        _ => false,
    }
}

pub open spec fn remove_at<T>(values: Seq<T>, i: int) -> Seq<T> {
    values.take(i) + values.skip(i + 1)
}

pub open spec fn spec_internal_result(
    before: Proc,
    i: int,
    outcome: InOutV,
) -> StepResultV<Proc, Pid, Message> {
    StepResultV {
        state: Proc {
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

pub open spec fn spec_idle(state: Proc) -> Seq<StepResultV<Proc, Pid, Message>> {
    seq![StepResultV {
        state,
        send: Seq::empty(),
    }]
}

impl RoverSpec::Spec for Spec {
    type Config = ServerConfig;
    type Pid = Pid;
    type Proc = Proc;
    type Message = Message;
    type Boundary = BoundaryEvent;

    open spec fn outside(&self) -> Pid {
        Pid::Outside
    }

    open spec fn processes(&self, _config: ServerConfig) -> Seq<(Pid, Proc)> {
        seq![(
            Pid::Service,
            Proc {
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

pub open spec fn spec_run(config: ServerConfig, state: Proc, call: Call, now: Time) -> Seq<StepResultV<Proc, Pid, Message>> {
    spec_handler(config, call.request, state.store, now).map_values(|outcome: OutV|
        spec_request_outcome(state, call, outcome)
    )
}

pub open spec fn spec_due_result(before: Proc, outcome: InOutV) -> StepResultV<Proc, Pid, Message> {
    StepResultV {
        state: Proc { store: outcome.next, pending: before.pending + outcome.work },
        send: outcome.send.map_values(|dispatch: DispatchV| (
            Pid::Outside,
            Message::Output(Output::Dispatch(lift_dispatch(dispatch))),
        )),
    }
}

pub open spec fn spec_queue(config: ServerConfig, state: Proc, now: Time, i: int) -> Seq<StepResultV<Proc, Pid, Message>>
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

pub open spec fn spec_keep(config: ServerConfig, state: Proc, now: Time, work: InternalV, rest: Seq<StepResultV<Proc, Pid, Message>>) -> Seq<StepResultV<Proc, Pid, Message>> {
    let outcome = spec_process_work(config, work, state.store, now);
    if outcome.not_due {
        rest
    } else {
        seq![spec_due_result(state, outcome)] + rest
    }
}

pub open spec fn spec_over_callbacks(
    config: ServerConfig,
    state: Proc,
    now: Time,
    awaited: Seq<char>,
    awaiters: Seq<Seq<char>>,
) -> Seq<StepResultV<Proc, Pid, Message>>
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
    state: Proc,
    now: Time,
    awaited: Seq<char>,
    addresses: Seq<Seq<char>>,
) -> Seq<StepResultV<Proc, Pid, Message>>
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

pub open spec fn spec_over_promises(config: ServerConfig, state: Proc, now: Time, keys: Seq<Seq<char>>) -> Seq<StepResultV<Proc, Pid, Message>>
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

pub open spec fn spec_over_tasks(config: ServerConfig, state: Proc, now: Time, keys: Seq<Seq<char>>) -> Seq<StepResultV<Proc, Pid, Message>>
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

pub open spec fn spec_over_schedules(config: ServerConfig, state: Proc, now: Time, keys: Seq<Seq<char>>) -> Seq<StepResultV<Proc, Pid, Message>>
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

pub open spec fn spec_derived(config: ServerConfig, state: Proc, now: Time) -> Seq<StepResultV<Proc, Pid, Message>> {
    spec_over_promises(config, state, now, spec_keys(state.store.promises))
        + spec_over_tasks(config, state, now, spec_keys(state.store.tasks))
        + spec_over_schedules(config, state, now, spec_keys(state.store.schedules))
}

pub open spec fn spec_run_timeout(config: ServerConfig, state: Proc, now: Time) -> Seq<StepResultV<Proc, Pid, Message>> {
    spec_queue(config, state, now, 0) + spec_derived(config, state, now)
}

pub open spec fn spec_service(config: ServerConfig, state: Proc, now: Time, event: ProcessEvent<Pid, Message>) -> Seq<StepResultV<Proc, Pid, Message>> {
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
