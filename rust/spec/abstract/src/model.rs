//! One process. `handler` is one request, `run` puts its reply on the send
//! list, and `process_work` is one work item. A timeout runs one queued
//! occurrence or one step the handler will perform, or it does nothing.

use vstd::prelude::*;

use echod_rover::certificate::trusted::copy;
#[allow(unused_imports)] // specification-only name is erased by ordinary Rust
use echod_rover::rover::semantics::{Label, StepResultV};
use echod_rover::rover::{Process, ProcessEvent, RoverModel, StepResult};
use echod_rover::{Sched, Time};

use echod_types::{Request, Response};

use super::machine::{
    echo, mk, promise_res, schedule_res, status, task_get_res, Dispatch, InOut, Out, ServerConfig, Store, Work,
};
use super::protocol::{BoundaryEvent, Call, Message, Output};
#[cfg(verus_keep_ghost)]
use super::view::{group_views, lemma_lift_dispatch, DispatchV, InOutV, OutV};
use super::view::{InternalV, StoreV};

mod step;

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
        assert(server.schedules@.map_values(|s: super::machine::Schedule| s@) =~= Map::empty());
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
        assert(pending@.map_values(|item: Work| item@)
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

    /// One local step. `step::spec_step` is that transition. The `ensures` on
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
        step::spec_step(config, pid, state, now, event)
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

verus! {

impl ServerConfig {
    /// A request takes effect in `s` at time `now`: every allowed outcome.
    pub fn handler(&self, op: &Request, s: &Store, now: Time) -> (outs: Vec<Out>)
    {
        broadcast use group_views;
        match op {
            Request::PromiseCreate(c) => self.promise_create(c, false, s, now),
            Request::PromiseGet(q) => match s.promises.get(&q.id) {
                None => status(promise_res(404, None), mk("get promise: none (404)"), s),
                Some(p) => {
                    let seen = p.project(now);
                    echo(promise_res(200, Some(seen.to_record(&q.id))), mk("get promise"), s)
                },
            },
            Request::PromiseSettle(st) => self.promise_settle(st, false, s, now),
            Request::PromiseRegisterCallback(q) => self.promise_register_callback(&q.awaited, &q.awaiter, s, now),
            Request::PromiseRegisterListener(q) => self.promise_register_listener(&q.awaited, &q.address, s, now),
            Request::TaskGet(q) => match s.tasks.get(&q.id) {
                None => status(task_get_res(404, None), mk("get task: none (404)"), s),
                Some(t) => {
                    let seen = match s.promises.get(&q.id) {
                        Some(p) => t.project(&p.project(now)),
                        None => copy(t),
                    };
                    echo(task_get_res(200, Some(seen.to_record(&q.id))), mk("get task"), s)
                },
            },
            Request::TaskCreate(q) => self.task_create(&q.pid, q.ttl, &q.action, s, now),
            Request::TaskAcquire(q) => self.task_acquire(&q.id, q.version, &q.pid, q.ttl, s, now),
            Request::TaskRelease(q) => self.task_release(&q.id, q.version, s, now),
            Request::TaskFulfill(q) => self.task_fulfill(&q.id, q.version, &q.action, s, now),
            Request::TaskHeartbeat(q) => self.task_heartbeat(&q.pid, &q.tasks, s, now),
            Request::TaskSuspend(q) => self.task_suspend(q, s, now),
            Request::TaskFence(q) => self.task_fence(q, s, now),
            Request::TaskFenceCheck(q) => self.task_fence_check(q, s, now),
            Request::TaskHalt(q) => self.task_halt(&q.id, s, now),
            Request::TaskContinue(q) => self.task_continue(&q.id, s, now),
            Request::ScheduleCreate(c) => self.schedule_create(c, s, now),
            Request::ScheduleGet(q) => match s.schedules.get(&q.id) {
                None => status(schedule_res(404, None), mk("get schedule: none (404)"), s),
                Some(c) => echo(schedule_res(200, Some(c.dup())), mk("get schedule"), s),
            },
            Request::ScheduleDelete(q) => self.schedule_delete(&q.id, s),
        }
    }

    /// One due item at `now`: a deadline, a callback, a listener, a lease, a
    /// retry, a schedule, or one queued occurrence.
    pub fn process_work(&self, step: &Work, s: &Store, now: Time) -> (r: InOut) {
        match step {
            Work::PromiseTimeout(id) => self.process_promise_timeout(id, s, now),
            Work::Callback { awaited, awaiter } => self.process_callback(awaited, awaiter, s, now),
            Work::Listener { awaited, address } => self.process_listener(awaited, address, s, now),
            Work::TaskLeaseTimeout(id) => self.process_lease_timeout(id, s, now),
            Work::TaskRetryTimeout(id) => self.process_retry_timeout(id, s, now),
            Work::ScheduleTimeout { id, .. } => self.process_schedule(id, s, now),
            Work::Occurrence { promise, at, timeout, param, tags } => self.create_if_absent(promise, *at, *timeout, param, tags, s, now),
        }
    }
}

} // verus!
