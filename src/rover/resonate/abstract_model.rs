//! Standalone abstract Resonate process.
//!
//! `on_event` is executable and powers Rover trace checking.
//! `spec_on_event` is its proof model. Their match trees are deliberately
//! parallel; helper functions follow the same convention.

use vstd::prelude::*;

use crate::certificate::trusted::copy;
#[allow(unused_imports)] // specification-only name is erased by ordinary Rust
use crate::rover::semantics::StepResultV;
use crate::rover::{ProcessEvent, RoverModel, StepResult};
use crate::Time;

use super::{
    Address, Call, Config, Message, Output, Promise, PromiseId, PromiseState, Promises, Record,
    Request, Response, State,
};

verus! {

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum Pid {
    Outside,
    Service,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Model;

pub open spec fn spec_record(promise: Promise) -> Record {
    Record {
        id: promise.id,
        state: promise.state,
        value: promise.value,
        timeout_at: promise.timeout_at,
    }
}

pub fn record(promise: &Promise) -> (result: Record)
    ensures
        result == spec_record(*promise),
{
    Record {
        id: promise.id,
        state: promise.state,
        value: promise.value,
        timeout_at: promise.timeout_at,
    }
}

pub open spec fn spec_remove(promises: Promises, id: PromiseId) -> Promises
    decreases promises,
{
    match promises {
        Promises::Nil => Promises::Nil,
        Promises::Cons(promise, rest) => {
            let tail = spec_remove(*rest, id);
            if promise.id == id {
                tail
            } else {
                Promises::Cons(promise, Box::new(tail))
            }
        }
    }
}

pub fn remove(promises: &Promises, id: PromiseId) -> (result: Promises)
    ensures
        result == spec_remove(*promises, id),
    decreases promises,
{
    match promises {
        Promises::Nil => Promises::Nil,
        Promises::Cons(promise, rest) => {
            let tail = remove(rest, id);
            if promise.id == id {
                tail
            } else {
                Promises::Cons(*promise, Box::new(tail))
            }
        }
    }
}

pub open spec fn spec_lookup(promises: Promises, id: PromiseId) -> Option<Promise>
    decreases promises,
{
    match promises {
        Promises::Nil => None,
        Promises::Cons(promise, rest) => {
            if promise.id == id {
                Some(promise)
            } else {
                spec_lookup(*rest, id)
            }
        }
    }
}

pub fn lookup(promises: &Promises, id: PromiseId) -> (result: Option<Promise>)
    ensures
        result == spec_lookup(*promises, id),
    decreases promises,
{
    match promises {
        Promises::Nil => None,
        Promises::Cons(promise, rest) => {
            if promise.id == id {
                Some(*promise)
            } else {
                lookup(rest, id)
            }
        }
    }
}

pub open spec fn spec_save(state: State, promise: Promise) -> State {
    State {
        promises: Promises::Cons(
            promise,
            Box::new(spec_remove(state.promises, promise.id)),
        ),
    }
}

pub fn save(state: &State, promise: Promise) -> (result: State)
    ensures
        result == spec_save(*state, promise),
{
    State {
        promises: Promises::Cons(
            promise,
            Box::new(remove(&state.promises, promise.id)),
        ),
    }
}

pub open spec fn spec_notification(
    listener: Option<Address>,
    promise: Promise,
) -> Seq<Output> {
    match listener {
        Some(address) => seq![Output::Notification {
            address,
            promise: spec_record(promise),
        }],
        None => Seq::empty(),
    }
}

pub fn notification(
    listener: Option<Address>,
    promise: &Promise,
) -> (outputs: Vec<Output>)
    ensures
        outputs@ == spec_notification(listener, *promise),
{
    match listener {
        Some(address) => vec![Output::Notification {
            address,
            promise: record(promise),
        }],
        None => Vec::new(),
    }
}

pub struct Loaded {
    pub state: State,
    pub promise: Option<Promise>,
    pub outputs: Vec<Output>,
}

pub struct LoadedV {
    pub state: State,
    pub promise: Option<Promise>,
    pub outputs: Seq<Output>,
}

pub open spec fn spec_load(state: State, id: PromiseId, now: Time) -> LoadedV {
    match spec_lookup(state.promises, id) {
        None => LoadedV {
            state,
            promise: None,
            outputs: Seq::empty(),
        },
        Some(promise) => {
            if promise.state == PromiseState::Pending && promise.timeout_at <= now {
                let settled = Promise {
                    state: PromiseState::TimedOut,
                    value: 0,
                    listener: None,
                    ..promise
                };
                LoadedV {
                    state: spec_save(state, settled),
                    promise: Some(settled),
                    outputs: spec_notification(promise.listener, settled),
                }
            } else {
                LoadedV {
                    state,
                    promise: Some(promise),
                    outputs: Seq::empty(),
                }
            }
        }
    }
}

pub fn load(state: &State, id: PromiseId, now: Time) -> (result: Loaded)
    ensures
        result.state == spec_load(*state, id, now).state,
        result.promise == spec_load(*state, id, now).promise,
        result.outputs@ == spec_load(*state, id, now).outputs,
{
    match lookup(&state.promises, id) {
        None => Loaded {
            state: copy(state),
            promise: None,
            outputs: Vec::new(),
        },
        Some(promise) => {
            if promise.state == PromiseState::Pending && promise.timeout_at <= now {
                let settled = Promise {
                    state: PromiseState::TimedOut,
                    value: 0,
                    listener: None,
                    ..promise
                };
                Loaded {
                    state: save(state, settled),
                    promise: Some(settled),
                    outputs: notification(promise.listener, &settled),
                }
            } else {
                Loaded {
                    state: copy(state),
                    promise: Some(promise),
                    outputs: Vec::new(),
                }
            }
        }
    }
}

pub struct Handled {
    pub state: State,
    pub response: Response,
    pub outputs: Vec<Output>,
}

pub struct HandledV {
    pub state: State,
    pub response: Response,
    pub outputs: Seq<Output>,
}

pub open spec fn spec_ok(promise: Promise) -> Response {
    Response {
        status: 200,
        promise: Some(spec_record(promise)),
    }
}

pub fn ok(promise: &Promise) -> (response: Response)
    ensures
        response == spec_ok(*promise),
{
    Response {
        status: 200,
        promise: Some(record(promise)),
    }
}

pub open spec fn spec_status(status: u16) -> Response {
    Response {
        status,
        promise: None,
    }
}

pub open spec fn spec_sat_add(a: u64, b: u64) -> u64 {
    if a > u64::MAX - b {
        u64::MAX
    } else {
        (a + b) as u64
    }
}

pub fn sat_add(a: u64, b: u64) -> (result: u64)
    ensures
        result == spec_sat_add(a, b),
{
    if a > u64::MAX - b {
        u64::MAX
    } else {
        a + b
    }
}

pub open spec fn spec_handle(
    config: Config,
    state: State,
    request: Request,
    now: Time,
) -> HandledV {
    let loaded = spec_load(state, request.spec_key(), now);
    match request {
        Request::Get { .. } => match loaded.promise {
            Some(promise) => HandledV {
                state: loaded.state,
                response: spec_ok(promise),
                outputs: loaded.outputs,
            },
            None => HandledV {
                state: loaded.state,
                response: spec_status(404),
                outputs: loaded.outputs,
            },
        },
        Request::Create { id, timeout_at } => match loaded.promise {
            Some(promise) => HandledV {
                state: loaded.state,
                response: spec_ok(promise),
                outputs: loaded.outputs,
            },
            None => {
                let timeout = match timeout_at {
                    Some(timeout) => timeout,
                    None => spec_sat_add(now, config.default_timeout),
                };
                let promise = Promise {
                    id,
                    state: if timeout <= now {
                        PromiseState::TimedOut
                    } else {
                        PromiseState::Pending
                    },
                    value: 0,
                    timeout_at: timeout,
                    listener: None,
                };
                HandledV {
                    state: spec_save(loaded.state, promise),
                    response: spec_ok(promise),
                    outputs: loaded.outputs,
                }
            }
        },
        Request::Settle {
            state: next_state,
            value,
            ..
        } => {
            if !next_state.spec_settable() {
                HandledV {
                    state: loaded.state,
                    response: spec_status(400),
                    outputs: loaded.outputs,
                }
            } else {
                match loaded.promise {
                    None => HandledV {
                        state: loaded.state,
                        response: spec_status(404),
                        outputs: loaded.outputs,
                    },
                    Some(promise) => {
                        if promise.state == PromiseState::Pending {
                            let settled = Promise {
                                state: next_state,
                                value,
                                listener: None,
                                ..promise
                            };
                            HandledV {
                                state: spec_save(loaded.state, settled),
                                response: spec_ok(settled),
                                outputs: loaded.outputs
                                    + spec_notification(promise.listener, settled),
                            }
                        } else {
                            HandledV {
                                state: loaded.state,
                                response: spec_ok(promise),
                                outputs: loaded.outputs,
                            }
                        }
                    }
                }
            }
        }
        Request::Listen { address, .. } => match loaded.promise {
            None => HandledV {
                state: loaded.state,
                response: spec_status(404),
                outputs: loaded.outputs,
            },
            Some(promise) => {
                let listened = if promise.state == PromiseState::Pending {
                    Promise {
                        listener: Some(address),
                        ..promise
                    }
                } else {
                    promise
                };
                HandledV {
                    state: spec_save(loaded.state, listened),
                    response: spec_ok(listened),
                    outputs: loaded.outputs,
                }
            }
        },
    }
}

pub fn handle(
    config: Config,
    state: &State,
    request: Request,
    now: Time,
) -> (result: Handled)
    ensures
        result.state == spec_handle(config, *state, request, now).state,
        result.response == spec_handle(config, *state, request, now).response,
        result.outputs@ == spec_handle(config, *state, request, now).outputs,
{
    let loaded = load(state, request.key(), now);
    match request {
        Request::Get { .. } => match loaded.promise {
            Some(promise) => Handled {
                state: loaded.state,
                response: ok(&promise),
                outputs: loaded.outputs,
            },
            None => Handled {
                state: loaded.state,
                response: Response {
                    status: 404,
                    promise: None,
                },
                outputs: loaded.outputs,
            },
        },
        Request::Create { id, timeout_at } => match loaded.promise {
            Some(promise) => Handled {
                state: loaded.state,
                response: ok(&promise),
                outputs: loaded.outputs,
            },
            None => {
                let timeout = match timeout_at {
                    Some(timeout) => timeout,
                    None => sat_add(now, config.default_timeout),
                };
                let promise = Promise {
                    id,
                    state: if timeout <= now {
                        PromiseState::TimedOut
                    } else {
                        PromiseState::Pending
                    },
                    value: 0,
                    timeout_at: timeout,
                    listener: None,
                };
                Handled {
                    state: save(&loaded.state, promise),
                    response: ok(&promise),
                    outputs: loaded.outputs,
                }
            }
        },
        Request::Settle {
            state: next_state,
            value,
            ..
        } => {
            if !next_state.settable() {
                Handled {
                    state: loaded.state,
                    response: Response {
                        status: 400,
                        promise: None,
                    },
                    outputs: loaded.outputs,
                }
            } else {
                match loaded.promise {
                    None => Handled {
                        state: loaded.state,
                        response: Response {
                            status: 404,
                            promise: None,
                        },
                        outputs: loaded.outputs,
                    },
                    Some(promise) => {
                        if promise.state == PromiseState::Pending {
                            let settled = Promise {
                                state: next_state,
                                value,
                                listener: None,
                                ..promise
                            };
                            let mut outputs = loaded.outputs;
                            outputs.append(&mut notification(promise.listener, &settled));
                            Handled {
                                state: save(&loaded.state, settled),
                                response: ok(&settled),
                                outputs,
                            }
                        } else {
                            Handled {
                                state: loaded.state,
                                response: ok(&promise),
                                outputs: loaded.outputs,
                            }
                        }
                    }
                }
            }
        }
        Request::Listen { address, .. } => match loaded.promise {
            None => Handled {
                state: loaded.state,
                response: Response {
                    status: 404,
                    promise: None,
                },
                outputs: loaded.outputs,
            },
            Some(promise) => {
                let listened = if promise.state == PromiseState::Pending {
                    Promise {
                        listener: Some(address),
                        ..promise
                    }
                } else {
                    promise
                };
                Handled {
                    state: save(&loaded.state, listened),
                    response: ok(&listened),
                    outputs: loaded.outputs,
                }
            }
        },
    }
}

pub open spec fn spec_messages(call: Call, handled: HandledV, status: u16) -> Seq<(Pid, Message)> {
    handled.outputs.map_values(|output: Output| (
        Pid::Outside,
        Message::Output(output),
    )).push((
        Pid::Outside,
        Message::Output(Output::Response {
            client: call.client,
            id: call.id,
            response: Response {
                status,
                promise: if status == handled.response.status {
                    handled.response.promise
                } else {
                    None
                },
            },
        }),
    ))
}

pub open spec fn spec_request_results(
    config: Config,
    state: State,
    call: Call,
) -> Seq<StepResultV<State, Pid, Message>> {
    let handled = spec_handle(config, state, call.request, call.requested_at);
    let served = StepResultV {
        state: handled.state,
        send: spec_messages(call, handled, handled.response.status),
    };
    if config.unreliable {
        seq![
            served,
            StepResultV {
                state,
                send: spec_messages(
                    call,
                    HandledV {
                        state,
                        response: spec_status(503),
                        outputs: Seq::empty(),
                    },
                    503,
                ),
            },
            StepResultV {
                state: handled.state,
                send: spec_messages(call, handled, 503),
            },
        ]
    } else {
        seq![served]
    }
}

pub open spec fn spec_idle(state: State) -> Seq<StepResultV<State, Pid, Message>> {
    seq![StepResultV {
        state,
        send: Seq::empty(),
    }]
}

pub fn messages(
    call: Call,
    handled: &Handled,
    status: u16,
) -> (messages: Vec<(Pid, Message)>)
    ensures
        messages@ == spec_messages(
            call,
            HandledV {
                state: handled.state,
                response: handled.response,
                outputs: handled.outputs@,
            },
            status,
        ),
{
    let ghost all = handled.outputs@;
    let mut outputs = copy(&handled.outputs);
    let mut messages = Vec::new();
    while !outputs.is_empty()
        invariant
            messages@.len() + outputs@.len() == all.len(),
            outputs@ == all.skip(messages@.len() as int),
            messages@ == all.take(messages@.len() as int).map_values(|output: Output| (
                Pid::Outside,
                Message::Output(output),
            )),
        decreases outputs.len(),
    {
        let ghost i = messages@.len() as int;
        assert(0 <= i < all.len());
        let output = outputs.remove(0);
        assert(output == all[i]);
        assert(all.skip(i).remove(0) =~= all.skip(i + 1));
        assert(all.take(i + 1) =~= all.take(i).push(all[i]));
        messages.push((Pid::Outside, Message::Output(output)));
    }
    proof {
        assert(all.take(all.len() as int) =~= all);
        assert(messages@ =~= all.map_values(|output: Output| (
            Pid::Outside,
            Message::Output(output),
        )));
    }
    messages.push((
        Pid::Outside,
        Message::Output(Output::Response {
            client: call.client,
            id: call.id,
            response: Response {
                status,
                promise: if status == handled.response.status {
                    handled.response.promise
                } else {
                    None
                },
            },
        }),
    ));
    proof {
        assert(messages@ =~= spec_messages(
            call,
            HandledV {
                state: handled.state,
                response: handled.response,
                outputs: handled.outputs@,
            },
            status,
        ));
    }
    messages
}

pub fn request_results(
    config: Config,
    state: &State,
    call: Call,
) -> (results: Vec<StepResult<Model>>)
    ensures
        results@.map_values(|result: StepResult<Model>| StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_request_results(config, *state, call),
{
    let handled = handle(config, state, call.request, call.requested_at);
    let served = StepResult {
        state: copy(&handled.state),
        send: messages(call, &handled, handled.response.status),
    };
    if config.unreliable {
        let shed = Handled {
            state: copy(state),
            response: Response {
                status: 503,
                promise: None,
            },
            outputs: Vec::new(),
        };
        let lost_send = messages(call, &handled, 503);
        vec![
            served,
            StepResult {
                state: copy(state),
                send: messages(call, &shed, 503),
            },
            StepResult {
                state: handled.state,
                send: lost_send,
            },
        ]
    } else {
        vec![served]
    }
}

pub struct Ticked {
    pub promises: Promises,
    pub outputs: Vec<Output>,
}

pub struct TickedV {
    pub promises: Promises,
    pub outputs: Seq<Output>,
}

pub open spec fn spec_tick(promises: Promises, now: Time) -> TickedV
    decreases promises,
{
    match promises {
        Promises::Nil => TickedV {
            promises: Promises::Nil,
            outputs: Seq::empty(),
        },
        Promises::Cons(promise, rest) => {
            let tail = spec_tick(*rest, now);
            if promise.state == PromiseState::Pending && promise.timeout_at <= now {
                let settled = Promise {
                    state: PromiseState::TimedOut,
                    value: 0,
                    listener: None,
                    ..promise
                };
                TickedV {
                    promises: Promises::Cons(settled, Box::new(tail.promises)),
                    outputs: spec_notification(promise.listener, settled) + tail.outputs,
                }
            } else {
                TickedV {
                    promises: Promises::Cons(promise, Box::new(tail.promises)),
                    outputs: tail.outputs,
                }
            }
        }
    }
}

pub fn tick(promises: &Promises, now: Time) -> (result: Ticked)
    ensures
        result.promises == spec_tick(*promises, now).promises,
        result.outputs@ == spec_tick(*promises, now).outputs,
    decreases promises,
{
    match promises {
        Promises::Nil => Ticked {
            promises: Promises::Nil,
            outputs: Vec::new(),
        },
        Promises::Cons(promise, rest) => {
            let mut tail = tick(rest, now);
            if promise.state == PromiseState::Pending && promise.timeout_at <= now {
                let settled = Promise {
                    state: PromiseState::TimedOut,
                    value: 0,
                    listener: None,
                    ..*promise
                };
                let mut outputs = notification(promise.listener, &settled);
                outputs.append(&mut tail.outputs);
                Ticked {
                    promises: Promises::Cons(settled, Box::new(tail.promises)),
                    outputs,
                }
            } else {
                Ticked {
                    promises: Promises::Cons(*promise, Box::new(tail.promises)),
                    outputs: tail.outputs,
                }
            }
        }
    }
}

pub open spec fn spec_tick_results(
    state: State,
    now: Time,
) -> Seq<StepResultV<State, Pid, Message>> {
    let ticked = spec_tick(state.promises, now);
    seq![StepResultV {
        state: State {
            promises: ticked.promises,
        },
        send: ticked.outputs.map_values(|output: Output| (
            Pid::Outside,
            Message::Output(output),
        )),
    }]
}

pub fn tick_results(state: &State, now: Time) -> (results: Vec<StepResult<Model>>)
    ensures
        results@.map_values(|result: StepResult<Model>| StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_tick_results(*state, now),
{
    let ticked = tick(&state.promises, now);
    let ghost all = ticked.outputs@;
    let mut outputs = ticked.outputs;
    let mut send = Vec::new();
    while !outputs.is_empty()
        invariant
            send@.len() + outputs@.len() == all.len(),
            outputs@ == all.skip(send@.len() as int),
            send@ == all.take(send@.len() as int).map_values(|output: Output| (
                Pid::Outside,
                Message::Output(output),
            )),
        decreases outputs.len(),
    {
        let ghost i = send@.len() as int;
        assert(0 <= i < all.len());
        let output = outputs.remove(0);
        assert(output == all[i]);
        assert(all.skip(i).remove(0) =~= all.skip(i + 1));
        assert(all.take(i + 1) =~= all.take(i).push(all[i]));
        send.push((Pid::Outside, Message::Output(output)));
    }
    proof {
        assert(all.take(all.len() as int) =~= all);
        assert(send@ =~= all.map_values(|output: Output| (
            Pid::Outside,
            Message::Output(output),
        )));
    }
    vec![StepResult {
        state: State {
            promises: ticked.promises,
        },
        send,
    }]
}

pub fn idle(state: &State) -> (results: Vec<StepResult<Model>>)
    ensures
        results@.map_values(|result: StepResult<Model>| StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_idle(*state),
{
    vec![StepResult {
        state: copy(state),
        send: Vec::new(),
    }]
}

impl RoverModel for Model {
    type Config = Config;
    type Pid = Pid;
    type StateV = State;
    type State = State;
    type Message = Message;

    fn outside(&self) -> (outside: Pid) {
        Pid::Outside
    }

    fn initial(&self, _config: &Config) -> (states: Vec<(Pid, State)>) {
        vec![(
            Pid::Service,
            State {
                promises: Promises::Nil,
            },
        )]
    }

    fn injectable(&self, _config: &Config, message: &Message) -> (injectable: bool) {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    fn on_event(
        &self,
        config: &Config,
        pid: &Pid,
        state: &State,
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
            ) => request_results(*config, state, *call),
            (Pid::Service, ProcessEvent::Timeout) => tick_results(state, _now),
            _ => idle(state),
        }
    }

    open spec fn spec_outside(&self) -> Pid {
        Pid::Outside
    }

    open spec fn spec_initial(&self, _config: Config) -> Seq<(Pid, State)> {
        seq![(Pid::Service, State {
            promises: Promises::Nil,
        })]
    }

    open spec fn spec_injectable(&self, _config: Config, message: Message) -> bool {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    open spec fn spec_on_event(
        &self,
        config: Config,
        pid: Pid,
        state: State,
        _now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<StepResultV<State, Pid, Message>> {
        match (pid, event) {
            (
                Pid::Service,
                ProcessEvent::Receive {
                    sender: Pid::Outside,
                    message: Message::Request(call),
                },
            ) => spec_request_results(config, state, call),
            (Pid::Service, ProcessEvent::Timeout) => spec_tick_results(state, _now),
            _ => spec_idle(state),
        }
    }
}

} // verus!
