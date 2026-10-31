//! Standalone Rover Resonate model traces.

use accordant::rover::resonate::abstract_model::{Model, Pid};
use accordant::rover::resonate::{
    Call, Config, Message, Output, PromiseState, Record, Request, Response,
};
use accordant::rover::{check, BoundaryEvent, CheckConfig};

type Event = BoundaryEvent<Pid, Message>;

fn input(at: u64, call: Call) -> Event {
    Event::Input {
        recipient: Pid::Service,
        at,
        message: Message::Request(call),
    }
}

fn response(at: u64, client: u64, id: u64, response: Response) -> Event {
    Event::Output {
        sender: Pid::Service,
        at,
        message: Message::Output(Output::Response {
            client,
            id,
            response,
        }),
    }
}

fn pending(id: u64, timeout_at: u64) -> Record {
    Record {
        id,
        state: PromiseState::Pending,
        value: 0,
        timeout_at,
    }
}

#[test]
fn create_get_listen_and_settle() {
    let created = pending(10, 100);
    let settled = Record {
        state: PromiseState::Resolved,
        value: 42,
        ..created
    };
    let trace = vec![
        input(
            0,
            Call {
                client: 1,
                id: 1,
                requested_at: 0,
                request: Request::Create {
                    id: 10,
                    timeout_at: Some(100),
                },
            },
        ),
        response(
            1,
            1,
            1,
            Response {
                status: 200,
                promise: Some(created),
            },
        ),
        input(
            1,
            Call {
                client: 1,
                id: 2,
                requested_at: 1,
                request: Request::Listen { id: 10, address: 7 },
            },
        ),
        response(
            2,
            1,
            2,
            Response {
                status: 200,
                promise: Some(created),
            },
        ),
        input(
            2,
            Call {
                client: 1,
                id: 3,
                requested_at: 2,
                request: Request::Settle {
                    id: 10,
                    state: PromiseState::Resolved,
                    value: 42,
                },
            },
        ),
        response(
            3,
            1,
            3,
            Response {
                status: 200,
                promise: Some(settled),
            },
        ),
        Event::Output {
            sender: Pid::Service,
            at: 4,
            message: Message::Output(Output::Notification {
                address: 7,
                promise: settled,
            }),
        },
    ];

    assert!(check(
        &Model,
        &Config::default(),
        &trace,
        CheckConfig { max_steps: 14 },
    )
    .is_some());
}

#[test]
fn timeout_is_a_complete_process_event() {
    let created = pending(20, 5);
    let timed_out = Record {
        state: PromiseState::TimedOut,
        value: 0,
        ..created
    };
    let trace = vec![
        input(
            0,
            Call {
                client: 1,
                id: 1,
                requested_at: 0,
                request: Request::Create {
                    id: 20,
                    timeout_at: Some(5),
                },
            },
        ),
        response(
            1,
            1,
            1,
            Response {
                status: 200,
                promise: Some(created),
            },
        ),
        input(
            1,
            Call {
                client: 1,
                id: 2,
                requested_at: 1,
                request: Request::Listen { id: 20, address: 9 },
            },
        ),
        response(
            2,
            1,
            2,
            Response {
                status: 200,
                promise: Some(created),
            },
        ),
        Event::Output {
            sender: Pid::Service,
            at: 6,
            message: Message::Output(Output::Notification {
                address: 9,
                promise: timed_out,
            }),
        },
    ];

    assert!(check(
        &Model,
        &Config::default(),
        &trace,
        CheckConfig { max_steps: 12 },
    )
    .is_some());
}

#[test]
fn unreliable_request_may_be_shed() {
    let trace = vec![
        input(
            0,
            Call {
                client: 1,
                id: 1,
                requested_at: 0,
                request: Request::Get { id: 99 },
            },
        ),
        response(
            1,
            1,
            1,
            Response {
                status: 503,
                promise: None,
            },
        ),
    ];

    assert!(check(
        &Model,
        &Config {
            unreliable: true,
            ..Config::default()
        },
        &trace,
        CheckConfig::for_trace_len(trace.len()),
    )
    .is_some());
}
