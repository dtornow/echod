//! Executable traces against the abstract Rover reference model.

use accordant::rover::{check, BoundaryEvent, CheckConfig};
use resonate::rover::abstract_model::{Model, Pid};
use resonate::rover::{Call, Message, Output};
use resonate::{Request, Response};

type Event = BoundaryEvent<Pid, Message>;

fn get_call() -> Call {
    Call {
        client: "client-a".into(),
        id: 7,
        requested_at: 0,
        request: Request::GetPromise("missing".into()),
    }
}

fn get_trace(response: Response) -> [Event; 2] {
    [
        Event::Input {
            recipient: Pid::Service,
            at: 0,
            message: Message::Request(get_call()),
        },
        Event::Output {
            sender: Pid::Service,
            at: 1,
            message: Message::Output(Output::Response {
                client: "client-a".into(),
                id: 7,
                response,
            }),
        },
    ]
}

#[test]
fn missing_promise_trace_is_accepted() {
    let trace = get_trace(Response::Status(404));
    assert!(check(
        &Model::default(),
        &(),
        &trace,
        CheckConfig::for_trace_len(trace.len()),
    )
    .is_some());
}

#[test]
fn wrong_abstract_response_is_rejected() {
    let trace = get_trace(Response::Status(200));
    assert!(check(
        &Model::default(),
        &(),
        &trace,
        CheckConfig::for_trace_len(trace.len()),
    )
    .is_none());
}
