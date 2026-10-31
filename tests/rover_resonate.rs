//! The complete standalone Resonate protocol through Rover's world.

use accordant::rover::resonate::abstract_model::{Model, Pid};
use accordant::rover::resonate::*;
use accordant::rover::{check, BoundaryEvent, CheckConfig, ProcessEvent, RoverModel};

type Event = BoundaryEvent<Pid, Message>;

fn create(id: &str) -> Create {
    Create {
        id: id.into(),
        timeout_at: 10_000,
        data: Some("value".into()),
        tags: PLAIN,
    }
}

/// Build one concrete execution using the standalone handler, then ask Rover
/// to rediscover and certify it from boundary events alone.
fn trace_for(requests: Vec<Request>) -> Vec<Event> {
    let logic = Resonate::default();
    let mut server = Server::default();
    let mut trace = Vec::new();

    for (i, request) in requests.into_iter().enumerate() {
        let call = Call {
            client: "client".into(),
            id: i as u64,
            request: request.clone(),
        };
        let mut outcomes = logic.request(&request, &server, 0);
        let outcome = outcomes.remove(0);

        trace.push(Event::Input {
            recipient: Pid::Service,
            at: 0,
            message: Message::Request(call),
        });
        trace.push(Event::Output {
            sender: Pid::Service,
            at: 0,
            message: Message::Output(Output::Response {
                client: "client".into(),
                id: i as u64,
                response: outcome.resp.clone(),
            }),
        });
        trace.extend(outcome.send.iter().cloned().map(|dispatch| Event::Output {
            sender: Pid::Service,
            at: 0,
            message: Message::Output(Output::Dispatch(dispatch)),
        }));
        server = outcome.next;
    }

    trace
}

#[test]
fn every_request_family_runs_through_rover() {
    let requests = vec![
        Request::CreatePromise(create("o:p")),
        Request::GetPromise("o:p".into()),
        Request::RegisterListener {
            awaited: "o:p".into(),
            address: "https://listener".into(),
        },
        Request::CreatePromise(create("o:awaiter")),
        Request::RegisterCallback {
            awaited: "o:p".into(),
            awaiter: "o:awaiter".into(),
        },
        Request::SettlePromise(Settle {
            id: "o:p".into(),
            state: "resolved".into(),
            data: Some("done".into()),
        }),
        Request::CreateTask {
            pid: "worker".into(),
            ttl: 1_000,
            action: create("o:task"),
        },
        Request::GetTask("o:task".into()),
        Request::AcquireTask {
            id: "o:task".into(),
            version: 1,
            pid: "worker".into(),
            ttl: 1_000,
        },
        Request::ReleaseTask {
            id: "o:task".into(),
            version: 1,
        },
        Request::HeartbeatTask {
            pid: "worker".into(),
            tasks: vec![TaskRef {
                id: "o:task".into(),
                version: 1,
            }],
        },
        Request::SuspendTask {
            id: "o:task".into(),
            version: 1,
            awaited: vec!["o:p".into()],
        },
        Request::FenceTask {
            id: "o:task".into(),
            version: 1,
            action: Fenced::Create(create("o:fenced")),
        },
        Request::FulfillTask {
            id: "o:task".into(),
            version: 1,
            state: "resolved".into(),
            data: Some("done".into()),
        },
        Request::HaltTask("o:task".into()),
        Request::ContinueTask("o:task".into()),
        Request::CreateSchedule(ScheduleCreate {
            id: "schedule".into(),
            cron: "* * * * *".into(),
            promise_id: "o:{{.id}}:{{.timestamp}}".into(),
            promise_timeout: 60_000,
            promise_param: None,
            promise_tags: PLAIN,
        }),
        Request::GetSchedule("schedule".into()),
        Request::DeleteSchedule("schedule".into()),
    ];
    for request in requests {
        let trace = trace_for(vec![request.clone()]);
        assert!(
            check(
                &Model,
                &Resonate::default(),
                &trace,
                CheckConfig { max_steps: 12 },
            )
            .is_some(),
            "Rover rejected {request:?}",
        );
    }
}

#[test]
fn an_unpredicted_response_is_rejected() {
    let mut trace = trace_for(vec![Request::GetPromise("missing".into())]);
    let Event::Output { message, .. } = &mut trace[1] else {
        unreachable!()
    };
    *message = Message::Output(Output::Response {
        client: "client".into(),
        id: 0,
        response: Response::Status(200),
    });

    assert!(check(
        &Model,
        &Resonate::default(),
        &trace,
        CheckConfig { max_steps: 8 },
    )
    .is_none());
}

#[test]
fn timeout_runs_the_internal_work_started_by_a_request() {
    let config = Resonate::default();
    let mut initial = Model.initial(&config);
    let state = initial.remove(0).1;
    let call = Call {
        client: "client".into(),
        id: 1,
        request: Request::CreatePromise(Create {
            id: "o:deadline".into(),
            timeout_at: 10,
            data: None,
            tags: PLAIN,
        }),
    };
    let event = ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(call),
    };
    let created = Model.on_event(&config, &Pid::Service, &state, 0, &event);
    assert!(!created[0].state.pending.is_empty());

    let timed_out = Model.on_event(
        &config,
        &Pid::Service,
        &created[0].state,
        10,
        &ProcessEvent::Timeout,
    );
    assert!(!timed_out.is_empty());
    assert!(timed_out.iter().any(|result| {
        result
            .state
            .server
            .promises
            .get(&"o:deadline".to_string())
            .is_some_and(|promise| promise.state == PState::TimedOut)
    }));
}
