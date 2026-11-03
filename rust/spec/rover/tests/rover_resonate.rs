//! The complete standalone Resonate protocol through Rover's world.

use echod_rover::rover::{check, BoundaryEvent, CheckConfig, ProcessEvent, RoverModel};
use echod_abstract::abstract_model::Pid;
use echod_abstract::types::*;
use echod_abstract::*;

type Event = BoundaryEvent<Pid, Message>;

fn create(id: &str) -> PromiseCreateReq {
    PromiseCreateReq {
        id: id.into(),
        timeout_at: 10_000,
        param: Value { headers: Vec::new(), data: Some("value".into()) },
        tags: plain(),
    }
}

fn settle(id: &str, data: &str) -> PromiseSettleReq {
    PromiseSettleReq {
        id: id.into(),
        state: PromiseState::Resolved,
        value: Value { headers: Vec::new(), data: Some(data.into()) },
    }
}

/// Build one concrete execution using the standalone handler, then ask Rover
/// to rediscover and certify it from boundary events alone.
fn trace_for(requests: Vec<Request>) -> Vec<Event> {
    let logic = ServerConfig::default();
    let mut server = Store::default();
    let mut trace = Vec::new();

    for (i, request) in requests.into_iter().enumerate() {
        let call = Call {
            client: "client".into(),
            id: i as u64,
            request: request.clone(),
        };
        let mut outcomes = logic.handler(&request, &server, 0);
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
    let cron = "* * * * *";
    let requests = vec![
        Request::PromiseCreate(create("o:p")),
        Request::PromiseGet(PromiseGetReq { id: "o:p".into() }),
        Request::PromiseRegisterListener(PromiseRegisterListenerReq {
            awaited: "o:p".into(),
            address: "https://listener".into(),
        }),
        Request::PromiseCreate(create("o:awaiter")),
        Request::PromiseRegisterCallback(PromiseRegisterCallbackReq {
            awaited: "o:p".into(),
            awaiter: "o:awaiter".into(),
        }),
        Request::PromiseSettle(settle("o:p", "done")),
        Request::TaskCreate(TaskCreateReq { pid: "worker".into(), ttl: 1_000, action: create("o:task") }),
        Request::TaskGet(TaskGetReq { id: "o:task".into() }),
        Request::TaskAcquire(TaskAcquireReq { id: "o:task".into(), version: 1, pid: "worker".into(), ttl: 1_000 }),
        Request::TaskRelease(TaskReleaseReq { id: "o:task".into(), version: 1 }),
        Request::TaskHeartbeat(TaskHeartbeatReq {
            pid: "worker".into(),
            tasks: vec![TaskRef { id: "o:task".into(), version: 1 }],
        }),
        Request::TaskSuspend(TaskSuspendReq {
            id: "o:task".into(),
            version: 1,
            actions: vec![PromiseRegisterCallbackReq { awaited: "o:p".into(), awaiter: "o:task".into() }],
        }),
        Request::TaskFence(TaskFenceReq {
            id: "o:task".into(),
            version: 1,
            action: TaskFenceAction::Create(create("o:fenced")),
        }),
        Request::TaskFulfill(TaskFulfillReq { id: "o:task".into(), version: 1, action: settle("o:task", "done") }),
        Request::TaskHalt(TaskHaltReq { id: "o:task".into() }),
        Request::TaskContinue(TaskContinueReq { id: "o:task".into() }),
        Request::ScheduleCreate(ScheduleCreateReq {
            id: "schedule".into(),
            cron: cron.into(),
            promise_id: "o:{{.id}}:{{.timestamp}}".into(),
            promise_timeout: 60_000,
            promise_param: Value::empty(),
            promise_tags: plain(),
            next_run_at: next_cron(cron, 0),
        }),
        Request::ScheduleGet(ScheduleGetReq { id: "schedule".into() }),
        Request::ScheduleDelete(ScheduleDeleteReq { id: "schedule".into() }),
    ];
    for request in requests {
        let trace = trace_for(vec![request.clone()]);
        assert!(
            check(&Model, &ServerConfig::default(), &trace, CheckConfig { max_steps: 12 }).is_some(),
            "Rover rejected {request:?}",
        );
    }
}

#[test]
fn an_unpredicted_response_is_rejected() {
    let mut trace = trace_for(vec![Request::PromiseGet(PromiseGetReq { id: "missing".into() })]);
    let Event::Output { message, .. } = &mut trace[1] else {
        unreachable!()
    };
    *message = Message::Output(Output::Response {
        client: "client".into(),
        id: 0,
        response: Response::Status(StatusRes { status: 200 }),
    });

    assert!(check(&Model, &ServerConfig::default(), &trace, CheckConfig { max_steps: 8 }).is_none());
}

#[test]
fn timeout_runs_the_internal_work_started_by_a_request() {
    let config = ServerConfig::default();
    let mut initial = Model.initial(&config);
    let state = initial.remove(0).1;
    let call = Call {
        client: "client".into(),
        id: 1,
        request: Request::PromiseCreate(PromiseCreateReq {
            id: "o:deadline".into(),
            timeout_at: 10,
            param: Value::empty(),
            tags: plain(),
        }),
    };
    let event = ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(call),
    };
    let created = Model.on_event(&config, &Pid::Service, &state, 0, &event);
    assert!(created[0].state.pending.is_empty(), "a deadline is read off the promise, not queued");

    let timed_out = Model.on_event(&config, &Pid::Service, &created[0].state, 10, &ProcessEvent::Timeout);
    assert!(!timed_out.is_empty());
    assert!(timed_out.iter().any(|result| {
        result
            .state
            .store
            .promises
            .get(&"o:deadline".to_string())
            .is_some_and(|promise| promise.state == PromiseState::RejectedTimedout)
    }));
}
