use echod_concrete::node::REQUEST_SWEEP_STEPS;
use echod_concrete::{
    clone_body, empty_workflow, peek, request_transition, DocumentBody, Outbound,
};
use echod_types::{
    PromiseCreateReq, PromiseGetReq, PromiseRegisterCallbackReq, PromiseRegisterListenerReq,
    PromiseSettleReq, PromiseState, Request, Response, TaskAcquireReq, TaskContinueReq,
    TaskHaltReq, TaskReleaseReq, TaskState, TaskSuspendReq, Value, MAX_TIME, MAX_VERSION,
};

const NOW: u64 = 1_000;
const RETRY: u64 = 100;

fn value(data: &str) -> Value {
    Value {
        headers: Vec::new(),
        data: Some(data.to_string()),
    }
}

fn target() -> Vec<(String, String)> {
    vec![("resonate:target".into(), "http://worker".into())]
}

fn external() -> Vec<(String, String)> {
    vec![("resonate:external".into(), "true".into())]
}

fn create(id: &str, tags: Vec<(String, String)>) -> Request {
    Request::PromiseCreate(PromiseCreateReq {
        id: id.into(),
        timeout_at: NOW + 10_000,
        param: value("input"),
        tags,
    })
}

fn settle(id: &str) -> Request {
    Request::PromiseSettle(PromiseSettleReq {
        id: id.into(),
        state: PromiseState::Resolved,
        value: value("done"),
    })
}

fn step(doc: DocumentBody, request: Request, now: u64) -> (DocumentBody, Response, Vec<Outbound>) {
    let (doc, response, born, notes) =
        request_transition(doc, &request, now, RETRY, REQUEST_SWEEP_STEPS);
    assert!(born.is_empty());
    (doc, response, notes)
}

fn status(response: &Response) -> u16 {
    match response {
        Response::Promise(r) => r.status,
        Response::TaskClaim(r) => r.status,
        Response::TaskGet(r) => r.status,
        Response::TaskFence(r) => r.status,
        Response::Schedule(r) => r.status,
        Response::Status(r) => r.status,
    }
}

#[test]
fn runnable_create_release_and_continue_dispatch_in_their_commit() {
    let (doc, response, notes) = step(empty_workflow(), create("wf:task", target()), NOW);
    assert_eq!(status(&response), 200);
    assert_eq!(
        notes,
        vec![Outbound::Execute {
            id: "wf:task".into(),
            version: 0
        }]
    );
    let task = peek(&doc, &"wf:task".into()).unwrap().task.unwrap();
    assert_eq!(task.state, TaskState::Pending);
    assert_eq!(task.retry_timeout_at, Some(NOW + RETRY));

    let acquire = Request::TaskAcquire(TaskAcquireReq {
        id: "wf:task".into(),
        version: 0,
        pid: "worker".into(),
        ttl: 500,
    });
    let (doc, response, notes) = step(doc, acquire, NOW + 1);
    assert_eq!(status(&response), 200);
    assert!(notes.is_empty());

    let release = Request::TaskRelease(TaskReleaseReq {
        id: "wf:task".into(),
        version: 1,
    });
    let (doc, response, notes) = step(doc, release, NOW + 2);
    assert_eq!(status(&response), 200);
    assert_eq!(
        notes,
        vec![Outbound::Execute {
            id: "wf:task".into(),
            version: 1
        }]
    );
    assert_eq!(
        peek(&doc, &"wf:task".into())
            .unwrap()
            .task
            .unwrap()
            .retry_timeout_at,
        Some(NOW + 2 + RETRY),
    );

    let halt = Request::TaskHalt(TaskHaltReq {
        id: "wf:task".into(),
    });
    let (doc, response, notes) = step(doc, halt, NOW + 3);
    assert_eq!(status(&response), 200);
    assert!(notes.is_empty());

    let cont = Request::TaskContinue(TaskContinueReq {
        id: "wf:task".into(),
    });
    let (doc, response, notes) = step(doc, cont, NOW + 4);
    assert_eq!(status(&response), 200);
    assert_eq!(
        notes,
        vec![Outbound::Execute {
            id: "wf:task".into(),
            version: 1
        }]
    );
    assert_eq!(
        peek(&doc, &"wf:task".into())
            .unwrap()
            .task
            .unwrap()
            .retry_timeout_at,
        Some(NOW + 4 + RETRY),
    );
}

#[test]
fn settlement_drains_callbacks_and_listeners_before_returning_effects() {
    let (doc, _, _) = step(empty_workflow(), create("wf:awaiter", target()), NOW);
    let acquire = Request::TaskAcquire(TaskAcquireReq {
        id: "wf:awaiter".into(),
        version: 0,
        pid: "worker".into(),
        ttl: 500,
    });
    let (doc, _, _) = step(doc, acquire, NOW + 1);
    let (doc, _, _) = step(doc, create("wf:awaited", external()), NOW + 2);

    let suspend = Request::TaskSuspend(TaskSuspendReq {
        id: "wf:awaiter".into(),
        version: 1,
        actions: vec![PromiseRegisterCallbackReq {
            awaited: "wf:awaited".into(),
            awaiter: "wf:awaiter".into(),
        }],
    });
    let (doc, response, _) = step(doc, suspend, NOW + 3);
    assert_eq!(status(&response), 200);

    let listener = Request::PromiseRegisterListener(PromiseRegisterListenerReq {
        awaited: "wf:awaited".into(),
        address: "http://listener".into(),
    });
    let (doc, response, _) = step(doc, listener, NOW + 4);
    assert_eq!(status(&response), 200);

    let (doc, response, notes) = step(doc, settle("wf:awaited"), NOW + 5);
    assert_eq!(status(&response), 200);
    let settled = match &response {
        Response::Promise(r) => r.promise.clone().unwrap(),
        _ => unreachable!(),
    };
    assert_eq!(notes.len(), 2);
    assert!(notes.contains(&Outbound::Execute {
        id: "wf:awaiter".into(),
        version: 1
    }));
    assert!(notes.contains(&Outbound::Unblock {
        address: "http://listener".into(),
        promise: settled,
    }));

    let awaited = peek(&doc, &"wf:awaited".into()).unwrap();
    assert!(awaited.promise.callbacks.is_empty());
    assert!(awaited.promise.listeners.is_empty());
    let awaiter = peek(&doc, &"wf:awaiter".into()).unwrap().task.unwrap();
    assert_eq!(awaiter.state, TaskState::Pending);
    assert_eq!(awaiter.resumes, vec!["wf:awaited".to_string()]);
    assert_eq!(awaiter.retry_timeout_at, Some(NOW + 5 + RETRY));
}

#[test]
fn callbacks_only_record_resumes_on_tasks_that_are_already_running_or_queued() {
    let (doc, _, _) = step(empty_workflow(), create("wf:awaiter", target()), NOW);
    let (doc, _, _) = step(doc, create("wf:awaited", external()), NOW + 1);
    let callback = Request::PromiseRegisterCallback(PromiseRegisterCallbackReq {
        awaited: "wf:awaited".into(),
        awaiter: "wf:awaiter".into(),
    });
    let (doc, response, _) = step(doc, callback, NOW + 2);
    assert_eq!(status(&response), 200);

    let (doc, _, notes) = step(doc, settle("wf:awaited"), NOW + 3);
    assert!(
        notes.is_empty(),
        "a pending awaiter only records the resume"
    );
    let task = peek(&doc, &"wf:awaiter".into()).unwrap().task.unwrap();
    assert_eq!(task.state, TaskState::Pending);
    assert_eq!(task.resumes, vec!["wf:awaited".to_string()]);
}

#[test]
fn reads_commit_only_when_the_pre_sweep_projects_state() {
    let (doc, _, _) = step(empty_workflow(), create("wf:p", external()), NOW);
    let before = clone_body(&doc);
    let get = Request::PromiseGet(PromiseGetReq { id: "wf:p".into() });
    let (same, response, notes) = step(doc, get, NOW + 1);
    assert_eq!(status(&response), 200);
    assert_eq!(same, before);
    assert!(notes.is_empty());

    let late = NOW + 20_000;
    let (projected, response, notes) = step(
        same,
        Request::PromiseGet(PromiseGetReq { id: "wf:p".into() }),
        late,
    );
    assert_eq!(status(&response), 200);
    assert!(notes.is_empty());
    assert_eq!(
        peek(&projected, &"wf:p".into()).unwrap().promise.state,
        PromiseState::RejectedTimedout,
    );
}

#[test]
fn client_bounds_and_stored_version_exhaustion_are_rejected() {
    let bad_create = Request::PromiseCreate(PromiseCreateReq {
        id: "wf:bad".into(),
        timeout_at: MAX_TIME + 1,
        param: Value::default(),
        tags: external(),
    });
    let (doc, response, _) = step(empty_workflow(), bad_create, NOW);
    assert_eq!(status(&response), 400);

    let (doc, _, _) = step(doc, create("wf:t", target()), NOW);
    let zero_ttl = Request::TaskAcquire(TaskAcquireReq {
        id: "wf:t".into(),
        version: 0,
        pid: "worker".into(),
        ttl: 0,
    });
    let (doc, response, _) = step(doc, zero_ttl, NOW + 1);
    assert_eq!(status(&response), 400);

    let mut encoded = serde_json::to_value(&doc).unwrap();
    encoded["Workflow"]["entries"][0][1]["task"]["version"] = MAX_VERSION.into();
    let exhausted: DocumentBody = serde_json::from_value(encoded).unwrap();
    let acquire = Request::TaskAcquire(TaskAcquireReq {
        id: "wf:t".into(),
        version: MAX_VERSION,
        pid: "worker".into(),
        ttl: 1,
    });
    let (_, response, notes) = step(exhausted, acquire, NOW + 2);
    assert_eq!(status(&response), 409);
    assert!(notes.is_empty());
}
