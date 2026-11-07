use echod_concrete::{peek, request_transition, DocumentBody, Obj, Objects, Outbound, Prom, Tk};
use echod_types::{
    PromiseCreateReq, PromiseGetReq, PromiseSettleReq, PromiseState, Request, Response, ScheduleCreateReq,
    Tags, TaskAcquireReq, TaskContinueReq, TaskCreateReq, TaskFenceAction, TaskFenceReq,
    TaskReleaseReq, TaskState, Value, MAX_TIME, MAX_VERSION,
};

fn tags(values: &[(&str, &str)]) -> Tags {
    values
        .iter()
        .map(|(key, value)| ((*key).to_string(), (*value).to_string()))
        .collect()
}

fn promise(tags: Tags, timeout_at: u64) -> Prom {
    Prom {
        state: PromiseState::Pending,
        param: Value::default(),
        value: Value::default(),
        tags,
        timeout_at,
        created_at: 1,
        settled_at: None,
        callbacks: Vec::new(),
        listeners: Vec::new(),
    }
}

fn task(state: TaskState, retry: Option<u64>, lease: Option<u64>) -> Tk {
    let acquired = state == TaskState::Acquired;
    Tk {
        state,
        version: 1,
        pid: acquired.then(|| "worker".to_string()),
        ttl: acquired.then_some(100),
        lease_timeout_at: lease,
        retry_timeout_at: retry,
        resumes: Vec::new(),
    }
}

fn workflow(entries: Vec<(String, Obj)>) -> DocumentBody {
    DocumentBody::Workflow(Objects::from_entries(entries))
}

fn object(doc: &DocumentBody, id: &str) -> Obj {
    peek(doc, &id.to_string()).expect("object")
}

fn status(response: &Response) -> u16 {
    match response {
        Response::Promise(r) => r.status,
        Response::Schedule(r) => r.status,
        Response::Status(r) => r.status,
        Response::TaskGet(r) => r.status,
        Response::TaskClaim(r) => r.status,
        Response::TaskFence(r) => r.status,
    }
}

fn assert_execute(notes: &[Outbound], id: &str, version: u64) {
    assert!(notes.iter().any(|note| {
        matches!(note, Outbound::Execute { id: actual, version: actual_version }
            if actual == id && *actual_version == version)
    }));
}

#[test]
fn runnable_create_executes_and_rearms_in_same_transition() {
    let request = Request::PromiseCreate(PromiseCreateReq {
        id: "wf.create".to_string(),
        timeout_at: 1_000,
        param: Value::default(),
        tags: tags(&[("resonate:target", "worker")]),
    });

    let (doc, response, born, notes) =
        request_transition(workflow(Vec::new()), &request, 10, 50, 32);

    assert_eq!(status(&response), 200);
    assert!(born.is_empty());
    assert_execute(&notes, "wf.create", 0);
    let created_task = object(&doc, "wf.create").task.expect("runnable task");
    assert_eq!(created_task.state, TaskState::Pending);
    assert_eq!(created_task.retry_timeout_at, Some(60));
}

#[test]
fn release_and_continue_execute_immediately() {
    let release_doc = workflow(vec![(
        "wf.release".to_string(),
        Obj {
            promise: promise(tags(&[("resonate:target", "worker")]), 1_000),
            task: Some(task(TaskState::Acquired, None, Some(500))),
        },
    )]);
    let release = Request::TaskRelease(TaskReleaseReq {
        id: "wf.release".to_string(),
        version: 1,
    });
    let (doc, response, _, notes) = request_transition(release_doc, &release, 10, 50, 32);
    assert_eq!(status(&response), 200);
    assert_execute(&notes, "wf.release", 1);
    assert_eq!(
        object(&doc, "wf.release").task.unwrap().retry_timeout_at,
        Some(60)
    );

    let continue_doc = workflow(vec![(
        "wf.continue".to_string(),
        Obj {
            promise: promise(tags(&[("resonate:target", "worker")]), 1_000),
            task: Some(task(TaskState::Halted, None, None)),
        },
    )]);
    let continue_request = Request::TaskContinue(TaskContinueReq {
        id: "wf.continue".to_string(),
    });
    let (doc, response, _, notes) = request_transition(continue_doc, &continue_request, 10, 50, 32);
    assert_eq!(status(&response), 200);
    assert_execute(&notes, "wf.continue", 1);
    assert_eq!(
        object(&doc, "wf.continue").task.unwrap().retry_timeout_at,
        Some(60)
    );
}

#[test]
fn settlement_drains_listener_and_resumes_suspended_task() {
    let mut awaited = promise(tags(&[("resonate:external", "true")]), 1_000);
    awaited.callbacks.push("wf:awaiter".to_string());
    awaited.listeners.push("inbox".to_string());
    let doc = workflow(vec![
        (
            "wf:awaited".to_string(),
            Obj {
                promise: awaited,
                task: None,
            },
        ),
        (
            "wf:awaiter".to_string(),
            Obj {
                promise: promise(tags(&[("resonate:target", "worker")]), 1_000),
                task: Some(task(TaskState::Suspended, None, None)),
            },
        ),
    ]);
    let settle = Request::PromiseSettle(PromiseSettleReq {
        id: "wf:awaited".to_string(),
        state: PromiseState::Resolved,
        value: Value::default(),
    });

    let (doc, response, _, notes) = request_transition(doc, &settle, 10, 50, 32);

    assert_eq!(status(&response), 200);
    assert!(notes
        .iter()
        .any(|note| { matches!(note, Outbound::Unblock { address, .. } if address == "inbox") }));
    assert_execute(&notes, "wf:awaiter", 1);
    let awaited = object(&doc, "wf:awaited");
    assert!(awaited.promise.callbacks.is_empty());
    assert!(awaited.promise.listeners.is_empty());
    let awaiter = object(&doc, "wf:awaiter").task.unwrap();
    assert_eq!(awaiter.state, TaskState::Pending);
    assert_eq!(awaiter.retry_timeout_at, Some(60));
    assert_eq!(awaiter.resumes, vec!["wf:awaited".to_string()]);
}

#[test]
fn callback_does_not_execute_pending_acquired_or_halted_task() {
    for (state, retry, lease) in [
        (TaskState::Pending, Some(500), None),
        (TaskState::Acquired, None, Some(500)),
        (TaskState::Halted, None, None),
    ] {
        let mut awaited = promise(tags(&[("resonate:external", "true")]), 1_000);
        awaited.callbacks.push("wf:awaiter".to_string());
        let doc = workflow(vec![
            (
                "wf:awaited".to_string(),
                Obj {
                    promise: awaited,
                    task: None,
                },
            ),
            (
                "wf:awaiter".to_string(),
                Obj {
                    promise: promise(tags(&[("resonate:target", "worker")]), 1_000),
                    task: Some(task(state, retry, lease)),
                },
            ),
        ]);
        let settle = Request::PromiseSettle(PromiseSettleReq {
            id: "wf:awaited".to_string(),
            state: PromiseState::Resolved,
            value: Value::default(),
        });

        let (doc, response, _, notes) = request_transition(doc, &settle, 10, 50, 32);

        assert_eq!(status(&response), 200);
        assert!(!notes
            .iter()
            .any(|note| matches!(note, Outbound::Execute { .. })));
        let awaiter = object(&doc, "wf:awaiter").task.unwrap();
        assert_eq!(awaiter.state, state);
        assert_eq!(awaiter.resumes, vec!["wf:awaited".to_string()]);
    }
}

#[test]
fn read_persists_expired_projection() {
    let doc = workflow(vec![(
        "wf.expired".to_string(),
        Obj {
            promise: promise(Vec::new(), 5),
            task: None,
        },
    )]);
    let get = Request::PromiseGet(PromiseGetReq {
        id: "wf.expired".to_string(),
    });

    let (doc, response, _, notes) = request_transition(doc, &get, 10, 50, 32);

    assert_eq!(status(&response), 200);
    assert!(notes.is_empty());
    let expired = object(&doc, "wf.expired");
    assert_eq!(expired.promise.state, PromiseState::RejectedTimedout);
    assert_eq!(expired.promise.settled_at, Some(5));
}

#[test]
fn exhausted_closure_is_atomic_503() {
    let original = workflow(vec![(
        "wf.due".to_string(),
        Obj {
            promise: promise(tags(&[("resonate:target", "worker")]), 1_000),
            task: Some(task(TaskState::Pending, Some(10), None)),
        },
    )]);
    let get = Request::PromiseGet(PromiseGetReq {
        id: "wf.due".to_string(),
    });

    let (doc, response, born, notes) = request_transition(original.clone(), &get, 10, 50, 0);

    assert_eq!(status(&response), 503);
    assert_eq!(doc, original);
    assert!(born.is_empty());
    assert!(notes.is_empty());
}

#[test]
fn invalid_timeout_is_atomic_before_the_pre_sweep() {
    let original = workflow(vec![(
        "wf.due".to_string(),
        Obj {
            promise: promise(tags(&[("resonate:target", "worker")]), 1_000),
            task: Some(task(TaskState::Pending, Some(10), None)),
        },
    )]);
    let request = Request::PromiseCreate(PromiseCreateReq {
        id: "wf.new".to_string(),
        timeout_at: MAX_TIME + 1,
        param: Value::default(),
        tags: Vec::new(),
    });

    let (doc, response, born, notes) =
        request_transition(original.clone(), &request, 10, 50, 32);

    assert_eq!(status(&response), 400);
    assert_eq!(doc, original);
    assert!(born.is_empty());
    assert!(notes.is_empty());
}

#[test]
fn invalid_ttl_is_operation_shaped_and_atomic() {
    let action = PromiseCreateReq {
        id: "wf.task".to_string(),
        timeout_at: 1_000,
        param: Value::default(),
        tags: tags(&[("resonate:target", "worker")]),
    };
    for ttl in [0, MAX_TIME + 1] {
        let original = workflow(Vec::new());
        let create = Request::TaskCreate(TaskCreateReq {
            pid: "worker".to_string(),
            ttl,
            action: action.clone(),
        });
        let (doc, response, born, notes) =
            request_transition(original.clone(), &create, 10, 50, 32);
        assert!(matches!(response, Response::TaskClaim(_)));
        assert_eq!(status(&response), 400);
        assert_eq!(doc, original);
        assert!(born.is_empty());
        assert!(notes.is_empty());

        let acquire = Request::TaskAcquire(TaskAcquireReq {
            id: "wf.task".to_string(),
            version: 0,
            pid: "worker".to_string(),
            ttl,
        });
        let (doc, response, born, notes) =
            request_transition(workflow(Vec::new()), &acquire, 10, 50, 32);
        assert!(matches!(response, Response::TaskClaim(_)));
        assert_eq!(status(&response), 400);
        assert_eq!(doc, workflow(Vec::new()));
        assert!(born.is_empty());
        assert!(notes.is_empty());
    }
}

#[test]
fn exact_protocol_limits_are_admitted() {
    let create = Request::TaskCreate(TaskCreateReq {
        pid: "worker".to_string(),
        ttl: MAX_TIME,
        action: PromiseCreateReq {
            id: "wf.task".to_string(),
            timeout_at: MAX_TIME,
            param: Value::default(),
            tags: tags(&[("resonate:target", "worker")]),
        },
    });
    let (doc, response, _, _) =
        request_transition(workflow(Vec::new()), &create, 10, 50, 32);
    assert_eq!(status(&response), 200);
    assert_eq!(object(&doc, "wf.task").task.unwrap().version, 1);
}

#[test]
fn maximum_task_version_cannot_be_incremented() {
    let mut at_limit = task(TaskState::Pending, Some(500), None);
    at_limit.version = MAX_VERSION;
    let original = workflow(vec![(
        "wf.task".to_string(),
        Obj {
            promise: promise(tags(&[("resonate:target", "worker")]), 1_000),
            task: Some(at_limit),
        },
    ), (
        "wf.due".to_string(),
        Obj {
            promise: promise(tags(&[("resonate:target", "worker")]), 1_000),
            task: Some(task(TaskState::Pending, Some(10), None)),
        },
    )]);

    let acquire = Request::TaskAcquire(TaskAcquireReq {
        id: "wf.task".to_string(),
        version: MAX_VERSION,
        pid: "worker".to_string(),
        ttl: 100,
    });
    let (doc, response, born, notes) =
        request_transition(original.clone(), &acquire, 10, 50, 32);
    assert_eq!(status(&response), 409);
    assert_eq!(doc, original);
    assert!(born.is_empty());
    assert!(notes.is_empty());

    let create = Request::TaskCreate(TaskCreateReq {
        pid: "worker".to_string(),
        ttl: 100,
        action: PromiseCreateReq {
            id: "wf.task".to_string(),
            timeout_at: 1_000,
            param: Value::default(),
            tags: tags(&[("resonate:target", "worker")]),
        },
    });
    let (doc, response, born, notes) =
        request_transition(original.clone(), &create, 10, 50, 32);
    assert_eq!(status(&response), 409);
    assert_eq!(doc, original);
    assert!(born.is_empty());
    assert!(notes.is_empty());
}

#[test]
fn fence_and_schedule_reject_timeout_overflow_without_effects() {
    let original = workflow(Vec::new());
    let fence = Request::TaskFence(TaskFenceReq {
        id: "wf.task".to_string(),
        version: 1,
        action: TaskFenceAction::Create(PromiseCreateReq {
            id: "wf.child".to_string(),
            timeout_at: MAX_TIME + 1,
            param: Value::default(),
            tags: Vec::new(),
        }),
    });
    let (doc, response, born, notes) =
        request_transition(original.clone(), &fence, 10, 50, 32);
    assert!(matches!(response, Response::TaskFence(_)));
    assert_eq!(status(&response), 400);
    assert_eq!(doc, original);
    assert!(born.is_empty());
    assert!(notes.is_empty());

    let schedule = Request::ScheduleCreate(ScheduleCreateReq {
        id: "tick".to_string(),
        cron: "* * * * * *".to_string(),
        promise_id: "tick-{{.timestamp}}".to_string(),
        promise_timeout: MAX_TIME,
        promise_param: Value::default(),
        promise_tags: Vec::new(),
        next_run_at: 0,
    });
    let original = DocumentBody::Schedule(None);
    let (doc, response, born, notes) =
        request_transition(original.clone(), &schedule, 10, 50, 32);
    assert!(matches!(response, Response::Schedule(_)));
    assert_eq!(status(&response), 400);
    assert_eq!(doc, original);
    assert!(born.is_empty());
    assert!(notes.is_empty());
}
