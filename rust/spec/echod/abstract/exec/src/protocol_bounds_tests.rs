use crate::collections::{PMap, PSet};
use crate::state::{Handlers, Promise, Store, Task};
use crate::Config;
use echod_types::{
    PromiseCreateReq, PromiseState, Request, Response, ScheduleCreateReq, TaskAcquireReq,
    TaskCreateReq, TaskFenceAction, TaskFenceReq, TaskState, Value, MAX_TIME, MAX_VERSION,
};

fn tags(values: &[(&str, &str)]) -> Vec<(String, String)> {
    values
        .iter()
        .map(|(key, value)| ((*key).to_string(), (*value).to_string()))
        .collect()
}

fn empty_store() -> Store {
    Store {
        promises: PMap::empty(),
        tasks: PMap::empty(),
        schedules: PMap::empty(),
    }
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

fn assert_atomic(store: &Store, request: Request, expected: u16) {
    let outcomes = Handlers(&Config { retry_timeout: 50 }).handler(&request, store, 10);
    assert_eq!(outcomes.len(), 1);
    let outcome = &outcomes[0];
    assert_eq!(status(&outcome.resp), expected);
    assert_eq!(&outcome.next, store);
    assert!(outcome.work.is_empty());
    assert!(outcome.send.is_empty());
}

#[test]
fn timeout_and_ttl_bounds_are_atomic() {
    assert_atomic(
        &empty_store(),
        Request::PromiseCreate(PromiseCreateReq {
            id: "wf.promise".to_string(),
            timeout_at: MAX_TIME + 1,
            param: Value::default(),
            tags: Vec::new(),
        }),
        400,
    );

    let action = PromiseCreateReq {
        id: "wf.task".to_string(),
        timeout_at: 1_000,
        param: Value::default(),
        tags: tags(&[("resonate:target", "worker")]),
    };
    for ttl in [0, MAX_TIME + 1] {
        assert_atomic(
            &empty_store(),
            Request::TaskCreate(TaskCreateReq {
                pid: "worker".to_string(),
                ttl,
                action: action.clone(),
            }),
            400,
        );
        assert_atomic(
            &empty_store(),
            Request::TaskAcquire(TaskAcquireReq {
                id: "wf.task".to_string(),
                version: 0,
                pid: "worker".to_string(),
                ttl,
            }),
            400,
        );
    }
}

#[test]
fn maximum_version_acquisitions_conflict_atomically() {
    let id = "wf.task".to_string();
    let target = tags(&[("resonate:target", "worker")]);
    let promise = Promise {
        state: PromiseState::Pending,
        value: Value::default(),
        param: Value::default(),
        timeout_at: 1_000,
        created_at: 1,
        settled_at: None,
        tags: target.clone(),
        callbacks: PSet::empty(),
        listeners: PSet::empty(),
    };
    let task = Task {
        state: TaskState::Pending,
        version: MAX_VERSION,
        pid: None,
        ttl: None,
        acquired_at: 0,
        retry_timeout_at: Some(500),
        resumes: Vec::new(),
    };
    let mut store = empty_store();
    store.promises.insert(id.clone(), promise);
    store.tasks.insert(id.clone(), task);

    assert_atomic(
        &store,
        Request::TaskAcquire(TaskAcquireReq {
            id: id.clone(),
            version: MAX_VERSION,
            pid: "worker".to_string(),
            ttl: 100,
        }),
        409,
    );
    assert_atomic(
        &store,
        Request::TaskCreate(TaskCreateReq {
            pid: "worker".to_string(),
            ttl: 100,
            action: PromiseCreateReq {
                id,
                timeout_at: 1_000,
                param: Value::default(),
                tags: target,
            },
        }),
        409,
    );
}

#[test]
fn fence_and_schedule_timeout_bounds_are_atomic() {
    assert_atomic(
        &empty_store(),
        Request::TaskFence(TaskFenceReq {
            id: "wf.task".to_string(),
            version: 1,
            action: TaskFenceAction::Create(PromiseCreateReq {
                id: "wf.child".to_string(),
                timeout_at: MAX_TIME + 1,
                param: Value::default(),
                tags: Vec::new(),
            }),
        }),
        400,
    );

    assert_atomic(
        &empty_store(),
        Request::ScheduleCreate(ScheduleCreateReq {
            id: "tick".to_string(),
            cron: "* * * * * *".to_string(),
            promise_id: "tick-{{.timestamp}}".to_string(),
            promise_timeout: MAX_TIME,
            promise_param: Value::default(),
            promise_tags: Vec::new(),
            next_run_at: 0,
        }),
        400,
    );
}
