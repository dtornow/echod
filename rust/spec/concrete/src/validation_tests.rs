use crate::{
    body_deadline, validate_schedule_well_formed, validate_workflow_well_formed, DocumentBody, Obj,
    Objects, Prom, ScheduleDocument, Tk, WorkflowDocument,
};
use echod_types::{
    PromiseState, Schedule, TaskState, Value, MAX_TIME, MAX_VERSION,
};

fn empty_value() -> Value {
    Value::default()
}

fn pending_promise() -> Prom {
    Prom {
        state: PromiseState::Pending,
        param: empty_value(),
        value: empty_value(),
        tags: Vec::new(),
        timeout_at: 100,
        created_at: 1,
        settled_at: None,
        callbacks: Vec::new(),
        listeners: Vec::new(),
    }
}

fn pending_object() -> Obj {
    Obj {
        promise: pending_promise(),
        task: None,
    }
}

fn targeted_pending_object() -> Obj {
    let mut object = pending_object();
    object.promise.tags =
        vec![("resonate:target".to_string(), "worker".to_string())];
    object.task = Some(Tk {
        state: TaskState::Pending,
        version: 1,
        pid: None,
        ttl: None,
        lease_timeout_at: None,
        retry_timeout_at: Some(50),
        resumes: Vec::new(),
    });
    object
}

fn workflow_with(entries: Vec<(&str, Obj)>) -> WorkflowDocument {
    let mut document = WorkflowDocument {
        document: "wf".to_string(),
        version: 1,
        committed_at: 10,
        next_wake_at: None,
        objects: Objects {
            entries: entries
                .into_iter()
                .map(|(id, object)| (id.to_string(), object))
                .collect(),
        },
    };
    fix_workflow_wake(&mut document);
    document
}

fn fix_workflow_wake(document: &mut WorkflowDocument) {
    document.next_wake_at =
        body_deadline(&DocumentBody::Workflow(document.objects.clone()));
}

fn assert_invalid(mut document: WorkflowDocument) {
    fix_workflow_wake(&mut document);
    assert!(!validate_workflow_well_formed(&document));
}

fn settled_object() -> Obj {
    let mut object = pending_object();
    object.promise.state = PromiseState::Resolved;
    object.promise.settled_at = Some(10);
    object
}

#[test]
fn validates_a_complete_pending_workflow() {
    let document = workflow_with(vec![("wf:a", pending_object())]);
    assert!(validate_workflow_well_formed(&document));
}

#[test]
fn rejects_identity_and_time_bounds() {
    assert_invalid(workflow_with(vec![("other:a", pending_object())]));

    let mut document = workflow_with(vec![("wf:a", pending_object())]);
    document.committed_at = MAX_TIME + 1;
    assert!(!validate_workflow_well_formed(&document));

    let mut document = workflow_with(vec![("wf:a", pending_object())]);
    document.objects.entries[0].1.promise.timeout_at = MAX_TIME + 1;
    assert_invalid(document);

    let mut document = workflow_with(vec![("wf:a", pending_object())]);
    document.objects.entries[0].1.promise.created_at = 101;
    assert_invalid(document);

    let mut document = workflow_with(vec![("wf:a", pending_object())]);
    document.objects.entries[0].1.promise.created_at = 11;
    assert_invalid(document);
}

#[test]
fn rejects_pending_and_settled_timestamp_or_value_mismatches() {
    let mut document = workflow_with(vec![("wf:a", pending_object())]);
    document.objects.entries[0].1.promise.settled_at = Some(5);
    assert_invalid(document);

    let mut document = workflow_with(vec![("wf:a", pending_object())]);
    document.objects.entries[0].1.promise.timeout_at = 10;
    assert_invalid(document);

    let mut document = workflow_with(vec![("wf:a", pending_object())]);
    document.objects.entries[0].1.promise.value.data = Some("not-empty".to_string());
    assert_invalid(document);

    let mut document = workflow_with(vec![("wf:a", settled_object())]);
    document.objects.entries[0].1.promise.settled_at = Some(0);
    assert_invalid(document);

    let mut document = workflow_with(vec![("wf:a", settled_object())]);
    document.objects.entries[0].1.promise.settled_at = Some(11);
    assert_invalid(document);

    let mut object = settled_object();
    object.promise.state = PromiseState::RejectedTimedout;
    object.promise.settled_at = Some(10);
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = settled_object();
    object.promise.settled_at = Some(object.promise.timeout_at);
    object.promise.value.data = Some("forbidden".to_string());
    assert_invalid(workflow_with(vec![("wf:a", object)]));
}

#[test]
fn rejects_callback_and_listener_set_violations() {
    let mut object = pending_object();
    object.promise.tags =
        vec![("resonate:external".to_string(), "true".to_string())];
    object.promise.callbacks = vec!["wf:b".to_string(), "wf:b".to_string()];
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = pending_object();
    object.promise.tags =
        vec![("resonate:external".to_string(), "true".to_string())];
    object.promise.listeners = vec!["listener".to_string(), "listener".to_string()];
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = pending_object();
    object.promise.tags =
        vec![("resonate:external".to_string(), "true".to_string())];
    object.promise.callbacks = vec!["wf:a".to_string()];
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = pending_object();
    object.promise.tags =
        vec![("resonate:external".to_string(), "true".to_string())];
    object.promise.callbacks = vec!["other:b".to_string()];
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = pending_object();
    object.promise.listeners = vec!["listener".to_string()];
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = settled_object();
    object.promise.tags =
        vec![("resonate:external".to_string(), "true".to_string())];
    object.promise.listeners = vec!["listener".to_string()];
    assert_invalid(workflow_with(vec![("wf:a", object)]));
}

#[test]
fn rejects_task_presence_and_state_field_coupling() {
    let mut object = pending_object();
    object.promise.tags =
        vec![("resonate:target".to_string(), "worker".to_string())];
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = pending_object();
    object.task = targeted_pending_object().task;
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = targeted_pending_object();
    object.task.as_mut().unwrap().retry_timeout_at = None;
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = targeted_pending_object();
    let task = object.task.as_mut().unwrap();
    task.state = TaskState::Acquired;
    task.retry_timeout_at = None;
    task.pid = None;
    task.ttl = Some(1);
    task.lease_timeout_at = Some(50);
    assert_invalid(workflow_with(vec![("wf:a", object)]));
}

#[test]
fn rejects_task_bounds_deadlines_and_terminal_closure() {
    let mut object = targeted_pending_object();
    object.task.as_mut().unwrap().retry_timeout_at = Some(10);
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = targeted_pending_object();
    let task = object.task.as_mut().unwrap();
    task.state = TaskState::Acquired;
    task.retry_timeout_at = None;
    task.pid = Some("worker".to_string());
    task.ttl = Some(0);
    task.lease_timeout_at = Some(50);
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = targeted_pending_object();
    let task = object.task.as_mut().unwrap();
    task.state = TaskState::Acquired;
    task.retry_timeout_at = None;
    task.pid = Some("worker".to_string());
    task.ttl = Some(1);
    task.lease_timeout_at = Some(10);
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = targeted_pending_object();
    object.task.as_mut().unwrap().version = MAX_VERSION + 1;
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = targeted_pending_object();
    let task = object.task.as_mut().unwrap();
    task.resumes = vec!["wf:x".to_string(), "wf:x".to_string()];
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    for state in [TaskState::Fulfilled, TaskState::Suspended, TaskState::Halted] {
        let mut object = targeted_pending_object();
        let task = object.task.as_mut().unwrap();
        task.state = state;
        task.retry_timeout_at = None;
        task.pid = Some("not-cleared".to_string());
        assert_invalid(workflow_with(vec![("wf:a", object)]));
    }

    let mut object = targeted_pending_object();
    let task = object.task.as_mut().unwrap();
    task.state = TaskState::Suspended;
    task.retry_timeout_at = None;
    task.resumes = vec!["wf:x".to_string()];
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = targeted_pending_object();
    let task = object.task.as_mut().unwrap();
    task.state = TaskState::Fulfilled;
    task.retry_timeout_at = None;
    assert_invalid(workflow_with(vec![("wf:a", object)]));

    let mut object = settled_object();
    object.promise.tags =
        vec![("resonate:target".to_string(), "worker".to_string())];
    object.task = Some(Tk {
        state: TaskState::Halted,
        version: 1,
        pid: None,
        ttl: None,
        lease_timeout_at: None,
        retry_timeout_at: None,
        resumes: Vec::new(),
    });
    assert_invalid(workflow_with(vec![("wf:a", object)]));
}

fn callback_workflow() -> WorkflowDocument {
    let mut parent = pending_object();
    parent.promise.tags =
        vec![("resonate:external".to_string(), "true".to_string())];
    parent.promise.callbacks = vec!["wf:b".to_string()];
    workflow_with(vec![
        ("wf:a", parent),
        ("wf:b", targeted_pending_object()),
    ])
}

#[test]
fn rejects_missing_or_malformed_callback_targets() {
    let valid = callback_workflow();
    assert!(validate_workflow_well_formed(&valid));

    let mut document = valid.clone();
    document.objects.entries.pop();
    assert_invalid(document);

    let mut document = valid.clone();
    document.objects.entries[1].1.task = None;
    assert_invalid(document);

    let mut document = valid;
    document.objects.entries[1].1.promise.tags.clear();
    assert_invalid(document);
}

#[test]
fn rejects_suspended_rung_without_reverse_callback() {
    let mut suspended = targeted_pending_object();
    let task = suspended.task.as_mut().unwrap();
    task.state = TaskState::Suspended;
    task.retry_timeout_at = None;

    let mut awaited = pending_object();
    awaited.promise.tags =
        vec![("resonate:external".to_string(), "true".to_string())];
    awaited.promise.callbacks = vec!["wf:a".to_string()];

    let valid = workflow_with(vec![("wf:a", suspended), ("wf:b", awaited)]);
    assert!(validate_workflow_well_formed(&valid));

    let mut invalid = valid;
    invalid.objects.entries[1].1.promise.callbacks.clear();
    assert_invalid(invalid);
}

#[test]
fn preserves_current_deferred_descendant_clause_status() {
    let document = workflow_with(vec![
        ("wf:parent", settled_object()),
        ("wf:parent.child", pending_object()),
    ]);
    assert!(validate_workflow_well_formed(&document));
}

fn valid_schedule() -> ScheduleDocument {
    ScheduleDocument {
        document: "schedule".to_string(),
        version: 1,
        committed_at: 10,
        next_wake_at: Some(20),
        schedule: Some(Schedule {
            id: "schedule".to_string(),
            cron: "* * * * *".to_string(),
            promise_id: "wf:{{.id}}".to_string(),
            promise_timeout: 100,
            promise_param: empty_value(),
            promise_tags: Vec::new(),
            next_run_at: 20,
            last_run_at: Some(5),
            created_at: 1,
        }),
    }
}

#[test]
fn rejects_every_schedule_shape_and_bound_violation() {
    assert!(validate_schedule_well_formed(&valid_schedule()));

    let mut schedule = valid_schedule();
    schedule.committed_at = MAX_TIME + 1;
    assert!(!validate_schedule_well_formed(&schedule));

    let mut schedule = valid_schedule();
    schedule.schedule.as_mut().unwrap().id = "other".to_string();
    assert!(!validate_schedule_well_formed(&schedule));

    let mut schedule = valid_schedule();
    schedule.schedule.as_mut().unwrap().promise_timeout = MAX_TIME + 1;
    assert!(!validate_schedule_well_formed(&schedule));

    let mut schedule = valid_schedule();
    schedule.schedule.as_mut().unwrap().created_at = 11;
    assert!(!validate_schedule_well_formed(&schedule));

    let mut schedule = valid_schedule();
    schedule.schedule.as_mut().unwrap().created_at = 21;
    assert!(!validate_schedule_well_formed(&schedule));

    let mut schedule = valid_schedule();
    schedule.schedule.as_mut().unwrap().last_run_at = Some(0);
    assert!(!validate_schedule_well_formed(&schedule));

    let mut schedule = valid_schedule();
    schedule.schedule.as_mut().unwrap().last_run_at = Some(20);
    assert!(!validate_schedule_well_formed(&schedule));

    let mut schedule = valid_schedule();
    schedule.schedule.as_mut().unwrap().promise_tags = vec![
        ("resonate:target".to_string(), "worker".to_string()),
        ("resonate:timer".to_string(), "true".to_string()),
    ];
    assert!(!validate_schedule_well_formed(&schedule));

    let mut schedule = valid_schedule();
    schedule.next_wake_at = Some(21);
    assert!(!validate_schedule_well_formed(&schedule));

    let mut schedule = valid_schedule();
    schedule.schedule = None;
    assert!(!validate_schedule_well_formed(&schedule));
}

