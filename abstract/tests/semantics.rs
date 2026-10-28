use echod_abstract::*;
use echod_abstract::state::{
    apply_effect, read_object, Object, PromiseObject, TaskObject,
};

fn text(s: &str) -> Text {
    Text { bytes: s.as_bytes().to_vec() }
}

fn id(origin: &str, suffix: &str) -> Ident {
    Ident { origin: text(origin), suffix: text(suffix) }
}

fn promise(state: PromiseState, timeout_at: u64) -> PromiseObject {
    PromiseObject {
        state,
        param: Value::empty(),
        value: Value::empty(),
        tags: vec![],
        timeout_at,
        created_at: 0,
        settled_at: None,
        callbacks: vec![],
        listeners: vec![],
    }
}

#[test]
fn set_promise_prepends_and_keeps_the_task_face() {
    let a = id("o", "a");
    let b = id("o", "b");
    let task = TaskObject {
        state: TaskState::Pending,
        version: 7,
        ttl: None,
        pid: None,
        lease_timeout_at: None,
        retry_timeout_at: Some(1),
        resumes: vec![],
    };
    let state = State {
        objects: vec![
            Object { id: a.clone(), promise: promise(PromiseState::Pending, 10), task: None },
            Object { id: b.clone(), promise: promise(PromiseState::Pending, 10), task: Some(task) },
        ],
        schedules: vec![],
        outbox: vec![],
    };

    let out = apply_effect(
        state,
        Effect::SetPromise(b.clone(), promise(PromiseState::Resolved, 10)),
    );

    assert_eq!(out.objects.len(), 2);
    assert_eq!(out.objects[0].id, b);
    assert_eq!(out.objects[1].id, a);
    assert_eq!(out.objects[0].task.as_ref().unwrap().version, 7);
}

#[test]
fn first_matching_tag_wins() {
    let tags = vec![
        Tag { key: text("resonate:timer"), value: text("false") },
        Tag { key: text("resonate:timer"), value: text("true") },
    ];
    assert!(!tags_is_timer(&tags));
}

#[test]
fn view_projects_without_emitting_materialization() {
    let x = id("o", "x");
    let state = State {
        objects: vec![Object {
            id: x.clone(),
            promise: promise(PromiseState::Pending, 5),
            task: None,
        }],
        schedules: vec![],
        outbox: vec![],
    };

    let view = read_object(&state, &x, 6, false);
    assert_eq!(view.object.unwrap().promise.state, PromiseState::RejectedTimedout);
    assert!(view.effects.is_empty());

    let touch = read_object(&state, &x, 6, true);
    assert_eq!(touch.effects.len(), 1);
}

#[test]
fn set_task_for_absent_object_is_a_noop() {
    let state = State::new();
    let task = TaskObject {
        state: TaskState::Pending,
        version: 0,
        ttl: None,
        pid: None,
        lease_timeout_at: None,
        retry_timeout_at: Some(0),
        resumes: vec![],
    };
    let out = apply_effect(state, Effect::SetTask(id("o", "missing"), task));
    assert!(out.objects.is_empty());
}

#[test]
fn upsert_filter_removes_every_duplicate_without_reordering_others() {
    let x = id("o", "x");
    let a = id("o", "a");
    let b = id("o", "b");
    let state = State {
        objects: vec![
            Object { id: a.clone(), promise: promise(PromiseState::Pending, 9), task: None },
            Object { id: x.clone(), promise: promise(PromiseState::Pending, 9), task: None },
            Object { id: b.clone(), promise: promise(PromiseState::Pending, 9), task: None },
            Object { id: x.clone(), promise: promise(PromiseState::Rejected, 9), task: None },
        ],
        schedules: vec![],
        outbox: vec![],
    };
    let out = apply_effect(
        state,
        Effect::SetPromise(x.clone(), promise(PromiseState::Resolved, 9)),
    );
    assert_eq!(out.objects.iter().map(|o| o.id.clone()).collect::<Vec<_>>(), vec![x, a, b]);
}
