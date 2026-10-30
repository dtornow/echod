use echod_abstract::*;
use echod_abstract::state::{
    apply_effect, read_object, Object, PromiseObject, TaskObject,
};

fn text(s: &str) -> Text {
    Text { chars: s.chars().collect() }
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
fn task_view_projects_both_faces_without_writing_either() {
    let x = id("o", "task");
    let task = TaskObject {
        state: TaskState::Acquired,
        version: 1,
        ttl: Some(10),
        pid: Some(text("worker")),
        lease_timeout_at: Some(20),
        retry_timeout_at: None,
        resumes: vec![],
    };
    let state = State {
        objects: vec![Object {
            id: x.clone(),
            promise: promise(PromiseState::Pending, 5),
            task: Some(task),
        }],
        schedules: vec![],
        outbox: vec![],
    };

    let view = echod_abstract::state::read_task_object(&state, &x, 6, false);
    let projected = view.object.unwrap();
    assert_eq!(projected.promise.state, PromiseState::RejectedTimedout);
    assert_eq!(projected.task.unwrap().state, TaskState::Fulfilled);
    assert!(view.effects.is_empty());

    let touch = echod_abstract::state::read_task_object(&state, &x, 6, true);
    assert_eq!(touch.effects.len(), 2);
}

#[test]
fn object_view_projects_task_without_emitting_materialization() {
    let x = id("o", "object-task");
    let task = TaskObject {
        state: TaskState::Pending,
        version: 0,
        ttl: None,
        pid: None,
        lease_timeout_at: None,
        retry_timeout_at: Some(0),
        resumes: vec![],
    };
    let state = State {
        objects: vec![Object {
            id: x.clone(),
            promise: promise(PromiseState::Pending, 5),
            task: Some(task),
        }],
        schedules: vec![],
        outbox: vec![],
    };

    let view = read_object(&state, &x, 6, false);
    let projected = view.object.unwrap();
    assert_eq!(projected.promise.state, PromiseState::RejectedTimedout);
    assert_eq!(projected.task.unwrap().state, TaskState::Fulfilled);
    assert!(view.effects.is_empty());

    let touch = read_object(&state, &x, 6, true);
    assert_eq!(touch.effects.len(), 2);
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

// Option B: the implementation's distributed semantics are authoritative. ----

fn tag(k: &str, v: &str) -> Tag {
    Tag { key: text(k), value: text(v) }
}

fn tag_map(tags: &Tags) -> Vec<(String, String)> {
    tags.iter()
        .map(|t| (t.key.chars.iter().collect(), t.value.chars.iter().collect()))
        .collect()
}

fn config() -> Config {
    Config { retry_timeout: 100 }
}

fn schedule_state() -> State {
    let create = ScheduleCreateReq {
        id: id("tick", ""),
        cron: text("* * * * * *"),
        promise_id: id("o", "tick-{{.timestamp}}"),
        promise_timeout: 5_000,
        promise_param: Value::empty(),
        promise_tags: vec![tag("resonate:target", "sim://w"), tag("resonate:schedule", "stale")],
        next_run_at: 2_000,
    };
    let made = handle_external(&State::new(), ExternalAction::ScheduleCreate(create), 1_000, false);
    apply_all(State::new(), made.effects)
}

fn occurrence() -> Occurrence {
    Occurrence { at: 2_000, promise_id: id("o", "tick-2000") }
}

#[test]
fn schedule_fire_creates_the_promise_and_leaves_the_schedule_alone() {
    let state = schedule_state();
    let effects = handle_internal(
        &state,
        InternalAction::ScheduleFire(ScheduleFireReq { schedule: id("tick", ""), occurrence: occurrence() }),
        2_000,
        &config(),
    );
    assert!(effects.iter().all(|e| !matches!(e, Effect::SetSchedule(_))));
    let state = apply_all(state, effects);
    let o = state.objects.iter().find(|o| o.id == id("o", "tick-2000")).expect("promise");
    assert_eq!(o.promise.created_at, 2_000);
    assert_eq!(o.promise.timeout_at, 7_000);
    assert!(o.task.is_some(), "a targeted template fires a runnable promise");
    assert_eq!(state.schedules[0].next_run_at, 2_000);
    assert_eq!(state.schedules[0].last_run_at, None);
    // the template's stale stamp is dropped; the lineage is stamped afresh
    assert_eq!(
        tag_map(&o.promise.tags),
        vec![
            ("resonate:target".into(), "sim://w".into()),
            ("resonate:schedule".into(), "tick".into()),
            ("resonate:origin".into(), "o:tick-2000".into()),
            ("resonate:branch".into(), "o:tick-2000".into()),
            ("resonate:parent".into(), "o:tick-2000".into()),
            ("resonate:prefix".into(), "o:tick-2000".into()),
        ]
    );
}

#[test]
fn schedule_advance_waits_for_the_promise() {
    let state = schedule_state();
    let advance = |state: &State| {
        handle_internal(
            state,
            InternalAction::ScheduleAdvance(ScheduleAdvanceReq {
                schedule: id("tick", ""),
                occurrence: occurrence(),
                next_run_at: 3_000,
            }),
            2_500,
            &config(),
        )
    };
    assert!(advance(&state).is_empty(), "no promise yet: the schedule must not move");
    let fire = handle_internal(
        &state,
        InternalAction::ScheduleFire(ScheduleFireReq { schedule: id("tick", ""), occurrence: occurrence() }),
        2_000,
        &config(),
    );
    let state = apply_all(state, fire);
    let effects = advance(&state);
    assert_eq!(effects.len(), 1);
    let state = apply_all(state, effects);
    assert_eq!(state.schedules[0].last_run_at, Some(2_000));
    assert_eq!(state.schedules[0].next_run_at, 3_000);
    // a second fire of the same occurrence is a no-op: the schedule has moved on
    let again = handle_internal(
        &state,
        InternalAction::ScheduleFire(ScheduleFireReq { schedule: id("tick", ""), occurrence: occurrence() }),
        2_500,
        &config(),
    );
    assert!(again.is_empty());
}

#[test]
fn schedule_fire_is_idempotent_after_a_crash_between_the_two_steps() {
    let state = schedule_state();
    let fire = || InternalAction::ScheduleFire(ScheduleFireReq { schedule: id("tick", ""), occurrence: occurrence() });
    let state = apply_all(state.clone(), handle_internal(&state, fire(), 2_000, &config()));
    let objects = state.objects.len();
    let second = handle_internal(&state, fire(), 2_100, &config());
    let state = apply_all(state, second);
    assert_eq!(state.objects.len(), objects, "createIfAbsent: one promise per occurrence");
}

#[test]
fn a_targeted_timer_is_accepted_as_a_timer_alone() {
    let create = PromiseCreateReq {
        id: id("o", "sleep"),
        timeout_at: 10,
        param: Value::empty(),
        tags: vec![tag("resonate:timer", "true"), tag("resonate:target", "sim://w")],
    };
    let made = handle_external(&State::new(), ExternalAction::PromiseCreate(create), 1, false);
    let Response::PromiseCreate(res) = made.response else { panic!("shape") };
    assert_eq!(res.status, 200);
    let record = res.promise.expect("record");
    assert_eq!(tag_map(&record.tags), vec![("resonate:timer".into(), "true".into())]);
    let state = apply_all(State::new(), made.effects);
    assert!(state.objects[0].task.is_none(), "a timer carries no task");
}

#[test]
fn searches_are_refused() {
    let state = State::new();
    let r = handle_external(
        &state,
        ExternalAction::PromiseSearch(PromiseSearchReq { state: None, tags: vec![], limit: None, cursor: None }),
        0,
        false,
    );
    let Response::PromiseSearch(res) = r.response else { panic!("shape") };
    assert_eq!(res.status, 403);
}

#[test]
fn retry_rearms_on_the_tasks_own_grid() {
    let create = PromiseCreateReq {
        id: id("o", "job"),
        timeout_at: 100_000,
        param: Value::empty(),
        tags: vec![tag("resonate:target", "sim://w")],
    };
    let made = handle_external(&State::new(), ExternalAction::PromiseCreate(create), 1_000, false);
    let state = apply_all(State::new(), made.effects);
    assert_eq!(state.objects[0].task.as_ref().unwrap().retry_timeout_at, Some(1_000));
    // dispatched late, at 1_250, the next offer is 1_100 + ... on the grid: 1_300
    let effects = handle_internal(
        &state,
        InternalAction::TaskRetryTimeout(TaskRetryTimeoutReq { id: id("o", "job") }),
        1_250,
        &config(),
    );
    let state = apply_all(state, effects);
    assert_eq!(state.objects[0].task.as_ref().unwrap().retry_timeout_at, Some(1_300));
    assert_eq!(state.outbox.len(), 1);
}

#[test]
fn lease_lapse_offers_from_the_leases_end() {
    let create = TaskCreateReq {
        pid: text("p1"),
        ttl: 500,
        action: PromiseCreateReq {
            id: id("o", "job"),
            timeout_at: 100_000,
            param: Value::empty(),
            tags: vec![tag("resonate:target", "sim://w")],
        },
    };
    let made = handle_external(&State::new(), ExternalAction::TaskCreate(create), 1_000, false);
    let state = apply_all(State::new(), made.effects);
    assert_eq!(state.objects[0].task.as_ref().unwrap().lease_timeout_at, Some(1_500));
    let effects = handle_internal(
        &state,
        InternalAction::TaskLeaseTimeout(TaskLeaseTimeoutReq { id: id("o", "job") }),
        1_900,
        &config(),
    );
    let state = apply_all(state, effects);
    let task = state.objects[0].task.as_ref().unwrap();
    assert_eq!(task.state, TaskState::Pending);
    assert_eq!(task.retry_timeout_at, Some(1_500));
}

#[test]
fn a_detached_fence_is_two_steps_and_a_stale_check_keeps_the_promise() {
    // task in origin `a`, acquired at version 1
    let create = TaskCreateReq {
        pid: text("p1"),
        ttl: 500,
        action: PromiseCreateReq {
            id: id("a", "root"),
            timeout_at: 100_000,
            param: Value::empty(),
            tags: vec![tag("resonate:target", "sim://w")],
        },
    };
    let made = handle_external(&State::new(), ExternalAction::TaskCreate(create), 1_000, false);
    let state = apply_all(State::new(), made.effects);

    let fence = ExternalAction::TaskFence(TaskFenceReq {
        id: id("a", "root"),
        version: 1,
        action: TaskFenceAction::Create(PromiseCreateReq {
            id: id("b", "child"),
            timeout_at: 100_000,
            param: Value::empty(),
            tags: vec![],
        }),
    });
    let Request::Detached { create, check } = decompose(fence) else { panic!("cross-origin create must detach") };
    assert_eq!(check.id, id("a", "root"));
    assert_eq!(check.version, 1);

    // step one: the create lands on its own
    let first = handle_external(&state, ExternalAction::PromiseCreate(create), 1_100, false);
    let Response::PromiseCreate(inner) = first.response else { panic!("shape") };
    let state = apply_all(state, first.effects);
    assert!(state.objects.iter().any(|o| o.id == id("b", "child")));

    // something interleaves: the lease lapses and the task is released
    let lapse = handle_internal(
        &state,
        InternalAction::TaskLeaseTimeout(TaskLeaseTimeoutReq { id: id("a", "root") }),
        1_600,
        &config(),
    );
    let state = apply_all(state, lapse);

    // step two: the check is stale; the promise stays
    let second = handle_external(&state, ExternalAction::TaskFenceCheck(check), 1_700, false);
    let Response::TaskFenceCheck(status) = second.response else { panic!("shape") };
    let fence_res = compose_detached(inner, status);
    assert_eq!(fence_res.status, 409);
    assert!(fence_res.action.is_none());
    let state = apply_all(state, second.effects);
    assert!(state.objects.iter().any(|o| o.id == id("b", "child")));
}

#[test]
fn a_same_origin_fence_stays_whole() {
    let fence = ExternalAction::TaskFence(TaskFenceReq {
        id: id("a", "root"),
        version: 1,
        action: TaskFenceAction::Create(PromiseCreateReq {
            id: id("a", "child"),
            timeout_at: 100_000,
            param: Value::empty(),
            tags: vec![],
        }),
    });
    assert!(matches!(decompose(fence), Request::Whole(ExternalAction::TaskFence(_))));
}
