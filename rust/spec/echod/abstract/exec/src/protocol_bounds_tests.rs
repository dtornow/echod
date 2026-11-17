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
fn raw_document_fence_rejects_cross_origin_create() {
    assert_atomic(
        &empty_store(),
        Request::TaskFence(echod_types::TaskFenceReq {
            id: "a:ghost".to_string(),
            version: 0,
            action: echod_types::TaskFenceAction::Create(PromiseCreateReq {
                id: "d:y".to_string(),
                timeout_at: 1_000,
                param: Value::default(),
                tags: Vec::new(),
            }),
        }),
        400,
    );
}

#[test]
fn detached_fence_completion_preserves_the_committed_create() {
    let config = Config { retry_timeout: 50 };
    let h = Handlers(&config);
    for (version, expected) in [(None, 404), (Some(9), 409), (Some(1), 200)] {
        let create = PromiseCreateReq {
            id: "d:y".to_string(),
            timeout_at: 1_000,
            param: Value::default(),
            tags: Vec::new(),
        };
        let mut origin = empty_store();
        if version.is_some() {
            let mut parent = create.clone();
            parent.id = "a:t".to_string();
            parent.tags = tags(&[("resonate:target", "poll://w")]);
            origin = h.handler(&Request::PromiseCreate(parent), &origin, 10).remove(0).next;
            origin = h.handler(
                &Request::TaskAcquire(TaskAcquireReq {
                    id: "a:t".to_string(), version: 0, pid: "w".to_string(), ttl: 500,
                }), &origin, 10,
            ).remove(0).next;
        }
        let created = h.handler(&Request::PromiseCreate(create.clone()), &origin, 10).remove(0);
        let inner = match created.resp {
            Response::Promise(inner) => inner,
            _ => panic!("create must return a promise"),
        };
        let pending = crate::state::DetachedFence {
            call: echod_types::Call {
                client: "client".to_string(),
                id: 7,
                request: Request::TaskFence(TaskFenceReq {
                    id: "a:t".to_string(), version: version.unwrap_or(0),
                    action: TaskFenceAction::Create(create),
                }),
            },
            check: echod_types::TaskFenceCheckReq {
                id: "a:t".to_string(), version: version.unwrap_or(0),
            },
            inner: inner.clone(),
            now: 10,
        };
        let completed = h.detached_fence(&pending, &created.next).remove(0);
        assert_eq!(completed.next, created.next);
        assert!(completed.work.is_empty());
        assert!(completed.send.is_empty());
        assert_eq!(completed.resp, Response::TaskFence(echod_types::TaskFenceRes {
            status: expected,
            action: if expected == 200 { Some(echod_types::TaskFenceInnerRes::Create(inner.clone())) } else { None },
        }));
        let settled = h.handler(
            &Request::PromiseSettle(echod_types::PromiseSettleReq {
                id: "d:y".to_string(),
                state: PromiseState::Resolved,
                value: Value::default(),
            }),
            &created.next,
            11,
        ).remove(0);
        let after_interleaving = h.detached_fence(&pending, &settled.next).remove(0);
        assert_eq!(after_interleaving.next, settled.next);
        assert_eq!(after_interleaving.resp, completed.resp);
    }
}

#[test]
fn timed_request_sweeps_before_create_without_sweeping_new_work() {
    use crate::requests::{admit_timed, timed_request_outcomes};
    let config = Config { retry_timeout: 0 };
    let h = Handlers(&config);
    let current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
        id: "a:old".into(), timeout_at: 1_000, param: Value::default(),
        tags: tags(&[("resonate:target", "poll://w")]),
    }), &empty_store(), 0).remove(0).next;
    let work = admit_timed(echod_types::protocol::TimedCall {
        call: echod_types::Call { client: "client".into(), id: 7, request: Request::PromiseCreate(PromiseCreateReq {
            id: "a:new".into(), timeout_at: 1_000, param: Value::default(),
            tags: tags(&[("resonate:target", "poll://w")]),
        }) },
        offered_at: 7, pinned: true,
    }, 100);
    let result = timed_request_outcomes(&config, &work, &current, 30).remove(0);
    assert_eq!(status(&result.resp), 200);
    assert_eq!(result.send, vec![echod_types::Dispatch::Execute { id: "a:old".into(), version: 0 }]);
    assert!(result.work.is_empty());
    assert_eq!(result.next.promises.get(&"a:new".into()).unwrap().created_at, 30);
    assert_eq!(result.next.tasks.get(&"a:new".into()).unwrap().retry_timeout_at, Some(30));
    assert_eq!(work.admitted_at, 7);
}

#[test]
fn timed_schedule_request_leaves_due_schedules_and_workflows_alone() {
    use crate::requests::{admit_timed, timed_request_outcomes};
    let config = Config { retry_timeout: 0 };
    let h = Handlers(&config);
    let current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
        id: "a:old".into(), timeout_at: 1_000, param: Value::default(),
        tags: tags(&[("resonate:target", "poll://w")]),
    }), &empty_store(), 0).remove(0).next;
    let created = h.handler(&Request::ScheduleCreate(ScheduleCreateReq {
        id: "a:tick".into(), cron: "* * * * * *".into(),
        promise_id: "tick-{{.timestamp}}".into(), promise_timeout: 100,
        promise_param: Value::default(), promise_tags: Vec::new(), next_run_at: 0,
    }), &current, 0).remove(0);
    assert_eq!(status(&created.resp), 200);
    let work = admit_timed(echod_types::protocol::TimedCall {
        call: echod_types::Call { client: "client".into(), id: 7, request: Request::ScheduleGet(echod_types::ScheduleGetReq { id: "a:tick".into() }) },
        offered_at: 7, pinned: true,
    }, 100);
    let result = timed_request_outcomes(&config, &work, &created.next, 30).remove(0);
    assert_eq!(status(&result.resp), 200);
    assert_eq!(result.next, created.next);
    assert!(result.send.is_empty());
    assert!(result.work.is_empty());
}

#[test]
fn admitted_work_is_evaluated_later_against_the_current_document_time() {
    use crate::requests::{admit_timed, timed_evaluation_time, timed_handler_outcomes};
    let config = Config { retry_timeout: 50 };
    let create = PromiseCreateReq {
        id: "a:later".into(), timeout_at: 1_000, param: Value::default(), tags: Vec::new(),
    };
    let work = admit_timed(echod_types::protocol::TimedCall {
        call: echod_types::Call { client: "client".into(), id: 7, request: Request::PromiseCreate(create.clone()) },
        offered_at: 7, pinned: true,
    }, 20);
    assert_eq!(work.admitted_at, 7);
    let mut anchor = create;
    anchor.id = "a:anchor".into();
    let current = Handlers(&config).handler(&Request::PromiseCreate(anchor.clone()), &empty_store(), 20).remove(0).next;
    assert_eq!(timed_evaluation_time(&work, 20), 20);
    let first = timed_handler_outcomes(&config, &work, &current, 20).remove(0);
    assert!(matches!(first.resp, Response::Promise(r) if r.promise.as_ref().unwrap().created_at == 20));
    anchor.id = "a:racer".into();
    let reread = Handlers(&config).handler(&Request::PromiseCreate(anchor), &current, 30).remove(0).next;
    let retried = timed_handler_outcomes(&config, &work, &reread, 30).remove(0);
    assert!(matches!(retried.resp, Response::Promise(r) if r.promise.as_ref().unwrap().created_at == 30));
    assert_eq!(work.admitted_at, 7);
    let unpinned = admit_timed(echod_types::protocol::TimedCall { pinned: false, ..work.call.clone() }, 20);
    assert_eq!(unpinned.admitted_at, 20);
    assert_eq!(timed_evaluation_time(&unpinned, 30), 30);
}

#[test]
fn timed_detached_work_retains_saved_time_and_current_committed_state() {
    use crate::requests::{admit_timed, continue_timed, timed_evaluation_time, timed_request_outcomes};
    let config = Config { retry_timeout: 50 };
    let h = Handlers(&config);
    let create = PromiseCreateReq { id: "b:child".into(), timeout_at: 1_000, param: Value::default(), tags: Vec::new() };
    let work = admit_timed(echod_types::protocol::TimedCall {
        call: echod_types::Call { client: "client".into(), id: 7, request: Request::TaskFence(TaskFenceReq {
            id: "a:t".into(), version: 1, action: TaskFenceAction::Create(create.clone()),
        }) },
        offered_at: 7, pinned: true,
    }, 20);
    let created = timed_request_outcomes(&config, &work, &empty_store(), 0).remove(0);
    assert!(matches!(&created.resp, Response::Promise(r) if r.promise.as_ref().unwrap().created_at == 7));
    let check = continue_timed(&work, &created.resp).unwrap();
    assert_eq!(check.call, work.call);
    assert_eq!(check.admitted_at, 7);
    let settled = h.handler(&Request::PromiseSettle(echod_types::PromiseSettleReq {
        id: create.id, state: PromiseState::Resolved, value: Value::default(),
    }), &created.next, 30).remove(0).next;
    let missing = timed_request_outcomes(&config, &check, &settled, 20).remove(0);
    assert_eq!(status(&missing.resp), 404);
    assert_eq!(missing.next, settled);
    let parent = PromiseCreateReq { id: "a:t".into(), timeout_at: 1_000, param: Value::default(), tags: tags(&[("resonate:target", "poll://w")]) };
    let current = h.handler(&Request::PromiseCreate(parent.clone()), &settled, 20).remove(0).next;
    let current = h.handler(&Request::TaskAcquire(TaskAcquireReq {
        id: parent.id.clone(), version: 0, pid: "w".into(), ttl: 100,
    }), &current, 20).remove(0).next;
    assert_eq!(timed_evaluation_time(&check, 20), 20);
    let completed = timed_request_outcomes(&config, &check, &current, 20).remove(0);
    assert_eq!(completed.next, current);
    assert!(matches!(completed.resp, Response::TaskFence(r) if r.status == 200 && matches!(&r.action,
        Some(echod_types::TaskFenceInnerRes::Create(inner)) if inner.promise.as_ref().unwrap().state == PromiseState::Pending)));
    assert_eq!(check.admitted_at, 7);
    let parent_settled = h.handler(&Request::PromiseSettle(echod_types::PromiseSettleReq {
        id: parent.id, state: PromiseState::Resolved, value: Value::default(),
    }), &current, 30).remove(0).next;
    let failed = timed_request_outcomes(&config, &check, &parent_settled, 30).remove(0);
    assert_eq!(status(&failed.resp), 409);
    assert_eq!(failed.next, parent_settled);
    assert_eq!(failed.next.promises.get(&"b:child".into()), settled.promises.get(&"b:child".into()));
}

#[test]
fn pre_sweep_projection_releases_and_offers_once_but_timeout_takes_priority() {
    let config = Config { retry_timeout: 50 };
    let h = Handlers(&config);
    let id = "a:t".to_string();
    let created = h.handler(&Request::PromiseCreate(PromiseCreateReq {
        id: id.clone(), timeout_at: 100, param: Value::default(),
        tags: tags(&[("resonate:target", "poll://w")]),
    }), &empty_store(), 20).remove(0).next;
    let acquired = h.handler(&Request::TaskAcquire(TaskAcquireReq {
        id: id.clone(), version: 0, pid: "w".into(), ttl: 10,
    }), &created, 20).remove(0).next;
    let projected = h.project_timed_key(&acquired, &id, 30);
    let task = projected.next.tasks.get(&id).unwrap();
    assert_eq!(task.state, echod_types::TaskState::Pending);
    assert_eq!(task.retry_timeout_at, Some(80));
    assert_eq!(task.pid, None);
    assert_eq!(projected.send, vec![echod_types::Dispatch::Execute { id: id.clone(), version: 1 }]);
    assert!(projected.work.is_empty());
    let repeated = h.project_timed_key(&projected.next, &id, 30);
    assert_eq!(repeated.next, projected.next);
    assert!(repeated.send.is_empty());
    let expired = h.project_timed_key(&acquired, &id, 100);
    assert_eq!(expired.next.tasks.get(&id).unwrap().state, echod_types::TaskState::Fulfilled);
    assert_eq!(expired.next.promises.get(&id).unwrap().state, PromiseState::RejectedTimedout);
    assert!(expired.send.is_empty());
    assert!(expired.work.is_empty());
}

#[test]
fn pre_sweep_projection_visits_the_finite_workset_without_refiring_zero_delay_retries() {
    let config = Config { retry_timeout: 0 };
    let h = Handlers(&config);
    let mut current = empty_store();
    let keys: Vec<String> = (0..130).map(|i| format!("a:{i:03}")).collect();
    for id in keys.iter().rev() {
        current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
            id: id.clone(), timeout_at: 100, param: Value::default(),
            tags: tags(&[("resonate:target", "poll://w")]),
        }), &current, 20).remove(0).next;
    }
    let other = "ab:unrelated".to_string();
    current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
        id: other.clone(), timeout_at: 100, param: Value::default(),
        tags: tags(&[("resonate:target", "poll://w")]),
    }), &current, 20).remove(0).next;
    let (projected, sends) = h.project_timed_origin(&current, &"a:request".into(), 20);
    assert_eq!(sends.len(), keys.len());
    assert_eq!(projected.tasks.get(&other), current.tasks.get(&other));
    assert_eq!(projected.promises.get(&other), current.promises.get(&other));
    for (id, send) in keys.iter().zip(&sends) {
        assert_eq!(send, &echod_types::Dispatch::Execute { id: id.clone(), version: 0 });
        assert_eq!(projected.tasks.get(id).unwrap().retry_timeout_at, Some(20));
    }
}

#[test]
fn callback_drain_offers_a_resumed_task_once_even_with_zero_retry_delay() {
    for retry_timeout in [0, 50] {
        let config = Config { retry_timeout };
        let h = Handlers(&config);
        let task = "a:t".to_string();
        let awaited = ["a:w1".to_string(), "a:w2".to_string()];
        let mut current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
            id: task.clone(), timeout_at: 100, param: Value::default(),
            tags: tags(&[("resonate:target", "poll://w")]),
        }), &empty_store(), 10).remove(0).next;
        for id in &awaited {
            current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
                id: id.clone(), timeout_at: 100, param: Value::default(),
                tags: tags(&[("resonate:external", "true")]),
            }), &current, 10).remove(0).next;
        }
        current = h.handler(&Request::TaskAcquire(TaskAcquireReq {
            id: task.clone(), version: 0, pid: "w".into(), ttl: 50,
        }), &current, 10).remove(0).next;
        let suspended = h.handler(&Request::TaskSuspend(echod_types::TaskSuspendReq {
            id: task.clone(), version: 1,
            actions: awaited.iter().map(|id| echod_types::PromiseRegisterCallbackReq {
                awaited: id.clone(), awaiter: task.clone(),
            }).collect(),
        }), &current, 10).remove(0);
        assert_eq!(status(&suspended.resp), 200);
        current = suspended.next;
        for id in &awaited {
            current = h.handler(&Request::PromiseSettle(echod_types::PromiseSettleReq {
                id: id.clone(), state: PromiseState::Resolved, value: Value::default(),
            }), &current, 20).remove(0).next;
        }
        let (projected, offers) = h.project_timed_origin(&current, &task, 20);
        assert!(offers.is_empty());
        let (resumed, offers) = h.drain_timed_callback(&projected, &awaited[0], &task, 20);
        assert_eq!(offers, vec![echod_types::Dispatch::Execute { id: task.clone(), version: 1 }]);
        assert_eq!(resumed.tasks.get(&task).unwrap().retry_timeout_at, Some(20 + retry_timeout));
        let (completed, offers) = h.drain_timed_callback(&resumed, &awaited[1], &task, 20);
        assert!(offers.is_empty());
        assert_eq!(completed.tasks.get(&task).unwrap().resumes, awaited.to_vec());
        let (bulk, bulk_sends) = h.bulk_timed_origin(&current, &task, 20);
        assert_eq!(bulk, completed);
        assert_eq!(bulk_sends, vec![echod_types::Dispatch::Execute { id: task.clone(), version: 1 }]);
        let (reverse_first, _) = h.drain_timed_callback(&projected, &awaited[1], &task, 20);
        let (reverse_completed, _) = h.drain_timed_callback(&reverse_first, &awaited[0], &task, 20);
        assert_eq!(reverse_completed.tasks.get(&task).unwrap().resumes, vec![awaited[1].clone(), awaited[0].clone()]);
        assert_ne!(reverse_completed, completed);
        for id in &awaited {
            assert!(!completed.promises.get(id).unwrap().callbacks.contains(&task));
        }
        let (duplicate, offers) = h.drain_timed_callback(&completed, &awaited[0], &task, 20);
        assert_eq!(duplicate, completed);
        assert!(offers.is_empty());
    }
}

#[test]
fn bulk_sweep_projects_every_object_then_callbacks_then_listeners() {
    let config = Config { retry_timeout: 0 };
    let h = Handlers(&config);
    let awaited = "a:z".to_string();
    let waiter = "a:t".to_string();
    let address = "https://receiver.invalid/result".to_string();
    let mut current = empty_store();
    for id in ["a:a", "a:t", "b:outside"] {
        current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
            id: id.into(), timeout_at: 100, param: Value::default(),
            tags: tags(&[("resonate:target", "poll://w")]),
        }), &current, 10).remove(0).next;
    }
    current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
        id: awaited.clone(), timeout_at: 20, param: Value::default(),
        tags: tags(&[("resonate:external", "true")]),
    }), &current, 10).remove(0).next;
    current = h.handler(&Request::PromiseRegisterListener(echod_types::PromiseRegisterListenerReq {
        awaited: awaited.clone(), address: address.clone(),
    }), &current, 10).remove(0).next;
    current = h.handler(&Request::TaskAcquire(TaskAcquireReq {
        id: waiter.clone(), version: 0, pid: "w".into(), ttl: 50,
    }), &current, 10).remove(0).next;
    current = h.handler(&Request::TaskSuspend(echod_types::TaskSuspendReq {
        id: waiter.clone(), version: 1,
        actions: vec![echod_types::PromiseRegisterCallbackReq { awaited: awaited.clone(), awaiter: waiter.clone() }],
    }), &current, 10).remove(0).next;
    let expected = h.handler(&Request::PromiseGet(echod_types::PromiseGetReq { id: awaited.clone() }), &current, 20).remove(0);
    let record = match expected.resp { Response::Promise(r) => r.promise.unwrap(), _ => panic!("expected promise") };
    let (completed, sends) = h.bulk_timed_origin(&current, &waiter, 20);
    assert_eq!(sends, vec![
        echod_types::Dispatch::Execute { id: "a:a".into(), version: 0 },
        echod_types::Dispatch::Execute { id: waiter.clone(), version: 1 },
        echod_types::Dispatch::Unblock { address, promise: record },
    ]);
    assert_eq!(completed.tasks.get(&waiter).unwrap().resumes, vec![awaited.clone()]);
    assert_eq!(completed.tasks.get(&waiter).unwrap().retry_timeout_at, Some(20));
    assert!(completed.promises.get(&awaited).unwrap().callbacks.to_vec().is_empty());
    assert!(completed.promises.get(&awaited).unwrap().listeners.to_vec().is_empty());
    assert_eq!(completed.tasks.get(&"b:outside".into()), current.tasks.get(&"b:outside".into()));
    assert_eq!(completed.promises.get(&"b:outside".into()), current.promises.get(&"b:outside".into()));
}

#[test]
fn listener_drain_retains_each_address_and_the_full_settled_record() {
    let config = Config { retry_timeout: 50 };
    let h = Handlers(&config);
    let id = "a:result".to_string();
    let addresses = vec!["https://receiver.invalid/b".to_string(), "https://receiver.invalid/a".to_string()];
    let mut current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
        id: id.clone(), timeout_at: 100,
        param: Value { headers: tags(&[("content-type", "text/plain")]), data: Some("request-data".into()) },
        tags: tags(&[("resonate:external", "true"), ("tenant", "example")]),
    }), &empty_store(), 10).remove(0).next;
    for address in &addresses {
        let registered = h.handler(&Request::PromiseRegisterListener(echod_types::PromiseRegisterListenerReq {
            awaited: id.clone(), address: address.clone(),
        }), &current, 10).remove(0);
        assert_eq!(status(&registered.resp), 200);
        current = registered.next;
    }
    let settled = h.handler(&Request::PromiseSettle(echod_types::PromiseSettleReq {
        id: id.clone(), state: PromiseState::Resolved,
        value: Value { headers: tags(&[("result-type", "text")]), data: Some("response-data".into()) },
    }), &current, 20).remove(0);
    let record = match settled.resp { Response::Promise(r) => r.promise.unwrap(), _ => panic!("expected promise") };
    let (completed, sends) = h.drain_timed_listener_plan(&settled.next, &id, &addresses, 20);
    assert_eq!(sends, addresses.iter().map(|address| echod_types::Dispatch::Unblock {
        address: address.clone(), promise: record.clone(),
    }).collect::<Vec<_>>());
    assert!(completed.promises.get(&id).unwrap().listeners.to_vec().is_empty());
    let (canonical, canonical_sends) = h.drain_timed_listeners(&settled.next, &id, 20);
    assert_eq!(canonical, completed);
    assert_eq!(canonical_sends, sends.iter().rev().cloned().collect::<Vec<_>>());
    let (bulk, bulk_sends) = h.bulk_timed_origin(&settled.next, &id, 20);
    assert_eq!(bulk, completed);
    assert_eq!(bulk_sends, canonical_sends);
    let (duplicate, sends) = h.drain_timed_listener_plan(&completed, &id, &addresses, 20);
    assert_eq!(duplicate, completed);
    assert!(sends.is_empty());
}

#[test]
fn callback_plan_drains_every_waiter_without_revisiting_new_retry_offers() {
    let config = Config { retry_timeout: 0 };
    let h = Handlers(&config);
    let awaited = "a:result".to_string();
    let awaiters: Vec<String> = (0..65).rev().map(|i| format!("a:t{i:03}")).collect();
    let mut current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
        id: awaited.clone(), timeout_at: 100, param: Value::default(),
        tags: tags(&[("resonate:external", "true")]),
    }), &empty_store(), 10).remove(0).next;
    for id in &awaiters {
        current = h.handler(&Request::PromiseCreate(PromiseCreateReq {
            id: id.clone(), timeout_at: 100, param: Value::default(),
            tags: tags(&[("resonate:target", "poll://w")]),
        }), &current, 10).remove(0).next;
        current = h.handler(&Request::TaskAcquire(TaskAcquireReq {
            id: id.clone(), version: 0, pid: "w".into(), ttl: 50,
        }), &current, 10).remove(0).next;
        let suspended = h.handler(&Request::TaskSuspend(echod_types::TaskSuspendReq {
            id: id.clone(), version: 1,
            actions: vec![echod_types::PromiseRegisterCallbackReq { awaited: awaited.clone(), awaiter: id.clone() }],
        }), &current, 10).remove(0);
        assert_eq!(status(&suspended.resp), 200);
        current = suspended.next;
    }
    current = h.handler(&Request::PromiseSettle(echod_types::PromiseSettleReq {
        id: awaited.clone(), state: PromiseState::Resolved, value: Value::default(),
    }), &current, 20).remove(0).next;
    let (projected, offers) = h.project_timed_origin(&current, &awaited, 20);
    assert!(offers.is_empty());
    let (completed, sends) = h.drain_timed_callback_plan(&projected, &awaited, &awaiters, 20);
    assert_eq!(sends, awaiters.iter().map(|id| echod_types::Dispatch::Execute { id: id.clone(), version: 1 }).collect::<Vec<_>>());
    assert!(completed.promises.get(&awaited).unwrap().callbacks.to_vec().is_empty());
    let (canonical, canonical_sends) = h.drain_timed_callbacks(&projected, &awaited, 20);
    assert_eq!(canonical, completed);
    assert_eq!(canonical_sends, sends.iter().rev().cloned().collect::<Vec<_>>());
    let (bulk, bulk_sends) = h.bulk_timed_origin(&current, &awaited, 20);
    assert_eq!(bulk, completed);
    assert_eq!(bulk_sends, canonical_sends);
    for id in &awaiters {
        let task = completed.tasks.get(id).unwrap();
        assert_eq!(task.state, TaskState::Pending);
        assert_eq!(task.resumes, vec![awaited.clone()]);
        assert_eq!(task.retry_timeout_at, Some(20));
    }
}

#[test]
fn rover_detached_creates_interleave_and_keep_correlated_failures() {
    use echod_types::{Call, Message, Output, PromiseSettleReq};
    use echod_abstract_spec::rover::Pid;
    use rover_spec::rover::comm::ProcessEvent;
    let config = Config { retry_timeout: 50 };
    let initial = crate::rover::initial(&config).remove(0).1;
    let event = |id, destination: &str| ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(Call {
            client: "client".to_string(),
            id,
            request: Request::TaskFence(TaskFenceReq {
                id: "a:missing".to_string(), version: 0,
                action: TaskFenceAction::Create(PromiseCreateReq {
                    id: destination.to_string(), timeout_at: 1_000,
                    param: Value::default(), tags: Vec::new(),
                }),
            }),
        }),
    };
    let results = initial.on_event(&config, 10, &event(7, "d:first"));
    assert_eq!(results.len(), 3);
    assert!(results[0].send.is_empty());
    assert_eq!(results[0].state.detached.len(), 1);
    assert!(results[1].state.store.promises.get(&"d:first".to_string()).is_some());
    assert!(results[1].state.detached.is_empty());
    assert!(results[2].state.store.promises.get(&"d:first".to_string()).is_none());
    for failure in &results[1..] {
        assert!(matches!(&failure.send[0].1, Message::Output(Output::Response {
            client, id: 7, response,
        }) if client == "client" && status(response) == 503));
    }
    let pending = results[0].state.on_event(&config, 10, &event(8, "e:second")).remove(0).state;
    assert_eq!(pending.detached.len(), 2);
    let settle = ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(Call {
            client: "other".to_string(), id: 9,
            request: Request::PromiseSettle(PromiseSettleReq {
                id: "d:first".to_string(), state: PromiseState::Resolved, value: Value::default(),
            }),
        }),
    };
    let settled = pending.on_event(&config, 11, &settle).remove(0).state;
    assert_eq!(settled.detached.len(), 2);
    let completions = settled.on_event(&config, 12, &ProcessEvent::Timeout);
    assert_eq!(completions.len(), 4);
    for (i, result) in completions.iter().enumerate() {
        assert_eq!(result.state.store, settled.store);
        assert_eq!(result.state.detached.len(), 1);
        let expected_id = if i < 2 { 7 } else { 8 };
        let expected_status = if i % 2 == 0 { 404 } else { 503 };
        assert!(matches!(&result.send[0].1, Message::Output(Output::Response {
            client, id, response,
        }) if client == "client" && *id == expected_id && status(response) == expected_status));
        assert_eq!(result.state.detached[0].call.id, if expected_id == 7 { 8 } else { 7 });
    }
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
