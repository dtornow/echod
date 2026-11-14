//! The concrete world: the nodes and the store Rover starts from, one node
//! flight, and the store's conditional write.

use echod_abstract_spec::{Call, Dispatch, Output};
use crate::concrete::rover::{Config, Proc, Message, Pid, Spec};
use crate::concrete::store::Store;
use crate::concrete::{Etag, StoreReq, StoreError, StoreRes};
use echod_types::{
    PromiseCreateReq, PromiseGetReq, PromiseRegisterListenerReq, PromiseRes, PromiseSettleReq,
    PromiseState, Request, Response, Value,
};
use rover_spec::rover::comm::{BoundaryEvent, ProcessEvent};
use rover_exec::{
    check, exec, replay, Action, CheckConfig, Driver, Proc as _, ProcResult, Spec as _,
};

fn node(local: &Proc) -> &crate::concrete::document::Node {
    match local {
        Proc::Node(node) => node,
        Proc::Store(_) => panic!("expected a node"),
    }
}

fn store(local: &Proc) -> &Store {
    match local {
        Proc::Store(store) => store,
        Proc::Node(_) => panic!("expected the store"),
    }
}

/// One local step; the fleet does not enter it.
fn step(
    _pid: &Pid,
    state: &Proc,
    now: u64,
    event: &ProcessEvent<Pid, Message>,
) -> Vec<ProcResult<Proc>> {
    state.on_event(&Config::new(1, true), now, event)
}

#[test]
fn echod_concrete_exec_is_deterministic_and_certified() {
    let config = Config::new(1, true);
    let request = request(
        7,
        Request::PromiseGet(PromiseGetReq {
            id: "a:missing".into(),
        }),
    );
    let run = || {
        exec(
            &Spec,
            &config,
            5,
            |driver: Driver<'_, Spec>| match driver.step {
                0 => Some(Action::Inject {
                    recipient: Pid::Node(0),
                    at: 3,
                    message: Message::Request(request.clone()),
                }),
                1 => driver
                    .internal
                    .iter()
                    .find(|action| matches!(
                        action,
                        Action::Process {
                            process: Pid::Node(0),
                            event: ProcessEvent::Receive {
                                sender: Pid::Outside,
                                message: Message::Request(_),
                            },
                            ..
                        }
                    ))
                    .cloned(),
                2 => driver
                    .internal
                    .iter()
                    .find(|action| matches!(
                        action,
                        Action::Process {
                            process: Pid::Store,
                            event: ProcessEvent::Receive {
                                sender: Pid::Node(0),
                                message: Message::StoreReq { .. },
                            },
                            ..
                        }
                    ))
                    .cloned(),
                3 => driver
                    .internal
                    .iter()
                    .find(|action| matches!(
                        action,
                        Action::Process {
                            process: Pid::Node(0),
                            event: ProcessEvent::Receive {
                                sender: Pid::Store,
                                message: Message::StoreRes { .. },
                            },
                            ..
                        }
                    ))
                    .cloned(),
                4 => driver.observe.first().cloned(),
                _ => None,
            },
        )
        .expect("concrete execution")
    };

    let first = run();
    assert_eq!(first, run());
    assert!(matches!(
        first.trace.as_slice(),
        [
            BoundaryEvent::Input { .. },
            BoundaryEvent::Output {
                message: Message::Output(Output::Response { .. }),
                ..
            }
        ]
    ));
    assert_eq!(
        replay(
            &Spec,
            &config,
            &first.trace,
            &first.certificate,
        ),
        Ok(())
    );
    // This dev-only round trip checks the concrete spec named by the adapter.
    // The abstract model has distinct boundary types; relating those traces
    // belongs to the concrete refinement rather than this execution harness.
    assert!(check(
        &Spec,
        &config,
        &first.trace,
        CheckConfig::for_trace_len(first.trace.len()),
        |_, _, _| 0,
    )
    .is_some());
}

#[test]
fn the_world_is_the_nodes_then_the_store() {
    let world = Spec.initial(&Config::new(2, true));
    assert_eq!(world.len(), 3);
    assert_eq!(world[0].0, Pid::Node(0));
    assert_eq!(world[1].0, Pid::Node(1));
    assert_eq!(world[2].0, Pid::Store);
    assert!(world.iter().all(|(pid, _)| *pid != Pid::Outside));

    let first = node(&world[0].1);
    let second = node(&world[1].1);
    assert!(first.logic.loops && second.logic.loops);
    assert_eq!(first.logic.clock, 0);
    assert!(!first.logic.stopping);
    assert_eq!(first.next_request, 1);
    assert_eq!(first.wake, None);
    assert!(store(&world[2].1).entries.is_empty());

    let quiet = Spec.initial(&Config::new(1, false));
    assert!(!node(&quiet[0].1).logic.loops);
}

#[test]
fn the_outside_injects_requests_and_stop() {
    let config = Config::new(2, true);
    assert_eq!(Spec.outside(), Pid::Outside);
    assert!(Spec.injectable(&config, &Message::Stop));
    assert!(!Spec.injectable(
        &config,
        &Message::StoreReq {
            op: 1,
            request: StoreReq::Get { key: "k".into() }
        },
    ));
}

#[test]
fn a_timeout_is_a_tick_only_when_a_wake_is_due() {
    let world = Spec.initial(&Config::new(1, true));
    let (pid, state) = &world[0];
    assert!(step(pid, state, 5, &ProcessEvent::Timeout).is_empty());

    let mut armed = node(state).clone();
    armed.wake = Some(10);
    let early = step(pid, &Proc::Node(armed.clone()), 9, &ProcessEvent::Timeout);
    assert!(early.is_empty());

    let due = step(pid, &Proc::Node(armed), 10, &ProcessEvent::Timeout);
    assert_eq!(due.len(), 1);
    let stepped = node(&due[0].state);
    assert_eq!(stepped.logic.clock, 10);
    assert_eq!(stepped.wake, None);
    assert!(due[0].send.is_empty());
    assert!(step(pid, &due[0].state, 10, &ProcessEvent::Timeout).is_empty());
}

fn request(id: u64, request: Request) -> Call {
    Call {
        client: "c".into(),
        id,
        request,
    }
}

fn deliver(
    node_pid: Pid,
    node_state: Proc,
    store_state: Proc,
    now: u64,
    event: &ProcessEvent<Pid, Message>,
) -> (Proc, Proc, Vec<(Pid, Message)>) {
    let stepped = step(&node_pid, &node_state, now, event);
    assert_eq!(stepped.len(), 1);
    let mut node_state = stepped[0].state.clone();
    let mut store_state = store_state;
    let mut send = stepped[0].send.clone();
    // A flight is one store round trip at a time. Answer it, then the node finishes.
    while let [(Pid::Store, Message::StoreReq { op, request })] = send.as_slice() {
        let stored = step(
            &Pid::Store,
            &store_state,
            now,
            &ProcessEvent::Receive {
                sender: node_pid,
                message: Message::StoreReq {
                    op: *op,
                    request: request.clone(),
                },
            },
        );
        assert_eq!(stored.len(), 1);
        store_state = stored[0].state.clone();
        let reply = stored[0].send[0].1.clone();
        let answered = step(
            &node_pid,
            &node_state,
            now,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: reply,
            },
        );
        assert_eq!(answered.len(), 1);
        node_state = answered[0].state.clone();
        send = answered[0].send.clone();
    }
    (node_state, store_state, send)
}

#[test]
fn a_promise_get_loads_the_document_and_a_miss_is_404() {
    let world = Spec.initial(&Config::new(1, true));
    let (pid, state) = world[0].clone();
    let mut armed = node(&state).clone();
    armed.wake = Some(40);
    let request = request(
        7,
        Request::PromiseGet(PromiseGetReq {
            id: "a:missing".into(),
        }),
    );
    let stepped = step(
        &pid,
        &Proc::Node(armed),
        3,
        &ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(request),
        },
    );
    assert_eq!(stepped.len(), 1);
    let loaded = node(&stepped[0].state);
    assert_eq!(loaded.logic.clock, 3);
    assert_eq!(loaded.next_request, 2);
    assert_eq!(loaded.wake, None);
    assert_eq!(
        stepped[0].send,
        vec![(
            Pid::Store,
            Message::StoreReq {
                op: 1,
                request: StoreReq::Get { key: "o/a".into() },
            },
        )]
    );

    let (node_state, _, send) = deliver(
        pid,
        stepped[0].state.clone(),
        world[1].1.clone(),
        3,
        &ProcessEvent::Receive {
            sender: Pid::Store,
            message: Message::StoreRes {
                op: 1,
                response: StoreRes::Get { result: Ok(None) },
            },
        },
    );
    assert_eq!(node(&node_state).wake, None);
    assert_eq!(
        send,
        vec![(
            Pid::Outside,
            Message::Output(Output::Response {
                client: "c".into(),
                id: 7,
                response: Response::Promise(PromiseRes {
                    status: 404,
                    promise: None,
                }),
            }),
        )]
    );
}

#[test]
fn a_promise_create_lands_and_the_next_get_reads_it() {
    let world = Spec.initial(&Config::new(1, true));
    let (pid, node_state) = world[0].clone();
    let store_state = world[1].1.clone();
    let create = request(
        1,
        Request::PromiseCreate(PromiseCreateReq {
            id: "a:1".into(),
            timeout_at: 1_000,
            param: Value::empty(),
            tags: Vec::new(),
        }),
    );
    let (node_state, store_state, send) = deliver(
        pid,
        node_state,
        store_state,
        5,
        &ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(create),
        },
    );
    match &send[..] {
        [(
            Pid::Outside,
            Message::Output(Output::Response {
                client,
                id: 1,
                response: Response::Promise(body),
            }),
        )] if client == "c" => {
            assert_eq!(body.status, 200);
            assert_eq!(body.promise.as_ref().map(|p| p.id.as_str()), Some("a:1"));
            assert_eq!(body.promise.as_ref().map(|p| p.timeout_at), Some(1_000));
        }
        other => panic!("create reply {other:?}"),
    }
    assert_eq!(node(&node_state).wake, Some(1_000));
    assert_eq!(store(&store_state).entries.len(), 1);
    assert_eq!(store(&store_state).entries[0].key, "o/a");

    let (node_state, store_state, send) = deliver(
        pid,
        node_state,
        store_state,
        6,
        &ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(request(
                2,
                Request::PromiseGet(PromiseGetReq { id: "a:1".into() }),
            )),
        },
    );
    match &send[..] {
        [(
            Pid::Outside,
            Message::Output(Output::Response {
                client,
                id: 2,
                response: Response::Promise(body),
            }),
        )] if client == "c" => {
            assert_eq!(
                body.promise.as_ref().map(|p| p.state),
                Some(echod_types::PromiseState::Pending)
            );
        }
        other => panic!("get reply {other:?}"),
    }
    assert_eq!(store(&store_state).entries.len(), 1);
    assert_eq!(node(&node_state).logic.clock, 6);
}

#[test]
fn stop_ends_the_loop() {
    let world = Spec.initial(&Config::new(1, true));
    let (pid, state) = world[0].clone();
    let stopped = step(
        &pid,
        &state,
        4,
        &ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Stop,
        },
    );
    let node = node(&stopped[0].state);
    assert!(node.logic.stopping);
    assert!(!node.logic.loops);
    assert_eq!(node.logic.clock, 4);
    assert!(stopped[0].send.is_empty());
}

#[test]
fn the_store_commits_a_conditional_write_and_answers_the_node() {
    let world = Spec.initial(&Config::new(1, false));
    let store = world[1].1.clone();
    let request = StoreReq::PutIfNoneMatch {
        key: "doc".into(),
        body: b"one".to_vec(),
    };
    let created = step(
        &Pid::Store,
        &store,
        0,
        &ProcessEvent::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq {
                op: 8,
                request: request.clone(),
            },
        },
    );
    assert_eq!(created.len(), 1);
    let tag = match &created[0].send[..] {
        [(
            Pid::Node(0),
            Message::StoreRes {
                op: 8,
                response: StoreRes::PutIfNoneMatch { result: Ok(tag) },
            },
        )] => tag.clone(),
        other => panic!("reply {other:?}"),
    };

    let again = step(
        &Pid::Store,
        &created[0].state,
        1,
        &ProcessEvent::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq { op: 9, request },
        },
    );
    assert!(matches!(
        again[0].send[0].1,
        Message::StoreRes {
            response: StoreRes::PutIfNoneMatch { result: Err(StoreError::PreconditionFailed) },
            ..
        }
    ));

    let wrong = StoreReq::PutIfMatch {
        key: "doc".into(),
        body: b"two".to_vec(),
        etag: Etag("nope".into()),
    };
    let rejected = step(
        &Pid::Store,
        &created[0].state,
        1,
        &ProcessEvent::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq {
                op: 10,
                request: wrong,
            },
        },
    );
    assert!(matches!(
        rejected[0].send[0].1,
        Message::StoreRes {
            response: StoreRes::PutIfMatch { result: Err(StoreError::PreconditionFailed) },
            ..
        }
    ));
    match (&rejected[0].state, &created[0].state) {
        (Proc::Store(after), Proc::Store(before)) => {
            assert_eq!(after.entries, before.entries);
            assert!(after.seen.contains(&(Pid::Node(0), 10)));
        }
        _ => panic!("store"),
    }

    let right = StoreReq::PutIfMatch {
        key: "doc".into(),
        body: b"two".to_vec(),
        etag: tag,
    };
    let wrote = step(
        &Pid::Store,
        &created[0].state,
        2,
        &ProcessEvent::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq {
                op: 11,
                request: right,
            },
        },
    );
    match &wrote[0].send[0].1 {
        Message::StoreRes {
            op: 11,
            response: StoreRes::PutIfMatch { result: Ok(_) },
        } => {}
        other => panic!("write {other:?}"),
    }
    match &wrote[0].state {
        Proc::Store(stored) => {
            assert_eq!(stored.entries.len(), 1);
            assert_eq!(stored.entries[0].key, "doc");
            assert_eq!(stored.entries[0].body, b"two");
            assert_eq!(stored.entries[0].version, 2);
        }
        Proc::Node(_) => panic!("store"),
    }
}

#[test]
fn the_store_executes_each_op_once() {
    let world = Spec.initial(&Config::new(1, false));
    let store = world[1].1.clone();
    let put = ProcessEvent::Receive {
        sender: Pid::Node(0),
        message: Message::StoreReq {
            op: 3,
            request: StoreReq::PutIfNoneMatch {
                key: "doc".into(),
                body: b"one".to_vec(),
            },
        },
    };
    let first = step(&Pid::Store, &store, 0, &put);
    assert_eq!(first.len(), 1);
    assert_eq!(first[0].send.len(), 1);

    let again = step(&Pid::Store, &first[0].state, 1, &put);
    assert_eq!(again.len(), 1);
    assert!(again[0].send.is_empty());
    assert_eq!(again[0].state, first[0].state);

    let other_node = ProcessEvent::Receive {
        sender: Pid::Node(1),
        message: Message::StoreReq {
            op: 3,
            request: StoreReq::Get { key: "doc".into() },
        },
    };
    let read = step(&Pid::Store, &first[0].state, 2, &other_node);
    assert_eq!(read.len(), 1);
    assert_eq!(read[0].send.len(), 1);
}

#[test]
fn a_node_ignores_a_store_request_and_a_store_ignores_a_client() {
    let world = Spec.initial(&Config::new(1, false));
    let (node_pid, node_state) = &world[0];
    let ask = ProcessEvent::Receive {
        sender: Pid::Node(0),
        message: Message::StoreReq {
            op: 1,
            request: StoreReq::Get { key: "k".into() },
        },
    };
    assert!(step(node_pid, node_state, 0, &ask).is_empty());
    let client = ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(request(
            1,
            Request::PromiseGet(PromiseGetReq { id: "a:1".into() }),
        )),
    };
    assert!(step(&Pid::Store, &world[1].1, 0, &client).is_empty());
}

#[test]
fn a_due_retry_offers_the_task() {
    let world = Spec.initial(&Config::new(1, true));
    let (pid, node_state) = world[0].clone();
    let store_state = world[1].1.clone();
    let create = request(
        1,
        Request::PromiseCreate(PromiseCreateReq {
            id: "a:1".into(),
            timeout_at: 10_000,
            param: Value::empty(),
            tags: vec![("resonate:target".into(), "worker".into())],
        }),
    );
    let (node_state, store_state, _) = deliver(
        pid,
        node_state,
        store_state,
        5,
        &ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(create),
        },
    );
    assert_eq!(node(&node_state).wake, Some(5));
    let (node_state, _, send) = deliver(pid, node_state, store_state, 5, &ProcessEvent::Timeout);
    assert_eq!(
        send,
        vec![(
            Pid::Outside,
            Message::Output(Output::Dispatch(Dispatch::Execute {
                id: "a:1".into(),
                version: 0,
            })),
        )]
    );
    assert_eq!(node(&node_state).wake, Some(5_005));
}

#[test]
fn a_settled_listener_is_told() {
    let world = Spec.initial(&Config::new(1, true));
    let (pid, node_state) = world[0].clone();
    let store_state = world[1].1.clone();
    let (node_state, store_state, _) = deliver(
        pid,
        node_state,
        store_state,
        5,
        &ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(request(
                1,
                Request::PromiseCreate(PromiseCreateReq {
                    id: "a:1".into(),
                    timeout_at: 10_000,
                    param: Value::empty(),
                    tags: vec![("resonate:external".into(), "true".into())],
                }),
            )),
        },
    );
    let (node_state, store_state, _) = deliver(
        pid,
        node_state,
        store_state,
        6,
        &ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(request(
                2,
                Request::PromiseRegisterListener(PromiseRegisterListenerReq {
                    awaited: "a:1".into(),
                    address: "http://x".into(),
                }),
            )),
        },
    );
    let (node_state, store_state, _) = deliver(
        pid,
        node_state,
        store_state,
        7,
        &ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(request(
                3,
                Request::PromiseSettle(PromiseSettleReq {
                    id: "a:1".into(),
                    state: PromiseState::Resolved,
                    value: Value::empty(),
                }),
            )),
        },
    );
    assert_eq!(node(&node_state).wake, Some(7));
    let (_, _, send) = deliver(pid, node_state, store_state, 7, &ProcessEvent::Timeout);
    match &send[..] {
        [(
            Pid::Outside,
            Message::Output(Output::Dispatch(Dispatch::Unblock { address, promise })),
        )] => {
            assert_eq!(address, "http://x");
            assert_eq!(promise.id, "a:1");
            assert_eq!(promise.state, PromiseState::Resolved);
            assert_eq!(promise.settled_at, Some(7));
        }
        other => panic!("listener {other:?}"),
    }
}
