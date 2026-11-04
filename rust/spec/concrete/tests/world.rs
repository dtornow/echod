//! The concrete world: the nodes and the store Rover starts from, one node
//! flight, and the store's conditional write.

use echod_abstract::{Call, Dispatch, Output};
use echod_concrete::model::{Fleet, Incoming, Local, Message, Model, Pid, Store};
use echod_concrete::{
    Etag, PromiseCreateReq, PromiseGetReq, PromiseRegisterListenerReq, PromiseRes,
    PromiseSettleReq, PromiseState, Request, Response, StoreCall, StoreError, StoreOutcome, Value,
};
use echod_rover::rover::{ProcessEvent, RoverModel};

fn node(local: &Local) -> &echod_concrete::model::Node {
    match local {
        Local::Node(node) => node,
        Local::Store(_) => panic!("expected a node"),
    }
}

fn store(local: &Local) -> &Store {
    match local {
        Local::Store(store) => store,
        Local::Node(_) => panic!("expected the store"),
    }
}

#[test]
fn the_world_is_the_nodes_then_the_store() {
    let world = Model.world(&Fleet::new(2, true));
    assert_eq!(world.now, 0);
    assert!(world.network.is_empty());
    assert_eq!(world.process.len(), 3);
    assert_eq!(world.process[0].0, Pid::Node(0));
    assert_eq!(world.process[1].0, Pid::Node(1));
    assert_eq!(world.process[2].0, Pid::Store);
    assert!(world.process.iter().all(|(pid, _)| *pid != Pid::Outside));

    let first = node(&world.process[0].1);
    let second = node(&world.process[1].1);
    assert!(first.logic.loops && second.logic.loops);
    assert_eq!(first.logic.clock, 0);
    assert!(!first.logic.stopping);
    assert_eq!(first.next_request, 1);
    assert_eq!(first.wake, None);
    assert!(store(&world.process[2].1).entries.is_empty());

    let quiet = Model.world(&Fleet::new(1, false));
    assert!(!node(&quiet.process[0].1).logic.loops);
}

#[test]
fn rover_assembles_the_same_processes() {
    let config = Fleet::new(2, true);
    assert_eq!(Model.initial(&config), Model.world(&config).process);
    assert_eq!(Model.outside(), Pid::Outside);
    assert!(Model.injectable(&config, &Message::Stop));
    assert!(!Model.injectable(
        &config,
        &Message::StoreReq {
            op: 1,
            call: StoreCall::Get { key: "k".into() }
        },
    ));
}

#[test]
fn a_timeout_is_a_tick_only_when_a_wake_is_due() {
    let world = Model.world(&Fleet::new(1, true));
    let (pid, state) = &world.process[0];
    assert!(Model.step(pid, state, 5, &Incoming::Timeout).is_empty());

    let mut armed = node(state).clone();
    armed.wake = Some(10);
    let early = Model.step(pid, &Local::Node(armed.clone()), 9, &Incoming::Timeout);
    assert!(early.is_empty());

    let due = Model.step(pid, &Local::Node(armed), 10, &Incoming::Timeout);
    assert_eq!(due.len(), 1);
    let stepped = node(&due[0].state);
    assert_eq!(stepped.logic.clock, 10);
    assert_eq!(stepped.wake, None);
    assert!(due[0].send.is_empty());

    let through = Model.on_event(
        &Fleet::new(1, true),
        pid,
        &due[0].state,
        10,
        &ProcessEvent::Timeout,
    );
    assert!(through.is_empty());
}

fn call(id: u64, request: Request) -> Call {
    Call {
        client: "c".into(),
        id,
        request,
    }
}

fn deliver(
    node_pid: Pid,
    node_state: Local,
    store_state: Local,
    now: u64,
    event: &Incoming,
) -> (Local, Local, Vec<(Pid, Message)>) {
    let stepped = Model.step(&node_pid, &node_state, now, event);
    assert_eq!(stepped.len(), 1);
    let mut node_state = stepped[0].state.clone();
    let mut store_state = store_state;
    let mut send = stepped[0].send.clone();
    // A flight is one store round trip at a time. Answer it, then the node finishes.
    while let [(Pid::Store, Message::StoreReq { op, call })] = send.as_slice() {
        let stored = Model.step(
            &Pid::Store,
            &store_state,
            now,
            &Incoming::Receive {
                sender: node_pid,
                message: Message::StoreReq {
                    op: *op,
                    call: call.clone(),
                },
            },
        );
        assert_eq!(stored.len(), 1);
        store_state = stored[0].state.clone();
        let reply = stored[0].send[0].1.clone();
        let answered = Model.step(
            &node_pid,
            &node_state,
            now,
            &Incoming::Receive {
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
    let world = Model.world(&Fleet::new(1, true));
    let (pid, state) = world.process[0].clone();
    let mut armed = node(&state).clone();
    armed.wake = Some(40);
    let request = call(
        7,
        Request::PromiseGet(PromiseGetReq {
            id: "a:missing".into(),
        }),
    );
    let stepped = Model.step(
        &pid,
        &Local::Node(armed),
        3,
        &Incoming::Receive {
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
                call: StoreCall::Get { key: "o/a".into() },
            },
        )]
    );

    let (node_state, _, send) = deliver(
        pid,
        stepped[0].state.clone(),
        world.process[1].1.clone(),
        3,
        &Incoming::Receive {
            sender: Pid::Store,
            message: Message::StoreReply {
                op: 1,
                outcome: StoreOutcome::Got(None),
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
    let world = Model.world(&Fleet::new(1, true));
    let (pid, node_state) = world.process[0].clone();
    let store_state = world.process[1].1.clone();
    let create = call(
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
        &Incoming::Receive {
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
        &Incoming::Receive {
            sender: Pid::Outside,
            message: Message::Request(call(
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
                Some(echod_concrete::PromiseState::Pending)
            );
        }
        other => panic!("get reply {other:?}"),
    }
    assert_eq!(store(&store_state).entries.len(), 1);
    assert_eq!(node(&node_state).logic.clock, 6);
}

#[test]
fn stop_ends_the_loop() {
    let world = Model.world(&Fleet::new(1, true));
    let (pid, state) = world.process[0].clone();
    let stopped = Model.step(
        &pid,
        &state,
        4,
        &Incoming::Receive {
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
    let world = Model.world(&Fleet::new(1, false));
    let store = world.process[1].1.clone();
    let call = StoreCall::PutIfNoneMatch {
        key: "doc".into(),
        body: b"one".to_vec(),
    };
    let created = Model.step(
        &Pid::Store,
        &store,
        0,
        &Incoming::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq {
                op: 8,
                call: call.clone(),
            },
        },
    );
    assert_eq!(created.len(), 1);
    let tag = match &created[0].send[..] {
        [(
            Pid::Node(0),
            Message::StoreReply {
                op: 8,
                outcome: StoreOutcome::Written(tag),
            },
        )] => tag.clone(),
        other => panic!("reply {other:?}"),
    };

    let again = Model.step(
        &Pid::Store,
        &created[0].state,
        1,
        &Incoming::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq { op: 9, call },
        },
    );
    assert!(matches!(
        again[0].send[0].1,
        Message::StoreReply {
            outcome: StoreOutcome::Failed(StoreError::PreconditionFailed),
            ..
        }
    ));

    let wrong = StoreCall::PutIfMatch {
        key: "doc".into(),
        body: b"two".to_vec(),
        etag: Etag("nope".into()),
    };
    let rejected = Model.step(
        &Pid::Store,
        &created[0].state,
        1,
        &Incoming::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq {
                op: 10,
                call: wrong,
            },
        },
    );
    assert!(matches!(
        rejected[0].send[0].1,
        Message::StoreReply {
            outcome: StoreOutcome::Failed(StoreError::PreconditionFailed),
            ..
        }
    ));
    assert_eq!(rejected[0].state, created[0].state);

    let right = StoreCall::PutIfMatch {
        key: "doc".into(),
        body: b"two".to_vec(),
        etag: tag,
    };
    let wrote = Model.step(
        &Pid::Store,
        &created[0].state,
        2,
        &Incoming::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq {
                op: 11,
                call: right,
            },
        },
    );
    match &wrote[0].send[0].1 {
        Message::StoreReply {
            op: 11,
            outcome: StoreOutcome::Written(_),
        } => {}
        other => panic!("write {other:?}"),
    }
    match &wrote[0].state {
        Local::Store(stored) => {
            assert_eq!(stored.entries.len(), 1);
            assert_eq!(stored.entries[0].key, "doc");
            assert_eq!(stored.entries[0].body, b"two");
            assert_eq!(stored.entries[0].version, 2);
        }
        Local::Node(_) => panic!("store"),
    }
}

#[test]
fn a_node_ignores_a_store_request_and_a_store_ignores_a_client() {
    let world = Model.world(&Fleet::new(1, false));
    let (node_pid, node_state) = &world.process[0];
    let ask = Incoming::Receive {
        sender: Pid::Node(0),
        message: Message::StoreReq {
            op: 1,
            call: StoreCall::Get { key: "k".into() },
        },
    };
    assert!(Model.step(node_pid, node_state, 0, &ask).is_empty());
    let client = Incoming::Receive {
        sender: Pid::Outside,
        message: Message::Request(call(
            1,
            Request::PromiseGet(PromiseGetReq { id: "a:1".into() }),
        )),
    };
    assert!(Model
        .step(&Pid::Store, &world.process[1].1, 0, &client)
        .is_empty());
}

#[test]
fn a_due_retry_offers_the_task() {
    let world = Model.world(&Fleet::new(1, true));
    let (pid, node_state) = world.process[0].clone();
    let store_state = world.process[1].1.clone();
    let create = call(
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
        &Incoming::Receive {
            sender: Pid::Outside,
            message: Message::Request(create),
        },
    );
    assert_eq!(node(&node_state).wake, Some(5));
    let (node_state, _, send) = deliver(
        pid,
        node_state,
        store_state,
        5,
        &Incoming::Timeout,
    );
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
    let world = Model.world(&Fleet::new(1, true));
    let (pid, node_state) = world.process[0].clone();
    let store_state = world.process[1].1.clone();
    let (node_state, store_state, _) = deliver(
        pid,
        node_state,
        store_state,
        5,
        &Incoming::Receive {
            sender: Pid::Outside,
            message: Message::Request(call(
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
        &Incoming::Receive {
            sender: Pid::Outside,
            message: Message::Request(call(
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
        &Incoming::Receive {
            sender: Pid::Outside,
            message: Message::Request(call(
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
    let (_, _, send) = deliver(pid, node_state, store_state, 7, &Incoming::Timeout);
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
