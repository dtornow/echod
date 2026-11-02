//! The concrete world: the nodes and the store Rover starts from, the shell
//! around a node, and the store's conditional write.

use echod_logic::types::{Etag, StoreCall, StoreError, StoreOutcome};
use echod_world::model::{
    route_effects, ClientRequest, Effect, Fleet, Incoming, Local, Message, Model, Pid, Store,
};
use echod_rover::rover::{ProcessEvent, RoverModel};

fn node(local: &Local) -> &echod_world::model::Node {
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

#[test]
fn the_shell_forwards_a_request_and_keeps_its_wake() {
    let world = Model.world(&Fleet::new(1, true));
    let (pid, state) = world.process[0].clone();
    let mut armed = node(&state).clone();
    armed.wake = Some(40);
    let request = ClientRequest {
        client: "c".into(),
        id: 7,
        kind: "create".into(),
    };
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
    let node = node(&stepped[0].state);
    assert_eq!(node.logic.clock, 3);
    assert_eq!(node.next_request, 2);
    assert_eq!(node.wake, Some(40));
    assert!(stepped[0].send.is_empty());
}

#[test]
fn stop_ends_the_loop_and_a_wake_replaces_only_the_shell() {
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

    let (wake, send) = route_effects(
        &[
            Effect::Wake { after_ms: 5 },
            Effect::Note,
            Effect::Reply { id: 1, status: 200 },
            Effect::Wake { after_ms: 9 },
            Effect::Store {
                op: 3,
                call: StoreCall::Delete { key: "n".into() },
            },
        ],
        10,
        Some(1),
    );
    assert_eq!(wake, Some(19));
    assert_eq!(
        send,
        vec![
            (Pid::Outside, Message::Reply { id: 1, status: 200 }),
            (
                Pid::Store,
                Message::StoreReq {
                    op: 3,
                    call: StoreCall::Delete { key: "n".into() }
                }
            ),
        ]
    );
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
        message: Message::Request(ClientRequest {
            client: "c".into(),
            id: 1,
            kind: "get".into(),
        }),
    };
    assert!(Model
        .step(&Pid::Store, &world.process[1].1, 0, &client)
        .is_empty());
}
