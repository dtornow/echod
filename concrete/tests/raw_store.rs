use echod_concrete::raw::{
    ConditionalRead, Environment, Failure, Key, Operation, RawStore, Response,
};

fn key(value: &str) -> Key {
    Key::new(value.as_bytes().to_vec())
}

fn normal(store: &mut RawStore, operation: Operation) -> Response {
    store.execute(operation, Environment::Normal)
}

#[test]
fn conditional_reads_creates_updates_and_appends_are_exact() {
    let mut store = RawStore::new("configured".to_owned());
    let document = key("wf/a");

    assert_eq!(
        normal(
            &mut store,
            Operation::Get {
                key: document.clone()
            }
        ),
        Response::Got(None),
    );
    assert_eq!(
        normal(
            &mut store,
            Operation::Create {
                key: document.clone(),
                bytes: b"one".to_vec(),
            },
        ),
        Response::Written(1),
    );
    assert_eq!(
        normal(
            &mut store,
            Operation::Create {
                key: document.clone(),
                bytes: b"other".to_vec(),
            },
        ),
        Response::Failed(Failure::Refused),
    );
    assert_eq!(
        normal(
            &mut store,
            Operation::GetIfNoneMatch {
                key: document.clone(),
                version: 1,
            },
        ),
        Response::Read(ConditionalRead::NotModified),
    );
    assert!(matches!(
        normal(
            &mut store,
            Operation::GetIfNoneMatch {
                key: document.clone(),
                version: 99,
            },
        ),
        Response::Read(ConditionalRead::Body(object))
            if object.bytes == b"one" && object.version == 1
    ));
    assert_eq!(
        normal(
            &mut store,
            Operation::Update {
                key: document.clone(),
                version: 99,
                bytes: b"two".to_vec(),
            },
        ),
        Response::Failed(Failure::Refused),
    );
    assert_eq!(
        normal(
            &mut store,
            Operation::Update {
                key: document.clone(),
                version: 1,
                bytes: b"two".to_vec(),
            },
        ),
        Response::Written(2),
    );
    assert_eq!(
        normal(
            &mut store,
            Operation::Append {
                key: document.clone(),
                version: 2,
                offset: 2,
                bytes: b"!".to_vec(),
            },
        ),
        Response::Failed(Failure::Refused),
    );
    assert_eq!(
        normal(
            &mut store,
            Operation::Append {
                key: document.clone(),
                version: 2,
                offset: 3,
                bytes: b"!".to_vec(),
            },
        ),
        Response::Written(3),
    );
    assert!(matches!(
        normal(&mut store, Operation::Get { key: document }),
        Response::Got(Some(object))
            if object.bytes == b"two!" && object.version == 3
    ));
}

#[test]
fn environmental_outcomes_make_unknown_application_explicit() {
    let mut store = RawStore::new("configured".to_owned());
    let document = key("wf/a");

    assert_eq!(
        store.execute(
            Operation::Put {
                key: document.clone(),
                bytes: b"before".to_vec(),
            },
            Environment::FailBeforeApply,
        ),
        Response::Failed(Failure::Unavailable),
    );
    assert_eq!(store.get(&document), None);

    assert_eq!(
        store.execute(
            Operation::Create {
                key: document.clone(),
                bytes: b"landed".to_vec(),
            },
            Environment::ApplyButLostAck,
        ),
        Response::Failed(Failure::Unavailable),
    );
    assert_eq!(store.get(&document).unwrap().bytes, b"landed");

    assert_eq!(
        store.execute(
            Operation::Create {
                key: document.clone(),
                bytes: b"retry".to_vec(),
            },
            Environment::Refused,
        ),
        Response::Failed(Failure::Refused),
    );
    assert_eq!(
        store.execute(
            Operation::Create {
                key: key("wf/fresh"),
                bytes: Vec::new(),
            },
            Environment::Refused,
        ),
        Response::InvalidChoice,
    );

    assert_eq!(
        normal(
            &mut store,
            Operation::Put {
                key: document.clone(),
                bytes: b"blind".to_vec(),
            },
        ),
        Response::Done,
    );
    assert_eq!(store.get(&document).unwrap().version, 2);
    assert_eq!(
        store.execute(
            Operation::Put {
                key: document.clone(),
                bytes: b"unknown".to_vec(),
            },
            Environment::ApplyButLostAck,
        ),
        Response::Failed(Failure::Unavailable),
    );
    assert_eq!(store.get(&document).unwrap().bytes, b"unknown");

    assert_eq!(
        store.execute(
            Operation::Delete {
                key: document.clone(),
            },
            Environment::ApplyButLostAck,
        ),
        Response::Failed(Failure::Unavailable),
    );
    assert_eq!(store.get(&document), None);
    assert_eq!(
        normal(&mut store, Operation::Delete { key: document }),
        Response::Done,
    );
}

#[test]
fn list_and_delimiter_list_are_sorted_exact_and_bounded() {
    let mut store = RawStore::new("configured".to_owned());
    for name in ["z", "t/b/2", "t/a/2", "t/root", "t/a/1", "t/b/1"] {
        assert_eq!(
            normal(
                &mut store,
                Operation::Put {
                    key: key(name),
                    bytes: Vec::new(),
                },
            ),
            Response::Done,
        );
    }

    assert_eq!(
        normal(
            &mut store,
            Operation::List {
                prefix: key("t/"),
                max_keys: 3,
            },
        ),
        Response::Listed(vec![key("t/a/1"), key("t/a/2"), key("t/b/1")]),
    );
    assert_eq!(
        normal(&mut store, Operation::ListPrefixes { prefix: key("t/") },),
        Response::Listed(vec![key("t/a/"), key("t/b/")]),
    );
}

#[test]
fn impossible_environment_choices_are_rejected_without_mutation() {
    let mut store = RawStore::new("configured".to_owned());
    assert_eq!(
        store.execute(
            Operation::Get {
                key: key("missing")
            },
            Environment::ApplyButLostAck,
        ),
        Response::InvalidChoice,
    );
    assert_eq!(
        store.execute(
            Operation::Put {
                key: key("k"),
                bytes: b"v".to_vec(),
            },
            Environment::Refused,
        ),
        Response::InvalidChoice,
    );
    assert!(store.entries.is_empty());
    assert_eq!(store.bucket, "configured");
}
