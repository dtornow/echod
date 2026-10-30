use echod::store::{call, Etag, MemoryStore, Read, Store, StoreCall, StoreError, StoreOutcome};
use echod_concrete::raw::{
    ConditionalRead, Environment, Failure, Key, Operation, RawStore, Response,
};

fn key(value: &str) -> Key {
    Key::new(value.as_bytes().to_vec())
}

fn runtime(response: Response) -> StoreOutcome {
    fn etag(version: u64) -> Etag {
        Etag(version.to_string())
    }
    fn text(key: Key) -> String {
        String::from_utf8(key.bytes).unwrap()
    }

    match response {
        Response::Got(object) => StoreOutcome::Got(
            object.map(|object| (object.bytes, etag(object.version))),
        ),
        Response::Read(ConditionalRead::Body(object)) =>
            StoreOutcome::Read(Read::Body(object.bytes, etag(object.version))),
        Response::Read(ConditionalRead::NotModified) =>
            StoreOutcome::Read(Read::NotModified),
        Response::Read(ConditionalRead::Absent) =>
            StoreOutcome::Read(Read::Absent),
        Response::Written(version) => StoreOutcome::Written(etag(version)),
        Response::Done => StoreOutcome::Done,
        Response::Listed(keys) =>
            StoreOutcome::Listed(keys.into_iter().map(text).collect()),
        Response::Failed(Failure::Refused) =>
            StoreOutcome::Failed(StoreError::PreconditionFailed),
        Response::Failed(Failure::Unavailable) =>
            StoreOutcome::Failed(StoreError::Unavailable("unavailable".into())),
        Response::InvalidChoice =>
            panic!("normal raw operations cannot be invalid"),
    }
}

async fn assert_normal_step(
    memory: &MemoryStore,
    raw: &mut RawStore,
    call_value: StoreCall,
    operation: Operation,
) {
    let actual = call(memory, call_value).await;
    let expected = runtime(raw.execute(operation, Environment::Normal));
    assert_eq!(actual, expected);
}

#[tokio::test]
async fn trait_calls_conform_to_raw_operations() {
    let memory = MemoryStore::appendable();
    let mut raw = RawStore::new("memory".into());
    let document = key("wf/a");

    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::Get { key: "wf/a".into() },
        Operation::Get { key: document.clone() },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::PutIfNoneMatch {
            key: "wf/a".into(),
            body: b"one".to_vec(),
        },
        Operation::Create {
            key: document.clone(),
            bytes: b"one".to_vec(),
        },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::PutIfNoneMatch {
            key: "wf/a".into(),
            body: b"other".to_vec(),
        },
        Operation::Create {
            key: document.clone(),
            bytes: b"other".to_vec(),
        },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::GetIfNoneMatch {
            key: "wf/a".into(),
            etag: Etag("1".into()),
        },
        Operation::GetIfNoneMatch {
            key: document.clone(),
            version: 1,
        },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::PutIfMatch {
            key: "wf/a".into(),
            body: b"two".to_vec(),
            etag: Etag("1".into()),
        },
        Operation::Update {
            key: document.clone(),
            version: 1,
            bytes: b"two".to_vec(),
        },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::GetIfNoneMatch {
            key: "wf/a".into(),
            etag: Etag("1".into()),
        },
        Operation::GetIfNoneMatch {
            key: document.clone(),
            version: 1,
        },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::AppendIfMatch {
            key: "wf/a".into(),
            offset: 3,
            body: b"!".to_vec(),
            etag: Etag("2".into()),
        },
        Operation::Append {
            key: document.clone(),
            version: 2,
            offset: 3,
            bytes: b"!".to_vec(),
        },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::Put {
            key: "t/a/1".into(),
            body: Vec::new(),
        },
        Operation::Put {
            key: key("t/a/1"),
            bytes: Vec::new(),
        },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::Put {
            key: "t/b/1".into(),
            body: Vec::new(),
        },
        Operation::Put {
            key: key("t/b/1"),
            bytes: Vec::new(),
        },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::List {
            prefix: "t/".into(),
            max_keys: 1,
        },
        Operation::List {
            prefix: key("t/"),
            max_keys: 1,
        },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::ListPrefixes { prefix: "t/".into() },
        Operation::ListPrefixes { prefix: key("t/") },
    ).await;
    assert_normal_step(
        &memory,
        &mut raw,
        StoreCall::Delete { key: "wf/a".into() },
        Operation::Delete { key: document },
    ).await;
}

#[tokio::test]
async fn explicit_environment_is_the_raw_step_input() {
    let memory = MemoryStore::new();

    assert!(matches!(
        memory.execute_with_environment(
            StoreCall::Put {
                key: "k".into(),
                body: b"before".to_vec(),
            },
            Environment::FailBeforeApply,
        ),
        StoreOutcome::Failed(StoreError::Unavailable(_))
    ));
    assert_eq!(memory.get("k").await.unwrap(), None);

    assert!(matches!(
        memory.execute_with_environment(
            StoreCall::PutIfNoneMatch {
                key: "k".into(),
                body: b"landed".to_vec(),
            },
            Environment::ApplyButLostAck,
        ),
        StoreOutcome::Failed(StoreError::Unavailable(_))
    ));
    assert_eq!(
        memory.get("k").await.unwrap(),
        Some((b"landed".to_vec(), Etag("1".into())))
    );

    assert_eq!(
        memory.execute_with_environment(
            StoreCall::PutIfNoneMatch {
                key: "k".into(),
                body: b"retry".to_vec(),
            },
            Environment::Refused,
        ),
        StoreOutcome::Failed(StoreError::PreconditionFailed)
    );
}
