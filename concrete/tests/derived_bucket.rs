use echod_codec::bridge::string_to_text;
use echod_codec::document::{encode_promise_segment, encode_schedule_segment};
use echod_codec::store_key_text::{encode_runtime_store_key, StringStoreKey};
use echod_codec::types::{Announcement, Header, Membership};
use echod_concrete::derived::decode_bucket;
use echod_concrete::raw::{Key, RawStore, Response};
use echod_kernel::{Promise, PromiseState, Schedule, Value};

const BUCKET_MS: u64 = 1_000;

fn text(value: &str) -> echod_codec::text::Text {
    string_to_text(&value.to_string())
}

fn key(prefix: &str, value: &StringStoreKey) -> String {
    encode_runtime_store_key(&prefix.to_string(), BUCKET_MS, value).unwrap()
}

fn put(store: &mut RawStore, key: String, body: Vec<u8>) {
    assert_eq!(store.put(Key::new(key.into_bytes()), body), Response::Done,);
}

fn promise(id: &str, state: PromiseState) -> Promise {
    Promise {
        id: id.into(),
        state,
        tags: vec![],
        param: Value {
            headers: vec![],
            data: None,
        },
        value: Value {
            headers: vec![],
            data: None,
        },
        timeout_at: 100,
        created_at: 1,
        settled_at: None,
        callbacks: vec![],
        listeners: vec![],
        task: None,
    }
}

fn schedule(id: &str) -> Schedule {
    Schedule {
        id: id.into(),
        cron: "* * * * *".into(),
        promise_id: "orders:{{timestamp}}".into(),
        promise_timeout: 50,
        promise_param: Value {
            headers: vec![],
            data: None,
        },
        promise_tags: vec![],
        next_run_at: 2_000,
        last_run_at: None,
        created_at: 1,
    }
}

#[test]
fn complete_bucket_decodes_keys_bodies_headers_rows_and_versions() {
    let prefix = "tenant".to_string();
    let mut store = RawStore::new("physical-bucket".into());

    let first = promise("orders:first", PromiseState::Pending);
    let second = promise("orders:second", PromiseState::Pending);
    let mut changed = first.clone();
    changed.state = PromiseState::Resolved;
    changed.settled_at = Some(20);
    let h1 = Header {
        stamp: 10,
        nonce: 11,
    };
    let h2 = Header {
        stamp: 20,
        nonce: 22,
    };
    let mut document = encode_promise_segment(&h1, &vec![first]).unwrap();
    document.extend_from_slice(&encode_promise_segment(&h2, &vec![changed, second]).unwrap());
    put(
        &mut store,
        key(&prefix, &StringStoreKey::Document("orders".into())),
        document,
    );

    put(
        &mut store,
        key(&prefix, &StringStoreKey::Schedule("daily".into())),
        encode_schedule_segment(&h1, &vec![schedule("daily")]).unwrap(),
    );

    let origin_timer = StringStoreKey::TimerOrigin {
        bucket: 2_000,
        deadline: 2_345,
        origin: "orders".into(),
        token: 0xab,
        by: "node-a".into(),
    };
    let origin_timer_key = key(&prefix, &origin_timer);
    put(&mut store, origin_timer_key.clone(), Vec::new());

    let schedule_timer = StringStoreKey::TimerSchedule {
        bucket: 3_000,
        deadline: 3_456,
        id: "daily".into(),
        token: 0xcd,
        by: "node-b".into(),
    };
    let schedule_timer_key = key(&prefix, &schedule_timer);
    put(&mut store, schedule_timer_key.clone(), Vec::new());

    let announcement = Announcement {
        id: text("node-a"),
        url: text("https://node-a.example"),
        at: 99,
    };
    put(
        &mut store,
        key(&prefix, &StringStoreKey::Node("node-a".into())),
        echod_codec::encode_announcement(&announcement).unwrap(),
    );

    let membership = Membership {
        epoch: 7,
        members: vec![text("node-a"), text("node-b")],
    };
    put(
        &mut store,
        key(&prefix, &StringStoreKey::Membership),
        echod_codec::encode_membership(&membership).unwrap(),
    );

    let bucket = decode_bucket(&store, &prefix, BUCKET_MS).unwrap();
    assert_eq!(bucket.origins.len(), 1);
    let origin = &bucket.origins[0];
    assert_eq!(origin.origin, "orders");
    assert_eq!((origin.stamp, origin.nonce, origin.version), (20, 22, 1));
    assert_eq!(
        origin
            .rows
            .iter()
            .map(|row| row.id.as_str())
            .collect::<Vec<_>>(),
        vec!["orders:first", "orders:second"],
    );
    assert_eq!(origin.rows[0].state, PromiseState::Resolved);

    assert_eq!(bucket.schedules.len(), 1);
    let schedules = &bucket.schedules[0];
    assert_eq!(schedules.id, "daily");
    assert_eq!(
        (schedules.stamp, schedules.nonce, schedules.version),
        (10, 11, 2)
    );
    assert_eq!(schedules.rows[0].schedule.id, "daily");

    assert_eq!(bucket.timers.len(), 2);
    assert_eq!(bucket.timers[0].key, origin_timer_key);
    assert_eq!(bucket.timers[0].target, "orders");
    assert!(!bucket.timers[0].schedule);
    assert_eq!(bucket.timers[1].key, schedule_timer_key);
    assert_eq!(bucket.timers[1].target, "daily");
    assert!(bucket.timers[1].schedule);

    assert_eq!(bucket.announcements.len(), 1);
    assert_eq!(bucket.announcements[0].id, "node-a");
    assert_eq!(bucket.announcements[0].url, "https://node-a.example");
    let membership = bucket.membership.unwrap();
    assert_eq!(membership.epoch, 7);
    assert_eq!(membership.members, vec!["node-a", "node-b"]);
}

#[test]
fn one_malformed_or_noncanonical_entry_rejects_the_entire_view() {
    let prefix = "tenant".to_string();
    let header = Header { stamp: 1, nonce: 2 };
    let valid_document =
        encode_promise_segment(&header, &vec![promise("orders:one", PromiseState::Pending)])
            .unwrap();

    let mut malformed_key = RawStore::new("bucket".into());
    put(
        &mut malformed_key,
        "tenant/wf/%6F".into(),
        valid_document.clone(),
    );
    assert!(decode_bucket(&malformed_key, &prefix, BUCKET_MS).is_err());

    let mut malformed_body = RawStore::new("bucket".into());
    put(
        &mut malformed_body,
        key(&prefix, &StringStoreKey::Document("orders".into())),
        valid_document,
    );
    put(
        &mut malformed_body,
        key(&prefix, &StringStoreKey::Node("node-a".into())),
        b"not an announcement".to_vec(),
    );
    assert!(decode_bucket(&malformed_body, &prefix, BUCKET_MS).is_err());

    let mut nonempty_timer = RawStore::new("bucket".into());
    put(
        &mut nonempty_timer,
        key(
            &prefix,
            &StringStoreKey::TimerOrigin {
                bucket: 1_000,
                deadline: 1_234,
                origin: "orders".into(),
                token: 1,
                by: "node-a".into(),
            },
        ),
        vec![0],
    );
    assert!(decode_bucket(&nonempty_timer, &prefix, BUCKET_MS).is_err());

    let mut headerless_document = RawStore::new("bucket".into());
    put(
        &mut headerless_document,
        key(&prefix, &StringStoreKey::Document("orders".into())),
        Vec::new(),
    );
    assert!(decode_bucket(&headerless_document, &prefix, BUCKET_MS,).is_err());
}
