use echod_codec::bridge::*;
use echod_codec::frame::FORMAT_VERSION;
use echod_codec::primitives::{decode_bool, decode_option_blob, encode_u64};
use echod_codec::types::*;
use echod_kernel::{PromiseState, TaskState};

fn text(value: &str) -> echod_codec::text::Text {
    string_to_text(&value.to_string())
}

fn kernel_promise() -> echod_kernel::Promise {
    echod_kernel::Promise {
        id: "订单:α".into(),
        state: PromiseState::Resolved,
        tags: vec![
            ("tenant".into(), "東京".into()),
            ("emoji".into(), "🦀".into()),
        ],
        param: echod_kernel::Value {
            headers: vec![("content-type".into(), "text/plain; charset=utf-8".into())],
            data: Some("héllo".into()),
        },
        value: echod_kernel::Value {
            headers: vec![],
            data: Some("готово".into()),
        },
        timeout_at: u64::MAX,
        created_at: 42,
        settled_at: Some(99),
        callbacks: vec!["回调:1".into()],
        listeners: vec!["https://例.example/✓".into()],
        task: Some(echod_kernel::Task {
            state: TaskState::Fulfilled,
            version: 7,
            ttl: Some(5000),
            pid: Some("worker-λ".into()),
            lease_timeout_at: None,
            retry_timeout_at: Some(88),
            resumes: vec!["a".into(), "β".into()],
        }),
    }
}

#[test]
fn header_announcement_membership_round_trip() {
    let header = Header {
        stamp: u64::MAX,
        nonce: 17,
    };
    assert_eq!(
        decode_header(&encode_header(&header).unwrap()).unwrap(),
        header
    );

    let announcement = Announcement {
        id: text("node-東京"),
        url: text("https://例.example/🦀"),
        at: 123,
    };
    assert_eq!(
        decode_announcement(&encode_announcement(&announcement).unwrap()).unwrap(),
        announcement,
    );

    let membership = Membership {
        epoch: 9,
        members: vec![text("alpha"), text("β"), text("节点")],
    };
    assert_eq!(
        decode_membership(&encode_membership(&membership).unwrap()).unwrap(),
        membership,
    );
}

#[test]
fn kernel_rows_round_trip_with_unicode() {
    let promise = kernel_promise();
    let promise_bytes = encode_promise(&promise).unwrap();
    let promise_after = decode_promise(&promise_bytes).unwrap();
    assert_eq!(promise_model(&promise_after), promise_model(&promise));

    let schedule = echod_kernel::Schedule {
        id: "计划:日".into(),
        cron: "0 0 * * *".into(),
        promise_id: "订单:{{timestamp}}".into(),
        promise_timeout: 10_000,
        promise_param: echod_kernel::Value {
            headers: vec![("语言".into(), "日本語".into())],
            data: Some("payload 🦀".into()),
        },
        promise_tags: vec![("kind".into(), "定期".into())],
        next_run_at: 1234,
        last_run_at: Some(1000),
        created_at: 1,
    };
    let schedule_bytes = encode_schedule(&schedule).unwrap();
    let schedule_after = decode_schedule(&schedule_bytes).unwrap();
    assert_eq!(schedule_model(&schedule_after), schedule_model(&schedule));
}

#[test]
fn every_store_key_variant_round_trips() {
    let keys = vec![
        StoreKey::Document(text("订单")),
        StoreKey::Schedule(text("计划")),
        StoreKey::TimerOrigin {
            bucket: 100,
            deadline: 123,
            origin: text("来源"),
            token: u64::MAX,
            by: text("节点-a"),
        },
        StoreKey::TimerSchedule {
            bucket: 200,
            deadline: 222,
            id: text("计划"),
            token: 3,
            by: text("node-b"),
        },
        StoreKey::Node(text("节点")),
        StoreKey::Membership,
    ];
    for key in keys {
        assert_eq!(
            decode_store_key(&encode_store_key(&key).unwrap()).unwrap(),
            key
        );
    }
}

#[test]
fn format_is_canonical_and_rejects_bad_envelopes() {
    let header = Header { stamp: 1, nonce: 2 };
    let bytes = encode_header(&header).unwrap();
    assert_eq!(&bytes[..4], b"ECHO");
    assert_eq!(bytes[4], FORMAT_VERSION);
    assert_eq!(encode_header(&header).unwrap(), bytes);

    let mut wrong_version = bytes.clone();
    wrong_version[4] = FORMAT_VERSION + 1;
    assert!(decode_header(&wrong_version).is_err());

    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(decode_header(&trailing).is_err());

    let mut wrong_kind = bytes;
    wrong_kind[5] = 255;
    assert!(decode_header(&wrong_kind).is_err());
}

#[test]
fn invalid_utf8_and_noncanonical_tags_are_rejected() {
    let invalid_announcement_fields = vec![vec![0xff], b"url".to_vec(), encode_u64(0)];
    let invalid = echod_codec::record::encode_record(
        echod_codec::laws::KIND_ANNOUNCEMENT,
        &invalid_announcement_fields,
    )
    .unwrap();
    assert!(decode_announcement(&invalid).is_err());

    let malformed_bool = vec![2];
    assert_eq!(decode_bool(&malformed_bool), None);
    let malformed_option = vec![2];
    assert_eq!(decode_option_blob(&malformed_option), None);

    for invalid_utf8 in [
        vec![0xc0, 0x80],             // overlong NUL
        vec![0xed, 0xa0, 0x80],       // surrogate U+D800
        vec![0xf4, 0x90, 0x80, 0x80], // above U+10FFFF
        vec![0xe2, 0x82],             // truncated
    ] {
        assert!(echod_codec::text::Text::from_utf8(invalid_utf8).is_none());
    }
}

#[test]
fn utf8_validation_is_iterative_for_large_text() {
    let bytes = vec![b'a'; 200_000];
    assert_eq!(
        echod_codec::text::Text::from_utf8(bytes.clone())
            .unwrap()
            .bytes,
        bytes,
    );
}

#[test]
fn verified_string_and_kernel_bridges_round_trip() {
    let string = "nul:\0, 東京, 🦀, e\u{301}".to_string();
    assert_eq!(echod_codec::text::round_trip_string(string.clone()), string,);

    let promise = kernel_promise();
    let promise_before = promise_model(&promise);
    let promise_after = echod_codec::bridge::round_trip_kernel_promise(promise);
    assert_eq!(promise_model(&promise_after), promise_before);

    let schedule = echod_kernel::Schedule {
        id: "计划:日".into(),
        cron: "0 0 * * *".into(),
        promise_id: "订单:{{timestamp}}".into(),
        promise_timeout: 100,
        promise_param: echod_kernel::Value {
            headers: vec![("语言".into(), "日本語".into())],
            data: Some("🦀".into()),
        },
        promise_tags: vec![],
        next_run_at: 200,
        last_run_at: None,
        created_at: 1,
    };
    let schedule_before = schedule_model(&schedule);
    let schedule_after = echod_codec::bridge::round_trip_kernel_schedule(schedule);
    assert_eq!(schedule_model(&schedule_after), schedule_before);
}
