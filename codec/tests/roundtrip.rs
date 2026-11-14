use echod_codec::bridge::*;
use echod_codec::frame::FORMAT_VERSION;
use echod_codec::primitives::{decode_bool, decode_option_blob, encode_u64};
use echod_codec::types::*;
use echod_kernel::{PromiseState, TaskState};

#[path = "../../logic/src/keys.rs"]
#[allow(dead_code)]
mod existing_keys;

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

#[test]
fn appendable_promise_document_is_segmented_and_last_row_wins() {
    use echod_codec::document::*;

    let header1 = Header {
        stamp: 10,
        nonce: 1,
    };
    let header2 = Header {
        stamp: 20,
        nonce: 2,
    };
    let mut first = kernel_promise();
    first.id = "first".into();
    first.state = PromiseState::Pending;
    let mut changed = first.clone();
    changed.state = PromiseState::Resolved;
    changed.settled_at = Some(20);
    let mut second = kernel_promise();
    second.id = "second".into();

    let segment1 = encode_promise_segment(&header1, &vec![first]).unwrap();
    let segment2 =
        encode_promise_segment(&header2, &vec![changed.clone(), second.clone()]).unwrap();

    let (split1, rest) = split_frame(&[segment1.clone(), segment2.clone()].concat()).unwrap();
    assert_eq!(split1, segment1);
    assert_eq!(rest, segment2);

    let mut document = split1;
    document.extend_from_slice(&rest);
    let (last_header, rows) = decode_promise_document(&document).unwrap();
    assert_eq!(last_header, Some(header2.clone()));
    assert_eq!(rows.len(), 2);
    assert_eq!(promise_model(&rows[0]), promise_model(&changed));
    assert_eq!(promise_model(&rows[1]), promise_model(&second));

    let (segment_header, segment_rows) = decode_promise_segment(&rest).unwrap();
    assert_eq!(segment_header, header2);
    assert_eq!(segment_rows.len(), 2);
}

#[test]
fn promise_and_schedule_compaction_preserve_folded_documents() {
    use echod_codec::document::*;

    let h1 = Header {
        stamp: 1,
        nonce: 11,
    };
    let h2 = Header {
        stamp: 2,
        nonce: 22,
    };
    let h3 = Header {
        stamp: 3,
        nonce: 33,
    };

    let mut old = kernel_promise();
    old.id = "same".into();
    old.state = PromiseState::Pending;
    let mut newest = old.clone();
    newest.state = PromiseState::Rejected;
    newest.settled_at = Some(2);
    let mut promise_doc = encode_promise_segment(&h1, &vec![old]).unwrap();
    promise_doc.extend_from_slice(&encode_promise_segment(&h2, &vec![newest]).unwrap());
    let (_, before_promises) = decode_promise_document(&promise_doc).unwrap();
    let compacted = compact_promise_document(&promise_doc, &h3).unwrap();
    let (compact_header, after_promises) = decode_promise_document(&compacted).unwrap();
    assert_eq!(compact_header, Some(h3.clone()));
    assert_eq!(
        after_promises.iter().map(promise_model).collect::<Vec<_>>(),
        before_promises
            .iter()
            .map(promise_model)
            .collect::<Vec<_>>()
    );
    assert!(split_frame(&compacted).unwrap().1.is_empty());

    let schedule = echod_kernel::Schedule {
        id: "daily".into(),
        cron: "0 0 * * *".into(),
        promise_id: "promise".into(),
        promise_timeout: 10,
        promise_param: echod_kernel::Value {
            headers: vec![],
            data: None,
        },
        promise_tags: vec![],
        next_run_at: 100,
        last_run_at: None,
        created_at: 1,
    };
    let mut changed = schedule.clone();
    changed.next_run_at = 200;
    changed.last_run_at = Some(100);
    let mut schedule_doc = encode_schedule_segment(&h1, &vec![schedule]).unwrap();
    schedule_doc.extend_from_slice(&encode_schedule_segment(&h2, &vec![changed]).unwrap());
    let (_, before_schedules) = decode_schedule_document(&schedule_doc).unwrap();
    let compacted = compact_schedule_document(&schedule_doc, &h3).unwrap();
    let (compact_header, after_schedules) = decode_schedule_document(&compacted).unwrap();
    assert_eq!(compact_header, Some(h3));
    assert_eq!(
        after_schedules
            .iter()
            .map(schedule_model)
            .collect::<Vec<_>>(),
        before_schedules
            .iter()
            .map(schedule_model)
            .collect::<Vec<_>>()
    );
}

#[test]
fn document_decoder_rejects_truncated_and_malformed_segments() {
    use echod_codec::document::*;

    let header = Header { stamp: 1, nonce: 1 };
    let segment = encode_promise_segment(&header, &vec![kernel_promise()]).unwrap();
    for end in 1..segment.len() {
        assert!(decode_promise_document(&segment[..end].to_vec()).is_err());
    }

    let mut trailing = segment.clone();
    trailing.extend_from_slice(&[0x45, 0x43, 0x48]);
    assert!(decode_promise_document(&trailing).is_err());

    let schedule = echod_kernel::Schedule {
        id: "schedule".into(),
        cron: "* * * * *".into(),
        promise_id: "promise".into(),
        promise_timeout: 10,
        promise_param: echod_kernel::Value {
            headers: vec![],
            data: None,
        },
        promise_tags: vec![],
        next_run_at: 1,
        last_run_at: None,
        created_at: 1,
    };
    let wrong_kind = encode_schedule_segment(&header, &vec![schedule]).unwrap();
    assert!(decode_promise_document(&wrong_kind).is_err());
    assert!(decode_schedule_document(&segment).is_err());
}

#[test]
fn textual_store_keys_match_existing_keyspace() {
    use echod_codec::store_key_text::{
        class_of_text_key, decode_runtime_store_key, encode_runtime_store_key, KeyClass,
        StringStoreKey,
    };
    use existing_keys::KeySpace;

    for prefix in ["", "tenant", "tenant/", "租户/"] {
        let keyspace = KeySpace::new(prefix, 1_000);
        let cases = vec![
            (
                StringStoreKey::Document("订单:α/a_b@c~d%".into()),
                keyspace.doc_key("订单:α/a_b@c~d%"),
                KeyClass::Document,
            ),
            (
                StringStoreKey::Schedule("计划/東京:_@~%".into()),
                keyspace.sched_key("计划/東京:_@~%"),
                KeyClass::Schedule,
            ),
            (
                StringStoreKey::Node("节点/東京 %".into()),
                keyspace.node_key("节点/東京 %"),
                KeyClass::Node,
            ),
            (
                StringStoreKey::Membership,
                keyspace.members_key(),
                KeyClass::Membership,
            ),
        ];
        for (key, expected, class) in cases {
            let encoded = encode_runtime_store_key(&prefix.to_string(), 1_000, &key).unwrap();
            assert_eq!(encoded, expected);
            assert_eq!(
                class_of_text_key(&prefix.to_string(), &encoded),
                Some(class)
            );
            assert_eq!(
                keyspace.class_of(&encoded),
                Some(match class {
                    KeyClass::Document => "wf",
                    KeyClass::Schedule => "sched",
                    KeyClass::Timer => "t",
                    KeyClass::Node => "nodes",
                    KeyClass::Membership => "members",
                })
            );
            assert_eq!(
                decode_runtime_store_key(&prefix.to_string(), 1_000, &encoded).unwrap(),
                key
            );
        }

        let deadline = 12_345;
        let bucket = keyspace.bucket_of(deadline);
        let origin = "来源/α:_@~%";
        let by = "节点/東京 @~%";
        let token = 0x00ab_cdef_1234_5678;
        let origin_key = StringStoreKey::TimerOrigin {
            bucket,
            deadline,
            origin: origin.into(),
            token,
            by: by.into(),
        };
        let encoded = encode_runtime_store_key(&prefix.to_string(), 1_000, &origin_key).unwrap();
        assert_eq!(encoded, keyspace.timer_key(origin, deadline, token, by));
        assert_eq!(
            class_of_text_key(&prefix.to_string(), &encoded),
            Some(KeyClass::Timer)
        );
        assert_eq!(
            decode_runtime_store_key(&prefix.to_string(), 1_000, &encoded).unwrap(),
            origin_key
        );

        let id = "计划/β:_@~%";
        let schedule_key = StringStoreKey::TimerSchedule {
            bucket,
            deadline,
            id: id.into(),
            token,
            by: by.into(),
        };
        let encoded = encode_runtime_store_key(&prefix.to_string(), 1_000, &schedule_key).unwrap();
        assert_eq!(encoded, keyspace.sched_timer_key(id, deadline, token, by));
        assert_eq!(
            decode_runtime_store_key(&prefix.to_string(), 1_000, &encoded).unwrap(),
            schedule_key
        );
    }
}

#[test]
fn textual_store_key_bucket_width_and_zero_config_match_keyspace() {
    use echod_codec::store_key_text::{
        decode_runtime_store_key, encode_runtime_store_key, StringStoreKey,
    };
    use existing_keys::KeySpace;

    for bucket_ms in [0, 1, 10, 1_000, u64::MAX] {
        let keyspace = KeySpace::new("p", bucket_ms);
        for deadline in [0, 1, 999, 1_000, u64::MAX] {
            let key = StringStoreKey::TimerOrigin {
                bucket: keyspace.bucket_of(deadline),
                deadline,
                origin: "o".into(),
                token: u64::MAX,
                by: "n".into(),
            };
            let encoded = encode_runtime_store_key(&"p".to_string(), bucket_ms, &key).unwrap();
            assert_eq!(encoded, keyspace.timer_key("o", deadline, u64::MAX, "n"));
            let rest = encoded.strip_prefix("p/t/").unwrap();
            assert_eq!(&rest[..20], format!("{:020}", keyspace.bucket_of(deadline)));
            assert_eq!(&rest[21..41], format!("{deadline:020}"));
            assert_eq!(
                decode_runtime_store_key(&"p".to_string(), bucket_ms, &encoded).unwrap(),
                key
            );
        }
    }
}

#[test]
fn textual_store_key_decoder_rejects_noncanonical_and_malformed_keys() {
    use echod_codec::store_key_text::{
        decode_runtime_store_key, encode_runtime_store_key, StringStoreKey,
    };

    let prefix = "p".to_string();
    for malformed in [
        "p/wf/%e6%9d%b1", // lowercase escapes
        "p/wf/%41",       // redundant escape
        "p/wf/%",         // truncated escape
        "p/wf/%GG",       // invalid escape
        "p/t/0000000000000000000/00000000000000000001_o@0000000000000000~n",
        "p/t/00000000000000000000/0000000000000000001_o@0000000000000000~n",
        "p/t/00000000000000000000/00000000000000000001_o@000000000000000~n",
        "p/t/00000000000000000000/00000000000000000001_o@000000000000000A~n",
        "p/t/00000000000000000001/00000000000000000002_o@0000000000000000~n",
        "wrong/wf/o",
        "p/unknown/o",
    ] {
        assert!(
            decode_runtime_store_key(&prefix, 1_000, &malformed.to_string()).is_err(),
            "accepted malformed key: {malformed}"
        );
    }

    let noncanonical_bucket = StringStoreKey::TimerOrigin {
        bucket: 1,
        deadline: 2,
        origin: "o".into(),
        token: 0,
        by: "n".into(),
    };
    assert!(encode_runtime_store_key(&prefix, 1_000, &noncanonical_bucket).is_err());
    assert!(
        echod_codec::store_key_text::decode_store_key_bytes(
            &b"p".to_vec(),
            1_000,
            &b"p/wf/%FF".to_vec(),
        )
        .is_err()
    );
}

#[test]
fn fixed_width_bucket_text_sorts_in_numeric_order() {
    let values = [0, 1, 9, 10, 999, 1_000, u64::MAX - 1, u64::MAX];
    let formatted: Vec<String> = values.iter().map(|value| format!("{value:020}")).collect();
    for i in 0..values.len() {
        for j in 0..values.len() {
            assert_eq!(formatted[i] < formatted[j], values[i] < values[j]);
        }
    }
}
