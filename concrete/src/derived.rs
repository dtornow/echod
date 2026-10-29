//! Verified derived semantic view of the raw object store.
//!
//! Every entry must have a canonical textual key and a body appropriate for
//! that key.  Decoding is all-or-nothing: one bad key or body rejects the
//! complete bucket.

use vstd::prelude::*;

use echod_codec::document::{decode_promise_document, decode_schedule_document};
use echod_codec::store_key_text::{
    decode_store_key_bytes, encode_store_key_text, model_key_string,
};
use echod_codec::types as codec_model;
use echod_kernel::types::Schedule;

use crate::raw::{Entry, RawStore};
use crate::{
    Bucket, MembershipConfiguration, NodeAnnouncement, OriginDocument, ScheduleDocument,
    ScheduleRow, SemanticBucket, TimerKey,
};

#[cfg(verus_keep_ghost)]
use crate::raw::{AEntry, ARawStore};
#[cfg(verus_keep_ghost)]
use crate::{
    ABucket, AMembershipConfiguration, ANodeAnnouncement, AOriginDocument, AScheduleDocument,
    AScheduleRow, ATimerKey,
};
#[cfg(verus_keep_ghost)]
use echod_codec::document::{
    decode_promise_document_spec, decode_schedule_document_spec,
    lemma_promises_kernel_model_round_trip, lemma_schedules_kernel_model_round_trip,
    promises_to_kernel, schedules_to_kernel,
};
#[cfg(verus_keep_ghost)]
use echod_codec::store_key_text::{decode_store_key_spec, encode_store_key_spec};
#[cfg(verus_keep_ghost)]
use echod_kernel::types::{APromise, ASchedule};

verus! {

pub type DecodeResult<T> = Result<T, &'static str>;

pub open spec fn empty_bucket() -> ABucket {
    ABucket {
        origins: Seq::empty(),
        schedules: Seq::empty(),
        timers: Seq::empty(),
        announcements: Seq::empty(),
        membership: None,
    }
}

pub open spec fn decoded_promises(
    bytes: Seq<u8>,
) -> Option<(Option<codec_model::AHeader>, Seq<APromise>)> {
    match decode_promise_document_spec(bytes) {
        Some((header, rows)) =>
            Some((header, promises_to_kernel(rows))),
        None => None,
    }
}

pub open spec fn decoded_schedules(
    bytes: Seq<u8>,
) -> Option<(Option<codec_model::AHeader>, Seq<ASchedule>)> {
    match decode_schedule_document_spec(bytes) {
        Some((header, rows)) =>
            Some((header, schedules_to_kernel(rows))),
        None => None,
    }
}

pub open spec fn schedule_rows(rows: Seq<ASchedule>) -> Seq<AScheduleRow> {
    rows.map_values(|schedule: ASchedule| AScheduleRow { schedule })
}

pub open spec fn decode_entry_spec(
    prefix: Seq<u8>,
    bucket_ms: u64,
    entry: AEntry,
    bucket: ABucket,
) -> Option<ABucket> {
    match decode_store_key_spec(prefix, bucket_ms, entry.key) {
        None => None,
        Some(key) => match encode_store_key_spec(prefix, bucket_ms, key) {
            None => None,
            Some(canonical_key) => match key {
                codec_model::AStoreKey::Document(origin) => {
                    match decoded_promises(entry.object.bytes) {
                        Some((Some(header), rows)) => Some(ABucket {
                            origins: bucket.origins.push(AOriginDocument {
                                origin: vstd::utf8::decode_utf8(origin),
                                rows,
                                stamp: header.stamp,
                                nonce: header.nonce,
                                version: entry.object.version,
                            }),
                            ..bucket
                        }),
                        _ => None,
                    }
                }
                codec_model::AStoreKey::Schedule(id) => {
                    match decoded_schedules(entry.object.bytes) {
                        Some((Some(header), rows)) => Some(ABucket {
                            schedules: bucket.schedules.push(AScheduleDocument {
                                id: vstd::utf8::decode_utf8(id),
                                rows: schedule_rows(rows),
                                stamp: header.stamp,
                                nonce: header.nonce,
                                version: entry.object.version,
                            }),
                            ..bucket
                        }),
                        _ => None,
                    }
                }
                codec_model::AStoreKey::TimerOrigin {
                    bucket: timer_bucket,
                    deadline,
                    origin,
                    token,
                    by,
                } => if entry.object.bytes.len() == 0 {
                    Some(ABucket {
                        timers: bucket.timers.push(ATimerKey {
                            key: vstd::utf8::decode_utf8(canonical_key),
                            bucket: timer_bucket,
                            deadline,
                            target: vstd::utf8::decode_utf8(origin),
                            schedule: false,
                            token,
                            by: vstd::utf8::decode_utf8(by),
                        }),
                        ..bucket
                    })
                } else {
                    None
                },
                codec_model::AStoreKey::TimerSchedule {
                    bucket: timer_bucket,
                    deadline,
                    id,
                    token,
                    by,
                } => if entry.object.bytes.len() == 0 {
                    Some(ABucket {
                        timers: bucket.timers.push(ATimerKey {
                            key: vstd::utf8::decode_utf8(canonical_key),
                            bucket: timer_bucket,
                            deadline,
                            target: vstd::utf8::decode_utf8(id),
                            schedule: true,
                            token,
                            by: vstd::utf8::decode_utf8(by),
                        }),
                        ..bucket
                    })
                } else {
                    None
                },
                codec_model::AStoreKey::Node(_) => {
                    match echod_codec::laws::decode_announcement_spec(
                        entry.object.bytes,
                    ) {
                        Some(value) => Some(ABucket {
                            announcements: bucket.announcements.push(
                                ANodeAnnouncement {
                                    id: vstd::utf8::decode_utf8(value.id),
                                    url: vstd::utf8::decode_utf8(value.url),
                                    at: value.at,
                                },
                            ),
                            ..bucket
                        }),
                        None => None,
                    }
                }
                codec_model::AStoreKey::Membership => {
                    match echod_codec::laws::decode_membership_spec(
                        entry.object.bytes,
                    ) {
                        Some(value) if bucket.membership is None =>
                            Some(ABucket {
                                membership: Some(AMembershipConfiguration {
                                    epoch: value.epoch,
                                    members:
                                        echod_codec::bridge::utf8_to_strings(
                                            value.members,
                                        ),
                                }),
                                ..bucket
                            }),
                        _ => None,
                    }
                }
            },
        },
    }
}

pub open spec fn decode_entries_spec(
    entries: Seq<AEntry>,
    index: nat,
    prefix: Seq<u8>,
    bucket_ms: u64,
    bucket: ABucket,
) -> Option<ABucket>
    decreases entries.len() - index,
{
    if index >= entries.len() {
        Some(bucket)
    } else {
        match decode_entry_spec(
            prefix, bucket_ms, entries[index as int], bucket,
        ) {
            Some(next) => decode_entries_spec(
                entries, index + 1, prefix, bucket_ms, next,
            ),
            None => None,
        }
    }
}

/// Ghost twin of [`decode_bucket`].  It describes the exact semantic bucket
/// returned by the executable decoder, including representation order.
pub open spec fn decode_bucket_spec(
    store: ARawStore,
    prefix: Seq<u8>,
    bucket_ms: u64,
) -> Option<ABucket> {
    decode_entries_spec(
        store.entries, 0, prefix, bucket_ms, empty_bucket(),
    )
}

fn push_origin(
    values: &mut Vec<OriginDocument>,
    value: OriginDocument,
)
    ensures
        final(values).deep_view()
            == old(values).deep_view().push(value.deep_view()),
{
    let ghost old_values = values.deep_view();
    let ghost value_view = value.deep_view();
    values.push(value);
    assert(values.deep_view() =~= old_values.push(value_view));
}

fn push_schedule(
    values: &mut Vec<ScheduleDocument>,
    value: ScheduleDocument,
)
    ensures
        final(values).deep_view()
            == old(values).deep_view().push(value.deep_view()),
{
    let ghost old_values = values.deep_view();
    let ghost value_view = value.deep_view();
    values.push(value);
    assert(values.deep_view() =~= old_values.push(value_view));
}

fn push_timer(values: &mut Vec<TimerKey>, value: TimerKey)
    ensures
        final(values).deep_view()
            == old(values).deep_view().push(value.deep_view()),
{
    let ghost old_values = values.deep_view();
    let ghost value_view = value.deep_view();
    values.push(value);
    assert(values.deep_view() =~= old_values.push(value_view));
}

fn push_announcement(
    values: &mut Vec<NodeAnnouncement>,
    value: NodeAnnouncement,
)
    ensures
        final(values).deep_view()
            == old(values).deep_view().push(value.deep_view()),
{
    let ghost old_values = values.deep_view();
    let ghost value_view = value.deep_view();
    values.push(value);
    assert(values.deep_view() =~= old_values.push(value_view));
}

fn wrap_schedule_rows(
    mut rows: Vec<Schedule>,
) -> (result: Vec<ScheduleRow>)
    ensures result.deep_view() == schedule_rows(rows.deep_view()),
    decreases rows.len(),
{
    if rows.len() == 0 {
        Vec::new()
    } else {
        let ghost original = rows.deep_view();
        let row = rows.pop().unwrap();
        let ghost row_view = row@;
        let ghost prefix = rows.deep_view();
        assert(prefix == original.drop_last());
        assert(row_view == original.last());
        let mut result = wrap_schedule_rows(rows);
        result.push(ScheduleRow { schedule: row });
        assert(result.deep_view() =~=
            schedule_rows(prefix).push(AScheduleRow { schedule: row_view }));
        result
    }
}

#[verifier::rlimit(40)]
fn decode_entry(
    entry: &Entry,
    prefix: &String,
    prefix_bytes: &Vec<u8>,
    bucket_ms: u64,
    bucket: Bucket,
) -> (result: DecodeResult<Bucket>)
    requires
        prefix_bytes@ == vstd::utf8::encode_utf8(prefix@),
    ensures
        match result {
            Ok(decoded) => decode_entry_spec(
                prefix_bytes@, bucket_ms, entry.deep_view(), bucket@,
            ) == Some(decoded@),
            Err(_) => decode_entry_spec(
                prefix_bytes@, bucket_ms, entry.deep_view(), bucket@,
            ) is None,
        },
{
    let ghost entry_view = entry.deep_view();
    let ghost before = bucket@;
    let key = match decode_store_key_bytes(
        prefix_bytes, bucket_ms, &entry.key.bytes,
    ) {
        Ok(key) => key,
        Err(error) => return Err(error),
    };
    let ghost key_view = key.deep_view();
    let canonical = match encode_store_key_text(prefix, bucket_ms, &key) {
        Ok(key) => key,
        Err(error) => return Err(error),
    };
    assert(encode_store_key_spec(prefix_bytes@, bucket_ms, key_view)
        == Some(vstd::utf8::encode_utf8(canonical@)));
    let string_key = model_key_string(key);
    proof {
        echod_codec::store_key_text::lemma_model_key_string_round_trip(
            key_view,
        );
    }
    assert(echod_codec::store_key_text::string_key_to_model(
        string_key.deep_view(),
    ) == key_view);
    match string_key {
        echod_codec::store_key_text::StringStoreKey::Document(origin) => {
            assert(key_view == codec_model::AStoreKey::Document(
                vstd::utf8::encode_utf8(origin@),
            ));
            let (header, rows) = match decode_promise_document(
                &entry.object.bytes,
            ) {
                Ok(document) => document,
                Err(error) => return Err(error),
            };
            let header = match header {
                Some(header) => header,
                None => return Err("Promise document has no Header"),
            };
            let ghost row_views = rows.deep_view();
            proof {
                lemma_promises_kernel_model_round_trip(row_views);
                vstd::utf8::encode_utf8_decode_utf8(origin@);
            }
            assert(decoded_promises(entry.object.bytes@)
                == Some((Some(header@), row_views)));
            let mut bucket = bucket;
            push_origin(&mut bucket.origins, OriginDocument {
                origin,
                rows,
                stamp: header.stamp,
                nonce: header.nonce,
                version: entry.object.version,
            });
            assert(decode_entry_spec(
                prefix_bytes@, bucket_ms, entry_view, before,
            ) == Some(bucket@));
            Ok(bucket)
        }
        echod_codec::store_key_text::StringStoreKey::Schedule(id) => {
            assert(key_view == codec_model::AStoreKey::Schedule(
                vstd::utf8::encode_utf8(id@),
            ));
            let (header, rows) = match decode_schedule_document(
                &entry.object.bytes,
            ) {
                Ok(document) => document,
                Err(error) => return Err(error),
            };
            let header = match header {
                Some(header) => header,
                None => return Err("Schedule document has no Header"),
            };
            let ghost row_views = rows.deep_view();
            proof {
                lemma_schedules_kernel_model_round_trip(row_views);
                vstd::utf8::encode_utf8_decode_utf8(id@);
            }
            assert(decoded_schedules(entry.object.bytes@)
                == Some((Some(header@), row_views)));
            let rows = wrap_schedule_rows(rows);
            assert(rows.deep_view() == schedule_rows(row_views));
            let mut bucket = bucket;
            push_schedule(&mut bucket.schedules, ScheduleDocument {
                id,
                rows,
                stamp: header.stamp,
                nonce: header.nonce,
                version: entry.object.version,
            });
            let ghost document = AScheduleDocument {
                id: id@,
                rows: schedule_rows(row_views),
                stamp: header.stamp,
                nonce: header.nonce,
                version: entry.object.version,
            };
            assert(bucket@ == ABucket {
                schedules: before.schedules.push(document),
                ..before
            });
            assert(decode_entry_spec(
                prefix_bytes@, bucket_ms, entry_view, before,
            ) == Some(bucket@));
            Ok(bucket)
        }
        echod_codec::store_key_text::StringStoreKey::TimerOrigin {
            bucket: timer_bucket,
            deadline,
            origin,
            token,
            by,
        } => {
            assert(key_view == codec_model::AStoreKey::TimerOrigin {
                bucket: timer_bucket,
                deadline,
                origin: vstd::utf8::encode_utf8(origin@),
                token,
                by: vstd::utf8::encode_utf8(by@),
            });
            proof {
                vstd::utf8::encode_utf8_decode_utf8(origin@);
                vstd::utf8::encode_utf8_decode_utf8(by@);
                vstd::utf8::encode_utf8_decode_utf8(canonical@);
            }
            if entry.object.bytes.len() != 0 {
                return Err("timer body is not empty");
            }
            let mut bucket = bucket;
            push_timer(&mut bucket.timers, TimerKey {
                key: canonical,
                bucket: timer_bucket,
                deadline,
                target: origin,
                schedule: false,
                token,
                by,
            });
            assert(decode_entry_spec(
                prefix_bytes@, bucket_ms, entry_view, before,
            ) == Some(bucket@));
            Ok(bucket)
        }
        echod_codec::store_key_text::StringStoreKey::TimerSchedule {
            bucket: timer_bucket,
            deadline,
            id,
            token,
            by,
        } => {
            assert(key_view == codec_model::AStoreKey::TimerSchedule {
                bucket: timer_bucket,
                deadline,
                id: vstd::utf8::encode_utf8(id@),
                token,
                by: vstd::utf8::encode_utf8(by@),
            });
            proof {
                vstd::utf8::encode_utf8_decode_utf8(id@);
                vstd::utf8::encode_utf8_decode_utf8(by@);
                vstd::utf8::encode_utf8_decode_utf8(canonical@);
            }
            if entry.object.bytes.len() != 0 {
                return Err("timer body is not empty");
            }
            let mut bucket = bucket;
            push_timer(&mut bucket.timers, TimerKey {
                key: canonical,
                bucket: timer_bucket,
                deadline,
                target: id,
                schedule: true,
                token,
                by,
            });
            assert(decode_entry_spec(
                prefix_bytes@, bucket_ms, entry_view, before,
            ) == Some(bucket@));
            Ok(bucket)
        }
        echod_codec::store_key_text::StringStoreKey::Node(_) => {
            let value = match echod_codec::decode_announcement(
                &entry.object.bytes,
            ) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let id = echod_codec::bridge::text_to_string(value.id);
            let url = echod_codec::bridge::text_to_string(value.url);
            let mut bucket = bucket;
            push_announcement(&mut bucket.announcements, NodeAnnouncement {
                id,
                url,
                at: value.at,
            });
            assert(decode_entry_spec(
                prefix_bytes@, bucket_ms, entry_view, before,
            ) == Some(bucket@));
            Ok(bucket)
        }
        echod_codec::store_key_text::StringStoreKey::Membership => {
            assert(key_view == codec_model::AStoreKey::Membership);
            if bucket.membership.is_some() {
                return Err("duplicate membership object");
            }
            assert(before.membership is None);
            let value = match echod_codec::decode_membership(
                &entry.object.bytes,
            ) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let ghost value_view = value@;
            assert(echod_codec::laws::decode_membership_spec(
                entry.object.bytes@,
            ) == Some(value_view));
            let members =
                echod_codec::bridge::texts_to_strings(value.members);
            assert(members.deep_view()
                == echod_codec::bridge::utf8_to_strings(
                    value_view.members,
                ));
            let mut bucket = bucket;
            bucket.membership = Some(MembershipConfiguration {
                epoch: value.epoch,
                members,
            });
            assert(bucket@ == ABucket {
                membership: Some(AMembershipConfiguration {
                    epoch: value_view.epoch,
                    members: echod_codec::bridge::utf8_to_strings(
                        value_view.members,
                    ),
                }),
                ..before
            });
            assert(decode_entry_spec(
                prefix_bytes@, bucket_ms, entry_view, before,
            ) == Some(bucket@));
            Ok(bucket)
        }
    }
}

fn decode_entries(
    entries: &Vec<Entry>,
    index: usize,
    prefix: &String,
    prefix_bytes: &Vec<u8>,
    bucket_ms: u64,
    bucket: Bucket,
) -> (result: DecodeResult<Bucket>)
    requires
        index <= entries.len(),
        prefix_bytes@ == vstd::utf8::encode_utf8(prefix@),
    ensures
        match result {
            Ok(decoded) => decode_entries_spec(
                entries.deep_view(),
                index as nat,
                prefix_bytes@,
                bucket_ms,
                bucket@,
            ) == Some(decoded@),
            Err(_) => decode_entries_spec(
                entries.deep_view(),
                index as nat,
                prefix_bytes@,
                bucket_ms,
                bucket@,
            ) is None,
        },
    decreases entries.len() - index,
{
    reveal_with_fuel(decode_entries_spec, 2);
    if index == entries.len() {
        return Ok(bucket);
    }
    let bucket = match decode_entry(
        &entries[index], prefix, prefix_bytes, bucket_ms, bucket,
    ) {
        Ok(bucket) => bucket,
        Err(error) => return Err(error),
    };
    decode_entries(
        entries, index + 1, prefix, prefix_bytes, bucket_ms, bucket,
    )
}

/// Decode a raw store into the semantic view used by deterministic simulation
/// and refinement. Any malformed/noncanonical entry rejects the whole view.
pub fn decode_bucket(
    store: &RawStore,
    prefix: &String,
    bucket_ms: u64,
) -> (result: DecodeResult<SemanticBucket>)
    ensures
        match result {
            Ok(bucket) => decode_bucket_spec(
                store@,
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
            ) == Some(bucket@),
            Err(_) => decode_bucket_spec(
                store@,
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
            ) is None,
        },
{
    let prefix_text = echod_codec::bridge::string_to_text(prefix);
    let prefix_bytes = prefix_text.bytes;
    let bucket = Bucket::new();
    decode_entries(
        &store.entries, 0, prefix, &prefix_bytes, bucket_ms, bucket,
    )
}

} // verus!
