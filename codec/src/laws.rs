//! Typed model encodings and their proved decoders.
//!
//! These specifications share the exact primitive parsers used by the
//! executable implementation. The larger Promise/Schedule models use the
//! canonical-field theorem at the bottom; primitive and nested component
//! decoders are factored independently.

use vstd::prelude::*;

use crate::primitives::*;
use crate::record::*;
#[cfg(verus_keep_ghost)]
use crate::text::valid_utf8;
use crate::types::*;

verus! {

pub const KIND_HEADER: u8 = 1;
pub const KIND_PROMISE: u8 = 2;
pub const KIND_SCHEDULE: u8 = 3;
pub const KIND_ANNOUNCEMENT: u8 = 4;
pub const KIND_MEMBERSHIP: u8 = 5;
pub const KIND_STORE_KEY: u8 = 6;

pub open spec fn record_encodable(fields: Seq<Seq<u8>>) -> bool {
    &&& fields.len() <= u64::MAX
    &&& fields.len() <= usize::MAX
    &&& fields.len() <= MAX_SEQUENCE_ITEMS
    &&& forall|i: int| 0 <= i < fields.len() ==> {
        &&& #[trigger] fields[i].len() <= u64::MAX
        &&& fields[i].len() <= usize::MAX
    }
    &&& blob_sequence_bytes(fields).len() <= u64::MAX
    &&& blob_sequence_bytes(fields).len() <= usize::MAX
}

pub open spec fn header_fields(header: AHeader) -> Seq<Seq<u8>> {
    seq![u64_bytes(header.stamp), u64_bytes(header.nonce)]
}

pub open spec fn header_bytes(header: AHeader) -> Seq<u8> {
    record_bytes(KIND_HEADER, header_fields(header))
}

pub open spec fn decode_header_spec(bytes: Seq<u8>) -> Option<AHeader> {
    match decode_record_spec(bytes, KIND_HEADER) {
        Some(fields) if fields.len() == 2 => {
            match (decode_u64_spec(fields[0]), decode_u64_spec(fields[1])) {
                (Some(stamp), Some(nonce)) => Some(AHeader { stamp, nonce }),
                _ => None,
            }
        }
        _ => None,
    }
}

pub proof fn lemma_header_round_trip(header: AHeader)
    ensures decode_header_spec(header_bytes(header)) == Some(header),
{
    assert(header_fields(header)
        == seq![u64_bytes(header.stamp), u64_bytes(header.nonce)]);
    assert(u64_bytes(header.stamp).len() == 8);
    assert(u64_bytes(header.nonce).len() == 8);
    assert(blob_sequence_tail(header_fields(header)).len() == 32) by (compute);
    assert(blob_sequence_bytes(header_fields(header)).len() == 40) by (compute);
    lemma_record_round_trip(KIND_HEADER, header_fields(header));
    lemma_u64_round_trip(header.stamp);
    lemma_u64_round_trip(header.nonce);
}

pub open spec fn announcement_wf(value: AAnnouncement) -> bool {
    &&& valid_utf8(value.id)
    &&& valid_utf8(value.url)
    &&& record_encodable(announcement_fields(value))
}

pub open spec fn announcement_fields(value: AAnnouncement) -> Seq<Seq<u8>> {
    seq![value.id, value.url, u64_bytes(value.at)]
}

pub open spec fn announcement_bytes(value: AAnnouncement) -> Seq<u8> {
    record_bytes(KIND_ANNOUNCEMENT, announcement_fields(value))
}

pub open spec fn decode_announcement_spec(
    bytes: Seq<u8>,
) -> Option<AAnnouncement> {
    match decode_record_spec(bytes, KIND_ANNOUNCEMENT) {
        Some(fields) if fields.len() == 3
            && valid_utf8(fields[0])
            && valid_utf8(fields[1]) => {
            match decode_u64_spec(fields[2]) {
                Some(at) => Some(AAnnouncement {
                    id: fields[0],
                    url: fields[1],
                    at,
                }),
                None => None,
            }
        }
        _ => None,
    }
}

pub proof fn lemma_announcement_round_trip(value: AAnnouncement)
    requires announcement_wf(value),
    ensures
        decode_announcement_spec(announcement_bytes(value)) == Some(value),
{
    lemma_record_round_trip(KIND_ANNOUNCEMENT, announcement_fields(value));
    lemma_u64_round_trip(value.at);
}

pub open spec fn all_valid_utf8(items: Seq<Seq<u8>>) -> bool {
    forall|i: int| 0 <= i < items.len() ==> valid_utf8(#[trigger] items[i])
}

pub open spec fn sequence_encodable(items: Seq<Seq<u8>>) -> bool {
    &&& items.len() <= u64::MAX
    &&& items.len() <= usize::MAX
    &&& items.len() <= MAX_SEQUENCE_ITEMS
    &&& forall|i: int| 0 <= i < items.len() ==> {
        &&& #[trigger] items[i].len() <= u64::MAX
        &&& items[i].len() <= usize::MAX
    }
}

pub open spec fn membership_wf(value: AMembership) -> bool {
    &&& all_valid_utf8(value.members)
    &&& value.members.len() <= u64::MAX
    &&& value.members.len() <= usize::MAX
    &&& value.members.len() <= MAX_SEQUENCE_ITEMS
    &&& forall|i: int| 0 <= i < value.members.len() ==> {
        &&& #[trigger] value.members[i].len() <= u64::MAX
        &&& value.members[i].len() <= usize::MAX
    }
    &&& record_encodable(membership_fields(value))
}

pub open spec fn membership_fields(value: AMembership) -> Seq<Seq<u8>> {
    seq![u64_bytes(value.epoch), blob_sequence_bytes(value.members)]
}

pub open spec fn membership_bytes(value: AMembership) -> Seq<u8> {
    record_bytes(KIND_MEMBERSHIP, membership_fields(value))
}

pub open spec fn decode_membership_spec(
    bytes: Seq<u8>,
) -> Option<AMembership> {
    match decode_record_spec(bytes, KIND_MEMBERSHIP) {
        Some(fields) if fields.len() == 2 => {
            match (
                decode_u64_spec(fields[0]),
                decode_blob_sequence_spec(fields[1]),
            ) {
                (Some(epoch), Some(members)) if all_valid_utf8(members) => {
                    Some(AMembership { epoch, members })
                }
                _ => None,
            }
        }
        _ => None,
    }
}

pub proof fn lemma_membership_round_trip(value: AMembership)
    requires membership_wf(value),
    ensures decode_membership_spec(membership_bytes(value)) == Some(value),
{
    lemma_blob_sequence_round_trip(value.members);
    lemma_record_round_trip(KIND_MEMBERSHIP, membership_fields(value));
    lemma_u64_round_trip(value.epoch);
}

pub open spec fn option_u64_bytes(value: Option<u64>) -> Seq<u8> {
    match value {
        None => option_blob_bytes(None),
        Some(value) => option_blob_bytes(Some(u64_bytes(value))),
    }
}

pub open spec fn decode_option_u64_spec(bytes: Seq<u8>) -> Option<Option<u64>> {
    match decode_option_blob_spec(bytes) {
        None => None,
        Some(None) => Some(None),
        Some(Some(value)) => match decode_u64_spec(value) {
            Some(value) => Some(Some(value)),
            None => None,
        },
    }
}

pub proof fn lemma_option_u64_round_trip(value: Option<u64>)
    ensures
        decode_option_u64_spec(option_u64_bytes(value)) == Some(value),
{
    match value {
        None => {
            lemma_option_blob_round_trip(None);
        }
        Some(value) => {
            lemma_u64_round_trip(value);
            lemma_option_blob_round_trip(Some(u64_bytes(value)));
        }
    }
}

pub open spec fn option_text_bytes(value: Option<Seq<u8>>) -> Seq<u8> {
    option_blob_bytes(value)
}

pub open spec fn decode_option_text_spec(
    bytes: Seq<u8>,
) -> Option<Option<Seq<u8>>> {
    match decode_option_blob_spec(bytes) {
        Some(Some(value)) if valid_utf8(value) => Some(Some(value)),
        Some(None) => Some(None),
        _ => None,
    }
}

pub proof fn lemma_option_text_round_trip(value: Option<Seq<u8>>)
    requires
        value is Some ==> valid_utf8(value->Some_0),
        value is Some ==> value->Some_0.len() <= u64::MAX,
        value is Some ==> value->Some_0.len() <= usize::MAX,
    ensures
        decode_option_text_spec(option_text_bytes(value)) == Some(value),
{
    lemma_option_blob_round_trip(value);
}

pub open spec fn text_list_bytes(value: Seq<Seq<u8>>) -> Seq<u8> {
    blob_sequence_bytes(value)
}

pub open spec fn decode_text_list_spec(
    bytes: Seq<u8>,
) -> Option<Seq<Seq<u8>>> {
    match decode_blob_sequence_spec(bytes) {
        Some(value) if all_valid_utf8(value) => Some(value),
        _ => None,
    }
}

pub proof fn lemma_text_list_round_trip(value: Seq<Seq<u8>>)
    requires
        all_valid_utf8(value),
        sequence_encodable(value),
    ensures
        decode_text_list_spec(text_list_bytes(value)) == Some(value),
{
    lemma_blob_sequence_round_trip(value);
}

pub open spec fn pair_bytes(pair: (Seq<u8>, Seq<u8>)) -> Seq<u8> {
    blob_sequence_bytes(seq![pair.0, pair.1])
}

pub open spec fn decode_pair_spec(
    bytes: Seq<u8>,
) -> Option<(Seq<u8>, Seq<u8>)> {
    match decode_blob_sequence_spec(bytes) {
        Some(fields) if fields.len() == 2
            && valid_utf8(fields[0])
            && valid_utf8(fields[1]) => Some((fields[0], fields[1])),
        _ => None,
    }
}

pub open spec fn pair_list_items(
    pairs: Seq<(Seq<u8>, Seq<u8>)>,
) -> Seq<Seq<u8>> {
    pairs.map_values(|pair: (Seq<u8>, Seq<u8>)| pair_bytes(pair))
}

pub open spec fn pair_list_wf(pairs: Seq<(Seq<u8>, Seq<u8>)>) -> bool {
    &&& forall|i: int| 0 <= i < pairs.len() ==> {
        &&& valid_utf8(#[trigger] pairs[i].0)
        &&& valid_utf8(pairs[i].1)
        &&& pairs[i].0.len() <= u64::MAX
        &&& pairs[i].0.len() <= usize::MAX
        &&& pairs[i].1.len() <= u64::MAX
        &&& pairs[i].1.len() <= usize::MAX
        &&& pair_bytes(pairs[i]).len() <= u64::MAX
        &&& pair_bytes(pairs[i]).len() <= usize::MAX
    }
    &&& sequence_encodable(pair_list_items(pairs))
}

pub open spec fn decode_pair_items(
    items: Seq<Seq<u8>>,
) -> Option<Seq<(Seq<u8>, Seq<u8>)>>
    decreases items.len(),
{
    if items.len() == 0 {
        Some(Seq::empty())
    } else {
        match (decode_pair_spec(items[0]), decode_pair_items(items.drop_first())) {
            (Some(first), Some(rest)) => Some(seq![first] + rest),
            _ => None,
        }
    }
}

pub open spec fn pair_list_bytes(
    pairs: Seq<(Seq<u8>, Seq<u8>)>,
) -> Seq<u8> {
    blob_sequence_bytes(pair_list_items(pairs))
}

pub open spec fn decode_pair_list_spec(
    bytes: Seq<u8>,
) -> Option<Seq<(Seq<u8>, Seq<u8>)>> {
    match decode_blob_sequence_spec(bytes) {
        Some(items) => decode_pair_items(items),
        None => None,
    }
}

proof fn lemma_pair_items_round_trip(pairs: Seq<(Seq<u8>, Seq<u8>)>)
    requires
        forall|i: int| 0 <= i < pairs.len() ==> {
            &&& valid_utf8(#[trigger] pairs[i].0)
            &&& valid_utf8(pairs[i].1)
            &&& pairs[i].0.len() <= u64::MAX
            &&& pairs[i].0.len() <= usize::MAX
            &&& pairs[i].1.len() <= u64::MAX
            &&& pairs[i].1.len() <= usize::MAX
        },
    ensures
        decode_pair_items(pair_list_items(pairs)) == Some(pairs),
    decreases pairs.len(),
{
    if pairs.len() > 0 {
        let first = pairs[0];
        let rest = pairs.drop_first();
        lemma_blob_sequence_round_trip(seq![first.0, first.1]);
        lemma_pair_items_round_trip(rest);
        assert(pair_list_items(pairs)[0] == pair_bytes(first));
        assert(pair_list_items(pairs).drop_first() == pair_list_items(rest));
        assert(seq![first] + rest == pairs);
    }
}

pub proof fn lemma_pair_list_round_trip(
    pairs: Seq<(Seq<u8>, Seq<u8>)>,
)
    requires pair_list_wf(pairs),
    ensures
        decode_pair_list_spec(pair_list_bytes(pairs)) == Some(pairs),
{
    assert forall|i: int| 0 <= i < pair_list_items(pairs).len()
        implies #[trigger] pair_list_items(pairs)[i].len() <= u64::MAX
            && pair_list_items(pairs)[i].len() <= usize::MAX by {
        let pair = pairs[i];
        assert(pair_list_items(pairs)[i] == pair_bytes(pair));
    }
    lemma_blob_sequence_round_trip(pair_list_items(pairs));
    lemma_pair_items_round_trip(pairs);
}

pub open spec fn option_text_wf(value: Option<Seq<u8>>) -> bool {
    &&& value is Some ==> valid_utf8(value->Some_0)
    &&& value is Some ==> value->Some_0.len() <= u64::MAX
    &&& value is Some ==> value->Some_0.len() <= usize::MAX
}

pub open spec fn value_fields(value: AValue) -> Seq<Seq<u8>> {
    seq![pair_list_bytes(value.headers), option_text_bytes(value.data)]
}

pub open spec fn value_bytes(value: AValue) -> Seq<u8> {
    blob_sequence_bytes(value_fields(value))
}

pub open spec fn value_wf(value: AValue) -> bool {
    &&& pair_list_wf(value.headers)
    &&& option_text_wf(value.data)
    &&& sequence_encodable(value_fields(value))
}

pub open spec fn decode_value_spec(bytes: Seq<u8>) -> Option<AValue> {
    match decode_blob_sequence_spec(bytes) {
        Some(fields) if fields.len() == 2 => {
            match (
                decode_pair_list_spec(fields[0]),
                decode_option_text_spec(fields[1]),
            ) {
                (Some(headers), Some(data)) => Some(AValue { headers, data }),
                _ => None,
            }
        }
        _ => None,
    }
}

pub proof fn lemma_value_round_trip(value: AValue)
    requires value_wf(value),
    ensures decode_value_spec(value_bytes(value)) == Some(value),
{
    lemma_pair_list_round_trip(value.headers);
    lemma_option_text_round_trip(value.data);
    lemma_blob_sequence_round_trip(value_fields(value));
}

pub open spec fn task_state_bytes(state: echod_kernel::TaskState) -> Seq<u8> {
    match state {
        echod_kernel::TaskState::Pending => seq![0u8],
        echod_kernel::TaskState::Acquired => seq![1u8],
        echod_kernel::TaskState::Suspended => seq![2u8],
        echod_kernel::TaskState::Halted => seq![3u8],
        echod_kernel::TaskState::Fulfilled => seq![4u8],
    }
}

pub open spec fn decode_task_state_spec(
    bytes: Seq<u8>,
) -> Option<echod_kernel::TaskState> {
    if bytes == seq![0u8] {
        Some(echod_kernel::TaskState::Pending)
    } else if bytes == seq![1u8] {
        Some(echod_kernel::TaskState::Acquired)
    } else if bytes == seq![2u8] {
        Some(echod_kernel::TaskState::Suspended)
    } else if bytes == seq![3u8] {
        Some(echod_kernel::TaskState::Halted)
    } else if bytes == seq![4u8] {
        Some(echod_kernel::TaskState::Fulfilled)
    } else {
        None
    }
}

pub proof fn lemma_task_state_round_trip(state: echod_kernel::TaskState)
    ensures
        decode_task_state_spec(task_state_bytes(state)) == Some(state),
{
    match state {
        echod_kernel::TaskState::Pending => {
            assert(task_state_bytes(state) == seq![0u8]);
            assert(decode_task_state_spec(seq![0u8])
                == Some(echod_kernel::TaskState::Pending)) by (compute);
        }
        echod_kernel::TaskState::Acquired => {
            assert(task_state_bytes(state) == seq![1u8]);
            assert(decode_task_state_spec(seq![1u8])
                == Some(echod_kernel::TaskState::Acquired)) by (compute);
        }
        echod_kernel::TaskState::Suspended => {
            assert(task_state_bytes(state) == seq![2u8]);
            assert(decode_task_state_spec(seq![2u8])
                == Some(echod_kernel::TaskState::Suspended)) by (compute);
        }
        echod_kernel::TaskState::Halted => {
            assert(task_state_bytes(state) == seq![3u8]);
            assert(decode_task_state_spec(seq![3u8])
                == Some(echod_kernel::TaskState::Halted)) by (compute);
        }
        echod_kernel::TaskState::Fulfilled => {
            assert(task_state_bytes(state) == seq![4u8]);
            assert(decode_task_state_spec(seq![4u8])
                == Some(echod_kernel::TaskState::Fulfilled)) by (compute);
        }
    }
}

pub open spec fn task_fields(value: ATask) -> Seq<Seq<u8>> {
    seq![
        task_state_bytes(value.state),
        u64_bytes(value.version),
        option_u64_bytes(value.ttl),
        option_text_bytes(value.pid),
        option_u64_bytes(value.lease_timeout_at),
        option_u64_bytes(value.retry_timeout_at),
        text_list_bytes(value.resumes),
    ]
}

pub open spec fn task_bytes(value: ATask) -> Seq<u8> {
    blob_sequence_bytes(task_fields(value))
}

pub open spec fn task_wf(value: ATask) -> bool {
    &&& option_text_wf(value.pid)
    &&& all_valid_utf8(value.resumes)
    &&& sequence_encodable(value.resumes)
    &&& sequence_encodable(task_fields(value))
}

pub open spec fn decode_task_spec(bytes: Seq<u8>) -> Option<ATask> {
    match decode_blob_sequence_spec(bytes) {
        Some(fields) if fields.len() == 7 => {
            match (
                decode_task_state_spec(fields[0]),
                decode_u64_spec(fields[1]),
                decode_option_u64_spec(fields[2]),
                decode_option_text_spec(fields[3]),
                decode_option_u64_spec(fields[4]),
                decode_option_u64_spec(fields[5]),
                decode_text_list_spec(fields[6]),
            ) {
                (
                    Some(state),
                    Some(version),
                    Some(ttl),
                    Some(pid),
                    Some(lease_timeout_at),
                    Some(retry_timeout_at),
                    Some(resumes),
                ) => Some(ATask {
                    state,
                    version,
                    ttl,
                    pid,
                    lease_timeout_at,
                    retry_timeout_at,
                    resumes,
                }),
                _ => None,
            }
        }
        _ => None,
    }
}

#[verifier::rlimit(20)]
pub proof fn lemma_task_round_trip(value: ATask)
    requires task_wf(value),
    ensures decode_task_spec(task_bytes(value)) == Some(value),
{
    lemma_task_state_round_trip(value.state);
    lemma_u64_round_trip(value.version);
    lemma_option_u64_round_trip(value.ttl);
    lemma_option_text_round_trip(value.pid);
    lemma_option_u64_round_trip(value.lease_timeout_at);
    lemma_option_u64_round_trip(value.retry_timeout_at);
    lemma_text_list_round_trip(value.resumes);
    lemma_blob_sequence_round_trip(task_fields(value));
}

pub open spec fn option_task_bytes(value: Option<ATask>) -> Seq<u8> {
    match value {
        None => option_blob_bytes(None),
        Some(value) => option_blob_bytes(Some(task_bytes(value))),
    }
}

pub open spec fn option_task_wf(value: Option<ATask>) -> bool {
    &&& value is Some ==> task_wf(value->Some_0)
    &&& value is Some ==> task_bytes(value->Some_0).len() <= u64::MAX
    &&& value is Some ==> task_bytes(value->Some_0).len() <= usize::MAX
}

pub open spec fn decode_option_task_spec(
    bytes: Seq<u8>,
) -> Option<Option<ATask>> {
    match decode_option_blob_spec(bytes) {
        Some(None) => Some(None),
        Some(Some(value)) => match decode_task_spec(value) {
            Some(value) => Some(Some(value)),
            None => None,
        },
        None => None,
    }
}

pub proof fn lemma_option_task_round_trip(value: Option<ATask>)
    requires option_task_wf(value),
    ensures
        decode_option_task_spec(option_task_bytes(value)) == Some(value),
{
    match value {
        None => {
            lemma_option_blob_round_trip(None);
        }
        Some(value) => {
            lemma_task_round_trip(value);
            lemma_option_blob_round_trip(Some(task_bytes(value)));
        }
    }
}

pub open spec fn promise_state_bytes(
    state: echod_kernel::PromiseState,
) -> Seq<u8> {
    match state {
        echod_kernel::PromiseState::Pending => seq![0u8],
        echod_kernel::PromiseState::Resolved => seq![1u8],
        echod_kernel::PromiseState::Rejected => seq![2u8],
        echod_kernel::PromiseState::RejectedCanceled => seq![3u8],
        echod_kernel::PromiseState::RejectedTimedout => seq![4u8],
    }
}

pub open spec fn decode_promise_state_spec(
    bytes: Seq<u8>,
) -> Option<echod_kernel::PromiseState> {
    if bytes == seq![0u8] {
        Some(echod_kernel::PromiseState::Pending)
    } else if bytes == seq![1u8] {
        Some(echod_kernel::PromiseState::Resolved)
    } else if bytes == seq![2u8] {
        Some(echod_kernel::PromiseState::Rejected)
    } else if bytes == seq![3u8] {
        Some(echod_kernel::PromiseState::RejectedCanceled)
    } else if bytes == seq![4u8] {
        Some(echod_kernel::PromiseState::RejectedTimedout)
    } else {
        None
    }
}

pub proof fn lemma_promise_state_round_trip(
    state: echod_kernel::PromiseState,
)
    ensures
        decode_promise_state_spec(promise_state_bytes(state)) == Some(state),
{
    match state {
        echod_kernel::PromiseState::Pending => {
            assert(decode_promise_state_spec(seq![0u8])
                == Some(echod_kernel::PromiseState::Pending)) by (compute);
        }
        echod_kernel::PromiseState::Resolved => {
            assert(decode_promise_state_spec(seq![1u8])
                == Some(echod_kernel::PromiseState::Resolved)) by (compute);
        }
        echod_kernel::PromiseState::Rejected => {
            assert(decode_promise_state_spec(seq![2u8])
                == Some(echod_kernel::PromiseState::Rejected)) by (compute);
        }
        echod_kernel::PromiseState::RejectedCanceled => {
            assert(decode_promise_state_spec(seq![3u8])
                == Some(echod_kernel::PromiseState::RejectedCanceled)) by (compute);
        }
        echod_kernel::PromiseState::RejectedTimedout => {
            assert(decode_promise_state_spec(seq![4u8])
                == Some(echod_kernel::PromiseState::RejectedTimedout)) by (compute);
        }
    }
}

pub open spec fn promise_fields(value: APromise) -> Seq<Seq<u8>> {
    seq![
        value.id,
        promise_state_bytes(value.state),
        pair_list_bytes(value.tags),
        value_bytes(value.param),
        value_bytes(value.value),
        u64_bytes(value.timeout_at),
        u64_bytes(value.created_at),
        option_u64_bytes(value.settled_at),
        text_list_bytes(value.callbacks),
        text_list_bytes(value.listeners),
        option_task_bytes(value.task),
    ]
}

pub open spec fn promise_bytes(value: APromise) -> Seq<u8> {
    record_bytes(KIND_PROMISE, promise_fields(value))
}

pub open spec fn promise_wf(value: APromise) -> bool {
    &&& valid_utf8(value.id)
    &&& pair_list_wf(value.tags)
    &&& value_wf(value.param)
    &&& value_wf(value.value)
    &&& all_valid_utf8(value.callbacks)
    &&& sequence_encodable(value.callbacks)
    &&& all_valid_utf8(value.listeners)
    &&& sequence_encodable(value.listeners)
    &&& option_task_wf(value.task)
    &&& record_encodable(promise_fields(value))
}

pub open spec fn decode_promise_spec(bytes: Seq<u8>) -> Option<APromise> {
    match decode_record_spec(bytes, KIND_PROMISE) {
        Some(fields) if fields.len() == 11 && valid_utf8(fields[0]) => {
            match (
                decode_promise_state_spec(fields[1]),
                decode_pair_list_spec(fields[2]),
                decode_value_spec(fields[3]),
                decode_value_spec(fields[4]),
                decode_u64_spec(fields[5]),
                decode_u64_spec(fields[6]),
                decode_option_u64_spec(fields[7]),
                decode_text_list_spec(fields[8]),
                decode_text_list_spec(fields[9]),
                decode_option_task_spec(fields[10]),
            ) {
                (
                    Some(state),
                    Some(tags),
                    Some(param),
                    Some(value),
                    Some(timeout_at),
                    Some(created_at),
                    Some(settled_at),
                    Some(callbacks),
                    Some(listeners),
                    Some(task),
                ) => Some(APromise {
                    id: fields[0],
                    state,
                    tags,
                    param,
                    value,
                    timeout_at,
                    created_at,
                    settled_at,
                    callbacks,
                    listeners,
                    task,
                }),
                _ => None,
            }
        }
        _ => None,
    }
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(60)]
pub proof fn lemma_promise_round_trip(value: APromise)
    requires promise_wf(value),
    ensures decode_promise_spec(promise_bytes(value)) == Some(value),
{
    lemma_promise_state_round_trip(value.state);
    lemma_pair_list_round_trip(value.tags);
    lemma_value_round_trip(value.param);
    lemma_value_round_trip(value.value);
    lemma_u64_round_trip(value.timeout_at);
    lemma_u64_round_trip(value.created_at);
    lemma_option_u64_round_trip(value.settled_at);
    lemma_text_list_round_trip(value.callbacks);
    lemma_text_list_round_trip(value.listeners);
    lemma_option_task_round_trip(value.task);
    lemma_record_round_trip(KIND_PROMISE, promise_fields(value));
    assert(decode_record_spec(promise_bytes(value), KIND_PROMISE)
        == Some(promise_fields(value)));
    assert(decode_promise_state_spec(promise_state_bytes(value.state))
        == Some(value.state));
    assert(decode_pair_list_spec(pair_list_bytes(value.tags))
        == Some(value.tags));
    assert(decode_value_spec(value_bytes(value.param)) == Some(value.param));
    assert(decode_value_spec(value_bytes(value.value)) == Some(value.value));
    assert(decode_option_u64_spec(option_u64_bytes(value.settled_at))
        == Some(value.settled_at));
    assert(decode_text_list_spec(text_list_bytes(value.callbacks))
        == Some(value.callbacks));
    assert(decode_text_list_spec(text_list_bytes(value.listeners))
        == Some(value.listeners));
    assert(decode_option_task_spec(option_task_bytes(value.task))
        == Some(value.task));
}

pub open spec fn schedule_fields(value: ASchedule) -> Seq<Seq<u8>> {
    seq![
        value.id,
        value.cron,
        value.promise_id,
        u64_bytes(value.promise_timeout),
        value_bytes(value.promise_param),
        pair_list_bytes(value.promise_tags),
        u64_bytes(value.next_run_at),
        option_u64_bytes(value.last_run_at),
        u64_bytes(value.created_at),
    ]
}

pub open spec fn schedule_bytes(value: ASchedule) -> Seq<u8> {
    record_bytes(KIND_SCHEDULE, schedule_fields(value))
}

pub open spec fn schedule_wf(value: ASchedule) -> bool {
    &&& valid_utf8(value.id)
    &&& valid_utf8(value.cron)
    &&& valid_utf8(value.promise_id)
    &&& value_wf(value.promise_param)
    &&& pair_list_wf(value.promise_tags)
    &&& record_encodable(schedule_fields(value))
}

pub open spec fn decode_schedule_spec(bytes: Seq<u8>) -> Option<ASchedule> {
    match decode_record_spec(bytes, KIND_SCHEDULE) {
        Some(fields) if fields.len() == 9
            && valid_utf8(fields[0])
            && valid_utf8(fields[1])
            && valid_utf8(fields[2]) => {
            match (
                decode_u64_spec(fields[3]),
                decode_value_spec(fields[4]),
                decode_pair_list_spec(fields[5]),
                decode_u64_spec(fields[6]),
                decode_option_u64_spec(fields[7]),
                decode_u64_spec(fields[8]),
            ) {
                (
                    Some(promise_timeout),
                    Some(promise_param),
                    Some(promise_tags),
                    Some(next_run_at),
                    Some(last_run_at),
                    Some(created_at),
                ) => Some(ASchedule {
                    id: fields[0],
                    cron: fields[1],
                    promise_id: fields[2],
                    promise_timeout,
                    promise_param,
                    promise_tags,
                    next_run_at,
                    last_run_at,
                    created_at,
                }),
                _ => None,
            }
        }
        _ => None,
    }
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(60)]
pub proof fn lemma_schedule_round_trip(value: ASchedule)
    requires schedule_wf(value),
    ensures decode_schedule_spec(schedule_bytes(value)) == Some(value),
{
    lemma_u64_round_trip(value.promise_timeout);
    lemma_value_round_trip(value.promise_param);
    lemma_pair_list_round_trip(value.promise_tags);
    lemma_u64_round_trip(value.next_run_at);
    lemma_option_u64_round_trip(value.last_run_at);
    lemma_u64_round_trip(value.created_at);
    lemma_record_round_trip(KIND_SCHEDULE, schedule_fields(value));
    assert(decode_record_spec(schedule_bytes(value), KIND_SCHEDULE)
        == Some(schedule_fields(value)));
    assert(decode_value_spec(value_bytes(value.promise_param))
        == Some(value.promise_param));
    assert(decode_pair_list_spec(pair_list_bytes(value.promise_tags))
        == Some(value.promise_tags));
    assert(decode_option_u64_spec(option_u64_bytes(value.last_run_at))
        == Some(value.last_run_at));
}

pub open spec fn store_key_fields(value: AStoreKey) -> Seq<Seq<u8>> {
    match value {
        AStoreKey::Document(id) => seq![seq![0u8], id],
        AStoreKey::Schedule(id) => seq![seq![1u8], id],
        AStoreKey::TimerOrigin { bucket, deadline, origin, token, by } => seq![
            seq![2u8],
            u64_bytes(bucket),
            u64_bytes(deadline),
            origin,
            u64_bytes(token),
            by,
        ],
        AStoreKey::TimerSchedule { bucket, deadline, id, token, by } => seq![
            seq![3u8],
            u64_bytes(bucket),
            u64_bytes(deadline),
            id,
            u64_bytes(token),
            by,
        ],
        AStoreKey::Node(id) => seq![seq![4u8], id],
        AStoreKey::Membership => seq![seq![5u8]],
    }
}

pub open spec fn store_key_wf(value: AStoreKey) -> bool {
    &&& match value {
        AStoreKey::Document(id) => valid_utf8(id),
        AStoreKey::Schedule(id) => valid_utf8(id),
        AStoreKey::TimerOrigin { origin, by, .. } => {
            valid_utf8(origin) && valid_utf8(by)
        }
        AStoreKey::TimerSchedule { id, by, .. } => {
            valid_utf8(id) && valid_utf8(by)
        }
        AStoreKey::Node(id) => valid_utf8(id),
        AStoreKey::Membership => true,
    }
    &&& record_encodable(store_key_fields(value))
}

pub open spec fn store_key_bytes(value: AStoreKey) -> Seq<u8> {
    record_bytes(KIND_STORE_KEY, store_key_fields(value))
}

pub open spec fn decode_store_key_spec(bytes: Seq<u8>) -> Option<AStoreKey> {
    match decode_record_spec(bytes, KIND_STORE_KEY) {
        Some(fields) if fields.len() == 2
            && fields[0] == seq![0u8]
            && valid_utf8(fields[1]) => Some(AStoreKey::Document(fields[1])),
        Some(fields) if fields.len() == 2
            && fields[0] == seq![1u8]
            && valid_utf8(fields[1]) => Some(AStoreKey::Schedule(fields[1])),
        Some(fields) if fields.len() == 6
            && fields[0] == seq![2u8]
            && valid_utf8(fields[3])
            && valid_utf8(fields[5]) => {
            match (
                decode_u64_spec(fields[1]),
                decode_u64_spec(fields[2]),
                decode_u64_spec(fields[4]),
            ) {
                (Some(bucket), Some(deadline), Some(token)) => {
                    Some(AStoreKey::TimerOrigin {
                        bucket,
                        deadline,
                        origin: fields[3],
                        token,
                        by: fields[5],
                    })
                }
                _ => None,
            }
        }
        Some(fields) if fields.len() == 6
            && fields[0] == seq![3u8]
            && valid_utf8(fields[3])
            && valid_utf8(fields[5]) => {
            match (
                decode_u64_spec(fields[1]),
                decode_u64_spec(fields[2]),
                decode_u64_spec(fields[4]),
            ) {
                (Some(bucket), Some(deadline), Some(token)) => {
                    Some(AStoreKey::TimerSchedule {
                        bucket,
                        deadline,
                        id: fields[3],
                        token,
                        by: fields[5],
                    })
                }
                _ => None,
            }
        }
        Some(fields) if fields.len() == 2
            && fields[0] == seq![4u8]
            && valid_utf8(fields[1]) => Some(AStoreKey::Node(fields[1])),
        Some(fields) if fields.len() == 1 && fields[0] == seq![5u8] => {
            Some(AStoreKey::Membership)
        }
        _ => None,
    }
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(30)]
pub proof fn lemma_store_key_round_trip(value: AStoreKey)
    requires store_key_wf(value),
    ensures decode_store_key_spec(store_key_bytes(value)) == Some(value),
{
    lemma_record_round_trip(KIND_STORE_KEY, store_key_fields(value));
    assert(decode_record_spec(store_key_bytes(value), KIND_STORE_KEY)
        == Some(store_key_fields(value)));
    match value {
        AStoreKey::Document(id) => {
            assert(store_key_fields(value) == seq![seq![0u8], id]);
            assert(valid_utf8(id));
            assert(decode_store_key_spec(store_key_bytes(value))
                == Some(AStoreKey::Document(id)));
        }
        AStoreKey::Schedule(id) => {
            assert(store_key_fields(value) == seq![seq![1u8], id]);
            assert(valid_utf8(id));
            assert(seq![1u8] != seq![0u8]) by (compute);
            assert(decode_store_key_spec(store_key_bytes(value))
                == Some(AStoreKey::Schedule(id)));
        }
        AStoreKey::TimerOrigin { bucket, deadline, origin, token, by } => {
            lemma_u64_round_trip(bucket);
            lemma_u64_round_trip(deadline);
            lemma_u64_round_trip(token);
            assert(store_key_fields(value) == seq![
                seq![2u8], u64_bytes(bucket), u64_bytes(deadline), origin,
                u64_bytes(token), by,
            ]);
            assert(decode_store_key_spec(store_key_bytes(value))
                == Some(AStoreKey::TimerOrigin {
                    bucket, deadline, origin, token, by,
                }));
        }
        AStoreKey::TimerSchedule { bucket, deadline, id, token, by } => {
            lemma_u64_round_trip(bucket);
            lemma_u64_round_trip(deadline);
            lemma_u64_round_trip(token);
            assert(store_key_fields(value) == seq![
                seq![3u8], u64_bytes(bucket), u64_bytes(deadline), id,
                u64_bytes(token), by,
            ]);
            assert(seq![3u8] != seq![0u8]) by (compute);
            assert(seq![3u8] != seq![1u8]) by (compute);
            assert(seq![3u8] != seq![2u8]) by (compute);
            assert(decode_store_key_spec(store_key_bytes(value))
                == Some(AStoreKey::TimerSchedule {
                    bucket, deadline, id, token, by,
                }));
        }
        AStoreKey::Node(id) => {
            assert(store_key_fields(value) == seq![seq![4u8], id]);
            assert(valid_utf8(id));
            assert(seq![4u8] != seq![0u8]) by (compute);
            assert(seq![4u8] != seq![1u8]) by (compute);
            assert(seq![4u8] != seq![2u8]) by (compute);
            assert(seq![4u8] != seq![3u8]) by (compute);
            assert(decode_store_key_spec(store_key_bytes(value))
                == Some(AStoreKey::Node(id)));
        }
        AStoreKey::Membership => {
            assert(store_key_fields(value) == seq![seq![5u8]]);
            assert(decode_store_key_spec(store_key_bytes(value))
                == Some(AStoreKey::Membership));
        }
    }
}

/// Exact recovery for arbitrary typed field layouts, used by future codecs.
pub proof fn lemma_typed_fields_round_trip(
    kind: u8,
    fields: Seq<Seq<u8>>,
)
    requires
        fields.len() <= u64::MAX,
        fields.len() <= usize::MAX,
        fields.len() <= MAX_SEQUENCE_ITEMS,
        forall|i: int| 0 <= i < fields.len() ==> {
            &&& #[trigger] fields[i].len() <= u64::MAX
            &&& fields[i].len() <= usize::MAX
        },
        blob_sequence_bytes(fields).len() <= u64::MAX,
        blob_sequence_bytes(fields).len() <= usize::MAX,
    ensures
        decode_record_spec(record_bytes(kind, fields), kind) == Some(fields),
{
    lemma_record_round_trip(kind, fields);
}

} // verus!
