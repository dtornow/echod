//! Runtime assembly of the verified primitive and typed bridge functions.

use crate::laws::*;
use crate::primitives::*;
use crate::record::{decode_record, encode_record};
use crate::text::Text;
use crate::types as model;

pub type CodecResult<T> = Result<T, &'static str>;

fn required<T>(value: Option<T>) -> CodecResult<T> {
    value.ok_or("value is not canonically encodable")
}

fn u64_field(value: u64) -> Vec<u8> {
    encode_u64(value)
}

fn parse_u64(bytes: &Vec<u8>) -> CodecResult<u64> {
    decode_u64(bytes).ok_or("invalid u64 field")
}

fn text_field(value: &Text) -> Vec<u8> {
    value.bytes.clone()
}

fn parse_text(bytes: Vec<u8>) -> CodecResult<Text> {
    Text::from_utf8(bytes).ok_or("invalid UTF-8 field")
}

fn option_u64_field(value: Option<u64>) -> CodecResult<Vec<u8>> {
    let payload = value.map(encode_u64);
    required(encode_option_blob(&payload))
}

fn parse_option_u64(bytes: &Vec<u8>) -> CodecResult<Option<u64>> {
    decode_option_blob(bytes)
        .ok_or("invalid option field")?
        .map(|value| parse_u64(&value))
        .transpose()
}

fn option_text_field(value: &Option<Text>) -> CodecResult<Vec<u8>> {
    let payload = value.as_ref().map(text_field);
    required(encode_option_blob(&payload))
}

fn parse_option_text(bytes: &Vec<u8>) -> CodecResult<Option<Text>> {
    decode_option_blob(bytes)
        .ok_or("invalid option field")?
        .map(parse_text)
        .transpose()
}

fn text_list_field(values: &[Text]) -> CodecResult<Vec<u8>> {
    let fields = values.iter().map(text_field).collect();
    required(encode_blob_sequence(&fields))
}

fn parse_text_list(bytes: &Vec<u8>) -> CodecResult<Vec<Text>> {
    decode_blob_sequence(bytes)
        .ok_or("invalid text sequence")?
        .into_iter()
        .map(parse_text)
        .collect()
}

fn pairs_field(values: &[(Text, Text)]) -> CodecResult<Vec<u8>> {
    let mut pairs = Vec::with_capacity(values.len());
    for (left, right) in values {
        let fields = vec![text_field(left), text_field(right)];
        pairs.push(required(encode_blob_sequence(&fields))?);
    }
    required(encode_blob_sequence(&pairs))
}

fn parse_pairs(bytes: &Vec<u8>) -> CodecResult<Vec<(Text, Text)>> {
    let pairs = decode_blob_sequence(bytes).ok_or("invalid pair sequence")?;
    let mut out = Vec::with_capacity(pairs.len());
    for pair in pairs {
        let mut fields = decode_blob_sequence(&pair).ok_or("invalid pair")?;
        if fields.len() != 2 {
            return Err("pair has wrong arity");
        }
        let right = parse_text(fields.pop().unwrap())?;
        let left = parse_text(fields.pop().unwrap())?;
        out.push((left, right));
    }
    Ok(out)
}

fn option_task_field(value: &Option<model::Task>) -> CodecResult<Vec<u8>> {
    let payload = value.as_ref().map(encode_task_payload).transpose()?;
    required(encode_option_blob(&payload))
}

fn parse_option_task(bytes: &Vec<u8>) -> CodecResult<Option<model::Task>> {
    decode_option_blob(bytes)
        .ok_or("invalid task option")?
        .map(|payload| decode_task_payload(&payload))
        .transpose()
}

fn encode_value(value: &model::Value) -> CodecResult<Vec<u8>> {
    let fields = vec![
        pairs_field(&value.headers)?,
        option_text_field(&value.data)?,
    ];
    required(encode_blob_sequence(&fields))
}

fn decode_value(bytes: &Vec<u8>) -> CodecResult<model::Value> {
    let fields = decode_blob_sequence(bytes).ok_or("invalid Value")?;
    if fields.len() != 2 {
        return Err("Value has wrong arity");
    }
    Ok(model::Value {
        headers: parse_pairs(&fields[0])?,
        data: parse_option_text(&fields[1])?,
    })
}

fn promise_state_field(value: echod_kernel::PromiseState) -> Vec<u8> {
    vec![match value {
        echod_kernel::PromiseState::Pending => 0,
        echod_kernel::PromiseState::Resolved => 1,
        echod_kernel::PromiseState::Rejected => 2,
        echod_kernel::PromiseState::RejectedCanceled => 3,
        echod_kernel::PromiseState::RejectedTimedout => 4,
    }]
}

fn parse_promise_state(bytes: &[u8]) -> CodecResult<echod_kernel::PromiseState> {
    match bytes {
        [0] => Ok(echod_kernel::PromiseState::Pending),
        [1] => Ok(echod_kernel::PromiseState::Resolved),
        [2] => Ok(echod_kernel::PromiseState::Rejected),
        [3] => Ok(echod_kernel::PromiseState::RejectedCanceled),
        [4] => Ok(echod_kernel::PromiseState::RejectedTimedout),
        _ => Err("invalid promise state"),
    }
}

fn task_state_field(value: echod_kernel::TaskState) -> Vec<u8> {
    vec![match value {
        echod_kernel::TaskState::Pending => 0,
        echod_kernel::TaskState::Acquired => 1,
        echod_kernel::TaskState::Suspended => 2,
        echod_kernel::TaskState::Halted => 3,
        echod_kernel::TaskState::Fulfilled => 4,
    }]
}

fn parse_task_state(bytes: &[u8]) -> CodecResult<echod_kernel::TaskState> {
    match bytes {
        [0] => Ok(echod_kernel::TaskState::Pending),
        [1] => Ok(echod_kernel::TaskState::Acquired),
        [2] => Ok(echod_kernel::TaskState::Suspended),
        [3] => Ok(echod_kernel::TaskState::Halted),
        [4] => Ok(echod_kernel::TaskState::Fulfilled),
        _ => Err("invalid task state"),
    }
}

fn encode_task_payload(value: &model::Task) -> CodecResult<Vec<u8>> {
    let fields = vec![
        task_state_field(value.state),
        u64_field(value.version),
        option_u64_field(value.ttl)?,
        option_text_field(&value.pid)?,
        option_u64_field(value.lease_timeout_at)?,
        option_u64_field(value.retry_timeout_at)?,
        text_list_field(&value.resumes)?,
    ];
    required(encode_blob_sequence(&fields))
}

fn decode_task_payload(bytes: &Vec<u8>) -> CodecResult<model::Task> {
    let fields = decode_blob_sequence(bytes).ok_or("invalid Task")?;
    if fields.len() != 7 {
        return Err("Task has wrong arity");
    }
    Ok(model::Task {
        state: parse_task_state(&fields[0])?,
        version: parse_u64(&fields[1])?,
        ttl: parse_option_u64(&fields[2])?,
        pid: parse_option_text(&fields[3])?,
        lease_timeout_at: parse_option_u64(&fields[4])?,
        retry_timeout_at: parse_option_u64(&fields[5])?,
        resumes: parse_text_list(&fields[6])?,
    })
}

pub fn encode_header(value: &model::Header) -> CodecResult<Vec<u8>> {
    required(encode_record(
        KIND_HEADER,
        &vec![u64_field(value.stamp), u64_field(value.nonce)],
    ))
}

pub fn decode_header(bytes: &Vec<u8>) -> CodecResult<model::Header> {
    let fields = decode_record(bytes, KIND_HEADER).ok_or("invalid Header")?;
    if fields.len() != 2 {
        return Err("Header has wrong arity");
    }
    Ok(model::Header {
        stamp: parse_u64(&fields[0])?,
        nonce: parse_u64(&fields[1])?,
    })
}

pub fn encode_announcement(value: &model::Announcement) -> CodecResult<Vec<u8>> {
    required(encode_record(
        KIND_ANNOUNCEMENT,
        &vec![
            text_field(&value.id),
            text_field(&value.url),
            u64_field(value.at),
        ],
    ))
}

pub fn decode_announcement(bytes: &Vec<u8>) -> CodecResult<model::Announcement> {
    let mut fields = decode_record(bytes, KIND_ANNOUNCEMENT).ok_or("invalid Announcement")?;
    if fields.len() != 3 {
        return Err("Announcement has wrong arity");
    }
    let at = parse_u64(&fields.pop().unwrap())?;
    let url = parse_text(fields.pop().unwrap())?;
    let id = parse_text(fields.pop().unwrap())?;
    Ok(model::Announcement { id, url, at })
}

pub fn encode_membership(value: &model::Membership) -> CodecResult<Vec<u8>> {
    required(encode_record(
        KIND_MEMBERSHIP,
        &vec![u64_field(value.epoch), text_list_field(&value.members)?],
    ))
}

pub fn decode_membership(bytes: &Vec<u8>) -> CodecResult<model::Membership> {
    let fields = decode_record(bytes, KIND_MEMBERSHIP).ok_or("invalid Membership")?;
    if fields.len() != 2 {
        return Err("Membership has wrong arity");
    }
    Ok(model::Membership {
        epoch: parse_u64(&fields[0])?,
        members: parse_text_list(&fields[1])?,
    })
}

pub fn encode_promise_model(value: &model::Promise) -> CodecResult<Vec<u8>> {
    let fields = vec![
        text_field(&value.id),
        promise_state_field(value.state),
        pairs_field(&value.tags)?,
        encode_value(&value.param)?,
        encode_value(&value.value)?,
        u64_field(value.timeout_at),
        u64_field(value.created_at),
        option_u64_field(value.settled_at)?,
        text_list_field(&value.callbacks)?,
        text_list_field(&value.listeners)?,
        option_task_field(&value.task)?,
    ];
    required(encode_record(KIND_PROMISE, &fields))
}

pub fn decode_promise_model(bytes: &Vec<u8>) -> CodecResult<model::Promise> {
    let fields = decode_record(bytes, KIND_PROMISE).ok_or("invalid Promise")?;
    if fields.len() != 11 {
        return Err("Promise has wrong arity");
    }
    Ok(model::Promise {
        id: parse_text(fields[0].clone())?,
        state: parse_promise_state(&fields[1])?,
        tags: parse_pairs(&fields[2])?,
        param: decode_value(&fields[3])?,
        value: decode_value(&fields[4])?,
        timeout_at: parse_u64(&fields[5])?,
        created_at: parse_u64(&fields[6])?,
        settled_at: parse_option_u64(&fields[7])?,
        callbacks: parse_text_list(&fields[8])?,
        listeners: parse_text_list(&fields[9])?,
        task: parse_option_task(&fields[10])?,
    })
}

pub fn encode_schedule_model(value: &model::Schedule) -> CodecResult<Vec<u8>> {
    let fields = vec![
        text_field(&value.id),
        text_field(&value.cron),
        text_field(&value.promise_id),
        u64_field(value.promise_timeout),
        encode_value(&value.promise_param)?,
        pairs_field(&value.promise_tags)?,
        u64_field(value.next_run_at),
        option_u64_field(value.last_run_at)?,
        u64_field(value.created_at),
    ];
    required(encode_record(KIND_SCHEDULE, &fields))
}

pub fn decode_schedule_model(bytes: &Vec<u8>) -> CodecResult<model::Schedule> {
    let fields = decode_record(bytes, KIND_SCHEDULE).ok_or("invalid Schedule")?;
    if fields.len() != 9 {
        return Err("Schedule has wrong arity");
    }
    Ok(model::Schedule {
        id: parse_text(fields[0].clone())?,
        cron: parse_text(fields[1].clone())?,
        promise_id: parse_text(fields[2].clone())?,
        promise_timeout: parse_u64(&fields[3])?,
        promise_param: decode_value(&fields[4])?,
        promise_tags: parse_pairs(&fields[5])?,
        next_run_at: parse_u64(&fields[6])?,
        last_run_at: parse_option_u64(&fields[7])?,
        created_at: parse_u64(&fields[8])?,
    })
}

pub fn encode_store_key(value: &model::StoreKey) -> CodecResult<Vec<u8>> {
    let fields = match value {
        model::StoreKey::Document(id) => vec![vec![0], text_field(id)],
        model::StoreKey::Schedule(id) => vec![vec![1], text_field(id)],
        model::StoreKey::TimerOrigin {
            bucket,
            deadline,
            origin,
            token,
            by,
        } => vec![
            vec![2],
            u64_field(*bucket),
            u64_field(*deadline),
            text_field(origin),
            u64_field(*token),
            text_field(by),
        ],
        model::StoreKey::TimerSchedule {
            bucket,
            deadline,
            id,
            token,
            by,
        } => vec![
            vec![3],
            u64_field(*bucket),
            u64_field(*deadline),
            text_field(id),
            u64_field(*token),
            text_field(by),
        ],
        model::StoreKey::Node(id) => vec![vec![4], text_field(id)],
        model::StoreKey::Membership => vec![vec![5]],
    };
    required(encode_record(KIND_STORE_KEY, &fields))
}

pub fn decode_store_key(bytes: &Vec<u8>) -> CodecResult<model::StoreKey> {
    let fields = decode_record(bytes, KIND_STORE_KEY).ok_or("invalid StoreKey")?;
    match fields.first().map(Vec::as_slice) {
        Some([0]) if fields.len() == 2 => {
            Ok(model::StoreKey::Document(parse_text(fields[1].clone())?))
        }
        Some([1]) if fields.len() == 2 => {
            Ok(model::StoreKey::Schedule(parse_text(fields[1].clone())?))
        }
        Some([2]) if fields.len() == 6 => Ok(model::StoreKey::TimerOrigin {
            bucket: parse_u64(&fields[1])?,
            deadline: parse_u64(&fields[2])?,
            origin: parse_text(fields[3].clone())?,
            token: parse_u64(&fields[4])?,
            by: parse_text(fields[5].clone())?,
        }),
        Some([3]) if fields.len() == 6 => Ok(model::StoreKey::TimerSchedule {
            bucket: parse_u64(&fields[1])?,
            deadline: parse_u64(&fields[2])?,
            id: parse_text(fields[3].clone())?,
            token: parse_u64(&fields[4])?,
            by: parse_text(fields[5].clone())?,
        }),
        Some([4]) if fields.len() == 2 => Ok(model::StoreKey::Node(parse_text(fields[1].clone())?)),
        Some([5]) if fields.len() == 1 => Ok(model::StoreKey::Membership),
        _ => Err("invalid StoreKey variant"),
    }
}

pub fn encode_promise(value: &echod_kernel::Promise) -> CodecResult<Vec<u8>> {
    encode_promise_model(&crate::bridge::promise_model(value))
}

pub fn decode_promise(bytes: &Vec<u8>) -> CodecResult<echod_kernel::Promise> {
    let value = decode_promise_model(bytes)?;
    Ok(crate::bridge::kernel_promise(value))
}

pub fn encode_schedule(value: &echod_kernel::Schedule) -> CodecResult<Vec<u8>> {
    encode_schedule_model(&crate::bridge::schedule_model(value))
}

pub fn decode_schedule(bytes: &Vec<u8>) -> CodecResult<echod_kernel::Schedule> {
    let value = decode_schedule_model(bytes)?;
    Ok(crate::bridge::kernel_schedule(value))
}
