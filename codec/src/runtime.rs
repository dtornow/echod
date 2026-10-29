//! Runtime assembly of the verified primitive and typed bridge functions.

use vstd::prelude::*;

use crate::laws::*;
use crate::primitives::*;
#[cfg(verus_keep_ghost)]
use crate::record::decode_record_spec;
use crate::record::{decode_record, encode_record};
#[cfg(verus_keep_ghost)]
use crate::text::valid_utf8;
use crate::text::Text;
use crate::types as model;

verus! {

pub type CodecResult<T> = Result<T, &'static str>;

proof fn lemma_subrange_step<A>(values: Seq<A>, i: int)
    requires 0 <= i < values.len(),
    ensures
        values.subrange(i, values.len() as int)[0] == values[i],
        values.subrange(0, i + 1)
            == values.subrange(0, i).push(values[i]),
        values.subrange(i + 1, values.len() as int)
            == values.subrange(i, values.len() as int).drop_first(),
{
}

proof fn lemma_pair_list_items_push(
    values: Seq<(Seq<u8>, Seq<u8>)>,
    value: (Seq<u8>, Seq<u8>),
)
    ensures
        pair_list_items(values.push(value))
            == pair_list_items(values).push(pair_bytes(value)),
{
}

proof fn lemma_decode_text_list_invalid(
    bytes: Seq<u8>,
    items: Seq<Seq<u8>>,
    index: int,
)
    requires
        decode_blob_sequence_spec(bytes) == Some(items),
        0 <= index < items.len(),
        !valid_utf8(items[index]),
    ensures decode_text_list_spec(bytes) is None,
{
    assert(!all_valid_utf8(items)) by {
        if all_valid_utf8(items) {
            assert(valid_utf8(items[index]));
        }
    }
}

proof fn lemma_decode_pair_items_head_none(items: Seq<Seq<u8>>)
    requires
        items.len() > 0,
        decode_pair_spec(items[0]) is None,
    ensures decode_pair_items(items) is None,
{
    reveal_with_fuel(decode_pair_items, 2);
}

proof fn lemma_decode_pair_items_rest_none(
    items: Seq<Seq<u8>>,
    first: (Seq<u8>, Seq<u8>),
)
    requires
        items.len() > 0,
        decode_pair_spec(items[0]) == Some(first),
        decode_pair_items(items.drop_first()) is None,
    ensures decode_pair_items(items) is None,
{
    reveal_with_fuel(decode_pair_items, 2);
}

proof fn lemma_decode_pair_items_some(
    items: Seq<Seq<u8>>,
    first: (Seq<u8>, Seq<u8>),
    rest: Seq<(Seq<u8>, Seq<u8>)>,
)
    requires
        items.len() > 0,
        decode_pair_spec(items[0]) == Some(first),
        decode_pair_items(items.drop_first()) == Some(rest),
    ensures
        decode_pair_items(items) == Some(seq![first] + rest),
{
    reveal_with_fuel(decode_pair_items, 2);
}

fn push_deep<T: DeepView>(values: &mut Vec<T>, value: T)
    ensures
        final(values).deep_view()
            == old(values).deep_view().push(value.deep_view()),
{
    let ghost old_vec = values@;
    let ghost old_values = values.deep_view();
    let ghost value_view = value.deep_view();
    values.push(value);
    assert(values.deep_view() =~= old_values.push(value_view)) by {
        assert(values.deep_view().len() == old_values.len() + 1);
        assert forall|i: int| 0 <= i < values.deep_view().len()
            implies values.deep_view()[i]
                == old_values.push(value_view)[i] by {
            if i < old_values.len() {
                assert(values@[i] == old_vec[i]);
                assert(old_values[i] == old_vec[i].deep_view());
            } else {
                assert(i == old_values.len());
            }
        }
    }
}

fn push_bytes(values: &mut Vec<Vec<u8>>, value: Vec<u8>)
    ensures
        final(values).deep_view()
            == old(values).deep_view().push(value@),
{
    let ghost value_view = value@;
    assert(value.deep_view() == value_view);
    push_deep(values, value);
}

fn required<T>(value: Option<T>) -> (result: CodecResult<T>)
    ensures
        match result {
            Ok(result) => value == Some(result),
            Err(_) => value is None,
        },
{
    value.ok_or("value is not canonically encodable")
}

fn u64_field(value: u64) -> (bytes: Vec<u8>)
    ensures bytes@ == u64_bytes(value),
{
    encode_u64(value)
}

fn parse_u64(bytes: &Vec<u8>) -> (result: CodecResult<u64>)
    ensures
        match result {
            Ok(value) => decode_u64_spec(bytes@) == Some(value),
            Err(_) => decode_u64_spec(bytes@) is None,
        },
{
    decode_u64(bytes).ok_or("invalid u64 field")
}

fn text_field(value: &Text) -> (bytes: Vec<u8>)
    ensures bytes@ == value@,
{
    value.bytes.clone()
}

fn tag_field(value: u8) -> (bytes: Vec<u8>)
    ensures bytes@ == seq![value],
{
    let mut bytes = Vec::new();
    bytes.push(value);
    bytes
}

fn parse_text(bytes: &Vec<u8>) -> (result: CodecResult<Text>)
    ensures
        match result {
            Ok(value) => value@ == bytes@ && valid_utf8(value@),
            Err(_) => !valid_utf8(bytes@),
        },
{
    Text::from_utf8(bytes.clone()).ok_or("invalid UTF-8 field")
}

fn option_u64_field(value: Option<u64>) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == option_u64_bytes(value),
{
    let payload = match value {
        None => None,
        Some(value) => Some(encode_u64(value)),
    };
    match encode_option_blob(&payload) {
        None => Err("value is not canonically encodable"),
        Some(bytes) => Ok(bytes),
    }
}

fn parse_option_u64(
    bytes: &Vec<u8>,
) -> (result: CodecResult<Option<u64>>)
    ensures
        match result {
            Ok(value) => decode_option_u64_spec(bytes@) == Some(value),
            Err(_) => decode_option_u64_spec(bytes@) is None,
        },
{
    match decode_option_blob(bytes) {
        None => Err("invalid option field"),
        Some(None) => Ok(None),
        Some(Some(value)) => match parse_u64(&value) {
            Ok(value) => Ok(Some(value)),
            Err(error) => Err(error),
        },
    }
}

fn option_text_field(
    value: &Option<Text>,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok
            ==> result->Ok_0@ == option_text_bytes(value.deep_view()),
{
    let payload = match value {
        None => None,
        Some(value) => Some(text_field(value)),
    };
    match encode_option_blob(&payload) {
        None => Err("value is not canonically encodable"),
        Some(bytes) => Ok(bytes),
    }
}

fn parse_option_text(
    bytes: &Vec<u8>,
) -> (result: CodecResult<Option<Text>>)
    ensures
        match result {
            Ok(value) => {
                &&& decode_option_text_spec(bytes@) == Some(value.deep_view())
                &&& value is Some ==> value->Some_0.wf()
            }
            Err(_) => decode_option_text_spec(bytes@) is None,
        },
{
    match decode_option_blob(bytes) {
        None => {
            assert(decode_option_blob_spec(bytes@) is None);
            Err("invalid option field")
        }
        Some(None) => {
            assert(decode_option_blob_spec(bytes@) == Some(None));
            Ok(None)
        }
        Some(Some(payload)) => {
            let ghost payload_view = payload@;
            assert(decode_option_blob_spec(bytes@) == Some(Some(payload_view)));
            match parse_text(&payload) {
                Ok(value) => {
                    assert(value@ == payload_view);
                    assert(decode_option_text_spec(bytes@)
                        == Some(Some(value@)));
                    Ok(Some(value))
                }
                Err(error) => {
                    assert(!valid_utf8(payload_view));
                    assert(decode_option_text_spec(bytes@) is None);
                    Err(error)
                }
            }
        }
    }
}

fn text_list_field(values: &Vec<Text>) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok
            ==> result->Ok_0@ == text_list_bytes(values.deep_view()),
{
    let mut fields: Vec<Vec<u8>> = Vec::new();
    let mut i = 0usize;
    while i < values.len()
        invariant
            i <= values.len(),
            fields.deep_view()
                == values.deep_view().subrange(0, i as int),
        decreases values.len() - i,
    {
        let ghost old_fields = fields.deep_view();
        let field = text_field(&values[i]);
        let ghost field_view = field.deep_view();
        let ghost item = values.deep_view()[i as int];
        assert(field@ == item);
        assert(field_view == item);
        proof {
            lemma_subrange_step(values.deep_view(), i as int);
        }
        push_bytes(&mut fields, field);
        assert(fields.deep_view() == old_fields.push(field_view));
        i += 1;
    }
    assert(values.deep_view().subrange(0, values.len() as int)
        == values.deep_view());
    match encode_blob_sequence(&fields) {
        None => Err("value is not canonically encodable"),
        Some(bytes) => Ok(bytes),
    }
}

fn parse_text_list(bytes: &Vec<u8>) -> (result: CodecResult<Vec<Text>>)
    ensures
        match result {
            Ok(value) => {
                &&& decode_text_list_spec(bytes@) == Some(value.deep_view())
                &&& forall|i: int| 0 <= i < value.len()
                    ==> value[i].wf()
            }
            Err(_) => decode_text_list_spec(bytes@) is None,
        },
{
    let fields = match decode_blob_sequence(bytes) {
        None => return Err("invalid text sequence"),
        Some(fields) => fields,
    };
    let ghost original = fields.deep_view();
    assert(decode_blob_sequence_spec(bytes@) == Some(original));
    let mut fields = fields;
    let mut out: Vec<Text> = Vec::new();
    while fields.len() > 0
        invariant
            fields.len() + out.len() == original.len(),
            decode_blob_sequence_spec(bytes@) == Some(original),
            fields.deep_view()
                == original.subrange(out.len() as int, original.len() as int),
            out.deep_view()
                == original.subrange(0, out.len() as int),
            forall|i: int| 0 <= i < out.len() ==> out[i].wf(),
        decreases fields.len(),
    {
        let ghost index = out.len() as int;
        proof {
            lemma_subrange_step(original, index);
        }
        let first = fields.remove(0);
        let ghost first_view = first@;
        assert(first_view == original[index]);
        assert(fields.deep_view()
            == original.subrange(index + 1, original.len() as int));
        match parse_text(&first) {
            Err(error) => {
                assert(!valid_utf8(first_view));
                assert(!all_valid_utf8(original)) by {
                    if all_valid_utf8(original) {
                        assert(valid_utf8(original[index]));
                    }
                }
                proof {
                    lemma_decode_text_list_invalid(bytes@, original, index);
                }
                return Err(error);
            }
            Ok(text) => {
                assert(text@ == original[index]);
                out.push(text);
            }
        }
    }
    assert(out.len() == original.len());
    assert(out.deep_view() == original);
    assert(all_valid_utf8(original));
    Ok(out)
}

fn pairs_field(
    values: &Vec<(Text, Text)>,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok
            ==> result->Ok_0@ == pair_list_bytes(values.deep_view()),
{
    let mut pairs: Vec<Vec<u8>> = Vec::new();
    let mut i = 0usize;
    while i < values.len()
        invariant
            i <= values.len(),
            pairs.deep_view()
                == pair_list_items(
                    values.deep_view().subrange(0, i as int),
                ),
        decreases values.len() - i,
    {
        let ghost old_pairs = pairs.deep_view();
        let ghost prefix =
            values.deep_view().subrange(0, i as int);
        let ghost item = values.deep_view()[i as int];
        proof {
            lemma_subrange_step(values.deep_view(), i as int);
        }
        let mut fields = Vec::new();
        let left = text_field(&values[i].0);
        let right = text_field(&values[i].1);
        let ghost left_view = left.deep_view();
        let ghost right_view = right.deep_view();
        assert(left@ == item.0);
        assert(right@ == item.1);
        assert(left_view == item.0);
        assert(right_view == item.1);
        push_bytes(&mut fields, left);
        push_bytes(&mut fields, right);
        assert(fields.deep_view() =~= seq![left_view, right_view]);
        let pair = match encode_blob_sequence(&fields) {
            None => return Err("value is not canonically encodable"),
            Some(pair) => pair,
        };
        assert(pair@ == pair_bytes(item));
        let ghost pair_view = pair.deep_view();
        assert(pair_view == pair_bytes(item));
        push_bytes(&mut pairs, pair);
        assert(pairs.deep_view() == old_pairs.push(pair_view));
        proof {
            lemma_pair_list_items_push(prefix, item);
        }
        i += 1;
    }
    assert(values.deep_view().subrange(0, values.len() as int)
        == values.deep_view());
    match encode_blob_sequence(&pairs) {
        None => Err("value is not canonically encodable"),
        Some(bytes) => Ok(bytes),
    }
}

fn parse_pair_items(
    items: &Vec<Vec<u8>>,
    index: usize,
) -> (result: CodecResult<Vec<(Text, Text)>>)
    requires index <= items.len(),
    ensures
        match result {
            Ok(value) => {
                &&& decode_pair_items(items.deep_view().subrange(
                    index as int, items.len() as int,
                ))
                    == Some(value.deep_view())
                &&& forall|i: int| 0 <= i < value.len() ==> {
                    &&& value[i].0.wf()
                    &&& value[i].1.wf()
                }
            }
            Err(_) => decode_pair_items(items.deep_view().subrange(
                index as int, items.len() as int,
            )) is None,
        },
    decreases items.len() - index,
{
    if index == items.len() {
        return Ok(Vec::new());
    }
    let ghost remaining =
        items.deep_view().subrange(index as int, items.len() as int);
    proof {
        lemma_subrange_step(items.deep_view(), index as int);
    }
    assert(remaining.len() > 0);
    assert(remaining[0] == items.deep_view()[index as int]);
    assert(remaining.drop_first()
        == items.deep_view().subrange(
            index as int + 1, items.len() as int,
        ));
    let first_bytes = &items[index];
    assert(first_bytes@ == items.deep_view()[index as int]);
    assert(first_bytes@ == remaining[0]);
    let fields = match decode_blob_sequence(first_bytes) {
        None => {
            assert(decode_pair_spec(first_bytes@) is None);
            assert(decode_pair_spec(remaining[0]) is None);
            proof {
                lemma_decode_pair_items_head_none(remaining);
            }
            return Err("invalid pair");
        }
        Some(fields) => fields,
    };
    assert(decode_blob_sequence_spec(first_bytes@)
        == Some(fields.deep_view()));
    if fields.len() != 2 {
        assert(decode_pair_spec(first_bytes@) is None);
        assert(decode_pair_spec(remaining[0]) is None);
        proof {
            lemma_decode_pair_items_head_none(remaining);
        }
        return Err("pair has wrong arity");
    }
    assert(fields[0]@ == fields.deep_view()[0]);
    assert(fields[1]@ == fields.deep_view()[1]);
    let left = match parse_text(&fields[0]) {
        Err(error) => {
            assert(!valid_utf8(fields.deep_view()[0]));
            assert(decode_pair_spec(first_bytes@) is None);
            assert(decode_pair_spec(remaining[0]) is None);
            proof {
                lemma_decode_pair_items_head_none(remaining);
            }
            return Err(error);
        }
        Ok(left) => left,
    };
    let right = match parse_text(&fields[1]) {
        Err(error) => {
            assert(valid_utf8(fields.deep_view()[0]));
            assert(!valid_utf8(fields.deep_view()[1]));
            assert(decode_pair_spec(first_bytes@) is None);
            assert(decode_pair_spec(remaining[0]) is None);
            proof {
                lemma_decode_pair_items_head_none(remaining);
            }
            return Err(error);
        }
        Ok(right) => right,
    };
    let ghost first = (left@, right@);
    assert(valid_utf8(fields.deep_view()[0]));
    assert(valid_utf8(fields.deep_view()[1]));
    assert(decode_pair_spec(first_bytes@) == Some(first));
    assert(decode_pair_spec(remaining[0]) == Some(first));
    let mut rest = match parse_pair_items(items, index + 1) {
        Err(error) => {
            assert(decode_pair_items(remaining.drop_first()) is None);
            proof {
                lemma_decode_pair_items_rest_none(remaining, first);
            }
            return Err(error);
        }
        Ok(rest) => rest,
    };
    let ghost old_rest = rest.deep_view();
    rest.insert(0, (left, right));
    assert(rest.deep_view() =~= seq![first] + old_rest);
    proof {
        lemma_decode_pair_items_some(remaining, first, old_rest);
    }
    Ok(rest)
}

fn parse_pairs(
    bytes: &Vec<u8>,
) -> (result: CodecResult<Vec<(Text, Text)>>)
    ensures
        match result {
            Ok(value) => {
                &&& decode_pair_list_spec(bytes@) == Some(value.deep_view())
                &&& forall|i: int| 0 <= i < value.len() ==> {
                    &&& value[i].0.wf()
                    &&& value[i].1.wf()
                }
            }
            Err(_) => decode_pair_list_spec(bytes@) is None,
        },
{
    match decode_blob_sequence(bytes) {
        None => Err("invalid pair sequence"),
        Some(items) => {
            assert(items.deep_view().subrange(0, items.len() as int)
                == items.deep_view());
            parse_pair_items(&items, 0)
        }
    }
}

fn option_task_field(
    value: &Option<model::Task>,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok
            ==> result->Ok_0@ == option_task_bytes(value.deep_view()),
{
    let payload = match value {
        None => None,
        Some(value) => match encode_task_payload(value) {
            Ok(payload) => Some(payload),
            Err(error) => return Err(error),
        },
    };
    required(encode_option_blob(&payload))
}

fn parse_option_task(
    bytes: &Vec<u8>,
) -> (result: CodecResult<Option<model::Task>>)
    ensures
        match result {
            Ok(value) => decode_option_task_spec(bytes@)
                == Some(value.deep_view()),
            Err(_) => decode_option_task_spec(bytes@) is None,
        },
{
    match decode_option_blob(bytes) {
        None => {
            assert(decode_option_blob_spec(bytes@) is None);
            Err("invalid task option")
        }
        Some(None) => {
            assert(decode_option_blob_spec(bytes@) == Some(None));
            Ok(None)
        }
        Some(Some(payload)) => {
            let ghost payload_view = payload@;
            assert(decode_option_blob_spec(bytes@)
                == Some(Some(payload_view)));
            match decode_task_payload(&payload) {
                Ok(value) => {
                    assert(decode_task_spec(payload_view) == Some(value@));
                    Ok(Some(value))
                }
                Err(error) => {
                    assert(decode_task_spec(payload_view) is None);
                    Err(error)
                }
            }
        }
    }
}

fn encode_value(
    value: &model::Value,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == value_bytes(value@),
{
    let mut fields = Vec::new();
    push_bytes(&mut fields, pairs_field(&value.headers)?);
    push_bytes(&mut fields, option_text_field(&value.data)?);
    assert(fields.deep_view() == value_fields(value@));
    required(encode_blob_sequence(&fields))
}

fn decode_value(
    bytes: &Vec<u8>,
) -> (result: CodecResult<model::Value>)
    ensures
        match result {
            Ok(value) => {
                &&& decode_value_spec(bytes@) == Some(value@)
                &&& crate::bridge::value_text_wf(value@)
            }
            Err(_) => decode_value_spec(bytes@) is None,
        },
{
    let fields = match decode_blob_sequence(bytes) {
        None => return Err("invalid Value"),
        Some(fields) => fields,
    };
    let ghost field_views = fields.deep_view();
    assert(decode_blob_sequence_spec(bytes@) == Some(field_views));
    if fields.len() != 2 {
        return Err("Value has wrong arity");
    }
    assert(fields[0]@ == field_views[0]);
    assert(fields[1]@ == field_views[1]);
    let headers = match parse_pairs(&fields[0]) {
        Err(error) => {
            assert(decode_pair_list_spec(field_views[0]) is None);
            return Err(error);
        }
        Ok(headers) => headers,
    };
    let data = match parse_option_text(&fields[1]) {
        Err(error) => {
            assert(decode_option_text_spec(field_views[1]) is None);
            return Err(error);
        }
        Ok(data) => data,
    };
    let value = model::Value { headers, data };
    assert(decode_value_spec(bytes@) == Some(value@));
    assert(crate::bridge::value_text_wf(value@));
    Ok(value)
}

fn promise_state_field(
    value: echod_kernel::PromiseState,
) -> (bytes: Vec<u8>)
    ensures bytes@ == promise_state_bytes(value),
{
    vec![match value {
        echod_kernel::PromiseState::Pending => 0,
        echod_kernel::PromiseState::Resolved => 1,
        echod_kernel::PromiseState::Rejected => 2,
        echod_kernel::PromiseState::RejectedCanceled => 3,
        echod_kernel::PromiseState::RejectedTimedout => 4,
    }]
}

fn parse_promise_state(
    bytes: &Vec<u8>,
) -> (result: CodecResult<echod_kernel::PromiseState>)
    ensures
        match result {
            Ok(value) => decode_promise_state_spec(bytes@) == Some(value),
            Err(_) => decode_promise_state_spec(bytes@) is None,
        },
{
    if bytes.len() != 1 {
        assert(decode_promise_state_spec(bytes@) is None);
        Err("invalid promise state")
    } else if bytes[0] == 0 {
        assert(bytes@ =~= seq![0u8]);
        Ok(echod_kernel::PromiseState::Pending)
    } else if bytes[0] == 1 {
        assert(bytes@ =~= seq![1u8]);
        Ok(echod_kernel::PromiseState::Resolved)
    } else if bytes[0] == 2 {
        assert(bytes@ =~= seq![2u8]);
        Ok(echod_kernel::PromiseState::Rejected)
    } else if bytes[0] == 3 {
        assert(bytes@ =~= seq![3u8]);
        Ok(echod_kernel::PromiseState::RejectedCanceled)
    } else if bytes[0] == 4 {
        assert(bytes@ =~= seq![4u8]);
        Ok(echod_kernel::PromiseState::RejectedTimedout)
    } else {
        assert(decode_promise_state_spec(bytes@) is None);
        Err("invalid promise state")
    }
}

fn task_state_field(
    value: echod_kernel::TaskState,
) -> (bytes: Vec<u8>)
    ensures bytes@ == task_state_bytes(value),
{
    vec![match value {
        echod_kernel::TaskState::Pending => 0,
        echod_kernel::TaskState::Acquired => 1,
        echod_kernel::TaskState::Suspended => 2,
        echod_kernel::TaskState::Halted => 3,
        echod_kernel::TaskState::Fulfilled => 4,
    }]
}

fn parse_task_state(
    bytes: &Vec<u8>,
) -> (result: CodecResult<echod_kernel::TaskState>)
    ensures
        match result {
            Ok(value) => decode_task_state_spec(bytes@) == Some(value),
            Err(_) => decode_task_state_spec(bytes@) is None,
        },
{
    if bytes.len() != 1 {
        assert(decode_task_state_spec(bytes@) is None);
        Err("invalid task state")
    } else if bytes[0] == 0 {
        assert(bytes@ =~= seq![0u8]);
        Ok(echod_kernel::TaskState::Pending)
    } else if bytes[0] == 1 {
        assert(bytes@ =~= seq![1u8]);
        Ok(echod_kernel::TaskState::Acquired)
    } else if bytes[0] == 2 {
        assert(bytes@ =~= seq![2u8]);
        Ok(echod_kernel::TaskState::Suspended)
    } else if bytes[0] == 3 {
        assert(bytes@ =~= seq![3u8]);
        Ok(echod_kernel::TaskState::Halted)
    } else if bytes[0] == 4 {
        assert(bytes@ =~= seq![4u8]);
        Ok(echod_kernel::TaskState::Fulfilled)
    } else {
        assert(decode_task_state_spec(bytes@) is None);
        Err("invalid task state")
    }
}

fn encode_task_payload(
    value: &model::Task,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == task_bytes(value@),
{
    let mut fields = Vec::new();
    push_bytes(&mut fields, task_state_field(value.state));
    push_bytes(&mut fields, u64_field(value.version));
    push_bytes(&mut fields, option_u64_field(value.ttl)?);
    push_bytes(&mut fields, option_text_field(&value.pid)?);
    push_bytes(&mut fields, option_u64_field(value.lease_timeout_at)?);
    push_bytes(&mut fields, option_u64_field(value.retry_timeout_at)?);
    push_bytes(&mut fields, text_list_field(&value.resumes)?);
    assert(fields.deep_view() =~= task_fields(value@));
    required(encode_blob_sequence(&fields))
}

fn decode_task_payload(
    bytes: &Vec<u8>,
) -> (result: CodecResult<model::Task>)
    ensures
        match result {
            Ok(value) => {
                &&& decode_task_spec(bytes@) == Some(value@)
                &&& crate::bridge::task_text_wf(value@)
            }
            Err(_) => decode_task_spec(bytes@) is None,
        },
{
    let fields = match decode_blob_sequence(bytes) {
        None => return Err("invalid Task"),
        Some(fields) => fields,
    };
    let ghost field_views = fields.deep_view();
    assert(decode_blob_sequence_spec(bytes@) == Some(field_views));
    if fields.len() != 7 {
        return Err("Task has wrong arity");
    }
    assert forall|i: int| 0 <= i < 7
        implies fields[i]@ == field_views[i] by {
    }
    let state = match parse_task_state(&fields[0]) {
        Err(error) => {
            assert(decode_task_state_spec(field_views[0]) is None);
            assert(decode_task_spec(bytes@) is None);
            return Err(error);
        }
        Ok(value) => value,
    };
    let version = match parse_u64(&fields[1]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let ttl = match parse_option_u64(&fields[2]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let pid = match parse_option_text(&fields[3]) {
        Err(error) => {
            assert(decode_option_text_spec(field_views[3]) is None);
            assert(decode_task_spec(bytes@) is None);
            return Err(error);
        }
        Ok(value) => value,
    };
    let lease_timeout_at = match parse_option_u64(&fields[4]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let retry_timeout_at = match parse_option_u64(&fields[5]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let resumes = match parse_text_list(&fields[6]) {
        Err(error) => {
            assert(decode_text_list_spec(field_views[6]) is None);
            assert(decode_task_spec(bytes@) is None);
            return Err(error);
        }
        Ok(value) => value,
    };
    let value = model::Task {
        state,
        version,
        ttl,
        pid,
        lease_timeout_at,
        retry_timeout_at,
        resumes,
    };
    assert(decode_task_spec(bytes@) == Some(value@));
    assert(crate::bridge::task_text_wf(value@));
    Ok(value)
}

pub fn encode_header(
    value: &model::Header,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == header_bytes(value@),
        result is Ok ==> decode_header_spec(result->Ok_0@)
            == Some(value@),
{
    let mut fields = Vec::new();
    push_bytes(&mut fields, u64_field(value.stamp));
    push_bytes(&mut fields, u64_field(value.nonce));
    assert(fields.deep_view() == header_fields(value@));
    let result = required(encode_record(KIND_HEADER, &fields));
    proof {
        if result is Ok {
            lemma_header_round_trip(value@);
        }
    }
    result
}

pub fn decode_header(
    bytes: &Vec<u8>,
) -> (result: CodecResult<model::Header>)
    ensures
        match result {
            Ok(value) => decode_header_spec(bytes@) == Some(value@),
            Err(_) => decode_header_spec(bytes@) is None,
        },
{
    let fields = decode_record(bytes, KIND_HEADER).ok_or("invalid Header")?;
    if fields.len() != 2 {
        return Err("Header has wrong arity");
    }
    Ok(model::Header {
        stamp: parse_u64(&fields[0])?,
        nonce: parse_u64(&fields[1])?,
    })
}

pub fn encode_announcement(
    value: &model::Announcement,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == announcement_bytes(value@),
        result is Ok && announcement_wf(value@)
            ==> decode_announcement_spec(result->Ok_0@) == Some(value@),
{
    let mut fields = Vec::new();
    push_bytes(&mut fields, text_field(&value.id));
    push_bytes(&mut fields, text_field(&value.url));
    push_bytes(&mut fields, u64_field(value.at));
    assert(fields.deep_view() == announcement_fields(value@));
    let result = required(encode_record(KIND_ANNOUNCEMENT, &fields));
    proof {
        if result is Ok && announcement_wf(value@) {
            lemma_announcement_round_trip(value@);
        }
    }
    result
}

pub fn decode_announcement(
    bytes: &Vec<u8>,
) -> (result: CodecResult<model::Announcement>)
    ensures
        match result {
            Ok(value) => decode_announcement_spec(bytes@) == Some(value@),
            Err(_) => decode_announcement_spec(bytes@) is None,
        },
{
    let fields = match decode_record(bytes, KIND_ANNOUNCEMENT) {
        None => return Err("invalid Announcement"),
        Some(fields) => fields,
    };
    let ghost field_views = fields.deep_view();
    assert(decode_record_spec(bytes@, KIND_ANNOUNCEMENT)
        == Some(field_views));
    if fields.len() != 3 {
        return Err("Announcement has wrong arity");
    }
    assert forall|i: int| 0 <= i < 3
        implies fields[i]@ == field_views[i] by {
    }
    let id = match parse_text(&fields[0]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let url = match parse_text(&fields[1]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let at = match parse_u64(&fields[2]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let value = model::Announcement { id, url, at };
    assert(decode_announcement_spec(bytes@) == Some(value@));
    Ok(value)
}

pub fn encode_membership(
    value: &model::Membership,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == membership_bytes(value@),
        result is Ok && membership_wf(value@)
            ==> decode_membership_spec(result->Ok_0@) == Some(value@),
{
    let mut fields = Vec::new();
    push_bytes(&mut fields, u64_field(value.epoch));
    push_bytes(&mut fields, text_list_field(&value.members)?);
    assert(fields.deep_view() == membership_fields(value@));
    let result = required(encode_record(KIND_MEMBERSHIP, &fields));
    proof {
        if result is Ok && membership_wf(value@) {
            lemma_membership_round_trip(value@);
        }
    }
    result
}

pub fn decode_membership(
    bytes: &Vec<u8>,
) -> (result: CodecResult<model::Membership>)
    ensures
        match result {
            Ok(value) => decode_membership_spec(bytes@) == Some(value@),
            Err(_) => decode_membership_spec(bytes@) is None,
        },
{
    let fields = match decode_record(bytes, KIND_MEMBERSHIP) {
        None => return Err("invalid Membership"),
        Some(fields) => fields,
    };
    let ghost field_views = fields.deep_view();
    assert(decode_record_spec(bytes@, KIND_MEMBERSHIP)
        == Some(field_views));
    if fields.len() != 2 {
        return Err("Membership has wrong arity");
    }
    assert(fields[0]@ == field_views[0]);
    assert(fields[1]@ == field_views[1]);
    let epoch = match parse_u64(&fields[0]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let members = match parse_text_list(&fields[1]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let value = model::Membership { epoch, members };
    assert(decode_membership_spec(bytes@) == Some(value@));
    Ok(value)
}

pub fn encode_promise_model(
    value: &model::Promise,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == promise_bytes(value@),
        result is Ok && promise_wf(value@)
            ==> decode_promise_spec(result->Ok_0@) == Some(value@),
{
    let mut fields = Vec::new();
    push_bytes(&mut fields, text_field(&value.id));
    push_bytes(&mut fields, promise_state_field(value.state));
    push_bytes(&mut fields, pairs_field(&value.tags)?);
    push_bytes(&mut fields, encode_value(&value.param)?);
    push_bytes(&mut fields, encode_value(&value.value)?);
    push_bytes(&mut fields, u64_field(value.timeout_at));
    push_bytes(&mut fields, u64_field(value.created_at));
    push_bytes(&mut fields, option_u64_field(value.settled_at)?);
    push_bytes(&mut fields, text_list_field(&value.callbacks)?);
    push_bytes(&mut fields, text_list_field(&value.listeners)?);
    push_bytes(&mut fields, option_task_field(&value.task)?);
    assert(fields.deep_view() =~= promise_fields(value@));
    let result = required(encode_record(KIND_PROMISE, &fields));
    proof {
        if result is Ok && promise_wf(value@) {
            lemma_promise_round_trip(value@);
        }
    }
    result
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(80)]
pub fn decode_promise_model(
    bytes: &Vec<u8>,
) -> (result: CodecResult<model::Promise>)
    ensures
        match result {
            Ok(value) => {
                &&& decode_promise_spec(bytes@) == Some(value@)
                &&& crate::bridge::promise_text_wf(value@)
            }
            Err(_) => decode_promise_spec(bytes@) is None,
        },
{
    let fields = match decode_record(bytes, KIND_PROMISE) {
        None => return Err("invalid Promise"),
        Some(fields) => fields,
    };
    let ghost fv = fields.deep_view();
    assert(decode_record_spec(bytes@, KIND_PROMISE) == Some(fv));
    if fields.len() != 11 {
        return Err("Promise has wrong arity");
    }
    assert forall|i: int| 0 <= i < 11
        implies fields[i]@ == fv[i] by {
    }
    let id = match parse_text(&fields[0]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let state = match parse_promise_state(&fields[1]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let tags = match parse_pairs(&fields[2]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let param = match decode_value(&fields[3]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let result_value = match decode_value(&fields[4]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let timeout_at = match parse_u64(&fields[5]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let created_at = match parse_u64(&fields[6]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let settled_at = match parse_option_u64(&fields[7]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let callbacks = match parse_text_list(&fields[8]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let listeners = match parse_text_list(&fields[9]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let task = match parse_option_task(&fields[10]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let value = model::Promise {
        id,
        state,
        tags,
        param,
        value: result_value,
        timeout_at,
        created_at,
        settled_at,
        callbacks,
        listeners,
        task,
    };
    assert(decode_promise_spec(bytes@) == Some(value@));
    assert(crate::bridge::promise_text_wf(value@));
    Ok(value)
}

pub fn encode_schedule_model(
    value: &model::Schedule,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == schedule_bytes(value@),
        result is Ok && schedule_wf(value@)
            ==> decode_schedule_spec(result->Ok_0@) == Some(value@),
{
    let mut fields = Vec::new();
    push_bytes(&mut fields, text_field(&value.id));
    push_bytes(&mut fields, text_field(&value.cron));
    push_bytes(&mut fields, text_field(&value.promise_id));
    push_bytes(&mut fields, u64_field(value.promise_timeout));
    push_bytes(&mut fields, encode_value(&value.promise_param)?);
    push_bytes(&mut fields, pairs_field(&value.promise_tags)?);
    push_bytes(&mut fields, u64_field(value.next_run_at));
    push_bytes(&mut fields, option_u64_field(value.last_run_at)?);
    push_bytes(&mut fields, u64_field(value.created_at));
    assert(fields.deep_view() =~= schedule_fields(value@));
    let result = required(encode_record(KIND_SCHEDULE, &fields));
    proof {
        if result is Ok && schedule_wf(value@) {
            lemma_schedule_round_trip(value@);
        }
    }
    result
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(60)]
pub fn decode_schedule_model(
    bytes: &Vec<u8>,
) -> (result: CodecResult<model::Schedule>)
    ensures
        match result {
            Ok(value) => {
                &&& decode_schedule_spec(bytes@) == Some(value@)
                &&& crate::bridge::schedule_text_wf(value@)
            }
            Err(_) => decode_schedule_spec(bytes@) is None,
        },
{
    let fields = match decode_record(bytes, KIND_SCHEDULE) {
        None => return Err("invalid Schedule"),
        Some(fields) => fields,
    };
    let ghost fv = fields.deep_view();
    assert(decode_record_spec(bytes@, KIND_SCHEDULE) == Some(fv));
    if fields.len() != 9 {
        return Err("Schedule has wrong arity");
    }
    assert forall|i: int| 0 <= i < 9
        implies fields[i]@ == fv[i] by {
    }
    let id = match parse_text(&fields[0]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let cron = match parse_text(&fields[1]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let promise_id = match parse_text(&fields[2]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let promise_timeout = match parse_u64(&fields[3]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let promise_param = match decode_value(&fields[4]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let promise_tags = match parse_pairs(&fields[5]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let next_run_at = match parse_u64(&fields[6]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let last_run_at = match parse_option_u64(&fields[7]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let created_at = match parse_u64(&fields[8]) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let value = model::Schedule {
        id,
        cron,
        promise_id,
        promise_timeout,
        promise_param,
        promise_tags,
        next_run_at,
        last_run_at,
        created_at,
    };
    assert(decode_schedule_spec(bytes@) == Some(value@));
    assert(crate::bridge::schedule_text_wf(value@));
    Ok(value)
}

pub fn encode_store_key(
    value: &model::StoreKey,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == store_key_bytes(value@),
        result is Ok && store_key_wf(value@)
            ==> decode_store_key_spec(result->Ok_0@) == Some(value@),
{
    let mut fields = Vec::new();
    match value {
        model::StoreKey::Document(id) => {
            push_bytes(&mut fields, tag_field(0));
            push_bytes(&mut fields, text_field(id));
        }
        model::StoreKey::Schedule(id) => {
            push_bytes(&mut fields, tag_field(1));
            push_bytes(&mut fields, text_field(id));
        }
        model::StoreKey::TimerOrigin {
            bucket,
            deadline,
            origin,
            token,
            by,
        } => {
            push_bytes(&mut fields, tag_field(2));
            push_bytes(&mut fields, u64_field(*bucket));
            push_bytes(&mut fields, u64_field(*deadline));
            push_bytes(&mut fields, text_field(origin));
            push_bytes(&mut fields, u64_field(*token));
            push_bytes(&mut fields, text_field(by));
        }
        model::StoreKey::TimerSchedule {
            bucket,
            deadline,
            id,
            token,
            by,
        } => {
            push_bytes(&mut fields, tag_field(3));
            push_bytes(&mut fields, u64_field(*bucket));
            push_bytes(&mut fields, u64_field(*deadline));
            push_bytes(&mut fields, text_field(id));
            push_bytes(&mut fields, u64_field(*token));
            push_bytes(&mut fields, text_field(by));
        }
        model::StoreKey::Node(id) => {
            push_bytes(&mut fields, tag_field(4));
            push_bytes(&mut fields, text_field(id));
        }
        model::StoreKey::Membership => {
            push_bytes(&mut fields, tag_field(5));
        }
    }
    assert(fields.deep_view() =~= store_key_fields(value@));
    let result = required(encode_record(KIND_STORE_KEY, &fields));
    proof {
        if result is Ok && store_key_wf(value@) {
            lemma_store_key_round_trip(value@);
        }
    }
    result
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(60)]
pub fn decode_store_key(
    bytes: &Vec<u8>,
) -> (result: CodecResult<model::StoreKey>)
    ensures
        match result {
            Ok(value) => decode_store_key_spec(bytes@) == Some(value@),
            Err(_) => decode_store_key_spec(bytes@) is None,
        },
{
    let fields = match decode_record(bytes, KIND_STORE_KEY) {
        None => return Err("invalid StoreKey"),
        Some(fields) => fields,
    };
    let ghost fv = fields.deep_view();
    assert(decode_record_spec(bytes@, KIND_STORE_KEY) == Some(fv));
    assert forall|i: int| 0 <= i < fields.len()
        implies fields[i]@ == fv[i] by {
    }
    if fields.len() == 2 && fields[0].len() == 1 && fields[0][0] == 0 {
        assert(fv[0] =~= seq![0u8]);
        let id = match parse_text(&fields[1]) {
            Err(error) => {
                assert(decode_store_key_spec(bytes@) is None);
                return Err(error);
            }
            Ok(value) => value,
        };
        let value = model::StoreKey::Document(id);
        assert(decode_store_key_spec(bytes@) == Some(value@));
        Ok(value)
    } else if fields.len() == 2 && fields[0].len() == 1 && fields[0][0] == 1 {
        assert(fv[0] =~= seq![1u8]);
        let id = match parse_text(&fields[1]) {
            Err(error) => {
                assert(decode_store_key_spec(bytes@) is None);
                return Err(error);
            }
            Ok(value) => value,
        };
        let value = model::StoreKey::Schedule(id);
        assert(decode_store_key_spec(bytes@) == Some(value@));
        Ok(value)
    } else if fields.len() == 6 && fields[0].len() == 1 && fields[0][0] == 2 {
        assert(fv[0] =~= seq![2u8]);
        let bucket = match parse_u64(&fields[1]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let deadline = match parse_u64(&fields[2]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let origin = match parse_text(&fields[3]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let token = match parse_u64(&fields[4]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let by = match parse_text(&fields[5]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let value = model::StoreKey::TimerOrigin {
            bucket, deadline, origin, token, by,
        };
        assert(decode_store_key_spec(bytes@) == Some(value@));
        Ok(value)
    } else if fields.len() == 6 && fields[0].len() == 1 && fields[0][0] == 3 {
        assert(fv[0] =~= seq![3u8]);
        let bucket = match parse_u64(&fields[1]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let deadline = match parse_u64(&fields[2]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let id = match parse_text(&fields[3]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let token = match parse_u64(&fields[4]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let by = match parse_text(&fields[5]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let value = model::StoreKey::TimerSchedule {
            bucket, deadline, id, token, by,
        };
        assert(decode_store_key_spec(bytes@) == Some(value@));
        Ok(value)
    } else if fields.len() == 2 && fields[0].len() == 1 && fields[0][0] == 4 {
        assert(fv[0] =~= seq![4u8]);
        let id = match parse_text(&fields[1]) {
            Err(error) => return Err(error),
            Ok(value) => value,
        };
        let value = model::StoreKey::Node(id);
        assert(decode_store_key_spec(bytes@) == Some(value@));
        Ok(value)
    } else if fields.len() == 1 && fields[0].len() == 1 && fields[0][0] == 5 {
        assert(fv[0] =~= seq![5u8]);
        let value = model::StoreKey::Membership;
        assert(decode_store_key_spec(bytes@) == Some(value@));
        Ok(value)
    } else {
        assert(decode_store_key_spec(bytes@) is None);
        Err("invalid StoreKey variant")
    }
}

pub fn encode_promise(
    value: &echod_kernel::Promise,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@
            == promise_bytes(crate::bridge::promise_from_kernel(value@)),
        result is Ok
            && promise_wf(crate::bridge::promise_from_kernel(value@))
            ==> decode_promise_spec(result->Ok_0@)
                == Some(crate::bridge::promise_from_kernel(value@)),
{
    let model = crate::bridge::promise_model(value);
    encode_promise_model(&model)
}

pub fn decode_promise(
    bytes: &Vec<u8>,
) -> (result: CodecResult<echod_kernel::Promise>)
    ensures
        match result {
            Ok(value) => decode_promise_spec(bytes@)
                == Some(crate::bridge::promise_from_kernel(value@)),
            Err(_) => decode_promise_spec(bytes@) is None,
        },
{
    let value = match decode_promise_model(bytes) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let ghost model_view = value@;
    let result = crate::bridge::kernel_promise(value);
    proof {
        crate::bridge::lemma_promise_model_round_trip(model_view);
    }
    assert(result@ == crate::bridge::promise_to_kernel(model_view));
    assert(crate::bridge::promise_from_kernel(result@) == model_view);
    Ok(result)
}

pub fn encode_schedule(
    value: &echod_kernel::Schedule,
) -> (result: CodecResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@
            == schedule_bytes(crate::bridge::schedule_from_kernel(value@)),
        result is Ok
            && schedule_wf(crate::bridge::schedule_from_kernel(value@))
            ==> decode_schedule_spec(result->Ok_0@)
                == Some(crate::bridge::schedule_from_kernel(value@)),
{
    let model = crate::bridge::schedule_model(value);
    encode_schedule_model(&model)
}

pub fn decode_schedule(
    bytes: &Vec<u8>,
) -> (result: CodecResult<echod_kernel::Schedule>)
    ensures
        match result {
            Ok(value) => decode_schedule_spec(bytes@)
                == Some(crate::bridge::schedule_from_kernel(value@)),
            Err(_) => decode_schedule_spec(bytes@) is None,
        },
{
    let value = match decode_schedule_model(bytes) {
        Err(error) => return Err(error),
        Ok(value) => value,
    };
    let ghost model_view = value@;
    let result = crate::bridge::kernel_schedule(value);
    proof {
        crate::bridge::lemma_schedule_model_round_trip(model_view);
    }
    assert(result@ == crate::bridge::schedule_to_kernel(model_view));
    assert(crate::bridge::schedule_from_kernel(result@) == model_view);
    Ok(result)
}

} // verus!
