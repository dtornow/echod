//! Verified correspondence between kernel `String` rows and UTF-8 codec models.

use vstd::prelude::*;

use crate::text::Text;
#[cfg(verus_keep_ghost)]
use crate::text::{lemma_valid_utf8_equiv, valid_utf8};
use crate::types as model;

verus! {

pub open spec fn strings_to_utf8(values: Seq<Seq<char>>) -> Seq<Seq<u8>> {
    values.map_values(|value: Seq<char>| vstd::utf8::encode_utf8(value))
}

pub open spec fn string_pairs_to_utf8(
    values: Seq<(Seq<char>, Seq<char>)>,
) -> Seq<(Seq<u8>, Seq<u8>)> {
    values.map_values(|pair: (Seq<char>, Seq<char>)| (
        vstd::utf8::encode_utf8(pair.0),
        vstd::utf8::encode_utf8(pair.1),
    ))
}

pub open spec fn utf8_to_strings(values: Seq<Seq<u8>>) -> Seq<Seq<char>> {
    values.map_values(|value: Seq<u8>| vstd::utf8::decode_utf8(value))
}

pub open spec fn utf8_pairs_to_strings(
    values: Seq<(Seq<u8>, Seq<u8>)>,
) -> Seq<(Seq<char>, Seq<char>)> {
    values.map_values(|pair: (Seq<u8>, Seq<u8>)| (
        vstd::utf8::decode_utf8(pair.0),
        vstd::utf8::decode_utf8(pair.1),
    ))
}

pub open spec fn option_string_to_utf8(
    value: Option<Seq<char>>,
) -> Option<Seq<u8>> {
    match value {
        None => None,
        Some(value) => Some(vstd::utf8::encode_utf8(value)),
    }
}

pub open spec fn option_utf8_to_string(
    value: Option<Seq<u8>>,
) -> Option<Seq<char>> {
    match value {
        None => None,
        Some(value) => Some(vstd::utf8::decode_utf8(value)),
    }
}

proof fn lemma_strings_to_utf8_push(
    values: Seq<Seq<char>>,
    value: Seq<char>,
)
    ensures
        strings_to_utf8(values.push(value))
            == strings_to_utf8(values).push(vstd::utf8::encode_utf8(value)),
{
}

proof fn lemma_string_pairs_to_utf8_push(
    values: Seq<(Seq<char>, Seq<char>)>,
    value: (Seq<char>, Seq<char>),
)
    ensures
        string_pairs_to_utf8(values.push(value))
            == string_pairs_to_utf8(values).push((
                vstd::utf8::encode_utf8(value.0),
                vstd::utf8::encode_utf8(value.1),
            )),
{
}

proof fn lemma_utf8_to_strings_push(
    values: Seq<Seq<u8>>,
    value: Seq<u8>,
)
    ensures
        utf8_to_strings(values.push(value))
            == utf8_to_strings(values).push(vstd::utf8::decode_utf8(value)),
{
}

proof fn lemma_utf8_pairs_to_strings_push(
    values: Seq<(Seq<u8>, Seq<u8>)>,
    value: (Seq<u8>, Seq<u8>),
)
    ensures
        utf8_pairs_to_strings(values.push(value))
            == utf8_pairs_to_strings(values).push((
                vstd::utf8::decode_utf8(value.0),
                vstd::utf8::decode_utf8(value.1),
            )),
{
}

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

proof fn lemma_strings_to_utf8_valid(values: Seq<Seq<char>>)
    ensures
        forall|i: int| 0 <= i < strings_to_utf8(values).len()
            ==> valid_utf8(#[trigger] strings_to_utf8(values)[i]),
{
    assert forall|i: int| 0 <= i < strings_to_utf8(values).len()
        implies valid_utf8(#[trigger] strings_to_utf8(values)[i]) by {
        assert(strings_to_utf8(values)[i]
            == vstd::utf8::encode_utf8(values[i]));
        vstd::utf8::encode_utf8_valid_utf8(values[i]);
        lemma_valid_utf8_equiv(vstd::utf8::encode_utf8(values[i]));
    }
}

proof fn lemma_string_pairs_to_utf8_valid(
    values: Seq<(Seq<char>, Seq<char>)>,
)
    ensures
        forall|i: int| 0 <= i < string_pairs_to_utf8(values).len()
            ==> valid_utf8(#[trigger] string_pairs_to_utf8(values)[i].0),
        forall|i: int| 0 <= i < string_pairs_to_utf8(values).len()
            ==> valid_utf8(#[trigger] string_pairs_to_utf8(values)[i].1),
{
    assert forall|i: int| 0 <= i < string_pairs_to_utf8(values).len()
        implies valid_utf8(#[trigger] string_pairs_to_utf8(values)[i].0) by {
        assert(string_pairs_to_utf8(values)[i].0
            == vstd::utf8::encode_utf8(values[i].0));
        vstd::utf8::encode_utf8_valid_utf8(values[i].0);
        lemma_valid_utf8_equiv(vstd::utf8::encode_utf8(values[i].0));
    }
    assert forall|i: int| 0 <= i < string_pairs_to_utf8(values).len()
        implies valid_utf8(#[trigger] string_pairs_to_utf8(values)[i].1) by {
        assert(string_pairs_to_utf8(values)[i].1
            == vstd::utf8::encode_utf8(values[i].1));
        vstd::utf8::encode_utf8_valid_utf8(values[i].1);
        lemma_valid_utf8_equiv(vstd::utf8::encode_utf8(values[i].1));
    }
}

proof fn lemma_strings_kernel_round_trip(values: Seq<Seq<char>>)
    ensures utf8_to_strings(strings_to_utf8(values)) == values,
{
    assert(utf8_to_strings(strings_to_utf8(values)) =~= values) by {
        assert forall|i: int| 0 <= i < values.len()
            implies utf8_to_strings(strings_to_utf8(values))[i]
                == values[i] by {
            assert(utf8_to_strings(strings_to_utf8(values))[i]
                == vstd::utf8::decode_utf8(
                    vstd::utf8::encode_utf8(values[i]),
                ));
            vstd::utf8::encode_utf8_decode_utf8(values[i]);
        }
    }
}

proof fn lemma_strings_model_round_trip(values: Seq<Seq<u8>>)
    requires
        forall|i: int| 0 <= i < values.len()
            ==> valid_utf8(#[trigger] values[i]),
    ensures strings_to_utf8(utf8_to_strings(values)) == values,
{
    assert(strings_to_utf8(utf8_to_strings(values)) =~= values) by {
        assert forall|i: int| 0 <= i < values.len()
            implies strings_to_utf8(utf8_to_strings(values))[i]
                == values[i] by {
            assert(strings_to_utf8(utf8_to_strings(values))[i]
                == vstd::utf8::encode_utf8(
                    vstd::utf8::decode_utf8(values[i]),
                ));
            lemma_valid_utf8_equiv(values[i]);
            vstd::utf8::decode_utf8_encode_utf8(values[i]);
        }
    }
}

proof fn lemma_pairs_kernel_round_trip(
    values: Seq<(Seq<char>, Seq<char>)>,
)
    ensures
        utf8_pairs_to_strings(string_pairs_to_utf8(values)) == values,
{
    assert(utf8_pairs_to_strings(string_pairs_to_utf8(values)) =~= values) by {
        assert forall|i: int| 0 <= i < values.len()
            implies utf8_pairs_to_strings(string_pairs_to_utf8(values))[i]
                == values[i] by {
            vstd::utf8::encode_utf8_decode_utf8(values[i].0);
            vstd::utf8::encode_utf8_decode_utf8(values[i].1);
        }
    }
}

proof fn lemma_pairs_model_round_trip(
    values: Seq<(Seq<u8>, Seq<u8>)>,
)
    requires
        forall|i: int| 0 <= i < values.len() ==> {
            &&& valid_utf8(#[trigger] values[i].0)
            &&& valid_utf8(values[i].1)
        },
    ensures
        string_pairs_to_utf8(utf8_pairs_to_strings(values)) == values,
{
    assert(string_pairs_to_utf8(utf8_pairs_to_strings(values)) =~= values) by {
        assert forall|i: int| 0 <= i < values.len()
            implies string_pairs_to_utf8(utf8_pairs_to_strings(values))[i]
                == values[i] by {
            lemma_valid_utf8_equiv(values[i].0);
            lemma_valid_utf8_equiv(values[i].1);
            vstd::utf8::decode_utf8_encode_utf8(values[i].0);
            vstd::utf8::decode_utf8_encode_utf8(values[i].1);
        }
    }
}

proof fn lemma_option_kernel_round_trip(value: Option<Seq<char>>)
    ensures
        option_utf8_to_string(option_string_to_utf8(value)) == value,
{
    match value {
        None => {}
        Some(value) => {
            vstd::utf8::encode_utf8_decode_utf8(value);
        }
    }
}

proof fn lemma_option_model_round_trip(value: Option<Seq<u8>>)
    requires
        value is Some ==> valid_utf8(value->Some_0),
    ensures
        option_string_to_utf8(option_utf8_to_string(value)) == value,
{
    match value {
        None => {}
        Some(value) => {
            lemma_valid_utf8_equiv(value);
            vstd::utf8::decode_utf8_encode_utf8(value);
        }
    }
}

pub fn string_to_text(value: &String) -> (text: Text)
    ensures
        text@ == vstd::utf8::encode_utf8(value@),
        text.wf(),
{
    Text::from_string(value)
}

pub fn text_to_string(value: Text) -> (string: String)
    requires value.wf(),
    ensures string@ == vstd::utf8::decode_utf8(value@),
{
    value.into_string()
}

fn strings_to_text(values: &Vec<String>) -> (texts: Vec<Text>)
    ensures
        texts.deep_view() == strings_to_utf8(values.deep_view()),
        forall|i: int| 0 <= i < texts.len()
            ==> valid_utf8(#[trigger] texts[i]@),
{
    let mut texts: Vec<Text> = Vec::new();
    let mut i = 0usize;
    while i < values.len()
        invariant
            i <= values.len(),
            texts.deep_view()
                == strings_to_utf8(values.deep_view().subrange(0, i as int)),
            forall|j: int| 0 <= j < texts.len()
                ==> valid_utf8(#[trigger] texts[j]@),
        decreases values.len() - i,
    {
        let ghost prefix = values.deep_view().subrange(0, i as int);
        let ghost item = values.deep_view()[i as int];
        texts.push(string_to_text(&values[i]));
        assert(values.deep_view().subrange(0, (i + 1) as int)
            == prefix.push(item));
        proof {
            lemma_strings_to_utf8_push(prefix, item);
        }
        i += 1;
    }
    assert(values.deep_view().subrange(0, values.len() as int)
        == values.deep_view());
    texts
}

fn string_pairs_to_text(
    values: &Vec<(String, String)>,
) -> (texts: Vec<(Text, Text)>)
    ensures texts.deep_view() == string_pairs_to_utf8(values.deep_view()),
{
    let mut texts: Vec<(Text, Text)> = Vec::new();
    let mut i = 0usize;
    while i < values.len()
        invariant
            i <= values.len(),
            texts.deep_view()
                == string_pairs_to_utf8(
                    values.deep_view().subrange(0, i as int),
                ),
        decreases values.len() - i,
    {
        let ghost prefix = values.deep_view().subrange(0, i as int);
        let ghost item = values.deep_view()[i as int];
        let left = string_to_text(&values[i].0);
        let right = string_to_text(&values[i].1);
        assert(left.wf());
        assert(right.wf());
        texts.push((left, right));
        assert(values.deep_view().subrange(0, (i + 1) as int)
            == prefix.push(item));
        proof {
            lemma_string_pairs_to_utf8_push(prefix, item);
        }
        i += 1;
    }
    assert(values.deep_view().subrange(0, values.len() as int)
        == values.deep_view());
    texts
}

fn option_string_to_text(value: &Option<String>) -> (text: Option<Text>)
    ensures
        text.deep_view() == option_string_to_utf8(value.deep_view()),
        text is Some ==> valid_utf8(text->Some_0@),
{
    match value {
        None => None,
        Some(value) => Some(string_to_text(value)),
    }
}

pub fn texts_to_strings(values: Vec<Text>) -> (strings: Vec<String>)
    requires
        forall|i: int| 0 <= i < values.len()
            ==> valid_utf8(#[trigger] values[i]@),
    ensures strings.deep_view() == utf8_to_strings(values.deep_view()),
{
    let ghost original = values.deep_view();
    let mut values = values;
    let mut strings = Vec::new();
    while values.len() > 0
        invariant
            values.len() + strings.len() == original.len(),
            strings.deep_view()
                == utf8_to_strings(
                    original.subrange(0, strings.len() as int),
                ),
            values.deep_view()
                == original.subrange(strings.len() as int, original.len() as int),
            forall|i: int| 0 <= i < values.len()
                ==> valid_utf8(#[trigger] values[i]@),
        decreases values.len(),
    {
        let ghost done = strings.deep_view();
        let ghost remaining = values.deep_view();
        let n = strings.len();
        proof {
            assert(n < original.len());
            lemma_subrange_step(original, n as int);
        }
        let first = values.remove(0);
        strings.push(text_to_string(first));
        assert(remaining[0] == original[n as int]);
        assert(values.deep_view() == remaining.drop_first());
        assert(original.subrange(0, (n + 1) as int)
            == original.subrange(0, n as int).push(original[n as int]));
        assert(original.subrange((n + 1) as int, original.len() as int)
            == remaining.drop_first());
        proof {
            lemma_utf8_to_strings_push(
                original.subrange(0, n as int),
                original[n as int],
            );
        }
    }
    assert(strings.len() == original.len());
    assert(original.subrange(0, original.len() as int) == original);
    strings
}

fn text_pairs_to_strings(
    values: Vec<(Text, Text)>,
) -> (strings: Vec<(String, String)>)
    requires
        forall|i: int| 0 <= i < values.len() ==> {
            &&& valid_utf8(#[trigger] values[i].0@)
            &&& valid_utf8(values[i].1@)
        },
    ensures strings.deep_view() == utf8_pairs_to_strings(values.deep_view()),
{
    let ghost original = values.deep_view();
    assert forall|i: int| 0 <= i < values.len()
        implies valid_utf8(#[trigger] values.deep_view()[i].0)
            && valid_utf8(values.deep_view()[i].1) by {
        assert(values.deep_view()[i].0 == values[i].0@);
        assert(values.deep_view()[i].1 == values[i].1@);
    }
    let mut values = values;
    let mut strings = Vec::new();
    while values.len() > 0
        invariant
            values.len() + strings.len() == original.len(),
            strings.deep_view()
                == utf8_pairs_to_strings(
                    original.subrange(0, strings.len() as int),
                ),
            values.deep_view()
                == original.subrange(strings.len() as int, original.len() as int),
            forall|i: int| 0 <= i < values.len() ==> {
                &&& valid_utf8(#[trigger] values[i].0@)
                &&& valid_utf8(values[i].1@)
            },
        decreases values.len(),
    {
        let ghost done = strings.deep_view();
        let ghost remaining = values.deep_view();
        let n = strings.len();
        proof {
            assert(n < original.len());
            lemma_subrange_step(original, n as int);
        }
        let first = values.remove(0);
        strings.push((
            text_to_string(first.0),
            text_to_string(first.1),
        ));
        assert(remaining[0] == original[n as int]);
        assert(values.deep_view() == remaining.drop_first());
        assert(original.subrange(0, (n + 1) as int)
            == original.subrange(0, n as int).push(original[n as int]));
        assert(original.subrange((n + 1) as int, original.len() as int)
            == remaining.drop_first());
        assert forall|i: int| 0 <= i < values.len()
            implies valid_utf8(#[trigger] values[i].0@)
                && valid_utf8(values[i].1@) by {
            assert(values.deep_view()[i] == remaining[i + 1]);
            assert(values[i].0@ == values.deep_view()[i].0);
            assert(values[i].1@ == values.deep_view()[i].1);
        }
        proof {
            lemma_utf8_pairs_to_strings_push(
                original.subrange(0, n as int),
                original[n as int],
            );
        }
    }
    assert(strings.len() == original.len());
    assert(original.subrange(0, original.len() as int) == original);
    strings
}

fn option_text_to_string(value: Option<Text>) -> (string: Option<String>)
    requires
        value is Some ==> valid_utf8(value->Some_0@),
    ensures string.deep_view() == option_utf8_to_string(value.deep_view()),
{
    match value {
        None => None,
        Some(value) => Some(text_to_string(value)),
    }
}

pub open spec fn value_from_kernel(
    value: echod_kernel::AValue,
) -> model::AValue {
    model::AValue {
        headers: string_pairs_to_utf8(value.headers),
        data: option_string_to_utf8(value.data),
    }
}

pub open spec fn value_to_kernel(
    value: model::AValue,
) -> echod_kernel::AValue {
    echod_kernel::AValue {
        headers: utf8_pairs_to_strings(value.headers),
        data: option_utf8_to_string(value.data),
    }
}

pub open spec fn value_text_wf(value: model::AValue) -> bool {
    &&& forall|i: int| 0 <= i < value.headers.len() ==> {
        &&& valid_utf8(#[trigger] value.headers[i].0)
        &&& valid_utf8(value.headers[i].1)
    }
    &&& value.data is Some ==> valid_utf8(value.data->Some_0)
}

pub proof fn lemma_value_kernel_round_trip(value: echod_kernel::AValue)
    ensures value_to_kernel(value_from_kernel(value)) == value,
{
    lemma_pairs_kernel_round_trip(value.headers);
    lemma_option_kernel_round_trip(value.data);
}

pub proof fn lemma_value_model_round_trip(value: model::AValue)
    requires value_text_wf(value),
    ensures value_from_kernel(value_to_kernel(value)) == value,
{
    lemma_pairs_model_round_trip(value.headers);
    lemma_option_model_round_trip(value.data);
}

fn model_value(value: &echod_kernel::Value) -> (result: model::Value)
    ensures
        result@ == value_from_kernel(value@),
        value_text_wf(result@),
{
    let headers = string_pairs_to_text(&value.headers);
    let data = option_string_to_text(&value.data);
    proof {
        lemma_string_pairs_to_utf8_valid(value.headers.deep_view());
    }
    assert forall|i: int| 0 <= i < headers.deep_view().len()
        implies valid_utf8(#[trigger] headers.deep_view()[i].0)
            && valid_utf8(headers.deep_view()[i].1) by {
        assert(headers.deep_view()[i].0 == headers[i].0@);
        assert(headers.deep_view()[i].1 == headers[i].1@);
    }
    assert(data.deep_view() is Some
        ==> valid_utf8(data.deep_view()->Some_0));
    model::Value { headers, data }
}

fn kernel_value(value: model::Value) -> (result: echod_kernel::Value)
    requires value_text_wf(value@),
    ensures result@ == value_to_kernel(value@),
{
    assert forall|i: int| 0 <= i < value.headers.len()
        implies valid_utf8(#[trigger] value.headers[i].0@)
            && valid_utf8(value.headers[i].1@) by {
        assert(value.headers.deep_view()[i].0 == value.headers[i].0@);
        assert(value.headers.deep_view()[i].1 == value.headers[i].1@);
    }
    echod_kernel::Value {
        headers: text_pairs_to_strings(value.headers),
        data: option_text_to_string(value.data),
    }
}

pub open spec fn task_from_kernel(
    value: echod_kernel::ATask,
) -> model::ATask {
    model::ATask {
        state: value.state,
        version: value.version,
        ttl: value.ttl,
        pid: option_string_to_utf8(value.pid),
        lease_timeout_at: value.lease_timeout_at,
        retry_timeout_at: value.retry_timeout_at,
        resumes: strings_to_utf8(value.resumes),
    }
}

pub open spec fn task_to_kernel(
    value: model::ATask,
) -> echod_kernel::ATask {
    echod_kernel::ATask {
        state: value.state,
        version: value.version,
        ttl: value.ttl,
        pid: option_utf8_to_string(value.pid),
        lease_timeout_at: value.lease_timeout_at,
        retry_timeout_at: value.retry_timeout_at,
        resumes: utf8_to_strings(value.resumes),
    }
}

pub open spec fn task_text_wf(value: model::ATask) -> bool {
    &&& value.pid is Some ==> valid_utf8(value.pid->Some_0)
    &&& forall|i: int| 0 <= i < value.resumes.len()
        ==> valid_utf8(#[trigger] value.resumes[i])
}

pub proof fn lemma_task_kernel_round_trip(value: echod_kernel::ATask)
    ensures task_to_kernel(task_from_kernel(value)) == value,
{
    lemma_option_kernel_round_trip(value.pid);
    lemma_strings_kernel_round_trip(value.resumes);
}

pub proof fn lemma_task_model_round_trip(value: model::ATask)
    requires task_text_wf(value),
    ensures task_from_kernel(task_to_kernel(value)) == value,
{
    lemma_option_model_round_trip(value.pid);
    lemma_strings_model_round_trip(value.resumes);
}

fn model_task(value: &echod_kernel::Task) -> (result: model::Task)
    ensures
        result@ == task_from_kernel(value@),
        task_text_wf(result@),
{
    let pid = option_string_to_text(&value.pid);
    let resumes = strings_to_text(&value.resumes);
    proof {
        lemma_strings_to_utf8_valid(value.resumes.deep_view());
    }
    assert forall|i: int| 0 <= i < resumes.deep_view().len()
        implies valid_utf8(#[trigger] resumes.deep_view()[i]) by {
        assert(resumes.deep_view()[i] == resumes[i]@);
    }
    model::Task {
        state: value.state,
        version: value.version,
        ttl: value.ttl,
        pid,
        lease_timeout_at: value.lease_timeout_at,
        retry_timeout_at: value.retry_timeout_at,
        resumes,
    }
}

fn kernel_task(value: model::Task) -> (result: echod_kernel::Task)
    requires task_text_wf(value@),
    ensures result@ == task_to_kernel(value@),
{
    assert forall|i: int| 0 <= i < value.resumes.len()
        implies valid_utf8(#[trigger] value.resumes[i]@) by {
        assert(value.resumes.deep_view()[i] == value.resumes[i]@);
    }
    echod_kernel::Task {
        state: value.state,
        version: value.version,
        ttl: value.ttl,
        pid: option_text_to_string(value.pid),
        lease_timeout_at: value.lease_timeout_at,
        retry_timeout_at: value.retry_timeout_at,
        resumes: texts_to_strings(value.resumes),
    }
}

pub open spec fn option_task_from_kernel(
    value: Option<echod_kernel::ATask>,
) -> Option<model::ATask> {
    match value {
        None => None,
        Some(value) => Some(task_from_kernel(value)),
    }
}

pub open spec fn option_task_to_kernel(
    value: Option<model::ATask>,
) -> Option<echod_kernel::ATask> {
    match value {
        None => None,
        Some(value) => Some(task_to_kernel(value)),
    }
}

proof fn lemma_option_task_kernel_round_trip(
    value: Option<echod_kernel::ATask>,
)
    ensures
        option_task_to_kernel(option_task_from_kernel(value)) == value,
{
    match value {
        None => {}
        Some(value) => lemma_task_kernel_round_trip(value),
    }
}

proof fn lemma_option_task_model_round_trip(
    value: Option<model::ATask>,
)
    requires
        value is Some ==> task_text_wf(value->Some_0),
    ensures
        option_task_from_kernel(option_task_to_kernel(value)) == value,
{
    match value {
        None => {}
        Some(value) => lemma_task_model_round_trip(value),
    }
}

fn model_option_task(
    value: &Option<echod_kernel::Task>,
) -> (result: Option<model::Task>)
    ensures
        result.deep_view() == option_task_from_kernel(value.deep_view()),
        result is Some ==> task_text_wf(result->Some_0@),
{
    match value {
        None => None,
        Some(value) => Some(model_task(value)),
    }
}

fn kernel_option_task(
    value: Option<model::Task>,
) -> (result: Option<echod_kernel::Task>)
    requires
        value is Some ==> task_text_wf(value->Some_0@),
    ensures result.deep_view() == option_task_to_kernel(value.deep_view()),
{
    match value {
        None => None,
        Some(value) => Some(kernel_task(value)),
    }
}

pub open spec fn promise_from_kernel(
    value: echod_kernel::APromise,
) -> model::APromise {
    model::APromise {
        id: vstd::utf8::encode_utf8(value.id),
        state: value.state,
        tags: string_pairs_to_utf8(value.tags),
        param: value_from_kernel(value.param),
        value: value_from_kernel(value.value),
        timeout_at: value.timeout_at,
        created_at: value.created_at,
        settled_at: value.settled_at,
        callbacks: strings_to_utf8(value.callbacks),
        listeners: strings_to_utf8(value.listeners),
        task: option_task_from_kernel(value.task),
    }
}

pub open spec fn promise_to_kernel(
    value: model::APromise,
) -> echod_kernel::APromise {
    echod_kernel::APromise {
        id: vstd::utf8::decode_utf8(value.id),
        state: value.state,
        tags: utf8_pairs_to_strings(value.tags),
        param: value_to_kernel(value.param),
        value: value_to_kernel(value.value),
        timeout_at: value.timeout_at,
        created_at: value.created_at,
        settled_at: value.settled_at,
        callbacks: utf8_to_strings(value.callbacks),
        listeners: utf8_to_strings(value.listeners),
        task: option_task_to_kernel(value.task),
    }
}

pub open spec fn promise_text_wf(value: model::APromise) -> bool {
    &&& valid_utf8(value.id)
    &&& forall|i: int| 0 <= i < value.tags.len() ==> {
        &&& valid_utf8(#[trigger] value.tags[i].0)
        &&& valid_utf8(value.tags[i].1)
    }
    &&& value_text_wf(value.param)
    &&& value_text_wf(value.value)
    &&& forall|i: int| 0 <= i < value.callbacks.len()
        ==> valid_utf8(#[trigger] value.callbacks[i])
    &&& forall|i: int| 0 <= i < value.listeners.len()
        ==> valid_utf8(#[trigger] value.listeners[i])
    &&& value.task is Some ==> task_text_wf(value.task->Some_0)
}

#[verifier(spinoff_prover)]
pub proof fn lemma_promise_kernel_round_trip(
    value: echod_kernel::APromise,
)
    ensures promise_to_kernel(promise_from_kernel(value)) == value,
{
    vstd::utf8::encode_utf8_decode_utf8(value.id);
    lemma_pairs_kernel_round_trip(value.tags);
    lemma_value_kernel_round_trip(value.param);
    lemma_value_kernel_round_trip(value.value);
    lemma_strings_kernel_round_trip(value.callbacks);
    lemma_strings_kernel_round_trip(value.listeners);
    lemma_option_task_kernel_round_trip(value.task);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_promise_model_round_trip(value: model::APromise)
    requires promise_text_wf(value),
    ensures promise_from_kernel(promise_to_kernel(value)) == value,
{
    lemma_valid_utf8_equiv(value.id);
    vstd::utf8::decode_utf8_encode_utf8(value.id);
    lemma_pairs_model_round_trip(value.tags);
    lemma_value_model_round_trip(value.param);
    lemma_value_model_round_trip(value.value);
    lemma_strings_model_round_trip(value.callbacks);
    lemma_strings_model_round_trip(value.listeners);
    lemma_option_task_model_round_trip(value.task);
}

pub fn promise_model(
    value: &echod_kernel::Promise,
) -> (result: model::Promise)
    ensures
        result@ == promise_from_kernel(value@),
        promise_text_wf(result@),
{
    let id = string_to_text(&value.id);
    let tags = string_pairs_to_text(&value.tags);
    let param = model_value(&value.param);
    let result_value = model_value(&value.value);
    let callbacks = strings_to_text(&value.callbacks);
    let listeners = strings_to_text(&value.listeners);
    let task = model_option_task(&value.task);
    proof {
        lemma_string_pairs_to_utf8_valid(value.tags.deep_view());
        lemma_strings_to_utf8_valid(value.callbacks.deep_view());
        lemma_strings_to_utf8_valid(value.listeners.deep_view());
    }
    assert forall|i: int| 0 <= i < tags.deep_view().len()
        implies valid_utf8(#[trigger] tags.deep_view()[i].0)
            && valid_utf8(tags.deep_view()[i].1) by {
        assert(tags.deep_view()[i].0 == tags[i].0@);
        assert(tags.deep_view()[i].1 == tags[i].1@);
    }
    assert forall|i: int| 0 <= i < callbacks.deep_view().len()
        implies valid_utf8(#[trigger] callbacks.deep_view()[i]) by {
        assert(callbacks.deep_view()[i] == callbacks[i]@);
    }
    assert forall|i: int| 0 <= i < listeners.deep_view().len()
        implies valid_utf8(#[trigger] listeners.deep_view()[i]) by {
        assert(listeners.deep_view()[i] == listeners[i]@);
    }
    model::Promise {
        id,
        state: value.state,
        tags,
        param,
        value: result_value,
        timeout_at: value.timeout_at,
        created_at: value.created_at,
        settled_at: value.settled_at,
        callbacks,
        listeners,
        task,
    }
}

pub fn kernel_promise(
    value: model::Promise,
) -> (result: echod_kernel::Promise)
    requires promise_text_wf(value@),
    ensures result@ == promise_to_kernel(value@),
{
    assert forall|i: int| 0 <= i < value.tags.len()
        implies valid_utf8(#[trigger] value.tags[i].0@)
            && valid_utf8(value.tags[i].1@) by {
        assert(value.tags.deep_view()[i].0 == value.tags[i].0@);
        assert(value.tags.deep_view()[i].1 == value.tags[i].1@);
    }
    assert forall|i: int| 0 <= i < value.callbacks.len()
        implies valid_utf8(#[trigger] value.callbacks[i]@) by {
        assert(value.callbacks.deep_view()[i] == value.callbacks[i]@);
    }
    assert forall|i: int| 0 <= i < value.listeners.len()
        implies valid_utf8(#[trigger] value.listeners[i]@) by {
        assert(value.listeners.deep_view()[i] == value.listeners[i]@);
    }
    echod_kernel::Promise {
        id: text_to_string(value.id),
        state: value.state,
        tags: text_pairs_to_strings(value.tags),
        param: kernel_value(value.param),
        value: kernel_value(value.value),
        timeout_at: value.timeout_at,
        created_at: value.created_at,
        settled_at: value.settled_at,
        callbacks: texts_to_strings(value.callbacks),
        listeners: texts_to_strings(value.listeners),
        task: kernel_option_task(value.task),
    }
}

pub fn round_trip_kernel_promise(
    value: echod_kernel::Promise,
) -> (result: echod_kernel::Promise)
    ensures result@ == value@,
{
    let model = promise_model(&value);
    let result = kernel_promise(model);
    proof {
        lemma_promise_kernel_round_trip(value@);
    }
    result
}

pub fn round_trip_model_promise(
    value: model::Promise,
) -> (result: model::Promise)
    requires promise_text_wf(value@),
    ensures result@ == value@,
{
    let ghost original = value@;
    let kernel = kernel_promise(value);
    let result = promise_model(&kernel);
    proof {
        lemma_promise_model_round_trip(original);
    }
    result
}

pub open spec fn schedule_from_kernel(
    value: echod_kernel::ASchedule,
) -> model::ASchedule {
    model::ASchedule {
        id: vstd::utf8::encode_utf8(value.id),
        cron: vstd::utf8::encode_utf8(value.cron),
        promise_id: vstd::utf8::encode_utf8(value.promise_id),
        promise_timeout: value.promise_timeout,
        promise_param: value_from_kernel(value.promise_param),
        promise_tags: string_pairs_to_utf8(value.promise_tags),
        next_run_at: value.next_run_at,
        last_run_at: value.last_run_at,
        created_at: value.created_at,
    }
}

pub open spec fn schedule_to_kernel(
    value: model::ASchedule,
) -> echod_kernel::ASchedule {
    echod_kernel::ASchedule {
        id: vstd::utf8::decode_utf8(value.id),
        cron: vstd::utf8::decode_utf8(value.cron),
        promise_id: vstd::utf8::decode_utf8(value.promise_id),
        promise_timeout: value.promise_timeout,
        promise_param: value_to_kernel(value.promise_param),
        promise_tags: utf8_pairs_to_strings(value.promise_tags),
        next_run_at: value.next_run_at,
        last_run_at: value.last_run_at,
        created_at: value.created_at,
    }
}

pub open spec fn schedule_text_wf(value: model::ASchedule) -> bool {
    &&& valid_utf8(value.id)
    &&& valid_utf8(value.cron)
    &&& valid_utf8(value.promise_id)
    &&& value_text_wf(value.promise_param)
    &&& forall|i: int| 0 <= i < value.promise_tags.len() ==> {
        &&& valid_utf8(#[trigger] value.promise_tags[i].0)
        &&& valid_utf8(value.promise_tags[i].1)
    }
}

#[verifier(spinoff_prover)]
pub proof fn lemma_schedule_kernel_round_trip(
    value: echod_kernel::ASchedule,
)
    ensures schedule_to_kernel(schedule_from_kernel(value)) == value,
{
    vstd::utf8::encode_utf8_decode_utf8(value.id);
    vstd::utf8::encode_utf8_decode_utf8(value.cron);
    vstd::utf8::encode_utf8_decode_utf8(value.promise_id);
    lemma_value_kernel_round_trip(value.promise_param);
    lemma_pairs_kernel_round_trip(value.promise_tags);
}

#[verifier(spinoff_prover)]
pub proof fn lemma_schedule_model_round_trip(value: model::ASchedule)
    requires schedule_text_wf(value),
    ensures schedule_from_kernel(schedule_to_kernel(value)) == value,
{
    lemma_valid_utf8_equiv(value.id);
    lemma_valid_utf8_equiv(value.cron);
    lemma_valid_utf8_equiv(value.promise_id);
    vstd::utf8::decode_utf8_encode_utf8(value.id);
    vstd::utf8::decode_utf8_encode_utf8(value.cron);
    vstd::utf8::decode_utf8_encode_utf8(value.promise_id);
    lemma_value_model_round_trip(value.promise_param);
    lemma_pairs_model_round_trip(value.promise_tags);
}

pub fn schedule_model(
    value: &echod_kernel::Schedule,
) -> (result: model::Schedule)
    ensures
        result@ == schedule_from_kernel(value@),
        schedule_text_wf(result@),
{
    let id = string_to_text(&value.id);
    let cron = string_to_text(&value.cron);
    let promise_id = string_to_text(&value.promise_id);
    let promise_param = model_value(&value.promise_param);
    let promise_tags = string_pairs_to_text(&value.promise_tags);
    proof {
        lemma_string_pairs_to_utf8_valid(value.promise_tags.deep_view());
    }
    assert forall|i: int| 0 <= i < promise_tags.deep_view().len()
        implies valid_utf8(#[trigger] promise_tags.deep_view()[i].0)
            && valid_utf8(promise_tags.deep_view()[i].1) by {
        assert(promise_tags.deep_view()[i].0 == promise_tags[i].0@);
        assert(promise_tags.deep_view()[i].1 == promise_tags[i].1@);
    }
    model::Schedule {
        id,
        cron,
        promise_id,
        promise_timeout: value.promise_timeout,
        promise_param,
        promise_tags,
        next_run_at: value.next_run_at,
        last_run_at: value.last_run_at,
        created_at: value.created_at,
    }
}

pub fn kernel_schedule(
    value: model::Schedule,
) -> (result: echod_kernel::Schedule)
    requires schedule_text_wf(value@),
    ensures result@ == schedule_to_kernel(value@),
{
    assert forall|i: int| 0 <= i < value.promise_tags.len()
        implies valid_utf8(#[trigger] value.promise_tags[i].0@)
            && valid_utf8(value.promise_tags[i].1@) by {
        assert(value.promise_tags.deep_view()[i].0 == value.promise_tags[i].0@);
        assert(value.promise_tags.deep_view()[i].1 == value.promise_tags[i].1@);
    }
    echod_kernel::Schedule {
        id: text_to_string(value.id),
        cron: text_to_string(value.cron),
        promise_id: text_to_string(value.promise_id),
        promise_timeout: value.promise_timeout,
        promise_param: kernel_value(value.promise_param),
        promise_tags: text_pairs_to_strings(value.promise_tags),
        next_run_at: value.next_run_at,
        last_run_at: value.last_run_at,
        created_at: value.created_at,
    }
}

pub fn round_trip_kernel_schedule(
    value: echod_kernel::Schedule,
) -> (result: echod_kernel::Schedule)
    ensures result@ == value@,
{
    let model = schedule_model(&value);
    let result = kernel_schedule(model);
    proof {
        lemma_schedule_kernel_round_trip(value@);
    }
    result
}

pub fn round_trip_model_schedule(
    value: model::Schedule,
) -> (result: model::Schedule)
    requires schedule_text_wf(value@),
    ensures result@ == value@,
{
    let ghost original = value@;
    let kernel = kernel_schedule(value);
    let result = schedule_model(&kernel);
    proof {
        lemma_schedule_model_round_trip(original);
    }
    result
}

} // verus!

#[cfg(not(verus_keep_ghost))]
pub use crate::runtime::{
    decode_announcement, decode_header, decode_membership, decode_promise, decode_promise_model,
    decode_schedule, decode_schedule_model, decode_store_key, encode_announcement, encode_header,
    encode_membership, encode_promise, encode_promise_model, encode_schedule,
    encode_schedule_model, encode_store_key, CodecResult,
};
