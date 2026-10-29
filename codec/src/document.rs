//! Appendable Promise and Schedule documents.
//!
//! A write is one self-framed segment. A stored document is the byte
//! concatenation of its segments, so appending never rewrites an outer length.

use vstd::prelude::*;

use crate::laws::*;
use crate::primitives::*;
#[cfg(verus_keep_ghost)]
use crate::record::decode_record_spec;
use crate::record::{decode_record, encode_record};
use crate::types as model;

verus! {

pub const KIND_PROMISE_SEGMENT: u8 = 7;
pub const KIND_SCHEDULE_SEGMENT: u8 = 8;

pub type DocumentResult<T> = Result<T, &'static str>;

// -------------------------------------------------------------------------
// Frame splitting
// -------------------------------------------------------------------------

/// Split the first complete versioned envelope from a byte stream.
///
/// This validates magic, version, the payload length, and truncation. The
/// segment decoder subsequently validates the kind and payload.
pub open spec fn split_frame_spec(
    bytes: Seq<u8>,
) -> Option<(Seq<u8>, Seq<u8>)> {
    if bytes.len() < 14
        || bytes[0] != 0x45
        || bytes[1] != 0x43
        || bytes[2] != 0x48
        || bytes[3] != 0x4f
        || bytes[4] != crate::frame::FORMAT_VERSION {
        None
    } else {
        match decode_u64_spec(bytes.subrange(6, 14)) {
            Some(n) if n <= usize::MAX && 14 + n <= bytes.len() => {
                let end = 14 + n;
                Some((
                    bytes.subrange(0, end as int),
                    bytes.subrange(end as int, bytes.len() as int),
                ))
            }
            _ => None,
        }
    }
}

pub fn split_frame(
    bytes: &Vec<u8>,
) -> (result: Option<(Vec<u8>, Vec<u8>)>)
    ensures
        match result {
            Some((frame, rest)) => {
                &&& split_frame_spec(bytes@) == Some((frame@, rest@))
                &&& frame@ + rest@ == bytes@
                &&& frame.len() >= 14
                &&& rest.len() < bytes.len()
            }
            None => split_frame_spec(bytes@) is None,
        },
{
    if bytes.len() < 14
        || bytes[0] != 0x45
        || bytes[1] != 0x43
        || bytes[2] != 0x48
        || bytes[3] != 0x4f
        || bytes[4] != crate::frame::FORMAT_VERSION {
        return None;
    }
    let prefix = copy_range(bytes, 6, 14);
    let n = match decode_u64(&prefix) {
        None => return None,
        Some(n) => n,
    };
    if n > usize::MAX as u64 {
        return None;
    }
    let payload_len = n as usize;
    if payload_len > bytes.len() - 14 {
        return None;
    }
    let end = 14 + payload_len;
    proof {
        assert(payload_len as int == n as int);
    }
    let frame = copy_range(bytes, 0, end);
    let rest = copy_range(bytes, end, bytes.len());
    assert(frame@ + rest@ == bytes@);
    Some((frame, rest))
}

pub proof fn lemma_split_envelope(
    kind: u8,
    payload: Seq<u8>,
    rest: Seq<u8>,
)
    requires
        payload.len() <= u64::MAX,
        payload.len() <= usize::MAX,
    ensures
        split_frame_spec(
            crate::frame::envelope_bytes(kind, payload) + rest,
        ) == Some((crate::frame::envelope_bytes(kind, payload), rest)),
{
    lemma_u64_round_trip(payload.len() as u64);
    let frame = crate::frame::envelope_bytes(kind, payload);
    assert(frame.subrange(6, 14)
        == u64_bytes(payload.len() as u64));
    assert((frame + rest).subrange(0, frame.len() as int) == frame);
    assert((frame + rest).subrange(
        frame.len() as int, (frame + rest).len() as int,
    ) == rest);
}

// -------------------------------------------------------------------------
// Segment models
// -------------------------------------------------------------------------

pub open spec fn promise_row_fields(
    rows: Seq<model::APromise>,
) -> Seq<Seq<u8>> {
    rows.map_values(|row: model::APromise| promise_bytes(row))
}

pub open spec fn schedule_row_fields(
    rows: Seq<model::ASchedule>,
) -> Seq<Seq<u8>> {
    rows.map_values(|row: model::ASchedule| schedule_bytes(row))
}

pub open spec fn promise_segment_fields(
    header: model::AHeader,
    rows: Seq<model::APromise>,
) -> Seq<Seq<u8>> {
    seq![header_bytes(header)] + promise_row_fields(rows)
}

pub open spec fn schedule_segment_fields(
    header: model::AHeader,
    rows: Seq<model::ASchedule>,
) -> Seq<Seq<u8>> {
    seq![header_bytes(header)] + schedule_row_fields(rows)
}

pub open spec fn promise_segment_bytes(
    header: model::AHeader,
    rows: Seq<model::APromise>,
) -> Seq<u8> {
    crate::record::record_bytes(
        KIND_PROMISE_SEGMENT,
        promise_segment_fields(header, rows),
    )
}

pub open spec fn schedule_segment_bytes(
    header: model::AHeader,
    rows: Seq<model::ASchedule>,
) -> Seq<u8> {
    crate::record::record_bytes(
        KIND_SCHEDULE_SEGMENT,
        schedule_segment_fields(header, rows),
    )
}

pub open spec fn decode_promise_rows_spec(
    fields: Seq<Seq<u8>>,
) -> Option<Seq<model::APromise>>
    decreases fields.len(),
{
    if fields.len() == 0 {
        Some(Seq::empty())
    } else {
        match (
            decode_promise_spec(fields[0]),
            decode_promise_rows_spec(fields.drop_first()),
        ) {
            (Some(first), Some(rest)) => Some(seq![first] + rest),
            _ => None,
        }
    }
}

pub open spec fn decode_schedule_rows_spec(
    fields: Seq<Seq<u8>>,
) -> Option<Seq<model::ASchedule>>
    decreases fields.len(),
{
    if fields.len() == 0 {
        Some(Seq::empty())
    } else {
        match (
            decode_schedule_spec(fields[0]),
            decode_schedule_rows_spec(fields.drop_first()),
        ) {
            (Some(first), Some(rest)) => Some(seq![first] + rest),
            _ => None,
        }
    }
}

pub closed spec fn decode_promise_segment_spec(
    bytes: Seq<u8>,
) -> Option<(model::AHeader, Seq<model::APromise>)> {
    match decode_record_spec(bytes, KIND_PROMISE_SEGMENT) {
        Some(fields) if fields.len() > 0 => {
            match (
                decode_header_spec(fields[0]),
                decode_promise_rows_spec(fields.drop_first()),
            ) {
                (Some(header), Some(rows)) => Some((header, rows)),
                _ => None,
            }
        }
        _ => None,
    }
}

pub closed spec fn decode_schedule_segment_spec(
    bytes: Seq<u8>,
) -> Option<(model::AHeader, Seq<model::ASchedule>)> {
    match decode_record_spec(bytes, KIND_SCHEDULE_SEGMENT) {
        Some(fields) if fields.len() > 0 => {
            match (
                decode_header_spec(fields[0]),
                decode_schedule_rows_spec(fields.drop_first()),
            ) {
                (Some(header), Some(rows)) => Some((header, rows)),
                _ => None,
            }
        }
        _ => None,
    }
}

pub open spec fn promise_segment_wf(
    header: model::AHeader,
    rows: Seq<model::APromise>,
) -> bool {
    &&& forall|i: int| 0 <= i < rows.len()
        ==> promise_wf(#[trigger] rows[i])
    &&& record_encodable(promise_segment_fields(header, rows))
}

pub open spec fn schedule_segment_wf(
    header: model::AHeader,
    rows: Seq<model::ASchedule>,
) -> bool {
    &&& forall|i: int| 0 <= i < rows.len()
        ==> schedule_wf(#[trigger] rows[i])
    &&& record_encodable(schedule_segment_fields(header, rows))
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(80)]
proof fn lemma_decode_promise_rows_round_trip(
    rows: Seq<model::APromise>,
)
    requires
        forall|i: int| 0 <= i < rows.len()
            ==> promise_wf(#[trigger] rows[i]),
    ensures
        decode_promise_rows_spec(promise_row_fields(rows)) == Some(rows),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_promise_round_trip(rows[0]);
        lemma_decode_promise_rows_round_trip(rows.drop_first());
        assert(promise_row_fields(rows)[0] == promise_bytes(rows[0]));
        assert(promise_row_fields(rows).drop_first()
            == promise_row_fields(rows.drop_first()));
        assert(seq![rows[0]] + rows.drop_first() == rows);
    }
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(80)]
proof fn lemma_decode_schedule_rows_round_trip(
    rows: Seq<model::ASchedule>,
)
    requires
        forall|i: int| 0 <= i < rows.len()
            ==> schedule_wf(#[trigger] rows[i]),
    ensures
        decode_schedule_rows_spec(schedule_row_fields(rows)) == Some(rows),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_schedule_round_trip(rows[0]);
        lemma_decode_schedule_rows_round_trip(rows.drop_first());
        assert(schedule_row_fields(rows)[0] == schedule_bytes(rows[0]));
        assert(schedule_row_fields(rows).drop_first()
            == schedule_row_fields(rows.drop_first()));
        assert(seq![rows[0]] + rows.drop_first() == rows);
    }
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(200)]
pub proof fn lemma_promise_segment_round_trip(
    header: model::AHeader,
    rows: Seq<model::APromise>,
)
    requires promise_segment_wf(header, rows),
    ensures
        decode_promise_segment_spec(promise_segment_bytes(header, rows))
            == Some((header, rows)),
{
    reveal(decode_promise_segment_spec);
    lemma_header_round_trip(header);
    lemma_decode_promise_rows_round_trip(rows);
    crate::record::lemma_record_round_trip(
        KIND_PROMISE_SEGMENT,
        promise_segment_fields(header, rows),
    );
    assert(decode_record_spec(
        promise_segment_bytes(header, rows),
        KIND_PROMISE_SEGMENT,
    ) == Some(promise_segment_fields(header, rows)));
    assert(promise_segment_fields(header, rows).len()
        == rows.len() + 1);
    assert(promise_segment_fields(header, rows)[0]
        == header_bytes(header));
    assert(promise_segment_fields(header, rows).drop_first()
        == promise_row_fields(rows));
    assert(decode_header_spec(header_bytes(header)) == Some(header));
    assert(decode_promise_rows_spec(promise_row_fields(rows))
        == Some(rows));
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(200)]
pub proof fn lemma_schedule_segment_round_trip(
    header: model::AHeader,
    rows: Seq<model::ASchedule>,
)
    requires schedule_segment_wf(header, rows),
    ensures
        decode_schedule_segment_spec(schedule_segment_bytes(header, rows))
            == Some((header, rows)),
{
    reveal(decode_schedule_segment_spec);
    lemma_header_round_trip(header);
    lemma_decode_schedule_rows_round_trip(rows);
    crate::record::lemma_record_round_trip(
        KIND_SCHEDULE_SEGMENT,
        schedule_segment_fields(header, rows),
    );
    assert(decode_record_spec(
        schedule_segment_bytes(header, rows),
        KIND_SCHEDULE_SEGMENT,
    ) == Some(schedule_segment_fields(header, rows)));
    assert(schedule_segment_fields(header, rows).len()
        == rows.len() + 1);
    assert(schedule_segment_fields(header, rows)[0]
        == header_bytes(header));
    assert(schedule_segment_fields(header, rows).drop_first()
        == schedule_row_fields(rows));
    assert(decode_header_spec(header_bytes(header)) == Some(header));
    assert(decode_schedule_rows_spec(schedule_row_fields(rows))
        == Some(rows));
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(40)]
pub proof fn lemma_split_promise_segment(
    header: model::AHeader,
    rows: Seq<model::APromise>,
    rest: Seq<u8>,
)
    requires
        promise_segment_wf(header, rows),
    ensures
        split_frame_spec(
            promise_segment_bytes(header, rows) + rest,
        ) == Some((promise_segment_bytes(header, rows), rest)),
{
    let payload = blob_sequence_bytes(
        promise_segment_fields(header, rows),
    );
    lemma_split_envelope(KIND_PROMISE_SEGMENT, payload, rest);
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(40)]
pub proof fn lemma_split_schedule_segment(
    header: model::AHeader,
    rows: Seq<model::ASchedule>,
    rest: Seq<u8>,
)
    requires
        schedule_segment_wf(header, rows),
    ensures
        split_frame_spec(
            schedule_segment_bytes(header, rows) + rest,
        ) == Some((schedule_segment_bytes(header, rows), rest)),
{
    let payload = blob_sequence_bytes(
        schedule_segment_fields(header, rows),
    );
    lemma_split_envelope(KIND_SCHEDULE_SEGMENT, payload, rest);
}

// -------------------------------------------------------------------------
// Executable model segments
// -------------------------------------------------------------------------

fn push_bytes(values: &mut Vec<Vec<u8>>, value: Vec<u8>)
    ensures
        final(values).deep_view()
            == old(values).deep_view().push(value@),
{
    let ghost old_vec = values@;
    let ghost old_values = values.deep_view();
    let ghost value_view = value@;
    values.push(value);
    assert(values.deep_view() =~= old_values.push(value_view)) by {
        assert(values.deep_view().len() == old_values.len() + 1);
        assert forall|i: int| 0 <= i < values.deep_view().len()
            implies values.deep_view()[i]
                == old_values.push(value_view)[i] by {
            if i < old_values.len() {
                assert(values@[i] == old_vec[i]);
                assert(old_values[i] == old_vec[i]@);
            } else {
                assert(i == old_values.len());
            }
        }
    }
}

proof fn lemma_subrange_step<A>(values: Seq<A>, i: int)
    requires 0 <= i < values.len(),
    ensures
        values.subrange(0, i + 1)
            == values.subrange(0, i).push(values[i]),
        values.subrange(i + 1, values.len() as int)
            == values.subrange(i, values.len() as int).drop_first(),
{
}

proof fn lemma_promise_row_fields_push(
    rows: Seq<model::APromise>,
    row: model::APromise,
)
    ensures
        promise_row_fields(rows.push(row))
            == promise_row_fields(rows).push(promise_bytes(row)),
{
}

proof fn lemma_schedule_row_fields_push(
    rows: Seq<model::ASchedule>,
    row: model::ASchedule,
)
    ensures
        schedule_row_fields(rows.push(row))
            == schedule_row_fields(rows).push(schedule_bytes(row)),
{
}

fn encode_promise_segment_model(
    header: &model::Header,
    rows: &Vec<model::Promise>,
) -> (result: DocumentResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@
            == promise_segment_bytes(header@, rows.deep_view()),
        result is Ok && promise_segment_wf(header@, rows.deep_view())
            ==> decode_promise_segment_spec(result->Ok_0@)
                == Some((header@, rows.deep_view())),
{
    let mut fields = Vec::new();
    push_bytes(&mut fields, crate::runtime::encode_header(header)?);
    let mut i = 0usize;
    while i < rows.len()
        invariant
            i <= rows.len(),
            fields.deep_view()
                == seq![header_bytes(header@)]
                    + promise_row_fields(
                        rows.deep_view().subrange(0, i as int),
                    ),
        decreases rows.len() - i,
    {
        let ghost prefix =
            rows.deep_view().subrange(0, i as int);
        let ghost row = rows.deep_view()[i as int];
        let encoded = crate::runtime::encode_promise_model(&rows[i])?;
        assert(encoded@ == promise_bytes(row));
        proof {
            lemma_subrange_step(rows.deep_view(), i as int);
            lemma_promise_row_fields_push(prefix, row);
        }
        push_bytes(&mut fields, encoded);
        i += 1;
    }
    assert(rows.deep_view().subrange(0, rows.len() as int)
        == rows.deep_view());
    assert(fields.deep_view()
        == promise_segment_fields(header@, rows.deep_view()));
    let result = match encode_record(KIND_PROMISE_SEGMENT, &fields) {
        None => Err("Promise segment is not canonically encodable"),
        Some(bytes) => Ok(bytes),
    };
    proof {
        if result is Ok
            && promise_segment_wf(header@, rows.deep_view()) {
            lemma_promise_segment_round_trip(header@, rows.deep_view());
        }
    }
    result
}

fn encode_schedule_segment_model(
    header: &model::Header,
    rows: &Vec<model::Schedule>,
) -> (result: DocumentResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@
            == schedule_segment_bytes(header@, rows.deep_view()),
        result is Ok && schedule_segment_wf(header@, rows.deep_view())
            ==> decode_schedule_segment_spec(result->Ok_0@)
                == Some((header@, rows.deep_view())),
{
    let mut fields = Vec::new();
    push_bytes(&mut fields, crate::runtime::encode_header(header)?);
    let mut i = 0usize;
    while i < rows.len()
        invariant
            i <= rows.len(),
            fields.deep_view()
                == seq![header_bytes(header@)]
                    + schedule_row_fields(
                        rows.deep_view().subrange(0, i as int),
                    ),
        decreases rows.len() - i,
    {
        let ghost prefix =
            rows.deep_view().subrange(0, i as int);
        let ghost row = rows.deep_view()[i as int];
        let encoded = crate::runtime::encode_schedule_model(&rows[i])?;
        assert(encoded@ == schedule_bytes(row));
        proof {
            lemma_subrange_step(rows.deep_view(), i as int);
            lemma_schedule_row_fields_push(prefix, row);
        }
        push_bytes(&mut fields, encoded);
        i += 1;
    }
    assert(rows.deep_view().subrange(0, rows.len() as int)
        == rows.deep_view());
    assert(fields.deep_view()
        == schedule_segment_fields(header@, rows.deep_view()));
    let result = match encode_record(KIND_SCHEDULE_SEGMENT, &fields) {
        None => Err("Schedule segment is not canonically encodable"),
        Some(bytes) => Ok(bytes),
    };
    proof {
        if result is Ok
            && schedule_segment_wf(header@, rows.deep_view()) {
            lemma_schedule_segment_round_trip(header@, rows.deep_view());
        }
    }
    result
}

proof fn lemma_decode_promise_rows_none(
    fields: Seq<Seq<u8>>,
)
    requires
        fields.len() > 0,
        decode_promise_spec(fields[0]) is None,
    ensures decode_promise_rows_spec(fields) is None,
{
    reveal_with_fuel(decode_promise_rows_spec, 2);
}

proof fn lemma_decode_promise_rows_rest_none(
    fields: Seq<Seq<u8>>,
    first: model::APromise,
)
    requires
        fields.len() > 0,
        decode_promise_spec(fields[0]) == Some(first),
        decode_promise_rows_spec(fields.drop_first()) is None,
    ensures decode_promise_rows_spec(fields) is None,
{
    reveal_with_fuel(decode_promise_rows_spec, 2);
}

proof fn lemma_decode_promise_rows_some(
    fields: Seq<Seq<u8>>,
    first: model::APromise,
    rest: Seq<model::APromise>,
)
    requires
        fields.len() > 0,
        decode_promise_spec(fields[0]) == Some(first),
        decode_promise_rows_spec(fields.drop_first()) == Some(rest),
    ensures
        decode_promise_rows_spec(fields) == Some(seq![first] + rest),
{
    reveal_with_fuel(decode_promise_rows_spec, 2);
}

proof fn lemma_decode_schedule_rows_none(
    fields: Seq<Seq<u8>>,
)
    requires
        fields.len() > 0,
        decode_schedule_spec(fields[0]) is None,
    ensures decode_schedule_rows_spec(fields) is None,
{
    reveal_with_fuel(decode_schedule_rows_spec, 2);
}

proof fn lemma_decode_schedule_rows_rest_none(
    fields: Seq<Seq<u8>>,
    first: model::ASchedule,
)
    requires
        fields.len() > 0,
        decode_schedule_spec(fields[0]) == Some(first),
        decode_schedule_rows_spec(fields.drop_first()) is None,
    ensures decode_schedule_rows_spec(fields) is None,
{
    reveal_with_fuel(decode_schedule_rows_spec, 2);
}

proof fn lemma_decode_schedule_rows_some(
    fields: Seq<Seq<u8>>,
    first: model::ASchedule,
    rest: Seq<model::ASchedule>,
)
    requires
        fields.len() > 0,
        decode_schedule_spec(fields[0]) == Some(first),
        decode_schedule_rows_spec(fields.drop_first()) == Some(rest),
    ensures
        decode_schedule_rows_spec(fields) == Some(seq![first] + rest),
{
    reveal_with_fuel(decode_schedule_rows_spec, 2);
}

fn decode_promise_fields(
    fields: &Vec<Vec<u8>>,
    index: usize,
) -> (result: DocumentResult<Vec<model::Promise>>)
    requires index <= fields.len(),
    ensures
        match result {
            Ok(rows) => {
                &&& decode_promise_rows_spec(
                    fields.deep_view().subrange(
                        index as int, fields.len() as int,
                    ),
                ) == Some(rows.deep_view())
                &&& forall|i: int| 0 <= i < rows.len()
                    ==> crate::bridge::promise_text_wf(rows[i]@)
            }
            Err(_) => decode_promise_rows_spec(
                fields.deep_view().subrange(
                    index as int, fields.len() as int,
                ),
            ) is None,
        },
    decreases fields.len() - index,
{
    if index == fields.len() {
        return Ok(Vec::new());
    }
    let ghost remaining = fields.deep_view().subrange(
        index as int, fields.len() as int,
    );
    proof {
        lemma_subrange_step(fields.deep_view(), index as int);
    }
    assert(remaining.len() > 0);
    let first_bytes = &fields[index];
    assert(remaining[0] == first_bytes@);
    let first = match crate::runtime::decode_promise_model(first_bytes) {
        Err(error) => {
            assert(decode_promise_spec(remaining[0]) is None);
            proof {
                lemma_decode_promise_rows_none(remaining);
            }
            return Err(error);
        }
        Ok(first) => first,
    };
    let ghost first_view = first@;
    assert(decode_promise_spec(remaining[0]) == Some(first_view));
    let mut rest = match decode_promise_fields(fields, index + 1) {
        Err(error) => {
            assert(decode_promise_rows_spec(remaining.drop_first()) is None);
            proof {
                lemma_decode_promise_rows_rest_none(
                    remaining, first_view,
                );
            }
            return Err(error);
        }
        Ok(rest) => rest,
    };
    let ghost old_rest = rest.deep_view();
    rest.insert(0, first);
    assert(rest.deep_view() =~= seq![first_view] + old_rest);
    proof {
        lemma_decode_promise_rows_some(
            remaining, first_view, old_rest,
        );
    }
    Ok(rest)
}

fn decode_schedule_fields(
    fields: &Vec<Vec<u8>>,
    index: usize,
) -> (result: DocumentResult<Vec<model::Schedule>>)
    requires index <= fields.len(),
    ensures
        match result {
            Ok(rows) => {
                &&& decode_schedule_rows_spec(
                    fields.deep_view().subrange(
                        index as int, fields.len() as int,
                    ),
                ) == Some(rows.deep_view())
                &&& forall|i: int| 0 <= i < rows.len()
                    ==> crate::bridge::schedule_text_wf(rows[i]@)
            }
            Err(_) => decode_schedule_rows_spec(
                fields.deep_view().subrange(
                    index as int, fields.len() as int,
                ),
            ) is None,
        },
    decreases fields.len() - index,
{
    if index == fields.len() {
        return Ok(Vec::new());
    }
    let ghost remaining = fields.deep_view().subrange(
        index as int, fields.len() as int,
    );
    proof {
        lemma_subrange_step(fields.deep_view(), index as int);
    }
    assert(remaining.len() > 0);
    let first_bytes = &fields[index];
    assert(remaining[0] == first_bytes@);
    let first = match crate::runtime::decode_schedule_model(first_bytes) {
        Err(error) => {
            assert(decode_schedule_spec(remaining[0]) is None);
            proof {
                lemma_decode_schedule_rows_none(remaining);
            }
            return Err(error);
        }
        Ok(first) => first,
    };
    let ghost first_view = first@;
    assert(decode_schedule_spec(remaining[0]) == Some(first_view));
    let mut rest = match decode_schedule_fields(fields, index + 1) {
        Err(error) => {
            assert(decode_schedule_rows_spec(remaining.drop_first()) is None);
            proof {
                lemma_decode_schedule_rows_rest_none(
                    remaining, first_view,
                );
            }
            return Err(error);
        }
        Ok(rest) => rest,
    };
    let ghost old_rest = rest.deep_view();
    rest.insert(0, first);
    assert(rest.deep_view() =~= seq![first_view] + old_rest);
    proof {
        lemma_decode_schedule_rows_some(
            remaining, first_view, old_rest,
        );
    }
    Ok(rest)
}

fn decode_promise_segment_model(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(model::Header, Vec<model::Promise>)>)
    ensures
        match result {
            Ok((header, rows)) => {
                &&& decode_promise_segment_spec(bytes@)
                    == Some((header@, rows.deep_view()))
                &&& forall|i: int| 0 <= i < rows.len()
                    ==> crate::bridge::promise_text_wf(rows[i]@)
            }
            Err(_) => decode_promise_segment_spec(bytes@) is None,
        },
{
    reveal(decode_promise_segment_spec);
    let fields = match decode_record(bytes, KIND_PROMISE_SEGMENT) {
        None => return Err("invalid Promise segment"),
        Some(fields) => fields,
    };
    let ghost fv = fields.deep_view();
    assert(decode_record_spec(bytes@, KIND_PROMISE_SEGMENT) == Some(fv));
    if fields.len() == 0 {
        return Err("Promise segment has no Header");
    }
    assert(fields[0]@ == fv[0]);
    let header = match crate::runtime::decode_header(&fields[0]) {
        Err(error) => return Err(error),
        Ok(header) => header,
    };
    let rows = match decode_promise_fields(&fields, 1) {
        Err(error) => return Err(error),
        Ok(rows) => rows,
    };
    assert(fv.subrange(1, fv.len() as int) == fv.drop_first());
    assert(decode_promise_segment_spec(bytes@)
        == Some((header@, rows.deep_view())));
    Ok((header, rows))
}

fn decode_schedule_segment_model(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(model::Header, Vec<model::Schedule>)>)
    ensures
        match result {
            Ok((header, rows)) => {
                &&& decode_schedule_segment_spec(bytes@)
                    == Some((header@, rows.deep_view()))
                &&& forall|i: int| 0 <= i < rows.len()
                    ==> crate::bridge::schedule_text_wf(rows[i]@)
            }
            Err(_) => decode_schedule_segment_spec(bytes@) is None,
        },
{
    reveal(decode_schedule_segment_spec);
    let fields = match decode_record(bytes, KIND_SCHEDULE_SEGMENT) {
        None => return Err("invalid Schedule segment"),
        Some(fields) => fields,
    };
    let ghost fv = fields.deep_view();
    assert(decode_record_spec(bytes@, KIND_SCHEDULE_SEGMENT) == Some(fv));
    if fields.len() == 0 {
        return Err("Schedule segment has no Header");
    }
    assert(fields[0]@ == fv[0]);
    let header = match crate::runtime::decode_header(&fields[0]) {
        Err(error) => return Err(error),
        Ok(header) => header,
    };
    let rows = match decode_schedule_fields(&fields, 1) {
        Err(error) => return Err(error),
        Ok(rows) => rows,
    };
    assert(fv.subrange(1, fv.len() as int) == fv.drop_first());
    assert(decode_schedule_segment_spec(bytes@)
        == Some((header@, rows.deep_view())));
    Ok((header, rows))
}

// -------------------------------------------------------------------------
// Last-row-wins folds
// -------------------------------------------------------------------------

pub open spec fn find_promise_id(
    rows: Seq<model::APromise>,
    id: Seq<u8>,
) -> Option<int>
    decreases rows.len(),
{
    if rows.len() == 0 {
        None
    } else if rows[0].id == id {
        Some(0)
    } else {
        match find_promise_id(rows.drop_first(), id) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

pub open spec fn find_schedule_id(
    rows: Seq<model::ASchedule>,
    id: Seq<u8>,
) -> Option<int>
    decreases rows.len(),
{
    if rows.len() == 0 {
        None
    } else if rows[0].id == id {
        Some(0)
    } else {
        match find_schedule_id(rows.drop_first(), id) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

pub open spec fn upsert_promise(
    rows: Seq<model::APromise>,
    row: model::APromise,
) -> Seq<model::APromise> {
    match find_promise_id(rows, row.id) {
        Some(i) => rows.update(i, row),
        None => rows.push(row),
    }
}

pub open spec fn upsert_schedule(
    rows: Seq<model::ASchedule>,
    row: model::ASchedule,
) -> Seq<model::ASchedule> {
    match find_schedule_id(rows, row.id) {
        Some(i) => rows.update(i, row),
        None => rows.push(row),
    }
}

/// Fold in commit order. Replacement keeps the first-seen position.
pub open spec fn fold_promises(
    rows: Seq<model::APromise>,
) -> Seq<model::APromise>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        upsert_promise(fold_promises(rows.drop_last()), rows.last())
    }
}

pub open spec fn fold_schedules(
    rows: Seq<model::ASchedule>,
) -> Seq<model::ASchedule>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        upsert_schedule(fold_schedules(rows.drop_last()), rows.last())
    }
}

pub open spec fn distinct_promise_ids(
    rows: Seq<model::APromise>,
) -> bool {
    forall|i: int, j: int|
        0 <= i < rows.len() && 0 <= j < rows.len()
            && #[trigger] rows[i].id == #[trigger] rows[j].id
        ==> i == j
}

pub open spec fn distinct_schedule_ids(
    rows: Seq<model::ASchedule>,
) -> bool {
    forall|i: int, j: int|
        0 <= i < rows.len() && 0 <= j < rows.len()
            && #[trigger] rows[i].id == #[trigger] rows[j].id
        ==> i == j
}

proof fn lemma_find_promise_id(
    rows: Seq<model::APromise>,
    id: Seq<u8>,
)
    ensures
        match find_promise_id(rows, id) {
            Some(i) => 0 <= i < rows.len() && rows[i].id == id,
            None => forall|i: int| 0 <= i < rows.len()
                ==> rows[i].id != id,
        },
    decreases rows.len(),
{
    if rows.len() > 0 {
        if rows[0].id != id {
            let rest = rows.drop_first();
            lemma_find_promise_id(rest, id);
            match find_promise_id(rest, id) {
                Some(i) => {
                    assert(rows[i + 1].id == rest[i].id);
                }
                None => {
                    assert forall|i: int| 0 <= i < rows.len()
                        implies rows[i].id != id by {
                        if i > 0 {
                            assert(rows[i].id == rest[i - 1].id);
                        }
                    }
                }
            }
        }
    }
}

proof fn lemma_find_schedule_id(
    rows: Seq<model::ASchedule>,
    id: Seq<u8>,
)
    ensures
        match find_schedule_id(rows, id) {
            Some(i) => 0 <= i < rows.len() && rows[i].id == id,
            None => forall|i: int| 0 <= i < rows.len()
                ==> rows[i].id != id,
        },
    decreases rows.len(),
{
    if rows.len() > 0 {
        if rows[0].id != id {
            let rest = rows.drop_first();
            lemma_find_schedule_id(rest, id);
            match find_schedule_id(rest, id) {
                Some(i) => {
                    assert(rows[i + 1].id == rest[i].id);
                }
                None => {
                    assert forall|i: int| 0 <= i < rows.len()
                        implies rows[i].id != id by {
                        if i > 0 {
                            assert(rows[i].id == rest[i - 1].id);
                        }
                    }
                }
            }
        }
    }
}

proof fn lemma_find_promise_at(
    rows: Seq<model::APromise>,
    id: Seq<u8>,
    index: int,
)
    requires
        0 <= index < rows.len(),
        rows[index].id == id,
        forall|j: int| 0 <= j < index ==> rows[j].id != id,
    ensures find_promise_id(rows, id) == Some(index),
    decreases index,
{
    if index > 0 {
        lemma_find_promise_at(rows.drop_first(), id, index - 1);
    }
}

proof fn lemma_find_schedule_at(
    rows: Seq<model::ASchedule>,
    id: Seq<u8>,
    index: int,
)
    requires
        0 <= index < rows.len(),
        rows[index].id == id,
        forall|j: int| 0 <= j < index ==> rows[j].id != id,
    ensures find_schedule_id(rows, id) == Some(index),
    decreases index,
{
    if index > 0 {
        lemma_find_schedule_at(rows.drop_first(), id, index - 1);
    }
}

proof fn lemma_upsert_promise_distinct(
    rows: Seq<model::APromise>,
    row: model::APromise,
)
    requires distinct_promise_ids(rows),
    ensures distinct_promise_ids(upsert_promise(rows, row)),
{
    lemma_find_promise_id(rows, row.id);
    match find_promise_id(rows, row.id) {
        Some(index) => {
            assert forall|i: int, j: int|
                0 <= i < rows.len() && 0 <= j < rows.len()
                    && #[trigger] rows.update(index, row)[i].id
                        == #[trigger] rows.update(index, row)[j].id
                implies i == j by {
                if i != index && j == index {
                    assert(rows[i].id != row.id);
                }
                if i == index && j != index {
                    assert(rows[j].id != row.id);
                }
            }
        }
        None => {
            assert forall|i: int, j: int|
                0 <= i < rows.push(row).len()
                    && 0 <= j < rows.push(row).len()
                    && #[trigger] rows.push(row)[i].id
                        == #[trigger] rows.push(row)[j].id
                implies i == j by {
                if i < rows.len() && j == rows.len() {
                    assert(rows[i].id != row.id);
                }
                if i == rows.len() && j < rows.len() {
                    assert(rows[j].id != row.id);
                }
            }
        }
    }
}

proof fn lemma_upsert_schedule_distinct(
    rows: Seq<model::ASchedule>,
    row: model::ASchedule,
)
    requires distinct_schedule_ids(rows),
    ensures distinct_schedule_ids(upsert_schedule(rows, row)),
{
    lemma_find_schedule_id(rows, row.id);
    match find_schedule_id(rows, row.id) {
        Some(index) => {
            assert forall|i: int, j: int|
                0 <= i < rows.len() && 0 <= j < rows.len()
                    && #[trigger] rows.update(index, row)[i].id
                        == #[trigger] rows.update(index, row)[j].id
                implies i == j by {
                if i != index && j == index {
                    assert(rows[i].id != row.id);
                }
                if i == index && j != index {
                    assert(rows[j].id != row.id);
                }
            }
        }
        None => {
            assert forall|i: int, j: int|
                0 <= i < rows.push(row).len()
                    && 0 <= j < rows.push(row).len()
                    && #[trigger] rows.push(row)[i].id
                        == #[trigger] rows.push(row)[j].id
                implies i == j by {
                if i < rows.len() && j == rows.len() {
                    assert(rows[i].id != row.id);
                }
                if i == rows.len() && j < rows.len() {
                    assert(rows[j].id != row.id);
                }
            }
        }
    }
}

pub proof fn lemma_fold_promises_distinct(
    rows: Seq<model::APromise>,
)
    ensures distinct_promise_ids(fold_promises(rows)),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_fold_promises_distinct(rows.drop_last());
        lemma_upsert_promise_distinct(
            fold_promises(rows.drop_last()), rows.last(),
        );
    }
}

pub proof fn lemma_fold_schedules_distinct(
    rows: Seq<model::ASchedule>,
)
    ensures distinct_schedule_ids(fold_schedules(rows)),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_fold_schedules_distinct(rows.drop_last());
        lemma_upsert_schedule_distinct(
            fold_schedules(rows.drop_last()), rows.last(),
        );
    }
}

proof fn lemma_fold_distinct_promises_unchanged(
    rows: Seq<model::APromise>,
)
    requires distinct_promise_ids(rows),
    ensures fold_promises(rows) == rows,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let prefix = rows.drop_last();
        let last = rows.last();
        assert(distinct_promise_ids(prefix));
        lemma_fold_distinct_promises_unchanged(prefix);
        lemma_find_promise_id(prefix, last.id);
        assert(find_promise_id(prefix, last.id) is None) by {
            if find_promise_id(prefix, last.id) is Some {
                let i = find_promise_id(prefix, last.id)->Some_0;
                assert(prefix[i].id == last.id);
                assert(rows[i].id == rows[rows.len() - 1].id);
            }
        }
        assert(prefix.push(last) == rows);
    }
}

proof fn lemma_fold_distinct_schedules_unchanged(
    rows: Seq<model::ASchedule>,
)
    requires distinct_schedule_ids(rows),
    ensures fold_schedules(rows) == rows,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let prefix = rows.drop_last();
        let last = rows.last();
        assert(distinct_schedule_ids(prefix));
        lemma_fold_distinct_schedules_unchanged(prefix);
        lemma_find_schedule_id(prefix, last.id);
        assert(find_schedule_id(prefix, last.id) is None) by {
            if find_schedule_id(prefix, last.id) is Some {
                let i = find_schedule_id(prefix, last.id)->Some_0;
                assert(prefix[i].id == last.id);
                assert(rows[i].id == rows[rows.len() - 1].id);
            }
        }
        assert(prefix.push(last) == rows);
    }
}

/// Replaying compacted rows is a no-op.
pub proof fn lemma_fold_promises_idempotent(
    rows: Seq<model::APromise>,
)
    ensures fold_promises(fold_promises(rows)) == fold_promises(rows),
{
    lemma_fold_promises_distinct(rows);
    lemma_fold_distinct_promises_unchanged(fold_promises(rows));
}

/// Replaying compacted rows is a no-op.
pub proof fn lemma_fold_schedules_idempotent(
    rows: Seq<model::ASchedule>,
)
    ensures fold_schedules(fold_schedules(rows)) == fold_schedules(rows),
{
    lemma_fold_schedules_distinct(rows);
    lemma_fold_distinct_schedules_unchanged(fold_schedules(rows));
}

fn find_promise(
    rows: &Vec<model::Promise>,
    id: &crate::text::Text,
) -> (result: Option<usize>)
    ensures
        match result {
            Some(i) => {
                &&& i < rows.len()
                &&& find_promise_id(rows.deep_view(), id@)
                    == Some(i as int)
            }
            None => find_promise_id(rows.deep_view(), id@) is None,
        },
{
    let mut i = 0usize;
    while i < rows.len()
        invariant
            i <= rows.len(),
            forall|j: int| 0 <= j < i
                ==> rows.deep_view()[j].id != id@,
        decreases rows.len() - i,
    {
        if rows[i].id.bytes == id.bytes {
            assert(rows.deep_view()[i as int].id == id@);
            proof {
                lemma_find_promise_at(
                    rows.deep_view(), id@, i as int,
                );
            }
            return Some(i);
        }
        i += 1;
    }
    proof {
        lemma_find_promise_id(rows.deep_view(), id@);
    }
    None
}

fn find_schedule(
    rows: &Vec<model::Schedule>,
    id: &crate::text::Text,
) -> (result: Option<usize>)
    ensures
        match result {
            Some(i) => {
                &&& i < rows.len()
                &&& find_schedule_id(rows.deep_view(), id@)
                    == Some(i as int)
            }
            None => find_schedule_id(rows.deep_view(), id@) is None,
        },
{
    let mut i = 0usize;
    while i < rows.len()
        invariant
            i <= rows.len(),
            forall|j: int| 0 <= j < i
                ==> rows.deep_view()[j].id != id@,
        decreases rows.len() - i,
    {
        if rows[i].id.bytes == id.bytes {
            assert(rows.deep_view()[i as int].id == id@);
            proof {
                lemma_find_schedule_at(
                    rows.deep_view(), id@, i as int,
                );
            }
            return Some(i);
        }
        i += 1;
    }
    proof {
        lemma_find_schedule_id(rows.deep_view(), id@);
    }
    None
}

fn upsert_promise_exec(
    rows: &mut Vec<model::Promise>,
    row: model::Promise,
)
    ensures
        final(rows).deep_view()
            == upsert_promise(old(rows).deep_view(), row@),
        (
            forall|i: int| 0 <= i < old(rows).len()
                ==> crate::bridge::promise_text_wf(old(rows)[i]@)
        ) && crate::bridge::promise_text_wf(row@)
            ==> forall|i: int| 0 <= i < final(rows).len()
                ==> crate::bridge::promise_text_wf(final(rows)[i]@),
{
    let ghost before = rows.deep_view();
    let ghost row_view = row@;
    match find_promise(rows, &row.id) {
        Some(i) => {
            rows.set(i, row);
            assert(rows.deep_view() =~= before.update(i as int, row_view));
        }
        None => {
            rows.push(row);
            assert(rows.deep_view() =~= before.push(row_view));
        }
    }
}

fn upsert_schedule_exec(
    rows: &mut Vec<model::Schedule>,
    row: model::Schedule,
)
    ensures
        final(rows).deep_view()
            == upsert_schedule(old(rows).deep_view(), row@),
        (
            forall|i: int| 0 <= i < old(rows).len()
                ==> crate::bridge::schedule_text_wf(old(rows)[i]@)
        ) && crate::bridge::schedule_text_wf(row@)
            ==> forall|i: int| 0 <= i < final(rows).len()
                ==> crate::bridge::schedule_text_wf(final(rows)[i]@),
{
    let ghost before = rows.deep_view();
    let ghost row_view = row@;
    match find_schedule(rows, &row.id) {
        Some(i) => {
            rows.set(i, row);
            assert(rows.deep_view() =~= before.update(i as int, row_view));
        }
        None => {
            rows.push(row);
            assert(rows.deep_view() =~= before.push(row_view));
        }
    }
}

fn fold_promises_exec(
    mut rows: Vec<model::Promise>,
    Ghost(input): Ghost<Seq<model::APromise>>,
) -> (result: Vec<model::Promise>)
    requires rows.deep_view() == input,
    ensures
        result.deep_view() == fold_promises(input),
        (
            forall|i: int| 0 <= i < input.len()
                ==> crate::bridge::promise_text_wf(#[trigger] input[i])
        ) ==> forall|i: int| 0 <= i < result.len()
            ==> crate::bridge::promise_text_wf(result[i]@),
    decreases rows.len(),
{
    if rows.len() == 0 {
        Vec::new()
    } else {
        let ghost original = rows.deep_view();
        let last = rows.pop().unwrap();
        let ghost last_view = last@;
        let ghost prefix = rows.deep_view();
        assert(prefix == original.drop_last());
        assert(last_view == original.last());
        let mut result = fold_promises_exec(rows, Ghost(prefix));
        upsert_promise_exec(&mut result, last);
        assert(original.drop_last().push(original.last()) == original);
        result
    }
}

fn fold_schedules_exec(
    mut rows: Vec<model::Schedule>,
    Ghost(input): Ghost<Seq<model::ASchedule>>,
) -> (result: Vec<model::Schedule>)
    requires rows.deep_view() == input,
    ensures
        result.deep_view() == fold_schedules(input),
        (
            forall|i: int| 0 <= i < input.len()
                ==> crate::bridge::schedule_text_wf(#[trigger] input[i])
        ) ==> forall|i: int| 0 <= i < result.len()
            ==> crate::bridge::schedule_text_wf(result[i]@),
    decreases rows.len(),
{
    if rows.len() == 0 {
        Vec::new()
    } else {
        let ghost original = rows.deep_view();
        let last = rows.pop().unwrap();
        let ghost last_view = last@;
        let ghost prefix = rows.deep_view();
        assert(prefix == original.drop_last());
        assert(last_view == original.last());
        let mut result = fold_schedules_exec(rows, Ghost(prefix));
        upsert_schedule_exec(&mut result, last);
        assert(original.drop_last().push(original.last()) == original);
        result
    }
}

// -------------------------------------------------------------------------
// Concatenated documents and append/compaction laws
// -------------------------------------------------------------------------

pub closed spec fn decode_promise_document_raw_spec(
    bytes: Seq<u8>,
) -> Option<(Option<model::AHeader>, Seq<model::APromise>)>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        Some((None, Seq::empty()))
    } else {
        match split_frame_spec(bytes) {
            Some((frame, rest)) if rest.len() < bytes.len() => {
                match (
                    decode_promise_segment_spec(frame),
                    decode_promise_document_raw_spec(rest),
                ) {
                    (
                        Some((header, rows)),
                        Some((tail_header, tail_rows)),
                    ) => Some((
                        if tail_header is Some {
                            tail_header
                        } else {
                            Some(header)
                        },
                        rows + tail_rows,
                    )),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

pub closed spec fn decode_schedule_document_raw_spec(
    bytes: Seq<u8>,
) -> Option<(Option<model::AHeader>, Seq<model::ASchedule>)>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        Some((None, Seq::empty()))
    } else {
        match split_frame_spec(bytes) {
            Some((frame, rest)) if rest.len() < bytes.len() => {
                match (
                    decode_schedule_segment_spec(frame),
                    decode_schedule_document_raw_spec(rest),
                ) {
                    (
                        Some((header, rows)),
                        Some((tail_header, tail_rows)),
                    ) => Some((
                        if tail_header is Some {
                            tail_header
                        } else {
                            Some(header)
                        },
                        rows + tail_rows,
                    )),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

pub closed spec fn decode_promise_document_spec(
    bytes: Seq<u8>,
) -> Option<(Option<model::AHeader>, Seq<model::APromise>)> {
    match decode_promise_document_raw_spec(bytes) {
        Some((header, rows)) => Some((header, fold_promises(rows))),
        None => None,
    }
}

pub closed spec fn decode_schedule_document_spec(
    bytes: Seq<u8>,
) -> Option<(Option<model::AHeader>, Seq<model::ASchedule>)> {
    match decode_schedule_document_raw_spec(bytes) {
        Some((header, rows)) => Some((header, fold_schedules(rows))),
        None => None,
    }
}

proof fn lemma_decode_promise_document_cons(
    bytes: Seq<u8>,
    frame: Seq<u8>,
    rest: Seq<u8>,
    header: model::AHeader,
    rows: Seq<model::APromise>,
    tail_header: Option<model::AHeader>,
    tail_rows: Seq<model::APromise>,
)
    requires
        bytes.len() > 0,
        split_frame_spec(bytes) == Some((frame, rest)),
        rest.len() < bytes.len(),
        decode_promise_segment_spec(frame) == Some((header, rows)),
        decode_promise_document_raw_spec(rest)
            == Some((tail_header, tail_rows)),
    ensures
        decode_promise_document_raw_spec(bytes) == Some((
            if tail_header is Some {
                tail_header
            } else {
                Some(header)
            },
            rows + tail_rows,
        )),
{
    reveal_with_fuel(decode_promise_document_raw_spec, 1);
}

proof fn lemma_decode_schedule_document_cons(
    bytes: Seq<u8>,
    frame: Seq<u8>,
    rest: Seq<u8>,
    header: model::AHeader,
    rows: Seq<model::ASchedule>,
    tail_header: Option<model::AHeader>,
    tail_rows: Seq<model::ASchedule>,
)
    requires
        bytes.len() > 0,
        split_frame_spec(bytes) == Some((frame, rest)),
        rest.len() < bytes.len(),
        decode_schedule_segment_spec(frame) == Some((header, rows)),
        decode_schedule_document_raw_spec(rest)
            == Some((tail_header, tail_rows)),
    ensures
        decode_schedule_document_raw_spec(bytes) == Some((
            if tail_header is Some {
                tail_header
            } else {
                Some(header)
            },
            rows + tail_rows,
        )),
{
    reveal_with_fuel(decode_schedule_document_raw_spec, 1);
}

pub open spec fn promise_document_bytes(
    segments: Seq<(model::AHeader, Seq<model::APromise>)>,
) -> Seq<u8>
    decreases segments.len(),
{
    if segments.len() == 0 {
        Seq::empty()
    } else {
        promise_segment_bytes(segments[0].0, segments[0].1)
            + promise_document_bytes(segments.drop_first())
    }
}

pub open spec fn schedule_document_bytes(
    segments: Seq<(model::AHeader, Seq<model::ASchedule>)>,
) -> Seq<u8>
    decreases segments.len(),
{
    if segments.len() == 0 {
        Seq::empty()
    } else {
        schedule_segment_bytes(segments[0].0, segments[0].1)
            + schedule_document_bytes(segments.drop_first())
    }
}

pub open spec fn promise_document_rows(
    segments: Seq<(model::AHeader, Seq<model::APromise>)>,
) -> Seq<model::APromise>
    decreases segments.len(),
{
    if segments.len() == 0 {
        Seq::empty()
    } else {
        segments[0].1 + promise_document_rows(segments.drop_first())
    }
}

pub open spec fn schedule_document_rows(
    segments: Seq<(model::AHeader, Seq<model::ASchedule>)>,
) -> Seq<model::ASchedule>
    decreases segments.len(),
{
    if segments.len() == 0 {
        Seq::empty()
    } else {
        segments[0].1 + schedule_document_rows(segments.drop_first())
    }
}

pub open spec fn promise_document_last_header(
    segments: Seq<(model::AHeader, Seq<model::APromise>)>,
) -> Option<model::AHeader> {
    if segments.len() == 0 {
        None
    } else {
        Some(segments.last().0)
    }
}

pub open spec fn schedule_document_last_header(
    segments: Seq<(model::AHeader, Seq<model::ASchedule>)>,
) -> Option<model::AHeader> {
    if segments.len() == 0 {
        None
    } else {
        Some(segments.last().0)
    }
}

pub open spec fn promise_document_wf(
    segments: Seq<(model::AHeader, Seq<model::APromise>)>,
) -> bool {
    &&& forall|i: int| 0 <= i < segments.len()
        ==> promise_segment_wf(
            #[trigger] segments[i].0, segments[i].1,
        )
    &&& promise_document_bytes(segments).len() <= usize::MAX
}

pub open spec fn schedule_document_wf(
    segments: Seq<(model::AHeader, Seq<model::ASchedule>)>,
) -> bool {
    &&& forall|i: int| 0 <= i < segments.len()
        ==> schedule_segment_wf(
            #[trigger] segments[i].0, segments[i].1,
        )
    &&& schedule_document_bytes(segments).len() <= usize::MAX
}

/// Appending a segment is literal byte concatenation; no previous length is
/// rewritten.
#[verifier::rlimit(20)]
pub proof fn lemma_promise_document_append_bytes(
    segments: Seq<(model::AHeader, Seq<model::APromise>)>,
    segment: (model::AHeader, Seq<model::APromise>),
)
    ensures
        promise_document_bytes(segments.push(segment))
            == promise_document_bytes(segments)
                + promise_segment_bytes(segment.0, segment.1),
    decreases segments.len(),
{
    reveal_with_fuel(promise_document_bytes, 2);
    if segments.len() == 0 {
        assert(segments.push(segment) == seq![segment]);
        assert(promise_document_bytes(segments) == Seq::<u8>::empty());
        assert(seq![segment][0] == segment);
        assert(seq![segment].drop_first()
            == Seq::<(model::AHeader, Seq<model::APromise>)>::empty());
        assert(promise_segment_bytes(segment.0, segment.1)
                + Seq::<u8>::empty()
            == promise_segment_bytes(segment.0, segment.1));
        assert(promise_document_bytes(segments.push(segment))
            == promise_segment_bytes(segment.0, segment.1));
    } else {
        let first_bytes =
            promise_segment_bytes(segments[0].0, segments[0].1);
        let rest = segments.drop_first();
        assert(segments.push(segment)[0] == segments[0]);
        assert(segments.push(segment).drop_first()
            == rest.push(segment));
        lemma_promise_document_append_bytes(
            rest, segment,
        );
        assert(promise_document_bytes(segments.push(segment))
            == first_bytes
                + promise_document_bytes(rest.push(segment)));
        assert(promise_document_bytes(segments)
            == first_bytes + promise_document_bytes(rest));
        assert(first_bytes
                + (promise_document_bytes(rest)
                    + promise_segment_bytes(segment.0, segment.1))
            == (first_bytes + promise_document_bytes(rest))
                + promise_segment_bytes(segment.0, segment.1));
    }
}

#[verifier::rlimit(20)]
pub proof fn lemma_schedule_document_append_bytes(
    segments: Seq<(model::AHeader, Seq<model::ASchedule>)>,
    segment: (model::AHeader, Seq<model::ASchedule>),
)
    ensures
        schedule_document_bytes(segments.push(segment))
            == schedule_document_bytes(segments)
                + schedule_segment_bytes(segment.0, segment.1),
    decreases segments.len(),
{
    reveal_with_fuel(schedule_document_bytes, 2);
    if segments.len() == 0 {
        assert(segments.push(segment) == seq![segment]);
        assert(schedule_document_bytes(segments) == Seq::<u8>::empty());
        assert(seq![segment][0] == segment);
        assert(seq![segment].drop_first()
            == Seq::<(model::AHeader, Seq<model::ASchedule>)>::empty());
        assert(schedule_segment_bytes(segment.0, segment.1)
                + Seq::<u8>::empty()
            == schedule_segment_bytes(segment.0, segment.1));
        assert(schedule_document_bytes(segments.push(segment))
            == schedule_segment_bytes(segment.0, segment.1));
    } else {
        let first_bytes =
            schedule_segment_bytes(segments[0].0, segments[0].1);
        let rest = segments.drop_first();
        assert(segments.push(segment)[0] == segments[0]);
        assert(segments.push(segment).drop_first()
            == rest.push(segment));
        lemma_schedule_document_append_bytes(
            rest, segment,
        );
        assert(schedule_document_bytes(segments.push(segment))
            == first_bytes
                + schedule_document_bytes(rest.push(segment)));
        assert(schedule_document_bytes(segments)
            == first_bytes + schedule_document_bytes(rest));
        assert(first_bytes
                + (schedule_document_bytes(rest)
                    + schedule_segment_bytes(segment.0, segment.1))
            == (first_bytes + schedule_document_bytes(rest))
                + schedule_segment_bytes(segment.0, segment.1));
    }
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(80)]
pub proof fn lemma_promise_document_raw_round_trip(
    segments: Seq<(model::AHeader, Seq<model::APromise>)>,
)
    requires promise_document_wf(segments),
    ensures
        decode_promise_document_raw_spec(promise_document_bytes(segments))
            == Some((
                promise_document_last_header(segments),
                promise_document_rows(segments),
            )),
    decreases segments.len(),
{
    if segments.len() == 0 {
        reveal_with_fuel(decode_promise_document_raw_spec, 1);
    } else {
        let first = segments[0];
        let rest = segments.drop_first();
        lemma_promise_segment_round_trip(first.0, first.1);
        lemma_promise_document_raw_round_trip(rest);
        lemma_split_promise_segment(
            first.0,
            first.1,
            promise_document_bytes(rest),
        );
        lemma_decode_promise_document_cons(
            promise_document_bytes(segments),
            promise_segment_bytes(first.0, first.1),
            promise_document_bytes(rest),
            first.0,
            first.1,
            promise_document_last_header(rest),
            promise_document_rows(rest),
        );
    }
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(80)]
pub proof fn lemma_schedule_document_raw_round_trip(
    segments: Seq<(model::AHeader, Seq<model::ASchedule>)>,
)
    requires schedule_document_wf(segments),
    ensures
        decode_schedule_document_raw_spec(schedule_document_bytes(segments))
            == Some((
                schedule_document_last_header(segments),
                schedule_document_rows(segments),
            )),
    decreases segments.len(),
{
    if segments.len() == 0 {
        reveal_with_fuel(decode_schedule_document_raw_spec, 1);
    } else {
        let first = segments[0];
        let rest = segments.drop_first();
        lemma_schedule_segment_round_trip(first.0, first.1);
        lemma_schedule_document_raw_round_trip(rest);
        lemma_split_schedule_segment(
            first.0,
            first.1,
            schedule_document_bytes(rest),
        );
        lemma_decode_schedule_document_cons(
            schedule_document_bytes(segments),
            schedule_segment_bytes(first.0, first.1),
            schedule_document_bytes(rest),
            first.0,
            first.1,
            schedule_document_last_header(rest),
            schedule_document_rows(rest),
        );
    }
}

pub proof fn lemma_promise_document_round_trip(
    segments: Seq<(model::AHeader, Seq<model::APromise>)>,
)
    requires promise_document_wf(segments),
    ensures
        decode_promise_document_spec(promise_document_bytes(segments))
            == Some((
                promise_document_last_header(segments),
                fold_promises(promise_document_rows(segments)),
            )),
{
    lemma_promise_document_raw_round_trip(segments);
    reveal(decode_promise_document_spec);
}

pub proof fn lemma_schedule_document_round_trip(
    segments: Seq<(model::AHeader, Seq<model::ASchedule>)>,
)
    requires schedule_document_wf(segments),
    ensures
        decode_schedule_document_spec(schedule_document_bytes(segments))
            == Some((
                schedule_document_last_header(segments),
                fold_schedules(schedule_document_rows(segments)),
            )),
{
    lemma_schedule_document_raw_round_trip(segments);
    reveal(decode_schedule_document_spec);
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(200)]
pub proof fn lemma_single_promise_document_raw_round_trip(
    header: model::AHeader,
    rows: Seq<model::APromise>,
)
    requires promise_segment_wf(header, rows),
    ensures
        decode_promise_document_raw_spec(
            promise_segment_bytes(header, rows),
        ) == Some((Some(header), rows)),
{
    lemma_promise_segment_round_trip(header, rows);
    lemma_split_promise_segment(header, rows, Seq::empty());
    assert(split_frame_spec(promise_segment_bytes(header, rows))
        == Some((
            promise_segment_bytes(header, rows),
            Seq::empty(),
        )));
    assert(decode_promise_segment_spec(
        promise_segment_bytes(header, rows),
    ) == Some((header, rows)));
    assert(decode_promise_document_raw_spec(Seq::empty())
        == Some((None, Seq::empty())));
    lemma_decode_promise_document_cons(
        promise_segment_bytes(header, rows),
        promise_segment_bytes(header, rows),
        Seq::empty(),
        header,
        rows,
        None,
        Seq::empty(),
    );
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(200)]
pub proof fn lemma_single_schedule_document_raw_round_trip(
    header: model::AHeader,
    rows: Seq<model::ASchedule>,
)
    requires schedule_segment_wf(header, rows),
    ensures
        decode_schedule_document_raw_spec(
            schedule_segment_bytes(header, rows),
        ) == Some((Some(header), rows)),
{
    lemma_schedule_segment_round_trip(header, rows);
    lemma_split_schedule_segment(header, rows, Seq::empty());
    assert(split_frame_spec(schedule_segment_bytes(header, rows))
        == Some((
            schedule_segment_bytes(header, rows),
            Seq::empty(),
        )));
    assert(decode_schedule_segment_spec(
        schedule_segment_bytes(header, rows),
    ) == Some((header, rows)));
    assert(decode_schedule_document_raw_spec(Seq::empty())
        == Some((None, Seq::empty())));
    lemma_decode_schedule_document_cons(
        schedule_segment_bytes(header, rows),
        schedule_segment_bytes(header, rows),
        Seq::empty(),
        header,
        rows,
        None,
        Seq::empty(),
    );
}

pub proof fn lemma_single_promise_document_round_trip(
    header: model::AHeader,
    rows: Seq<model::APromise>,
)
    requires promise_segment_wf(header, rows),
    ensures
        decode_promise_document_spec(
            promise_segment_bytes(header, rows),
        ) == Some((Some(header), fold_promises(rows))),
{
    lemma_single_promise_document_raw_round_trip(header, rows);
    reveal(decode_promise_document_spec);
}

pub proof fn lemma_single_schedule_document_round_trip(
    header: model::AHeader,
    rows: Seq<model::ASchedule>,
)
    requires schedule_segment_wf(header, rows),
    ensures
        decode_schedule_document_spec(
            schedule_segment_bytes(header, rows),
        ) == Some((Some(header), fold_schedules(rows))),
{
    lemma_single_schedule_document_raw_round_trip(header, rows);
    reveal(decode_schedule_document_spec);
}

/// Rewriting a Promise document as one Header plus its folded rows preserves
/// its last-row-wins state.
pub proof fn lemma_promise_compaction(
    header: model::AHeader,
    rows: Seq<model::APromise>,
)
    requires promise_segment_wf(header, fold_promises(rows)),
    ensures
        decode_promise_document_spec(
            promise_segment_bytes(header, fold_promises(rows)),
        ) == Some((Some(header), fold_promises(rows))),
{
    lemma_single_promise_document_round_trip(
        header, fold_promises(rows),
    );
    lemma_fold_promises_idempotent(rows);
}

/// Rewriting a Schedule document as one Header plus its folded rows preserves
/// its last-row-wins state.
pub proof fn lemma_schedule_compaction(
    header: model::AHeader,
    rows: Seq<model::ASchedule>,
)
    requires schedule_segment_wf(header, fold_schedules(rows)),
    ensures
        decode_schedule_document_spec(
            schedule_segment_bytes(header, fold_schedules(rows)),
        ) == Some((Some(header), fold_schedules(rows))),
{
    lemma_single_schedule_document_round_trip(
        header, fold_schedules(rows),
    );
    lemma_fold_schedules_idempotent(rows);
}

pub open spec fn compact_promise_document_spec(
    bytes: Seq<u8>,
    header: model::AHeader,
) -> Option<Seq<u8>> {
    match decode_promise_document_spec(bytes) {
        Some((_, rows)) => Some(promise_segment_bytes(header, rows)),
        None => None,
    }
}

pub open spec fn compact_schedule_document_spec(
    bytes: Seq<u8>,
    header: model::AHeader,
) -> Option<Seq<u8>> {
    match decode_schedule_document_spec(bytes) {
        Some((_, rows)) => Some(schedule_segment_bytes(header, rows)),
        None => None,
    }
}

// -------------------------------------------------------------------------
// Executable whole-document decoders
// -------------------------------------------------------------------------

fn prepend_promises(
    mut prefix: Vec<model::Promise>,
    suffix: Vec<model::Promise>,
    Ghost(prefix_view): Ghost<Seq<model::APromise>>,
    Ghost(suffix_view): Ghost<Seq<model::APromise>>,
) -> (result: Vec<model::Promise>)
    requires
        prefix.deep_view() == prefix_view,
        suffix.deep_view() == suffix_view,
    ensures
        result.deep_view() == prefix_view + suffix_view,
    decreases prefix.len(),
{
    if prefix.len() == 0 {
        assert(prefix_view == Seq::<model::APromise>::empty());
        suffix
    } else {
        let ghost original = prefix.deep_view();
        let last = prefix.pop().unwrap();
        let ghost last_view = last@;
        let ghost rest_view = prefix.deep_view();
        assert(rest_view == original.drop_last());
        assert(last_view == original.last());
        let position = prefix.len();
        let mut result = prepend_promises(
            prefix,
            suffix,
            Ghost(rest_view),
            Ghost(suffix_view),
        );
        let ghost before = result.deep_view();
        assert(before == rest_view + suffix_view);
        result.insert(position, last);
        assert(result.deep_view() =~=
            before.subrange(0, position as int)
                + seq![last_view]
                + before.subrange(
                    position as int, before.len() as int,
                ));
        assert(before.subrange(0, position as int) == rest_view);
        assert(before.subrange(
            position as int, before.len() as int,
        ) == suffix_view);
        assert(original == rest_view.push(last_view));
        result
    }
}

fn prepend_schedules(
    mut prefix: Vec<model::Schedule>,
    suffix: Vec<model::Schedule>,
    Ghost(prefix_view): Ghost<Seq<model::ASchedule>>,
    Ghost(suffix_view): Ghost<Seq<model::ASchedule>>,
) -> (result: Vec<model::Schedule>)
    requires
        prefix.deep_view() == prefix_view,
        suffix.deep_view() == suffix_view,
    ensures
        result.deep_view() == prefix_view + suffix_view,
    decreases prefix.len(),
{
    if prefix.len() == 0 {
        assert(prefix_view == Seq::<model::ASchedule>::empty());
        suffix
    } else {
        let ghost original = prefix.deep_view();
        let last = prefix.pop().unwrap();
        let ghost last_view = last@;
        let ghost rest_view = prefix.deep_view();
        assert(rest_view == original.drop_last());
        assert(last_view == original.last());
        let position = prefix.len();
        let mut result = prepend_schedules(
            prefix,
            suffix,
            Ghost(rest_view),
            Ghost(suffix_view),
        );
        let ghost before = result.deep_view();
        assert(before == rest_view + suffix_view);
        result.insert(position, last);
        assert(result.deep_view() =~=
            before.subrange(0, position as int)
                + seq![last_view]
                + before.subrange(
                    position as int, before.len() as int,
                ));
        assert(before.subrange(0, position as int) == rest_view);
        assert(before.subrange(
            position as int, before.len() as int,
        ) == suffix_view);
        assert(original == rest_view.push(last_view));
        result
    }
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(400)]
fn decode_promise_document_raw_model(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(
    Option<model::Header>,
    Vec<model::Promise>,
)>)
    ensures
        match result {
            Ok((header, rows)) => {
                &&& decode_promise_document_raw_spec(bytes@)
                    == Some((header.deep_view(), rows.deep_view()))
                &&& forall|i: int| 0 <= i < rows.len()
                    ==> crate::bridge::promise_text_wf(rows[i]@)
            }
            Err(_) => decode_promise_document_raw_spec(bytes@) is None,
        },
    decreases bytes.len(),
{
    reveal_with_fuel(decode_promise_document_raw_spec, 2);
    if bytes.len() == 0 {
        return Ok((None, Vec::new()));
    }
    let (frame, rest) = match split_frame(bytes) {
        None => return Err("malformed or truncated document segment"),
        Some(parts) => parts,
    };
    assert(rest.len() < bytes.len());
    let (header, rows) = match decode_promise_segment_model(&frame) {
        Err(error) => return Err(error),
        Ok(segment) => segment,
    };
    let ghost header_view = header@;
    let ghost row_views = rows.deep_view();
    let (tail_header, tail_rows) =
        match decode_promise_document_raw_model(&rest) {
            Err(error) => return Err(error),
            Ok(document) => document,
        };
    let ghost tail_header_view = tail_header.deep_view();
    let ghost tail_row_views = tail_rows.deep_view();
    let rows = prepend_promises(
        rows,
        tail_rows,
        Ghost(row_views),
        Ghost(tail_row_views),
    );
    let final_header = match tail_header {
        Some(header) => Some(header),
        None => Some(header),
    };
    assert(decode_promise_document_raw_spec(bytes@)
        == Some((final_header.deep_view(), rows.deep_view())));
    assert(rows.deep_view() == row_views + tail_row_views);
    assert(rows.deep_view().len()
        == row_views.len() + tail_row_views.len());
    assert forall|i: int| 0 <= i < rows.len()
        implies crate::bridge::promise_text_wf(rows[i]@) by {
        assert(i < rows.deep_view().len());
        assert(rows.deep_view()[i]
            == (row_views + tail_row_views)[i]);
        if i < row_views.len() {
            assert(rows.deep_view()[i] == row_views[i]);
        } else {
            assert(row_views.len() <= i);
            assert(0 <= i - row_views.len() < tail_row_views.len());
            assert((row_views + tail_row_views)[i]
                == tail_row_views[i - row_views.len()]);
            assert(rows.deep_view()[i]
                == tail_row_views[i - row_views.len()]);
        }
    }
    Ok((final_header, rows))
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(200)]
fn decode_schedule_document_raw_model(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(
    Option<model::Header>,
    Vec<model::Schedule>,
)>)
    ensures
        match result {
            Ok((header, rows)) => {
                &&& decode_schedule_document_raw_spec(bytes@)
                    == Some((header.deep_view(), rows.deep_view()))
                &&& forall|i: int| 0 <= i < rows.len()
                    ==> crate::bridge::schedule_text_wf(rows[i]@)
            }
            Err(_) => decode_schedule_document_raw_spec(bytes@) is None,
        },
    decreases bytes.len(),
{
    reveal_with_fuel(decode_schedule_document_raw_spec, 2);
    if bytes.len() == 0 {
        return Ok((None, Vec::new()));
    }
    let (frame, rest) = match split_frame(bytes) {
        None => return Err("malformed or truncated document segment"),
        Some(parts) => parts,
    };
    assert(rest.len() < bytes.len());
    let (header, rows) = match decode_schedule_segment_model(&frame) {
        Err(error) => return Err(error),
        Ok(segment) => segment,
    };
    let ghost header_view = header@;
    let ghost row_views = rows.deep_view();
    let (tail_header, tail_rows) =
        match decode_schedule_document_raw_model(&rest) {
            Err(error) => return Err(error),
            Ok(document) => document,
        };
    let ghost tail_header_view = tail_header.deep_view();
    let ghost tail_row_views = tail_rows.deep_view();
    let rows = prepend_schedules(
        rows,
        tail_rows,
        Ghost(row_views),
        Ghost(tail_row_views),
    );
    let final_header = match tail_header {
        Some(header) => Some(header),
        None => Some(header),
    };
    assert(decode_schedule_document_raw_spec(bytes@)
        == Some((final_header.deep_view(), rows.deep_view())));
    assert(rows.deep_view() == row_views + tail_row_views);
    assert(rows.deep_view().len()
        == row_views.len() + tail_row_views.len());
    assert forall|i: int| 0 <= i < rows.len()
        implies crate::bridge::schedule_text_wf(rows[i]@) by {
        assert(i < rows.deep_view().len());
        assert(rows.deep_view()[i]
            == (row_views + tail_row_views)[i]);
        if i < row_views.len() {
            assert(rows.deep_view()[i] == row_views[i]);
        } else {
            assert(row_views.len() <= i);
            assert(0 <= i - row_views.len() < tail_row_views.len());
            assert((row_views + tail_row_views)[i]
                == tail_row_views[i - row_views.len()]);
            assert(rows.deep_view()[i]
                == tail_row_views[i - row_views.len()]);
        }
    }
    Ok((final_header, rows))
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(40)]
fn decode_promise_document_model(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(
    Option<model::Header>,
    Vec<model::Promise>,
)>)
    ensures
        match result {
            Ok((header, rows)) => {
                &&& decode_promise_document_spec(bytes@)
                    == Some((header.deep_view(), rows.deep_view()))
                &&& forall|i: int| 0 <= i < rows.len()
                    ==> crate::bridge::promise_text_wf(rows[i]@)
            }
            Err(_) => decode_promise_document_spec(bytes@) is None,
        },
{
    reveal(decode_promise_document_spec);
    let (header, rows) =
        match decode_promise_document_raw_model(bytes) {
            Err(error) => return Err(error),
            Ok(document) => document,
        };
    let ghost header_view = header.deep_view();
    let ghost raw = rows.deep_view();
    assert(decode_promise_document_raw_spec(bytes@)
        == Some((header_view, raw)));
    let rows = fold_promises_exec(rows, Ghost(raw));
    assert(rows.deep_view() == fold_promises(raw));
    assert(decode_promise_document_spec(bytes@)
        == Some((header_view, rows.deep_view())));
    Ok((header, rows))
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(40)]
fn decode_schedule_document_model(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(
    Option<model::Header>,
    Vec<model::Schedule>,
)>)
    ensures
        match result {
            Ok((header, rows)) => {
                &&& decode_schedule_document_spec(bytes@)
                    == Some((header.deep_view(), rows.deep_view()))
                &&& forall|i: int| 0 <= i < rows.len()
                    ==> crate::bridge::schedule_text_wf(rows[i]@)
            }
            Err(_) => decode_schedule_document_spec(bytes@) is None,
        },
{
    reveal(decode_schedule_document_spec);
    let (header, rows) =
        match decode_schedule_document_raw_model(bytes) {
            Err(error) => return Err(error),
            Ok(document) => document,
        };
    let ghost header_view = header.deep_view();
    let ghost raw = rows.deep_view();
    assert(decode_schedule_document_raw_spec(bytes@)
        == Some((header_view, raw)));
    let rows = fold_schedules_exec(rows, Ghost(raw));
    assert(rows.deep_view() == fold_schedules(raw));
    assert(decode_schedule_document_spec(bytes@)
        == Some((header_view, rows.deep_view())));
    Ok((header, rows))
}

// -------------------------------------------------------------------------
// Verified kernel-facing runtime API
// -------------------------------------------------------------------------

pub open spec fn promises_from_kernel(
    rows: Seq<echod_kernel::APromise>,
) -> Seq<model::APromise> {
    rows.map_values(|row: echod_kernel::APromise| {
        crate::bridge::promise_from_kernel(row)
    })
}

pub open spec fn schedules_from_kernel(
    rows: Seq<echod_kernel::ASchedule>,
) -> Seq<model::ASchedule> {
    rows.map_values(|row: echod_kernel::ASchedule| {
        crate::bridge::schedule_from_kernel(row)
    })
}

pub open spec fn promises_to_kernel(
    rows: Seq<model::APromise>,
) -> Seq<echod_kernel::APromise> {
    rows.map_values(|row: model::APromise| {
        crate::bridge::promise_to_kernel(row)
    })
}

pub open spec fn schedules_to_kernel(
    rows: Seq<model::ASchedule>,
) -> Seq<echod_kernel::ASchedule> {
    rows.map_values(|row: model::ASchedule| {
        crate::bridge::schedule_to_kernel(row)
    })
}

proof fn lemma_promises_from_kernel_push(
    rows: Seq<echod_kernel::APromise>,
    row: echod_kernel::APromise,
)
    ensures
        promises_from_kernel(rows.push(row))
            == promises_from_kernel(rows).push(
                crate::bridge::promise_from_kernel(row),
            ),
{
}

proof fn lemma_schedules_from_kernel_push(
    rows: Seq<echod_kernel::ASchedule>,
    row: echod_kernel::ASchedule,
)
    ensures
        schedules_from_kernel(rows.push(row))
            == schedules_from_kernel(rows).push(
                crate::bridge::schedule_from_kernel(row),
            ),
{
}

proof fn lemma_promises_to_kernel_push(
    rows: Seq<model::APromise>,
    row: model::APromise,
)
    ensures
        promises_to_kernel(rows.push(row))
            == promises_to_kernel(rows).push(
                crate::bridge::promise_to_kernel(row),
            ),
{
}

proof fn lemma_schedules_to_kernel_push(
    rows: Seq<model::ASchedule>,
    row: model::ASchedule,
)
    ensures
        schedules_to_kernel(rows.push(row))
            == schedules_to_kernel(rows).push(
                crate::bridge::schedule_to_kernel(row),
            ),
{
}

pub proof fn lemma_promises_model_kernel_round_trip(
    rows: Seq<model::APromise>,
)
    requires
        forall|i: int| 0 <= i < rows.len()
            ==> crate::bridge::promise_text_wf(#[trigger] rows[i]),
    ensures
        promises_from_kernel(promises_to_kernel(rows)) == rows,
{
    assert forall|i: int| 0 <= i < rows.len()
        implies promises_from_kernel(promises_to_kernel(rows))[i]
            == rows[i] by {
        crate::bridge::lemma_promise_model_round_trip(rows[i]);
    }
}

pub proof fn lemma_schedules_model_kernel_round_trip(
    rows: Seq<model::ASchedule>,
)
    requires
        forall|i: int| 0 <= i < rows.len()
            ==> crate::bridge::schedule_text_wf(#[trigger] rows[i]),
    ensures
        schedules_from_kernel(schedules_to_kernel(rows)) == rows,
{
    assert forall|i: int| 0 <= i < rows.len()
        implies schedules_from_kernel(schedules_to_kernel(rows))[i]
            == rows[i] by {
        crate::bridge::lemma_schedule_model_round_trip(rows[i]);
    }
}

fn model_promises(
    rows: &Vec<echod_kernel::Promise>,
) -> (result: Vec<model::Promise>)
    ensures result.deep_view() == promises_from_kernel(rows.deep_view()),
{
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < rows.len()
        invariant
            i <= rows.len(),
            result.deep_view()
                == promises_from_kernel(
                    rows.deep_view().subrange(0, i as int),
                ),
        decreases rows.len() - i,
    {
        let ghost prefix =
            rows.deep_view().subrange(0, i as int);
        let ghost row = rows.deep_view()[i as int];
        let value = crate::bridge::promise_model(&rows[i]);
        let ghost value_view = value@;
        assert(value_view == crate::bridge::promise_from_kernel(row));
        proof {
            lemma_subrange_step(rows.deep_view(), i as int);
            lemma_promises_from_kernel_push(prefix, row);
        }
        result.push(value);
        assert(result.deep_view() =~= promises_from_kernel(prefix).push(
            value_view,
        ));
        i += 1;
    }
    assert(rows.deep_view().subrange(0, rows.len() as int)
        == rows.deep_view());
    result
}

fn model_schedules(
    rows: &Vec<echod_kernel::Schedule>,
) -> (result: Vec<model::Schedule>)
    ensures result.deep_view() == schedules_from_kernel(rows.deep_view()),
{
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < rows.len()
        invariant
            i <= rows.len(),
            result.deep_view()
                == schedules_from_kernel(
                    rows.deep_view().subrange(0, i as int),
                ),
        decreases rows.len() - i,
    {
        let ghost prefix =
            rows.deep_view().subrange(0, i as int);
        let ghost row = rows.deep_view()[i as int];
        let value = crate::bridge::schedule_model(&rows[i]);
        let ghost value_view = value@;
        assert(value_view == crate::bridge::schedule_from_kernel(row));
        proof {
            lemma_subrange_step(rows.deep_view(), i as int);
            lemma_schedules_from_kernel_push(prefix, row);
        }
        result.push(value);
        assert(result.deep_view() =~= schedules_from_kernel(prefix).push(
            value_view,
        ));
        i += 1;
    }
    assert(rows.deep_view().subrange(0, rows.len() as int)
        == rows.deep_view());
    result
}

fn kernel_promises(
    mut rows: Vec<model::Promise>,
    Ghost(input): Ghost<Seq<model::APromise>>,
) -> (result: Vec<echod_kernel::Promise>)
    requires
        rows.deep_view() == input,
        forall|i: int| 0 <= i < input.len()
            ==> crate::bridge::promise_text_wf(#[trigger] input[i]),
    ensures result.deep_view() == promises_to_kernel(input),
    decreases rows.len(),
{
    if rows.len() == 0 {
        Vec::new()
    } else {
        let ghost original = rows.deep_view();
        let last = rows.pop().unwrap();
        let ghost last_view = last@;
        let ghost prefix = rows.deep_view();
        assert(prefix == original.drop_last());
        assert(last_view == original.last());
        let mut result = kernel_promises(rows, Ghost(prefix));
        let value = crate::bridge::kernel_promise(last);
        let ghost value_view = value@;
        assert(value_view == crate::bridge::promise_to_kernel(last_view));
        proof {
            lemma_promises_to_kernel_push(prefix, last_view);
        }
        result.push(value);
        assert(result.deep_view() =~= promises_to_kernel(prefix).push(
            value_view,
        ));
        result
    }
}

fn kernel_schedules(
    mut rows: Vec<model::Schedule>,
    Ghost(input): Ghost<Seq<model::ASchedule>>,
) -> (result: Vec<echod_kernel::Schedule>)
    requires
        rows.deep_view() == input,
        forall|i: int| 0 <= i < input.len()
            ==> crate::bridge::schedule_text_wf(#[trigger] input[i]),
    ensures result.deep_view() == schedules_to_kernel(input),
    decreases rows.len(),
{
    if rows.len() == 0 {
        Vec::new()
    } else {
        let ghost original = rows.deep_view();
        let last = rows.pop().unwrap();
        let ghost last_view = last@;
        let ghost prefix = rows.deep_view();
        assert(prefix == original.drop_last());
        assert(last_view == original.last());
        let mut result = kernel_schedules(rows, Ghost(prefix));
        let value = crate::bridge::kernel_schedule(last);
        let ghost value_view = value@;
        assert(value_view == crate::bridge::schedule_to_kernel(last_view));
        proof {
            lemma_schedules_to_kernel_push(prefix, last_view);
        }
        result.push(value);
        assert(result.deep_view() =~= schedules_to_kernel(prefix).push(
            value_view,
        ));
        result
    }
}

pub fn encode_promise_segment(
    header: &model::Header,
    rows: &Vec<echod_kernel::Promise>,
) -> (result: DocumentResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == promise_segment_bytes(
            header@, promises_from_kernel(rows.deep_view()),
        ),
        result is Ok
            && promise_segment_wf(
                header@, promises_from_kernel(rows.deep_view()),
            )
            ==> decode_promise_segment_spec(result->Ok_0@)
                == Some((
                    header@, promises_from_kernel(rows.deep_view()),
                )),
{
    let rows = model_promises(rows);
    encode_promise_segment_model(header, &rows)
}

pub fn encode_schedule_segment(
    header: &model::Header,
    rows: &Vec<echod_kernel::Schedule>,
) -> (result: DocumentResult<Vec<u8>>)
    ensures
        result is Ok ==> result->Ok_0@ == schedule_segment_bytes(
            header@, schedules_from_kernel(rows.deep_view()),
        ),
        result is Ok
            && schedule_segment_wf(
                header@, schedules_from_kernel(rows.deep_view()),
            )
            ==> decode_schedule_segment_spec(result->Ok_0@)
                == Some((
                    header@, schedules_from_kernel(rows.deep_view()),
                )),
{
    let rows = model_schedules(rows);
    encode_schedule_segment_model(header, &rows)
}

pub fn decode_promise_segment(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(
    model::Header,
    Vec<echod_kernel::Promise>,
)>)
    ensures
        match result {
            Ok((header, rows)) => decode_promise_segment_spec(bytes@)
                == Some((
                    header@, promises_from_kernel(rows.deep_view()),
                )),
            Err(_) => decode_promise_segment_spec(bytes@) is None,
        },
{
    let (header, rows) = match decode_promise_segment_model(bytes) {
        Err(error) => return Err(error),
        Ok(segment) => segment,
    };
    let ghost model_rows = rows.deep_view();
    let rows = kernel_promises(rows, Ghost(model_rows));
    proof {
        lemma_promises_model_kernel_round_trip(model_rows);
    }
    assert(promises_from_kernel(rows.deep_view()) == model_rows);
    Ok((header, rows))
}

pub fn decode_schedule_segment(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(
    model::Header,
    Vec<echod_kernel::Schedule>,
)>)
    ensures
        match result {
            Ok((header, rows)) => decode_schedule_segment_spec(bytes@)
                == Some((
                    header@, schedules_from_kernel(rows.deep_view()),
                )),
            Err(_) => decode_schedule_segment_spec(bytes@) is None,
        },
{
    let (header, rows) = match decode_schedule_segment_model(bytes) {
        Err(error) => return Err(error),
        Ok(segment) => segment,
    };
    let ghost model_rows = rows.deep_view();
    let rows = kernel_schedules(rows, Ghost(model_rows));
    proof {
        lemma_schedules_model_kernel_round_trip(model_rows);
    }
    assert(schedules_from_kernel(rows.deep_view()) == model_rows);
    Ok((header, rows))
}

pub fn decode_promise_document(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(
    Option<model::Header>,
    Vec<echod_kernel::Promise>,
)>)
    ensures
        match result {
            Ok((header, rows)) => decode_promise_document_spec(bytes@)
                == Some((
                    header.deep_view(),
                    promises_from_kernel(rows.deep_view()),
                )),
            Err(_) => decode_promise_document_spec(bytes@) is None,
        },
{
    let (header, rows) = match decode_promise_document_model(bytes) {
        Err(error) => return Err(error),
        Ok(document) => document,
    };
    let ghost model_rows = rows.deep_view();
    let rows = kernel_promises(rows, Ghost(model_rows));
    proof {
        lemma_promises_model_kernel_round_trip(model_rows);
    }
    assert(promises_from_kernel(rows.deep_view()) == model_rows);
    Ok((header, rows))
}

pub fn decode_schedule_document(
    bytes: &Vec<u8>,
) -> (result: DocumentResult<(
    Option<model::Header>,
    Vec<echod_kernel::Schedule>,
)>)
    ensures
        match result {
            Ok((header, rows)) => decode_schedule_document_spec(bytes@)
                == Some((
                    header.deep_view(),
                    schedules_from_kernel(rows.deep_view()),
                )),
            Err(_) => decode_schedule_document_spec(bytes@) is None,
        },
{
    let (header, rows) = match decode_schedule_document_model(bytes) {
        Err(error) => return Err(error),
        Ok(document) => document,
    };
    let ghost model_rows = rows.deep_view();
    let rows = kernel_schedules(rows, Ghost(model_rows));
    proof {
        lemma_schedules_model_kernel_round_trip(model_rows);
    }
    assert(schedules_from_kernel(rows.deep_view()) == model_rows);
    Ok((header, rows))
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(40)]
pub fn compact_promise_document(
    bytes: &Vec<u8>,
    header: &model::Header,
) -> (result: DocumentResult<Vec<u8>>)
    ensures
        result is Ok ==> compact_promise_document_spec(bytes@, header@)
            == Some(result->Ok_0@),
{
    let (old_header, rows) =
        match decode_promise_document_model(bytes) {
            Err(error) => return Err(error),
            Ok(document) => document,
        };
    let result = encode_promise_segment_model(header, &rows);
    result
}

#[verifier(spinoff_prover)]
#[verifier::rlimit(40)]
pub fn compact_schedule_document(
    bytes: &Vec<u8>,
    header: &model::Header,
) -> (result: DocumentResult<Vec<u8>>)
    ensures
        result is Ok ==> compact_schedule_document_spec(bytes@, header@)
            == Some(result->Ok_0@),
{
    let (old_header, rows) =
        match decode_schedule_document_model(bytes) {
            Err(error) => return Err(error),
            Ok(document) => document,
        };
    let result = encode_schedule_segment_model(header, &rows);
    result
}

} // verus!
