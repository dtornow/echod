//! Records are envelopes whose payload is a sequence of framed field bytes.

use vstd::prelude::*;

use crate::frame::{decode_envelope, encode_envelope};
#[cfg(verus_keep_ghost)]
use crate::frame::{decode_envelope_spec, envelope_bytes, lemma_envelope_round_trip};
#[cfg(verus_keep_ghost)]
use crate::primitives::{
    blob_sequence_bytes, decode_blob_sequence_spec, lemma_blob_sequence_round_trip,
    MAX_SEQUENCE_ITEMS,
};
use crate::primitives::{decode_blob_sequence, encode_blob_sequence};

verus! {

pub open spec fn record_bytes(kind: u8, fields: Seq<Seq<u8>>) -> Seq<u8> {
    envelope_bytes(kind, blob_sequence_bytes(fields))
}

pub open spec fn decode_record_spec(
    bytes: Seq<u8>,
    expected_kind: u8,
) -> Option<Seq<Seq<u8>>> {
    match decode_envelope_spec(bytes, expected_kind) {
        None => None,
        Some(payload) => decode_blob_sequence_spec(payload),
    }
}

pub fn encode_record(
    kind: u8,
    fields: &Vec<Vec<u8>>,
) -> (r: Option<Vec<u8>>)
    ensures
        r is Some ==> r->Some_0@ == record_bytes(kind, fields.deep_view()),
{
    match encode_blob_sequence(fields) {
        None => None,
        Some(payload) => encode_envelope(kind, &payload),
    }
}

pub fn decode_record(
    bytes: &Vec<u8>,
    expected_kind: u8,
) -> (r: Option<Vec<Vec<u8>>>)
    ensures
        r.deep_view() == decode_record_spec(bytes@, expected_kind),
{
    match decode_envelope(bytes, expected_kind) {
        None => {
            assert(decode_envelope_spec(bytes@, expected_kind) is None);
            None
        }
        Some(payload) => {
            assert(decode_envelope_spec(bytes@, expected_kind)
                == Some(payload@));
            decode_blob_sequence(&payload)
        }
    }
}

pub proof fn lemma_record_round_trip(kind: u8, fields: Seq<Seq<u8>>)
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
    lemma_blob_sequence_round_trip(fields);
    lemma_envelope_round_trip(kind, blob_sequence_bytes(fields));
}

} // verus!
