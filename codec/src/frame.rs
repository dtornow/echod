//! Top-level magic, format version, kind, and payload framing.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::primitives::{blob_bytes, decode_blob_spec, lemma_blob_round_trip};
use crate::primitives::{copy_range, decode_blob, encode_blob};

verus! {

pub const FORMAT_VERSION: u8 = 1;

pub open spec fn magic() -> Seq<u8> {
    seq![0x45u8, 0x43u8, 0x48u8, 0x4fu8] // "ECHO"
}

pub open spec fn envelope_bytes(kind: u8, payload: Seq<u8>) -> Seq<u8> {
    magic() + seq![FORMAT_VERSION, kind] + blob_bytes(payload)
}

pub open spec fn decode_envelope_spec(
    bytes: Seq<u8>,
    expected_kind: u8,
) -> Option<Seq<u8>> {
    if bytes.len() < 6
        || bytes[0] != 0x45
        || bytes[1] != 0x43
        || bytes[2] != 0x48
        || bytes[3] != 0x4f
        || bytes[4] != FORMAT_VERSION
        || bytes[5] != expected_kind {
        None
    } else {
        decode_blob_spec(bytes.subrange(6, bytes.len() as int))
    }
}

pub fn encode_envelope(kind: u8, payload: &Vec<u8>) -> (r: Option<Vec<u8>>)
    ensures
        r is Some ==> r->Some_0@ == envelope_bytes(kind, payload@),
{
    match encode_blob(payload) {
        None => None,
        Some(framed) => {
            let mut out = Vec::new();
            out.push(0x45);
            out.push(0x43);
            out.push(0x48);
            out.push(0x4f);
            out.push(FORMAT_VERSION);
            out.push(kind);
            if framed.len() > usize::MAX - 6 {
                None
            } else {
                crate::primitives::append_bytes(&mut out, &framed);
                Some(out)
            }
        }
    }
}

pub fn decode_envelope(
    bytes: &Vec<u8>,
    expected_kind: u8,
) -> (r: Option<Vec<u8>>)
    ensures
        r.deep_view() == decode_envelope_spec(bytes@, expected_kind),
{
    if bytes.len() < 6
        || bytes[0] != 0x45
        || bytes[1] != 0x43
        || bytes[2] != 0x48
        || bytes[3] != 0x4f
        || bytes[4] != FORMAT_VERSION
        || bytes[5] != expected_kind {
        None
    } else {
        let rest = copy_range(bytes, 6, bytes.len());
        decode_blob(&rest)
    }
}

pub proof fn lemma_envelope_round_trip(kind: u8, payload: Seq<u8>)
    requires
        payload.len() <= u64::MAX,
        payload.len() <= usize::MAX,
    ensures
        decode_envelope_spec(envelope_bytes(kind, payload), kind)
            == Some(payload),
{
    lemma_blob_round_trip(payload);
    assert(envelope_bytes(kind, payload).subrange(
        6, envelope_bytes(kind, payload).len() as int,
    ) == blob_bytes(payload));
}

pub proof fn lemma_envelope_kind_separation(
    encoded_kind: u8,
    expected_kind: u8,
    payload: Seq<u8>,
)
    requires encoded_kind != expected_kind,
    ensures
        decode_envelope_spec(
            envelope_bytes(encoded_kind, payload),
            expected_kind,
        ) is None,
{
}

} // verus!
