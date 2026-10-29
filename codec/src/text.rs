//! Validated Unicode text represented by canonical UTF-8 bytes.

use vstd::prelude::*;
use vstd::string::{StrSliceExecFns, StringExecFns, StringSliceAdditionalSpecFns};

#[cfg(verus_keep_ghost)]
use crate::primitives::decode_blob_spec;
use crate::primitives::{decode_blob, encode_blob};

verus! {

pub open spec fn continuation(byte: u8) -> bool {
    0x80 <= byte <= 0xbf
}

/// Width of the first canonical UTF-8 scalar, or zero when the prefix is
/// truncated, overlong, surrogate-encoded, or above U+10FFFF.
pub open spec fn utf8_unit_width(bytes: Seq<u8>) -> nat {
    if bytes.len() == 0 {
        0
    } else if bytes[0] <= 0x7f {
        1
    } else if 0xc2 <= bytes[0] <= 0xdf {
        if bytes.len() >= 2 && continuation(bytes[1]) { 2 } else { 0 }
    } else if bytes[0] == 0xe0 {
        if bytes.len() >= 3
            && 0xa0 <= bytes[1] <= 0xbf
            && continuation(bytes[2]) { 3 } else { 0 }
    } else if (0xe1 <= bytes[0] <= 0xec) || (0xee <= bytes[0] <= 0xef) {
        if bytes.len() >= 3
            && continuation(bytes[1])
            && continuation(bytes[2]) { 3 } else { 0 }
    } else if bytes[0] == 0xed {
        if bytes.len() >= 3
            && 0x80 <= bytes[1] <= 0x9f
            && continuation(bytes[2]) { 3 } else { 0 }
    } else if bytes[0] == 0xf0 {
        if bytes.len() >= 4
            && 0x90 <= bytes[1] <= 0xbf
            && continuation(bytes[2])
            && continuation(bytes[3]) { 4 } else { 0 }
    } else if 0xf1 <= bytes[0] <= 0xf3 {
        if bytes.len() >= 4
            && continuation(bytes[1])
            && continuation(bytes[2])
            && continuation(bytes[3]) { 4 } else { 0 }
    } else if bytes[0] == 0xf4 {
        if bytes.len() >= 4
            && 0x80 <= bytes[1] <= 0x8f
            && continuation(bytes[2])
            && continuation(bytes[3]) { 4 } else { 0 }
    } else {
        0
    }
}

pub open spec fn valid_utf8(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        true
    } else {
        let width = utf8_unit_width(bytes);
        0 < width <= bytes.len()
            && valid_utf8(bytes.subrange(width as int, bytes.len() as int))
    }
}

#[verifier::bit_vector]
proof fn lemma_width_2_conditions(b0: u8, b1: u8)
    requires
        0xc0 <= b0 <= 0xdf,
        0x80 <= b1 <= 0xbf,
    ensures
        vstd::utf8::not_overlong_encoding(
            vstd::utf8::codepoint_width_2(b0, b1), 2,
        ) <==> 0xc2 <= b0,
        vstd::utf8::not_surrogate(vstd::utf8::codepoint_width_2(b0, b1)),
{
}

#[verifier::bit_vector]
proof fn lemma_width_3_conditions(b0: u8, b1: u8, b2: u8)
    requires
        0xe0 <= b0 <= 0xef,
        0x80 <= b1 <= 0xbf,
        0x80 <= b2 <= 0xbf,
    ensures
        vstd::utf8::not_overlong_encoding(
            vstd::utf8::codepoint_width_3(b0, b1, b2), 3,
        ) <==> (b0 != 0xe0 || b1 >= 0xa0),
        vstd::utf8::not_surrogate(
            vstd::utf8::codepoint_width_3(b0, b1, b2),
        ) <==> (b0 != 0xed || b1 <= 0x9f),
{
}

#[verifier::bit_vector]
proof fn lemma_width_4_conditions(b0: u8, b1: u8, b2: u8, b3: u8)
    requires
        0xf0 <= b0 <= 0xf7,
        0x80 <= b1 <= 0xbf,
        0x80 <= b2 <= 0xbf,
        0x80 <= b3 <= 0xbf,
    ensures
        vstd::utf8::not_overlong_encoding(
            vstd::utf8::codepoint_width_4(b0, b1, b2, b3), 4,
        ) <==> (
            (b0 == 0xf0 && b1 >= 0x90)
            || (0xf1 <= b0 <= 0xf3)
            || (b0 == 0xf4 && b1 <= 0x8f)
        ),
        vstd::utf8::not_overlong_encoding(
            vstd::utf8::codepoint_width_4(b0, b1, b2, b3), 4,
        ) ==> vstd::utf8::not_surrogate(
                vstd::utf8::codepoint_width_4(b0, b1, b2, b3),
            ),
{
}

proof fn lemma_unit_matches_vstd(bytes: Seq<u8>)
    ensures
        utf8_unit_width(bytes) > 0
            <==> vstd::utf8::valid_first_scalar(bytes),
        utf8_unit_width(bytes) > 0 ==> {
            &&& utf8_unit_width(bytes)
                == vstd::utf8::length_of_first_scalar(bytes)
            &&& bytes.subrange(
                utf8_unit_width(bytes) as int, bytes.len() as int,
            ) == vstd::utf8::pop_first_scalar(bytes)
        },
{
    if bytes.len() > 0 {
        let b0 = bytes[0];
        if bytes.len() >= 2 {
            let b1 = bytes[1];
            if 0xc0 <= b0 <= 0xdf && 0x80 <= b1 <= 0xbf {
                lemma_width_2_conditions(b0, b1);
            }
            if bytes.len() >= 3 {
                let b2 = bytes[2];
                if 0xe0 <= b0 <= 0xef
                    && 0x80 <= b1 <= 0xbf
                    && 0x80 <= b2 <= 0xbf {
                    lemma_width_3_conditions(b0, b1, b2);
                }
                if bytes.len() >= 4 {
                    let b3 = bytes[3];
                    if 0xf0 <= b0 <= 0xf7
                        && 0x80 <= b1 <= 0xbf
                        && 0x80 <= b2 <= 0xbf
                        && 0x80 <= b3 <= 0xbf {
                        lemma_width_4_conditions(b0, b1, b2, b3);
                    }
                }
            }
        }
    }
}

pub proof fn lemma_valid_utf8_equiv(bytes: Seq<u8>)
    ensures
        valid_utf8(bytes) == vstd::utf8::valid_utf8(bytes),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        lemma_unit_matches_vstd(bytes);
        let width = utf8_unit_width(bytes);
        if width > 0 {
            let rest = bytes.subrange(width as int, bytes.len() as int);
            lemma_valid_utf8_equiv(rest);
        }
    }
}

fn utf8_unit_width_at(bytes: &Vec<u8>, pos: usize) -> (width: usize)
    requires pos <= bytes.len(),
    ensures width as nat == utf8_unit_width(
        bytes@.subrange(pos as int, bytes@.len() as int),
    ),
{
    if pos == bytes.len() {
        return 0;
    }
    let b0 = bytes[pos];
    if b0 <= 0x7f {
        1
    } else if 0xc2 <= b0 && b0 <= 0xdf {
        if bytes.len() - pos >= 2
            && 0x80 <= bytes[pos + 1] && bytes[pos + 1] <= 0xbf { 2 } else { 0 }
    } else if b0 == 0xe0 {
        if bytes.len() - pos >= 3
            && 0xa0 <= bytes[pos + 1] && bytes[pos + 1] <= 0xbf
            && 0x80 <= bytes[pos + 2] && bytes[pos + 2] <= 0xbf { 3 } else { 0 }
    } else if (0xe1 <= b0 && b0 <= 0xec) || (0xee <= b0 && b0 <= 0xef) {
        if bytes.len() - pos >= 3
            && 0x80 <= bytes[pos + 1] && bytes[pos + 1] <= 0xbf
            && 0x80 <= bytes[pos + 2] && bytes[pos + 2] <= 0xbf { 3 } else { 0 }
    } else if b0 == 0xed {
        if bytes.len() - pos >= 3
            && 0x80 <= bytes[pos + 1] && bytes[pos + 1] <= 0x9f
            && 0x80 <= bytes[pos + 2] && bytes[pos + 2] <= 0xbf { 3 } else { 0 }
    } else if b0 == 0xf0 {
        if bytes.len() - pos >= 4
            && 0x90 <= bytes[pos + 1] && bytes[pos + 1] <= 0xbf
            && 0x80 <= bytes[pos + 2] && bytes[pos + 2] <= 0xbf
            && 0x80 <= bytes[pos + 3] && bytes[pos + 3] <= 0xbf { 4 } else { 0 }
    } else if 0xf1 <= b0 && b0 <= 0xf3 {
        if bytes.len() - pos >= 4
            && 0x80 <= bytes[pos + 1] && bytes[pos + 1] <= 0xbf
            && 0x80 <= bytes[pos + 2] && bytes[pos + 2] <= 0xbf
            && 0x80 <= bytes[pos + 3] && bytes[pos + 3] <= 0xbf { 4 } else { 0 }
    } else if b0 == 0xf4 {
        if bytes.len() - pos >= 4
            && 0x80 <= bytes[pos + 1] && bytes[pos + 1] <= 0x8f
            && 0x80 <= bytes[pos + 2] && bytes[pos + 2] <= 0xbf
            && 0x80 <= bytes[pos + 3] && bytes[pos + 3] <= 0xbf { 4 } else { 0 }
    } else {
        0
    }
}

pub fn is_valid_utf8(bytes: &Vec<u8>) -> (valid: bool)
    ensures valid == valid_utf8(bytes@),
{
    let mut pos = 0usize;
    assert(bytes@.subrange(0, bytes@.len() as int) == bytes@);
    while pos < bytes.len()
        invariant
            pos <= bytes.len(),
            valid_utf8(bytes@) == valid_utf8(
                bytes@.subrange(pos as int, bytes@.len() as int),
            ),
        decreases bytes.len() - pos,
    {
        let width = utf8_unit_width_at(bytes, pos);
        if width == 0 {
            return false;
        } else {
            assert(width <= bytes.len() - pos);
            let ghost suffix = bytes@.subrange(
                pos as int, bytes@.len() as int,
            );
            assert(suffix.subrange(
                width as int,
                bytes@.len() - pos,
            ) == bytes@.subrange((pos + width) as int, bytes@.len() as int));
            assert(valid_utf8(suffix)
                == valid_utf8(bytes@.subrange(
                    (pos + width) as int, bytes@.len() as int,
                )));
            pos += width;
        }
    }
    assert(bytes@.subrange(pos as int, bytes@.len() as int)
        == Seq::<u8>::empty());
    true
}

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Text {
    /// Public for Verus's structural view; codec entry points require `wf`.
    pub bytes: Vec<u8>,
}

impl View for Text {
    type V = Seq<u8>;

    open spec fn view(&self) -> Seq<u8> {
        self.bytes@
    }
}

impl DeepView for Text {
    type V = Seq<u8>;

    open spec fn deep_view(&self) -> Seq<u8> {
        self.bytes@
    }
}

impl Text {
    pub open spec fn wf(&self) -> bool {
        valid_utf8(self@)
    }

    pub fn from_utf8(bytes: Vec<u8>) -> (r: Option<Text>)
        ensures
            r is Some ==> r->Some_0@ == bytes@,
            r is Some ==> r->Some_0.wf(),
            r is None ==> !valid_utf8(bytes@),
    {
        if is_valid_utf8(&bytes) {
            Some(Text { bytes })
        } else {
            None
        }
    }

    pub fn as_bytes(&self) -> &Vec<u8> {
        &self.bytes
    }

    pub fn into_bytes(self) -> (bytes: Vec<u8>)
        ensures bytes@ == self@,
    {
        self.bytes
    }

    pub fn from_string(value: &String) -> (text: Text)
        ensures
            text@ == vstd::utf8::encode_utf8(value@),
            text.wf(),
    {
        let bytes = value.as_str().as_bytes_vec();
        proof {
            vstd::utf8::encode_utf8_valid_utf8(value@);
            lemma_valid_utf8_equiv(bytes@);
        }
        Text { bytes }
    }

    pub fn into_string(self) -> (value: String)
        requires self.wf(),
        ensures value@ == vstd::utf8::decode_utf8(self@),
    {
        let ghost bytes_view = self@;
        proof {
            lemma_valid_utf8_equiv(bytes_view);
        }
        let bytes = self.bytes;
        let slice = bytes.as_slice();
        let string_slice = unsafe { str::from_utf8_unchecked(slice) };
        let value = <String as StringExecFns>::from_str(string_slice);
        proof {
            assert(string_slice.spec_bytes() == bytes_view);
            assert(vstd::utf8::encode_utf8(string_slice@) == bytes_view);
            vstd::utf8::encode_utf8_decode_utf8(string_slice@);
            assert(vstd::utf8::decode_utf8(bytes_view) == string_slice@);
        }
        value
    }
}

pub proof fn lemma_string_text_model_round_trip(chars: Seq<char>)
    ensures
        vstd::utf8::decode_utf8(vstd::utf8::encode_utf8(chars)) == chars,
{
    vstd::utf8::encode_utf8_decode_utf8(chars);
}

pub proof fn lemma_text_string_model_round_trip(bytes: Seq<u8>)
    requires valid_utf8(bytes),
    ensures
        vstd::utf8::encode_utf8(vstd::utf8::decode_utf8(bytes)) == bytes,
{
    lemma_valid_utf8_equiv(bytes);
    vstd::utf8::decode_utf8_encode_utf8(bytes);
}

pub fn round_trip_string(value: String) -> (result: String)
    ensures result@ == value@,
{
    let text = Text::from_string(&value);
    let result = text.into_string();
    proof {
        vstd::utf8::encode_utf8_decode_utf8(value@);
    }
    result
}

pub fn round_trip_text(value: Text) -> (result: Text)
    requires value.wf(),
    ensures result@ == value@,
{
    let ghost original = value@;
    let string = value.into_string();
    let result = Text::from_string(&string);
    proof {
        lemma_text_string_model_round_trip(original);
    }
    result
}

pub open spec fn text_bytes(text: Seq<u8>) -> Seq<u8> {
    crate::primitives::blob_bytes(text)
}

pub fn encode_text(text: &Text) -> (r: Option<Vec<u8>>)
    ensures
        r is Some ==> r->Some_0@ == text_bytes(text@),
{
    encode_blob(&text.bytes)
}

pub open spec fn decode_text_spec(bytes: Seq<u8>) -> Option<Seq<u8>> {
    match decode_blob_spec(bytes) {
        Some(text) if valid_utf8(text) => Some(text),
        _ => None,
    }
}

pub fn decode_text(bytes: &Vec<u8>) -> (r: Option<Text>)
    ensures
        r.deep_view() == decode_text_spec(bytes@),
{
    match decode_blob(bytes) {
        None => {
            assert(decode_blob_spec(bytes@) is None);
            None
        }
        Some(payload) => {
            assert(decode_blob_spec(bytes@) == Some(payload@));
            match Text::from_utf8(payload) {
                None => None,
                Some(text) => Some(text),
            }
        }
    }
}

pub proof fn lemma_text_round_trip(text: Seq<u8>)
    requires
        valid_utf8(text),
        text.len() <= u64::MAX,
        text.len() <= usize::MAX,
    ensures
        decode_text_spec(text_bytes(text)) == Some(text),
{
    crate::primitives::lemma_blob_round_trip(text);
}

} // verus!
