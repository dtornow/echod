//! Validated Unicode text represented by canonical UTF-8 bytes.

use vstd::prelude::*;

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
