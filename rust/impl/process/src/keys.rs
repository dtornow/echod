//! Where everything lives under the bucket.
//!
//! ```text
//! <prefix>wf/<origin>                                    a workflow document: rows
//! <prefix>sched/<id>                                     a schedule: one row
//! <prefix>t/<bucket>/<deadline>_<origin>@<token>         a deadline for an origin, empty
//! <prefix>t/<bucket>/<deadline>_sched:<id>@<token>       a schedule's next run, empty
//! <prefix>nodes/<node id>                                a node's announcement
//! <prefix>members                                        the configuration: members and epoch
//! ```
//!
//! A deadline key lives in the time bucket its deadline falls in, so what is
//! due is found by listing the buckets at or before now and nothing later. The
//! token names the arm that wrote the key, so a writer removes exactly the key
//! its predecessor wrote and never one that happens to share the deadline.
//!
//! The text of a key is written and read by `text`, plain Rust; each of its
//! functions is stated once, as the characters it produces, and `KeySpace`
//! computes those statements. Which bucket an instant falls in is proved.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;
use vstd::string::{
    StringSliceAdditionalSpecFns,
    StrSliceExecFns,
};

use crate::verified::text::copy_string;

verus! {

pub const DEADLINE_WIDTH: usize = 20;

#[make_spec_type]
#[derive(Debug, Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct KeySpace {
    pub prefix: String,
    /// The width of a timer bucket, ms. At least 1.
    pub bucket_ms: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum TimerEntry {
    Origin { deadline: u64, origin: String, token: u64, by: String },
    Schedule { deadline: u64, id: String, token: u64, by: String },
}

#[cfg(verus_keep_ghost)]
pub ghost enum TimerEntrySpec {
    Origin { deadline: u64, origin: Seq<char>, token: u64, by: Seq<char> },
    Schedule { deadline: u64, id: Seq<char>, token: u64, by: Seq<char> },
}

#[cfg(verus_keep_ghost)]
impl DeepView for TimerEntry {
    type V = TimerEntrySpec;
    open spec fn deep_view(&self) -> TimerEntrySpec {
        match self {
            TimerEntry::Origin { deadline, origin, token, by } => TimerEntrySpec::Origin { deadline: *deadline, origin: origin@, token: *token, by: by@ },
            TimerEntry::Schedule { deadline, id, token, by } => TimerEntrySpec::Schedule { deadline: *deadline, id: id@, token: *token, by: by@ },
        }
    }
}

#[cfg(verus_keep_ghost)]
impl TimerEntrySpec {
    pub open spec fn deadline(self) -> u64 {
        match self {
            TimerEntrySpec::Origin { deadline, .. } | TimerEntrySpec::Schedule { deadline, .. } => deadline,
        }
    }

    pub open spec fn target(self) -> Seq<char> {
        match self {
            TimerEntrySpec::Origin { origin, .. } => origin,
            TimerEntrySpec::Schedule { id, .. } => id,
        }
    }

    pub open spec fn token(self) -> u64 {
        match self {
            TimerEntrySpec::Origin { token, .. } | TimerEntrySpec::Schedule { token, .. } => token,
        }
    }

    pub open spec fn by(self) -> Seq<char> {
        match self {
            TimerEntrySpec::Origin { by, .. } | TimerEntrySpec::Schedule { by, .. } => by,
        }
    }
}

impl TimerEntry {
    pub fn deadline(&self) -> (r: u64)
        ensures
            r == self.deep_view().deadline(),
    {
        match self {
            TimerEntry::Origin { deadline, .. } | TimerEntry::Schedule { deadline, .. } => *deadline,
        }
    }

    /// What ownership is decided on.
    pub fn target(&self) -> (r: &String)
        ensures
            r@ == self.deep_view().target(),
    {
        match self {
            TimerEntry::Origin { origin, .. } => origin,
            TimerEntry::Schedule { id, .. } => id,
        }
    }

    pub fn token(&self) -> (r: u64)
        ensures
            r == self.deep_view().token(),
    {
        match self {
            TimerEntry::Origin { token, .. } | TimerEntry::Schedule { token, .. } => *token,
        }
    }

    pub fn by(&self) -> (r: &String)
        ensures
            r@ == self.deep_view().by(),
    {
        match self {
            TimerEntry::Origin { by, .. } | TimerEntry::Schedule { by, .. } => by,
        }
    }
}

// ---------------------------------------------------------------------------
// The text of a key, stated
// ---------------------------------------------------------------------------

pub open spec fn spec_safe_key_byte(b: u8) -> bool {
    ||| b'A' <= b <= b'Z'
    ||| b'a' <= b <= b'z'
    ||| b'0' <= b <= b'9'
    ||| b == b'.'
    ||| b == b'-'
}

pub open spec fn spec_upper_hex_digit(n: u8) -> char {
    if n < 10 {
        (b'0' + n) as char
    } else {
        (b'A' + (n - 10)) as char
    }
}

pub open spec fn spec_hex_value(c: char) -> Option<u8> {
    if '0' <= c <= '9' {
        Some((c as u32 - '0' as u32) as u8)
    } else if 'A' <= c <= 'F' {
        Some((c as u32 - 'A' as u32 + 10) as u8)
    } else if 'a' <= c <= 'f' {
        Some((c as u32 - 'a' as u32 + 10) as u8)
    } else {
        None
    }
}

pub open spec fn spec_encode_key_byte(b: u8) -> Seq<char> {
    if spec_safe_key_byte(b) {
        seq![b as char]
    } else {
        seq![
            '%',
            spec_upper_hex_digit(b >> 4),
            spec_upper_hex_digit(b & 0x0f),
        ]
    }
}

pub open spec fn spec_encode_key_bytes(bytes: Seq<u8>) -> Seq<char>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        Seq::empty()
    } else {
        spec_encode_key_byte(bytes[0])
            + spec_encode_key_bytes(bytes.drop_first())
    }
}

pub open spec fn spec_decode_key_bytes(encoded: Seq<char>) -> Option<Seq<u8>>
    decreases encoded.len(),
{
    if encoded.len() == 0 {
        Some(Seq::empty())
    } else if encoded[0] == '%' {
        if encoded.len() < 3 {
            None
        } else {
            match (spec_hex_value(encoded[1]), spec_hex_value(encoded[2])) {
                (Some(hi), Some(lo)) => {
                    match spec_decode_key_bytes(encoded.skip(3)) {
                        Some(rest) => Some(seq![((hi << 4) | lo) as u8] + rest),
                        None => None,
                    }
                },
                _ => None,
            }
        }
    } else {
        match spec_decode_key_bytes(encoded.drop_first()) {
            Some(rest) => {
                let c = encoded[0] as u32;
                let raw = if c <= 0x7f {
                    seq![c as u8]
                } else {
                    vstd::utf8::encode_utf8(seq![encoded[0]])
                };
                Some(raw + rest)
            },
            None => None,
        }
    }
}

pub open spec fn spec_encode_key(s: Seq<char>) -> Seq<char> {
    spec_encode_key_bytes(vstd::utf8::encode_utf8(s))
}

pub open spec fn spec_decode_key(s: Seq<char>) -> Option<Seq<char>> {
    match spec_decode_key_bytes(s) {
        Some(bytes) => if vstd::utf8::valid_utf8(bytes) {
            Some(vstd::utf8::decode_utf8(bytes))
        } else {
            None
        },
        None => None,
    }
}

pub open spec fn spec_normalize_prefix(s: Seq<char>) -> Seq<char> {
    if s.len() == 0 || s.last() == '/' {
        s
    } else {
        s.push('/')
    }
}

pub open spec fn spec_starts_with_chars(
    text: Seq<char>,
    prefix: Seq<char>,
) -> bool {
    text.len() >= prefix.len()
        && text.take(prefix.len() as int) == prefix
}

pub open spec fn spec_take_to_slash(text: Seq<char>) -> Seq<char>
    decreases text.len(),
{
    if text.len() == 0 || text[0] == '/' {
        Seq::empty()
    } else {
        seq![text[0]] + spec_take_to_slash(text.drop_first())
    }
}

pub open spec fn spec_class_of(
    prefix: Seq<char>,
    key: Seq<char>,
) -> Option<Seq<char>> {
    if spec_starts_with_chars(key, prefix) {
        Some(spec_take_to_slash(key.skip(prefix.len() as int)))
    } else {
        None
    }
}

pub open spec fn spec_doc_key(
    prefix: Seq<char>,
    origin: Seq<char>,
) -> Seq<char> {
    prefix + "wf/"@ + spec_encode_key(origin)
}

pub open spec fn spec_sched_key(
    prefix: Seq<char>,
    id: Seq<char>,
) -> Seq<char> {
    prefix + "sched/"@ + spec_encode_key(id)
}

pub open spec fn spec_members_key(prefix: Seq<char>) -> Seq<char> {
    prefix + "members"@
}

pub open spec fn spec_node_prefix(prefix: Seq<char>) -> Seq<char> {
    prefix + "nodes/"@
}

pub open spec fn spec_node_key(
    prefix: Seq<char>,
    id: Seq<char>,
) -> Seq<char> {
    spec_node_prefix(prefix) + spec_encode_key(id)
}

pub open spec fn spec_node_of_key(
    prefix: Seq<char>,
    key: Seq<char>,
) -> Option<Seq<char>> {
    let node_prefix = spec_node_prefix(prefix);
    if spec_starts_with_chars(key, node_prefix) {
        spec_decode_key(key.skip(node_prefix.len() as int))
    } else {
        None
    }
}

pub open spec fn spec_timer_prefix(prefix: Seq<char>) -> Seq<char> {
    prefix + "t/"@
}

pub open spec fn spec_pow10(exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        10 * spec_pow10((exp - 1) as nat)
    }
}

pub open spec fn spec_decimal_digit(n: nat) -> char {
    if n < 10 {
        (b'0' + n as u8) as char
    } else {
        '?'
    }
}

pub open spec fn spec_decimal20_from(n: u64, pos: nat) -> Seq<char>
    recommends
        pos <= 20,
    decreases 20 - pos,
{
    if pos >= 20 {
        Seq::empty()
    } else {
        let divisor = spec_pow10((19 - pos) as nat);
        seq![spec_decimal_digit(((n as nat) / divisor) % 10)]
            + spec_decimal20_from(n, pos + 1)
    }
}

pub open spec fn spec_decimal_fixed(n: u64, width: nat) -> Seq<char>
    decreases width,
{
    if width == 0 {
        Seq::empty()
    } else {
        spec_decimal_fixed(n / 10, (width - 1) as nat)
            .push(spec_decimal_digit((n % 10) as nat))
    }
}

pub open spec fn spec_decimal20(n: u64) -> Seq<char> {
    spec_decimal_fixed(n, 20)
}

pub open spec fn spec_lower_hex_digit(n: u64) -> char {
    if n < 10 {
        (b'0' + n as u8) as char
    } else if n < 16 {
        (b'a' + (n - 10) as u8) as char
    } else {
        '?'
    }
}

pub open spec fn spec_hex16_from(n: u64, pos: nat) -> Seq<char>
    recommends
        pos <= 16,
    decreases 16 - pos,
{
    if pos >= 16 {
        Seq::empty()
    } else {
        let shift = ((15 - pos) * 4) as u64;
        seq![spec_lower_hex_digit((n >> shift) & 0x0f)]
            + spec_hex16_from(n, pos + 1)
    }
}

pub open spec fn spec_hex_fixed(n: u64, width: nat) -> Seq<char>
    decreases width,
{
    if width == 0 {
        Seq::empty()
    } else {
        spec_hex_fixed(n / 16, (width - 1) as nat)
            .push(spec_lower_hex_digit(n % 16))
    }
}

pub open spec fn spec_hex16(n: u64) -> Seq<char> {
    spec_hex_fixed(n, 16)
}

pub open spec fn spec_bucket_prefix(
    prefix: Seq<char>,
    bucket: u64,
) -> Seq<char> {
    (spec_timer_prefix(prefix) + spec_decimal20(bucket)).push('/')
}
pub open spec fn spec_decimal_value(
    text: Seq<char>,
    acc: u64,
) -> Option<u64>
    decreases text.len(),
{
    if text.len() == 0 {
        Some(acc)
    } else {
        let c = text[0];
        if '0' <= c <= '9' {
            let digit = (c as u32 - '0' as u32) as u64;
            if acc <= (u64::MAX - digit) / 10 {
                spec_decimal_value(
                    text.drop_first(),
                    (acc * 10 + digit) as u64,
                )
            } else {
                None
            }
        } else {
            None
        }
    }
}

pub open spec fn spec_parse_bucket_prefix(
    prefix: Seq<char>,
    p: Seq<char>,
) -> Option<u64> {
    let base = spec_timer_prefix(prefix);
    if spec_starts_with_chars(p, base)
        && p.len() == base.len() + 21
        && p.last() == '/'
    {
        spec_decimal_value(
            p.subrange(
                base.len() as int,
                base.len() as int + 20,
            ),
            0,
        )
    } else {
        None
    }
}

pub open spec fn spec_timer_key_for(
    prefix: Seq<char>,
    bucket_ms: u64,
    encoded_target: Seq<char>,
    at: u64,
    token: u64,
    by: Seq<char>,
) -> Seq<char> {
    (((spec_bucket_prefix(prefix, spec_bucket_of(at, bucket_ms))
        + spec_decimal20(at)).push('_')
        + encoded_target).push('@')
        + spec_hex16(token)).push('~')
        + spec_encode_key(by)
}

pub open spec fn spec_timer_key(
    prefix: Seq<char>,
    bucket_ms: u64,
    origin: Seq<char>,
    at: u64,
    token: u64,
    by: Seq<char>,
) -> Seq<char> {
    spec_timer_key_for(
        prefix,
        bucket_ms,
        spec_encode_key(origin),
        at,
        token,
        by,
    )
}

pub open spec fn spec_sched_timer_key(
    prefix: Seq<char>,
    bucket_ms: u64,
    id: Seq<char>,
    at: u64,
    token: u64,
    by: Seq<char>,
) -> Seq<char> {
    spec_timer_key_for(
        prefix,
        bucket_ms,
        "sched:"@ + spec_encode_key(id),
        at,
        token,
        by,
    )
}
pub open spec fn spec_last_segment(key: Seq<char>) -> Seq<char>
    decreases key.len(),
{
    if key.len() == 0 || key.last() == '/' {
        Seq::empty()
    } else {
        spec_last_segment(key.drop_last()).push(key.last())
    }
}

pub open spec fn spec_timer_name_for(
    encoded_target: Seq<char>,
    deadline: u64,
    token: u64,
    by: Seq<char>,
) -> Seq<char> {
    ((spec_decimal20(deadline).push('_')
        + encoded_target).push('@')
        + spec_hex16(token)).push('~')
        + spec_encode_key(by)
}

pub open spec fn spec_timer_entry_name(entry: TimerEntrySpec) -> Seq<char> {
    match entry {
        TimerEntrySpec::Origin {
            deadline,
            origin,
            token,
            by,
        } => spec_timer_name_for(
            spec_encode_key(origin),
            deadline,
            token,
            by,
        ),
        TimerEntrySpec::Schedule {
            deadline,
            id,
            token,
            by,
        } => spec_timer_name_for(
            "sched:"@ + spec_encode_key(id),
            deadline,
            token,
            by,
        ),
    }
}

pub open spec fn spec_find_char(
    text: Seq<char>,
    needle: char,
    at: int,
) -> Option<int>
    decreases text.len() - at,
{
    if at < 0 || at >= text.len() {
        None
    } else if text[at] == needle {
        Some(at)
    } else {
        spec_find_char(text, needle, at + 1)
    }
}

pub open spec fn spec_hex_value_acc(
    text: Seq<char>,
    acc: u64,
) -> Option<u64>
    decreases text.len(),
{
    if text.len() == 0 {
        Some(acc)
    } else {
        match spec_hex_value(text[0]) {
            Some(digit) => spec_hex_value_acc(
                text.drop_first(),
                acc.wrapping_mul(16).wrapping_add(digit as u64),
            ),
            None => None,
        }
    }
}

pub open spec fn spec_parsed_timer_entry(
    name: Seq<char>,
) -> Option<TimerEntrySpec> {
    if name.len() < 39 || name[20] != '_' {
        None
    } else {
        match (
            spec_decimal_value(name.take(20), 0),
            spec_find_char(name, '@', 21),
        ) {
            (Some(deadline), Some(separator))
                if separator + 18 <= name.len()
                    && name[separator + 17] == '~' => {
                match (
                    spec_hex_value_acc(
                        name.subrange(separator + 1, separator + 17),
                        0,
                    ),
                    spec_decode_key(name.skip(separator + 18)),
                ) {
                    (Some(token), Some(by)) => {
                        let target = name.subrange(21, separator);
                        let candidate =
                            if spec_starts_with_chars(target, "sched:"@) {
                                match spec_decode_key(target.skip(6)) {
                                    Some(id) => Some(
                                        TimerEntrySpec::Schedule {
                                            deadline,
                                            id,
                                            token,
                                            by,
                                        },
                                    ),
                                    None => None,
                                }
                            } else {
                                match spec_decode_key(target) {
                                    Some(origin) => Some(
                                        TimerEntrySpec::Origin {
                                            deadline,
                                            origin,
                                            token,
                                            by,
                                        },
                                    ),
                                    None => None,
                                }
                            };
                        match candidate {
                            Some(entry)
                                if spec_timer_entry_name(entry) == name =>
                                    Some(entry),
                            _ => None,
                        }
                    },
                    _ => None,
                }
            },
            _ => None,
        }
    }
}

pub open spec fn spec_parse_timer_key(
    key: Seq<char>,
) -> Option<TimerEntrySpec> {
    spec_parsed_timer_entry(spec_last_segment(key))
}

pub proof fn lemma_upper_hex_digit_inverse(n: u8)
    requires
        n < 16,
    ensures
        spec_hex_value(spec_upper_hex_digit(n)) == Some(n),
{
    if n < 10 {
        assert('0' as u32 + n as u32 <= '9' as u32);
    } else {
        assert(n - 10 < 6);
        assert('A' as u32 + (n - 10) as u32 <= 'F' as u32);
    }
}

pub proof fn lemma_decode_safe_key_head(
    b: u8,
    encoded_rest: Seq<char>,
    decoded_rest: Seq<u8>,
)
    requires
        spec_safe_key_byte(b),
        spec_decode_key_bytes(encoded_rest) == Some(decoded_rest),
    ensures
        spec_decode_key_bytes(seq![b as char] + encoded_rest)
            == Some(seq![b] + decoded_rest),
{
    assert(b != b'%');
    assert((b as char) != '%');
    assert(b <= 0x7f);
    assert((b as char) as u32 <= 0x7f);
    assert((seq![b as char] + encoded_rest).drop_first()
        == encoded_rest);
}

pub proof fn lemma_decode_escaped_key_head(
    b: u8,
    encoded_rest: Seq<char>,
    decoded_rest: Seq<u8>,
)
    requires
        !spec_safe_key_byte(b),
        spec_decode_key_bytes(encoded_rest) == Some(decoded_rest),
    ensures
        spec_decode_key_bytes(
            seq![
                '%',
                spec_upper_hex_digit(b >> 4),
                spec_upper_hex_digit(b & 0x0f),
            ] + encoded_rest,
        ) == Some(seq![b] + decoded_rest),
{
    assert((b >> 4) < 16) by (bit_vector);
    assert((b & 0x0f) < 16) by (bit_vector);
    lemma_upper_hex_digit_inverse(b >> 4);
    lemma_upper_hex_digit_inverse(b & 0x0f);
    assert((((b >> 4) << 4) | (b & 0x0f)) as u8 == b)
        by (bit_vector);
    assert((seq![
        '%',
        spec_upper_hex_digit(b >> 4),
        spec_upper_hex_digit(b & 0x0f),
    ] + encoded_rest).skip(3) == encoded_rest);
}

pub proof fn lemma_decode_encode_key_bytes(bytes: Seq<u8>)
    ensures
        spec_decode_key_bytes(spec_encode_key_bytes(bytes))
            == Some(bytes),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        let b = bytes[0];
        lemma_decode_encode_key_bytes(bytes.drop_first());
        if spec_safe_key_byte(b) {
            lemma_decode_safe_key_head(
                b,
                spec_encode_key_bytes(bytes.drop_first()),
                bytes.drop_first(),
            );
            assert(bytes =~= seq![b] + bytes.drop_first());
        } else {
            let head = seq![
                '%',
                spec_upper_hex_digit(b >> 4),
                spec_upper_hex_digit(b & 0x0f),
            ];
            lemma_decode_escaped_key_head(
                b,
                spec_encode_key_bytes(bytes.drop_first()),
                bytes.drop_first(),
            );
            assert(bytes =~= seq![b] + bytes.drop_first());
        }
    }
}

pub proof fn lemma_encode_key_bytes_cons(
    b: u8,
    tail: Seq<u8>,
)
    ensures
        spec_encode_key_bytes(seq![b] + tail)
            == spec_encode_key_byte(b)
                + spec_encode_key_bytes(tail),
{
    reveal(spec_encode_key_bytes);
    assert((seq![b] + tail).len() > 0);
    assert((seq![b] + tail)[0] == b);
    assert((seq![b] + tail).drop_first() == tail);
}

pub proof fn lemma_encode_key_bytes_concat(
    left: Seq<u8>,
    right: Seq<u8>,
)
    ensures
        spec_encode_key_bytes(left + right)
            == spec_encode_key_bytes(left)
                + spec_encode_key_bytes(right),
    decreases left.len(),
{
    if left.len() > 0 {
        let b = left[0];
        let tail = left.drop_first();
        lemma_encode_key_bytes_concat(left.drop_first(), right);
        assert(left =~= seq![b] + tail);
        assert(left + right =~= seq![b] + (tail + right));
        lemma_encode_key_bytes_cons(b, tail + right);
        lemma_encode_key_bytes_cons(b, tail);
    }
}

pub proof fn lemma_encode_key_round_trip(s: Seq<char>)
    ensures
        spec_decode_key(spec_encode_key(s)) == Some(s),
{
    let bytes = vstd::utf8::encode_utf8(s);
    lemma_decode_encode_key_bytes(bytes);
    vstd::utf8::encode_utf8_valid_utf8(s);
    vstd::utf8::encode_utf8_decode_utf8(s);
}

pub proof fn lemma_encode_key_injective(
    left: Seq<char>,
    right: Seq<char>,
)
    requires
        spec_encode_key(left) == spec_encode_key(right),
    ensures
        left == right,
{
    lemma_encode_key_round_trip(left);
    lemma_encode_key_round_trip(right);
}

} // verus!

#[cfg(all(verus_keep_ghost, feature = "key-algebra-proofs"))]
#[verifier::spinoff_prover]
pub mod algebra {
use super::*;

verus! {

#[verifier::spinoff_prover]
pub proof fn lemma_decimal_digit_injective(a: nat, b: nat)
    requires
        a < 10,
        b < 10,
        spec_decimal_digit(a) == spec_decimal_digit(b),
    ensures
        a == b,
{
}

#[verifier::spinoff_prover]
pub proof fn lemma_decimal_fixed_injective(
    left: u64,
    right: u64,
    width: nat,
)
    requires
        (left as nat) < spec_pow10(width),
        (right as nat) < spec_pow10(width),
        spec_decimal_fixed(left, width)
            == spec_decimal_fixed(right, width),
    ensures
        left == right,
    decreases width,
{
    if width == 0 {
        assert(spec_pow10(0) == 1);
    } else {
        assert(spec_pow10(width)
            == 10 * spec_pow10((width - 1) as nat));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            left as int,
            10,
        );
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            right as int,
            10,
        );
        assert((left as int) / 10 == (left / 10) as int);
        assert((left as int) % 10 == (left % 10) as int);
        assert((right as int) / 10 == (right / 10) as int);
        assert((right as int) % 10 == (right % 10) as int);
        assert(0 <= ((left % 10) as int) && ((left % 10) as int) < 10);
        assert(0 <= ((right % 10) as int) && ((right % 10) as int) < 10);
        assert(0 <= (left / 10) as int);
        assert(0 <= (right / 10) as int);
        assert(left as int
            == (left / 10) as int * 10 + (left % 10) as int);
        assert(right as int
            == (right / 10) as int * 10 + (right % 10) as int);
        assert((left as int)
            < (spec_pow10((width - 1) as nat) as int) * 10);
        assert((right as int)
            < (spec_pow10((width - 1) as nat) as int) * 10);
        assert(((left / 10) as int) * 10 <= left as int)
            by (nonlinear_arith);
        assert(((right / 10) as int) * 10 <= right as int)
            by (nonlinear_arith);
        assert(((left / 10) as int)
            < (spec_pow10((width - 1) as nat) as int)) by {
            if ((left / 10) as int)
                    >= (spec_pow10((width - 1) as nat) as int) {
                assert(((left / 10) as int) * 10
                    >= (spec_pow10((width - 1) as nat) as int) * 10);
                assert(false);
            }
        }
        assert(((right / 10) as int)
            < (spec_pow10((width - 1) as nat) as int)) by {
            if ((right / 10) as int)
                    >= (spec_pow10((width - 1) as nat) as int) {
                assert(((right / 10) as int) * 10
                    >= (spec_pow10((width - 1) as nat) as int) * 10);
                assert(false);
            }
        }
        assert(((left / 10) as nat)
            < spec_pow10((width - 1) as nat));
        assert(((right / 10) as nat)
            < spec_pow10((width - 1) as nat));
        assert(spec_decimal_fixed(left, width).drop_last()
            == spec_decimal_fixed(left / 10, (width - 1) as nat));
        assert(spec_decimal_fixed(right, width).drop_last()
            == spec_decimal_fixed(right / 10, (width - 1) as nat));
        lemma_decimal_fixed_injective(
            left / 10,
            right / 10,
            (width - 1) as nat,
        );
        assert(spec_decimal_fixed(left, width).last()
            == spec_decimal_digit((left % 10) as nat));
        assert(spec_decimal_fixed(right, width).last()
            == spec_decimal_digit((right % 10) as nat));
        lemma_decimal_digit_injective(
            (left % 10) as nat,
            (right % 10) as nat,
        );
        assert(left / 10 == right / 10);
        assert(left % 10 == right % 10);
        assert((left / 10) as int == (right / 10) as int);
        assert((left % 10) as int == (right % 10) as int);
        assert(left as int == right as int);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_decimal20_injective(left: u64, right: u64)
    requires
        spec_decimal20(left) == spec_decimal20(right),
    ensures
        left == right,
{
    assert(spec_pow10(20) == 100_000_000_000_000_000_000nat)
        by (compute);
    lemma_decimal_fixed_injective(left, right, 20);
}

pub open spec fn spec_pow16(exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        16 * spec_pow16((exp - 1) as nat)
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_lower_hex_digit_injective(a: u64, b: u64)
    requires
        a < 16,
        b < 16,
        spec_lower_hex_digit(a) == spec_lower_hex_digit(b),
    ensures
        a == b,
{
}

#[verifier::spinoff_prover]
pub proof fn lemma_hex_fixed_injective(
    left: u64,
    right: u64,
    width: nat,
)
    requires
        (left as nat) < spec_pow16(width),
        (right as nat) < spec_pow16(width),
        spec_hex_fixed(left, width) == spec_hex_fixed(right, width),
    ensures
        left == right,
    decreases width,
{
    if width == 0 {
        assert(spec_pow16(0) == 1);
    } else {
        assert(spec_pow16(width)
            == 16 * spec_pow16((width - 1) as nat));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            left as int,
            16,
        );
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            right as int,
            16,
        );
        assert((left as int) / 16 == (left / 16) as int);
        assert((left as int) % 16 == (left % 16) as int);
        assert((right as int) / 16 == (right / 16) as int);
        assert((right as int) % 16 == (right % 16) as int);
        assert(0 <= ((left % 16) as int) && ((left % 16) as int) < 16);
        assert(0 <= ((right % 16) as int) && ((right % 16) as int) < 16);
        assert(0 <= (left / 16) as int);
        assert(0 <= (right / 16) as int);
        assert(left as int
            == (left / 16) as int * 16 + (left % 16) as int);
        assert(right as int
            == (right / 16) as int * 16 + (right % 16) as int);
        assert((left as int)
            < (spec_pow16((width - 1) as nat) as int) * 16);
        assert((right as int)
            < (spec_pow16((width - 1) as nat) as int) * 16);
        assert(((left / 16) as int) * 16 <= left as int)
            by (nonlinear_arith);
        assert(((right / 16) as int) * 16 <= right as int)
            by (nonlinear_arith);
        assert(((left / 16) as int)
            < (spec_pow16((width - 1) as nat) as int)) by {
            if ((left / 16) as int)
                    >= (spec_pow16((width - 1) as nat) as int) {
                assert(((left / 16) as int) * 16
                    >= (spec_pow16((width - 1) as nat) as int) * 16);
                assert(false);
            }
        }
        assert(((right / 16) as int)
            < (spec_pow16((width - 1) as nat) as int)) by {
            if ((right / 16) as int)
                    >= (spec_pow16((width - 1) as nat) as int) {
                assert(((right / 16) as int) * 16
                    >= (spec_pow16((width - 1) as nat) as int) * 16);
                assert(false);
            }
        }
        assert(((left / 16) as nat)
            < spec_pow16((width - 1) as nat));
        assert(((right / 16) as nat)
            < spec_pow16((width - 1) as nat));
        assert(spec_hex_fixed(left, width).drop_last()
            == spec_hex_fixed(left / 16, (width - 1) as nat));
        assert(spec_hex_fixed(right, width).drop_last()
            == spec_hex_fixed(right / 16, (width - 1) as nat));
        lemma_hex_fixed_injective(
            left / 16,
            right / 16,
            (width - 1) as nat,
        );
        assert(spec_hex_fixed(left, width).last()
            == spec_lower_hex_digit(left % 16));
        assert(spec_hex_fixed(right, width).last()
            == spec_lower_hex_digit(right % 16));
        lemma_lower_hex_digit_injective(left % 16, right % 16);
        assert(left / 16 == right / 16);
        assert(left % 16 == right % 16);
        assert((left / 16) as int == (right / 16) as int);
        assert((left % 16) as int == (right % 16) as int);
        assert(left as int == right as int);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_hex16_injective(left: u64, right: u64)
    requires
        spec_hex16(left) == spec_hex16(right),
    ensures
        left == right,
{
    assert(spec_pow16(16) == 18_446_744_073_709_551_616nat)
        by (compute);
    lemma_hex_fixed_injective(left, right, 16);
}

pub open spec fn spec_excludes(text: Seq<char>, delimiter: char) -> bool {
    forall|i: int| 0 <= i < text.len() ==> text[i] != delimiter
}

#[verifier::spinoff_prover]
pub proof fn lemma_decimal_fixed_len(n: u64, width: nat)
    ensures
        spec_decimal_fixed(n, width).len() == width,
    decreases width,
{
    if width > 0 {
        lemma_decimal_fixed_len(n / 10, (width - 1) as nat);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_hex_fixed_len(n: u64, width: nat)
    ensures
        spec_hex_fixed(n, width).len() == width,
    decreases width,
{
    if width > 0 {
        lemma_hex_fixed_len(n / 16, (width - 1) as nat);
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_hex_fixed_excludes_delimiters(n: u64, width: nat)
    ensures
        spec_excludes(spec_hex_fixed(n, width), '@'),
        spec_excludes(spec_hex_fixed(n, width), '~'),
        spec_excludes(spec_hex_fixed(n, width), '/'),
    decreases width,
{
    if width > 0 {
        lemma_hex_fixed_excludes_delimiters(
            n / 16,
            (width - 1) as nat,
        );
        assert(spec_lower_hex_digit(n % 16) != '@');
        assert(spec_lower_hex_digit(n % 16) != '~');
        assert(spec_lower_hex_digit(n % 16) != '/');
        assert forall|i: int| 0 <= i < spec_hex_fixed(n, width).len()
        implies spec_hex_fixed(n, width)[i] != '@'
            && spec_hex_fixed(n, width)[i] != '~'
            && spec_hex_fixed(n, width)[i] != '/' by {
            if i < spec_hex_fixed(
                n / 16,
                (width - 1) as nat,
            ).len() {
                assert(spec_hex_fixed(n, width)[i]
                    == spec_hex_fixed(
                        n / 16,
                        (width - 1) as nat,
                    )[i]);
            } else {
                assert(i == spec_hex_fixed(
                    n / 16,
                    (width - 1) as nat,
                ).len());
            }
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_decimal_fixed_excludes_delimiters(
    n: u64,
    width: nat,
)
    ensures
        spec_excludes(spec_decimal_fixed(n, width), '_'),
        spec_excludes(spec_decimal_fixed(n, width), '@'),
        spec_excludes(spec_decimal_fixed(n, width), '~'),
        spec_excludes(spec_decimal_fixed(n, width), '/'),
    decreases width,
{
    if width > 0 {
        lemma_decimal_fixed_excludes_delimiters(
            n / 10,
            (width - 1) as nat,
        );
        assert(spec_decimal_digit((n % 10) as nat) != '_');
        assert(spec_decimal_digit((n % 10) as nat) != '@');
        assert(spec_decimal_digit((n % 10) as nat) != '~');
        assert(spec_decimal_digit((n % 10) as nat) != '/');
        assert forall|i: int|
            0 <= i < spec_decimal_fixed(n, width).len()
        implies spec_decimal_fixed(n, width)[i] != '_'
            && spec_decimal_fixed(n, width)[i] != '@'
            && spec_decimal_fixed(n, width)[i] != '~'
            && spec_decimal_fixed(n, width)[i] != '/' by {
            if i < spec_decimal_fixed(
                n / 10,
                (width - 1) as nat,
            ).len() {
                assert(spec_decimal_fixed(n, width)[i]
                    == spec_decimal_fixed(
                        n / 10,
                        (width - 1) as nat,
                    )[i]);
            } else {
                assert(i == spec_decimal_fixed(
                    n / 10,
                    (width - 1) as nat,
                ).len());
            }
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_encoded_byte_excludes_delimiters(b: u8)
    ensures
        spec_excludes(spec_encode_key_byte(b), '_'),
        spec_excludes(spec_encode_key_byte(b), '@'),
        spec_excludes(spec_encode_key_byte(b), '~'),
        spec_excludes(spec_encode_key_byte(b), '/'),
        spec_excludes(spec_encode_key_byte(b), ':'),
{
    if spec_safe_key_byte(b) {
        assert(b != b'_');
        assert(b != b'@');
        assert(b != b'~');
        assert(b != b'/');
        assert(b != b':');
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_encode_key_bytes_excludes_delimiters(bytes: Seq<u8>)
    ensures
        spec_excludes(spec_encode_key_bytes(bytes), '_'),
        spec_excludes(spec_encode_key_bytes(bytes), '@'),
        spec_excludes(spec_encode_key_bytes(bytes), '~'),
        spec_excludes(spec_encode_key_bytes(bytes), '/'),
        spec_excludes(spec_encode_key_bytes(bytes), ':'),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        lemma_encoded_byte_excludes_delimiters(bytes[0]);
        lemma_encode_key_bytes_excludes_delimiters(bytes.drop_first());
        assert forall|i: int|
            0 <= i < spec_encode_key_bytes(bytes).len()
        implies spec_encode_key_bytes(bytes)[i] != '_'
            && spec_encode_key_bytes(bytes)[i] != '@'
            && spec_encode_key_bytes(bytes)[i] != '~'
            && spec_encode_key_bytes(bytes)[i] != '/'
            && spec_encode_key_bytes(bytes)[i] != ':' by {
            if i < spec_encode_key_byte(bytes[0]).len() {
                assert(spec_encode_key_bytes(bytes)[i]
                    == spec_encode_key_byte(bytes[0])[i]);
            } else {
                let j = i - spec_encode_key_byte(bytes[0]).len();
                assert(0 <= j
                    < spec_encode_key_bytes(bytes.drop_first()).len());
                assert(spec_encode_key_bytes(bytes)[i]
                    == spec_encode_key_bytes(bytes.drop_first())[j]);
            }
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_encode_key_excludes_delimiters(text: Seq<char>)
    ensures
        spec_excludes(spec_encode_key(text), '_'),
        spec_excludes(spec_encode_key(text), '@'),
        spec_excludes(spec_encode_key(text), '~'),
        spec_excludes(spec_encode_key(text), '/'),
        spec_excludes(spec_encode_key(text), ':'),
{
    lemma_encode_key_bytes_excludes_delimiters(
        vstd::utf8::encode_utf8(text),
    );
}

#[verifier::spinoff_prover]
pub proof fn lemma_delimited_injective(
    left: Seq<char>,
    right: Seq<char>,
    left_tail: Seq<char>,
    right_tail: Seq<char>,
    delimiter: char,
)
    requires
        spec_excludes(left, delimiter),
        spec_excludes(right, delimiter),
        left.push(delimiter) + left_tail
            == right.push(delimiter) + right_tail,
    ensures
        left == right,
        left_tail == right_tail,
    decreases left.len() + right.len(),
{
    if left.len() == 0 {
        if right.len() > 0 {
            assert((left.push(delimiter) + left_tail)[0] == delimiter);
            assert((right.push(delimiter) + right_tail)[0] == right[0]);
            assert(right[0] != delimiter);
            assert(false);
        }
        assert(left.push(delimiter).len() == 1);
        assert(right.push(delimiter).len() == 1);
        assert((left.push(delimiter) + left_tail).skip(1)
            == left_tail);
        assert((right.push(delimiter) + right_tail).skip(1)
            == right_tail);
    } else if right.len() == 0 {
        assert((right.push(delimiter) + right_tail)[0] == delimiter);
        assert((left.push(delimiter) + left_tail)[0] == left[0]);
        assert(left[0] != delimiter);
        assert(false);
    } else {
        assert((left.push(delimiter) + left_tail)[0] == left[0]);
        assert((right.push(delimiter) + right_tail)[0] == right[0]);
        assert(left[0] == right[0]);
        assert(spec_excludes(left.drop_first(), delimiter));
        assert(spec_excludes(right.drop_first(), delimiter));
        assert((left.push(delimiter) + left_tail).drop_first()
            == left.drop_first().push(delimiter) + left_tail);
        assert((right.push(delimiter) + right_tail).drop_first()
            == right.drop_first().push(delimiter) + right_tail);
        lemma_delimited_injective(
            left.drop_first(),
            right.drop_first(),
            left_tail,
            right_tail,
            delimiter,
        );
        assert(left =~= seq![left[0]] + left.drop_first());
        assert(right =~= seq![right[0]] + right.drop_first());
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_excludes_concat(
    left: Seq<char>,
    right: Seq<char>,
    delimiter: char,
)
    requires
        spec_excludes(left, delimiter),
        spec_excludes(right, delimiter),
    ensures
        spec_excludes(left + right, delimiter),
{
    assert forall|i: int| 0 <= i < (left + right).len()
    implies (left + right)[i] != delimiter by {
        if i < left.len() {
            assert((left + right)[i] == left[i]);
        } else {
            assert((left + right)[i] == right[i - left.len()]);
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_excludes_push(
    text: Seq<char>,
    added: char,
    delimiter: char,
)
    requires
        spec_excludes(text, delimiter),
        added != delimiter,
    ensures
        spec_excludes(text.push(added), delimiter),
{
    assert forall|i: int| 0 <= i < text.push(added).len()
    implies text.push(added)[i] != delimiter by {
        if i < text.len() {
            assert(text.push(added)[i] == text[i]);
        } else {
            assert(i == text.len());
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_last_segment_after_slash(
    prefix: Seq<char>,
    name: Seq<char>,
)
    requires
        prefix.len() > 0,
        prefix.last() == '/',
        spec_excludes(name, '/'),
    ensures
        spec_last_segment(prefix + name) == name,
    decreases name.len(),
{
    if name.len() == 0 {
        assert(prefix + name == prefix);
    } else {
        assert(spec_excludes(name.drop_last(), '/'));
        lemma_last_segment_after_slash(prefix, name.drop_last());
        assert((prefix + name).last() == name.last());
        assert((prefix + name).last() != '/');
        assert((prefix + name).drop_last()
            == prefix + name.drop_last());
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_last_segment_slash_free(name: Seq<char>)
    requires
        spec_excludes(name, '/'),
    ensures
        spec_last_segment(name) == name,
    decreases name.len(),
{
    if name.len() > 0 {
        assert(spec_excludes(name.drop_last(), '/'));
        lemma_last_segment_slash_free(name.drop_last());
        assert(name.last() != '/');
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_workflow_key_injective(
    prefix: Seq<char>,
    left: Seq<char>,
    right: Seq<char>,
)
    requires
        spec_doc_key(prefix, left) == spec_doc_key(prefix, right),
    ensures
        left == right,
{
    let base = prefix + "wf/"@;
    assert(spec_doc_key(prefix, left).skip(base.len() as int)
        == spec_encode_key(left));
    assert(spec_doc_key(prefix, right).skip(base.len() as int)
        == spec_encode_key(right));
    lemma_encode_key_injective(left, right);
}

#[verifier::spinoff_prover]
pub proof fn lemma_schedule_key_injective(
    prefix: Seq<char>,
    left: Seq<char>,
    right: Seq<char>,
)
    requires
        spec_sched_key(prefix, left) == spec_sched_key(prefix, right),
    ensures
        left == right,
{
    let base = prefix + "sched/"@;
    assert(spec_sched_key(prefix, left).skip(base.len() as int)
        == spec_encode_key(left));
    assert(spec_sched_key(prefix, right).skip(base.len() as int)
        == spec_encode_key(right));
    lemma_encode_key_injective(left, right);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn lemma_bucket_prefix_injective(
    prefix: Seq<char>,
    left: u64,
    right: u64,
)
    requires
        spec_bucket_prefix(prefix, left)
            == spec_bucket_prefix(prefix, right),
    ensures
        left == right,
{
    let base = spec_timer_prefix(prefix);
    lemma_decimal_fixed_len(left, 20);
    lemma_decimal_fixed_len(right, 20);
    assert(spec_bucket_prefix(prefix, left)
        .skip(base.len() as int).take(20)
        == spec_decimal20(left));
    assert(spec_bucket_prefix(prefix, right)
        .skip(base.len() as int).take(20)
        == spec_decimal20(right));
    lemma_decimal20_injective(left, right);
}

#[verifier::spinoff_prover]
pub proof fn lemma_parse_bucket_prefix_constructor(
    prefix: Seq<char>,
    bucket: u64,
)
    ensures
        spec_parse_bucket_prefix(
            prefix,
            spec_bucket_prefix(prefix, bucket),
        ) == Some(bucket),
{
    reveal(spec_parse_bucket_prefix);
    let parsed = choose|candidate: u64|
        spec_bucket_prefix(prefix, bucket)
            == spec_bucket_prefix(prefix, candidate);
    lemma_bucket_prefix_injective(prefix, bucket, parsed);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn lemma_timer_key_for_injective(
    prefix: Seq<char>,
    bucket_ms: u64,
    left_target: Seq<char>,
    left_deadline: u64,
    left_token: u64,
    left_by: Seq<char>,
    right_target: Seq<char>,
    right_deadline: u64,
    right_token: u64,
    right_by: Seq<char>,
)
    requires
        spec_excludes(left_target, '@'),
        spec_excludes(right_target, '@'),
        spec_timer_key_for(
            prefix,
            bucket_ms,
            left_target,
            left_deadline,
            left_token,
            left_by,
        ) == spec_timer_key_for(
            prefix,
            bucket_ms,
            right_target,
            right_deadline,
            right_token,
            right_by,
        ),
    ensures
        left_target == right_target,
        left_deadline == right_deadline,
        left_token == right_token,
        left_by == right_by,
{
    lemma_decimal_fixed_len(
        spec_bucket_of(left_deadline, bucket_ms),
        20,
    );
    lemma_decimal_fixed_len(
        spec_bucket_of(right_deadline, bucket_ms),
        20,
    );
    lemma_decimal_fixed_len(left_deadline, 20);
    lemma_decimal_fixed_len(right_deadline, 20);
    lemma_hex_fixed_len(left_token, 16);
    lemma_hex_fixed_len(right_token, 16);
    let base = spec_timer_prefix(prefix);
    let left_suffix = spec_timer_key_for(
        prefix,
        bucket_ms,
        left_target,
        left_deadline,
        left_token,
        left_by,
    ).skip(base.len() as int);
    let right_suffix = spec_timer_key_for(
        prefix,
        bucket_ms,
        right_target,
        right_deadline,
        right_token,
        right_by,
    ).skip(base.len() as int);
    assert(left_suffix == right_suffix);
    assert(left_suffix.skip(21).take(20)
        == spec_decimal20(left_deadline));
    assert(right_suffix.skip(21).take(20)
        == spec_decimal20(right_deadline));
    lemma_decimal20_injective(left_deadline, right_deadline);
    let left_payload = left_suffix.skip(42);
    let right_payload = right_suffix.skip(42);
    assert(left_payload == right_payload);
    assert(left_payload
        == left_target.push('@')
            + spec_hex16(left_token).push('~')
            + spec_encode_key(left_by));
    assert(right_payload
        == right_target.push('@')
            + spec_hex16(right_token).push('~')
            + spec_encode_key(right_by));
    assert(left_target.push('@')
        + (spec_hex16(left_token).push('~')
            + spec_encode_key(left_by))
        =~= left_payload);
    assert(right_target.push('@')
        + (spec_hex16(right_token).push('~')
            + spec_encode_key(right_by))
        =~= right_payload);
    lemma_delimited_injective(
        left_target,
        right_target,
        spec_hex16(left_token).push('~') + spec_encode_key(left_by),
        spec_hex16(right_token).push('~') + spec_encode_key(right_by),
        '@',
    );
    lemma_hex_fixed_excludes_delimiters(left_token, 16);
    lemma_hex_fixed_excludes_delimiters(right_token, 16);
    lemma_delimited_injective(
        spec_hex16(left_token),
        spec_hex16(right_token),
        spec_encode_key(left_by),
        spec_encode_key(right_by),
        '~',
    );
    lemma_hex16_injective(left_token, right_token);
    lemma_encode_key_injective(left_by, right_by);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn lemma_timer_name_for_injective(
    left_target: Seq<char>,
    left_deadline: u64,
    left_token: u64,
    left_by: Seq<char>,
    right_target: Seq<char>,
    right_deadline: u64,
    right_token: u64,
    right_by: Seq<char>,
)
    requires
        spec_excludes(left_target, '@'),
        spec_excludes(right_target, '@'),
        spec_timer_name_for(
            left_target,
            left_deadline,
            left_token,
            left_by,
        ) == spec_timer_name_for(
            right_target,
            right_deadline,
            right_token,
            right_by,
        ),
    ensures
        left_target == right_target,
        left_deadline == right_deadline,
        left_token == right_token,
        left_by == right_by,
{
    lemma_decimal_fixed_len(left_deadline, 20);
    lemma_decimal_fixed_len(right_deadline, 20);
    assert(spec_timer_name_for(
        left_target,
        left_deadline,
        left_token,
        left_by,
    ).take(20) == spec_decimal20(left_deadline));
    assert(spec_timer_name_for(
        right_target,
        right_deadline,
        right_token,
        right_by,
    ).take(20) == spec_decimal20(right_deadline));
    lemma_decimal20_injective(left_deadline, right_deadline);
    let prefix = Seq::<char>::empty();
    assert(spec_timer_key_for(
        prefix,
        1,
        left_target,
        left_deadline,
        left_token,
        left_by,
    ) == spec_bucket_prefix(
        prefix,
        spec_bucket_of(left_deadline, 1),
    ) + spec_timer_name_for(
        left_target,
        left_deadline,
        left_token,
        left_by,
    ));
    assert(spec_timer_key_for(
        prefix,
        1,
        right_target,
        right_deadline,
        right_token,
        right_by,
    ) == spec_bucket_prefix(
        prefix,
        spec_bucket_of(right_deadline, 1),
    ) + spec_timer_name_for(
        right_target,
        right_deadline,
        right_token,
        right_by,
    ));
    lemma_timer_key_for_injective(
        prefix,
        1,
        left_target,
        left_deadline,
        left_token,
        left_by,
        right_target,
        right_deadline,
        right_token,
        right_by,
    );
}

/// A physical origin-timer key identifies every component of the arm.
#[verifier::spinoff_prover]
pub proof fn lemma_timer_key_injective(
    prefix: Seq<char>,
    bucket_ms: u64,
    left_target: Seq<char>,
    left_deadline: u64,
    left_token: u64,
    left_by: Seq<char>,
    right_target: Seq<char>,
    right_deadline: u64,
    right_token: u64,
    right_by: Seq<char>,
)
    requires
        spec_timer_key(
            prefix,
            bucket_ms,
            left_target,
            left_deadline,
            left_token,
            left_by,
        ) == spec_timer_key(
            prefix,
            bucket_ms,
            right_target,
            right_deadline,
            right_token,
            right_by,
        ),
    ensures
        left_target == right_target,
        left_deadline == right_deadline,
        left_token == right_token,
        left_by == right_by,
{
    lemma_encode_key_excludes_delimiters(left_target);
    lemma_encode_key_excludes_delimiters(right_target);
    lemma_timer_key_for_injective(
        prefix,
        bucket_ms,
        spec_encode_key(left_target),
        left_deadline,
        left_token,
        left_by,
        spec_encode_key(right_target),
        right_deadline,
        right_token,
        right_by,
    );
    lemma_encode_key_injective(left_target, right_target);
}

#[verifier::spinoff_prover]
pub proof fn lemma_schedule_timer_key_injective(
    prefix: Seq<char>,
    bucket_ms: u64,
    left_id: Seq<char>,
    left_deadline: u64,
    left_token: u64,
    left_by: Seq<char>,
    right_id: Seq<char>,
    right_deadline: u64,
    right_token: u64,
    right_by: Seq<char>,
)
    requires
        spec_sched_timer_key(
            prefix,
            bucket_ms,
            left_id,
            left_deadline,
            left_token,
            left_by,
        ) == spec_sched_timer_key(
            prefix,
            bucket_ms,
            right_id,
            right_deadline,
            right_token,
            right_by,
        ),
    ensures
        left_id == right_id,
        left_deadline == right_deadline,
        left_token == right_token,
        left_by == right_by,
{
    lemma_encode_key_excludes_delimiters(left_id);
    lemma_encode_key_excludes_delimiters(right_id);
    assert(spec_excludes("sched:"@, '@')) by (compute);
    lemma_excludes_concat("sched:"@, spec_encode_key(left_id), '@');
    lemma_excludes_concat("sched:"@, spec_encode_key(right_id), '@');
    lemma_timer_key_for_injective(
        prefix,
        bucket_ms,
        "sched:"@ + spec_encode_key(left_id),
        left_deadline,
        left_token,
        left_by,
        "sched:"@ + spec_encode_key(right_id),
        right_deadline,
        right_token,
        right_by,
    );
    assert(("sched:"@ + spec_encode_key(left_id)).skip(6)
        == spec_encode_key(left_id)) by (compute);
    assert(("sched:"@ + spec_encode_key(right_id)).skip(6)
        == spec_encode_key(right_id)) by (compute);
    lemma_encode_key_injective(left_id, right_id);
}

#[verifier::spinoff_prover]
pub proof fn lemma_origin_schedule_timer_keys_separated(
    prefix: Seq<char>,
    bucket_ms: u64,
    origin: Seq<char>,
    origin_deadline: u64,
    origin_token: u64,
    origin_by: Seq<char>,
    schedule: Seq<char>,
    schedule_deadline: u64,
    schedule_token: u64,
    schedule_by: Seq<char>,
)
    ensures
        spec_timer_key(
            prefix,
            bucket_ms,
            origin,
            origin_deadline,
            origin_token,
            origin_by,
        ) != spec_sched_timer_key(
            prefix,
            bucket_ms,
            schedule,
            schedule_deadline,
            schedule_token,
            schedule_by,
        ),
{
    lemma_encode_key_excludes_delimiters(origin);
    lemma_encode_key_excludes_delimiters(schedule);
    assert(spec_excludes("sched:"@, '@')) by (compute);
    lemma_excludes_concat("sched:"@, spec_encode_key(schedule), '@');
    if spec_timer_key(
        prefix,
        bucket_ms,
        origin,
        origin_deadline,
        origin_token,
        origin_by,
    ) == spec_sched_timer_key(
        prefix,
        bucket_ms,
        schedule,
        schedule_deadline,
        schedule_token,
        schedule_by,
    ) {
        lemma_timer_key_for_injective(
            prefix,
            bucket_ms,
            spec_encode_key(origin),
            origin_deadline,
            origin_token,
            origin_by,
            "sched:"@ + spec_encode_key(schedule),
            schedule_deadline,
            schedule_token,
            schedule_by,
        );
        assert(("sched:"@ + spec_encode_key(schedule))[5] == ':')
            by (compute);
        assert(spec_encode_key(origin)[5] == ':');
        assert(spec_encode_key(origin).len() > 5);
        assert(spec_encode_key(origin)[5] != ':');
        assert(false);
    }
}

} // verus!

#[cfg(feature = "key-parser-proofs")]
pub mod parser {
use super::*;

verus! {

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn lemma_timer_entry_name_injective(
    left: TimerEntrySpec,
    right: TimerEntrySpec,
)
    requires
        spec_timer_entry_name(left) == spec_timer_entry_name(right),
    ensures
        left == right,
{
    match (left, right) {
        (
            TimerEntrySpec::Origin {
                deadline: left_deadline,
                origin: left_target,
                token: left_token,
                by: left_by,
            },
            TimerEntrySpec::Origin {
                deadline: right_deadline,
                origin: right_target,
                token: right_token,
                by: right_by,
            },
        ) => {
            lemma_encode_key_excludes_delimiters(left_target);
            lemma_encode_key_excludes_delimiters(right_target);
            lemma_timer_name_for_injective(
                spec_encode_key(left_target),
                left_deadline,
                left_token,
                left_by,
                spec_encode_key(right_target),
                right_deadline,
                right_token,
                right_by,
            );
            lemma_encode_key_injective(left_target, right_target);
        },
        (
            TimerEntrySpec::Schedule {
                deadline: left_deadline,
                id: left_target,
                token: left_token,
                by: left_by,
            },
            TimerEntrySpec::Schedule {
                deadline: right_deadline,
                id: right_target,
                token: right_token,
                by: right_by,
            },
        ) => {
            lemma_encode_key_excludes_delimiters(left_target);
            lemma_encode_key_excludes_delimiters(right_target);
            assert(spec_excludes("sched:"@, '@')) by (compute);
            lemma_excludes_concat(
                "sched:"@,
                spec_encode_key(left_target),
                '@',
            );
            lemma_excludes_concat(
                "sched:"@,
                spec_encode_key(right_target),
                '@',
            );
            lemma_timer_name_for_injective(
                "sched:"@ + spec_encode_key(left_target),
                left_deadline,
                left_token,
                left_by,
                "sched:"@ + spec_encode_key(right_target),
                right_deadline,
                right_token,
                right_by,
            );
            assert(("sched:"@ + spec_encode_key(left_target)).skip(6)
                == spec_encode_key(left_target));
            assert(("sched:"@ + spec_encode_key(right_target)).skip(6)
                == spec_encode_key(right_target));
            lemma_encode_key_injective(left_target, right_target);
        },
        (
            TimerEntrySpec::Origin {
                deadline: left_deadline,
                origin: left_target,
                token: left_token,
                by: left_by,
            },
            TimerEntrySpec::Schedule {
                deadline: right_deadline,
                id: right_target,
                token: right_token,
                by: right_by,
            },
        ) => {
            lemma_encode_key_excludes_delimiters(left_target);
            lemma_encode_key_excludes_delimiters(right_target);
            assert(spec_excludes("sched:"@, '@')) by (compute);
            lemma_excludes_concat(
                "sched:"@,
                spec_encode_key(right_target),
                '@',
            );
            lemma_timer_name_for_injective(
                spec_encode_key(left_target),
                left_deadline,
                left_token,
                left_by,
                "sched:"@ + spec_encode_key(right_target),
                right_deadline,
                right_token,
                right_by,
            );
            assert(spec_encode_key(left_target).len() > 5);
            assert(spec_encode_key(left_target)[5] == ':');
            assert(spec_encode_key(left_target)[5] != ':');
            assert(false);
        },
        (
            TimerEntrySpec::Schedule {
                deadline: left_deadline,
                id: left_target,
                token: left_token,
                by: left_by,
            },
            TimerEntrySpec::Origin {
                deadline: right_deadline,
                origin: right_target,
                token: right_token,
                by: right_by,
            },
        ) => {
            lemma_encode_key_excludes_delimiters(left_target);
            lemma_encode_key_excludes_delimiters(right_target);
            assert(spec_excludes("sched:"@, '@')) by (compute);
            lemma_excludes_concat(
                "sched:"@,
                spec_encode_key(left_target),
                '@',
            );
            lemma_timer_name_for_injective(
                "sched:"@ + spec_encode_key(left_target),
                left_deadline,
                left_token,
                left_by,
                spec_encode_key(right_target),
                right_deadline,
                right_token,
                right_by,
            );
            assert(spec_encode_key(right_target).len() > 5);
            assert(spec_encode_key(right_target)[5] == ':');
            assert(spec_encode_key(right_target)[5] != ':');
            assert(false);
        },
    }
}

pub proof fn lemma_timer_name_for_excludes_slash(
    target: Seq<char>,
    deadline: u64,
    token: u64,
    by: Seq<char>,
)
    requires
        spec_excludes(target, '/'),
    ensures
        spec_excludes(
            spec_timer_name_for(target, deadline, token, by),
            '/',
        ),
{
    lemma_decimal_fixed_excludes_delimiters(deadline, 20);
    lemma_excludes_push(spec_decimal20(deadline), '_', '/');
    lemma_excludes_concat(
        spec_decimal20(deadline).push('_'),
        target,
        '/',
    );
    lemma_excludes_push(
        spec_decimal20(deadline).push('_') + target,
        '@',
        '/',
    );
    lemma_hex_fixed_excludes_delimiters(token, 16);
    lemma_excludes_concat(
        (spec_decimal20(deadline).push('_') + target).push('@'),
        spec_hex16(token),
        '/',
    );
    lemma_excludes_push(
        (spec_decimal20(deadline).push('_') + target).push('@')
            + spec_hex16(token),
        '~',
        '/',
    );
    lemma_encode_key_excludes_delimiters(by);
    lemma_excludes_concat(
        ((spec_decimal20(deadline).push('_') + target).push('@')
            + spec_hex16(token)).push('~'),
        spec_encode_key(by),
        '/',
    );
}

pub proof fn lemma_timer_entry_name_excludes_slash(
    entry: TimerEntrySpec,
)
    ensures
        spec_excludes(spec_timer_entry_name(entry), '/'),
{
    match entry {
        TimerEntrySpec::Origin {
            deadline,
            origin,
            token,
            by,
        } => {
            lemma_encode_key_excludes_delimiters(origin);
            lemma_timer_name_for_excludes_slash(
                spec_encode_key(origin),
                deadline,
                token,
                by,
            );
        },
        TimerEntrySpec::Schedule {
            deadline,
            id,
            token,
            by,
        } => {
            lemma_encode_key_excludes_delimiters(id);
            assert(spec_excludes("sched:"@, '/')) by (compute);
            lemma_excludes_concat(
                "sched:"@,
                spec_encode_key(id),
                '/',
            );
            lemma_timer_name_for_excludes_slash(
                "sched:"@ + spec_encode_key(id),
                deadline,
                token,
                by,
            );
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_parse_timer_entry_name(entry: TimerEntrySpec)
    ensures
        spec_parse_timer_key(spec_timer_entry_name(entry))
            == Some(entry),
{
    reveal(spec_parse_timer_key);
    lemma_timer_entry_name_excludes_slash(entry);
    lemma_last_segment_slash_free(spec_timer_entry_name(entry));
    let parsed = choose|candidate: TimerEntrySpec|
        spec_last_segment(spec_timer_entry_name(entry))
            == spec_timer_entry_name(candidate);
    lemma_timer_entry_name_injective(entry, parsed);
}

#[verifier::spinoff_prover]
pub proof fn lemma_parse_origin_timer_constructor(
    prefix: Seq<char>,
    bucket_ms: u64,
    origin: Seq<char>,
    deadline: u64,
    token: u64,
    by: Seq<char>,
)
    ensures
        spec_parse_timer_key(spec_timer_key(
            prefix,
            bucket_ms,
            origin,
            deadline,
            token,
            by,
        )) == Some(TimerEntrySpec::Origin {
            deadline,
            origin,
            token,
            by,
        }),
{
    reveal(spec_parse_timer_key);
    let entry = TimerEntrySpec::Origin {
        deadline,
        origin,
        token,
        by,
    };
    lemma_timer_entry_name_excludes_slash(entry);
    let path = spec_bucket_prefix(
        prefix,
        spec_bucket_of(deadline, bucket_ms),
    );
    assert(path.len() > 0);
    assert(path.last() == '/');
    assert(spec_timer_key(
        prefix,
        bucket_ms,
        origin,
        deadline,
        token,
        by,
    ) == path + spec_timer_entry_name(entry));
    lemma_last_segment_after_slash(path, spec_timer_entry_name(entry));
    let parsed = choose|candidate: TimerEntrySpec|
        spec_last_segment(spec_timer_key(
            prefix,
            bucket_ms,
            origin,
            deadline,
            token,
            by,
        )) == spec_timer_entry_name(candidate);
    lemma_timer_entry_name_injective(entry, parsed);
}

#[verifier::spinoff_prover]
pub proof fn lemma_parse_schedule_timer_constructor(
    prefix: Seq<char>,
    bucket_ms: u64,
    id: Seq<char>,
    deadline: u64,
    token: u64,
    by: Seq<char>,
)
    ensures
        spec_parse_timer_key(spec_sched_timer_key(
            prefix,
            bucket_ms,
            id,
            deadline,
            token,
            by,
        )) == Some(TimerEntrySpec::Schedule {
            deadline,
            id,
            token,
            by,
        }),
{
    reveal(spec_parse_timer_key);
    let entry = TimerEntrySpec::Schedule {
        deadline,
        id,
        token,
        by,
    };
    lemma_timer_entry_name_excludes_slash(entry);
    let path = spec_bucket_prefix(
        prefix,
        spec_bucket_of(deadline, bucket_ms),
    );
    assert(path.len() > 0);
    assert(path.last() == '/');
    assert(spec_sched_timer_key(
        prefix,
        bucket_ms,
        id,
        deadline,
        token,
        by,
    ) == path + spec_timer_entry_name(entry));
    lemma_last_segment_after_slash(path, spec_timer_entry_name(entry));
    let parsed = choose|candidate: TimerEntrySpec|
        spec_last_segment(spec_sched_timer_key(
            prefix,
            bucket_ms,
            id,
            deadline,
            token,
            by,
        )) == spec_timer_entry_name(candidate);
    lemma_timer_entry_name_injective(entry, parsed);
}

} // verus!
} // mod parser
} // mod algebra

verus! {

pub proof fn lemma_fixed_namespaces_separated(
    prefix: Seq<char>,
    workflow: Seq<char>,
    schedule: Seq<char>,
    node: Seq<char>,
    timer_suffix: Seq<char>,
)
    ensures
        spec_doc_key(prefix, workflow)
            != spec_sched_key(prefix, schedule),
        spec_doc_key(prefix, workflow)
            != spec_node_key(prefix, node),
        spec_sched_key(prefix, schedule)
            != spec_node_key(prefix, node),
        spec_members_key(prefix)
            != spec_doc_key(prefix, workflow),
        spec_members_key(prefix)
            != spec_sched_key(prefix, schedule),
        spec_members_key(prefix)
            != spec_node_key(prefix, node),
        spec_timer_prefix(prefix) + timer_suffix
            != spec_doc_key(prefix, workflow),
        spec_timer_prefix(prefix) + timer_suffix
            != spec_sched_key(prefix, schedule),
        spec_timer_prefix(prefix) + timer_suffix
            != spec_node_key(prefix, node),
        spec_timer_prefix(prefix) + timer_suffix
            != spec_members_key(prefix),
{
    reveal_strlit("wf/");
    reveal_strlit("sched/");
    reveal_strlit("nodes/");
    reveal_strlit("members");
    reveal_strlit("t/");
    assert((spec_doc_key(prefix, workflow))[prefix.len() as int] == 'w');
    assert((spec_sched_key(prefix, schedule))[prefix.len() as int] == 's');
    assert((spec_node_key(prefix, node))[prefix.len() as int] == 'n');
    assert((spec_members_key(prefix))[prefix.len() as int] == 'm');
    assert((spec_timer_prefix(prefix) + timer_suffix)[prefix.len() as int]
        == 't');
}

pub proof fn lemma_timer_key_is_not_document_key(
    prefix: Seq<char>,
    bucket_ms: u64,
    origin: Seq<char>,
    at: u64,
    token: u64,
    by: Seq<char>,
    document: Seq<char>,
    schedule: bool,
)
    ensures
        spec_timer_key(prefix, bucket_ms, origin, at, token, by)
            != if schedule {
                spec_sched_key(prefix, document)
            } else {
                spec_doc_key(prefix, document)
            },
{
    let key = spec_timer_key(prefix, bucket_ms, origin, at, token, by);
    let timer_suffix = key.skip(spec_timer_prefix(prefix).len() as int);
    assert(key == spec_timer_prefix(prefix) + timer_suffix);
    lemma_fixed_namespaces_separated(
        prefix,
        document,
        document,
        Seq::empty(),
        timer_suffix,
    );
}

pub proof fn lemma_schedule_timer_key_is_not_document_key(
    prefix: Seq<char>,
    bucket_ms: u64,
    id: Seq<char>,
    at: u64,
    token: u64,
    by: Seq<char>,
    document: Seq<char>,
    schedule: bool,
)
    ensures
        spec_sched_timer_key(prefix, bucket_ms, id, at, token, by)
            != if schedule {
                spec_sched_key(prefix, document)
            } else {
                spec_doc_key(prefix, document)
            },
{
    let key = spec_sched_timer_key(prefix, bucket_ms, id, at, token, by);
    let timer_suffix = key.skip(spec_timer_prefix(prefix).len() as int);
    assert(key == spec_timer_prefix(prefix) + timer_suffix);
    lemma_fixed_namespaces_separated(
        prefix,
        document,
        document,
        Seq::empty(),
        timer_suffix,
    );
}

fn hex_value(c: char) -> (r: Option<u8>)
    ensures
        r == spec_hex_value(c),
{
    if '0' <= c && c <= '9' {
        Some((c as u32 - '0' as u32) as u8)
    } else if 'A' <= c && c <= 'F' {
        Some((c as u32 - 'A' as u32 + 10) as u8)
    } else if 'a' <= c && c <= 'f' {
        Some((c as u32 - 'a' as u32 + 10) as u8)
    } else {
        None
    }
}

#[cfg(any())]
fn concat_bytes(mut left: Vec<u8>, right: Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == left@ + right@,
{
    let ghost original = left@;
    let mut i: usize = 0;
    while i < right.len()
        invariant
            i <= right.len(),
            left@ == original + right@.take(i as int),
        decreases right.len() - i,
    {
        left.push(right[i]);
        proof {
            assert(right@.take(i + 1)
                =~= right@.take(i as int).push(right@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(right@.take(right.len() as int) =~= right@);
    }
    left
}

#[cfg(any())]
fn decode_key_bytes_at(s: &str, at: usize) -> (r: Option<Vec<u8>>)
    requires
        at <= s@.len(),
    ensures
        r.deep_view() == spec_decode_key_bytes(s@.skip(at as int)),
    decreases s@.len() - at,
{
    let len = s.unicode_len();
    if at == len {
        Some(Vec::new())
    } else {
        let c = s.get_char(at);
        if c == '%' {
            if at + 2 >= len {
                None
            } else {
                match (
                    hex_value(s.get_char(at + 1)),
                    hex_value(s.get_char(at + 2)),
                ) {
                    (Some(hi), Some(lo)) => {
                        match decode_key_bytes_at(s, at + 3) {
                            Some(rest) => {
                                let mut head = Vec::new();
                                head.push(((hi << 4) | lo) as u8);
                                Some(concat_bytes(head, rest))
                            },
                            None => None,
                        }
                    },
                    _ => None,
                }
            }
        } else {
            match decode_key_bytes_at(s, at + 1) {
                Some(rest) => {
                    let one = s.substring_char(at, at + 1);
                    let raw = one.as_bytes_vec();
                    proof {
                        assert(one@ == seq![c]);
                        assert(raw@
                            == vstd::utf8::encode_utf8(seq![c]));
                        assert(s@.skip(at as int).drop_first()
                            == s@.skip(at as int + 1));
                    }
                    Some(concat_bytes(raw, rest))
                },
                None => None,
            }
        }
    }
}

#[cfg(any())]
fn valid_utf8_at(bytes: &Vec<u8>, at: usize) -> (r: bool)
    requires
        at <= bytes.len(),
    ensures
        r == vstd::utf8::valid_utf8(bytes@.skip(at as int)),
    decreases bytes.len() - at,
{
    if at == bytes.len() {
        true
    } else {
        let b0 = bytes[at];
        let remaining = bytes.len() - at;
        if b0 <= 0x7f {
            valid_utf8_at(bytes, at + 1)
        } else if 0xc0 <= b0 && b0 <= 0xdf {
            if remaining < 2 {
                false
            } else {
                let b1 = bytes[at + 1];
                let scalar = (((b0 & 0x1f) as u32) << 6)
                    | ((b1 & 0x3f) as u32);
                if !(0x80 <= b1 && b1 <= 0xbf)
                    || scalar < 0x80
                {
                    false
                } else {
                    valid_utf8_at(bytes, at + 2)
                }
            }
        } else if 0xe0 <= b0 && b0 <= 0xef {
            if remaining < 3 {
                false
            } else {
                let b1 = bytes[at + 1];
                let b2 = bytes[at + 2];
                let scalar = (((b0 & 0x0f) as u32) << 12)
                    | (((b1 & 0x3f) as u32) << 6)
                    | ((b2 & 0x3f) as u32);
                if !(0x80 <= b1 && b1 <= 0xbf)
                    || !(0x80 <= b2 && b2 <= 0xbf)
                    || scalar < 0x800
                    || (0xd800 <= scalar && scalar <= 0xdfff)
                {
                    false
                } else {
                    valid_utf8_at(bytes, at + 3)
                }
            }
        } else if 0xf0 <= b0 && b0 <= 0xf7 {
            if remaining < 4 {
                false
            } else {
                let b1 = bytes[at + 1];
                let b2 = bytes[at + 2];
                let b3 = bytes[at + 3];
                let scalar = (((b0 & 0x07) as u32) << 18)
                    | (((b1 & 0x3f) as u32) << 12)
                    | (((b2 & 0x3f) as u32) << 6)
                    | ((b3 & 0x3f) as u32);
                if !(0x80 <= b1 && b1 <= 0xbf)
                    || !(0x80 <= b2 && b2 <= 0xbf)
                    || !(0x80 <= b3 && b3 <= 0xbf)
                    || scalar < 0x10000
                    || scalar > 0x10ffff
                {
                    false
                } else {
                    valid_utf8_at(bytes, at + 4)
                }
            }
        } else {
            false
        }
    }
}

pub assume_specification [text::decode_key](s: &str) -> (r: Option<String>)
    ensures
        r.deep_view() == spec_decode_key(s@);

pub fn decode_key(s: &str) -> (r: Option<String>)
    ensures
        r.deep_view() == spec_decode_key(s@),
{
    text::decode_key(s)
}

fn normalize_prefix(s: &str) -> (r: String)
    ensures
        r@ == spec_normalize_prefix(s@),
{
    let len = s.unicode_len();
    let mut out = String::new();
    out.push_str(s);
    if len == 0 || s.get_char(len - 1) == '/' {
        out
    } else {
        out.push('/');
        out
    }
}

fn starts_with_chars(text: &str, prefix: &str) -> (r: bool)
    ensures
        r == spec_starts_with_chars(text@, prefix@),
{
    let text_len = text.unicode_len();
    let prefix_len = prefix.unicode_len();
    assert(text_len as nat == text@.len());
    assert(prefix_len as nat == prefix@.len());
    if text_len < prefix_len {
        false
    } else {
        let mut i: usize = 0;
        while i < prefix_len
            invariant
                i <= prefix_len,
                i <= text_len,
                text_len as nat == text@.len(),
                prefix_len as nat == prefix@.len(),
                (i as int) <= prefix@.len(),
                (i as int) <= text@.len(),
                text_len >= prefix_len,
                forall|j: int| 0 <= j < (i as int) ==>
                    text@[j] == prefix@[j],
            decreases prefix_len - i,
        {
            assert((i as int) < text@.len());
            assert((i as int) < prefix@.len());
            if text.get_char(i) != prefix.get_char(i) {
                proof {
                    assert((i as int)
                        < text@.take(prefix@.len() as int).len());
                    assert(text@.take(prefix@.len() as int)[i as int]
                        == text@[i as int]);
                    assert(text@.take(prefix@.len() as int)
                        != prefix@);
                }
                return false;
            }
            i += 1;
        }
        assert(text@.take(prefix@.len() as int) =~= prefix@) by {
            assert forall|j: int| 0 <= j < prefix@.len()
            implies text@.take(prefix@.len() as int)[j]
                == prefix@[j] by {
                assert(text@.take(prefix@.len() as int)[j]
                    == text@[j]);
            }
        };
        true
    }
}

fn take_to_slash_at(text: &str, at: usize) -> (r: String)
    requires
        at <= text@.len(),
    ensures
        r@ == spec_take_to_slash(text@.skip(at as int)),
    decreases text@.len() - at,
{
    let len = text.unicode_len();
    if at == len || text.get_char(at) == '/' {
        String::new()
    } else {
        let mut out = String::new();
        out.push(text.get_char(at));
        let rest = take_to_slash_at(text, at + 1);
        out.push_str(rest.as_str());
        proof {
            assert(text@.skip(at as int).drop_first()
                == text@.skip(at as int + 1));
        }
        out
    }
}

fn class_of(prefix: &str, key: &str) -> (r: Option<String>)
    ensures
        r.deep_view() == spec_class_of(prefix@, key@),
{
    if starts_with_chars(key, prefix) {
        Some(take_to_slash_at(key, prefix.unicode_len()))
    } else {
        None
    }
}

fn node_of_key(prefix: &str, key: &str) -> (r: Option<String>)
    ensures
        r.deep_view() == spec_node_of_key(prefix@, key@),
{
    let node_prefix = crate::verified::text::concat(prefix, "nodes/");
    if starts_with_chars(key, node_prefix.as_str()) {
        let rest = key.substring_char(
            node_prefix.as_str().unicode_len(),
            key.unicode_len(),
        );
        decode_key(rest)
    } else {
        None
    }
}

fn parse_decimal_range(
    text: &str,
    at: usize,
    end: usize,
    acc: u64,
) -> (r: Option<u64>)
    requires
        at <= end <= text@.len(),
    ensures
        r == spec_decimal_value(
            text@.subrange(at as int, end as int),
            acc,
        ),
    decreases end - at,
{
    if at == end {
        Some(acc)
    } else {
        let c = text.get_char(at);
        if '0' <= c && c <= '9' {
            let digit = (c as u32 - '0' as u32) as u64;
            if acc <= (u64::MAX - digit) / 10 {
                let next = acc * 10 + digit;
                let result =
                    parse_decimal_range(text, at + 1, end, next);
                proof {
                    assert(text@.subrange(at as int, end as int)
                        .drop_first()
                        == text@.subrange(at as int + 1, end as int));
                }
                result
            } else {
                None
            }
        } else {
            None
        }
    }
}

fn parse_bucket_prefix(prefix: &str, p: &str) -> (r: Option<u64>)
    ensures
        r == spec_parse_bucket_prefix(prefix@, p@),
{
    let base = crate::verified::text::concat(prefix, "t/");
    let base_len = base.as_str().unicode_len();
    let p_len = p.unicode_len();
    if starts_with_chars(p, base.as_str())
        && base_len <= usize::MAX - 21
        && p_len == base_len + 21
        && p.get_char(p_len - 1) == '/'
    {
        parse_decimal_range(p, base_len, base_len + 20, 0)
    } else {
        None
    }
}

fn find_char_from(
    text: &str,
    needle: char,
    at: usize,
) -> (r: Option<usize>)
    requires
        at <= text@.len(),
    ensures
        match r {
            Some(found) => {
                &&& at <= found
                &&& (found as int) < text@.len()
                &&& spec_find_char(text@, needle, at as int)
                    == Some(found as int)
            },
            None =>
                spec_find_char(text@, needle, at as int) is None,
        },
    decreases text@.len() - at,
{
    let len = text.unicode_len();
    if at == len {
        None
    } else if text.get_char(at) == needle {
        Some(at)
    } else {
        find_char_from(text, needle, at + 1)
    }
}

fn parse_hex_range(
    text: &str,
    at: usize,
    end: usize,
    acc: u64,
) -> (r: Option<u64>)
    requires
        at <= end <= text@.len(),
    ensures
        r == spec_hex_value_acc(
            text@.subrange(at as int, end as int),
            acc,
        ),
    decreases end - at,
{
    if at == end {
        Some(acc)
    } else {
        assert((at as int) < text@.len());
        assert(text@.subrange(at as int, end as int)[0]
            == text@[at as int]);
        match hex_value(text.get_char(at)) {
            Some(digit) => {
                let next = acc.wrapping_mul(16)
                    .wrapping_add(digit as u64);
                let result =
                    parse_hex_range(text, at + 1, end, next);
                proof {
                    assert(text@.subrange(at as int, end as int)
                        .drop_first()
                        == text@.subrange(at as int + 1, end as int));
                }
                result
            },
            None => None,
        }
    }
}

fn timer_entry_name(entry: &TimerEntry) -> (r: String)
    ensures
        r@ == spec_timer_entry_name(entry.deep_view()),
{
    let mut out = decimal20(entry.deadline());
    out.push('_');
    match entry {
        TimerEntry::Origin { origin, .. } => {
            let encoded = encode_key(origin.as_str());
            out.push_str(encoded.as_str());
        },
        TimerEntry::Schedule { id, .. } => {
            out.push_str("sched:");
            let encoded = encode_key(id.as_str());
            out.push_str(encoded.as_str());
        },
    }
    out.push('@');
    let token = hex16(entry.token());
    out.push_str(token.as_str());
    out.push('~');
    let by = encode_key(entry.by().as_str());
    out.push_str(by.as_str());
    out
}

fn parse_timer_name(name: &str) -> (r: Option<TimerEntry>)
    ensures
        r.deep_view() == spec_parsed_timer_entry(name@),
{
    let len = name.unicode_len();
    assert(len as nat == name@.len());
    if len < 39 || name.get_char(20) != '_' {
        None
    } else {
        match (
            parse_decimal_range(name, 0, 20, 0),
            find_char_from(name, '@', 21),
        ) {
            (Some(deadline), Some(separator))
                if separator <= usize::MAX - 18
                    && separator + 18 <= len
                    && name.get_char(separator + 17) == '~' => {
                proof {
                    assert(spec_find_char(name@, '@', 21)
                        == Some(separator as int));
                    assert((separator as int) + 18 <= name@.len());
                    assert(name@[separator as int + 17] == '~');
                }
                match (
                    parse_hex_range(
                        name,
                        separator + 1,
                        separator + 17,
                        0,
                    ),
                    decode_key(name.substring_char(
                        separator + 18,
                        len,
                    )),
                ) {
                    (Some(token), Some(by)) => {
                        proof {
                            assert(21 <= separator);
                            assert(separator <= len);
                        }
                        let target = name.substring_char(21, separator);
                        proof {
                            assert(target@ == name@.subrange(
                                21,
                                separator as int,
                            ));
                        }
                        let candidate =
                            if starts_with_chars(target, "sched:") {
                                proof {
                                    reveal_strlit("sched:");
                                    assert("sched:"@.len() == 6);
                                    assert(target@.len() >= 6);
                                }
                                let encoded = target.substring_char(
                                    6,
                                    target.unicode_len(),
                                );
                                match decode_key(encoded) {
                                    Some(id) => Some(TimerEntry::Schedule {
                                        deadline,
                                        id,
                                        token,
                                        by,
                                    }),
                                    None => None,
                                }
                            } else {
                                match decode_key(target) {
                                    Some(origin) => Some(TimerEntry::Origin {
                                        deadline,
                                        origin,
                                        token,
                                        by,
                                    }),
                                    None => None,
                                }
                            };
                        match candidate {
                            Some(entry) => {
                                let canonical = timer_entry_name(&entry);
                                assert(canonical@
                                    == spec_timer_entry_name(
                                        entry.deep_view(),
                                    ));
                                if crate::verified::node::str_eq(
                                    canonical.as_str(),
                                    name,
                                ) {
                                    Some(entry)
                                } else {
                                    None
                                }
                            },
                            None => None,
                        }
                    },
                    _ => None,
                }
            },
            _ => None,
        }
    }
}

fn parse_timer_key(key: &str) -> (r: Option<TimerEntry>)
    ensures
        r.deep_view() == spec_parse_timer_key(key@),
{
    let name = last_segment(key);
    parse_timer_name(name.as_str())
}

fn last_segment_take(key: &str, len: usize) -> (r: String)
    requires
        len <= key@.len(),
    ensures
        r@ == spec_last_segment(key@.take(len as int)),
    decreases len,
{
    if len == 0 || key.get_char(len - 1) == '/' {
        proof {
            if len > 0 {
                assert(key@.take(len as int).last()
                    == key@[len as int - 1]);
            }
        }
        String::new()
    } else {
        let mut out = last_segment_take(key, len - 1);
        out.push(key.get_char(len - 1));
        proof {
            assert(key@.take(len as int).last()
                == key@[len as int - 1]);
            assert(key@.take(len as int).drop_last()
                == key@.take(len as int - 1));
        }
        out
    }
}

pub fn last_segment(key: &str) -> (r: String)
    ensures
        r@ == spec_last_segment(key@),
{
    let len = key.unicode_len();
    let out = last_segment_take(key, len);
    proof {
        assert(key@.take(len as int) == key@);
    }
    out
}

/// Percent-encode anything that is not safe and stable in a key.
fn upper_hex_digit(n: u8) -> (r: char)
    requires
        n < 16,
    ensures
        r == spec_upper_hex_digit(n),
{
    if n < 10 {
        (b'0' + n) as char
    } else {
        (b'A' + (n - 10)) as char
    }
}

fn decimal_digit(n: u64) -> (r: char)
    ensures
        r == spec_decimal_digit(n as nat),
{
    if n < 10 {
        (b'0' + n as u8) as char
    } else {
        '?'
    }
}

fn decimal_fixed(n: u64, width: usize) -> (r: String)
    ensures
        r@ == spec_decimal_fixed(n, width as nat),
    decreases width,
{
    if width == 0 {
        String::new()
    } else {
        let mut out = decimal_fixed(n / 10, width - 1);
        out.push(decimal_digit(n % 10));
        out
    }
}

fn decimal20(n: u64) -> (r: String)
    ensures
        r@ == spec_decimal20(n),
{
    decimal_fixed(n, 20)
}

fn lower_hex_digit(n: u64) -> (r: char)
    ensures
        r == spec_lower_hex_digit(n),
{
    if n < 10 {
        (b'0' + n as u8) as char
    } else if n < 16 {
        (b'a' + (n - 10) as u8) as char
    } else {
        '?'
    }
}

fn hex_fixed(n: u64, width: usize) -> (r: String)
    ensures
        r@ == spec_hex_fixed(n, width as nat),
    decreases width,
{
    if width == 0 {
        String::new()
    } else {
        let mut out = hex_fixed(n / 16, width - 1);
        out.push(lower_hex_digit(n % 16));
        out
    }
}

fn hex16(n: u64) -> (r: String)
    ensures
        r@ == spec_hex16(n),
{
    hex_fixed(n, 16)
}

pub fn encode_key(s: &str) -> (r: String)
    ensures
        r@ == spec_encode_key(s@),
{
    let bytes = s.as_bytes();
    let mut out = String::new();
    let mut i: usize = 0;
    while i < bytes.len()
        invariant
            i <= bytes.len(),
            out@ == spec_encode_key_bytes(bytes@.take(i as int)),
        decreases bytes.len() - i,
    {
        let b = bytes[i];
        let ghost before = out@;
        if (b'A' <= b && b <= b'Z')
            || (b'a' <= b && b <= b'z')
            || (b'0' <= b && b <= b'9')
            || b == b'.'
            || b == b'-'
        {
            proof {
                assert(spec_safe_key_byte(b));
                reveal_with_fuel(spec_encode_key_bytes, 2);
            }
            out.push(b as char);
            proof {
                assert(before + spec_encode_key_byte(b)
                    == out@);
            }
        } else {
            proof {
                assert(!spec_safe_key_byte(b));
                assert((b >> 4) < 16) by (bit_vector);
                assert((b & 0x0f) < 16) by (bit_vector);
                reveal_with_fuel(spec_encode_key_bytes, 2);
            }
            out.push('%');
            out.push(upper_hex_digit(b >> 4));
            out.push(upper_hex_digit(b & 0x0f));
            proof {
                assert(before + spec_encode_key_byte(b)
                    == out@);
            }
        }
        proof {
            assert(bytes@.take(i as int + 1)
                == bytes@.take(i as int).push(b));
            assert(bytes@.take(i as int).push(b)
                =~= bytes@.take(i as int) + seq![b]);
            lemma_encode_key_bytes_concat(
                bytes@.take(i as int),
                seq![b],
            );
            lemma_encode_key_bytes_cons(b, Seq::empty());
            assert(spec_encode_key_bytes(seq![b])
                == spec_encode_key_byte(b));
            assert(spec_encode_key_bytes(
                bytes@.take(i as int).push(b),
            ) == spec_encode_key_bytes(bytes@.take(i as int))
                + spec_encode_key_byte(b));
        }
        i += 1;
    }
    assert(i == bytes.len());
    assert(bytes@.take(i as int) == bytes@);
    assert(out@ == spec_encode_key_bytes(bytes@));
    assert(bytes@ == s.spec_bytes());
    assert(s.spec_bytes() == vstd::utf8::encode_utf8(s@));
    assert(bytes@ == vstd::utf8::encode_utf8(s@));
    assert(spec_encode_key(s@)
        == spec_encode_key_bytes(vstd::utf8::encode_utf8(s@)));
    out
}

/// FNV-1a: the hash `verified::node` proves against `hash`.
pub fn fnv1a(s: &str) -> (r: u64)
    ensures
        r as nat == crate::verified::node_spec::hash(s@),
{
    crate::verified::node::fnv1a(s)
}

/// The start of the bucket `at` falls in.
pub open spec fn spec_bucket_of(at: u64, bucket_ms: u64) -> u64 {
    let width = if bucket_ms < 1 { 1u64 } else { bucket_ms };
    ((at / width) * width) as u64
}

/// The start of the bucket `at` falls in. `bucket_ms` is at least 1, as
/// `KeySpace::new` stores it.
pub fn bucket_of(at: u64, bucket_ms: u64) -> (r: u64)
    ensures
        r == spec_bucket_of(at, bucket_ms),
{
    let width = if bucket_ms < 1 { 1 } else { bucket_ms };
    proof {
        let q = (at / width) as int;
        let w = width as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int, w);
        vstd::arithmetic::div_mod::lemma_mod_bound(at as int, w);
        assert(q * w == w * q) by (nonlinear_arith);
        assert(q * w <= at);
    }
    at / width * width
}

/// The version a body quotes, as an S3 ETag: the same bytes are the same version.
pub fn content_etag(body: &[u8]) -> (r: crate::types::Etag)
    ensures
        r == echod_concrete::store::spec_etag(body@),
{
    echod_concrete::content_etag(body)
}

/// The origin of an id: everything before the first `:`.
pub fn origin_of<'a>(id: &'a str) -> (r: &'a str)
    ensures
        r@ == echod_types::origin(id@),
{
    echod_types::origin_of(id)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn timer_key_for(
    prefix: &str,
    bucket_ms: u64,
    encoded_target: &str,
    at: u64,
    token: u64,
    by: &str,
) -> (r: String)
    ensures
        r@ == spec_timer_key_for(
            prefix@,
            bucket_ms,
            encoded_target@,
            at,
            token,
            by@,
        ),
{
    let bucket = bucket_of(at, bucket_ms);
    let bucket_text = decimal20(bucket);
    let deadline = decimal20(at);
    let token_text = hex16(token);
    let encoded_by = encode_key(by);
    let mut out = crate::verified::text::concat3(
        prefix,
        "t/",
        bucket_text.as_str(),
    );
    assert(out@ == prefix@ + "t/"@ + bucket_text@);
    out.push('/');
    assert(out@ == (prefix@ + "t/"@ + bucket_text@).push('/'));
    out.push_str(deadline.as_str());
    assert(out@ == (prefix@ + "t/"@ + bucket_text@).push('/')
        + deadline@);
    out.push('_');
    assert(out@ == ((prefix@ + "t/"@ + bucket_text@).push('/')
        + deadline@).push('_'));
    out.push_str(encoded_target);
    assert(out@ == ((prefix@ + "t/"@ + bucket_text@).push('/')
        + deadline@).push('_') + encoded_target@);
    out.push('@');
    assert(out@ == (((prefix@ + "t/"@ + bucket_text@).push('/')
        + deadline@).push('_') + encoded_target@).push('@'));
    out.push_str(token_text.as_str());
    assert(out@ == (((prefix@ + "t/"@ + bucket_text@).push('/')
        + deadline@).push('_') + encoded_target@).push('@')
        + token_text@);
    out.push('~');
    assert(out@ == ((((prefix@ + "t/"@ + bucket_text@).push('/')
        + deadline@).push('_') + encoded_target@).push('@')
        + token_text@).push('~'));
    out.push_str(encoded_by.as_str());
    assert(out@ == ((((prefix@ + "t/"@ + bucket_text@).push('/')
        + deadline@).push('_') + encoded_target@).push('@')
        + token_text@).push('~') + encoded_by@);
    assert(bucket == spec_bucket_of(at, bucket_ms));
    assert(bucket_text@ == spec_decimal20(bucket));
    assert(deadline@ == spec_decimal20(at));
    assert(token_text@ == spec_hex16(token));
    assert(encoded_by@ == spec_encode_key(by@));
    assert(spec_bucket_prefix(prefix@, bucket)
        == (prefix@ + "t/"@ + bucket_text@).push('/'));
    out
}

impl KeySpace {
    pub fn new(prefix: &str, bucket_ms: u64) -> (r: KeySpace)
        ensures
            r.deep_view() == (KeySpaceSpec {
                prefix: spec_normalize_prefix(prefix@),
                bucket_ms: if bucket_ms < 1 { 1u64 } else { bucket_ms },
            }),
    {
        KeySpace { prefix: normalize_prefix(prefix), bucket_ms: if bucket_ms < 1 { 1 } else { bucket_ms } }
    }

    pub fn copy(&self) -> (r: KeySpace)
        ensures
            r == *self,
    {
        KeySpace { prefix: copy_string(&self.prefix), bucket_ms: self.bucket_ms }
    }

    pub fn bucket_ms(&self) -> (r: u64)
        ensures
            r == self.bucket_ms,
    {
        self.bucket_ms
    }

    /// The class of object a key names: its first path segment under the
    /// prefix (`wf`, `sched`, `t`, `nodes`, `members`); `None` for a key
    /// outside the prefix.
    pub fn class_of(&self, key: &str) -> (r: Option<String>)
        ensures
            r.deep_view() == spec_class_of(self.prefix@, key@),
    {
        class_of(self.prefix.as_str(), key)
    }

    pub fn doc_key(&self, origin: &str) -> (r: String)
        ensures
            r@ == spec_doc_key(self.prefix@, origin@),
    {
        let encoded = encode_key(origin);
        crate::verified::text::concat3(
            self.prefix.as_str(),
            "wf/",
            encoded.as_str(),
        )
    }

    pub fn sched_key(&self, id: &str) -> (r: String)
        ensures
            r@ == spec_sched_key(self.prefix@, id@),
    {
        let encoded = encode_key(id);
        crate::verified::text::concat3(
            self.prefix.as_str(),
            "sched/",
            encoded.as_str(),
        )
    }

    /// The configuration object: the members and their epoch.
    pub fn members_key(&self) -> (r: String)
        ensures
            r@ == spec_members_key(self.prefix@),
    {
        crate::verified::text::concat(
            self.prefix.as_str(),
            "members",
        )
    }

    pub fn node_prefix(&self) -> (r: String)
        ensures
            r@ == spec_node_prefix(self.prefix@),
    {
        crate::verified::text::concat(
            self.prefix.as_str(),
            "nodes/",
        )
    }

    pub fn node_key(&self, id: &str) -> (r: String)
        ensures
            r@ == spec_node_key(self.prefix@, id@),
    {
        let encoded = encode_key(id);
        crate::verified::text::concat3(
            self.prefix.as_str(),
            "nodes/",
            encoded.as_str(),
        )
    }

    pub fn node_of_key(&self, key: &str) -> (r: Option<String>)
        ensures
            r.deep_view() == spec_node_of_key(self.prefix@, key@),
    {
        node_of_key(self.prefix.as_str(), key)
    }

    /// The start of the bucket an instant falls in.
    pub fn bucket_of(&self, at: u64) -> (r: u64)
        ensures
            r == spec_bucket_of(at, self.bucket_ms),
    {
        bucket_of(at, self.bucket_ms)
    }

    /// Every timer key lives under this.
    pub fn timer_prefix(&self) -> (r: String)
        ensures
            r@ == spec_timer_prefix(self.prefix@),
    {
        crate::verified::text::concat(self.prefix.as_str(), "t/")
    }

    /// The keys of one bucket live under this. `bucket` is a bucket start.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(10)]
    pub fn bucket_prefix(&self, bucket: u64) -> (r: String)
        ensures
            r@ == spec_bucket_prefix(self.prefix@, bucket),
    {
        let encoded = decimal20(bucket);
        let mut result = crate::verified::text::concat3(
            self.prefix.as_str(),
            "t/",
            encoded.as_str(),
        );
        result.push('/');
        assert(encoded@ == spec_decimal20(bucket));
        assert(result@ == (self.prefix@ + "t/"@ + encoded@).push('/'));
        result
    }

    /// The bucket start a bucket prefix names, as a listing returns it.
    pub fn parse_bucket_prefix(&self, prefix: &str) -> (r: Option<u64>)
        ensures
            r == spec_parse_bucket_prefix(self.prefix@, prefix@),
    {
        parse_bucket_prefix(self.prefix.as_str(), prefix)
    }

    pub fn timer_key(&self, origin: &str, at: u64, token: u64, by: &str) -> (r: String)
        ensures
            r@ == spec_timer_key(self.prefix@, self.bucket_ms, origin@, at, token, by@),
    {
        let encoded = encode_key(origin);
        timer_key_for(
            self.prefix.as_str(),
            self.bucket_ms,
            encoded.as_str(),
            at,
            token,
            by,
        )
    }

    pub fn sched_timer_key(&self, id: &str, at: u64, token: u64, by: &str) -> (r: String)
        ensures
            r@ == spec_sched_timer_key(self.prefix@, self.bucket_ms, id@, at, token, by@),
    {
        let encoded = encode_key(id);
        let target = crate::verified::text::concat(
            "sched:",
            encoded.as_str(),
        );
        timer_key_for(
            self.prefix.as_str(),
            self.bucket_ms,
            target.as_str(),
            at,
            token,
            by,
        )
    }

    pub fn parse_timer_key(&self, key: &str) -> (r: Option<TimerEntry>)
        ensures
            r.deep_view() == spec_parse_timer_key(key@),
    {
        parse_timer_key(key)
    }
}

} // verus!

/// The text of each key, and what a key's text says. Plain Rust: stated
/// above, as the characters each function writes or reads.
pub mod text {
    use super::{TimerEntry, DEADLINE_WIDTH};

    /// Percent-encode anything that is not safe and stable in a key.
    pub fn encode_key(s: &str) -> String {
        let mut out = String::with_capacity(s.len());
        for b in s.as_bytes() {
            match b {
                b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'.' | b'-' => out.push(*b as char),
                other => out.push_str(&format!("%{other:02X}")),
            }
        }
        out
    }

    pub fn decode_key(s: &str) -> Option<String> {
        let bytes = s.as_bytes();
        let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'%' {
                if i + 2 >= bytes.len() {
                    return None;
                }
                let hex = std::str::from_utf8(&bytes[i + 1..i + 3]).ok()?;
                out.push(u8::from_str_radix(hex, 16).ok()?);
                i += 3;
            } else {
                out.push(bytes[i]);
                i += 1;
            }
        }
        String::from_utf8(out).ok()
    }

    /// The prefix with its trailing `/`, when it has any text.
    pub fn normalize_prefix(prefix: &str) -> String {
        let mut prefix = prefix.to_string();
        if !prefix.is_empty() && !prefix.ends_with('/') {
            prefix.push('/');
        }
        prefix
    }

    pub fn class_of(prefix: &str, key: &str) -> Option<String> {
        let rest = key.strip_prefix(prefix)?;
        Some(rest.split('/').next().unwrap_or(rest).to_string())
    }

    pub fn last_segment(key: &str) -> String {
        key.rsplit('/').next().unwrap_or(key).to_string()
    }

    pub fn doc_key(prefix: &str, origin: &str) -> String {
        format!("{}wf/{}", prefix, encode_key(origin))
    }

    pub fn sched_key(prefix: &str, id: &str) -> String {
        format!("{}sched/{}", prefix, encode_key(id))
    }

    pub fn members_key(prefix: &str) -> String {
        format!("{}members", prefix)
    }

    pub fn node_prefix(prefix: &str) -> String {
        format!("{}nodes/", prefix)
    }

    pub fn node_key(prefix: &str, id: &str) -> String {
        format!("{}nodes/{}", prefix, encode_key(id))
    }

    pub fn node_of_key(prefix: &str, key: &str) -> Option<String> {
        decode_key(key.strip_prefix(&node_prefix(prefix))?)
    }

    pub fn timer_prefix(prefix: &str) -> String {
        format!("{}t/", prefix)
    }

    pub fn bucket_prefix(prefix: &str, bucket: u64) -> String {
        format!("{}t/{:0width$}/", prefix, bucket, width = DEADLINE_WIDTH)
    }

    pub fn parse_bucket_prefix(prefix: &str, p: &str) -> Option<u64> {
        let name = p.strip_prefix(&timer_prefix(prefix))?.strip_suffix('/')?;
        if name.len() != DEADLINE_WIDTH {
            return None;
        }
        name.parse().ok()
    }

    fn bucket_of(at: u64, bucket_ms: u64) -> u64 {
        let width = bucket_ms.max(1);
        at / width * width
    }

    /// A key names what is due, when, a token drawn per arm, and the node
    /// that armed it: only that node deletes it outright.
    fn timer_key_for(prefix: &str, bucket_ms: u64, encoded: &str, at: u64, token: u64, by: &str) -> String {
        format!("{}{:0width$}_{}@{:016x}~{}", bucket_prefix(prefix, bucket_of(at, bucket_ms)), at, encoded, token, encode_key(by), width = DEADLINE_WIDTH)
    }

    pub fn timer_key(prefix: &str, bucket_ms: u64, origin: &str, at: u64, token: u64, by: &str) -> String {
        timer_key_for(prefix, bucket_ms, &encode_key(origin), at, token, by)
    }

    pub fn sched_timer_key(prefix: &str, bucket_ms: u64, id: &str, at: u64, token: u64, by: &str) -> String {
        timer_key_for(prefix, bucket_ms, &format!("sched:{}", encode_key(id)), at, token, by)
    }

    fn timer_entry_name(entry: &TimerEntry) -> String {
        match entry {
            TimerEntry::Origin { deadline, origin, token, by } =>
                format!("{:0width$}_{}@{:016x}~{}", deadline, encode_key(origin), token, encode_key(by), width = DEADLINE_WIDTH),
            TimerEntry::Schedule { deadline, id, token, by } =>
                format!("{:0width$}_sched:{}@{:016x}~{}", deadline, encode_key(id), token, encode_key(by), width = DEADLINE_WIDTH),
        }
    }

    pub fn parse_timer_key(key: &str) -> Option<TimerEntry> {
        let name = key.rsplit('/').next()?;
        if name.len() < DEADLINE_WIDTH + 2 {
            return None;
        }
        let (deadline, rest) = name.split_at(DEADLINE_WIDTH);
        let deadline: u64 = deadline.parse().ok()?;
        let (target, rest) = rest.strip_prefix('_')?.rsplit_once('@')?;
        let (token, by) = rest.split_once('~')?;
        let token = u64::from_str_radix(token, 16).ok()?;
        let by = decode_key(by)?;
        let entry = match target.strip_prefix("sched:") {
            Some(id) => Some(TimerEntry::Schedule { deadline, id: decode_key(id)?, token, by }),
            None => Some(TimerEntry::Origin { deadline, origin: decode_key(target)?, token, by }),
        }?;
        (timer_entry_name(&entry) == name).then_some(entry)
    }
}

#[cfg(test)]
mod key_algebra_tests {
    use super::{text, KeySpace};

    #[test]
    fn constructors_preserve_legacy_bytes_for_adversarial_ids() {
        let ids = [
            "",
            "/@~:_%",
            "%2F",
            "wf/document",
            "sched:document",
            "t/00000000000000000000/",
            "nodes/member",
            "members",
            "snowman-\u{2603}",
            "\u{1f642}/\u{4e16}\u{754c}",
        ];
        let prefixes = ["", "root/", "namespace-like/t/"];

        for prefix in prefixes {
            let keys = KeySpace::new(prefix, 1_000);
            for id in ids {
                assert_eq!(keys.doc_key(id), text::doc_key(&keys.prefix, id));
                assert_eq!(
                    keys.sched_key(id),
                    text::sched_key(&keys.prefix, id),
                );
                assert_eq!(
                    keys.node_key(id),
                    text::node_key(&keys.prefix, id),
                );
                assert_eq!(
                    keys.timer_key(id, u64::MAX, u64::MAX, id),
                    text::timer_key(
                        &keys.prefix,
                        keys.bucket_ms,
                        id,
                        u64::MAX,
                        u64::MAX,
                        id,
                    ),
                );
                assert_eq!(
                    keys.sched_timer_key(id, 0, 0, id),
                    text::sched_timer_key(
                        &keys.prefix,
                        keys.bucket_ms,
                        id,
                        0,
                        0,
                        id,
                    ),
                );
            }
        }
    }

    #[test]
    fn document_and_timer_namespaces_do_not_collide() {
        let ids = [
            "",
            "wf/x",
            "sched:x",
            "t/x",
            "nodes/x",
            "members",
            "/@~:_%",
            "\u{1f642}",
        ];
        let keys = KeySpace::new("tenant/", 17);

        for left in ids {
            for right in ids {
                assert_ne!(keys.doc_key(left), keys.sched_key(right));
                assert_ne!(
                    keys.timer_key(left, 42, 7, right),
                    keys.doc_key(right),
                );
                assert_ne!(
                    keys.timer_key(left, 42, 7, right),
                    keys.sched_key(right),
                );
                assert_ne!(
                    keys.sched_timer_key(left, 42, 7, right),
                    keys.doc_key(right),
                );
                assert_ne!(
                    keys.sched_timer_key(left, 42, 7, right),
                    keys.sched_key(right),
                );
            }
        }
    }

    #[test]
    fn generated_keys_round_trip_through_production_parsers() {
        let ids = [
            "",
            "/@~:_%",
            "%2F",
            "sched:x",
            "wf/x",
            "\u{2603}",
            "\u{1f642}/\u{4e16}\u{754c}",
        ];
        let keys = KeySpace::new("root/", 1_000);

        for id in ids {
            assert_eq!(text::decode_key(&text::encode_key(id)).as_deref(), Some(id));
            assert_eq!(keys.node_of_key(&keys.node_key(id)).as_deref(), Some(id));

            let origin = keys.timer_key(id, u64::MAX, u64::MAX, id);
            let parsed = keys.parse_timer_key(&origin).expect("origin timer");
            assert_eq!(parsed.deadline(), u64::MAX);
            assert_eq!(parsed.target(), id);
            assert_eq!(parsed.token(), u64::MAX);
            assert_eq!(parsed.by(), id);

            let schedule = keys.sched_timer_key(id, 0, 0, id);
            let parsed = keys.parse_timer_key(&schedule).expect("schedule timer");
            assert_eq!(parsed.deadline(), 0);
            assert_eq!(parsed.target(), id);
            assert_eq!(parsed.token(), 0);
            assert_eq!(parsed.by(), id);
        }
    }

    #[test]
    fn malformed_percent_escapes_are_rejected() {
        for malformed in ["%", "%0", "%GG", "%FF"] {
            assert_eq!(text::decode_key(malformed), None, "{malformed:?}");
        }
        assert_eq!(text::decode_key("\u{2603}").as_deref(), Some("\u{2603}"));
        assert_eq!(text::decode_key("%2f").as_deref(), Some("/"));
        assert_eq!(text::decode_key("%2F").as_deref(), Some("/"));
    }

    #[test]
    fn parsers_reject_noncanonical_aliases() {
        let keys = KeySpace::new("root/", 1_000);
        let canonical = keys.timer_key("/", 7, 9, "node");
        assert!(keys.parse_timer_key(&canonical).is_some());
        assert!(keys.parse_timer_key(
            &canonical.replace("%2F", "%2f"),
        ).is_none());
        assert_eq!(
            keys.parse_bucket_prefix("root/t/00000000000000000007//"),
            None,
        );
    }
}
