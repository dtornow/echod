//! Canonical textual object-store keys matching `logic::keys::KeySpace`.

use vstd::prelude::*;

use crate::primitives::copy_range;
#[cfg(verus_keep_ghost)]
use crate::text::valid_utf8;
use crate::text::Text;
use crate::types as model;

verus! {

pub type KeyResult<T> = Result<T, &'static str>;

pub const DECIMAL_WIDTH: usize = 20;
pub const TOKEN_WIDTH: usize = 16;

pub open spec fn safe_key_byte(byte: u8) -> bool {
    ||| 0x41 <= byte <= 0x5a
    ||| 0x61 <= byte <= 0x7a
    ||| 0x30 <= byte <= 0x39
    ||| byte == 0x2e
    ||| byte == 0x2d
}

pub open spec fn upper_hex_digit(value: u8) -> u8 {
    if value < 10 {
        (0x30 + value as int) as u8
    } else {
        (0x41 + (value as int - 10)) as u8
    }
}

pub open spec fn lower_hex_digit(value: u8) -> u8 {
    if value < 10 {
        (0x30 + value as int) as u8
    } else {
        (0x61 + (value as int - 10)) as u8
    }
}

pub open spec fn decode_upper_hex(byte: u8) -> Option<u8> {
    if 0x30 <= byte <= 0x39 {
        Some((byte as int - 0x30) as u8)
    } else if 0x41 <= byte <= 0x46 {
        Some((byte as int - 0x41 + 10) as u8)
    } else {
        None
    }
}

pub open spec fn decode_lower_hex(byte: u8) -> Option<u8> {
    if 0x30 <= byte <= 0x39 {
        Some((byte as int - 0x30) as u8)
    } else if 0x61 <= byte <= 0x66 {
        Some((byte as int - 0x61 + 10) as u8)
    } else {
        None
    }
}

pub closed spec fn percent_encode(bytes: Seq<u8>) -> Seq<u8>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        Seq::empty()
    } else {
        let first = bytes[0];
        (if safe_key_byte(first) {
            seq![first]
        } else {
            seq![
                0x25u8,
                upper_hex_digit(first / 16),
                upper_hex_digit(first % 16),
            ]
        }) + percent_encode(bytes.drop_first())
    }
}

pub closed spec fn percent_decode(bytes: Seq<u8>) -> Option<Seq<u8>>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        Some(Seq::empty())
    } else if safe_key_byte(bytes[0]) {
        match percent_decode(bytes.drop_first()) {
            Some(rest) => Some(seq![bytes[0]] + rest),
            None => None,
        }
    } else if bytes.len() >= 3 && bytes[0] == 0x25 {
        match (
            decode_upper_hex(bytes[1]),
            decode_upper_hex(bytes[2]),
            percent_decode(bytes.subrange(3, bytes.len() as int)),
        ) {
            (Some(hi), Some(lo), Some(rest)) => {
                Some(seq![(hi * 16 + lo) as u8] + rest)
            }
            _ => None,
        }
    } else {
        None
    }
}

pub proof fn lemma_upper_hex_round_trip(value: u8)
    requires value < 16,
    ensures decode_upper_hex(upper_hex_digit(value)) == Some(value),
{
}

pub proof fn lemma_lower_hex_round_trip(value: u8)
    requires value < 16,
    ensures decode_lower_hex(lower_hex_digit(value)) == Some(value),
{
}

#[verifier::bit_vector]
proof fn lemma_byte_nibbles(byte: u8)
    ensures
        byte / 16 < 16,
        byte % 16 < 16,
        ((byte / 16) * 16 + byte % 16) as u8 == byte,
{
}

pub proof fn lemma_percent_round_trip(bytes: Seq<u8>)
    ensures percent_decode(percent_encode(bytes)) == Some(bytes),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        let first = bytes[0];
        let rest = bytes.drop_first();
        if !safe_key_byte(first) {
            lemma_byte_nibbles(first);
            lemma_upper_hex_round_trip(first / 16);
            lemma_upper_hex_round_trip(first % 16);
        }
        lemma_percent_round_trip(rest);
        lemma_percent_decode_cons(first, rest);
        reveal_with_fuel(percent_encode, 2);
        assert(seq![first] + rest == bytes);
        assert(percent_encode(bytes)
            == (if safe_key_byte(first) {
                seq![first]
            } else {
                seq![
                    0x25u8,
                    upper_hex_digit(first / 16),
                    upper_hex_digit(first % 16),
                ]
            }) + percent_encode(rest));
    }
}

proof fn lemma_percent_decode_cons(byte: u8, rest: Seq<u8>)
    requires percent_decode(percent_encode(rest)) == Some(rest),
    ensures
        percent_decode(
            (if safe_key_byte(byte) {
                seq![byte]
            } else {
                seq![
                    0x25u8,
                    upper_hex_digit(byte / 16),
                    upper_hex_digit(byte % 16),
                ]
            }) + percent_encode(rest),
        ) == Some(seq![byte] + rest),
{
    reveal_with_fuel(percent_decode, 4);
    if safe_key_byte(byte) {
        let encoded = seq![byte] + percent_encode(rest);
        assert(encoded.len() > 0);
        assert(encoded[0] == byte);
        assert(encoded.drop_first() == percent_encode(rest));
    } else {
        lemma_byte_nibbles(byte);
        lemma_upper_hex_round_trip(byte / 16);
        lemma_upper_hex_round_trip(byte % 16);
        let encoded = seq![
            0x25u8,
            upper_hex_digit(byte / 16),
            upper_hex_digit(byte % 16),
        ] + percent_encode(rest);
        assert(encoded.subrange(3, encoded.len() as int)
            == percent_encode(rest));
    }
}

proof fn lemma_percent_singleton(byte: u8)
    ensures
        percent_encode(seq![byte]) == if safe_key_byte(byte) {
            seq![byte]
        } else {
            seq![
                0x25u8,
                upper_hex_digit(byte / 16),
                upper_hex_digit(byte % 16),
            ]
        },
{
    reveal_with_fuel(percent_encode, 3);
    assert(seq![byte].drop_first() == Seq::<u8>::empty());
}

proof fn lemma_percent_encode_push(bytes: Seq<u8>, byte: u8)
    ensures
        percent_encode(bytes.push(byte))
            == percent_encode(bytes) + percent_encode(seq![byte]),
    decreases bytes.len(),
{
    reveal_with_fuel(percent_encode, 3);
    if bytes.len() == 0 {
        assert(bytes.push(byte) == seq![byte]);
    } else {
        let rest = bytes.drop_first();
        assert(bytes.push(byte)[0] == bytes[0]);
        assert(bytes.push(byte).drop_first() == rest.push(byte));
        lemma_percent_encode_push(rest, byte);
        assert(percent_encode(bytes.push(byte))
            == (if safe_key_byte(bytes[0]) {
                seq![bytes[0]]
            } else {
                seq![
                    0x25u8,
                    upper_hex_digit(bytes[0] / 16),
                    upper_hex_digit(bytes[0] % 16),
                ]
            }) + percent_encode(rest.push(byte)));
    }
}

fn encode_component(bytes: &Vec<u8>) -> (result: Vec<u8>)
    ensures result@ == percent_encode(bytes@),
{
    reveal_with_fuel(percent_encode, 2);
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < bytes.len()
        invariant
            i <= bytes.len(),
            result@ == percent_encode(
                bytes@.subrange(0, i as int),
            ),
        decreases bytes.len() - i,
    {
        let ghost before = result@;
        let ghost prefix = bytes@.subrange(0, i as int);
        let byte = bytes[i];
        proof {
            lemma_percent_singleton(byte);
        }
        if (byte >= b'A' && byte <= b'Z')
            || (byte >= b'a' && byte <= b'z')
            || (byte >= b'0' && byte <= b'9')
            || byte == b'.'
            || byte == b'-' {
            result.push(byte);
            assert(result@ == before.push(byte));
            assert(percent_encode(seq![byte]) == seq![byte]);
        } else {
            result.push(b'%');
            result.push(if byte / 16 < 10 {
                b'0' + byte / 16
            } else {
                b'A' + (byte / 16 - 10)
            });
            result.push(if byte % 16 < 10 {
                b'0' + byte % 16
            } else {
                b'A' + (byte % 16 - 10)
            });
            assert(result@ =~= before + seq![
                0x25u8,
                upper_hex_digit(byte / 16),
                upper_hex_digit(byte % 16),
            ]);
            assert(percent_encode(seq![byte]) == seq![
                0x25u8,
                upper_hex_digit(byte / 16),
                upper_hex_digit(byte % 16),
            ]);
        }
        assert(bytes@.subrange(0, i as int + 1)
            == prefix.push(byte));
        proof {
            lemma_percent_encode_push(prefix, byte);
        }
        assert(result@ == before + percent_encode(seq![byte]));
        i += 1;
    }
    assert(bytes@.subrange(0, bytes.len() as int) == bytes@);
    result
}

#[verifier::rlimit(20)]
fn decode_component(bytes: &Vec<u8>) -> (result: Option<Vec<u8>>)
    ensures result.deep_view() == percent_decode(bytes@),
    decreases bytes.len(),
{
    reveal_with_fuel(percent_decode, 4);
    if bytes.len() == 0 {
        return Some(Vec::new());
    }
    let first = bytes[0];
    if (first >= b'A' && first <= b'Z')
        || (first >= b'a' && first <= b'z')
        || (first >= b'0' && first <= b'9')
        || first == b'.'
        || first == b'-' {
        let tail = copy_range(bytes, 1, bytes.len());
        let mut rest = match decode_component(&tail) {
            None => return None,
            Some(rest) => rest,
        };
        let ghost old_rest = rest@;
        rest.insert(0, first);
        assert(rest@ =~= seq![first] + old_rest);
        Some(rest)
    } else if first == b'%' && bytes.len() >= 3 {
        let hi = if bytes[1] >= b'0' && bytes[1] <= b'9' {
            bytes[1] - b'0'
        } else if bytes[1] >= b'A' && bytes[1] <= b'F' {
            bytes[1] - b'A' + 10
        } else {
            return None;
        };
        let lo = if bytes[2] >= b'0' && bytes[2] <= b'9' {
            bytes[2] - b'0'
        } else if bytes[2] >= b'A' && bytes[2] <= b'F' {
            bytes[2] - b'A' + 10
        } else {
            return None;
        };
        let tail = copy_range(bytes, 3, bytes.len());
        let mut rest = match decode_component(&tail) {
            None => return None,
            Some(rest) => rest,
        };
        let ghost old_rest = rest@;
        rest.insert(0, hi * 16 + lo);
        assert(rest@ =~= seq![(hi * 16 + lo) as u8] + old_rest);
        Some(rest)
    } else {
        None
    }
}

// -------------------------------------------------------------------------
// Fixed-width unsigned formatting
// -------------------------------------------------------------------------

pub open spec fn pow(base: int, width: nat) -> int
    decreases width,
{
    if width == 0 { 1 } else { base * pow(base, (width - 1) as nat) }
}

pub open spec fn fixed_digits(
    value: int,
    base: int,
    width: nat,
) -> Seq<u8>
    decreases width,
{
    if width == 0 {
        Seq::empty()
    } else {
        fixed_digits(value / base, base, (width - 1) as nat).push(
            (value % base) as u8,
        )
    }
}

pub open spec fn digits_value(
    digits: Seq<u8>,
    base: int,
) -> int
    decreases digits.len(),
{
    if digits.len() == 0 {
        0
    } else {
        digits_value(digits.drop_last(), base) * base
            + digits.last() as int
    }
}

proof fn lemma_pow_positive(base: int, width: nat)
    requires base > 0,
    ensures pow(base, width) > 0,
    decreases width,
{
    if width > 0 {
        let p = pow(base, (width - 1) as nat);
        lemma_pow_positive(base, (width - 1) as nat);
        assert(pow(base, width)
            == base * p);
        assert(base >= 1);
        assert(p >= 1);
        vstd::arithmetic::mul::lemma_mul_strictly_positive(base, p);
        assert(base * p >= 1);
    }
}

pub proof fn lemma_fixed_digits_value(
    value: int,
    base: int,
    width: nat,
)
    requires
        base > 1,
        base <= 16,
        value >= 0,
        value < pow(base, width),
    ensures
        fixed_digits(value, base, width).len() == width,
        digits_value(fixed_digits(value, base, width), base) == value,
    decreases width,
{
    if width == 0 {
        assert(pow(base, width) == 1);
        assert(value == 0);
    } else {
        let p = pow(base, (width - 1) as nat);
        let q = value / base;
        let r = value % base;
        lemma_pow_positive(base, (width - 1) as nat);
        assert(pow(base, width) == base * p);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            value, base,
        );
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(
            value, base,
        );
        assert(value == q * base + r);
        assert(r >= 0);
        assert(r < base);
        assert(q >= 0);
        assert(value < base * p);
        assert(q < p) by {
            if q >= p {
                vstd::arithmetic::mul::lemma_mul_inequality(
                    p, q, base,
                );
                vstd::arithmetic::mul::lemma_mul_is_commutative(q, base);
                vstd::arithmetic::mul::lemma_mul_is_commutative(p, base);
                assert(q * base >= p * base);
                assert(q * base == base * q);
                assert(p * base == base * p);
                assert(value == q * base + r);
                assert(value >= q * base);
                assert(value >= p * base);
                assert(value >= base * p);
            }
        }
        lemma_fixed_digits_value(
            q, base, (width - 1) as nat,
        );
        assert(digits_value(
            fixed_digits(q, base, (width - 1) as nat),
            base,
        ) == q);
        reveal_with_fuel(fixed_digits, 2);
        reveal_with_fuel(digits_value, 2);
        assert((r as u8) as int == r);
        let prefix =
            fixed_digits(q, base, (width - 1) as nat);
        assert(fixed_digits(value, base, width)
            == prefix.push(r as u8));
        assert(prefix.push(r as u8).drop_last() == prefix);
        assert(prefix.push(r as u8).last() == r as u8);
        assert(digits_value(prefix.push(r as u8), base)
            == digits_value(prefix, base) * base + r);
        assert(digits_value(fixed_digits(value, base, width), base)
            == q * base + r);
        assert(q * base + r == value);
    }
}

pub open spec fn decimal20(value: u64) -> Seq<u8> {
    fixed_digits(value as int, 10, 20).map_values(
        |digit: u8| encode_ascii_digit(digit, false),
    )
}

pub open spec fn hex16(value: u64) -> Seq<u8> {
    fixed_digits(value as int, 16, 16).map_values(
        |digit: u8| encode_ascii_digit(digit, true),
    )
}

pub open spec fn encode_ascii_digit(digit: u8, hex: bool) -> u8 {
    if hex {
        lower_hex_digit(digit)
    } else {
        (0x30u8 + digit) as u8
    }
}

proof fn lemma_pow10_20_large()
    ensures (u64::MAX as int) < pow(10, 20),
{
    assert(pow(10, 20) == 100000000000000000000int) by (compute);
}

proof fn lemma_pow16_16_large()
    ensures (u64::MAX as int) < pow(16, 16),
{
    assert(pow(16, 16) == 18446744073709551616int) by (compute);
}

fn encode_fixed_digits(
    value: u64,
    base: u64,
    width: usize,
    hex: bool,
) -> (result: Vec<u8>)
    requires
        base == 10 || base == 16,
    ensures
        result@ == fixed_digits(
            value as int, base as int, width as nat,
        ).map_values(
            |digit: u8| encode_ascii_digit(digit, hex),
        ),
    decreases width,
{
    if width == 0 {
        Vec::new()
    } else {
        let mut result = encode_fixed_digits(
            value / base, base, width - 1, hex,
        );
        let digit = (value % base) as u8;
        result.push(if hex {
            if digit < 10 { b'0' + digit } else { b'a' + digit - 10 }
        } else {
            b'0' + digit
        });
        result
    }
}

fn encode_decimal20(value: u64) -> (result: Vec<u8>)
    ensures result@ == decimal20(value),
{
    encode_fixed_digits(value, 10, DECIMAL_WIDTH, false)
}

fn encode_hex16(value: u64) -> (result: Vec<u8>)
    ensures result@ == hex16(value),
{
    encode_fixed_digits(value, 16, TOKEN_WIDTH, true)
}

pub open spec fn decode_ascii_digit(
    byte: u8,
    base: int,
    hex: bool,
) -> Option<u8> {
    if 0x30 <= byte <= 0x39
        && (byte as int - 0x30) < base {
        Some((byte as int - 0x30) as u8)
    } else if hex && 0x61 <= byte <= 0x66
        && (byte as int - 0x61 + 10) < base {
        Some((byte as int - 0x61 + 10) as u8)
    } else {
        None
    }
}

pub open spec fn decode_ascii_digits(
    bytes: Seq<u8>,
    base: int,
    hex: bool,
) -> Option<Seq<u8>>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        Some(Seq::empty())
    } else {
        match (
            decode_ascii_digits(bytes.drop_last(), base, hex),
            decode_ascii_digit(bytes.last(), base, hex),
        ) {
            (Some(rest), Some(last)) => Some(rest.push(last)),
            _ => None,
        }
    }
}

pub open spec fn decode_fixed_u64(
    bytes: Seq<u8>,
    base: int,
    width: nat,
    hex: bool,
) -> Option<u64> {
    if bytes.len() != width {
        None
    } else {
        match decode_ascii_digits(bytes, base, hex) {
            Some(digits) if digits_value(digits, base) <= u64::MAX => {
                Some(digits_value(digits, base) as u64)
            }
            _ => None,
        }
    }
}

pub open spec fn decode_decimal20(bytes: Seq<u8>) -> Option<u64> {
    decode_fixed_u64(bytes, 10, 20, false)
}

pub open spec fn decode_hex16(bytes: Seq<u8>) -> Option<u64> {
    decode_fixed_u64(bytes, 16, 16, true)
}

proof fn lemma_fixed_digits_bounded(
    value: int,
    base: int,
    width: nat,
)
    requires
        value >= 0,
        base > 1,
        base <= 16,
    ensures
        forall|i: int| 0 <= i < fixed_digits(value, base, width).len()
            ==> 0 <= #[trigger] fixed_digits(value, base, width)[i] < base,
    decreases width,
{
    if width > 0 {
        let q = value / base;
        let r = value % base;
        let prefix = fixed_digits(q, base, (width - 1) as nat);
        lemma_fixed_digits_bounded(
            q, base, (width - 1) as nat,
        );
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(value, base);
        reveal_with_fuel(fixed_digits, 2);
        assert(fixed_digits(value, base, width) == prefix.push(r as u8));
        assert forall|i: int| 0 <= i < prefix.push(r as u8).len()
            implies 0 <= #[trigger] prefix.push(r as u8)[i] < base by {
            if i < prefix.len() {
                assert(prefix.push(r as u8)[i] == prefix[i]);
            } else {
                assert(i == prefix.len());
                assert(prefix.push(r as u8)[i] == r as u8);
                assert((r as u8) as int == r);
            }
        }
    }
}

proof fn lemma_decode_ascii_fixed(
    value: int,
    base: int,
    width: nat,
    hex: bool,
)
    requires
        value >= 0,
        base == 10 || base == 16,
        hex ==> base == 16,
        !hex ==> base == 10,
    ensures
        decode_ascii_digits(
            fixed_digits(value, base, width).map_values(
                |digit: u8| encode_ascii_digit(digit, hex),
            ),
            base,
            hex,
        ) == Some(fixed_digits(value, base, width)),
    decreases width,
{
    if width > 0 {
        let q = value / base;
        let r = value % base;
        let prefix = fixed_digits(q, base, (width - 1) as nat);
        lemma_decode_ascii_fixed(
            q, base, (width - 1) as nat, hex,
        );
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(value, base);
        reveal_with_fuel(fixed_digits, 2);
        reveal_with_fuel(decode_ascii_digits, 2);
        let digit = r as u8;
        assert(0 <= r < base);
        assert(digit < base);
        assert((base as u8) as int == base);
        lemma_ascii_digit_round_trip(digit, base as u8, hex);
        assert(fixed_digits(value, base, width) == prefix.push(digit));
        let encoded_prefix = prefix.map_values(
            |digit: u8| encode_ascii_digit(digit, hex),
        );
        let encoded_digit = encode_ascii_digit(digit, hex);
        assert(fixed_digits(value, base, width).map_values(
            |digit: u8| encode_ascii_digit(digit, hex),
        ) == encoded_prefix.push(encoded_digit));
        assert(encoded_prefix.push(encoded_digit).drop_last()
            == encoded_prefix);
        assert(encoded_prefix.push(encoded_digit).last()
            == encoded_digit);
        assert(decode_ascii_digits(encoded_prefix, base, hex)
            == Some(prefix));
        assert(decode_ascii_digit(encoded_digit, base, hex)
            == Some(digit));
    }
}

proof fn lemma_ascii_digit_round_trip(
    digit: u8,
    base: u8,
    hex: bool,
)
    requires
        base == 10 || base == 16,
        hex ==> base == 16,
        !hex ==> base == 10,
        digit < base,
    ensures
        decode_ascii_digit(
            encode_ascii_digit(digit, hex),
            base as int,
            hex,
        ) == Some(digit),
{
    reveal(encode_ascii_digit);
    if hex {
        if digit < 10 {
            assert(lower_hex_digit(digit)
                == (0x30u8 + digit) as u8);
        } else {
            assert(base == 16);
            assert(10 <= digit < 16);
            assert(lower_hex_digit(digit)
                == (0x61 + (digit as int - 10)) as u8);
        }
    } else {
        assert(digit < 10);
        assert(0x30 + digit as int <= 0x39);
        assert(((0x30u8 + digit) as u8) as int
            == 0x30 + digit as int);
        assert((0x30u8 + digit) as u8 >= 0x30);
        assert((0x30u8 + digit) as u8 <= 0x39);
    }
}

pub proof fn lemma_decimal20_round_trip(value: u64)
    ensures decode_decimal20(decimal20(value)) == Some(value),
{
    lemma_pow10_20_large();
    lemma_fixed_digits_value(value as int, 10, 20);
    lemma_decode_ascii_fixed(value as int, 10, 20, false);
    assert(decode_ascii_digits(
        fixed_digits(value as int, 10, 20).map_values(
            |digit: u8| encode_ascii_digit(digit, false),
        ),
        10,
        false,
    ) == Some(fixed_digits(value as int, 10, 20)));
    reveal(decimal20);
    assert(decimal20(value)
        == fixed_digits(value as int, 10, 20).map_values(
            |digit: u8| encode_ascii_digit(digit, false),
        ));
    assert(decimal20(value).len() == 20);
    assert(decode_ascii_digits(decimal20(value), 10, false)
        == Some(fixed_digits(value as int, 10, 20)));
    assert(digits_value(
        fixed_digits(value as int, 10, 20), 10,
    ) == value as int);
    assert(value as int <= u64::MAX);
    reveal(decode_decimal20);
    reveal(decode_fixed_u64);
}

pub proof fn lemma_hex16_round_trip(value: u64)
    ensures decode_hex16(hex16(value)) == Some(value),
{
    lemma_pow16_16_large();
    lemma_fixed_digits_value(value as int, 16, 16);
    lemma_decode_ascii_fixed(value as int, 16, 16, true);
    assert(decode_ascii_digits(
        fixed_digits(value as int, 16, 16).map_values(
            |digit: u8| encode_ascii_digit(digit, true),
        ),
        16,
        true,
    ) == Some(fixed_digits(value as int, 16, 16)));
    reveal(hex16);
    assert(hex16(value)
        == fixed_digits(value as int, 16, 16).map_values(
            |digit: u8| encode_ascii_digit(digit, true),
        ));
    assert(hex16(value).len() == 16);
    assert(decode_ascii_digits(hex16(value), 16, true)
        == Some(fixed_digits(value as int, 16, 16)));
    assert(digits_value(
        fixed_digits(value as int, 16, 16), 16,
    ) == value as int);
    assert(value as int <= u64::MAX);
    reveal(decode_hex16);
    reveal(decode_fixed_u64);
}

fn decode_digit(
    byte: u8,
    base: u64,
    hex: bool,
) -> (result: Option<u8>)
    requires base == 10 || base == 16,
    ensures result == decode_ascii_digit(byte, base as int, hex),
{
    if byte >= b'0' && byte <= b'9' {
        let digit = byte - b'0';
        if (digit as u64) < base {
            Some(digit)
        } else {
            None
        }
    } else if hex && byte >= b'a' && byte <= b'f' {
        let digit = byte - b'a' + 10;
        if (digit as u64) < base {
            Some(digit)
        } else {
            None
        }
    } else {
        None
    }
}

fn decode_digits(
    bytes: &Vec<u8>,
    base: u64,
    hex: bool,
) -> (result: Option<Vec<u8>>)
    requires base == 10 || base == 16,
    ensures result.deep_view()
        == decode_ascii_digits(bytes@, base as int, hex),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        Some(Vec::new())
    } else {
        let n = bytes.len();
        let prefix = copy_range(bytes, 0, n - 1);
        let mut rest = match decode_digits(&prefix, base, hex) {
            None => return None,
            Some(rest) => rest,
        };
        let last = match decode_digit(bytes[n - 1], base, hex) {
            None => return None,
            Some(last) => last,
        };
        let ghost old_rest = rest@;
        rest.push(last);
        assert(bytes@.drop_last()
            == bytes@.subrange(0, (n - 1) as int));
        assert(bytes@.last() == bytes@[(n - 1) as int]);
        assert(rest@ == old_rest.push(last));
        Some(rest)
    }
}

proof fn lemma_digits_value_push(
    digits: Seq<u8>,
    digit: u8,
    base: int,
)
    ensures
        digits_value(digits.push(digit), base)
            == digits_value(digits, base) * base + digit as int,
{
    reveal_with_fuel(digits_value, 2);
    assert(digits.push(digit).len() > 0);
    assert(digits.push(digit).drop_last() == digits);
    assert(digits.push(digit).last() == digit);
}

proof fn lemma_digits_value_nonnegative(
    digits: Seq<u8>,
    base: int,
)
    requires base >= 0,
    ensures digits_value(digits, base) >= 0,
    decreases digits.len(),
{
    if digits.len() > 0 {
        lemma_digits_value_nonnegative(digits.drop_last(), base);
        reveal_with_fuel(digits_value, 2);
    }
}

proof fn lemma_digits_value_prefix_monotonic(
    digits: Seq<u8>,
    base: int,
    n: int,
)
    requires
        base >= 1,
        0 <= n <= digits.len(),
    ensures
        digits_value(digits.subrange(0, n), base)
            <= digits_value(digits, base),
    decreases digits.len() - n,
{
    if n < digits.len() {
        let prefix = digits.subrange(0, n);
        let digit = digits[n];
        let extended = digits.subrange(0, n + 1);
        assert(extended == prefix.push(digit));
        lemma_digits_value_nonnegative(prefix, base);
        lemma_digits_value_push(prefix, digit, base);
        vstd::arithmetic::mul::lemma_mul_inequality(
            1, base, digits_value(prefix, base),
        );
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            1, digits_value(prefix, base),
        );
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            base, digits_value(prefix, base),
        );
        assert(digits_value(prefix, base)
            <= digits_value(extended, base));
        lemma_digits_value_prefix_monotonic(digits, base, n + 1);
    } else {
        assert(n == digits.len());
        assert(digits.subrange(0, n) == digits);
    }
}

proof fn lemma_decode_ascii_digits_bounded(
    bytes: Seq<u8>,
    digits: Seq<u8>,
    base: int,
    hex: bool,
)
    requires
        base == 10 || base == 16,
        decode_ascii_digits(bytes, base, hex) == Some(digits),
    ensures
        digits.len() == bytes.len(),
        forall|i: int| 0 <= i < digits.len()
            ==> #[trigger] digits[i] < base,
    decreases bytes.len(),
{
    reveal_with_fuel(decode_ascii_digits, 2);
    if bytes.len() > 0 {
        let prefix = bytes.drop_last();
        let last = bytes.last();
        let decoded_prefix = decode_ascii_digits(prefix, base, hex);
        let decoded_last = decode_ascii_digit(last, base, hex);
        assert(decoded_prefix is Some);
        assert(decoded_last is Some);
        let prefix_digits = decoded_prefix->Some_0;
        let digit = decoded_last->Some_0;
        assert(digits == prefix_digits.push(digit));
        lemma_decode_ascii_digits_bounded(
            prefix, prefix_digits, base, hex,
        );
        assert(digit < base);
        assert forall|i: int| 0 <= i < digits.len()
            implies #[trigger] digits[i] < base by {
            if i < prefix_digits.len() {
                assert(digits[i] == prefix_digits[i]);
            } else {
                assert(i == prefix_digits.len());
                assert(digits[i] == digit);
            }
        }
    }
}

fn digits_to_u64(
    digits: &Vec<u8>,
    base: u64,
) -> (result: Option<u64>)
    requires
        base == 10 || base == 16,
        forall|i: int| 0 <= i < digits.len()
            ==> digits[i] < base,
    ensures
        match result {
            Some(value) => {
                &&& digits_value(digits@, base as int) <= u64::MAX
                &&& value as int == digits_value(digits@, base as int)
            }
            None => digits_value(digits@, base as int) > u64::MAX,
        },
{
    let mut value = 0u64;
    let mut i = 0usize;
    assert(base > 0);
    while i < digits.len()
        invariant
            i <= digits.len(),
            base == 10 || base == 16,
            forall|j: int| 0 <= j < digits.len()
                ==> digits[j] < base,
            value as int == digits_value(
                digits@.subrange(0, i as int), base as int,
            ),
            0 <= digits_value(
                digits@.subrange(0, i as int), base as int,
            ),
        decreases digits.len() - i,
    {
        let digit = digits[i] as u64;
        let ghost prefix = digits@.subrange(0, i as int);
        assert(digits[i as int] < base);
        assert(digit < base);
        assert(digit <= u64::MAX);
        let ghost remaining = u64::MAX as int - digit as int;
        let ghost quotient = remaining / base as int;
        let ghost remainder = remaining % base as int;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                remaining, base as int,
            );
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(
                remaining, base as int,
            );
            vstd::arithmetic::mul::lemma_mul_is_commutative(
                quotient, base as int,
            );
            assert(remaining
                == quotient * base as int + remainder);
            assert(0 <= remainder < base);
        }
        if value > (u64::MAX - digit) / base {
            proof {
                assert(value as int > quotient);
                assert(value as int >= quotient + 1);
                vstd::arithmetic::mul::lemma_mul_inequality(
                    quotient + 1, value as int, base as int,
                );
                vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                    quotient, 1, base as int,
                );
                assert((quotient + 1) * base as int
                    > quotient * base as int + remainder);
                assert(value as int * base as int > remaining);
                assert(value as int * base as int + digit as int
                    > u64::MAX);
                lemma_digits_value_push(
                    prefix, digits[i as int], base as int,
                );
                assert(digits@.subrange(0, i as int + 1)
                    == prefix.push(digits[i as int]));
                assert(digits_value(
                    digits@.subrange(0, i as int + 1), base as int,
                ) > u64::MAX);
                lemma_digits_value_prefix_monotonic(
                    digits@, base as int, i as int + 1,
                );
            }
            return None;
        }
        proof {
            assert(value as int <= quotient);
            vstd::arithmetic::mul::lemma_mul_inequality(
                value as int, quotient, base as int,
            );
            assert(value as int * base as int
                <= quotient * base as int);
            assert(value as int * base as int + digit as int
                <= u64::MAX);
        }
        value = value * base + digit;
        assert(digits@.subrange(0, i as int + 1)
            == digits@.subrange(0, i as int).push(digits[i as int]));
        proof {
            lemma_digits_value_push(
                prefix, digits[i as int], base as int,
            );
        }
        i += 1;
    }
    assert(digits@.subrange(0, digits.len() as int) == digits@);
    Some(value)
}

fn decode_fixed(
    bytes: &Vec<u8>,
    base: u64,
    width: usize,
    hex: bool,
) -> (result: Option<u64>)
    requires base == 10 || base == 16,
        hex ==> base == 16,
        !hex ==> base == 10,
    ensures result == decode_fixed_u64(
        bytes@, base as int, width as nat, hex,
    ),
{
    if bytes.len() != width {
        return None;
    }
    let digits = match decode_digits(bytes, base, hex) {
        None => return None,
        Some(digits) => digits,
    };
    assert(decode_ascii_digits(bytes@, base as int, hex)
        == Some(digits@));
    proof {
        lemma_decode_ascii_digits_bounded(
            bytes@, digits@, base as int, hex,
        );
    }
    assert forall|i: int| 0 <= i < digits.len()
        implies digits[i] < base by {
        assert(digits[i] == digits@[i]);
    }
    let result = digits_to_u64(&digits, base);
    reveal(decode_fixed_u64);
    result
}

fn decode_decimal20_exec(bytes: &Vec<u8>) -> (result: Option<u64>)
    ensures result == decode_decimal20(bytes@),
{
    decode_fixed(bytes, 10, DECIMAL_WIDTH, false)
}

fn decode_hex16_exec(bytes: &Vec<u8>) -> (result: Option<u64>)
    ensures result == decode_hex16(bytes@),
{
    decode_fixed(bytes, 16, TOKEN_WIDTH, true)
}

pub open spec fn lex_less(left: Seq<u8>, right: Seq<u8>) -> bool
    decreases left.len(),
{
    if left.len() == 0 || right.len() == 0 {
        left.len() < right.len()
    } else if left[0] == right[0] {
        lex_less(left.drop_first(), right.drop_first())
    } else {
        left[0] < right[0]
    }
}

// -------------------------------------------------------------------------
// Store-key grammar and executable byte bridge
// -------------------------------------------------------------------------

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Copy, Debug, PartialEq, Eq))]
pub enum KeyClass {
    Document,
    Schedule,
    Timer,
    Node,
    Membership,
}

pub open spec fn effective_bucket_ms(bucket_ms: u64) -> u64 {
    if bucket_ms == 0 { 1 } else { bucket_ms }
}

pub open spec fn bucket_of(deadline: u64, bucket_ms: u64) -> u64 {
    (deadline / effective_bucket_ms(bucket_ms)
        * effective_bucket_ms(bucket_ms)) as u64
}

pub open spec fn normalized_prefix(prefix: Seq<u8>) -> Seq<u8> {
    if prefix.len() == 0 || prefix.last() == b'/' {
        prefix
    } else {
        prefix.push(b'/')
    }
}

pub open spec fn wf_key(key: model::AStoreKey, bucket_ms: u64) -> bool {
    match key {
        model::AStoreKey::Document(value)
        | model::AStoreKey::Schedule(value)
        | model::AStoreKey::Node(value) => valid_utf8(value),
        model::AStoreKey::TimerOrigin {
            bucket, deadline, origin, token: _, by,
        } => {
            &&& valid_utf8(origin)
            &&& valid_utf8(by)
            &&& bucket == bucket_of(deadline, bucket_ms)
        }
        model::AStoreKey::TimerSchedule {
            bucket, deadline, id, token: _, by,
        } => {
            &&& valid_utf8(id)
            &&& valid_utf8(by)
            &&& bucket == bucket_of(deadline, bucket_ms)
        }
        model::AStoreKey::Membership => true,
    }
}

pub open spec fn key_text_wf(key: model::AStoreKey) -> bool {
    match key {
        model::AStoreKey::Document(value)
        | model::AStoreKey::Schedule(value)
        | model::AStoreKey::Node(value) => valid_utf8(value),
        model::AStoreKey::TimerOrigin { origin, by, .. } =>
            valid_utf8(origin) && valid_utf8(by),
        model::AStoreKey::TimerSchedule { id, by, .. } =>
            valid_utf8(id) && valid_utf8(by),
        model::AStoreKey::Membership => true,
    }
}

pub open spec fn key_suffix(key: model::AStoreKey) -> Seq<u8> {
    match key {
        model::AStoreKey::Document(origin) => {
            seq![b'w', b'f', b'/'] + percent_encode(origin)
        }
        model::AStoreKey::Schedule(id) => {
            seq![b's', b'c', b'h', b'e', b'd', b'/']
                + percent_encode(id)
        }
        model::AStoreKey::TimerOrigin {
            bucket, deadline, origin, token, by,
        } => {
            seq![b't', b'/'] + decimal20(bucket) + seq![b'/']
                + decimal20(deadline) + seq![b'_']
                + percent_encode(origin) + seq![b'@']
                + hex16(token) + seq![b'~'] + percent_encode(by)
        }
        model::AStoreKey::TimerSchedule {
            bucket, deadline, id, token, by,
        } => {
            seq![b't', b'/'] + decimal20(bucket) + seq![b'/']
                + decimal20(deadline)
                + seq![b'_', b's', b'c', b'h', b'e', b'd', b':']
                + percent_encode(id) + seq![b'@']
                + hex16(token) + seq![b'~'] + percent_encode(by)
        }
        model::AStoreKey::Node(id) => {
            seq![b'n', b'o', b'd', b'e', b's', b'/']
                + percent_encode(id)
        }
        model::AStoreKey::Membership => {
            seq![b'm', b'e', b'm', b'b', b'e', b'r', b's']
        }
    }
}

pub open spec fn encode_store_key_spec(
    prefix: Seq<u8>,
    bucket_ms: u64,
    key: model::AStoreKey,
) -> Option<Seq<u8>> {
    if wf_key(key, bucket_ms) {
        Some(normalized_prefix(prefix) + key_suffix(key))
    } else {
        None
    }
}

fn push_all(out: &mut Vec<u8>, bytes: &Vec<u8>)
    ensures final(out)@ == old(out)@ + bytes@,
{
    let ghost before = out@;
    let mut i = 0usize;
    while i < bytes.len()
        invariant
            i <= bytes.len(),
            out@ == before + bytes@.subrange(0, i as int),
        decreases bytes.len() - i,
    {
        out.push(bytes[i]);
        i += 1;
    }
}

fn normalized_prefix_exec(prefix: &Vec<u8>) -> (result: Vec<u8>)
    ensures result@ == normalized_prefix(prefix@),
{
    let mut result = copy_range(prefix, 0, prefix.len());
    if result.len() > 0 && result[result.len() - 1] != b'/' {
        result.push(b'/');
    }
    result
}

fn push_literal(out: &mut Vec<u8>, literal: &[u8])
    ensures final(out)@ == old(out)@ + literal@,
{
    let ghost before = out@;
    let mut i = 0usize;
    while i < literal.len()
        invariant
            i <= literal.len(),
            out@ == before + literal@.subrange(0, i as int),
        decreases literal.len() - i,
    {
        out.push(literal[i]);
        i += 1;
    }
}

fn append_component(out: &mut Vec<u8>, value: &Text)
    ensures final(out)@ == old(out)@ + percent_encode(value@),
{
    let bytes = value.as_bytes();
    let encoded = encode_component(bytes);
    push_all(out, &encoded);
}

fn append_decimal20(out: &mut Vec<u8>, value: u64)
    ensures final(out)@ == old(out)@ + decimal20(value),
{
    let encoded = encode_decimal20(value);
    push_all(out, &encoded);
}

fn append_hex16(out: &mut Vec<u8>, value: u64)
    ensures final(out)@ == old(out)@ + hex16(value),
{
    let encoded = encode_hex16(value);
    push_all(out, &encoded);
}

#[verifier::rlimit(30)]
pub fn encode_store_key_bytes(
    prefix: &Vec<u8>,
    bucket_ms: u64,
    key: &model::StoreKey,
) -> (result: KeyResult<Vec<u8>>)
    ensures
        match result {
            Ok(bytes) => encode_store_key_spec(
                prefix@, bucket_ms, key.deep_view(),
            ) == Some(bytes@),
            Err(_) => encode_store_key_spec(
                prefix@, bucket_ms, key.deep_view(),
            ) is None,
        },
{
    reveal(encode_store_key_spec);
    reveal(wf_key);
    reveal(key_suffix);
    if !key_runtime_wf(key, bucket_ms) {
        return Err("invalid text or noncanonical timer bucket");
    }
    let mut out = normalized_prefix_exec(prefix);
    assert(out@ == normalized_prefix(prefix@));
    match key {
        model::StoreKey::Document(origin) => {
            out.push(b'w');
            out.push(b'f');
            out.push(b'/');
            assert(out@ == normalized_prefix(prefix@)
                + seq![b'w', b'f', b'/']);
            append_component(&mut out, origin);
            assert(out@ == (normalized_prefix(prefix@)
                + seq![b'w', b'f', b'/'])
                + percent_encode(origin@));
            assert(out@ == normalized_prefix(prefix@)
                + key_suffix(key.deep_view()));
        }
        model::StoreKey::Schedule(id) => {
            out.push(b's');
            out.push(b'c');
            out.push(b'h');
            out.push(b'e');
            out.push(b'd');
            out.push(b'/');
            append_component(&mut out, id);
            assert(out@ == normalized_prefix(prefix@)
                + key_suffix(key.deep_view()));
        }
        model::StoreKey::TimerOrigin {
            bucket, deadline, origin, token, by,
        } => {
            out.push(b't');
            out.push(b'/');
            append_decimal20(&mut out, *bucket);
            out.push(b'/');
            append_decimal20(&mut out, *deadline);
            out.push(b'_');
            append_component(&mut out, origin);
            out.push(b'@');
            append_hex16(&mut out, *token);
            out.push(b'~');
            append_component(&mut out, by);
            assert(out@ == normalized_prefix(prefix@)
                + key_suffix(key.deep_view()));
        }
        model::StoreKey::TimerSchedule {
            bucket, deadline, id, token, by,
        } => {
            out.push(b't');
            out.push(b'/');
            append_decimal20(&mut out, *bucket);
            out.push(b'/');
            append_decimal20(&mut out, *deadline);
            out.push(b'_');
            out.push(b's');
            out.push(b'c');
            out.push(b'h');
            out.push(b'e');
            out.push(b'd');
            out.push(b':');
            append_component(&mut out, id);
            out.push(b'@');
            append_hex16(&mut out, *token);
            out.push(b'~');
            append_component(&mut out, by);
            assert(out@ == normalized_prefix(prefix@)
                + key_suffix(key.deep_view()));
        }
        model::StoreKey::Node(id) => {
            out.push(b'n');
            out.push(b'o');
            out.push(b'd');
            out.push(b'e');
            out.push(b's');
            out.push(b'/');
            append_component(&mut out, id);
            assert(out@ == normalized_prefix(prefix@)
                + key_suffix(key.deep_view()));
        }
        model::StoreKey::Membership => {
            out.push(b'm');
            out.push(b'e');
            out.push(b'm');
            out.push(b'b');
            out.push(b'e');
            out.push(b'r');
            out.push(b's');
            assert(out@ == normalized_prefix(prefix@)
                + key_suffix(key.deep_view()));
        }
    }
    assert(out@ == normalized_prefix(prefix@)
        + key_suffix(key.deep_view()));
    Ok(out)
}

fn key_runtime_wf(
    key: &model::StoreKey,
    bucket_ms: u64,
) -> (result: bool)
    ensures result == wf_key(key.deep_view(), bucket_ms),
{
    reveal(wf_key);
    match key {
        model::StoreKey::Document(value)
        | model::StoreKey::Schedule(value)
        | model::StoreKey::Node(value) => {
            crate::text::is_valid_utf8(value.as_bytes())
        }
        model::StoreKey::TimerOrigin {
            bucket, deadline, origin, by, ..
        } => {
            crate::text::is_valid_utf8(origin.as_bytes())
                && crate::text::is_valid_utf8(by.as_bytes())
                && *bucket == bucket_of_exec(*deadline, bucket_ms)
        }
        model::StoreKey::TimerSchedule {
            bucket, deadline, id, by, ..
        } => {
            crate::text::is_valid_utf8(id.as_bytes())
                && crate::text::is_valid_utf8(by.as_bytes())
                && *bucket == bucket_of_exec(*deadline, bucket_ms)
        }
        model::StoreKey::Membership => true,
    }
}

pub fn bucket_of_exec(
    deadline: u64,
    bucket_ms: u64,
) -> (bucket: u64)
    ensures bucket == bucket_of(deadline, bucket_ms),
{
    let width = if bucket_ms == 0 { 1 } else { bucket_ms };
    let remainder = deadline % width;
    proof {
        vstd::arithmetic::div_mod::lemma_mod_decreases(
            deadline as nat, width as nat,
        );
    }
    let bucket = deadline - remainder;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
            deadline as int, width as int,
        );
        vstd::arithmetic::mul::lemma_mul_is_commutative(
            deadline as int / width as int, width as int,
        );
        assert(deadline as int - remainder as int
            == deadline as int / width as int * width as int);
    }
    bucket
}

pub open spec fn starts_with(bytes: Seq<u8>, prefix: Seq<u8>) -> bool {
    prefix.len() <= bytes.len()
        && bytes.subrange(0, prefix.len() as int) == prefix
}

pub open spec fn strip_prefix(
    bytes: Seq<u8>,
    prefix: Seq<u8>,
) -> Option<Seq<u8>> {
    if starts_with(bytes, prefix) {
        Some(bytes.subrange(prefix.len() as int, bytes.len() as int))
    } else {
        None
    }
}

fn starts_with_exec(
    bytes: &Vec<u8>,
    prefix: &Vec<u8>,
) -> (result: bool)
    ensures result == starts_with(bytes@, prefix@),
{
    reveal(starts_with);
    if prefix.len() > bytes.len() {
        return false;
    }
    let mut i = 0usize;
    while i < prefix.len()
        invariant
            i <= prefix.len(),
            prefix.len() <= bytes.len(),
            bytes@.subrange(0, i as int)
                == prefix@.subrange(0, i as int),
        decreases prefix.len() - i,
    {
        if bytes[i] != prefix[i] {
            assert(bytes@.subrange(0, prefix.len() as int)
                != prefix@) by {
                assert(bytes@.subrange(0, prefix.len() as int)[i as int]
                    != prefix@[i as int]);
            }
            return false;
        }
        assert(bytes@.subrange(0, (i + 1) as int)
            == bytes@.subrange(0, i as int).push(bytes[i as int]));
        assert(prefix@.subrange(0, (i + 1) as int)
            == prefix@.subrange(0, i as int).push(prefix[i as int]));
        i += 1;
    }
    assert(bytes@.subrange(0, prefix.len() as int) == prefix@);
    true
}

fn strip_prefix_exec(
    bytes: &Vec<u8>,
    prefix: &Vec<u8>,
) -> (result: Option<Vec<u8>>)
    ensures result.deep_view() == strip_prefix(bytes@, prefix@),
{
    if starts_with_exec(bytes, prefix) {
        Some(copy_range(bytes, prefix.len(), bytes.len()))
    } else {
        None
    }
}

fn bytes_equal(left: &Vec<u8>, right: &Vec<u8>) -> (equal: bool)
    ensures equal == (left@ == right@),
{
    if left.len() != right.len() {
        return false;
    }
    let mut i = 0usize;
    while i < left.len()
        invariant
            i <= left.len(),
            left.len() == right.len(),
            left@.subrange(0, i as int)
                == right@.subrange(0, i as int),
        decreases left.len() - i,
    {
        if left[i] != right[i] {
            assert(left@ != right@) by {
                assert(left@[i as int] != right@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    assert(left@.subrange(0, left.len() as int) == left@);
    assert(right@.subrange(0, right.len() as int) == right@);
    assert(left@ =~= right@);
    true
}

pub open spec fn split_once(
    bytes: Seq<u8>,
    delimiter: u8,
) -> Option<(Seq<u8>, Seq<u8>)>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        None
    } else if bytes[0] == delimiter {
        Some((Seq::empty(), bytes.drop_first()))
    } else {
        match split_once(bytes.drop_first(), delimiter) {
            None => None,
            Some((left, right)) => {
                Some((seq![bytes[0]] + left, right))
            }
        }
    }
}

fn split_once_exec(
    bytes: &Vec<u8>,
    delimiter: u8,
) -> (result: Option<(Vec<u8>, Vec<u8>)>)
    ensures result.deep_view() == split_once(bytes@, delimiter),
    decreases bytes.len(),
{
    reveal_with_fuel(split_once, 2);
    if bytes.len() == 0 {
        return None;
    }
    if bytes[0] == delimiter {
        return Some((
            Vec::new(),
            copy_range(bytes, 1, bytes.len()),
        ));
    }
    let tail = copy_range(bytes, 1, bytes.len());
    match split_once_exec(&tail, delimiter) {
        None => None,
        Some((mut left, right)) => {
            let ghost old_left = left@;
            left.insert(0, bytes[0]);
            assert(left@ == seq![bytes@[0]] + old_left);
            Some((left, right))
        }
    }
}

pub open spec fn decode_text_component_spec(
    encoded: Seq<u8>,
) -> Option<Seq<u8>> {
    match percent_decode(encoded) {
        Some(decoded) if
            percent_encode(decoded) == encoded && valid_utf8(decoded) =>
                Some(decoded),
        _ => None,
    }
}

fn decode_text_component(
    encoded: &Vec<u8>,
) -> (result: Option<Text>)
    ensures result.deep_view() == decode_text_component_spec(encoded@),
{
    reveal(decode_text_component_spec);
    let decoded = match decode_component(encoded) {
        None => return None,
        Some(decoded) => decoded,
    };
    assert(percent_decode(encoded@) == Some(decoded@));
    let canonical = encode_component(&decoded);
    if !bytes_equal(&canonical, encoded) {
        assert(percent_encode(decoded@) != encoded@);
        return None;
    }
    assert(percent_encode(decoded@) == encoded@);
    match Text::from_utf8(decoded) {
        None => None,
        Some(text) => Some(text),
    }
}

pub open spec fn has_class(rest: Seq<u8>, name: Seq<u8>) -> bool {
    rest == name
        || starts_with(rest, name + seq![b'/'])
}

pub open spec fn first_segment(rest: Seq<u8>) -> Seq<u8> {
    match split_once(rest, b'/') {
        Some((segment, _)) => segment,
        None => rest,
    }
}

pub open spec fn class_of_spec(
    prefix: Seq<u8>,
    key: Seq<u8>,
) -> Option<KeyClass> {
    match strip_prefix(key, normalized_prefix(prefix)) {
        None => None,
        Some(rest) => {
            let class = first_segment(rest);
            if class == seq![b'w', b'f'] {
                Some(KeyClass::Document)
            } else if class == seq![b's', b'c', b'h', b'e', b'd'] {
                Some(KeyClass::Schedule)
            } else if class == seq![b't'] {
                Some(KeyClass::Timer)
            } else if class == seq![b'n', b'o', b'd', b'e', b's'] {
                Some(KeyClass::Node)
            } else if class == seq![
                b'm', b'e', b'm', b'b', b'e', b'r', b's',
            ] {
                Some(KeyClass::Membership)
            } else {
                None
            }
        }
    }
}

pub open spec fn decode_timer_spec(
    rest: Seq<u8>,
    bucket_ms: u64,
) -> Option<model::AStoreKey> {
    if rest.len() < 42 || rest[20] != b'/' || rest[41] != b'_' {
        None
    } else {
        let bucket_bytes = rest.subrange(0, 20);
        let deadline_bytes = rest.subrange(21, 41);
        let target_and_arm = rest.subrange(42, rest.len() as int);
        match (
            decode_decimal20(bucket_bytes),
            decode_decimal20(deadline_bytes),
            split_once(target_and_arm, b'@'),
        ) {
            (Some(bucket), Some(deadline), Some((target, arm))) => {
                match split_once(arm, b'~') {
                    Some((token_bytes, by_bytes)) => {
                        match (
                            decode_hex16(token_bytes),
                            decode_text_component_spec(by_bytes),
                        ) {
                            (Some(token), Some(by)) if
                                bucket == bucket_of(deadline, bucket_ms) => {
                                let schedule_prefix =
                                    seq![b's', b'c', b'h', b'e', b'd', b':'];
                                match strip_prefix(target, schedule_prefix) {
                                    Some(encoded_id) => {
                                    match decode_text_component_spec(encoded_id) {
                                        Some(id) => Some(
                                            model::AStoreKey::TimerSchedule {
                                                bucket,
                                                deadline,
                                                id,
                                                token,
                                                by,
                                            },
                                        ),
                                        None => None,
                                    }
                                    }
                                    None => {
                                    match decode_text_component_spec(target) {
                                        Some(origin) => Some(
                                            model::AStoreKey::TimerOrigin {
                                                bucket,
                                                deadline,
                                                origin,
                                                token,
                                                by,
                                            },
                                        ),
                                        None => None,
                                    }
                                    }
                                }
                            }
                            _ => None,
                        }
                    }
                    None => None,
                }
            }
            _ => None,
        }
    }
}

pub open spec fn decode_store_key_spec(
    prefix: Seq<u8>,
    bucket_ms: u64,
    key: Seq<u8>,
) -> Option<model::AStoreKey> {
    match strip_prefix(key, normalized_prefix(prefix)) {
        None => None,
        Some(rest) => {
            if rest == seq![
                b'm', b'e', b'm', b'b', b'e', b'r', b's',
            ] {
                Some(model::AStoreKey::Membership)
            } else {
                match strip_prefix(rest, seq![b'w', b'f', b'/']) {
                    Some(encoded) => {
                        match decode_text_component_spec(encoded) {
                            Some(origin) =>
                                Some(model::AStoreKey::Document(origin)),
                            None => None,
                        }
                    }
                    None => {
                        match strip_prefix(
                            rest,
                            seq![b's', b'c', b'h', b'e', b'd', b'/'],
                        ) {
                            Some(encoded) => {
                                match decode_text_component_spec(encoded) {
                                    Some(id) =>
                                        Some(model::AStoreKey::Schedule(id)),
                                    None => None,
                                }
                            }
                            None => {
                                match strip_prefix(
                                    rest,
                                    seq![b'n', b'o', b'd', b'e', b's', b'/'],
                                ) {
                                    Some(encoded) => {
                                        match decode_text_component_spec(encoded) {
                                            Some(id) => Some(
                                                model::AStoreKey::Node(id),
                                            ),
                                            None => None,
                                        }
                                    }
                                    None => {
                                        match strip_prefix(
                                            rest, seq![b't', b'/'],
                                        ) {
                                            Some(timer) =>
                                                decode_timer_spec(
                                                    timer, bucket_ms,
                                                ),
                                            None => None,
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

fn literal_wf() -> (value: Vec<u8>)
    ensures value@ == seq![b'w', b'f', b'/'],
{
    let mut value = Vec::new();
    value.push(b'w');
    value.push(b'f');
    value.push(b'/');
    value
}

fn literal_sched() -> (value: Vec<u8>)
    ensures value@ == seq![b's', b'c', b'h', b'e', b'd', b'/'],
{
    let mut value = Vec::new();
    value.push(b's');
    value.push(b'c');
    value.push(b'h');
    value.push(b'e');
    value.push(b'd');
    value.push(b'/');
    value
}

fn literal_nodes() -> (value: Vec<u8>)
    ensures value@ == seq![b'n', b'o', b'd', b'e', b's', b'/'],
{
    let mut value = Vec::new();
    value.push(b'n');
    value.push(b'o');
    value.push(b'd');
    value.push(b'e');
    value.push(b's');
    value.push(b'/');
    value
}

fn literal_timer() -> (value: Vec<u8>)
    ensures value@ == seq![b't', b'/'],
{
    let mut value = Vec::new();
    value.push(b't');
    value.push(b'/');
    value
}

fn literal_schedule_target() -> (value: Vec<u8>)
    ensures
        value@ == seq![b's', b'c', b'h', b'e', b'd', b':'],
{
    let mut value = Vec::new();
    value.push(b's');
    value.push(b'c');
    value.push(b'h');
    value.push(b'e');
    value.push(b'd');
    value.push(b':');
    value
}

fn literal_members() -> (value: Vec<u8>)
    ensures
        value@ == seq![b'm', b'e', b'm', b'b', b'e', b'r', b's'],
{
    let mut value = Vec::new();
    value.push(b'm');
    value.push(b'e');
    value.push(b'm');
    value.push(b'b');
    value.push(b'e');
    value.push(b'r');
    value.push(b's');
    value
}

fn literal_class_wf() -> (value: Vec<u8>)
    ensures value@ == seq![b'w', b'f'],
{
    let mut value = Vec::new();
    value.push(b'w');
    value.push(b'f');
    value
}

fn literal_class_sched() -> (value: Vec<u8>)
    ensures value@ == seq![b's', b'c', b'h', b'e', b'd'],
{
    let mut value = Vec::new();
    value.push(b's');
    value.push(b'c');
    value.push(b'h');
    value.push(b'e');
    value.push(b'd');
    value
}

fn literal_class_timer() -> (value: Vec<u8>)
    ensures value@ == seq![b't'],
{
    let mut value = Vec::new();
    value.push(b't');
    value
}

fn literal_class_nodes() -> (value: Vec<u8>)
    ensures value@ == seq![b'n', b'o', b'd', b'e', b's'],
{
    let mut value = Vec::new();
    value.push(b'n');
    value.push(b'o');
    value.push(b'd');
    value.push(b'e');
    value.push(b's');
    value
}

fn is_members(bytes: &Vec<u8>) -> (result: bool)
    ensures result == (
        bytes@ == seq![b'm', b'e', b'm', b'b', b'e', b'r', b's']
    ),
{
    let members = literal_members();
    bytes_equal(bytes, &members)
}

pub fn class_of_bytes(
    prefix: &Vec<u8>,
    key: &Vec<u8>,
) -> (result: Option<KeyClass>)
    ensures result == class_of_spec(prefix@, key@),
{
    reveal(class_of_spec);
    reveal(first_segment);
    let normalized = normalized_prefix_exec(prefix);
    assert(normalized@ == normalized_prefix(prefix@));
    let rest = match strip_prefix_exec(key, &normalized) {
        None => return None,
        Some(rest) => rest,
    };
    assert(strip_prefix(key@, normalized_prefix(prefix@))
        == Some(rest@));
    let class = match split_once_exec(&rest, b'/') {
        Some((segment, remainder)) => {
            assert(split_once(rest@, b'/')
                == Some((segment@, remainder@)));
            segment
        }
        None => {
            assert(split_once(rest@, b'/') is None);
            rest
        }
    };
    assert(class@ == first_segment(rest@));
    let wf = literal_class_wf();
    if bytes_equal(&class, &wf) {
        return Some(KeyClass::Document);
    }
    assert(class@ != wf@);
    let sched = literal_class_sched();
    if bytes_equal(&class, &sched) {
        return Some(KeyClass::Schedule);
    }
    assert(class@ != sched@);
    let timer = literal_class_timer();
    if bytes_equal(&class, &timer) {
        return Some(KeyClass::Timer);
    }
    assert(class@ != timer@);
    let nodes = literal_class_nodes();
    if bytes_equal(&class, &nodes) {
        return Some(KeyClass::Node);
    }
    assert(class@ != nodes@);
    let members = literal_members();
    if bytes_equal(&class, &members) {
        return Some(KeyClass::Membership);
    }
    assert(class@ != members@);
    None
}

#[verifier::rlimit(30)]
fn decode_timer_exec(
    rest: &Vec<u8>,
    bucket_ms: u64,
) -> (result: Option<model::StoreKey>)
    ensures result.deep_view() == decode_timer_spec(rest@, bucket_ms),
{
    reveal(decode_timer_spec);
    if rest.len() < 42 || rest[20] != b'/' || rest[41] != b'_' {
        return None;
    }
    let bucket_bytes = copy_range(rest, 0, 20);
    let deadline_bytes = copy_range(rest, 21, 41);
    let target_and_arm = copy_range(rest, 42, rest.len());
    let bucket = match decode_decimal20_exec(&bucket_bytes) {
        None => {
            assert(decode_decimal20(bucket_bytes@) is None);
            return None;
        }
        Some(value) => value,
    };
    assert(decode_decimal20(bucket_bytes@) == Some(bucket));
    let deadline = match decode_decimal20_exec(&deadline_bytes) {
        None => {
            assert(decode_decimal20(deadline_bytes@) is None);
            return None;
        }
        Some(value) => value,
    };
    assert(decode_decimal20(deadline_bytes@) == Some(deadline));
    let (target, arm) = match split_once_exec(&target_and_arm, b'@') {
        None => {
            assert(split_once(target_and_arm@, b'@') is None);
            return None;
        }
        Some(parts) => parts,
    };
    assert(split_once(target_and_arm@, b'@')
        == Some((target@, arm@)));
    let (token_bytes, by_bytes) = match split_once_exec(&arm, b'~') {
        None => {
            assert(split_once(arm@, b'~') is None);
            return None;
        }
        Some(parts) => parts,
    };
    assert(split_once(arm@, b'~')
        == Some((token_bytes@, by_bytes@)));
    let token = match decode_hex16_exec(&token_bytes) {
        None => {
            assert(decode_hex16(token_bytes@) is None);
            return None;
        }
        Some(value) => value,
    };
    assert(decode_hex16(token_bytes@) == Some(token));
    let by = match decode_text_component(&by_bytes) {
        None => {
            assert(decode_text_component_spec(by_bytes@) is None);
            return None;
        }
        Some(value) => value,
    };
    assert(decode_text_component_spec(by_bytes@) == Some(by@));
    if bucket != bucket_of_exec(deadline, bucket_ms) {
        return None;
    }
    let schedule_prefix = literal_schedule_target();
    match strip_prefix_exec(&target, &schedule_prefix) {
        Some(encoded_id) => {
            assert(strip_prefix(target@, schedule_prefix@)
                == Some(encoded_id@));
            let id = match decode_text_component(&encoded_id) {
                None => return None,
                Some(value) => value,
            };
            Some(model::StoreKey::TimerSchedule {
                bucket,
                deadline,
                id,
                token,
                by,
            })
        }
        None => {
            assert(strip_prefix(target@, schedule_prefix@) is None);
            let origin = match decode_text_component(&target) {
                None => return None,
                Some(value) => value,
            };
            Some(model::StoreKey::TimerOrigin {
                bucket,
                deadline,
                origin,
                token,
                by,
            })
        }
    }
}

#[verifier::rlimit(30)]
pub fn decode_store_key_bytes(
    prefix: &Vec<u8>,
    bucket_ms: u64,
    key: &Vec<u8>,
) -> (result: KeyResult<model::StoreKey>)
    ensures
        match result {
            Ok(value) => decode_store_key_spec(
                prefix@, bucket_ms, key@,
            ) == Some(value.deep_view()),
            Err(_) => decode_store_key_spec(
                prefix@, bucket_ms, key@,
            ) is None,
        },
{
    reveal(decode_store_key_spec);
    let normalized = normalized_prefix_exec(prefix);
    assert(normalized@ == normalized_prefix(prefix@));
    let rest = match strip_prefix_exec(key, &normalized) {
        None => return Err("key is outside configured prefix"),
        Some(rest) => rest,
    };
    assert(strip_prefix(key@, normalized_prefix(prefix@))
        == Some(rest@));
    if is_members(&rest) {
        return Ok(model::StoreKey::Membership);
    }
    assert(rest@ != seq![b'm', b'e', b'm', b'b', b'e', b'r', b's']);
    let wf = literal_wf();
    match strip_prefix_exec(&rest, &wf) {
        Some(encoded) => {
            assert(strip_prefix(rest@, wf@) == Some(encoded@));
            return match decode_text_component(&encoded) {
                Some(origin) => {
                    assert(decode_text_component_spec(encoded@)
                        == Some(origin@));
                    Ok(model::StoreKey::Document(origin))
                }
                None => {
                    assert(decode_text_component_spec(encoded@) is None);
                    Err("invalid document key")
                }
            };
        }
        None => {
            assert(strip_prefix(rest@, wf@) is None);
        }
    }
    let sched = literal_sched();
    match strip_prefix_exec(&rest, &sched) {
        Some(encoded) => {
            assert(strip_prefix(rest@, sched@) == Some(encoded@));
            return match decode_text_component(&encoded) {
                Some(id) => {
                    assert(decode_text_component_spec(encoded@)
                        == Some(id@));
                    Ok(model::StoreKey::Schedule(id))
                }
                None => {
                    assert(decode_text_component_spec(encoded@) is None);
                    Err("invalid schedule key")
                }
            };
        }
        None => {
            assert(strip_prefix(rest@, sched@) is None);
        }
    }
    let nodes = literal_nodes();
    match strip_prefix_exec(&rest, &nodes) {
        Some(encoded) => {
            assert(strip_prefix(rest@, nodes@) == Some(encoded@));
            return match decode_text_component(&encoded) {
                Some(id) => {
                    assert(decode_text_component_spec(encoded@)
                        == Some(id@));
                    Ok(model::StoreKey::Node(id))
                }
                None => {
                    assert(decode_text_component_spec(encoded@) is None);
                    Err("invalid node key")
                }
            };
        }
        None => {
            assert(strip_prefix(rest@, nodes@) is None);
        }
    }
    let timer = literal_timer();
    match strip_prefix_exec(&rest, &timer) {
        Some(encoded) => {
            assert(strip_prefix(rest@, timer@) == Some(encoded@));
            return match decode_timer_exec(&encoded, bucket_ms) {
                Some(value) => {
                    assert(decode_timer_spec(encoded@, bucket_ms)
                        == Some(value.deep_view()));
                    Ok(value)
                }
                None => {
                    assert(decode_timer_spec(encoded@, bucket_ms) is None);
                    Err("invalid timer key")
                }
            };
        }
        None => {
            assert(strip_prefix(rest@, timer@) is None);
        }
    }
    Err("unknown key class")
}

proof fn lemma_strip_prefix_concat(
    prefix: Seq<u8>,
    suffix: Seq<u8>,
)
    ensures strip_prefix(prefix + suffix, prefix) == Some(suffix),
{
    reveal(starts_with);
    reveal(strip_prefix);
    assert((prefix + suffix).subrange(0, prefix.len() as int)
        == prefix);
    assert((prefix + suffix).subrange(
        prefix.len() as int, (prefix + suffix).len() as int,
    ) == suffix);
}

proof fn lemma_component_round_trip(bytes: Seq<u8>)
    requires valid_utf8(bytes),
    ensures
        decode_text_component_spec(percent_encode(bytes)) == Some(bytes),
{
    lemma_percent_round_trip(bytes);
    reveal(decode_text_component_spec);
}

proof fn lemma_percent_excludes_delimiter(
    bytes: Seq<u8>,
    delimiter: u8,
)
    requires
        delimiter == b'@' || delimiter == b'~' || delimiter == b':',
    ensures
        forall|i: int| 0 <= i < percent_encode(bytes).len()
            ==> #[trigger] percent_encode(bytes)[i] != delimiter,
    decreases bytes.len(),
{
    reveal_with_fuel(percent_encode, 2);
    if bytes.len() > 0 {
        let first = bytes[0];
        let rest = bytes.drop_first();
        lemma_percent_excludes_delimiter(
            rest, delimiter,
        );
        let head = if safe_key_byte(first) {
            seq![first]
        } else {
            seq![
                b'%',
                upper_hex_digit(first / 16),
                upper_hex_digit(first % 16),
            ]
        };
        if safe_key_byte(first) {
            assert(first != delimiter);
        } else {
            lemma_byte_nibbles(first);
            assert(upper_hex_digit(first / 16) != delimiter);
            assert(upper_hex_digit(first % 16) != delimiter);
        }
        assert(percent_encode(bytes) == head + percent_encode(rest));
        assert forall|i: int| 0 <= i < percent_encode(bytes).len()
            implies #[trigger] percent_encode(bytes)[i] != delimiter by {
            if i < head.len() {
                if safe_key_byte(first) {
                    assert(i == 0);
                    assert(head[i] == first);
                } else {
                    assert(head.len() == 3);
                    if i == 0 {
                        assert(head[i] == b'%');
                    } else if i == 1 {
                        assert(head[i] == upper_hex_digit(first / 16));
                    } else {
                        assert(i == 2);
                        assert(head[i] == upper_hex_digit(first % 16));
                    }
                }
            } else {
                assert(percent_encode(bytes)[i]
                    == percent_encode(rest)[i - head.len()]);
            }
        }
    }
}

proof fn lemma_split_once_concat(
    left: Seq<u8>,
    delimiter: u8,
    right: Seq<u8>,
)
    requires
        forall|i: int| 0 <= i < left.len()
            ==> #[trigger] left[i] != delimiter,
    ensures
        split_once(left + seq![delimiter] + right, delimiter)
            == Some((left, right)),
    decreases left.len(),
{
    reveal_with_fuel(split_once, 2);
    if left.len() == 0 {
        assert(left + seq![delimiter] + right
            == seq![delimiter] + right);
    } else {
        let tail = left.drop_first();
        assert forall|i: int| 0 <= i < tail.len()
            implies #[trigger] tail[i] != delimiter by {
            assert(tail[i] == left[i + 1]);
        }
        lemma_split_once_concat(tail, delimiter, right);
        assert((left + seq![delimiter] + right).drop_first()
            == tail + seq![delimiter] + right);
        assert(seq![(left + seq![delimiter] + right)[0]] + tail
            == left);
    }
}

proof fn lemma_hex16_excludes_tilde(value: u64)
    ensures
        forall|i: int| 0 <= i < hex16(value).len()
            ==> #[trigger] hex16(value)[i] != b'~',
{
    reveal(hex16);
    assert forall|i: int| 0 <= i < hex16(value).len()
        implies #[trigger] hex16(value)[i] != b'~' by {
        let digit = fixed_digits(value as int, 16, 16)[i];
        lemma_fixed_digits_bounded(value as int, 16, 16);
        assert(digit < 16);
        reveal(encode_ascii_digit);
        if digit < 10 {
            assert(lower_hex_digit(digit) <= b'9');
        } else {
            assert(lower_hex_digit(digit) <= b'f');
        }
    }
}

#[verifier::rlimit(100)]
proof fn lemma_timer_round_trip(
    key: model::AStoreKey,
    bucket_ms: u64,
)
    requires
        wf_key(key, bucket_ms),
        key is TimerOrigin || key is TimerSchedule,
    ensures
        decode_timer_spec(
            key_suffix(key).subrange(2, key_suffix(key).len() as int),
            bucket_ms,
        ) == Some(key),
{
    reveal(wf_key);
    reveal(key_suffix);
    reveal(decode_timer_spec);
    match key {
        model::AStoreKey::TimerOrigin {
            bucket, deadline, origin, token, by,
        } => {
            lemma_decimal20_round_trip(bucket);
            lemma_decimal20_round_trip(deadline);
            lemma_hex16_round_trip(token);
            lemma_component_round_trip(origin);
            lemma_component_round_trip(by);
            lemma_percent_excludes_delimiter(origin, b'@');
            lemma_percent_excludes_delimiter(origin, b':');
            lemma_percent_excludes_delimiter(by, b'~');
            lemma_split_once_concat(
                percent_encode(origin),
                b'@',
                hex16(token) + seq![b'~'] + percent_encode(by),
            );
            lemma_hex16_excludes_tilde(token);
            lemma_split_once_concat(
                hex16(token), b'~', percent_encode(by),
            );
            lemma_pow10_20_large();
            lemma_fixed_digits_value(bucket as int, 10, 20);
            lemma_fixed_digits_value(deadline as int, 10, 20);
            assert(decimal20(bucket).len() == 20);
            assert(decimal20(deadline).len() == 20);
            assert(key_suffix(key).subrange(
                2, key_suffix(key).len() as int,
            ) == decimal20(bucket) + seq![b'/']
                + decimal20(deadline) + seq![b'_']
                + percent_encode(origin) + seq![b'@']
                + hex16(token) + seq![b'~'] + percent_encode(by));
            let timer = key_suffix(key).subrange(
                2, key_suffix(key).len() as int,
            );
            assert(timer.len() >= 42);
            assert(timer[20] == b'/');
            assert(timer[41] == b'_');
            assert(timer.subrange(0, 20) == decimal20(bucket));
            assert(timer.subrange(21, 41) == decimal20(deadline));
            assert(timer.subrange(42, timer.len() as int)
                == percent_encode(origin) + seq![b'@']
                    + hex16(token) + seq![b'~'] + percent_encode(by));
            assert(timer.subrange(42, timer.len() as int) =~=
                percent_encode(origin) + seq![b'@']
                    + (hex16(token) + seq![b'~']
                        + percent_encode(by)));
            assert(split_once(
                timer.subrange(42, timer.len() as int), b'@',
            ) == Some((
                percent_encode(origin),
                hex16(token) + seq![b'~'] + percent_encode(by),
            )));
            assert(split_once(
                hex16(token) + seq![b'~'] + percent_encode(by), b'~',
            ) == Some((hex16(token), percent_encode(by))));
            assert(strip_prefix(
                percent_encode(origin),
                seq![b's', b'c', b'h', b'e', b'd', b':'],
            ) is None) by {
                if starts_with(
                    percent_encode(origin),
                    seq![b's', b'c', b'h', b'e', b'd', b':'],
                ) {
                    assert(percent_encode(origin).len() >= 6);
                    assert(percent_encode(origin)[5] == b':');
                }
            }
            assert(decode_timer_spec(
                key_suffix(key).subrange(
                    2, key_suffix(key).len() as int,
                ),
                bucket_ms,
            ) == Some(key));
        }
        model::AStoreKey::TimerSchedule {
            bucket, deadline, id, token, by,
        } => {
            lemma_decimal20_round_trip(bucket);
            lemma_decimal20_round_trip(deadline);
            lemma_hex16_round_trip(token);
            lemma_component_round_trip(id);
            lemma_component_round_trip(by);
            lemma_percent_excludes_delimiter(id, b'@');
            lemma_percent_excludes_delimiter(by, b'~');
            let target = seq![
                b's', b'c', b'h', b'e', b'd', b':',
            ] + percent_encode(id);
            assert forall|i: int| 0 <= i < target.len()
                implies #[trigger] target[i] != b'@' by {
                if i < 6 {
                    assert(target[i] != b'@');
                } else {
                    assert(target[i] == percent_encode(id)[i - 6]);
                }
            }
            lemma_split_once_concat(
                target,
                b'@',
                hex16(token) + seq![b'~'] + percent_encode(by),
            );
            lemma_hex16_excludes_tilde(token);
            lemma_split_once_concat(
                hex16(token), b'~', percent_encode(by),
            );
            lemma_strip_prefix_concat(
                seq![b's', b'c', b'h', b'e', b'd', b':'],
                percent_encode(id),
            );
            lemma_pow10_20_large();
            lemma_fixed_digits_value(bucket as int, 10, 20);
            lemma_fixed_digits_value(deadline as int, 10, 20);
            assert(decimal20(bucket).len() == 20);
            assert(decimal20(deadline).len() == 20);
            assert(key_suffix(key).subrange(
                2, key_suffix(key).len() as int,
            ) == decimal20(bucket) + seq![b'/']
                + decimal20(deadline)
                + seq![b'_', b's', b'c', b'h', b'e', b'd', b':']
                + percent_encode(id) + seq![b'@']
                + hex16(token) + seq![b'~'] + percent_encode(by));
            let timer = key_suffix(key).subrange(
                2, key_suffix(key).len() as int,
            );
            assert(timer.len() >= 42);
            assert(timer[20] == b'/');
            assert(timer[41] == b'_');
            assert(timer.subrange(0, 20) == decimal20(bucket));
            assert(timer.subrange(21, 41) == decimal20(deadline));
            assert(timer.subrange(42, timer.len() as int)
                == target + seq![b'@']
                    + hex16(token) + seq![b'~'] + percent_encode(by));
            assert(timer.subrange(42, timer.len() as int) =~=
                target + seq![b'@']
                    + (hex16(token) + seq![b'~']
                        + percent_encode(by)));
            assert(split_once(
                timer.subrange(42, timer.len() as int), b'@',
            ) == Some((
                target,
                hex16(token) + seq![b'~'] + percent_encode(by),
            )));
            assert(split_once(
                hex16(token) + seq![b'~'] + percent_encode(by), b'~',
            ) == Some((hex16(token), percent_encode(by))));
            assert(decode_timer_spec(
                key_suffix(key).subrange(
                    2, key_suffix(key).len() as int,
                ),
                bucket_ms,
            ) == Some(key));
        }
        _ => {}
    }
}

#[verifier::rlimit(40)]
pub proof fn lemma_store_key_round_trip(
    prefix: Seq<u8>,
    bucket_ms: u64,
    key: model::AStoreKey,
)
    requires wf_key(key, bucket_ms),
    ensures
        decode_store_key_spec(
            prefix,
            bucket_ms,
            encode_store_key_spec(prefix, bucket_ms, key)->Some_0,
        ) == Some(key),
{
    reveal(encode_store_key_spec);
    reveal(decode_store_key_spec);
    reveal(key_suffix);
    let normalized = normalized_prefix(prefix);
    lemma_strip_prefix_concat(normalized, key_suffix(key));
    match key {
        model::AStoreKey::Document(origin) => {
            lemma_strip_prefix_concat(
                seq![b'w', b'f', b'/'], percent_encode(origin),
            );
            lemma_component_round_trip(origin);
            assert(decode_store_key_spec(
                prefix, bucket_ms,
                encode_store_key_spec(prefix, bucket_ms, key)->Some_0,
            ) == Some(key));
        }
        model::AStoreKey::Schedule(id) => {
            lemma_strip_prefix_concat(
                seq![b's', b'c', b'h', b'e', b'd', b'/'],
                percent_encode(id),
            );
            lemma_component_round_trip(id);
            assert(decode_store_key_spec(
                prefix, bucket_ms,
                encode_store_key_spec(prefix, bucket_ms, key)->Some_0,
            ) == Some(key));
        }
        model::AStoreKey::Node(id) => {
            lemma_strip_prefix_concat(
                seq![b'n', b'o', b'd', b'e', b's', b'/'],
                percent_encode(id),
            );
            lemma_component_round_trip(id);
            assert(decode_store_key_spec(
                prefix, bucket_ms,
                encode_store_key_spec(prefix, bucket_ms, key)->Some_0,
            ) == Some(key));
        }
        model::AStoreKey::TimerOrigin { .. }
        | model::AStoreKey::TimerSchedule { .. } => {
            let timer = key_suffix(key).subrange(
                2, key_suffix(key).len() as int,
            );
            assert(key_suffix(key) == seq![b't', b'/'] + timer);
            lemma_strip_prefix_concat(
                seq![b't', b'/'],
                timer,
            );
            assert(key_suffix(key)[0] == b't');
            assert(key_suffix(key) != seq![
                b'm', b'e', b'm', b'b', b'e', b'r', b's',
            ]);
            assert(strip_prefix(
                key_suffix(key), seq![b'w', b'f', b'/'],
            ) is None);
            assert(strip_prefix(
                key_suffix(key),
                seq![b's', b'c', b'h', b'e', b'd', b'/'],
            ) is None);
            assert(strip_prefix(
                key_suffix(key),
                seq![b'n', b'o', b'd', b'e', b's', b'/'],
            ) is None);
            lemma_timer_round_trip(key, bucket_ms);
            assert(decode_store_key_spec(
                prefix, bucket_ms,
                encode_store_key_spec(prefix, bucket_ms, key)->Some_0,
            ) == Some(key));
        }
        model::AStoreKey::Membership => {
            assert(decode_store_key_spec(
                prefix, bucket_ms,
                encode_store_key_spec(prefix, bucket_ms, key)->Some_0,
            ) == Some(key));
        }
    }
}

proof fn lemma_lex_push_same(
    prefix: Seq<u8>,
    left: u8,
    right: u8,
)
    ensures
        lex_less(prefix.push(left), prefix.push(right))
            == (left < right),
    decreases prefix.len(),
{
    reveal_with_fuel(lex_less, 2);
    if prefix.len() > 0 {
        lemma_lex_push_same(prefix.drop_first(), left, right);
        assert(prefix.push(left).drop_first()
            == prefix.drop_first().push(left));
        assert(prefix.push(right).drop_first()
            == prefix.drop_first().push(right));
    }
}

proof fn lemma_lex_push_preserves(
    left: Seq<u8>,
    right: Seq<u8>,
    left_last: u8,
    right_last: u8,
)
    requires
        left.len() == right.len(),
        lex_less(left, right),
    ensures
        lex_less(left.push(left_last), right.push(right_last)),
    decreases left.len(),
{
    reveal_with_fuel(lex_less, 2);
    if left.len() > 0 && left[0] == right[0] {
        lemma_lex_push_preserves(
            left.drop_first(),
            right.drop_first(),
            left_last,
            right_last,
        );
        assert(left.push(left_last).drop_first()
            == left.drop_first().push(left_last));
        assert(right.push(right_last).drop_first()
            == right.drop_first().push(right_last));
    }
}

proof fn lemma_fixed_digits_lex(
    left: int,
    right: int,
    base: int,
    width: nat,
)
    requires
        base > 1,
        base <= 16,
        0 <= left < right,
        right < pow(base, width),
    ensures
        lex_less(
            fixed_digits(left, base, width),
            fixed_digits(right, base, width),
        ),
    decreases width,
{
    assert(width > 0);
    let p = pow(base, (width - 1) as nat);
    let left_q = left / base;
    let right_q = right / base;
    let left_r = left % base;
    let right_r = right % base;
    lemma_pow_positive(base, (width - 1) as nat);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(
        left, right, base,
    );
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        left, base,
    );
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        right, base,
    );
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(left, base);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(right, base);
    assert(0 <= left_q <= right_q);
    assert(0 <= left_r < base);
    assert(0 <= right_r < base);
    assert(left == base * left_q + left_r);
    assert(right == base * right_q + right_r);
    assert(right_q < p) by {
        if right_q >= p {
            vstd::arithmetic::mul::lemma_mul_inequality(
                p, right_q, base,
            );
            assert(base * right_q >= base * p);
            assert(right >= base * right_q);
            assert(pow(base, width) == base * p);
        }
    }
    reveal_with_fuel(fixed_digits, 2);
    let left_prefix =
        fixed_digits(left_q, base, (width - 1) as nat);
    let right_prefix =
        fixed_digits(right_q, base, (width - 1) as nat);
    assert(fixed_digits(left, base, width)
        == left_prefix.push(left_r as u8));
    assert(fixed_digits(right, base, width)
        == right_prefix.push(right_r as u8));
    if left_q < right_q {
        lemma_fixed_digits_lex(
            left_q, right_q, base, (width - 1) as nat,
        );
        lemma_fixed_digits_value(
            left_q, base, (width - 1) as nat,
        );
        lemma_fixed_digits_value(
            right_q, base, (width - 1) as nat,
        );
        lemma_lex_push_preserves(
            left_prefix,
            right_prefix,
            left_r as u8,
            right_r as u8,
        );
    } else {
        assert(left_q == right_q);
        assert(left_r < right_r);
        lemma_lex_push_same(
            left_prefix, left_r as u8, right_r as u8,
        );
    }
}

proof fn lemma_decimal_map_lex(
    left: Seq<u8>,
    right: Seq<u8>,
)
    requires
        left.len() == right.len(),
        lex_less(left, right),
        forall|i: int| 0 <= i < left.len()
            ==> #[trigger] left[i] < 10,
        forall|i: int| 0 <= i < right.len()
            ==> #[trigger] right[i] < 10,
    ensures
        lex_less(
            left.map_values(
                |digit: u8| encode_ascii_digit(digit, false),
            ),
            right.map_values(
                |digit: u8| encode_ascii_digit(digit, false),
            ),
        ),
    decreases left.len(),
{
    reveal_with_fuel(lex_less, 2);
    if left.len() > 0 {
        let left_encoded = left.map_values(
            |digit: u8| encode_ascii_digit(digit, false),
        );
        let right_encoded = right.map_values(
            |digit: u8| encode_ascii_digit(digit, false),
        );
        assert(left_encoded.len() == left.len());
        assert(right_encoded.len() == right.len());
        assert(left_encoded[0]
            == encode_ascii_digit(left[0], false));
        assert(right_encoded[0]
            == encode_ascii_digit(right[0], false));
        assert(left_encoded.drop_first() =~=
            left.drop_first().map_values(
                |digit: u8| encode_ascii_digit(digit, false),
            ));
        assert(right_encoded.drop_first() =~=
            right.drop_first().map_values(
                |digit: u8| encode_ascii_digit(digit, false),
            ));
        if left[0] == right[0] {
            lemma_decimal_map_lex(
                left.drop_first(), right.drop_first(),
            );
        } else {
            assert(left[0] < right[0]);
            reveal(encode_ascii_digit);
            assert(encode_ascii_digit(left[0], false)
                < encode_ascii_digit(right[0], false));
        }
    }
}

pub proof fn lemma_decimal20_lexicographic(
    left: u64,
    right: u64,
)
    requires left < right,
    ensures lex_less(decimal20(left), decimal20(right)),
{
    lemma_pow10_20_large();
    lemma_fixed_digits_lex(
        left as int, right as int, 10, 20,
    );
    lemma_fixed_digits_bounded(left as int, 10, 20);
    lemma_fixed_digits_bounded(right as int, 10, 20);
    lemma_fixed_digits_value(left as int, 10, 20);
    lemma_fixed_digits_value(right as int, 10, 20);
    lemma_decimal_map_lex(
        fixed_digits(left as int, 10, 20),
        fixed_digits(right as int, 10, 20),
    );
    reveal(decimal20);
}

proof fn lemma_lex_irreflexive(value: Seq<u8>)
    ensures !lex_less(value, value),
    decreases value.len(),
{
    reveal_with_fuel(lex_less, 2);
    if value.len() > 0 {
        lemma_lex_irreflexive(value.drop_first());
    }
}

proof fn lemma_lex_asymmetric(left: Seq<u8>, right: Seq<u8>)
    requires lex_less(left, right),
    ensures !lex_less(right, left),
    decreases left.len(),
{
    reveal_with_fuel(lex_less, 2);
    if left.len() > 0 && right.len() > 0 && left[0] == right[0] {
        lemma_lex_asymmetric(left.drop_first(), right.drop_first());
    }
}

pub proof fn lemma_decimal20_lexicographic_iff(
    left: u64,
    right: u64,
)
    ensures
        lex_less(decimal20(left), decimal20(right))
            == (left < right),
{
    if left < right {
        lemma_decimal20_lexicographic(left, right);
    } else if left == right {
        lemma_lex_irreflexive(decimal20(left));
    } else {
        lemma_decimal20_lexicographic(right, left);
        lemma_lex_asymmetric(decimal20(right), decimal20(left));
    }
}

pub open spec fn ascii_bytes(bytes: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < bytes.len()
        ==> #[trigger] bytes[i] <= 0x7f
}

proof fn lemma_ascii_concat(left: Seq<u8>, right: Seq<u8>)
    requires
        ascii_bytes(left),
        ascii_bytes(right),
    ensures ascii_bytes(left + right),
{
    assert forall|i: int| 0 <= i < (left + right).len()
        implies #[trigger] (left + right)[i] <= 0x7f by {
        if i < left.len() {
            assert((left + right)[i] == left[i]);
        } else {
            assert((left + right)[i] == right[i - left.len()]);
        }
    }
}

proof fn lemma_ascii_valid_utf8(bytes: Seq<u8>)
    requires ascii_bytes(bytes),
    ensures valid_utf8(bytes),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        assert(bytes[0] <= 0x7f);
        assert forall|i: int| 0 <= i < bytes.drop_first().len()
            implies #[trigger] bytes.drop_first()[i] <= 0x7f by {
            assert(bytes.drop_first()[i] == bytes[i + 1]);
        }
        lemma_ascii_valid_utf8(bytes.drop_first());
        reveal_with_fuel(valid_utf8, 2);
        assert(crate::text::utf8_unit_width(bytes) == 1);
        assert(bytes.subrange(1, bytes.len() as int)
            == bytes.drop_first());
    }
}

proof fn lemma_percent_ascii(bytes: Seq<u8>)
    ensures ascii_bytes(percent_encode(bytes)),
    decreases bytes.len(),
{
    reveal_with_fuel(percent_encode, 2);
    if bytes.len() > 0 {
        lemma_percent_ascii(bytes.drop_first());
        let first = bytes[0];
        let head = if safe_key_byte(first) {
            seq![first]
        } else {
            seq![
                b'%',
                upper_hex_digit(first / 16),
                upper_hex_digit(first % 16),
            ]
        };
        if safe_key_byte(first) {
            assert(first <= 0x7f);
        } else {
            lemma_byte_nibbles(first);
            assert(upper_hex_digit(first / 16) <= b'F');
            assert(upper_hex_digit(first % 16) <= b'F');
        }
        assert(ascii_bytes(head));
        lemma_ascii_concat(head, percent_encode(bytes.drop_first()));
    }
}

proof fn lemma_decimal20_ascii(value: u64)
    ensures ascii_bytes(decimal20(value)),
{
    reveal(decimal20);
    lemma_fixed_digits_bounded(value as int, 10, 20);
    assert forall|i: int| 0 <= i < decimal20(value).len()
        implies #[trigger] decimal20(value)[i] <= 0x7f by {
        let digit = fixed_digits(value as int, 10, 20)[i];
        assert(digit < 10);
        reveal(encode_ascii_digit);
        assert(encode_ascii_digit(digit, false) <= b'9');
    }
}

proof fn lemma_hex16_ascii(value: u64)
    ensures ascii_bytes(hex16(value)),
{
    reveal(hex16);
    lemma_fixed_digits_bounded(value as int, 16, 16);
    assert forall|i: int| 0 <= i < hex16(value).len()
        implies #[trigger] hex16(value)[i] <= 0x7f by {
        let digit = fixed_digits(value as int, 16, 16)[i];
        assert(digit < 16);
        reveal(encode_ascii_digit);
        if digit < 10 {
            assert(lower_hex_digit(digit) <= b'9');
        } else {
            assert(lower_hex_digit(digit) <= b'f');
        }
    }
}

#[verifier::rlimit(50)]
proof fn lemma_key_suffix_ascii(key: model::AStoreKey)
    ensures ascii_bytes(key_suffix(key)),
{
    reveal(key_suffix);
    match key {
        model::AStoreKey::Document(origin) => {
            lemma_percent_ascii(origin);
            assert(ascii_bytes(seq![b'w', b'f', b'/']));
            lemma_ascii_concat(
                seq![b'w', b'f', b'/'], percent_encode(origin),
            );
        }
        model::AStoreKey::Schedule(id) => {
            lemma_percent_ascii(id);
            assert(ascii_bytes(
                seq![b's', b'c', b'h', b'e', b'd', b'/'],
            ));
            lemma_ascii_concat(
                seq![b's', b'c', b'h', b'e', b'd', b'/'],
                percent_encode(id),
            );
        }
        model::AStoreKey::Node(id) => {
            lemma_percent_ascii(id);
            assert(ascii_bytes(
                seq![b'n', b'o', b'd', b'e', b's', b'/'],
            ));
            lemma_ascii_concat(
                seq![b'n', b'o', b'd', b'e', b's', b'/'],
                percent_encode(id),
            );
        }
        model::AStoreKey::TimerOrigin {
            bucket, deadline, origin, token, by,
        } => {
            lemma_decimal20_ascii(bucket);
            lemma_decimal20_ascii(deadline);
            lemma_hex16_ascii(token);
            lemma_percent_ascii(origin);
            lemma_percent_ascii(by);
            assert(ascii_bytes(seq![b't', b'/']));
            assert(ascii_bytes(seq![b'/']));
            assert(ascii_bytes(seq![b'_']));
            assert(ascii_bytes(seq![b'@']));
            assert(ascii_bytes(seq![b'~']));
            let a = seq![b't', b'/'] + decimal20(bucket);
            lemma_ascii_concat(seq![b't', b'/'], decimal20(bucket));
            let b = a + seq![b'/'];
            lemma_ascii_concat(a, seq![b'/']);
            let c = b + decimal20(deadline);
            lemma_ascii_concat(b, decimal20(deadline));
            let d = c + seq![b'_'];
            lemma_ascii_concat(c, seq![b'_']);
            let e = d + percent_encode(origin);
            lemma_ascii_concat(d, percent_encode(origin));
            let f = e + seq![b'@'];
            lemma_ascii_concat(e, seq![b'@']);
            let g = f + hex16(token);
            lemma_ascii_concat(f, hex16(token));
            let h = g + seq![b'~'];
            lemma_ascii_concat(g, seq![b'~']);
            lemma_ascii_concat(h, percent_encode(by));
        }
        model::AStoreKey::TimerSchedule {
            bucket, deadline, id, token, by,
        } => {
            lemma_decimal20_ascii(bucket);
            lemma_decimal20_ascii(deadline);
            lemma_hex16_ascii(token);
            lemma_percent_ascii(id);
            lemma_percent_ascii(by);
            let literal = seq![
                b'_', b's', b'c', b'h', b'e', b'd', b':',
            ];
            assert(ascii_bytes(seq![b't', b'/']));
            assert(ascii_bytes(seq![b'/']));
            assert(ascii_bytes(literal));
            assert(ascii_bytes(seq![b'@']));
            assert(ascii_bytes(seq![b'~']));
            let a = seq![b't', b'/'] + decimal20(bucket);
            lemma_ascii_concat(seq![b't', b'/'], decimal20(bucket));
            let b = a + seq![b'/'];
            lemma_ascii_concat(a, seq![b'/']);
            let c = b + decimal20(deadline);
            lemma_ascii_concat(b, decimal20(deadline));
            let d = c + literal;
            lemma_ascii_concat(c, literal);
            let e = d + percent_encode(id);
            lemma_ascii_concat(d, percent_encode(id));
            let f = e + seq![b'@'];
            lemma_ascii_concat(e, seq![b'@']);
            let g = f + hex16(token);
            lemma_ascii_concat(f, hex16(token));
            let h = g + seq![b'~'];
            lemma_ascii_concat(g, seq![b'~']);
            lemma_ascii_concat(h, percent_encode(by));
        }
        model::AStoreKey::Membership => {
            assert(ascii_bytes(seq![
                b'm', b'e', b'm', b'b', b'e', b'r', b's',
            ]));
        }
    }
}

proof fn lemma_normalized_prefix_valid(prefix: Seq<u8>)
    requires valid_utf8(prefix),
    ensures valid_utf8(normalized_prefix(prefix)),
{
    reveal(normalized_prefix);
    if prefix.len() == 0 || prefix.last() == b'/' {
        assert(normalized_prefix(prefix) == prefix);
    } else {
        assert(prefix.len() > 0);
        assert(prefix.last() != b'/');
        assert(ascii_bytes(seq![b'/']));
        lemma_ascii_valid_utf8(seq![b'/']);
        crate::text::lemma_valid_utf8_equiv(prefix);
        crate::text::lemma_valid_utf8_equiv(seq![b'/']);
        vstd::utf8::valid_utf8_concat(prefix, seq![b'/']);
        crate::text::lemma_valid_utf8_equiv(prefix + seq![b'/']);
        assert(prefix.push(b'/') == prefix + seq![b'/']);
        assert(normalized_prefix(prefix) == prefix.push(b'/'));
    }
}

pub proof fn lemma_encoded_store_key_valid_utf8(
    prefix: Seq<u8>,
    bucket_ms: u64,
    key: model::AStoreKey,
)
    requires
        valid_utf8(prefix),
        wf_key(key, bucket_ms),
    ensures
        valid_utf8(
            encode_store_key_spec(prefix, bucket_ms, key)->Some_0,
        ),
{
    reveal(encode_store_key_spec);
    lemma_normalized_prefix_valid(prefix);
    lemma_key_suffix_ascii(key);
    lemma_ascii_valid_utf8(key_suffix(key));
    crate::text::lemma_valid_utf8_equiv(normalized_prefix(prefix));
    crate::text::lemma_valid_utf8_equiv(key_suffix(key));
    vstd::utf8::valid_utf8_concat(
        normalized_prefix(prefix), key_suffix(key),
    );
    crate::text::lemma_valid_utf8_equiv(
        normalized_prefix(prefix) + key_suffix(key),
    );
}

pub fn encode_store_key_text(
    prefix: &String,
    bucket_ms: u64,
    key: &model::StoreKey,
) -> (result: KeyResult<String>)
    ensures
        match result {
            Ok(value) => encode_store_key_spec(
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
                key.deep_view(),
            ) == Some(vstd::utf8::encode_utf8(value@)),
            Err(_) => encode_store_key_spec(
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
                key.deep_view(),
            ) is None,
        },
{
    let prefix_text = Text::from_string(prefix);
    let bytes = match encode_store_key_bytes(
        prefix_text.as_bytes(), bucket_ms, key,
    ) {
        Err(error) => return Err(error),
        Ok(bytes) => bytes,
    };
    proof {
        lemma_encoded_store_key_valid_utf8(
            prefix_text@, bucket_ms, key.deep_view(),
        );
    }
    let ghost bytes_view = bytes@;
    let text = Text { bytes };
    let value = text.into_string();
    proof {
        crate::text::lemma_text_string_model_round_trip(bytes_view);
    }
    Ok(value)
}

pub fn decode_store_key_text(
    prefix: &String,
    bucket_ms: u64,
    key: &String,
) -> (result: KeyResult<model::StoreKey>)
    ensures
        match result {
            Ok(value) => decode_store_key_spec(
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
                vstd::utf8::encode_utf8(key@),
            ) == Some(value.deep_view()),
            Err(_) => decode_store_key_spec(
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
                vstd::utf8::encode_utf8(key@),
            ) is None,
        },
{
    let prefix_text = Text::from_string(prefix);
    let key_text = Text::from_string(key);
    decode_store_key_bytes(
        prefix_text.as_bytes(), bucket_ms, key_text.as_bytes(),
    )
}

pub fn class_of_text_key(
    prefix: &String,
    key: &String,
) -> (result: Option<KeyClass>)
    ensures
        result == class_of_spec(
            vstd::utf8::encode_utf8(prefix@),
            vstd::utf8::encode_utf8(key@),
        ),
{
    let prefix_text = Text::from_string(prefix);
    let key_text = Text::from_string(key);
    class_of_bytes(prefix_text.as_bytes(), key_text.as_bytes())
}

pub fn round_trip_store_key_text(
    prefix: &String,
    bucket_ms: u64,
    key: model::StoreKey,
) -> (result: KeyResult<model::StoreKey>)
    requires wf_key(key.deep_view(), bucket_ms),
    ensures
        result is Ok,
        result->Ok_0.deep_view() == key.deep_view(),
{
    let ghost original = key.deep_view();
    let encoded = match encode_store_key_text(prefix, bucket_ms, &key) {
        Ok(encoded) => encoded,
        Err(error) => {
            reveal(encode_store_key_spec);
            assert(false);
            return Err(error);
        }
    };
    proof {
        lemma_store_key_round_trip(
            vstd::utf8::encode_utf8(prefix@),
            bucket_ms,
            original,
        );
    }
    let decoded = match decode_store_key_text(
        prefix, bucket_ms, &encoded,
    ) {
        Ok(decoded) => decoded,
        Err(error) => {
            assert(false);
            return Err(error);
        }
    };
    Ok(decoded)
}

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub enum StringStoreKey {
    Document(String),
    Schedule(String),
    TimerOrigin {
        bucket: u64,
        deadline: u64,
        origin: String,
        token: u64,
        by: String,
    },
    TimerSchedule {
        bucket: u64,
        deadline: u64,
        id: String,
        token: u64,
        by: String,
    },
    Node(String),
    Membership,
}

#[cfg(verus_keep_ghost)]
pub enum AStringStoreKey {
    Document(Seq<char>),
    Schedule(Seq<char>),
    TimerOrigin {
        bucket: u64,
        deadline: u64,
        origin: Seq<char>,
        token: u64,
        by: Seq<char>,
    },
    TimerSchedule {
        bucket: u64,
        deadline: u64,
        id: Seq<char>,
        token: u64,
        by: Seq<char>,
    },
    Node(Seq<char>),
    Membership,
}

#[cfg(verus_keep_ghost)]
impl DeepView for StringStoreKey {
    type V = AStringStoreKey;

    open spec fn deep_view(&self) -> AStringStoreKey {
        match self {
            StringStoreKey::Document(value) =>
                AStringStoreKey::Document(value@),
            StringStoreKey::Schedule(value) =>
                AStringStoreKey::Schedule(value@),
            StringStoreKey::TimerOrigin {
                bucket, deadline, origin, token, by,
            } => AStringStoreKey::TimerOrigin {
                bucket: *bucket,
                deadline: *deadline,
                origin: origin@,
                token: *token,
                by: by@,
            },
            StringStoreKey::TimerSchedule {
                bucket, deadline, id, token, by,
            } => AStringStoreKey::TimerSchedule {
                bucket: *bucket,
                deadline: *deadline,
                id: id@,
                token: *token,
                by: by@,
            },
            StringStoreKey::Node(value) =>
                AStringStoreKey::Node(value@),
            StringStoreKey::Membership =>
                AStringStoreKey::Membership,
        }
    }
}

pub open spec fn string_key_to_model(
    key: AStringStoreKey,
) -> model::AStoreKey {
    match key {
        AStringStoreKey::Document(value) =>
            model::AStoreKey::Document(vstd::utf8::encode_utf8(value)),
        AStringStoreKey::Schedule(value) =>
            model::AStoreKey::Schedule(vstd::utf8::encode_utf8(value)),
        AStringStoreKey::TimerOrigin {
            bucket, deadline, origin, token, by,
        } => model::AStoreKey::TimerOrigin {
            bucket,
            deadline,
            origin: vstd::utf8::encode_utf8(origin),
            token,
            by: vstd::utf8::encode_utf8(by),
        },
        AStringStoreKey::TimerSchedule {
            bucket, deadline, id, token, by,
        } => model::AStoreKey::TimerSchedule {
            bucket,
            deadline,
            id: vstd::utf8::encode_utf8(id),
            token,
            by: vstd::utf8::encode_utf8(by),
        },
        AStringStoreKey::Node(value) =>
            model::AStoreKey::Node(vstd::utf8::encode_utf8(value)),
        AStringStoreKey::Membership => model::AStoreKey::Membership,
    }
}

pub open spec fn model_key_to_string(
    key: model::AStoreKey,
) -> AStringStoreKey {
    match key {
        model::AStoreKey::Document(value) =>
            AStringStoreKey::Document(vstd::utf8::decode_utf8(value)),
        model::AStoreKey::Schedule(value) =>
            AStringStoreKey::Schedule(vstd::utf8::decode_utf8(value)),
        model::AStoreKey::TimerOrigin {
            bucket, deadline, origin, token, by,
        } => AStringStoreKey::TimerOrigin {
            bucket,
            deadline,
            origin: vstd::utf8::decode_utf8(origin),
            token,
            by: vstd::utf8::decode_utf8(by),
        },
        model::AStoreKey::TimerSchedule {
            bucket, deadline, id, token, by,
        } => AStringStoreKey::TimerSchedule {
            bucket,
            deadline,
            id: vstd::utf8::decode_utf8(id),
            token,
            by: vstd::utf8::decode_utf8(by),
        },
        model::AStoreKey::Node(value) =>
            AStringStoreKey::Node(vstd::utf8::decode_utf8(value)),
        model::AStoreKey::Membership => AStringStoreKey::Membership,
    }
}

pub proof fn lemma_string_key_model_round_trip(key: AStringStoreKey)
    ensures
        model_key_to_string(string_key_to_model(key)) == key,
{
    match key {
        AStringStoreKey::Document(value)
        | AStringStoreKey::Schedule(value)
        | AStringStoreKey::Node(value) => {
            vstd::utf8::encode_utf8_decode_utf8(value);
        }
        AStringStoreKey::TimerOrigin { origin, by, .. } => {
            vstd::utf8::encode_utf8_decode_utf8(origin);
            vstd::utf8::encode_utf8_decode_utf8(by);
        }
        AStringStoreKey::TimerSchedule { id, by, .. } => {
            vstd::utf8::encode_utf8_decode_utf8(id);
            vstd::utf8::encode_utf8_decode_utf8(by);
        }
        AStringStoreKey::Membership => {}
    }
}

pub proof fn lemma_model_key_string_round_trip(key: model::AStoreKey)
    requires key_text_wf(key),
    ensures
        string_key_to_model(model_key_to_string(key)) == key,
{
    reveal(key_text_wf);
    match key {
        model::AStoreKey::Document(value)
        | model::AStoreKey::Schedule(value)
        | model::AStoreKey::Node(value) => {
            crate::text::lemma_valid_utf8_equiv(value);
            vstd::utf8::decode_utf8_encode_utf8(value);
        }
        model::AStoreKey::TimerOrigin { origin, by, .. } => {
            crate::text::lemma_valid_utf8_equiv(origin);
            crate::text::lemma_valid_utf8_equiv(by);
            vstd::utf8::decode_utf8_encode_utf8(origin);
            vstd::utf8::decode_utf8_encode_utf8(by);
        }
        model::AStoreKey::TimerSchedule { id, by, .. } => {
            crate::text::lemma_valid_utf8_equiv(id);
            crate::text::lemma_valid_utf8_equiv(by);
            vstd::utf8::decode_utf8_encode_utf8(id);
            vstd::utf8::decode_utf8_encode_utf8(by);
        }
        model::AStoreKey::Membership => {}
    }
}

fn string_key_model(
    key: &StringStoreKey,
) -> (result: model::StoreKey)
    ensures
        result.deep_view() == string_key_to_model(key.deep_view()),
        key_text_wf(result.deep_view()),
{
    match key {
        StringStoreKey::Document(value) =>
            model::StoreKey::Document(Text::from_string(value)),
        StringStoreKey::Schedule(value) =>
            model::StoreKey::Schedule(Text::from_string(value)),
        StringStoreKey::TimerOrigin {
            bucket, deadline, origin, token, by,
        } => model::StoreKey::TimerOrigin {
            bucket: *bucket,
            deadline: *deadline,
            origin: Text::from_string(origin),
            token: *token,
            by: Text::from_string(by),
        },
        StringStoreKey::TimerSchedule {
            bucket, deadline, id, token, by,
        } => model::StoreKey::TimerSchedule {
            bucket: *bucket,
            deadline: *deadline,
            id: Text::from_string(id),
            token: *token,
            by: Text::from_string(by),
        },
        StringStoreKey::Node(value) =>
            model::StoreKey::Node(Text::from_string(value)),
        StringStoreKey::Membership => model::StoreKey::Membership,
    }
}

fn model_key_string(
    key: model::StoreKey,
) -> (result: StringStoreKey)
    requires key_text_wf(key.deep_view()),
    ensures result.deep_view() == model_key_to_string(key.deep_view()),
{
    match key {
        model::StoreKey::Document(value) =>
            StringStoreKey::Document(value.into_string()),
        model::StoreKey::Schedule(value) =>
            StringStoreKey::Schedule(value.into_string()),
        model::StoreKey::TimerOrigin {
            bucket, deadline, origin, token, by,
        } => StringStoreKey::TimerOrigin {
            bucket,
            deadline,
            origin: origin.into_string(),
            token,
            by: by.into_string(),
        },
        model::StoreKey::TimerSchedule {
            bucket, deadline, id, token, by,
        } => StringStoreKey::TimerSchedule {
            bucket,
            deadline,
            id: id.into_string(),
            token,
            by: by.into_string(),
        },
        model::StoreKey::Node(value) =>
            StringStoreKey::Node(value.into_string()),
        model::StoreKey::Membership => StringStoreKey::Membership,
    }
}

pub fn encode_runtime_store_key(
    prefix: &String,
    bucket_ms: u64,
    key: &StringStoreKey,
) -> (result: KeyResult<String>)
    ensures
        match result {
            Ok(value) => encode_store_key_spec(
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
                string_key_to_model(key.deep_view()),
            ) == Some(vstd::utf8::encode_utf8(value@)),
            Err(_) => encode_store_key_spec(
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
                string_key_to_model(key.deep_view()),
            ) is None,
        },
{
    let model = string_key_model(key);
    encode_store_key_text(prefix, bucket_ms, &model)
}

pub fn decode_runtime_store_key(
    prefix: &String,
    bucket_ms: u64,
    key: &String,
) -> (result: KeyResult<StringStoreKey>)
    ensures
        match result {
            Ok(value) => decode_store_key_spec(
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
                vstd::utf8::encode_utf8(key@),
            ) == Some(string_key_to_model(value.deep_view())),
            Err(_) => decode_store_key_spec(
                vstd::utf8::encode_utf8(prefix@),
                bucket_ms,
                vstd::utf8::encode_utf8(key@),
            ) is None,
        },
{
    match decode_store_key_text(prefix, bucket_ms, key) {
        Err(error) => Err(error),
        Ok(model) => {
            let ghost model_view = model.deep_view();
            proof {
                lemma_model_key_string_round_trip(model_view);
            }
            Ok(model_key_string(model))
        }
    }
}

} // verus!
