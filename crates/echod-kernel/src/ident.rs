//! Identifiers and the three string primitives the kernel trusts.
//!
//! An id is `origin:suffix`; the origin is everything before the first `:`.
//! These three functions are `external_body`: their bodies are ordinary Rust
//! and their `ensures` are assumed, not proved. They are the whole of the
//! kernel's trusted computing base beyond vstd.

use vstd::prelude::*;

use crate::types::MAX_TIME;

verus! {

/// Everything before the first `:`, or the whole string if there is none.
pub open spec fn origin(s: Seq<char>) -> Seq<char>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == ':' {
        Seq::empty()
    } else {
        seq![s[0]] + origin(s.drop_first())
    }
}

pub open spec fn same_origin_spec(a: Seq<char>, b: Seq<char>) -> bool {
    origin(a) == origin(b)
}

/// Do two ids share an origin?
#[verifier::external_body]
pub fn same_origin(a: &String, b: &String) -> (r: bool)
    ensures r == same_origin_spec(a@, b@),
{
    a.split(':').next() == b.split(':').next()
}

/// `str == str`, with its meaning stated.
#[verifier::external_body]
pub fn str_eq(a: &str, b: &str) -> (r: bool)
    ensures r == (a@ == b@),
{
    a == b
}

/// `parseNat` of the specification, saturating at `MAX_TIME`.
pub uninterp spec fn spec_parse_nat(s: Seq<char>) -> nat;

#[verifier::external_body]
pub fn parse_nat(s: &String) -> (r: u64)
    ensures
        r as nat == spec_parse_nat(s@),
        r <= MAX_TIME,
{
    let mut acc: u64 = 0;
    for c in s.chars() {
        let d = (c as u32).wrapping_sub('0' as u32) as u64;
        acc = acc.saturating_mul(10).saturating_add(d);
        if acc > MAX_TIME {
            return MAX_TIME;
        }
    }
    acc
}

} // verus!
