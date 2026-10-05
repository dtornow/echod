//! What the replay trusts beyond vstd: that a derived `Clone` copies and a
//! derived `PartialEq` compares, for a model's own types. Both `external_body`:
//! Verus takes the `ensures` on trust and checks every use against them. Keep
//! it to these two; everything else in `certificate.rs` is verified.

use vstd::prelude::*;

verus! {

/// A `Clone` is a copy.
#[verifier::external_body]
pub(crate) fn copy<T: Clone>(t: &T) -> (r: T)
    ensures
        r == *t,
{
    t.clone()
}

/// A `PartialEq` is equality.
#[verifier::external_body]
pub(crate) fn same<T: PartialEq>(a: &T, b: &T) -> (r: bool)
    ensures
        r == (*a == *b),
{
    a == b
}

} // verus!
