//! Local trusted helpers for executable process bookkeeping.

use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub fn copy<T: Clone>(value: &T) -> (result: T)
    ensures
        result == *value,
{
    value.clone()
}

} // verus!
