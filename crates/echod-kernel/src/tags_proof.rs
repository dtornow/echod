//! The proofs of tags: what `get` returns at a match and at none. Nothing
//! here is executed.

use vstd::prelude::*;

use crate::types::str_eq;
use crate::tags::*;
use crate::types::{ATags, Tags};

verus! {

// ---------------------------------------------------------------------------
// The recursive definition, as an index
// ---------------------------------------------------------------------------

/// If `i` is the first index whose key is `k`, `tags_get` returns its value.
pub proof fn lemma_tags_get_at(t: ATags, k: Seq<char>, i: int)
    requires
        0 <= i < t.len(),
        t[i].0 == k,
        forall|j: int| 0 <= j < i ==> t[j].0 != k,
    ensures
        tags_get(t, k) == Some(t[i].1),
    decreases i,
{
    if i == 0 {
    } else {
        assert(t[0].0 != k);
        let r = t.drop_first();
        assert(r[i - 1] == t[i]);
        assert forall|j: int| 0 <= j < i - 1 implies r[j].0 != k by {
            assert(r[j] == t[j + 1]);
        }
        lemma_tags_get_at(r, k, i - 1);
    }
}

/// If no key is `k`, `tags_get` returns `None`.
pub proof fn lemma_tags_get_none(t: ATags, k: Seq<char>)
    requires
        forall|j: int| 0 <= j < t.len() ==> t[j].0 != k,
    ensures
        tags_get(t, k) is None,
    decreases t.len(),
{
    if t.len() == 0 {
    } else {
        let r = t.drop_first();
        assert forall|j: int| 0 <= j < r.len() implies r[j].0 != k by {
            assert(r[j] == t[j + 1]);
        }
        lemma_tags_get_none(r, k);
    }
}

} // verus!
