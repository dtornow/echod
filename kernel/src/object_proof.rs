//! The proofs of the object edits: the two lemmas on `without`, the
//! sequence with one element removed. Nothing here is executed.

use vstd::prelude::*;

use crate::object::*;
use crate::tags::OType;
use crate::types::*;
use crate::types::MAX_TIME;

verus! {

/// What `without` keeps: everything but `x`.
pub proof fn lemma_without_contains(s: Seq<Seq<char>>, x: Seq<char>, y: Seq<char>)
    ensures
        without(s, x).contains(y) <==> (s.contains(y) && y != x),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let init = s.drop_last();
        lemma_without_contains(init, x, y);
        assert(s.contains(y) <==> (init.contains(y) || s.last() == y)) by {
            if s.contains(y) {
                let i = choose|i: int| 0 <= i < s.len() && s[i] == y;
                if i < s.len() - 1 {
                    assert(init[i] == y);
                }
            }
            if init.contains(y) {
                let i = choose|i: int| 0 <= i < init.len() && init[i] == y;
                assert(s[i] == y);
            }
            if s.last() == y {
                assert(s[s.len() - 1] == y);
            }
        }
        if s.last() != x {
            let w = without(init, x);
            assert(w.push(s.last()).contains(y) <==> (w.contains(y) || s.last() == y)) by {
                if w.push(s.last()).contains(y) {
                    let i = choose|i: int| 0 <= i < w.push(s.last()).len() && w.push(s.last())[i] == y;
                    if i < w.len() {
                        assert(w[i] == y);
                    }
                }
                if w.contains(y) {
                    let i = choose|i: int| 0 <= i < w.len() && w[i] == y;
                    assert(w.push(s.last())[i] == y);
                }
                if s.last() == y {
                    assert(w.push(s.last())[w.len() as int] == y);
                }
            }
        }
    }
}

/// `without` keeps a duplicate-free sequence duplicate-free.
pub proof fn lemma_without_no_dups(s: Seq<Seq<char>>, x: Seq<char>)
    requires
        crate::properties::no_dups(s),
    ensures
        crate::properties::no_dups(without(s, x)),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let init = s.drop_last();
        assert(crate::properties::no_dups(init)) by {
            assert forall|i: int, j: int| 0 <= i < init.len() && 0 <= j < init.len() && init[i] == init[j]
                implies i == j by {
                assert(s[i] == init[i]);
                assert(s[j] == init[j]);
            }
        }
        lemma_without_no_dups(init, x);
        if s.last() != x {
            let w = without(init, x);
            assert(!w.contains(s.last())) by {
                lemma_without_contains(init, x, s.last());
                if init.contains(s.last()) {
                    let i = choose|i: int| 0 <= i < init.len() && init[i] == s.last();
                    assert(s[i] == s[s.len() - 1]);
                }
            }
            assert forall|i: int, j: int| 0 <= i < w.push(s.last()).len() && 0 <= j < w.push(s.last()).len()
                && w.push(s.last())[i] == w.push(s.last())[j] implies i == j by {
                if i < w.len() && j < w.len() {
                } else if i < w.len() {
                    assert(w[i] == s.last());
                } else if j < w.len() {
                    assert(w[j] == s.last());
                }
            }
        }
    }
}

} // verus!
