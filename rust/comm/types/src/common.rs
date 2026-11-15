//! Shared mathematical declarations and proofs, independent of either model.
use vstd::prelude::*;
use crate::{Tags, Value};

verus! {

pub uninterp spec fn spec_next_cron(cron: Seq<char>, after: u64) -> u64;

#[verifier::external_body]
pub proof fn axiom_next_cron_after(cron: Seq<char>, after: u64)
    ensures
        spec_next_cron(cron, after) > after,
{
}

pub uninterp spec fn spec_expand(template: Seq<char>, id: Seq<char>, at: u64) -> Seq<char>;

pub axiom fn axiom_string_ext(a: String, b: String)
    requires
        a@ == b@,
    ensures
        a == b,
;

pub axiom fn axiom_vec_ext<T>(a: Vec<T>, b: Vec<T>)
    requires
        a@ == b@,
    ensures
        a == b,
;

pub axiom fn axiom_string_realised(chars: Seq<char>)
    ensures
        exists|s: String| s@ == chars,
;

pub axiom fn axiom_bytes_realised(bytes: Seq<u8>)
    ensures
        exists|v: Vec<u8>| v@ == bytes,
;

pub proof fn lemma_tags_ext(a: Tags, b: Tags)
    requires
        a.deep_view() == b.deep_view(),
    ensures
        a == b,
{
    let av = a@;
    let bv = b@;
    assert(a.deep_view().len() == av.len());
    assert(b.deep_view().len() == bv.len());
    assert forall|i: int| 0 <= i < av.len() implies #[trigger] av[i] == bv[i] by {
        assert(a.deep_view()[i] == av[i].deep_view());
        assert(b.deep_view()[i] == bv[i].deep_view());
        axiom_string_ext(av[i].0, bv[i].0);
        axiom_string_ext(av[i].1, bv[i].1);
    };
    assert(av =~= bv);
    axiom_vec_ext(a, b);
}

pub proof fn lemma_value_ext(a: Value, b: Value)
    requires
        a@ == b@,
    ensures
        a == b,
{
    assert(a@.headers == a.headers.deep_view());
    assert(b@.headers == b.headers.deep_view());
    lemma_tags_ext(a.headers, b.headers);
    match (a.data, b.data) {
        (Some(x), Some(y)) => {
            assert(x@ == y@);
            axiom_string_ext(x, y);
        },
        (None, None) => {},
        _ => {
            assert(false);
        },
    }
}

}
