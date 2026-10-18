//! Tags: first match wins, and the three axes read off them.

use vstd::prelude::*;

use crate::ident::str_eq;
use crate::types::{ATags, Tags};

verus! {

/// `Tags.get?`: the value of the first pair whose key is `k`.
pub open spec fn tags_get(t: ATags, k: Seq<char>) -> Option<Seq<char>>
    decreases t.len(),
{
    if t.len() == 0 {
        None
    } else if t[0].0 == k {
        Some(t[0].1)
    } else {
        tags_get(t.drop_first(), k)
    }
}

pub open spec fn tags_has(t: ATags, k: Seq<char>) -> bool {
    tags_get(t, k) is Some
}

pub open spec fn is_timer(t: ATags) -> bool {
    tags_get(t, "resonate:timer"@) == Some("true"@)
}

#[derive(PartialEq, Eq, Structural, Clone, Copy)]
pub enum OType {
    Internal,
    External,
    Runnable,
}

impl OType {
    pub open spec fn awaitable(self) -> bool {
        self != OType::Internal
    }
}

/// `Tags.otype`.
pub open spec fn otype(t: ATags) -> OType {
    if tags_has(t, "resonate:target"@) {
        OType::Runnable
    } else if tags_get(t, "resonate:scope"@) == Some("global"@)
        || tags_get(t, "resonate:external"@) == Some("true"@) || is_timer(t) {
        OType::External
    } else {
        OType::Internal
    }
}

pub open spec fn timer_targeted(t: ATags) -> bool {
    is_timer(t) && tags_has(t, "resonate:target"@)
}

/// The target address, `""` if absent (`getD ""`).
pub open spec fn target_of(t: ATags) -> Seq<char> {
    match tags_get(t, "resonate:target"@) {
        Some(a) => a,
        None => Seq::empty(),
    }
}

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

// ---------------------------------------------------------------------------
// Executable reads
// ---------------------------------------------------------------------------

/// The index of the first pair whose key is `key`.
pub fn tag_find(tags: &Tags, key: &str) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < tags@.len() && tags_get(tags.deep_view(), key@) == Some(tags@[i as int].1@),
            None => tags_get(tags.deep_view(), key@) is None,
        },
{
    let ghost t = tags.deep_view();
    let mut i: usize = 0;
    while i < tags.len()
        invariant
            i <= tags@.len(),
            t == tags.deep_view(),
            forall|j: int| 0 <= j < i ==> t[j].0 != key@,
        decreases tags@.len() - i,
    {
        if str_eq(tags[i].0.as_str(), key) {
            proof {
                assert(t[i as int] == (tags@[i as int].0@, tags@[i as int].1@));
                lemma_tags_get_at(t, key@, i as int);
            }
            return Some(i);
        }
        proof {
            assert(t[i as int] == (tags@[i as int].0@, tags@[i as int].1@));
        }
        i += 1;
    }
    proof {
        lemma_tags_get_none(t, key@);
    }
    None
}

/// Is `key` present with value exactly `val`?
pub fn tag_is(tags: &Tags, key: &str, val: &str) -> (r: bool)
    ensures r == (tags_get(tags.deep_view(), key@) == Some(val@)),
{
    match tag_find(tags, key) {
        Some(i) => str_eq(tags[i].1.as_str(), val),
        None => false,
    }
}

pub fn tag_has(tags: &Tags, key: &str) -> (r: bool)
    ensures r == tags_has(tags.deep_view(), key@),
{
    tag_find(tags, key).is_some()
}

pub fn exec_is_timer(tags: &Tags) -> (r: bool)
    ensures r == is_timer(tags.deep_view()),
{
    tag_is(tags, "resonate:timer", "true")
}

pub fn exec_otype(tags: &Tags) -> (r: OType)
    ensures r == otype(tags.deep_view()),
{
    if tag_has(tags, "resonate:target") {
        OType::Runnable
    } else if tag_is(tags, "resonate:scope", "global") || tag_is(tags, "resonate:external", "true")
        || exec_is_timer(tags) {
        OType::External
    } else {
        OType::Internal
    }
}

pub fn exec_timer_targeted(tags: &Tags) -> (r: bool)
    ensures r == timer_targeted(tags.deep_view()),
{
    exec_is_timer(tags) && tag_has(tags, "resonate:target")
}

/// The target address, cloned; `""` if absent.
pub fn exec_target_of(tags: &Tags) -> (r: String)
    ensures r@ == target_of(tags.deep_view()),
{
    match tag_find(tags, "resonate:target") {
        Some(i) => tags[i].1.clone(),
        None => String::new(),
    }
}

} // verus!
