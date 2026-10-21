//! Tags: first match wins, and the three axes read off them.

use vstd::prelude::*;
use vstd::string::StringExecFns;

use crate::tags_proof::*;

use crate::types::str_eq;
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

    pub fn is_awaitable(self) -> (r: bool)
        ensures r == self.awaitable(),
    {
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
// Stamping: the tags a schedule's occurrence is born with
// ---------------------------------------------------------------------------

/// The keys a schedule's template does not carry onto the promise it fires:
/// the schedule's own, and the lineage, which the firing sets.
pub open spec fn stamped_key(k: Seq<char>) -> bool {
    ||| k == "resonate:schedule"@
    ||| k == "resonate:origin"@
    ||| k == "resonate:branch"@
    ||| k == "resonate:parent"@
    ||| k == "resonate:prefix"@
}

/// The template without the stamped keys, in order.
pub open spec fn strip(t: ATags) -> ATags
    decreases t.len(),
{
    if t.len() == 0 {
        Seq::empty()
    } else if stamped_key(t[0].0) {
        strip(t.drop_first())
    } else {
        seq![t[0]] + strip(t.drop_first())
    }
}

/// What the firing sets: the schedule, and the lineage, which is the
/// promise itself.
pub open spec fn lineage(sid: Seq<char>, pid: Seq<char>) -> ATags {
    seq![("resonate:schedule"@, sid), ("resonate:origin"@, pid), ("resonate:branch"@, pid), ("resonate:parent"@, pid), ("resonate:prefix"@, pid)]
}

/// The tags of the promise schedule `sid` fires at `pid`: the template
/// stripped, then the stamp.
pub open spec fn spec_stamp(t: ATags, sid: Seq<char>, pid: Seq<char>) -> ATags {
    strip(t) + lineage(sid, pid)
}

pub fn is_stamped_key(k: &str) -> (r: bool)
    ensures r == stamped_key(k@),
{
    str_eq(k, "resonate:schedule") || str_eq(k, "resonate:origin") || str_eq(k, "resonate:branch") || str_eq(k, "resonate:parent") || str_eq(k, "resonate:prefix")
}

pub fn stamp_tags(t: &Tags, sid: &str, pid: &str) -> (r: Tags)
    ensures r.deep_view() == spec_stamp(t.deep_view(), sid@, pid@),
{
    let ghost s = t.deep_view();
    let mut r: Tags = Vec::new();
    let mut i: usize = 0;
    assert(r.deep_view() =~= strip(s.take(0)));
    while i < t.len()
        invariant
            i <= t@.len(),
            s == t.deep_view(),
            r.deep_view() == strip(s.take(i as int)),
        decreases t@.len() - i,
    {
        let ghost before = r.deep_view();
        let keep = !is_stamped_key(t[i].0.as_str());
        if keep {
            r.push((crate::types::clone_string(&t[i].0), crate::types::clone_string(&t[i].1)));
        }
        proof {
            assert(s[i as int] == (t@[i as int].0@, t@[i as int].1@));
            assert(s.take(i as int + 1) =~= s.take(i as int).push(s[i as int]));
            lemma_strip_push(s.take(i as int), s[i as int]);
            if keep {
                assert(r.deep_view() =~= before.push(s[i as int]));
            }
        }
        i += 1;
    }
    assert(s.take(s.len() as int) =~= s);
    let ghost stripped = r.deep_view();
    r.push((String::from_str("resonate:schedule"), String::from_str(sid)));
    r.push((String::from_str("resonate:origin"), String::from_str(pid)));
    r.push((String::from_str("resonate:branch"), String::from_str(pid)));
    r.push((String::from_str("resonate:parent"), String::from_str(pid)));
    r.push((String::from_str("resonate:prefix"), String::from_str(pid)));
    assert(r.deep_view() =~= stripped + lineage(sid@, pid@));
    r
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
