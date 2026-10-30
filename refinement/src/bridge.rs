//! The two vocabularies agree.
//!
//! The kernel reads tags, ids and delays with its own spec functions
//! (`tags_get`, `is_timer`, `otype`, `origin`, `spec_parse_nat`); the
//! Abstract model has independent ones over its own types (`spec_tag_value`,
//! `spec_is_timer`, `spec_otype`, `AIdent`, `spec_parse_nat_bounded`). Each
//! lemma here says that, under the mapping in `lib.rs`, the two compute the
//! same thing. Nothing here is assumed: both sides are definitions.

use vstd::prelude::*;

use echod_abstract::state as abs_state;
use echod_abstract::types as abs;
use echod_kernel::object as kobject;
use echod_kernel::tags as ktags;
use echod_kernel::types as kernel;

use crate::*;

verus! {

// ---------------------------------------------------------------------------
// The list maps are index-wise
// ---------------------------------------------------------------------------

pub proof fn lemma_tags_index(xs: Seq<(Chars, Chars)>)
    ensures
        tags(xs).len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] tags(xs)[i] == tag(xs[i]),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_tags_index(xs.drop_last());
        assert forall|i: int| 0 <= i < xs.len() implies #[trigger] tags(xs)[i] == tag(xs[i]) by {
            if i < xs.len() - 1 {
                assert(tags(xs)[i] == tags(xs.drop_last())[i]);
                assert(xs.drop_last()[i] == xs[i]);
            }
        }
    }
}

pub proof fn lemma_id_list_index(xs: Seq<Chars>)
    ensures
        id_list(xs).len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] id_list(xs)[i] == ident(xs[i]),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_id_list_index(xs.drop_last());
        assert forall|i: int| 0 <= i < xs.len() implies #[trigger] id_list(xs)[i] == ident(xs[i]) by {
            if i < xs.len() - 1 {
                assert(id_list(xs)[i] == id_list(xs.drop_last())[i]);
                assert(xs.drop_last()[i] == xs[i]);
            }
        }
    }
}

pub proof fn lemma_text_list_index(xs: Seq<Chars>)
    ensures
        text_list(xs).len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] text_list(xs)[i] == text(xs[i]),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_text_list_index(xs.drop_last());
        assert forall|i: int| 0 <= i < xs.len() implies #[trigger] text_list(xs)[i] == text(xs[i]) by {
            if i < xs.len() - 1 {
                assert(text_list(xs)[i] == text_list(xs.drop_last())[i]);
                assert(xs.drop_last()[i] == xs[i]);
            }
        }
    }
}

pub proof fn lemma_id_list_push(xs: Seq<Chars>, x: Chars)
    ensures id_list(xs.push(x)) == id_list(xs).push(ident(x)),
{
    assert(xs.push(x).drop_last() =~= xs);
    assert(xs.push(x).last() == x);
}

pub proof fn lemma_text_list_push(xs: Seq<Chars>, x: Chars)
    ensures text_list(xs.push(x)) == text_list(xs).push(text(x)),
{
    assert(xs.push(x).drop_last() =~= xs);
    assert(xs.push(x).last() == x);
}

pub proof fn lemma_id_list_contains(xs: Seq<Chars>, x: Chars)
    requires
        canonical(x),
        forall|i: int| 0 <= i < xs.len() ==> canonical(#[trigger] xs[i]),
    ensures id_list(xs).contains(ident(x)) == xs.contains(x),
{
    lemma_id_list_index(xs);
    if xs.contains(x) {
        let i = choose|i: int| 0 <= i < xs.len() && xs[i] == x;
        assert(id_list(xs)[i] == ident(x));
    }
    if id_list(xs).contains(ident(x)) {
        let i = choose|i: int| 0 <= i < id_list(xs).len() && id_list(xs)[i] == ident(x);
        lemma_ident_injective(xs[i], x);
        assert(xs[i] == x);
    }
}

pub proof fn lemma_text_list_contains(xs: Seq<Chars>, x: Chars)
    ensures text_list(xs).contains(text(x)) == xs.contains(x),
{
    lemma_text_list_index(xs);
    if xs.contains(x) {
        let i = choose|i: int| 0 <= i < xs.len() && xs[i] == x;
        assert(text_list(xs)[i] == text(x));
    }
    if text_list(xs).contains(text(x)) {
        let i = choose|i: int| 0 <= i < text_list(xs).len() && text_list(xs)[i] == text(x);
        assert(text(xs[i]) == text(x));
        assert(xs[i] == x);
    }
}

// ---------------------------------------------------------------------------
// Identifiers
// ---------------------------------------------------------------------------

/// The id carries a `:`.
pub open spec fn has_colon(id: Chars) -> bool
    decreases id.len(),
{
    if id.len() == 0 {
        false
    } else if id[0] == ':' {
        true
    } else {
        has_colon(id.drop_first())
    }
}

/// An id the Abstract `AIdent` can spell back: not `origin:` with nothing
/// after the colon, which `AIdent` cannot tell from `origin` alone. The
/// protocol's ids are of this shape; this is the one door on ids.
pub open spec fn canonical(id: Chars) -> bool {
    !(has_colon(id) && suffix(id).len() == 0)
}

/// An id is its origin, then, if it has a colon, the colon and its suffix.
pub proof fn lemma_split_id(id: Chars)
    ensures
        has_colon(id) ==> id == kernel::origin(id) + seq![':'] + suffix(id),
        !has_colon(id) ==> id == kernel::origin(id) && suffix(id) == Seq::<char>::empty(),
    decreases id.len(),
{
    if id.len() == 0 {
        assert(id =~= kernel::origin(id));
    } else if id[0] == ':' {
        assert(id =~= kernel::origin(id) + seq![':'] + suffix(id));
    } else {
        let rest = id.drop_first();
        lemma_split_id(rest);
        assert(kernel::origin(id) == seq![id[0]] + kernel::origin(rest));
        assert(suffix(id) == suffix(rest));
        assert(id =~= seq![id[0]] + rest);
        if has_colon(id) {
            assert(has_colon(rest));
            assert(rest == kernel::origin(rest) + seq![':'] + suffix(rest));
            assert(seq![id[0]] + (kernel::origin(rest) + seq![':'] + suffix(rest))
                =~= (seq![id[0]] + kernel::origin(rest)) + seq![':'] + suffix(rest));
            assert(id =~= kernel::origin(id) + seq![':'] + suffix(id));
        } else {
            assert(id =~= kernel::origin(id));
        }
    }
}

pub proof fn lemma_ident_injective(x: Chars, y: Chars)
    requires canonical(x), canonical(y), ident(x) == ident(y),
    ensures x == y,
{
    lemma_split_id(x);
    lemma_split_id(y);
    assert(kernel::origin(x) == kernel::origin(y));
    assert(suffix(x) == suffix(y));
    if has_colon(x) && has_colon(y) {
        assert(x == y);
    } else if !has_colon(x) && !has_colon(y) {
        assert(x == y);
    } else if has_colon(x) {
        assert(suffix(y) == Seq::<char>::empty());
        assert(suffix(x).len() == 0);
        assert(false);
    } else {
        assert(suffix(x) == Seq::<char>::empty());
        assert(suffix(y).len() == 0);
        assert(false);
    }
}

pub proof fn lemma_same_origin(x: Chars, y: Chars)
    ensures kernel::same_origin_spec(x, y) == (ident(x).origin == ident(y).origin),
{
}

// ---------------------------------------------------------------------------
// Tags
// ---------------------------------------------------------------------------

/// The key the Abstract model's numbered tag lookups name.
pub open spec fn which_key(which: u8) -> Chars {
    match which {
        0 => "resonate:target"@,
        1 => "resonate:scope"@,
        2 => "resonate:external"@,
        3 => "resonate:timer"@,
        _ => "resonate:delay"@,
    }
}

pub open spec fn opt_text(x: Option<Chars>) -> Option<abs::AText> {
    match x {
        Some(v) => Some(text(v)),
        None => None,
    }
}

pub proof fn lemma_tag_key(k: Chars, which: u8)
    ensures abs::spec_tag_key(k, which) == (k == which_key(which)),
{
    reveal_strlit("resonate:target");
    reveal_strlit("resonate:scope");
    reveal_strlit("resonate:external");
    reveal_strlit("resonate:timer");
    reveal_strlit("resonate:delay");
    match which {
        0 => {
            assert("resonate:target"@ =~= seq!['r','e','s','o','n','a','t','e',':','t','a','r','g','e','t']);
        }
        1 => {
            assert("resonate:scope"@ =~= seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e']);
        }
        2 => {
            assert("resonate:external"@ =~= seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l']);
        }
        3 => {
            assert("resonate:timer"@ =~= seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r']);
        }
        _ => {
            assert("resonate:delay"@ =~= seq!['r','e','s','o','n','a','t','e',':','d','e','l','a','y']);
        }
    }
}

pub proof fn lemma_ascii_true(v: Chars)
    ensures abs::spec_ascii_true(text(v)) == (v == "true"@),
{
    reveal_strlit("true");
    assert("true"@ =~= seq!['t','r','u','e']);
}

pub proof fn lemma_ascii_global(v: Chars)
    ensures abs::spec_ascii_global(text(v)) == (v == "global"@),
{
    reveal_strlit("global");
    assert("global"@ =~= seq!['g','l','o','b','a','l']);
}

proof fn lemma_tag_value_at(xs: Seq<(Chars, Chars)>, which: u8, start: nat)
    requires start <= xs.len(),
    ensures
        abs::spec_tag_value_at(tags(xs), which, start)
            == opt_text(ktags::tags_get(xs.skip(start as int), which_key(which))),
    decreases xs.len() - start,
{
    lemma_tags_index(xs);
    let rest = xs.skip(start as int);
    if start >= xs.len() {
        assert(rest =~= Seq::<(Chars, Chars)>::empty());
    } else {
        assert(rest.len() > 0);
        assert(rest[0] == xs[start as int]);
        assert(rest.drop_first() =~= xs.skip(start as int + 1));
        lemma_tag_key(xs[start as int].0, which);
        assert(tags(xs)[start as int] == tag(xs[start as int]));
        if xs[start as int].0 == which_key(which) {
        } else {
            lemma_tag_value_at(xs, which, start + 1);
        }
    }
}

pub proof fn lemma_tag_value(xs: Seq<(Chars, Chars)>, which: u8)
    ensures
        abs::spec_tag_value(tags(xs), which)
            == opt_text(ktags::tags_get(xs, which_key(which))),
{
    lemma_tag_value_at(xs, which, 0);
    assert(xs.skip(0) =~= xs);
}

pub proof fn lemma_is_timer(xs: Seq<(Chars, Chars)>)
    ensures abs::spec_is_timer(tags(xs)) == ktags::is_timer(xs),
{
    lemma_tag_value(xs, 3);
    match ktags::tags_get(xs, "resonate:timer"@) {
        Some(v) => { lemma_ascii_true(v); }
        None => {}
    }
}

pub proof fn lemma_has_target(xs: Seq<(Chars, Chars)>)
    ensures abs::spec_has_target(tags(xs)) == ktags::tags_has(xs, "resonate:target"@),
{
    lemma_tag_value(xs, 0);
}

pub open spec fn otype(o: ktags::OType) -> abs::OType {
    match o {
        ktags::OType::Internal => abs::OType::Internal,
        ktags::OType::External => abs::OType::External,
        ktags::OType::Runnable => abs::OType::Runnable,
    }
}

pub proof fn lemma_otype(xs: Seq<(Chars, Chars)>)
    ensures abs::spec_otype(tags(xs)) == otype(ktags::otype(xs)),
{
    lemma_has_target(xs);
    lemma_is_timer(xs);
    lemma_tag_value(xs, 1);
    lemma_tag_value(xs, 2);
    match ktags::tags_get(xs, "resonate:scope"@) {
        Some(v) => { lemma_ascii_global(v); }
        None => {}
    }
    match ktags::tags_get(xs, "resonate:external"@) {
        Some(v) => { lemma_ascii_true(v); }
        None => {}
    }
}

pub proof fn lemma_timer_targeted(xs: Seq<(Chars, Chars)>)
    ensures
        (abs::spec_is_timer(tags(xs)) && abs::spec_has_target(tags(xs)))
            == ktags::timer_targeted(xs),
{
    lemma_is_timer(xs);
    lemma_has_target(xs);
}

/// A create whose tags are not a targeted timer is left alone by the
/// Abstract normalization.
pub proof fn lemma_strip_identity(xs: Seq<(Chars, Chars)>)
    requires !ktags::timer_targeted(xs),
    ensures abs::spec_strip_timer_target(tags(xs)) == tags(xs),
{
    lemma_is_timer(xs);
    lemma_has_target(xs);
    if abs::spec_is_timer(tags(xs)) {
        lemma_without_target_identity(tags(xs));
    }
}

proof fn lemma_without_target_identity(t: abs::ATags)
    requires !abs::spec_has_target(t),
    ensures abs::spec_without_target(t) == t,
    decreases t.len(),
{
    if t.len() > 0 {
        assert(abs::spec_tag_value_at(t, 0, 0) is None);
        assert(!abs::spec_tag_key(t[0].key.chars, 0));
        assert(abs::spec_tag_value_at(t, 0, 1) is None);
        assert forall|k: nat| k <= t.drop_first().len()
            implies #[trigger] abs::spec_tag_value_at(t.drop_first(), 0, k)
                == abs::spec_tag_value_at(t, 0, k + 1) by {
            lemma_tag_value_at_shift(t, k);
        }
        assert(!abs::spec_has_target(t.drop_first()));
        lemma_without_target_identity(t.drop_first());
        assert(seq![t[0]] + t.drop_first() =~= t);
    }
}

proof fn lemma_tag_value_at_shift(t: abs::ATags, k: nat)
    requires t.len() > 0, k <= t.drop_first().len(),
    ensures abs::spec_tag_value_at(t.drop_first(), 0, k) == abs::spec_tag_value_at(t, 0, k + 1),
    decreases t.len() - k,
{
    if k < t.drop_first().len() {
        assert(t.drop_first()[k as int] == t[k as int + 1]);
        if !abs::spec_tag_key(t[k as int + 1].key.chars, 0) {
            lemma_tag_value_at_shift(t, k + 1);
        }
    }
}

// ---------------------------------------------------------------------------
// Delays
// ---------------------------------------------------------------------------

proof fn lemma_parse_at(s: Chars, start: nat, acc: u64)
    requires acc <= kernel::MAX_TIME,
    ensures
        kernel::spec_parse_nat_at(s, start, acc as nat)
            == abs::spec_parse_nat_at(s, start, acc) as nat,
    decreases s.len() - start,
{
    if start < s.len() {
        if acc <= kernel::MAX_TIME / 10 {
            let ten = acc * 10;
            let d = abs::spec_digit(s[start as int]);
            assert(kernel::spec_digit(s[start as int]) == d as nat);
            if d <= kernel::MAX_TIME - ten {
                lemma_parse_at(s, start + 1, (ten + d) as u64);
            }
        }
    }
}

pub proof fn lemma_parse_nat(s: Chars)
    ensures kernel::spec_parse_nat(s) == abs::spec_parse_nat_bounded(text(s)) as nat,
{
    lemma_parse_at(s, 0, 0);
}

/// `first_dispatch` and the Abstract task's due instant agree.
pub proof fn lemma_first_dispatch(xs: Seq<(Chars, Chars)>, now: u64)
    ensures
        kobject::first_dispatch(xs, now as nat)
            == (match abs::spec_tag_value(tags(xs), 4) {
                Some(d) => {
                    let parsed = abs::spec_parse_nat_bounded(d);
                    if parsed > now { parsed } else { now }
                }
                None => now,
            }) as nat,
{
    lemma_tag_value(xs, 4);
    match ktags::tags_get(xs, "resonate:delay"@) {
        Some(d) => { lemma_parse_nat(d); }
        None => {}
    }
}

// ---------------------------------------------------------------------------
// Removal from lists
// ---------------------------------------------------------------------------

pub proof fn lemma_without_ident(s: Seq<Chars>, x: Chars)
    requires
        canonical(x),
        forall|i: int| 0 <= i < s.len() ==> canonical(#[trigger] s[i]),
    ensures
        abs_state::spec_without_ident(id_list(s), ident(x)) == id_list(kobject::without(s, x)),
    decreases s.len(),
{
    if s.len() > 0 {
        assert(id_list(s).drop_last() =~= id_list(s.drop_last()));
        assert(id_list(s).last() == ident(s.last()));
        assert forall|i: int| 0 <= i < s.drop_last().len() implies canonical(#[trigger] s.drop_last()[i]) by {
            assert(s.drop_last()[i] == s[i]);
        }
        lemma_without_ident(s.drop_last(), x);
        if s.last() == x {
        } else {
            if ident(s.last()) == ident(x) {
                lemma_ident_injective(s.last(), x);
                assert(false);
            }
            lemma_id_list_push(kobject::without(s.drop_last(), x), s.last());
        }
    } else {
        assert(id_list(s) =~= Seq::<abs::AIdent>::empty());
    }
}

pub proof fn lemma_without_text(s: Seq<Chars>, x: Chars)
    ensures
        abs_state::spec_without_text(text_list(s), text(x)) == text_list(kobject::without(s, x)),
    decreases s.len(),
{
    if s.len() > 0 {
        assert(text_list(s).drop_last() =~= text_list(s.drop_last()));
        assert(text_list(s).last() == text(s.last()));
        lemma_without_text(s.drop_last(), x);
        if s.last() == x {
        } else {
            assert(text(s.last()) != text(x));
            lemma_text_list_push(kobject::without(s.drop_last(), x), s.last());
        }
    } else {
        assert(text_list(s) =~= Seq::<abs::AText>::empty());
    }
}

} // verus!
