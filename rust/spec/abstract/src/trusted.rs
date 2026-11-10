//! Explicit mathematical declarations and axioms trusted by the specification.
//! Runtime realizations live with their callers, outside this crate.

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
pub use echod_types::origin;

verus! {
/// Any absolute URL, as the spec sees it: what `address_valid` decides.
pub uninterp spec fn spec_address_valid(addr: Seq<char>) -> bool;

pub open spec fn spec_has_colon(id: Seq<char>) -> bool {
    exists|i: int| 0 <= i < id.len() && id[i] == ':'
}

/// A cron the engine accepts, as the spec sees it.
pub uninterp spec fn spec_cron_valid(cron: Seq<char>) -> bool;

/// Lean's `nextCron`, as the spec sees it: strictly after `after`.
pub uninterp spec fn spec_next_cron(cron: Seq<char>, after: u64) -> u64;

#[verifier::external_body]
pub proof fn axiom_next_cron_after(cron: Seq<char>, after: u64)
    ensures
        spec_next_cron(cron, after) > after,
{
}

/// Lean's `expand`, as the spec sees it.
pub uninterp spec fn spec_expand(template: Seq<char>, id: Seq<char>, at: u64) -> Seq<char>;

// ------------------------------------------------------------------- axioms

/// A set's elements, in the set's order, each once. Which order is the
/// `BTreeSet`'s; the spec only ever uses that there is one.
pub uninterp spec fn pset_seq(s: Set<Seq<char>>) -> Seq<Seq<char>>;

pub broadcast axiom fn axiom_pset_seq(s: Set<Seq<char>>)
    ensures
        (#[trigger] pset_seq(s)).to_set() == s,
        pset_seq(s).no_duplicates(),
        pset_seq(s).len() == s.len(),
;

/// A string is its characters.
pub axiom fn axiom_string_ext(a: String, b: String)
    requires
        a@ == b@,
    ensures
        a == b,
;

/// A promise record is its fields.
pub axiom fn axiom_record_ext(a: echod_types::PromiseRecord, b: echod_types::PromiseRecord)
    requires
        a@ == b@,
    ensures
        a == b,
;

/// A vector is its elements.
pub axiom fn axiom_vec_ext<T>(a: Vec<T>, b: Vec<T>)
    requires
        a@ == b@,
    ensures
        a == b,
;

/// Any characters are some string's characters.
pub axiom fn axiom_string_realised(chars: Seq<char>)
    ensures
        exists|s: String| s@ == chars,
;

/// Any bytes are some vector's bytes.
pub axiom fn axiom_bytes_realised(bytes: Seq<u8>)
    ensures
        exists|v: Vec<u8>| v@ == bytes,
;


} // verus!
