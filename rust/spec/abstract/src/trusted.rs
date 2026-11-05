//! What the spec trusts: persistent maps and sets as Verus maps and sets, a copy
//! that is a copy, string helpers, and the reference server's cron engine.
//! Everything here is `external_body` or an axiom:
//! Verus takes the `ensures` on trust and checks every use against them. Keep
//! it small; everything else in the crate is verified.
//!
//! The axioms at the end say two things of the types as built. A value is
//! its view: two strings, vectors, maps or sets with the same view are the
//! same value, which is what their `PartialEq` decides and what the checker
//! compares. And a set's elements come out in one order (`pset_seq`): the
//! `BTreeSet`'s, which the spec never looks into.

use std::collections::BTreeSet;

use echod_rover::HashedMap;
use vstd::prelude::*;

pub use echod_types::same_origin;
#[cfg(verus_keep_ghost)]
pub use echod_types::origin;

verus! {

/// A persistent map from ids to `V`: `echod_rover::HashedMap`, seen by Verus as a
/// `Map` from the ids' characters.
#[verifier::external_body]
#[verifier::reject_recursive_types(V)]
pub struct PMap<V> {
    pub(crate) inner: HashedMap<String, V>,
}

impl<V> View for PMap<V> {
    type V = Map<Seq<char>, V>;

    uninterp spec fn view(&self) -> Map<Seq<char>, V>;
}

impl<V: Clone + std::hash::Hash> PMap<V> {
    #[verifier::external_body]
    pub fn empty() -> (m: Self)
        ensures
            m@ == Map::<Seq<char>, V>::empty(),
    {
        PMap { inner: HashedMap::new() }
    }

    #[verifier::external_body]
    pub fn get(&self, k: &String) -> (r: Option<&V>)
        ensures
            r == if self@.contains_key(k@) {
                Some(&self@[k@])
            } else {
                None::<&V>
            },
    {
        self.inner.get(k.as_str())
    }

    #[verifier::external_body]
    pub fn contains_key(&self, k: &String) -> (r: bool)
        ensures
            r == self@.contains_key(k@),
    {
        self.inner.contains_key(k.as_str())
    }

    #[verifier::external_body]
    pub fn insert(&mut self, k: String, v: V)
        ensures
            final(self)@ == old(self)@.insert(k@, v),
    {
        self.inner.insert(k, v);
    }

    #[verifier::external_body]
    pub fn remove(&mut self, k: &String)
        ensures
            final(self)@ == old(self)@.remove(k@),
    {
        self.inner.remove(k.as_str());
    }

    /// A copy, in constant time: the map is persistent.
    #[verifier::external_body]
    pub fn copy(&self) -> (r: Self)
        ensures
            r@ == self@,
    {
        PMap { inner: self.inner.clone() }
    }

    /// Every key, in order, each once.
    #[verifier::external_body]
    pub fn keys(&self) -> (r: Vec<String>)
        ensures
            forall|i: int| 0 <= i < r.len() ==> #[trigger] self@.contains_key(r[i]@),
            forall|k: Seq<char>| #[trigger] self@.contains_key(k) ==> exists|i: int| 0 <= i < r.len() && #[trigger] r[i]@ == k,
    {
        let mut keys: Vec<String> = self.inner.iter().map(|(k, _)| k.clone()).collect();
        keys.sort();
        keys
    }
}

/// A set of ids: a `BTreeSet`, seen by Verus as a `Set` of the ids' characters.
#[verifier::external_body]
pub struct PSet {
    pub(crate) inner: BTreeSet<String>,
}

impl View for PSet {
    type V = Set<Seq<char>>;

    uninterp spec fn view(&self) -> Set<Seq<char>>;
}

impl PSet {
    #[verifier::external_body]
    pub fn empty() -> (s: Self)
        ensures
            s@ == Set::<Seq<char>>::empty(),
    {
        PSet { inner: BTreeSet::new() }
    }

    #[verifier::external_body]
    pub fn contains(&self, k: &String) -> (r: bool)
        ensures
            r == self@.contains(k@),
    {
        self.inner.contains(k.as_str())
    }

    #[verifier::external_body]
    pub fn insert(&mut self, k: String)
        ensures
            final(self)@ == old(self)@.insert(k@),
    {
        self.inner.insert(k);
    }

    #[verifier::external_body]
    pub fn remove(&mut self, k: &String)
        ensures
            final(self)@ == old(self)@.remove(k@),
    {
        self.inner.remove(k.as_str());
    }

    /// Every element, in order, each once: `pset_seq` of the set.
    #[verifier::external_body]
    pub fn to_vec(&self) -> (r: Vec<String>)
        ensures
            r@.map_values(|s: String| s@) == pset_seq(self@),
    {
        self.inner.iter().cloned().collect()
    }
}

/// A derived `Clone` is a copy.
#[verifier::external_body]
pub fn copy<T: Clone>(t: &T) -> (r: T)
    ensures
        r == *t,
{
    t.clone()
}

/// Any absolute URL, as the spec sees it: what `address_valid` decides.
pub uninterp spec fn spec_address_valid(addr: Seq<char>) -> bool;

/// Any absolute URL: a scheme, a colon, and a non-empty rest with no whitespace.
#[verifier::external_body]
pub fn address_valid(addr: &String) -> (r: bool)
    ensures
        r == spec_address_valid(addr@),
{
    super::footprint::address_valid(addr)
}

/// Whether an id holds a `:`: the reference server keeps it as the separator
/// between an origin and the rest, so a schedule's id may not have one.
#[verifier::external_body]
pub fn has_colon(id: &String) -> (r: bool)
    ensures
        r == spec_has_colon(id@),
{
    id.contains(':')
}

pub open spec fn spec_has_colon(id: Seq<char>) -> bool {
    exists|i: int| 0 <= i < id.len() && id[i] == ':'
}

/// A cron the engine accepts, as the spec sees it.
pub uninterp spec fn spec_cron_valid(cron: Seq<char>) -> bool;

/// A cron expression the reference server's engine accepts: five fields, or
/// six to seven with seconds (and a year).
#[verifier::external_body]
pub fn cron_valid(cron: &String) -> (r: bool)
    ensures
        r == spec_cron_valid(cron@),
{
    super::footprint::cron_valid(cron)
}

/// Lean's `nextCron`, as the spec sees it: strictly after `after`.
pub uninterp spec fn spec_next_cron(cron: Seq<char>, after: u64) -> u64;

#[verifier::external_body]
pub proof fn axiom_next_cron_after(cron: Seq<char>, after: u64)
    ensures
        spec_next_cron(cron, after) > after,
{
}

/// Lean's `nextCron`: the first instant strictly after `after` the cron names,
/// as the reference server computes it (whole seconds, in milliseconds).
#[verifier::external_body]
pub fn next_cron(cron: &String, after: u64) -> (r: u64)
    ensures
        r == spec_next_cron(cron@, after),
        r > after,
{
    super::footprint::next_cron(cron, after)
}

/// Lean's `expand`, as the spec sees it.
pub uninterp spec fn spec_expand(template: Seq<char>, id: Seq<char>, at: u64) -> Seq<char>;

/// Lean's `expand`: the schedule's promise id template with `{{.id}}` the
/// schedule's id and `{{.timestamp}}` the occurrence's instant.
#[verifier::external_body]
pub fn expand(template: &String, id: &String, at: u64) -> (r: String)
    ensures
        r@ == spec_expand(template@, id@, at),
{
    super::footprint::expand(template, id, at)
}

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

/// A map is its entries.
pub axiom fn axiom_pmap_ext<V>(a: PMap<V>, b: PMap<V>)
    requires
        a@ == b@,
    ensures
        a == b,
;

/// A set is its elements.
pub axiom fn axiom_pset_ext(a: PSet, b: PSet)
    requires
        a@ == b@,
    ensures
        a == b,
;

} // verus!

// The traits the checker needs, outside Verus.

impl<V: Clone + std::hash::Hash> Clone for PMap<V> {
    fn clone(&self) -> Self {
        PMap { inner: self.inner.clone() }
    }
}

impl<V: Clone + std::hash::Hash + PartialEq> PartialEq for PMap<V> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<V: Clone + std::hash::Hash + Eq> Eq for PMap<V> {}

impl<V: Clone + std::hash::Hash> std::hash::Hash for PMap<V> {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.inner.hash(h)
    }
}

impl<V: Clone + std::hash::Hash + std::fmt::Debug> std::fmt::Debug for PMap<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl<V: Clone + std::hash::Hash> Default for PMap<V> {
    fn default() -> Self {
        PMap { inner: HashedMap::new() }
    }
}

impl<V: Clone + std::hash::Hash> PMap<V> {
    /// Every entry, in key order.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &V)> {
        self.inner.iter()
    }
}

impl<V: Clone + std::hash::Hash> std::ops::Index<&str> for PMap<V> {
    type Output = V;
    fn index(&self, k: &str) -> &V {
        &self.inner[k]
    }
}

impl<V: Clone + std::hash::Hash> FromIterator<(String, V)> for PMap<V> {
    fn from_iter<I: IntoIterator<Item = (String, V)>>(iter: I) -> Self {
        PMap { inner: iter.into_iter().collect() }
    }
}

impl Clone for PSet {
    fn clone(&self) -> Self {
        PSet { inner: self.inner.clone() }
    }
}

impl PartialEq for PSet {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl Eq for PSet {}

impl std::hash::Hash for PSet {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.inner.hash(h)
    }
}

impl std::fmt::Debug for PSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl PSet {
    pub fn iter(&self) -> impl Iterator<Item = &String> {
        self.inner.iter()
    }
}
