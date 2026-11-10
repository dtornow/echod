//! Persistent executable collections and their verified views.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use std::collections::BTreeSet;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::axioms::pset_seq;

use std::borrow::Borrow;
use std::fmt;
use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher, Hash, Hasher};

/// A persistent ordered map that keeps a hash of its contents up to date.
///
/// Clones share structure (`imbl::OrdMap`), an update copies one path, and the
/// hash is the wrapping sum of per-entry hashes, adjusted on every insert and
/// remove. Hashing a state built from these costs O(1) per map instead of a
/// walk over every entry, which is what dominates checking large states.
#[derive(Clone)]
pub struct HashedMap<K, V> {
    map: imbl::OrdMap<K, V>,
    sum: u64,
}

fn entry_hash<K: Hash, V: Hash>(k: &K, v: &V) -> u64 {
    BuildHasherDefault::<DefaultHasher>::default().hash_one((k, v))
}

impl<K: Ord + Clone + Hash, V: Clone + Hash> HashedMap<K, V> {
    pub fn new() -> Self {
        HashedMap { map: imbl::OrdMap::new(), sum: 0 }
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.get(k)
    }

    pub fn contains_key<Q>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.map.contains_key(k)
    }

    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.sum = self.sum.wrapping_add(entry_hash(&k, &v));
        let old = self.map.insert(k.clone(), v);
        if let Some(o) = &old {
            self.sum = self.sum.wrapping_sub(entry_hash(&k, o));
        }
        old
    }

    pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (key, old) = self.map.remove_with_key(k)?;
        self.sum = self.sum.wrapping_sub(entry_hash(&key, &old));
        Some(old)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.map.iter()
    }
}

impl<K: Ord + Clone + Hash, V: Clone + Hash> Default for HashedMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + Clone + Hash, V: Clone + Hash> FromIterator<(K, V)> for HashedMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut m = HashedMap::new();
        for (k, v) in iter {
            m.insert(k, v);
        }
        m
    }
}

impl<K, V, Q> std::ops::Index<&Q> for HashedMap<K, V>
where
    K: Ord + Clone + Hash + Borrow<Q>,
    V: Clone + Hash,
    Q: Ord + ?Sized,
{
    type Output = V;
    fn index(&self, k: &Q) -> &V {
        self.map.get(k).expect("key not in HashedMap")
    }
}

impl<K: Ord, V: PartialEq> PartialEq for HashedMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.sum == other.sum && self.map == other.map
    }
}

impl<K: Ord, V: Eq> Eq for HashedMap<K, V> {}

impl<K, V> Hash for HashedMap<K, V> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        h.write_usize(self.map.len());
        h.write_u64(self.sum);
    }
}

impl<K: Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for HashedMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.map.iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_depends_only_on_contents() {
        let mut a: HashedMap<u32, i64> = (0..100).map(|i| (i, 0)).collect();
        let mut b: HashedMap<u32, i64> = (0..100).rev().map(|i| (i, 0)).collect();
        a.insert(7, 10);
        a.insert(9, 20);
        b.insert(9, 20);
        b.insert(7, 5);
        b.insert(7, 10);
        b.insert(500, 1);
        b.remove(&500);
        assert_eq!(a, b);
        assert_eq!(a.sum, b.sum);
        b.insert(7, 11);
        assert_ne!(a.sum, b.sum);
        assert_ne!(a, b);
    }
}


verus! {

/// A persistent map from ids to `V`, seen by Verus as a
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

    /// Every key, in order, each once: `spec_keys` of the map, the keys
    /// sorted. `String`'s order is its bytes', which for UTF-8 is its
    /// characters' (`spec_before`).
    #[verifier::external_body]
    pub fn keys(&self) -> (r: Vec<String>)
        ensures
            r@.map_values(|s: String| s@) == echod_abstract_spec::state::spec_keys(self@),
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
