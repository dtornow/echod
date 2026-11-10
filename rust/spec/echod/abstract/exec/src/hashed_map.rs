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
