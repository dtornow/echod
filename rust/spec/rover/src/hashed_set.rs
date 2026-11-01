use std::fmt;
use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher, Hash, Hasher};

/// A persistent ordered set that keeps a hash of its contents up to date: the
/// set counterpart of [`crate::HashedMap`]. Cloning is O(1), an insert or remove
/// copies one path, and hashing is O(1). The checker keeps each node's pending
/// work in one, so a node that differs from its parent by one item costs one
/// item, however much other work is pending.
#[derive(Clone)]
pub struct HashedSet<T> {
    set: imbl::OrdSet<T>,
    sum: u64,
}

fn item_hash<T: Hash>(t: &T) -> u64 {
    BuildHasherDefault::<DefaultHasher>::default().hash_one(t)
}

impl<T: Ord + Clone + Hash> HashedSet<T> {
    pub fn new() -> Self {
        HashedSet { set: imbl::OrdSet::new(), sum: 0 }
    }

    /// Returns whether `t` was newly inserted.
    pub fn insert(&mut self, t: T) -> bool {
        let h = item_hash(&t);
        if self.set.insert(t).is_some() {
            return false;
        }
        self.sum = self.sum.wrapping_add(h);
        true
    }

    /// Returns whether `t` was present.
    pub fn remove(&mut self, t: &T) -> bool {
        if self.set.remove(t).is_none() {
            return false;
        }
        self.sum = self.sum.wrapping_sub(item_hash(t));
        true
    }

    pub fn contains(&self, t: &T) -> bool {
        self.set.contains(t)
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.set.iter()
    }

    pub fn len(&self) -> usize {
        self.set.len()
    }

    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }

    pub fn union(&self, other: &Self) -> Self {
        let (big, small) = if self.len() >= other.len() { (self, other) } else { (other, self) };
        let mut out = big.clone();
        for t in small.iter() {
            out.insert(t.clone());
        }
        out
    }
}

impl<T: Ord + Clone + Hash> Default for HashedSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord + Clone + Hash> FromIterator<T> for HashedSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut s = HashedSet::new();
        for t in iter {
            s.insert(t);
        }
        s
    }
}

impl<'a, T: Ord + Clone + Hash> IntoIterator for &'a HashedSet<T> {
    type Item = &'a T;
    type IntoIter = imbl::ordset::Iter<'a, T, imbl::shared_ptr::DefaultSharedPtr>;
    fn into_iter(self) -> Self::IntoIter {
        self.set.iter()
    }
}

impl<T: Ord> PartialEq for HashedSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.sum == other.sum && self.set == other.set
    }
}

impl<T: Ord> Eq for HashedSet<T> {}

impl<T> Hash for HashedSet<T> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        h.write_usize(self.set.len());
        h.write_u64(self.sum);
    }
}

impl<T: Ord + fmt::Debug> fmt::Debug for HashedSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.set.iter()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_depends_only_on_contents() {
        let mut a: HashedSet<u32> = (0..50).collect();
        let b: HashedSet<u32> = (0..50).rev().collect();
        assert_eq!(a, b);
        assert!(!a.insert(7));
        assert!(a.insert(500));
        assert_ne!(a, b);
        assert!(a.remove(&500));
        assert_eq!((a.sum, a.len()), (b.sum, b.len()));
        assert_eq!(a.union(&[1000].into_iter().collect()).len(), 51);
    }
}
