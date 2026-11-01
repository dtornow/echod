use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher, Hash, Hasher};
use std::ops::Deref;
use std::sync::Arc;

/// A state hashed once, shared by every node that holds it. Two `Interned`
/// values from the same [`Interner`] are equal exactly when they are the same pointer.
pub struct Interned<T>(Arc<(u64, T)>);

impl<T> Interned<T> {
    pub fn hash64(&self) -> u64 {
        self.0 .0
    }
}

impl<T> Clone for Interned<T> {
    fn clone(&self) -> Self {
        Interned(self.0.clone())
    }
}

impl<T> Deref for Interned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0 .1
    }
}

impl<T: PartialEq> PartialEq for Interned<T> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || (self.0 .0 == other.0 .0 && self.0 .1 == other.0 .1)
    }
}

impl<T: Eq> Eq for Interned<T> {}

impl<T> Hash for Interned<T> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        h.write_u64(self.0 .0);
    }
}

impl<T: fmt::Debug> fmt::Debug for Interned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0 .1.fmt(f)
    }
}

/// Hash-consing table. Entries nobody else holds are dropped by [`Interner::collect`].
pub struct Interner<T> {
    table: RefCell<HashMap<u64, Vec<Interned<T>>, BuildHasherDefault<NoHash>>>,
}

impl<T: Eq + Hash> Interner<T> {
    pub fn new() -> Self {
        Interner { table: RefCell::default() }
    }

    pub fn intern(&self, value: T) -> Interned<T> {
        let hash = BuildHasherDefault::<DefaultHasher>::default().hash_one(&value);
        let mut table = self.table.borrow_mut();
        let bucket = table.entry(hash).or_default();
        if let Some(hit) = bucket.iter().find(|i| i.0 .1 == value) {
            return hit.clone();
        }
        let fresh = Interned(Arc::new((hash, value)));
        bucket.push(fresh.clone());
        fresh
    }

    pub fn collect(&self) {
        self.table.borrow_mut().retain(|_, bucket| {
            bucket.retain(|i| Arc::strong_count(&i.0) > 1);
            !bucket.is_empty()
        });
    }
}

impl<T: Eq + Hash> Default for Interner<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// The keys are already hashes.
#[derive(Default)]
pub struct NoHash(u64);

impl Hasher for NoHash {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = self.0.rotate_left(8) ^ u64::from(*b);
        }
    }
    fn write_u64(&mut self, n: u64) {
        self.0 = n;
    }
}
