//! What a node remembers between requests: the documents it read or wrote.
//!
//! The port is `Cache`. The one implementation keeps everything in memory,
//! least recently used first out, bounded by entry count and by bytes, since
//! an origin's document grows with every promise in it and a count alone
//! bounds nothing. A persistent cache would implement the same trait and gain
//! a warm start; it would still have to revalidate, so it saves bodies, not
//! round trips.

use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;

use crate::doc::Loaded;
use crate::store::Etag;

/// A document this node has seen, and the version it saw.
#[derive(Clone)]
pub struct Cached {
    pub loaded: Loaded,
    pub etag: Etag,
    /// When the entry was read from or written to the store, or last
    /// revalidated against it.
    pub filled_at: u64,
}

impl Cached {
    /// What the entry weighs against the byte budget: the object's size.
    pub fn weight(&self) -> u64 {
        self.loaded.bytes.max(1)
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CacheStats {
    pub entries: usize,
    pub bytes: u64,
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
}

pub trait Cache: Send + Sync {
    /// The document cached for `origin`, and a touch.
    fn get(&self, origin: &str) -> Option<Cached>;

    /// Remember `cached` for `origin`, replacing what was there. Returns the
    /// origins evicted to make room, so whoever keeps count of the entries
    /// can forget them too.
    fn put(&self, origin: &str, cached: Cached) -> Vec<String>;

    /// Drop the document cached for `origin`.
    fn forget(&self, origin: &str);

    fn stats(&self) -> CacheStats;
}

// ---------------------------------------------------------------------------
// In memory, least recently used out
// ---------------------------------------------------------------------------

struct Entry {
    cached: Cached,
    /// Position in the recency order; larger is more recent.
    tick: u64,
}

struct Inner {
    entries: HashMap<String, Entry>,
    /// Recency order: tick to origin.
    order: BTreeMap<u64, String>,
    bytes: u64,
    tick: u64,
    stats: CacheStats,
}

pub struct MemoryCache {
    inner: Mutex<Inner>,
    max_entries: usize,
    max_bytes: u64,
}

impl MemoryCache {
    /// A cache of at most `max_entries` documents weighing at most
    /// `max_bytes` together. The entry just put is never evicted, however
    /// heavy: the request that committed it reads it next.
    pub fn new(max_entries: usize, max_bytes: u64) -> Self {
        Self {
            inner: Mutex::new(Inner { entries: HashMap::new(), order: BTreeMap::new(), bytes: 0, tick: 0, stats: CacheStats::default() }),
            max_entries: max_entries.max(1),
            max_bytes: max_bytes.max(1),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Inner> {
        self.inner.lock().unwrap_or_else(|e| e.into_inner())
    }
}

impl Inner {
    fn touch(&mut self, origin: &str) {
        self.tick += 1;
        let tick = self.tick;
        if let Some(e) = self.entries.get_mut(origin) {
            self.order.remove(&e.tick);
            e.tick = tick;
            self.order.insert(tick, origin.to_string());
        }
    }

    fn remove(&mut self, origin: &str) -> Option<Cached> {
        let e = self.entries.remove(origin)?;
        self.order.remove(&e.tick);
        self.bytes -= e.cached.weight();
        Some(e.cached)
    }

    /// Evict, oldest first, until the bounds hold, keeping `keep`. Returns
    /// what was evicted.
    fn trim(&mut self, keep: &str, max_entries: usize, max_bytes: u64) -> Vec<String> {
        let mut evicted = Vec::new();
        while self.entries.len() > max_entries || self.bytes > max_bytes {
            let Some((_, oldest)) = self.order.iter().next().map(|(t, o)| (*t, o.clone())) else { break };
            if oldest == keep {
                break;
            }
            self.remove(&oldest);
            self.stats.evictions += 1;
            evicted.push(oldest);
        }
        evicted
    }
}

impl Cache for MemoryCache {
    fn get(&self, origin: &str) -> Option<Cached> {
        let mut i = self.lock();
        let hit = i.entries.get(origin).map(|e| e.cached.clone());
        match &hit {
            Some(_) => {
                i.stats.hits += 1;
                i.touch(origin);
            }
            None => i.stats.misses += 1,
        }
        hit
    }

    fn put(&self, origin: &str, cached: Cached) -> Vec<String> {
        let mut i = self.lock();
        i.remove(origin);
        i.tick += 1;
        let tick = i.tick;
        i.bytes += cached.weight();
        i.entries.insert(origin.to_string(), Entry { cached, tick });
        i.order.insert(tick, origin.to_string());
        i.trim(origin, self.max_entries, self.max_bytes)
    }

    fn forget(&self, origin: &str) {
        self.lock().remove(origin);
    }

    fn stats(&self) -> CacheStats {
        let i = self.lock();
        CacheStats { entries: i.entries.len(), bytes: i.bytes, ..i.stats }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn doc(bytes: u64, v: &str) -> Cached {
        Cached { loaded: Loaded { rows: vec![], row_count: 0, bytes, stamp: 0 }, etag: Etag(v.to_string()), filled_at: 0 }
    }

    #[test]
    fn least_recently_used_goes_first() {
        let c = MemoryCache::new(2, u64::MAX);
        c.put("a", doc(1, "1"));
        c.put("b", doc(1, "1"));
        assert!(c.get("a").is_some()); // a is now newer than b
        assert_eq!(c.put("c", doc(1, "1")), vec!["b".to_string()]);
        assert!(c.get("b").is_none(), "b was the least recently used");
        assert!(c.get("a").is_some());
        assert!(c.get("c").is_some());
        assert_eq!(c.stats().evictions, 1);
    }

    #[test]
    fn the_byte_budget_binds_too() {
        let c = MemoryCache::new(100, 10);
        c.put("a", doc(4, "1"));
        c.put("b", doc(4, "1"));
        c.put("c", doc(4, "1"));
        assert!(c.get("a").is_none());
        assert_eq!(c.stats().bytes, 8);
        assert_eq!(c.stats().entries, 2);
    }

    #[test]
    fn the_entry_just_put_is_kept_however_heavy() {
        let c = MemoryCache::new(100, 10);
        c.put("a", doc(4, "1"));
        c.put("big", doc(50, "1"));
        assert!(c.get("a").is_none());
        assert!(c.get("big").is_some());
        assert_eq!(c.stats().entries, 1);
    }

    #[test]
    fn a_replaced_entry_is_reweighed() {
        let c = MemoryCache::new(100, 100);
        c.put("a", doc(40, "1"));
        c.put("a", doc(10, "2"));
        assert_eq!(c.stats().bytes, 10);
        assert_eq!(c.get("a").unwrap().etag, Etag("2".into()));
        c.forget("a");
        assert_eq!(c.stats().bytes, 0);
        assert_eq!(c.stats().entries, 0);
    }
}
