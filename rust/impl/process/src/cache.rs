//! What a node remembers between requests: the documents it read or wrote.
//!
//! Everything is in memory, least recently used first out, bounded by entry
//! count and by bytes, since a workflow document grows with every promise
//! in it and a count alone bounds nothing. The entries sit in recency
//! order, least recent first: a hit moves its entry to the end, a put adds
//! at the end, eviction takes from the front. Each operation ensures it
//! computes its `spec_*` over that sequence.


use vstd::prelude::*;

use crate::document::Loaded;
use crate::types::Etag;
use crate::verified::node::str_eq;
use crate::verified::text::copy_string;

#[cfg(verus_keep_ghost)]
use crate::document::LoadedSpec;
#[cfg(verus_keep_ghost)]
use crate::concrete::store::EtagSpec;

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionCachedV as CachedSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionCacheStatsV as CacheStatsSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionCacheEntryV as EntrySpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionCacheV as CacheSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{spec_production_cache_find as spec_find, spec_production_cache_new as spec_new, spec_production_cache_get as spec_get, spec_production_cache_remove as spec_remove, spec_production_cache_trim as spec_trim, spec_production_cache_put as spec_put, spec_production_cache_stats as spec_stats};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::property_proof::lemma_production_cache_find_step as lemma_find_step;

verus! {
#[cfg(verus_keep_ghost)]
impl DeepView for Cached {
    type V = CachedSpec;
    open spec fn deep_view(&self) -> CachedSpec {
        CachedSpec {
            loaded: self.loaded.deep_view(),
            etag: self.etag.deep_view(),
            filled_at: self.filled_at.deep_view(),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for Cached {
    type V = CachedSpec;
    open spec fn view(&self) -> CachedSpec { self.deep_view() }
}

#[cfg(verus_keep_ghost)]
impl DeepView for CacheStats {
    type V = CacheStatsSpec;
    open spec fn deep_view(&self) -> CacheStatsSpec {
        CacheStatsSpec {
            entries: self.entries.deep_view(),
            bytes: self.bytes.deep_view(),
            hits: self.hits.deep_view(),
            misses: self.misses.deep_view(),
            evictions: self.evictions.deep_view(),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for CacheStats {
    type V = CacheStatsSpec;
    open spec fn view(&self) -> CacheStatsSpec { self.deep_view() }
}

#[cfg(verus_keep_ghost)]
impl DeepView for Entry {
    type V = EntrySpec;
    open spec fn deep_view(&self) -> EntrySpec {
        EntrySpec {
            origin: self.origin.deep_view(),
            cached: self.cached.deep_view(),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for Entry {
    type V = EntrySpec;
    open spec fn view(&self) -> EntrySpec { self.deep_view() }
}

#[cfg(verus_keep_ghost)]
impl DeepView for Cache {
    type V = CacheSpec;
    open spec fn deep_view(&self) -> CacheSpec {
        CacheSpec {
            entries: self.entries.deep_view(),
            bytes: self.bytes.deep_view(),
            max_entries: self.max_entries.deep_view(),
            max_bytes: self.max_bytes.deep_view(),
            hits: self.hits.deep_view(),
            misses: self.misses.deep_view(),
            evictions: self.evictions.deep_view(),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for Cache {
    type V = CacheSpec;
    open spec fn view(&self) -> CacheSpec { self.deep_view() }
}



/// A document this node has seen, and the version it saw.
pub struct Cached {
    pub loaded: Loaded,
    pub etag: Etag,
    /// When the entry was read from or written to the store, or last
    /// revalidated against it.
    pub filled_at: u64,
}


impl Cached {
    pub fn weight(&self) -> (r: u64)
        ensures
            r == self.deep_view().weight(),
    {
        if self.loaded.bytes < 1 { 1 } else { self.loaded.bytes }
    }

    pub fn copy(&self) -> (r: Cached)
        ensures
            r == *self,
    {
        Cached { loaded: self.loaded.copy(), etag: Etag(copy_string(&self.etag.0)), filled_at: self.filled_at }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]

pub struct CacheStats {
    pub entries: usize,
    pub bytes: u64,
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
}

/// One remembered document, under its origin.
pub struct Entry {
    pub origin: String,
    pub cached: Cached,
}

/// The cache: entries least recently used first.
pub struct Cache {
    pub entries: Vec<Entry>,
    pub bytes: u64,
    pub max_entries: usize,
    pub max_bytes: u64,
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
}

// ---------------------------------------------------------------------------
// What each operation means
// ---------------------------------------------------------------------------

/// The index of `origin`'s entry, the first if several.
impl Cache {
    /// A cache of at most `max_entries` documents weighing at most
    /// `max_bytes` together.
    pub fn new(max_entries: usize, max_bytes: u64) -> (r: Cache)
        ensures
            r.deep_view() == spec_new(max_entries, max_bytes),
    {
        let r = Cache {
            entries: Vec::new(),
            bytes: 0,
            max_entries: if max_entries < 1 { 1 } else { max_entries },
            max_bytes: if max_bytes < 1 { 1 } else { max_bytes },
            hits: 0,
            misses: 0,
            evictions: 0,
        };
        proof {
            assert(r.entries.deep_view() =~= Seq::<EntrySpec>::empty());
        }
        r
    }

    /// The index of `origin`'s entry.
    fn find(&self, origin: &str) -> (r: Option<usize>)
        ensures
            match r {
                Some(i) => i < self.entries.len() && spec_find(self.entries.deep_view(), origin@) == Some(i as int),
                None => spec_find(self.entries.deep_view(), origin@) is None,
            },
    {
        let ghost view = self.entries.deep_view();
        let mut i = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                view == self.entries.deep_view(),
                forall|j: int| 0 <= j < i ==> view[j].origin != origin@,
            decreases self.entries.len() - i,
        {
            if str_eq(self.entries[i].origin.as_str(), origin) {
                proof {
                    lemma_find_step(view, origin@, i as int);
                    assert(view.skip(i as int)[0] == view[i as int]);
                }
                return Some(i);
            }
            i += 1;
        }
        proof {
            lemma_find_step(view, origin@, i as int);
            assert(view.skip(i as int).len() == 0);
        }
        None
    }

    /// The document cached for `origin`, and a touch.
    pub fn get(&mut self, origin: &str) -> (r: Option<Cached>)
        ensures
            (final(self).deep_view(), r.deep_view()) == spec_get(old(self).deep_view(), origin@),
    {
        match self.find(origin) {
            Some(i) => {
                let ghost before = self.entries.deep_view();
                let e = self.entries.remove(i);
                let cached = e.cached.copy();
                self.entries.push(e);
                self.hits = self.hits.wrapping_add(1);
                proof {
                    assert(self.entries.deep_view() =~= before.remove(i as int).push(before[i as int]));
                }
                Some(cached)
            },
            None => {
                self.misses = self.misses.wrapping_add(1);
                None
            },
        }
    }

    /// Drop the document cached for `origin`.
    pub fn forget(&mut self, origin: &str)
        ensures
            final(self).deep_view() == spec_remove(old(self).deep_view(), origin@),
    {
        match self.find(origin) {
            Some(i) => {
                let ghost before = self.entries.deep_view();
                let e = self.entries.remove(i);
                self.bytes = self.bytes.wrapping_sub(e.cached.weight());
                proof {
                    assert(self.entries.deep_view() =~= before.remove(i as int));
                }
            },
            None => {},
        }
    }

    /// Evict, least recent first, until the bounds hold, keeping `keep`.
    /// Returns what was evicted.
    fn trim(&mut self, keep: &str) -> (r: Vec<String>)
        ensures
            (r.deep_view(), final(self).deep_view()) == spec_trim(old(self).deep_view(), keep@),
    {
        let ghost start = self.deep_view();
        let mut evicted: Vec<String> = Vec::new();
        proof {
            assert(evicted.deep_view() =~= Seq::<Seq<char>>::empty());
        }
        loop
            invariant
                spec_trim(start, keep@) == {
                    let (rest, after) = spec_trim(self.deep_view(), keep@);
                    (evicted.deep_view() + rest, after)
                },
            ensures
                !(self.entries.len() > self.max_entries || self.bytes > self.max_bytes)
                    || self.entries.len() == 0
                    || self.entries.deep_view()[0].origin == keep@,
            decreases self.entries.len(),
        {
            if !(self.entries.len() > self.max_entries || self.bytes > self.max_bytes) {
                break;
            }
            if self.entries.len() == 0 {
                break;
            }
            if str_eq(self.entries[0].origin.as_str(), keep) {
                break;
            }
            let ghost before = self.deep_view();
            let ghost ev0 = evicted.deep_view();
            let e = self.entries.remove(0);
            self.bytes = self.bytes.wrapping_sub(e.cached.weight());
            self.evictions = self.evictions.wrapping_add(1);
            evicted.push(e.origin);
            proof {
                assert(before.entries.drop_first() =~= self.deep_view().entries);
                let x = before.entries[0].origin;
                assert(evicted.deep_view() =~= ev0.push(x));
                let (rest, after) = spec_trim(self.deep_view(), keep@);
                assert(ev0 + (seq![x] + rest) =~= ev0.push(x) + rest);
            }
        }
        proof {
            assert(spec_trim(self.deep_view(), keep@) == (Seq::<Seq<char>>::empty(), self.deep_view()));
            assert(evicted.deep_view() + Seq::<Seq<char>>::empty() =~= evicted.deep_view());
        }
        evicted
    }

    /// Remember `cached` for `origin`, replacing what was there. Returns
    /// the origins evicted to make room, so whoever keeps count of the
    /// entries can forget them too.
    pub fn put(&mut self, origin: &str, cached: Cached) -> (r: Vec<String>)
        ensures
            (r.deep_view(), final(self).deep_view()) == spec_put(old(self).deep_view(), origin@, cached.deep_view()),
    {
        self.forget(origin);
        let ghost mid = self.entries.deep_view();
        self.bytes = self.bytes.wrapping_add(cached.weight());
        let ghost c = cached.deep_view();
        self.entries.push(Entry { origin: crate::verified::text::text(origin), cached });
        proof {
            assert(self.entries.deep_view() =~= mid.push(EntrySpec { origin: origin@, cached: c }));
        }
        self.trim(origin)
    }

    pub fn stats(&self) -> (r: CacheStats)
        ensures
            r.deep_view() == spec_stats(self.deep_view()),
    {
        CacheStats { entries: self.entries.len(), bytes: self.bytes, hits: self.hits, misses: self.misses, evictions: self.evictions }
    }
}

} // verus!
