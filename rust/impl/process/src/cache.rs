//! What a node remembers between requests: the documents it read or wrote.
//!
//! Everything is in memory, least recently used first out, bounded by entry
//! count and by bytes, since a workflow document grows with every promise
//! in it and a count alone bounds nothing. The entries sit in recency
//! order, least recent first: a hit moves its entry to the end, a put adds
//! at the end, eviction takes from the front. Each operation ensures it
//! computes its `spec_*` over that sequence.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use crate::doc::Loaded;
use crate::types::Etag;
use crate::verified::node::str_eq;
use crate::verified::text::copy_string;

#[cfg(verus_keep_ghost)]
use crate::doc::LoadedSpec;
#[cfg(verus_keep_ghost)]
use echod_concrete::store::EtagSpec;

verus! {

/// A document this node has seen, and the version it saw.
#[make_spec_type]
pub struct Cached {
    pub loaded: Loaded,
    pub etag: Etag,
    /// When the entry was read from or written to the store, or last
    /// revalidated against it.
    pub filled_at: u64,
}

#[cfg(verus_keep_ghost)]
impl CachedSpec {
    /// What the entry weighs against the byte budget: the object's size.
    pub open spec fn weight(self) -> u64 {
        if self.loaded.bytes < 1 { 1u64 } else { self.loaded.bytes }
    }
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

#[make_spec_type]
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
#[make_spec_type]
pub struct Entry {
    pub origin: String,
    pub cached: Cached,
}

/// The cache: entries least recently used first.
#[make_spec_type]
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
pub open spec fn spec_find(entries: Seq<EntrySpec>, origin: Seq<char>) -> Option<int>
    decreases entries.len(),
{
    if entries.len() == 0 {
        None
    } else if entries[0].origin == origin {
        Some(0int)
    } else {
        match spec_find(entries.drop_first(), origin) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

pub open spec fn spec_new(max_entries: usize, max_bytes: u64) -> CacheSpec {
    CacheSpec {
        entries: Seq::empty(),
        bytes: 0,
        max_entries: if max_entries < 1 { 1usize } else { max_entries },
        max_bytes: if max_bytes < 1 { 1u64 } else { max_bytes },
        hits: 0,
        misses: 0,
        evictions: 0,
    }
}

/// A hit moves the entry to the end and counts; a miss counts.
pub open spec fn spec_get(c: CacheSpec, origin: Seq<char>) -> (CacheSpec, Option<CachedSpec>) {
    match spec_find(c.entries, origin) {
        Some(i) => {
            let e = c.entries[i];
            (CacheSpec { entries: c.entries.remove(i).push(e), hits: c.hits.wrapping_add(1), ..c }, Some(e.cached))
        },
        None => (CacheSpec { misses: c.misses.wrapping_add(1), ..c }, None),
    }
}

/// The entry of `origin` taken out, its weight returned to the budget.
pub open spec fn spec_remove(c: CacheSpec, origin: Seq<char>) -> CacheSpec {
    match spec_find(c.entries, origin) {
        Some(i) => CacheSpec {
            entries: c.entries.remove(i),
            bytes: c.bytes.wrapping_sub(c.entries[i].cached.weight()),
            ..c
        },
        None => c,
    }
}

/// Evict, least recent first, until the bounds hold, keeping `keep`: the
/// entries evicted, in order, and the cache after.
pub open spec fn spec_trim(c: CacheSpec, keep: Seq<char>) -> (Seq<Seq<char>>, CacheSpec)
    decreases c.entries.len(),
{
    if (c.entries.len() > c.max_entries || c.bytes > c.max_bytes) && c.entries.len() > 0 && c.entries[0].origin != keep {
        let e = c.entries[0];
        let next = CacheSpec {
            entries: c.entries.drop_first(),
            bytes: c.bytes.wrapping_sub(e.cached.weight()),
            evictions: c.evictions.wrapping_add(1),
            ..c
        };
        let (rest, after) = spec_trim(next, keep);
        (seq![e.origin] + rest, after)
    } else {
        (Seq::empty(), c)
    }
}

/// Remember `cached` for `origin` in place of what was there, as the most
/// recent entry; then trim. The entry just put is never evicted, however
/// heavy: the request that committed it reads it next.
pub open spec fn spec_put(c: CacheSpec, origin: Seq<char>, cached: CachedSpec) -> (Seq<Seq<char>>, CacheSpec) {
    let c = spec_remove(c, origin);
    let c = CacheSpec {
        entries: c.entries.push(EntrySpec { origin, cached }),
        bytes: c.bytes.wrapping_add(cached.weight()),
        ..c
    };
    spec_trim(c, origin)
}

pub open spec fn spec_stats(c: CacheSpec) -> CacheStatsSpec {
    CacheStatsSpec { entries: c.entries.len() as usize, bytes: c.bytes, hits: c.hits, misses: c.misses, evictions: c.evictions }
}

// ---------------------------------------------------------------------------
// The cache, step for step
// ---------------------------------------------------------------------------

proof fn lemma_find_step(entries: Seq<EntrySpec>, origin: Seq<char>, i: int)
    requires
        0 <= i <= entries.len(),
        forall|j: int| 0 <= j < i ==> entries[j].origin != origin,
    ensures
        spec_find(entries, origin) == match spec_find(entries.skip(i), origin) {
            Some(k) => Some(k + i),
            None => None::<int>,
        },
    decreases i,
{
    if i == 0 {
        assert(entries.skip(0) =~= entries);
    } else {
        lemma_find_step(entries, origin, i - 1);
        assert(entries.skip(i - 1).drop_first() =~= entries.skip(i));
        assert(entries.skip(i - 1)[0] == entries[i - 1]);
    }
}

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
