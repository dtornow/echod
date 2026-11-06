//! A table: entries looked up by key, viewed as a map from the key's view
//! to the value's view. The last entry with a key is the one the map
//! holds; `insert` replaces in place and `remove` takes every entry with
//! the key, so the map reads the same whatever the order of operations.

use vstd::prelude::*;

use super::node::str_eq;

/// A value the table views: `DeepView` under Verus; under cargo the
/// views are erased and any value will do.
#[cfg(verus_keep_ghost)]
pub use vstd::view::DeepView as Viewed;
#[cfg(not(verus_keep_ghost))]
pub trait Viewed {}
#[cfg(not(verus_keep_ghost))]
impl<T> Viewed for T {}

verus! {

/// A key: compared by its view.
pub trait KeyEq: View + Sized {
    fn key_eq(&self, other: &Self) -> (r: bool)
        ensures
            r == (self@ == other@),
    ;
}

impl KeyEq for u64 {
    fn key_eq(&self, other: &u64) -> (r: bool)
        ensures
            r == (self@ == other@),
    {
        *self == *other
    }
}

impl KeyEq for String {
    fn key_eq(&self, other: &String) -> (r: bool)
        ensures
            r == (self@ == other@),
    {
        str_eq(self.as_str(), other.as_str())
    }
}

pub struct Table<K, V> {
    pub entries: Vec<(K, V)>,
}

/// The map a sequence of entries reads as: later entries win.
pub open spec fn spec_table<K: View, V: DeepView>(s: Seq<(K, V)>) -> Map<K::V, V::V>
    decreases s.len(),
{
    if s.len() == 0 {
        Map::empty()
    } else {
        spec_table(s.drop_last()).insert(s.last().0@, s.last().1.deep_view())
    }
}

/// The entries without those keyed `k`, in order.
pub open spec fn spec_without<K: View, V: DeepView>(s: Seq<(K, V)>, k: K::V) -> Seq<(K, V)>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else if s.last().0@ == k {
        spec_without(s.drop_last(), k)
    } else {
        spec_without(s.drop_last(), k).push(s.last())
    }
}

impl<K: KeyEq, V: DeepView> DeepView for Table<K, V> {
    type V = Map<K::V, V::V>;
    open spec fn deep_view(&self) -> Map<K::V, V::V> {
        spec_table(self.entries@)
    }
}

impl<K: KeyEq, V: DeepView> View for Table<K, V> {
    type V = Map<K::V, V::V>;
    open spec fn view(&self) -> Map<K::V, V::V> {
        spec_table(self.entries@)
    }
}

pub proof fn lemma_table_last_match<K: View, V: DeepView>(s: Seq<(K, V)>, k: K::V, i: int)
    requires
        0 <= i < s.len(),
        s[i].0@ == k,
        forall|j: int| i < j < s.len() ==> s[j].0@ != k,
    ensures
        spec_table(s).contains_key(k),
        spec_table(s)[k] == s[i].1.deep_view(),
    decreases s.len(),
{
    if i < s.len() - 1 {
        lemma_table_last_match(s.drop_last(), k, i);
    }
}

pub proof fn lemma_table_absent<K: View, V: DeepView>(s: Seq<(K, V)>, k: K::V)
    requires
        forall|j: int| 0 <= j < s.len() ==> s[j].0@ != k,
    ensures
        !spec_table(s).contains_key(k),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_table_absent(s.drop_last(), k);
    }
}

pub proof fn lemma_table_push<K: View, V: DeepView>(s: Seq<(K, V)>, e: (K, V))
    ensures
        spec_table(s.push(e)) == spec_table(s).insert(e.0@, e.1.deep_view()),
{
    assert(s.push(e).drop_last() =~= s);
}

pub proof fn lemma_table_set<K: View, V: DeepView>(s: Seq<(K, V)>, i: int, e: (K, V))
    requires
        0 <= i < s.len(),
        s[i].0@ == e.0@,
        forall|j: int| i < j < s.len() ==> s[j].0@ != e.0@,
    ensures
        spec_table(s.update(i, e)) =~= spec_table(s).insert(e.0@, e.1.deep_view()),
    decreases s.len(),
{
    let t = s.update(i, e);
    if i == s.len() - 1 {
        assert(t.drop_last() =~= s.drop_last());
    } else {
        lemma_table_set(s.drop_last(), i, e);
        assert(t.drop_last() =~= s.drop_last().update(i, e));
    }
}

pub proof fn lemma_table_without<K: View, V: DeepView>(s: Seq<(K, V)>, k: K::V)
    ensures
        spec_table(spec_without(s, k)) =~= spec_table(s).remove(k),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_table_without(s.drop_last(), k);
        if s.last().0@ != k {
            lemma_table_push(spec_without(s.drop_last(), k), s.last());
        }
    }
}

/// `spec_without` over one more entry.
pub proof fn lemma_without_step<K: View, V: DeepView>(s: Seq<(K, V)>, i: int, k: K::V)
    requires
        0 <= i < s.len(),
    ensures
        spec_without(s.take(i + 1), k) == if s[i].0@ == k {
            spec_without(s.take(i), k)
        } else {
            spec_without(s.take(i), k).push(s[i])
        },
{
    assert(s.take(i + 1).drop_last() =~= s.take(i));
    assert(s.take(i + 1).last() == s[i]);
}

impl<K: KeyEq, V: Viewed> Table<K, V> {
    pub fn new() -> (r: Table<K, V>)
        ensures
            r@ == Map::<K::V, V::V>::empty(),
    {
        Table { entries: Vec::new() }
    }

    /// The position of the last entry keyed `k`.
    fn find(&self, k: &K) -> (r: Option<usize>)
        ensures
            match r {
                Some(i) => i < self.entries.len() && self.entries@[i as int].0@ == k@ && forall|j: int| i < j < self.entries.len() ==> self.entries@[j].0@ != k@,
                None => forall|j: int| 0 <= j < self.entries.len() ==> self.entries@[j].0@ != k@,
            },
    {
        let mut i = self.entries.len();
        while i > 0
            invariant
                i <= self.entries.len(),
                forall|j: int| i <= j < self.entries.len() ==> self.entries@[j].0@ != k@,
            decreases i,
        {
            i = i - 1;
            if self.entries[i].0.key_eq(k) {
                return Some(i);
            }
        }
        None
    }

    pub fn get(&self, k: &K) -> (r: Option<&V>)
        ensures
            match r {
                Some(v) => self@.contains_key(k@) && self@[k@] == v.deep_view(),
                None => !self@.contains_key(k@),
            },
    {
        match self.find(k) {
            Some(i) => {
                proof {
                    lemma_table_last_match(self.entries@, k@, i as int);
                }
                Some(&self.entries[i].1)
            },
            None => {
                proof {
                    lemma_table_absent(self.entries@, k@);
                }
                None
            },
        }
    }

    pub fn contains(&self, k: &K) -> (r: bool)
        ensures
            r == self@.contains_key(k@),
    {
        match self.get(k) {
            Some(_) => true,
            None => false,
        }
    }

    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == (self@ =~= Map::<K::V, V::V>::empty()),
    {
        if self.entries.len() == 0 {
            true
        } else {
            proof {
                let n = self.entries.len() as int;
                lemma_table_last_match(self.entries@, self.entries@[n - 1].0@, n - 1);
            }
            false
        }
    }

    pub fn insert(&mut self, k: K, v: V)
        ensures
            final(self)@ == old(self)@.insert(k@, v.deep_view()),
    {
        let ghost before = self.entries@;
        match self.find(&k) {
            Some(i) => {
                let e = (k, v);
                proof {
                    lemma_table_set(before, i as int, e);
                }
                self.entries.set(i, e);
            },
            None => {
                let e = (k, v);
                proof {
                    lemma_table_push(before, e);
                }
                self.entries.push(e);
            },
        }
    }

    /// Take every entry keyed `k`; the value the map held, if any.
    pub fn remove(&mut self, k: &K) -> (r: Option<V>)
        ensures
            final(self)@ == old(self)@.remove(k@),
            match r {
                Some(v) => old(self)@.contains_key(k@) && old(self)@[k@] == v.deep_view(),
                None => !old(self)@.contains_key(k@),
            },
    {
        let ghost before = self.entries@;
        let total = self.entries.len();
        let mut i: usize = 0;
        let mut n: usize = 0;
        let mut out: Option<V> = None;
        while n < total
            invariant
                total == before.len(),
                i <= n <= before.len(),
                self.entries@ == spec_without(before.take(n as int), k@) + before.skip(n as int),
                i == spec_without(before.take(n as int), k@).len(),
                match out {
                    Some(v) => spec_table(before.take(n as int)).contains_key(k@) && spec_table(before.take(n as int))[k@] == v.deep_view(),
                    None => !spec_table(before.take(n as int)).contains_key(k@),
                },
            decreases before.len() - n,
        {
            proof {
                lemma_without_step(before, n as int, k@);
                assert(before.take(n as int + 1).drop_last() =~= before.take(n as int));
                assert(before.take(n as int + 1).last() == before[n as int]);
                assert(self.entries@[i as int] == before[n as int]);
            }
            if self.entries[i].0.key_eq(k) {
                let e = self.entries.remove(i);
                out = Some(e.1);
                proof {
                    assert(self.entries@ =~= spec_without(before.take(n as int + 1), k@) + before.skip(n as int + 1));
                }
            } else {
                i = i + 1;
                proof {
                    assert(self.entries@ =~= spec_without(before.take(n as int + 1), k@) + before.skip(n as int + 1));
                }
            }
            n = n + 1;
        }
        proof {
            assert(before.take(before.len() as int) =~= before);
            assert(before.skip(before.len() as int) =~= Seq::empty());
            assert(self.entries@ =~= spec_without(before, k@));
            lemma_table_without(before, k@);
        }
        out
    }
}

} // verus!
