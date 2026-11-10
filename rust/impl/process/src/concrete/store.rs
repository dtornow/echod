//! Executable in-memory concrete store.
//!
//! The passive call/outcome algebra and mathematical store transition live in
//! `echod-rover-concrete-spec`; this module realizes that transition.

use vstd::pervasive::VecAdditionalExecFns;
use vstd::prelude::*;

pub use rover_concrete_spec::store::{Etag, Read, StoreCall, StoreError, StoreOutcome};
use rover_concrete_spec::store::*;
use rover_concrete_spec::model::Pid;
#[cfg(verus_keep_ghost)]
use rover_concrete_spec::model::{spec_bytes, spec_string};

verus! {

/// FNV-1a over the bytes. Ownership of a key is this hash modulo the fleet.
#[verifier::external_body]
pub fn fnv1a(s: &str) -> (r: u64) {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// The version a body quotes, as an S3 ETag: the same bytes are the same
/// version. Trusted to compute `spec_etag`: the hex, the hash and the lossy
/// decoding are `format!`, `fnv1a` and `from_utf8_lossy`.
#[verifier::external_body]
pub fn content_etag(body: &[u8]) -> (r: Etag)
    ensures
        r == spec_etag(body@),
{
    Etag(format!("{:016x}", fnv1a(&String::from_utf8_lossy(body))))
}

// ---------------------------------------------------------------------------
// The store
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Entry {
    pub key: String,
    pub body: Vec<u8>,
    pub version: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Store {
    pub entries: Vec<Entry>,
    pub appendable: bool,
    /// Each call a node makes carries a fresh `op`. The store executes each
    /// `(node, op)` once; Rover may deliver the envelope again, and a real
    /// HTTP exchange runs once. This is the counterpart of the version
    /// compare-and-swap in the Lean physical store: a stale write is never
    /// applied a second time, whatever the body's etag.
    pub seen: Vec<(Pid, u64)>,
}

impl View for Entry {
    type V = EntryV;
    open spec fn view(&self) -> EntryV {
        EntryV { key: self.key@, body: self.body@, version: self.version as nat }
    }
}

impl View for Store {
    type V = StoreV;
    open spec fn view(&self) -> StoreV {
        StoreV {
            entries: self.entries@.map_values(|e: Entry| e@),
            appendable: self.appendable,
            seen: self.seen@,
        }
    }
}

/// The content hash the in-memory store quotes: `content_etag`.
pub fn etag(body: &Vec<u8>) -> (r: Etag)
    ensures
        r == spec_etag(body@),
{
    content_etag(body.as_slice())
}

/// A string's characters. Trusted: the view of a `String` is its characters.
#[verifier::external_body]
pub fn chars_of(text: &String) -> (r: Vec<char>)
    ensures
        r@ == text@,
{
    text.chars().collect()
}

/// The string of some characters. Trusted, as `chars_of`.
#[verifier::external_body]
pub fn string_of(chars: &Vec<char>) -> (r: String)
    ensures
        r@ == chars@,
{
    chars.iter().collect()
}

fn copy_bytes(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == v@,
{
    let mut r: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            r@ == v@.take(i as int),
        decreases v.len() - i,
    {
        r.push(v[i]);
        proof {
            assert(v@.take(i + 1) =~= v@.take(i as int).push(v@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(v@.take(v.len() as int) =~= v@);
    }
    r
}

fn copy_seen(v: &Vec<(Pid, u64)>) -> (r: Vec<(Pid, u64)>)
    ensures
        r@ == v@,
{
    let mut r: Vec<(Pid, u64)> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            r@ == v@.take(i as int),
        decreases v.len() - i,
    {
        r.push(v[i]);
        proof {
            assert(v@.take(i + 1) =~= v@.take(i as int).push(v@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(v@.take(v.len() as int) =~= v@);
    }
    r
}

fn copy_entry(e: &Entry) -> (r: Entry)
    ensures
        r == *e,
{
    let r = Entry { key: e.key.clone(), body: copy_bytes(&e.body), version: e.version };
    proof {
        rover_abstract_spec::trusted::axiom_vec_ext(r.body, e.body);
    }
    r
}

fn copy_entries(v: &Vec<Entry>) -> (r: Vec<Entry>)
    ensures
        r@ == v@,
{
    let mut r: Vec<Entry> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            r@ == v@.take(i as int),
        decreases v.len() - i,
    {
        r.push(copy_entry(&v[i]));
        proof {
            assert(v@.take(i + 1) =~= v@.take(i as int).push(v@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(v@.take(v.len() as int) =~= v@);
    }
    r
}

/// Character order: `spec_before`. Byte order of UTF-8 is code point
/// order, so this is the order `str` compares in.
pub fn before(a: &String, b: &String) -> (r: bool)
    ensures
        r == spec_before(a@, b@),
{
    let ac = chars_of(a);
    let bc = chars_of(b);
    let mut i = 0;
    proof {
        assert(a@.skip(0) =~= a@);
        assert(b@.skip(0) =~= b@);
    }
    while i < ac.len() && i < bc.len()
        invariant
            i <= ac.len(),
            i <= bc.len(),
            ac@ == a@,
            bc@ == b@,
            spec_before(a@, b@) == spec_before(a@.skip(i as int), b@.skip(i as int)),
        decreases ac.len() - i,
    {
        if ac[i] != bc[i] {
            return ac[i] < bc[i];
        }
        proof {
            assert(a@.skip(i as int).drop_first() =~= a@.skip(i + 1));
            assert(b@.skip(i as int).drop_first() =~= b@.skip(i + 1));
        }
        i += 1;
    }
    ac.len() < bc.len()
}

/// `spec_starts`.
fn starts(text: &Vec<char>, prefix: &Vec<char>) -> (r: bool)
    ensures
        r == spec_starts(text@, prefix@),
{
    let mut i = 0;
    proof {
        assert(text@.skip(0) =~= text@);
        assert(prefix@.skip(0) =~= prefix@);
    }
    while i < prefix.len()
        invariant
            i <= prefix.len(),
            i <= text.len(),
            spec_starts(text@, prefix@) == spec_starts(text@.skip(i as int), prefix@.skip(i as int)),
        decreases prefix.len() - i,
    {
        if i >= text.len() || text[i] != prefix[i] {
            return false;
        }
        proof {
            assert(text@.skip(i as int).drop_first() =~= text@.skip(i + 1));
            assert(prefix@.skip(i as int).drop_first() =~= prefix@.skip(i + 1));
        }
        i += 1;
    }
    true
}

/// The first `/` at or after `start`: `spec_slash` on the tail.
fn slash_from(chars: &Vec<char>, start: usize) -> (r: Option<usize>)
    requires
        start <= chars.len(),
    ensures
        match r {
            Some(j) => start <= j < chars.len() && spec_slash(chars@.skip(start as int), 0) == Some(j - start),
            None => spec_slash(chars@.skip(start as int), 0) is None,
        },
{
    let mut j = start;
    while j < chars.len()
        invariant
            start <= j <= chars.len(),
            spec_slash(chars@.skip(start as int), 0) == spec_slash(chars@.skip(start as int), j - start),
        decreases chars.len() - j,
    {
        if chars[j] == '/' {
            return Some(j);
        }
        j += 1;
    }
    None
}

fn take_chars(chars: &Vec<char>, n: usize) -> (r: Vec<char>)
    requires
        n <= chars.len(),
    ensures
        r@ == chars@.take(n as int),
{
    let mut r: Vec<char> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n <= chars.len(),
            r@ == chars@.take(i as int),
        decreases n - i,
    {
        r.push(chars[i]);
        proof {
            assert(chars@.take(i + 1) =~= chars@.take(i as int).push(chars@[i as int]));
        }
        i += 1;
    }
    r
}

/// `spec_bump`.
fn bump(version: u64) -> (r: u64)
    ensures
        r as nat == spec_bump(version as nat),
{
    if version < u64::MAX { version + 1 } else { version }
}

pub open spec fn entries_v(v: Seq<Entry>) -> Seq<EntryV> {
    v.map_values(|e: Entry| e@)
}

pub open spec fn key_views(v: Seq<String>) -> Seq<Seq<char>> {
    v.map_values(|s: String| s@)
}

/// The vector some keys name is the vector whose keys they are.
pub proof fn lemma_bytes_keys(v: Vec<String>)
    ensures
        spec_bytes_keys(key_views(v@)) == v,
{
    let w = spec_bytes_keys(key_views(v@));
    assert(key_views(w@) == key_views(v@));
    assert(w@.len() == v@.len());
    assert forall|i: int| 0 <= i < v@.len() implies #[trigger] w@[i] == v@[i] by {
        assert(key_views(w@)[i] == w@[i]@);
        assert(key_views(v@)[i] == v@[i]@);
        rover_abstract_spec::trusted::axiom_string_ext(w@[i], v@[i]);
    }
    assert(w@ =~= v@);
    rover_abstract_spec::trusted::axiom_vec_ext(w, v);
}

/// `spec_find`.
fn find_entry(entries: &Vec<Entry>, key: &String) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < entries.len() && spec_find(entries_v(entries@), key@, 0) == Some(i as int),
            None => spec_find(entries_v(entries@), key@, 0) is None,
        },
{
    let mut i = 0;
    while i < entries.len()
        invariant
            i <= entries.len(),
            spec_find(entries_v(entries@), key@, 0) == spec_find(entries_v(entries@), key@, i as int),
        decreases entries.len() - i,
    {
        if entries[i].key == *key {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Where `spec_insert_at` puts an entry: before the first key it is before.
fn insert_index(entries: &Vec<Entry>, entry: &Entry) -> (i: usize)
    ensures
        i <= entries.len(),
        spec_insert_at(entries_v(entries@), entry@, 0) == if i < entries.len() {
            entries_v(entries@).take(i as int).push(entry@) + entries_v(entries@).skip(i as int)
        } else {
            entries_v(entries@).push(entry@)
        },
{
    let mut i = 0;
    while i < entries.len()
        invariant
            i <= entries.len(),
            spec_insert_at(entries_v(entries@), entry@, 0) == spec_insert_at(entries_v(entries@), entry@, i as int),
        decreases entries.len() - i,
    {
        if before(&entry.key, &entries[i].key) {
            return i;
        }
        i += 1;
    }
    i
}

/// `spec_put`: in place at the key, else at its place in order.
fn put_entry(entries: &mut Vec<Entry>, entry: Entry)
    ensures
        entries_v(final(entries)@) == spec_put(entries_v(old(entries)@), entry@),
{
    let ghost ev = entry@;
    let ghost before_v = entries_v(entries@);
    match find_entry(entries, &entry.key) {
        Some(i) => {
            entries.set(i, entry);
            proof {
                assert(entries_v(entries@) =~= before_v.update(i as int, ev));
            }
        },
        None => {
            let i = insert_index(entries, &entry);
            entries.insert(i, entry);
            proof {
                if i < before_v.len() {
                    assert(entries_v(entries@) =~= before_v.take(i as int).push(ev) + before_v.skip(i as int));
                } else {
                    assert(entries_v(entries@) =~= before_v.push(ev));
                }
            }
        },
    }
}

/// `spec_list`.
fn list_keys(entries: &Vec<Entry>, prefix: &String, max_keys: usize) -> (r: Vec<String>)
    ensures
        r == spec_bytes_keys(spec_list(entries_v(entries@), prefix@, max_keys as nat, 0, Seq::empty())),
{
    let pc = chars_of(prefix);
    let mut keys: Vec<String> = Vec::new();
    let mut i = 0;
    proof {
        assert(key_views(keys@) =~= Seq::<Seq<char>>::empty());
    }
    while i < entries.len() && keys.len() < max_keys
        invariant
            i <= entries.len(),
            pc@ == prefix@,
            spec_list(entries_v(entries@), prefix@, max_keys as nat, 0, Seq::empty())
                == spec_list(entries_v(entries@), prefix@, max_keys as nat, i as int, key_views(keys@)),
        decreases entries.len() - i,
    {
        let kc = chars_of(&entries[i].key);
        if starts(&kc, &pc) {
            let ghost before_v = key_views(keys@);
            keys.push(entries[i].key.clone());
            proof {
                assert(key_views(keys@) =~= before_v.push(entries@[i as int].key@));
            }
        }
        i += 1;
    }
    proof {
        lemma_bytes_keys(keys);
    }
    keys
}

/// `spec_prefixes`: the children one level under the prefix, each once.
fn prefix_children(entries: &Vec<Entry>, prefix: &String) -> (r: Vec<String>)
    ensures
        r == spec_bytes_keys(spec_prefixes(entries_v(entries@), prefix@, 0, Seq::empty())),
{
    let pc = chars_of(prefix);
    let mut out: Vec<String> = Vec::new();
    let mut i = 0;
    proof {
        assert(key_views(out@) =~= Seq::<Seq<char>>::empty());
    }
    while i < entries.len()
        invariant
            i <= entries.len(),
            pc@ == prefix@,
            spec_prefixes(entries_v(entries@), prefix@, 0, Seq::empty())
                == spec_prefixes(entries_v(entries@), prefix@, i as int, key_views(out@)),
        decreases entries.len() - i,
    {
        let kc = chars_of(&entries[i].key);
        if starts(&kc, &pc) {
            proof {
                lemma_starts_len(kc@, pc@);
            }
            match slash_from(&kc, pc.len()) {
                Some(j) => {
                    let child = string_of(&take_chars(&kc, j + 1));
                    let ghost before_v = key_views(out@);
                    if out.len() > 0 && out[out.len() - 1] == child {
                        assert(before_v.last() == child@);
                    } else {
                        out.push(child);
                        proof {
                            assert(key_views(out@) =~= before_v.push(child@));
                        }
                    }
                },
                None => {},
            }
        }
        i += 1;
    }
    proof {
        lemma_bytes_keys(out);
    }
    out
}

/// A prefix is no longer than what it starts.
pub proof fn lemma_starts_len(text: Seq<char>, prefix: Seq<char>)
    requires
        spec_starts(text, prefix),
    ensures
        prefix.len() <= text.len(),
    decreases prefix.len(),
{
    if prefix.len() > 0 {
        lemma_starts_len(text.drop_first(), prefix.drop_first());
    }
}

impl Store {
    pub fn empty(appendable: bool) -> (r: Store)
        ensures
            r@ == (StoreV { entries: Seq::empty(), appendable, seen: Seq::empty() }),
    {
        let r = Store { entries: Vec::new(), appendable, seen: Vec::new() };
        proof {
            assert(r@.entries =~= Seq::<EntryV>::empty());
        }
        r
    }

    pub fn copy(&self) -> (r: Store)
        ensures
            r == *self,
    {
        let r = Store { entries: copy_entries(&self.entries), appendable: self.appendable, seen: copy_seen(&self.seen) };
        proof {
            rover_abstract_spec::trusted::axiom_vec_ext(r.entries, self.entries);
            rover_abstract_spec::trusted::axiom_vec_ext(r.seen, self.seen);
        }
        r
    }

    /// One call: `spec_apply`.
    pub fn apply(&self, call: &StoreCall) -> (r: (Store, StoreOutcome))
        ensures
            (r.0@, r.1) == spec_apply(self@, *call),
    {
        let mut next = self.copy();
        let outcome = match call {
            StoreCall::Get { key } => match find_entry(&self.entries, key) {
                None => StoreOutcome::Got(None),
                Some(i) => {
                    let entry = &self.entries[i];
                    let body = copy_bytes(&entry.body);
                    proof {
                        rover_concrete_spec::simulation::lemma_bytes(entry.body@);
                        rover_abstract_spec::trusted::axiom_vec_ext(body, spec_bytes(entry.body@));
                    }
                    StoreOutcome::Got(Some((body, etag(&entry.body))))
                },
            },
            StoreCall::GetIfNoneMatch { key, etag: want } => match find_entry(&self.entries, key) {
                None => StoreOutcome::Read(Read::Absent),
                Some(i) => {
                    let entry = &self.entries[i];
                    let have = etag(&entry.body);
                    if have.0 == want.0 {
                        proof {
                            rover_abstract_spec::trusted::axiom_string_ext(have.0, want.0);
                        }
                        StoreOutcome::Read(Read::NotModified)
                    } else {
                        let body = copy_bytes(&entry.body);
                        proof {
                            rover_concrete_spec::simulation::lemma_bytes(entry.body@);
                            rover_abstract_spec::trusted::axiom_vec_ext(body, spec_bytes(entry.body@));
                        }
                        StoreOutcome::Read(Read::Body(body, have))
                    }
                },
            },
            StoreCall::PutIfNoneMatch { key, body } => {
                if find_entry(&self.entries, key).is_some() {
                    StoreOutcome::Failed(StoreError::PreconditionFailed)
                } else {
                    put_entry(&mut next.entries, Entry { key: key.clone(), body: copy_bytes(body), version: 1 });
                    StoreOutcome::Written(etag(body))
                }
            },
            StoreCall::PutIfMatch { key, body, etag: want } => match find_entry(&self.entries, key) {
                Some(i) => {
                    let have = etag(&self.entries[i].body);
                    if have.0 == want.0 {
                        proof {
                            rover_abstract_spec::trusted::axiom_string_ext(have.0, want.0);
                        }
                        let version = bump(self.entries[i].version);
                        put_entry(&mut next.entries, Entry { key: key.clone(), body: copy_bytes(body), version });
                        StoreOutcome::Written(etag(body))
                    } else {
                        proof {
                            if have.0@ != want.0@ {
                                assert(have != *want);
                            }
                        }
                        StoreOutcome::Failed(StoreError::PreconditionFailed)
                    }
                },
                None => StoreOutcome::Failed(StoreError::PreconditionFailed),
            },
            StoreCall::AppendIfMatch { key, offset, body, etag: want } => {
                if !self.appendable {
                    let text = "this store does not append".to_owned();
                    proof {
                        reveal_strlit("this store does not append");
                        assert(text@ =~= seq![
                            't', 'h', 'i', 's', ' ', 's', 't', 'o', 'r', 'e', ' ', 'd', 'o', 'e', 's', ' ',
                            'n', 'o', 't', ' ', 'a', 'p', 'p', 'e', 'n', 'd',
                        ]);
                        rover_concrete_spec::interpret::lemma_string_of(text);
                    }
                    StoreOutcome::Failed(StoreError::Unavailable(text))
                } else {
                    match find_entry(&self.entries, key) {
                        Some(i) => {
                            let have = etag(&self.entries[i].body);
                            if have.0 == want.0 && self.entries[i].body.len() as u64 == *offset {
                                proof {
                                    rover_abstract_spec::trusted::axiom_string_ext(have.0, want.0);
                                }
                                let mut joined = copy_bytes(&self.entries[i].body);
                                let mut more = copy_bytes(body);
                                joined.append(&mut more);
                                let version = bump(self.entries[i].version);
                                let tag = etag(&joined);
                                put_entry(&mut next.entries, Entry { key: key.clone(), body: joined, version });
                                StoreOutcome::Written(tag)
                            } else {
                                proof {
                                    if have.0@ != want.0@ {
                                        assert(have != *want);
                                    }
                                }
                                StoreOutcome::Failed(StoreError::PreconditionFailed)
                            }
                        },
                        None => StoreOutcome::Failed(StoreError::PreconditionFailed),
                    }
                }
            },
            StoreCall::Put { key, body } => {
                let version = match find_entry(&self.entries, key) {
                    Some(i) => bump(self.entries[i].version),
                    None => 1,
                };
                put_entry(&mut next.entries, Entry { key: key.clone(), body: copy_bytes(body), version });
                StoreOutcome::Done
            },
            StoreCall::Delete { key } => {
                match find_entry(&next.entries, key) {
                    Some(i) => {
                        let ghost before_v = entries_v(next.entries@);
                        next.entries.remove(i);
                        proof {
                            assert(entries_v(next.entries@) =~= spec_remove_at(before_v, i as int));
                        }
                    },
                    None => {},
                }
                StoreOutcome::Done
            },
            StoreCall::List { prefix, max_keys } => StoreOutcome::Listed(list_keys(&self.entries, prefix, *max_keys)),
            StoreCall::ListPrefixes { prefix } => StoreOutcome::Listed(prefix_children(&self.entries, prefix)),
        };
        (next, outcome)
    }
}

} // verus!
