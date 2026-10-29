//! Executable raw object-store semantics.
//!
//! The store owns one configured bucket.  Its durable state is only keyed
//! bytes and opaque versions; document decoding belongs to a later derived
//! view.  An environmental disposition is an explicit input to every step,
//! so an unavailable response never silently chooses whether a write landed.

#![cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_kernel::store::{distinct_by, fold_by, mentions};
#[cfg(verus_keep_ghost)]
use echod_kernel::store_proof::{
    lemma_fold_distinct, lemma_fold_dom, lemma_fold_push, lemma_fold_remove, lemma_fold_update,
};

verus! {

/// Store keys are opaque byte strings.  This avoids giving decoded document
/// names any place in the durable state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Key {
    pub bytes: Vec<u8>,
}

impl Key {
    pub fn new(bytes: Vec<u8>) -> Key {
        Key { bytes }
    }

    pub fn copy(&self) -> (key: Key)
        ensures key@ == self@,
    {
        let mut bytes: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < self.bytes.len()
            invariant
                i <= self.bytes@.len(),
                bytes@ == self.bytes@.take(i as int),
            decreases self.bytes@.len() - i,
        {
            bytes.push(self.bytes[i]);
            i += 1;
        }
        Key { bytes }
    }

    pub fn equal(&self, other: &Key) -> (equal: bool)
        ensures equal == (self@ == other@),
    {
        if self.bytes.len() != other.bytes.len() {
            return false;
        }
        let mut i: usize = 0;
        while i < self.bytes.len()
            invariant
                self.bytes@.len() == other.bytes@.len(),
                i <= self.bytes@.len(),
                forall|j: int| 0 <= j < i
                    ==> self.bytes@[j] == other.bytes@[j],
            decreases self.bytes@.len() - i,
        {
            if self.bytes[i] != other.bytes[i] {
                return false;
            }
            i += 1;
        }
        assert(self.bytes@ =~= other.bytes@);
        true
    }
}

#[cfg(verus_keep_ghost)]
impl View for Key {
    type V = Seq<u8>;
    open spec fn view(&self) -> Seq<u8> { self.bytes@ }
}

#[cfg(verus_keep_ghost)]
impl DeepView for Key {
    type V = Seq<u8>;
    open spec fn deep_view(&self) -> Seq<u8> { self@ }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawObject {
    pub bytes: Vec<u8>,
    pub version: u64,
}

#[cfg(verus_keep_ghost)]
pub struct ARawObject {
    pub bytes: Seq<u8>,
    pub version: u64,
}

#[cfg(verus_keep_ghost)]
impl View for RawObject {
    type V = ARawObject;
    open spec fn view(&self) -> ARawObject {
        ARawObject { bytes: self.bytes@, version: self.version }
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for RawObject {
    type V = ARawObject;
    open spec fn deep_view(&self) -> ARawObject { self@ }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub key: Key,
    pub object: RawObject,
}

#[cfg(verus_keep_ghost)]
pub struct AEntry {
    pub key: Seq<u8>,
    pub object: ARawObject,
}

#[cfg(verus_keep_ghost)]
impl View for Entry {
    type V = AEntry;
    open spec fn view(&self) -> AEntry {
        AEntry { key: self.key@, object: self.object@ }
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for Entry {
    type V = AEntry;
    open spec fn deep_view(&self) -> AEntry { self@ }
}

#[cfg(verus_keep_ghost)]
pub open spec fn entry_key() -> spec_fn(Entry) -> Seq<u8> {
    |entry: Entry| entry.key@
}

#[cfg(verus_keep_ghost)]
pub open spec fn entry_value() -> spec_fn(Entry) -> ARawObject {
    |entry: Entry| entry.object@
}

#[cfg(verus_keep_ghost)]
pub open spec fn entry_keys(entries: Seq<Entry>) -> Seq<Seq<u8>> {
    entries.map_values(|entry: Entry| entry.key@)
}

/// One configured bucket. `next_version` is a deterministic source of fresh
/// opaque versions and is not itself an object.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawStore {
    pub bucket: String,
    pub entries: Vec<Entry>,
    pub next_version: u64,
}

#[cfg(verus_keep_ghost)]
pub struct ARawStore {
    pub bucket: Seq<char>,
    /// The exact executable representation, exposed to the derived decoder.
    pub entries: Seq<AEntry>,
    pub objects: Map<Seq<u8>, ARawObject>,
    /// Executable representation order. It is not listing order.
    pub keys: Seq<Seq<u8>>,
    pub next_version: u64,
}

#[cfg(verus_keep_ghost)]
impl View for RawStore {
    type V = ARawStore;
    open spec fn view(&self) -> ARawStore {
        ARawStore {
            bucket: self.bucket@,
            entries: self.entries.deep_view(),
            objects: fold_by(self.entries@, entry_key(), entry_value()),
            keys: entry_keys(self.entries@),
            next_version: self.next_version,
        }
    }
}

impl RawStore {
    pub open spec fn wf(self) -> bool {
        &&& distinct_by(self.entries@, entry_key())
        &&& self.next_version > 0
        &&& forall|i: int| 0 <= i < self.entries@.len()
            ==> self.entries@[i].object.version < self.next_version
    }

    pub fn new(bucket: String) -> (store: RawStore)
        ensures
            store.wf(),
            store@.bucket == bucket@,
            store@.objects =~= Map::<Seq<u8>, ARawObject>::empty(),
            store@.keys == Seq::<Seq<u8>>::empty(),
            store@.next_version == 1,
    {
        RawStore { bucket, entries: Vec::new(), next_version: 1 }
    }

    pub fn find(&self, key: &Key) -> (found: Option<usize>)
        ensures
            match found {
                Some(i) => i < self.entries@.len()
                    && self.entries@[i as int].key@ == key@,
                None => !self@.objects.contains_key(key@),
            },
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries@.len(),
                forall|j: int| 0 <= j < i
                    ==> self.entries@[j].key@ != key@,
            decreases self.entries@.len() - i,
        {
            if self.entries[i].key.equal(key) {
                proof {
                    assert(self.entries@[i as int].key@ == key@);
                }
                return Some(i);
            }
            i += 1;
        }
        proof {
            lemma_fold_dom(self.entries@, entry_key(), entry_value());
            assert forall|j: int| 0 <= j < self.entries@.len()
                implies #[trigger] entry_key()(self.entries@[j]) != key@ by {}
        }
        None
    }

    fn replace(&mut self, i: usize, object: RawObject)
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
            object.version > 0,
            object.version < old(self).next_version,
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
            final(self)@.keys == old(self)@.keys,
            final(self)@.next_version == old(self)@.next_version,
            final(self)@.objects =~= old(self)@.objects.insert(
                old(self).entries@[i as int].key@, object@),
    {
        let key = self.entries[i].key.copy();
        let entry = Entry { key, object };
        proof {
            lemma_fold_update(
                self.entries@, entry_key(), entry_value(), i as int, entry,
            );
        }
        self.entries[i] = entry;
    }

    fn push(&mut self, entry: Entry)
        requires
            old(self).wf(),
            !old(self)@.objects.contains_key(entry.key@),
            entry.object.version > 0,
            entry.object.version < old(self).next_version,
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
            final(self)@.keys == old(self)@.keys.push(entry.key@),
            final(self)@.next_version == old(self)@.next_version,
            final(self)@.objects
                == old(self)@.objects.insert(entry.key@, entry.object@),
    {
        proof {
            let s = self.entries@;
            lemma_fold_dom(s, entry_key(), entry_value());
            lemma_fold_push(s, entry_key(), entry_value(), entry);
            let t = s.push(entry);
            assert forall|a: int, b: int|
                0 <= a < t.len() && 0 <= b < t.len()
                && #[trigger] entry_key()(t[a]) == #[trigger] entry_key()(t[b])
                implies a == b by {
                if a == s.len() && b < s.len() {
                    assert(entry_key()(s[b]) == entry.key@);
                    assert(mentions(s, entry_key(), entry.key@));
                }
                if b == s.len() && a < s.len() {
                    assert(entry_key()(s[a]) == entry.key@);
                    assert(mentions(s, entry_key(), entry.key@));
                }
            }
        }
        self.entries.push(entry);
    }

    fn remove(&mut self, i: usize)
        requires
            old(self).wf(),
            i < old(self).entries@.len(),
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
            final(self)@.next_version == old(self)@.next_version,
            final(self)@.keys
                == old(self)@.keys.remove(i as int),
            final(self)@.objects =~= old(self)@.objects.remove(
                old(self).entries@[i as int].key@),
    {
        proof {
            lemma_fold_remove(
                self.entries@, entry_key(), entry_value(), i as int,
            );
        }
        self.entries.remove(i);
    }
}

/// The environment's resolution of one operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum Environment {
    /// The store answers with the operation's ordinary result.
    Normal,
    /// No mutation occurs and the caller sees unavailable.
    FailBeforeApply,
    /// A successful mutation occurs, but the caller sees unavailable.
    ApplyButLostAck,
    /// A failed conditional is explicitly observed as refused.
    Refused,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operation {
    Get { key: Key },
    GetIfNoneMatch { key: Key, version: u64 },
    Create { key: Key, bytes: Vec<u8> },
    Update { key: Key, version: u64, bytes: Vec<u8> },
    Append { key: Key, version: u64, offset: u64, bytes: Vec<u8> },
    Put { key: Key, bytes: Vec<u8> },
    Delete { key: Key },
    List { prefix: Key, max_keys: usize },
    ListPrefixes { prefix: Key },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConditionalRead {
    Body(RawObject),
    NotModified,
    Absent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum Failure {
    Unavailable,
    Refused,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Response {
    Got(Option<RawObject>),
    Read(ConditionalRead),
    Written(u64),
    Done,
    Listed(Vec<Key>),
    Failed(Failure),
    /// The selected environment cannot describe this operation/state pair.
    InvalidChoice,
}

/// Lexicographic byte order, shared by both listing operations.
pub open spec fn lex_less_from(a: Seq<u8>, b: Seq<u8>, i: nat) -> bool
    decreases a.len() - i,
{
    if i >= a.len() {
        i < b.len()
    } else if i >= b.len() {
        false
    } else if a[i as int] < b[i as int] {
        true
    } else if a[i as int] > b[i as int] {
        false
    } else {
        lex_less_from(a, b, i + 1)
    }
}

pub open spec fn lex_less(a: Seq<u8>, b: Seq<u8>) -> bool {
    lex_less_from(a, b, 0)
}

fn key_less_from(a: &Key, b: &Key, i: usize) -> (less: bool)
    requires i <= a@.len(), i <= b@.len(),
    ensures less == lex_less_from(a@, b@, i as nat),
    decreases a@.len() - i,
{
    if i >= a.bytes.len() {
        i < b.bytes.len()
    } else if i >= b.bytes.len() {
        false
    } else if a.bytes[i] < b.bytes[i] {
        true
    } else if a.bytes[i] > b.bytes[i] {
        false
    } else {
        key_less_from(a, b, i + 1)
    }
}

pub fn key_less(a: &Key, b: &Key) -> (less: bool)
    ensures less == lex_less(a@, b@),
{
    key_less_from(a, b, 0)
}

pub open spec fn is_prefix_from(
    key: Seq<u8>,
    prefix: Seq<u8>,
    i: nat,
) -> bool
    decreases prefix.len() - i,
{
    if i >= prefix.len() {
        true
    } else if i >= key.len() {
        false
    } else {
        key[i as int] == prefix[i as int]
            && is_prefix_from(key, prefix, i + 1)
    }
}

pub open spec fn is_prefix(key: Seq<u8>, prefix: Seq<u8>) -> bool {
    is_prefix_from(key, prefix, 0)
}

fn starts_with_from(key: &Key, prefix: &Key, i: usize) -> (yes: bool)
    requires i <= key@.len(), i <= prefix@.len(),
    ensures yes == is_prefix_from(key@, prefix@, i as nat),
    decreases prefix@.len() - i,
{
    if i >= prefix.bytes.len() {
        true
    } else if i >= key.bytes.len() {
        false
    } else if key.bytes[i] != prefix.bytes[i] {
        false
    } else {
        starts_with_from(key, prefix, i + 1)
    }
}

pub fn starts_with(key: &Key, prefix: &Key) -> (yes: bool)
    ensures yes == is_prefix(key@, prefix@),
{
    starts_with_from(key, prefix, 0)
}

pub open spec fn insert_position_from(
    keys: Seq<Seq<u8>>,
    key: Seq<u8>,
    i: nat,
) -> nat
    decreases keys.len() - i,
{
    if i >= keys.len() || lex_less(key, keys[i as int]) {
        i
    } else {
        insert_position_from(keys, key, i + 1)
    }
}

fn insertion_position_from(
    keys: &Vec<Key>,
    key: &Key,
    i: usize,
) -> (position: usize)
    requires i <= keys@.len(),
    ensures
        position as nat == insert_position_from(keys.deep_view(), key@, i as nat),
        i <= position <= keys@.len(),
    decreases keys@.len() - i,
{
    if i >= keys.len() || key_less(key, &keys[i]) {
        i
    } else {
        insertion_position_from(keys, key, i + 1)
    }
}

pub open spec fn sorted_insert(
    keys: Seq<Seq<u8>>,
    key: Seq<u8>,
) -> Seq<Seq<u8>> {
    keys.insert(insert_position_from(keys, key, 0) as int, key)
}

fn insert_sorted(keys: &mut Vec<Key>, key: Key)
    ensures
        final(keys).deep_view()
            == sorted_insert(old(keys).deep_view(), key@),
{
    let i = insertion_position_from(keys, &key, 0);
    keys.insert(i, key);
}

fn insert_sorted_unique(keys: &mut Vec<Key>, key: Key)
    ensures
        final(keys).deep_view() == if old(keys).deep_view().contains(key@) {
            old(keys).deep_view()
        } else {
            sorted_insert(old(keys).deep_view(), key@)
        },
{
    let mut i: usize = 0;
    while i < keys.len()
        invariant
            i <= keys@.len(),
            forall|j: int| 0 <= j < i ==> keys@[j]@ != key@,
        decreases keys@.len() - i,
    {
        if keys[i].equal(&key) {
            proof {
                assert(keys.deep_view()[i as int] == key@);
                assert(keys.deep_view().contains(key@));
            }
            return;
        }
        i += 1;
    }
    proof {
        assert(!keys.deep_view().contains(key@)) by {
            if keys.deep_view().contains(key@) {
                let j = choose|j: int| 0 <= j < keys.deep_view().len()
                    && keys.deep_view()[j] == key@;
                assert(keys@[j]@ == key@);
            }
        }
    }
    insert_sorted(keys, key);
}

pub open spec fn matching_keys(
    entries: Seq<Entry>,
    prefix: Seq<u8>,
) -> Seq<Seq<u8>>
    decreases entries.len(),
{
    if entries.len() == 0 {
        Seq::empty()
    } else {
        let before = matching_keys(entries.drop_last(), prefix);
        let key = entries.last().key@;
        if is_prefix(key, prefix) {
            sorted_insert(before, key)
        } else {
            before
        }
    }
}

fn pop_to_limit(keys: &mut Vec<Key>, max_keys: usize)
    ensures
        final(keys).deep_view()
            == take_at_most(old(keys).deep_view(), max_keys as nat),
{
    if max_keys < keys.len() {
        keys.truncate(max_keys);
        proof {
            lemma_deep_view_take(old(keys)@, max_keys as int);
        }
    }
}

pub open spec fn take_at_most<T>(items: Seq<T>, max: nat) -> Seq<T> {
    if max < items.len() {
        items.take(max as int)
    } else {
        items
    }
}

pub proof fn lemma_deep_view_take(keys: Seq<Key>, n: int)
    requires 0 <= n <= keys.len(),
    ensures
        keys.take(n).map_values(|key: Key| key@)
            == keys.map_values(|key: Key| key@).take(n),
{
    let left = keys.take(n).map_values(|key: Key| key@);
    let right = keys.map_values(|key: Key| key@).take(n);
    assert(left.len() == right.len());
    assert forall|i: int| 0 <= i < left.len()
        implies left[i] == right[i] by {}
    assert(left =~= right);
}

impl RawStore {
    pub fn list(&self, prefix: &Key, max_keys: usize) -> (keys: Vec<Key>)
        ensures
            keys.deep_view()
                == take_at_most(
                    matching_keys(self.entries@, prefix@), max_keys as nat),
    {
        let mut keys: Vec<Key> = Vec::new();
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries@.len(),
                keys.deep_view()
                    == matching_keys(self.entries@.take(i as int), prefix@),
            decreases self.entries@.len() - i,
        {
            if starts_with(&self.entries[i].key, prefix) {
                insert_sorted(&mut keys, self.entries[i].key.copy());
            }
            proof {
                let processed = self.entries@.take(i as int + 1);
                assert(processed.drop_last()
                    =~= self.entries@.take(i as int));
                assert(processed.last() == self.entries@[i as int]);
            }
            i += 1;
        }
        pop_to_limit(&mut keys, max_keys);
        assert(self.entries@.take(self.entries@.len() as int) == self.entries@);
        keys
    }
}

pub open spec fn delimiter_end_from(key: Seq<u8>, i: nat) -> Option<nat>
    decreases key.len() - i,
{
    if i >= key.len() {
        None
    } else if key[i as int] == 47u8 {
        Some(i + 1)
    } else {
        delimiter_end_from(key, i + 1)
    }
}

pub open spec fn direct_prefix(
    key: Seq<u8>,
    prefix: Seq<u8>,
) -> Option<Seq<u8>> {
    if is_prefix(key, prefix) {
        match delimiter_end_from(key, prefix.len()) {
            Some(end) => Some(key.take(end as int)),
            None => None,
        }
    } else {
        None
    }
}

fn delimiter_end(key: &Key, i: usize) -> (end: Option<usize>)
    requires i <= key@.len(),
    ensures
        match end {
            Some(n) => delimiter_end_from(key@, i as nat) == Some(n as nat)
                && n <= key@.len(),
            None => delimiter_end_from(key@, i as nat) is None,
        },
    decreases key@.len() - i,
{
    if i >= key.bytes.len() {
        None
    } else if key.bytes[i] == 47u8 {
        Some(i + 1)
    } else {
        delimiter_end(key, i + 1)
    }
}

fn key_take(key: &Key, end: usize) -> (taken: Key)
    requires end <= key@.len(),
    ensures taken@ == key@.take(end as int),
{
    let mut bytes: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < end
        invariant
            i <= end,
            end <= key@.len(),
            bytes@ == key@.take(i as int),
        decreases end - i,
    {
        bytes.push(key.bytes[i]);
        i += 1;
    }
    Key { bytes }
}

fn get_direct_prefix(key: &Key, prefix: &Key) -> (result: Option<Key>)
    ensures result.deep_view() == direct_prefix(key@, prefix@),
{
    if !starts_with(key, prefix) {
        None
    } else {
        proof {
            lemma_prefix_length(key@, prefix@, 0);
        }
        match delimiter_end(key, prefix.bytes.len()) {
            Some(end) => Some(key_take(key, end)),
            None => None,
        }
    }
}

pub proof fn lemma_prefix_length(key: Seq<u8>, prefix: Seq<u8>, i: nat)
    requires
        i <= key.len(),
        i <= prefix.len(),
        is_prefix_from(key, prefix, i),
    ensures
        prefix.len() <= key.len(),
    decreases prefix.len() - i,
{
    if i < prefix.len() {
        assert(i < key.len());
        lemma_prefix_length(key, prefix, i + 1);
    }
}

pub open spec fn direct_prefixes(
    entries: Seq<Entry>,
    prefix: Seq<u8>,
) -> Seq<Seq<u8>>
    decreases entries.len(),
{
    if entries.len() == 0 {
        Seq::empty()
    } else {
        let before = direct_prefixes(entries.drop_last(), prefix);
        match direct_prefix(entries.last().key@, prefix) {
            Some(key) => if before.contains(key) {
                before
            } else {
                sorted_insert(before, key)
            },
            None => before,
        }
    }
}

impl RawStore {
    pub fn list_prefixes(&self, prefix: &Key) -> (keys: Vec<Key>)
        ensures keys.deep_view() == direct_prefixes(self.entries@, prefix@),
    {
        let mut keys: Vec<Key> = Vec::new();
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries@.len(),
                keys.deep_view()
                    == direct_prefixes(self.entries@.take(i as int), prefix@),
            decreases self.entries@.len() - i,
        {
            match get_direct_prefix(&self.entries[i].key, prefix) {
                Some(key) => insert_sorted_unique(&mut keys, key),
                None => {},
            }
            proof {
                let processed = self.entries@.take(i as int + 1);
                assert(processed.drop_last()
                    =~= self.entries@.take(i as int));
                assert(processed.last() == self.entries@[i as int]);
            }
            i += 1;
        }
        assert(self.entries@.take(self.entries@.len() as int) == self.entries@);
        keys
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn same_raw_state(a: ARawStore, b: ARawStore) -> bool {
    &&& a.bucket == b.bucket
    &&& a.entries == b.entries
    &&& a.objects == b.objects
    &&& a.keys == b.keys
    &&& a.next_version == b.next_version
}

fn copy_bytes(source: &Vec<u8>) -> (bytes: Vec<u8>)
    ensures bytes@ == source@,
{
    let mut bytes: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < source.len()
        invariant
            i <= source@.len(),
            bytes@ == source@.take(i as int),
        decreases source@.len() - i,
    {
        bytes.push(source[i]);
        i += 1;
    }
    bytes
}

fn append_bytes(left: &Vec<u8>, right: &Vec<u8>) -> (bytes: Vec<u8>)
    ensures bytes@ == left@ + right@,
{
    let mut bytes = copy_bytes(left);
    let mut i: usize = 0;
    while i < right.len()
        invariant
            i <= right@.len(),
            bytes@ == left@ + right@.take(i as int),
        decreases right@.len() - i,
    {
        bytes.push(right[i]);
        i += 1;
    }
    bytes
}

impl RawObject {
    pub fn copy(&self) -> (object: RawObject)
        ensures object@ == self@,
    {
        RawObject { bytes: copy_bytes(&self.bytes), version: self.version }
    }
}

impl RawStore {
    /// Exact read of one key.
    pub fn get(&self, key: &Key) -> (object: Option<RawObject>)
        requires self.wf(),
        ensures
            match object {
                Some(value) => self@.objects.contains_key(key@)
                    && value@ == self@.objects[key@],
                None => !self@.objects.contains_key(key@),
            },
    {
        match self.find(key) {
            Some(i) => {
                proof {
                    echod_kernel::store_proof::lemma_fold_distinct(
                        self.entries@, entry_key(), entry_value(),
                    );
                    assert(self.entries@[i as int].key@ == key@);
                    assert(self@.objects.contains_key(
                        entry_key()(self.entries@[i as int])));
                    assert(self@.objects[
                        entry_key()(self.entries@[i as int])]
                        == entry_value()(self.entries@[i as int]));
                    assert(self@.objects.contains_key(key@));
                    assert(self@.objects[key@]
                        == self.entries@[i as int].object@);
                }
                Some(self.entries[i].object.copy())
            }
            None => None,
        }
    }

    /// Exact conditional read.
    pub fn get_if_none_match(
        &self,
        key: &Key,
        version: u64,
    ) -> (read: ConditionalRead)
        requires self.wf(),
        ensures
            match read {
                ConditionalRead::Body(value) =>
                    self@.objects.contains_key(key@)
                    && self@.objects[key@].version != version
                    && value@ == self@.objects[key@],
                ConditionalRead::NotModified =>
                    self@.objects.contains_key(key@)
                    && self@.objects[key@].version == version,
                ConditionalRead::Absent =>
                    !self@.objects.contains_key(key@),
            },
    {
        match self.get(key) {
            Some(object) => {
                if object.version == version {
                    ConditionalRead::NotModified
                } else {
                    ConditionalRead::Body(object)
                }
            }
            None => ConditionalRead::Absent,
        }
    }

    /// Conditional create (`If-None-Match: *`).
    pub fn create(
        &mut self,
        key: Key,
        bytes: Vec<u8>,
    ) -> (response: Response)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
            match response {
                Response::Written(version) => {
                    &&& !old(self)@.objects.contains_key(key@)
                    &&& old(self)@.next_version < u64::MAX
                    &&& version == old(self)@.next_version
                    &&& final(self)@.objects == old(self)@.objects.insert(
                        key@, ARawObject { bytes: bytes@, version })
                    &&& final(self)@.keys == old(self)@.keys.push(key@)
                    &&& final(self)@.next_version
                        == old(self)@.next_version + 1
                },
                Response::Failed(Failure::Refused) =>
                    old(self)@.objects.contains_key(key@)
                    && same_raw_state(final(self)@, old(self)@),
                Response::Failed(Failure::Unavailable) =>
                    !old(self)@.objects.contains_key(key@)
                    && old(self)@.next_version == u64::MAX
                    && same_raw_state(final(self)@, old(self)@),
                _ => false,
            },
    {
        match self.find(&key) {
            Some(i) => {
                proof {
                    lemma_fold_dom(
                        self.entries@, entry_key(), entry_value(),
                    );
                    assert(entry_key()(self.entries@[i as int]) == key@);
                    assert(mentions(self.entries@, entry_key(), key@));
                }
                return Response::Failed(Failure::Refused);
            }
            None => {},
        }
        if self.next_version == u64::MAX {
            return Response::Failed(Failure::Unavailable);
        }
        let version = self.next_version;
        self.next_version += 1;
        let entry = Entry { key, object: RawObject { bytes, version } };
        self.push(entry);
        Response::Written(version)
    }

    /// Conditional replacement (`If-Match`).
    pub fn update(
        &mut self,
        key: Key,
        expected: u64,
        bytes: Vec<u8>,
    ) -> (response: Response)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
            match response {
                Response::Written(version) => {
                    &&& old(self)@.objects.contains_key(key@)
                    &&& old(self)@.objects[key@].version == expected
                    &&& old(self)@.next_version < u64::MAX
                    &&& version == old(self)@.next_version
                    &&& final(self)@.objects == old(self)@.objects.insert(
                        key@, ARawObject { bytes: bytes@, version })
                    &&& final(self)@.keys == old(self)@.keys
                    &&& final(self)@.next_version
                        == old(self)@.next_version + 1
                },
                Response::Failed(Failure::Refused) => {
                    &&& (!old(self)@.objects.contains_key(key@)
                        || old(self)@.objects[key@].version != expected)
                    &&& same_raw_state(final(self)@, old(self)@)
                },
                Response::Failed(Failure::Unavailable) => {
                    &&& old(self)@.objects.contains_key(key@)
                    &&& old(self)@.objects[key@].version == expected
                    &&& old(self)@.next_version == u64::MAX
                    &&& same_raw_state(final(self)@, old(self)@)
                },
                _ => false,
            },
    {
        let i = match self.find(&key) {
            Some(i) => i,
            None => return Response::Failed(Failure::Refused),
        };
        proof {
            echod_kernel::store_proof::lemma_fold_distinct(
                self.entries@, entry_key(), entry_value(),
            );
            assert(self.entries@[i as int].key@ == key@);
            assert(self@.objects.contains_key(
                entry_key()(self.entries@[i as int])));
            assert(self@.objects[entry_key()(self.entries@[i as int])]
                == entry_value()(self.entries@[i as int]));
            assert(self@.objects.contains_key(key@));
            assert(self@.objects[key@] == self.entries@[i as int].object@);
        }
        if self.entries[i].object.version != expected {
            return Response::Failed(Failure::Refused);
        }
        if self.next_version == u64::MAX {
            return Response::Failed(Failure::Unavailable);
        }
        let version = self.next_version;
        self.next_version += 1;
        self.replace(i, RawObject { bytes, version });
        Response::Written(version)
    }

    /// Conditional append. Both version and byte offset must match.
    pub fn append(
        &mut self,
        key: Key,
        expected: u64,
        offset: u64,
        suffix: Vec<u8>,
    ) -> (response: Response)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
            match response {
                Response::Written(version) => {
                    &&& old(self)@.objects.contains_key(key@)
                    &&& old(self)@.objects[key@].version == expected
                    &&& old(self)@.objects[key@].bytes.len() == offset
                    &&& old(self)@.next_version < u64::MAX
                    &&& version == old(self)@.next_version
                    &&& final(self)@.objects == old(self)@.objects.insert(
                        key@,
                        ARawObject {
                            bytes: old(self)@.objects[key@].bytes + suffix@,
                            version,
                        })
                    &&& final(self)@.keys == old(self)@.keys
                    &&& final(self)@.next_version
                        == old(self)@.next_version + 1
                },
                Response::Failed(Failure::Refused) => {
                    &&& (!old(self)@.objects.contains_key(key@)
                        || old(self)@.objects[key@].version != expected
                        || old(self)@.objects[key@].bytes.len() != offset)
                    &&& same_raw_state(final(self)@, old(self)@)
                },
                Response::Failed(Failure::Unavailable) => {
                    &&& old(self)@.objects.contains_key(key@)
                    &&& old(self)@.objects[key@].version == expected
                    &&& old(self)@.objects[key@].bytes.len() == offset
                    &&& old(self)@.next_version == u64::MAX
                    &&& same_raw_state(final(self)@, old(self)@)
                },
                _ => false,
            },
    {
        let i = match self.find(&key) {
            Some(i) => i,
            None => return Response::Failed(Failure::Refused),
        };
        proof {
            echod_kernel::store_proof::lemma_fold_distinct(
                self.entries@, entry_key(), entry_value(),
            );
            assert(self.entries@[i as int].key@ == key@);
            assert(self@.objects.contains_key(
                entry_key()(self.entries@[i as int])));
            assert(self@.objects[entry_key()(self.entries@[i as int])]
                == entry_value()(self.entries@[i as int]));
            assert(self@.objects.contains_key(key@));
            assert(self@.objects[key@] == self.entries@[i as int].object@);
        }
        if self.entries[i].object.version != expected
            || self.entries[i].object.bytes.len() as u64 != offset
        {
            return Response::Failed(Failure::Refused);
        }
        if self.next_version == u64::MAX {
            return Response::Failed(Failure::Unavailable);
        }
        let bytes = append_bytes(&self.entries[i].object.bytes, &suffix);
        let version = self.next_version;
        self.next_version += 1;
        self.replace(i, RawObject { bytes, version });
        Response::Written(version)
    }

    /// Unconditional replacement or creation.
    pub fn put(&mut self, key: Key, bytes: Vec<u8>) -> (response: Response)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
            match response {
                Response::Done => {
                    &&& old(self)@.next_version < u64::MAX
                    &&& final(self)@.objects == old(self)@.objects.insert(
                        key@,
                        ARawObject {
                            bytes: bytes@,
                            version: old(self)@.next_version,
                        })
                    &&& final(self)@.keys == if old(self)@.objects.contains_key(key@) {
                        old(self)@.keys
                    } else {
                        old(self)@.keys.push(key@)
                    }
                    &&& final(self)@.next_version
                        == old(self)@.next_version + 1
                },
                Response::Failed(Failure::Unavailable) =>
                    old(self)@.next_version == u64::MAX
                    && same_raw_state(final(self)@, old(self)@),
                _ => false,
            },
    {
        if self.next_version == u64::MAX {
            return Response::Failed(Failure::Unavailable);
        }
        let found = self.find(&key);
        let ghost before_objects = self@.objects;
        let ghost before_keys = self@.keys;
        let ghost key_view = key@;
        let ghost bytes_view = bytes@;
        let version = self.next_version;
        self.next_version += 1;
        let object = RawObject { bytes, version };
        match found {
            Some(i) => {
                proof {
                    lemma_fold_distinct(
                        self.entries@, entry_key(), entry_value(),
                    );
                    assert(self.entries@[i as int].key@ == key_view);
                    assert(self@.objects.contains_key(
                        entry_key()(self.entries@[i as int])));
                    assert(before_objects.contains_key(key_view));
                }
                self.replace(i, object);
                proof {
                    assert(self@.objects == before_objects.insert(
                        key_view,
                        ARawObject { bytes: bytes_view, version },
                    ));
                    assert(self@.keys == before_keys);
                }
            }
            None => {
                self.push(Entry { key, object });
                proof {
                    assert(self@.objects == before_objects.insert(
                        key_view,
                        ARawObject { bytes: bytes_view, version },
                    ));
                    assert(self@.keys == before_keys.push(key_view));
                }
            }
        }
        Response::Done
    }

    /// Unconditional, idempotent deletion.
    pub fn delete(&mut self, key: &Key) -> (response: Response)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
            response is Done,
            final(self)@.objects == old(self)@.objects.remove(key@),
            final(self)@.next_version == old(self)@.next_version,
    {
        match self.find(key) {
            Some(i) => {
                proof {
                    assert(self@.keys[i as int] == key@);
                }
                self.remove(i);
            }
            None => {
                proof {
                    assert(!self@.keys.contains(key@)) by {
                        if self@.keys.contains(key@) {
                            let i = choose|i: int| 0 <= i < self@.keys.len()
                                && self@.keys[i] == key@;
                            assert(entry_key()(self.entries@[i]) == key@);
                            assert(mentions(self.entries@, entry_key(), key@));
                            lemma_fold_dom(
                                self.entries@, entry_key(), entry_value(),
                            );
                        }
                    }
                }
            }
        }
        Response::Done
    }
}

impl Operation {
    pub fn is_mutation(&self) -> bool {
        match self {
            Operation::Create { .. }
            | Operation::Update { .. }
            | Operation::Append { .. }
            | Operation::Put { .. }
            | Operation::Delete { .. } => true,
            Operation::Get { .. }
            | Operation::GetIfNoneMatch { .. }
            | Operation::List { .. }
            | Operation::ListPrefixes { .. } => false,
        }
    }
}

impl RawStore {
    fn can_refuse(&self, operation: &Operation) -> bool
        requires self.wf(),
    {
        match operation {
            Operation::Create { key, .. } => self.find(key).is_some(),
            Operation::Update { key, version, .. } => {
                match self.find(key) {
                    Some(i) => self.entries[i].object.version != *version,
                    None => true,
                }
            }
            Operation::Append { key, version, offset, .. } => {
                match self.find(key) {
                    Some(i) => self.entries[i].object.version != *version
                        || self.entries[i].object.bytes.len() as u64 != *offset,
                    None => true,
                }
            }
            _ => false,
        }
    }

    /// Execute an operation under ordinary store behavior.
    pub fn execute_normal(&mut self, operation: Operation) -> (response: Response)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
    {
        match operation {
            Operation::Get { key } =>
                Response::Got(self.get(&key)),
            Operation::GetIfNoneMatch { key, version } =>
                Response::Read(self.get_if_none_match(&key, version)),
            Operation::Create { key, bytes } =>
                self.create(key, bytes),
            Operation::Update { key, version, bytes } =>
                self.update(key, version, bytes),
            Operation::Append { key, version, offset, bytes } =>
                self.append(key, version, offset, bytes),
            Operation::Put { key, bytes } =>
                self.put(key, bytes),
            Operation::Delete { key } =>
                self.delete(&key),
            Operation::List { prefix, max_keys } =>
                Response::Listed(self.list(&prefix, max_keys)),
            Operation::ListPrefixes { prefix } =>
                Response::Listed(self.list_prefixes(&prefix)),
        }
    }

    /// One deterministic automaton step. `InvalidChoice` means the selected
    /// environmental event is impossible for this operation/state pair.
    pub fn execute(
        &mut self,
        operation: Operation,
        environment: Environment,
    ) -> (response: Response)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@.bucket == old(self)@.bucket,
            environment == Environment::FailBeforeApply
                ==> same_raw_state(final(self)@, old(self)@)
                    && response is Failed
                    && response->Failed_0 == Failure::Unavailable,
            environment == Environment::Refused
                ==> same_raw_state(final(self)@, old(self)@)
                    && (response is InvalidChoice
                        || (response is Failed
                            && response->Failed_0 == Failure::Refused)),
    {
        match environment {
            Environment::Normal => self.execute_normal(operation),
            Environment::FailBeforeApply =>
                Response::Failed(Failure::Unavailable),
            Environment::Refused => {
                if self.can_refuse(&operation) {
                    Response::Failed(Failure::Refused)
                } else {
                    Response::InvalidChoice
                }
            }
            Environment::ApplyButLostAck => {
                if !operation.is_mutation() {
                    return Response::InvalidChoice;
                }
                let response = self.execute_normal(operation);
                match response {
                    Response::Written(_) | Response::Done =>
                        Response::Failed(Failure::Unavailable),
                    _ => Response::InvalidChoice,
                }
            }
        }
    }
}

} // verus!
