//! The store: the protocol the concrete Rover model speaks, and the store
//! that answers it.
//!
//! One definition of the calls. The process re-exports these types and sends
//! them as `Effect::Store`. `Store::apply` applies one call; `spec_apply` is
//! that step as a specification, and Verus checks that `apply` computes it.
//! Trusted here: `content_etag` computes `spec_etag`, and a string is its
//! characters (`chars_of`, `string_of`).

use vstd::pervasive::VecAdditionalExecFns;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::model::{spec_bytes, spec_string};
use crate::model::Pid;

verus! {

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Etag(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreError {
    /// A conditional write found the object at another version.
    PreconditionFailed,
    /// The store did not answer, or answered with an error: the effect of
    /// a write is unknown.
    Unavailable(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Read {
    Body(Vec<u8>, Etag),
    NotModified,
    Absent,
}

/// A call on the store, as the executor makes it.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreCall {
    Get { key: String },
    GetIfNoneMatch { key: String, etag: Etag },
    PutIfMatch { key: String, body: Vec<u8>, etag: Etag },
    PutIfNoneMatch { key: String, body: Vec<u8> },
    AppendIfMatch { key: String, offset: u64, body: Vec<u8>, etag: Etag },
    Put { key: String, body: Vec<u8> },
    Delete { key: String },
    List { prefix: String, max_keys: usize },
    ListPrefixes { prefix: String },
}

impl StoreCall {
    #[verifier::external_body]
    pub fn key(&self) -> &str {
        match self {
            StoreCall::Get { key }
            | StoreCall::GetIfNoneMatch { key, .. }
            | StoreCall::PutIfMatch { key, .. }
            | StoreCall::PutIfNoneMatch { key, .. }
            | StoreCall::AppendIfMatch { key, .. }
            | StoreCall::Put { key, .. }
            | StoreCall::Delete { key } => key,
            StoreCall::List { prefix, .. } | StoreCall::ListPrefixes { prefix } => prefix,
        }
    }
}

/// What a store call answered.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreOutcome {
    /// `Get`: the object and its version, or nothing.
    Got(Option<(Vec<u8>, Etag)>),
    /// `GetIfNoneMatch`.
    Read(Read),
    /// A conditional write landed at this version.
    Written(Etag),
    /// `Put` or `Delete` landed.
    Done,
    /// `List` or `ListPrefixes`.
    Listed(Vec<String>),
    Failed(StoreError),
}

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

pub struct EntryV {
    pub key: Seq<char>,
    pub body: Seq<u8>,
    pub version: nat,
}

pub struct StoreV {
    pub entries: Seq<EntryV>,
    pub appendable: bool,
    /// The `(node, op)` pairs the store has answered. A second delivery of
    /// one is a stutter.
    pub seen: Seq<(Pid, u64)>,
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

// ---------------------------------------------------------------------------
// The store, as a specification
// ---------------------------------------------------------------------------

pub open spec fn spec_wrap_mul(a: u64, b: u64) -> u64 {
    (((a as nat) * (b as nat)) % 0x10000000000000000) as u64
}

pub open spec fn spec_fnv_acc(bytes: Seq<u8>, h: u64) -> u64
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        h
    } else {
        let mixed = h ^ (bytes[0] as u64);
        spec_fnv_acc(bytes.drop_first(), spec_wrap_mul(mixed, 0x00000100000001b3))
    }
}

pub open spec fn spec_utf8(chars: Seq<char>) -> Seq<u8>
    decreases chars.len(),
{
    if chars.len() == 0 {
        Seq::empty()
    } else {
        let c = chars[0] as u64;
        let head = if c < 0x80 {
            seq![c as u8]
        } else if c < 0x800 {
            seq![((c >> 6) | 0xc0) as u8, ((c & 0x3f) | 0x80) as u8]
        } else if c < 0x10000 {
            seq![((c >> 12) | 0xe0) as u8, (((c >> 6) & 0x3f) | 0x80) as u8, ((c & 0x3f) | 0x80) as u8]
        } else {
            seq![
                ((c >> 18) | 0xf0) as u8,
                (((c >> 12) & 0x3f) | 0x80) as u8,
                (((c >> 6) & 0x3f) | 0x80) as u8,
                ((c & 0x3f) | 0x80) as u8,
            ]
        };
        head + spec_utf8(chars.drop_first())
    }
}

pub open spec fn spec_fnv(chars: Seq<char>) -> u64 {
    spec_fnv_acc(spec_utf8(chars), 0xcbf29ce484222325)
}

pub open spec fn spec_hex_digit(n: u64) -> char {
    if n == 0 { '0' }
    else if n == 1 { '1' }
    else if n == 2 { '2' }
    else if n == 3 { '3' }
    else if n == 4 { '4' }
    else if n == 5 { '5' }
    else if n == 6 { '6' }
    else if n == 7 { '7' }
    else if n == 8 { '8' }
    else if n == 9 { '9' }
    else if n == 10 { 'a' }
    else if n == 11 { 'b' }
    else if n == 12 { 'c' }
    else if n == 13 { 'd' }
    else if n == 14 { 'e' }
    else { 'f' }
}

pub open spec fn spec_hex_from(n: u64, shift: int) -> Seq<char>
    decreases shift,
{
    let d = (n >> (shift * 4)) & 0xf;
    if shift <= 0 {
        seq![spec_hex_digit(d)]
    } else {
        seq![spec_hex_digit(d)] + spec_hex_from(n, shift - 1)
    }
}

/// `content_etag`: FNV-1a of the lossy UTF-8 view of the body, as sixteen hex digits.
pub open spec fn spec_etag_chars(body: Seq<u8>) -> Seq<char> {
    spec_hex_from(spec_fnv_acc(spec_lossy(body), 0xcbf29ce484222325), 15)
}

pub open spec fn spec_cont(b: u8) -> bool {
    b >= 0x80 && b < 0xc0
}

pub open spec fn spec_utf8_width(lead: u8) -> nat {
    if lead < 0x80 {
        1
    } else if lead >= 0xc2 && lead <= 0xdf {
        2
    } else if lead >= 0xe0 && lead <= 0xef {
        3
    } else if lead >= 0xf0 && lead <= 0xf4 {
        4
    } else {
        0
    }
}

pub open spec fn spec_utf8_ok(lead: u8, pos: nat, b: u8) -> bool {
    if pos == 0 {
        true
    } else if pos == 1 {
        if lead >= 0xc2 && lead <= 0xdf {
            spec_cont(b)
        } else if lead == 0xe0 {
            b >= 0xa0 && b <= 0xbf
        } else if (lead >= 0xe1 && lead <= 0xec) || (lead >= 0xee && lead <= 0xef) {
            spec_cont(b)
        } else if lead == 0xed {
            b >= 0x80 && b <= 0x9f
        } else if lead == 0xf0 {
            b >= 0x90 && b <= 0xbf
        } else if lead >= 0xf1 && lead <= 0xf3 {
            spec_cont(b)
        } else if lead == 0xf4 {
            b >= 0x80 && b <= 0x8f
        } else {
            false
        }
    } else {
        spec_cont(b)
    }
}

/// `spec_prefix` stays within the bytes it reads.
pub proof fn lemma_prefix_bounds(bytes: Seq<u8>, width: nat, pos: nat)
    requires
        pos <= bytes.len(),
        pos <= width,
    ensures
        pos <= spec_prefix(bytes, width, pos) <= bytes.len(),
    decreases width - pos,
{
    if pos >= width {
    } else if pos >= bytes.len() || !spec_utf8_ok(bytes[0], pos, bytes[pos as int]) {
    } else {
        lemma_prefix_bounds(bytes, width, pos + 1);
    }
}

#[via_fn]
proof fn spec_lossy_decreases(bytes: Seq<u8>) {
    if bytes.len() > 0 {
        let width = spec_utf8_width(bytes[0]);
        if width >= 2 {
            lemma_prefix_bounds(bytes, width, 1);
        }
    }
}

/// How many leading bytes form one UTF-8 character, or the maximal subpart
/// of one ill-formed sequence. The same split `String::from_utf8_lossy` uses.
pub open spec fn spec_prefix(bytes: Seq<u8>, width: nat, pos: nat) -> nat
    decreases width - pos,
{
    if pos >= width {
        width
    } else if pos >= bytes.len() || !spec_utf8_ok(bytes[0], pos, bytes[pos as int]) {
        pos
    } else {
        spec_prefix(bytes, width, pos + 1)
    }
}

pub open spec fn spec_lossy(bytes: Seq<u8>) -> Seq<u8>
    decreases bytes.len(),
    via spec_lossy_decreases
{
    if bytes.len() == 0 {
        Seq::empty()
    } else {
        let width = spec_utf8_width(bytes[0]);
        if width == 1 {
            seq![bytes[0]] + spec_lossy(bytes.skip(1))
        } else if width == 0 {
            seq![0xefu8, 0xbfu8, 0xbdu8] + spec_lossy(bytes.skip(1))
        } else {
            let prefix = spec_prefix(bytes, width, 1);
            if prefix == width {
                bytes.take(width as int) + spec_lossy(bytes.skip(width as int))
            } else {
                seq![0xefu8, 0xbfu8, 0xbdu8] + spec_lossy(bytes.skip(prefix as int))
            }
        }
    }
}

pub open spec fn spec_sat_add(a: u64, b: u64) -> u64 {
    if (a as nat) + (b as nat) > (u64::MAX as nat) {
        u64::MAX
    } else {
        ((a as nat) + (b as nat)) as u64
    }
}

pub open spec fn spec_etag(body: Seq<u8>) -> Etag {
    Etag(spec_string(spec_etag_chars(body)))
}

pub open spec fn spec_find(entries: Seq<EntryV>, key: Seq<char>, i: int) -> Option<int>
    decreases entries.len() - i,
{
    if i < 0 || i >= entries.len() {
        None
    } else if entries[i].key == key {
        Some(i)
    } else {
        spec_find(entries, key, i + 1)
    }
}

pub open spec fn spec_insert_at(entries: Seq<EntryV>, entry: EntryV, i: int) -> Seq<EntryV>
    decreases entries.len() - i,
{
    if i >= entries.len() {
        entries.push(entry)
    } else if spec_before(entry.key, entries[i].key) {
        entries.take(i).push(entry) + entries.skip(i)
    } else {
        spec_insert_at(entries, entry, i + 1)
    }
}

pub open spec fn spec_before(a: Seq<char>, b: Seq<char>) -> bool
    decreases a.len() + b.len(),
{
    if a.len() == 0 { b.len() != 0 }
    else if b.len() == 0 { false }
    else if a[0] != b[0] { a[0] < b[0] }
    else { spec_before(a.drop_first(), b.drop_first()) }
}

pub open spec fn spec_put(entries: Seq<EntryV>, entry: EntryV) -> Seq<EntryV> {
    match spec_find(entries, entry.key, 0) {
        Some(i) => entries.update(i, entry),
        None => spec_insert_at(entries, entry, 0),
    }
}

pub open spec fn spec_remove_at(entries: Seq<EntryV>, i: int) -> Seq<EntryV> {
    entries.take(i) + entries.skip(i + 1)
}

/// The next version. A `u64` counter stops at its top.
pub open spec fn spec_bump(version: nat) -> nat {
    if version < u64::MAX as nat { version + 1 } else { version }
}

/// One store call. The same cases as `Store::apply`.
pub open spec fn spec_apply(store: StoreV, call: StoreCall) -> (StoreV, StoreOutcome) {
    match call {
        StoreCall::Get { key } => {
            match spec_find(store.entries, key@, 0) {
                None => (store, StoreOutcome::Got(None)),
                Some(i) => {
                    let body = store.entries[i].body;
                    (store, StoreOutcome::Got(Some((spec_bytes(body), spec_etag(body)))))
                },
            }
        },
        StoreCall::GetIfNoneMatch { key, etag } => {
            match spec_find(store.entries, key@, 0) {
                None => (store, StoreOutcome::Read(Read::Absent)),
                Some(i) => {
                    let body = store.entries[i].body;
                    let have = spec_etag(body);
                    if have == etag {
                        (store, StoreOutcome::Read(Read::NotModified))
                    } else {
                        (store, StoreOutcome::Read(Read::Body(spec_bytes(body), have)))
                    }
                },
            }
        },
        StoreCall::PutIfNoneMatch { key, body } => {
            if spec_find(store.entries, key@, 0) is Some {
                (store, StoreOutcome::Failed(StoreError::PreconditionFailed))
            } else {
                let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version: 1 });
                (StoreV { entries, ..store }, StoreOutcome::Written(spec_etag(body@)))
            }
        },
        StoreCall::PutIfMatch { key, body, etag } => {
            match spec_find(store.entries, key@, 0) {
                Some(i) if spec_etag(store.entries[i].body) == etag => {
                    let version = spec_bump(store.entries[i].version);
                    let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version });
                    (StoreV { entries, ..store }, StoreOutcome::Written(spec_etag(body@)))
                },
                _ => (store, StoreOutcome::Failed(StoreError::PreconditionFailed)),
            }
        },
        StoreCall::AppendIfMatch { key, offset, body, etag } => {
            if !store.appendable {
                (store, StoreOutcome::Failed(StoreError::Unavailable(spec_string(seq![
                    't', 'h', 'i', 's', ' ', 's', 't', 'o', 'r', 'e', ' ', 'd', 'o', 'e', 's', ' ',
                    'n', 'o', 't', ' ', 'a', 'p', 'p', 'e', 'n', 'd',
                ]))))
            } else {
                match spec_find(store.entries, key@, 0) {
                    Some(i) if spec_etag(store.entries[i].body) == etag && store.entries[i].body.len() == offset => {
                        let joined = store.entries[i].body + body@;
                        let version = spec_bump(store.entries[i].version);
                        let entries = spec_put(store.entries, EntryV { key: key@, body: joined, version });
                        (StoreV { entries, ..store }, StoreOutcome::Written(spec_etag(joined)))
                    },
                    _ => (store, StoreOutcome::Failed(StoreError::PreconditionFailed)),
                }
            }
        },
        StoreCall::Put { key, body } => {
            let version = match spec_find(store.entries, key@, 0) {
                Some(i) => spec_bump(store.entries[i].version),
                None => 1,
            };
            let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version });
            (StoreV { entries, ..store }, StoreOutcome::Done)
        },
        StoreCall::Delete { key } => {
            match spec_find(store.entries, key@, 0) {
                Some(i) => (StoreV { entries: spec_remove_at(store.entries, i), ..store }, StoreOutcome::Done),
                None => (store, StoreOutcome::Done),
            }
        },
        StoreCall::List { prefix, max_keys } => {
            (store, StoreOutcome::Listed(spec_bytes_keys(spec_list(store.entries, prefix@, max_keys as nat, 0, Seq::empty()))))
        },
        StoreCall::ListPrefixes { prefix } => {
            (store, StoreOutcome::Listed(spec_bytes_keys(spec_prefixes(store.entries, prefix@, 0, Seq::empty()))))
        },
    }
}

pub open spec fn spec_list(entries: Seq<EntryV>, prefix: Seq<char>, max: nat, i: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases entries.len() - i,
{
    if i < 0 || i >= entries.len() || acc.len() >= max {
        acc
    } else if spec_starts(entries[i].key, prefix) {
        spec_list(entries, prefix, max, i + 1, acc.push(entries[i].key))
    } else {
        spec_list(entries, prefix, max, i + 1, acc)
    }
}

pub open spec fn spec_starts(text: Seq<char>, prefix: Seq<char>) -> bool
    decreases prefix.len(),
{
    if prefix.len() == 0 { true }
    else if text.len() == 0 { false }
    else { text[0] == prefix[0] && spec_starts(text.drop_first(), prefix.drop_first()) }
}

pub open spec fn spec_prefixes(entries: Seq<EntryV>, prefix: Seq<char>, i: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases entries.len() - i,
{
    if i < 0 || i >= entries.len() {
        acc
    } else if spec_starts(entries[i].key, prefix) {
        let tail = entries[i].key.skip(prefix.len() as int);
        match spec_slash(tail, 0) {
            Some(n) => {
                let child = entries[i].key.take(prefix.len() + n + 1);
                let acc = if acc.len() > 0 && acc.last() == child { acc } else { acc.push(child) };
                spec_prefixes(entries, prefix, i + 1, acc)
            },
            None => spec_prefixes(entries, prefix, i + 1, acc),
        }
    } else {
        spec_prefixes(entries, prefix, i + 1, acc)
    }
}

pub open spec fn spec_slash(text: Seq<char>, i: int) -> Option<int>
    decreases text.len() - i,
{
    if i < 0 || i >= text.len() { None }
    else if text[i] == '/' { Some(i) }
    else { spec_slash(text, i + 1) }
}

pub open spec fn spec_bytes_keys(keys: Seq<Seq<char>>) -> Vec<String> {
    choose|v: Vec<String>| v@.map_values(|s: String| s@) == keys
}

// ---------------------------------------------------------------------------
// The store, executed: each function computes its specification above
// ---------------------------------------------------------------------------

/// The content hash the in-memory store quotes: `content_etag`.
pub fn etag(body: &Vec<u8>) -> (r: Etag)
    ensures
        r == spec_etag(body@),
{
    content_etag(body.as_slice())
}

/// A string's characters. Trusted: the view of a `String` is its characters.
#[verifier::external_body]
fn chars_of(text: &String) -> (r: Vec<char>)
    ensures
        r@ == text@,
{
    text.chars().collect()
}

/// The string of some characters. Trusted, as `chars_of`.
#[verifier::external_body]
fn string_of(chars: &Vec<char>) -> (r: String)
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
        echod_abstract::trusted::axiom_vec_ext(r.body, e.body);
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
fn before(a: &String, b: &String) -> (r: bool)
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
        echod_abstract::trusted::axiom_string_ext(w@[i], v@[i]);
    }
    assert(w@ =~= v@);
    echod_abstract::trusted::axiom_vec_ext(w, v);
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
            echod_abstract::trusted::axiom_vec_ext(r.entries, self.entries);
            echod_abstract::trusted::axiom_vec_ext(r.seen, self.seen);
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
                        crate::simulation::lemma_bytes(entry.body@);
                        echod_abstract::trusted::axiom_vec_ext(body, spec_bytes(entry.body@));
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
                            echod_abstract::trusted::axiom_string_ext(have.0, want.0);
                        }
                        StoreOutcome::Read(Read::NotModified)
                    } else {
                        let body = copy_bytes(&entry.body);
                        proof {
                            crate::simulation::lemma_bytes(entry.body@);
                            echod_abstract::trusted::axiom_vec_ext(body, spec_bytes(entry.body@));
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
                            echod_abstract::trusted::axiom_string_ext(have.0, want.0);
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
                        crate::interpret::lemma_string_of(text);
                    }
                    StoreOutcome::Failed(StoreError::Unavailable(text))
                } else {
                    match find_entry(&self.entries, key) {
                        Some(i) => {
                            let have = etag(&self.entries[i].body);
                            if have.0 == want.0 && self.entries[i].body.len() as u64 == *offset {
                                proof {
                                    echod_abstract::trusted::axiom_string_ext(have.0, want.0);
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

#[cfg(not(verus_keep_ghost))]
impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StoreError::PreconditionFailed => f.write_str("precondition failed"),
            StoreError::Unavailable(m) => write!(f, "store unavailable: {m}"),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl std::error::Error for StoreError {}
