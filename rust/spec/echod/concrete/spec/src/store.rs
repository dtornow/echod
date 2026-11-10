//! Passive store protocol and mathematical store algebra.
//!
//! The executable in-memory realization lives in `echod-process::concrete`.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::model::{spec_bytes, spec_string};
use crate::model::Pid;

verus! {


#[make_spec_type]
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

// ---------------------------------------------------------------------------
// The calls and outcomes as views: strings as their characters
// ---------------------------------------------------------------------------

pub ghost enum StoreErrorSpec {
    PreconditionFailed,
    Unavailable(Seq<char>),
}

impl DeepView for StoreError {
    type V = StoreErrorSpec;
    open spec fn deep_view(&self) -> StoreErrorSpec {
        match self {
            StoreError::PreconditionFailed => StoreErrorSpec::PreconditionFailed,
            StoreError::Unavailable(m) => StoreErrorSpec::Unavailable(m@),
        }
    }
}

#[cfg(verus_keep_ghost)]
pub ghost enum ReadSpec {
    Body(Seq<u8>, EtagSpec),
    NotModified,
    Absent,
}

#[cfg(verus_keep_ghost)]
impl DeepView for Read {
    type V = ReadSpec;
    open spec fn deep_view(&self) -> ReadSpec {
        match self {
            Read::Body(b, e) => ReadSpec::Body(b@, e.deep_view()),
            Read::NotModified => ReadSpec::NotModified,
            Read::Absent => ReadSpec::Absent,
        }
    }
}

#[cfg(verus_keep_ghost)]
pub ghost enum StoreCallSpec {
    Get { key: Seq<char> },
    GetIfNoneMatch { key: Seq<char>, etag: EtagSpec },
    PutIfMatch { key: Seq<char>, body: Seq<u8>, etag: EtagSpec },
    PutIfNoneMatch { key: Seq<char>, body: Seq<u8> },
    AppendIfMatch { key: Seq<char>, offset: u64, body: Seq<u8>, etag: EtagSpec },
    Put { key: Seq<char>, body: Seq<u8> },
    Delete { key: Seq<char> },
    List { prefix: Seq<char>, max_keys: usize },
    ListPrefixes { prefix: Seq<char> },
}

#[cfg(verus_keep_ghost)]
impl DeepView for StoreCall {
    type V = StoreCallSpec;
    open spec fn deep_view(&self) -> StoreCallSpec {
        match self {
            StoreCall::Get { key } => StoreCallSpec::Get { key: key@ },
            StoreCall::GetIfNoneMatch { key, etag } => StoreCallSpec::GetIfNoneMatch { key: key@, etag: etag.deep_view() },
            StoreCall::PutIfMatch { key, body, etag } => StoreCallSpec::PutIfMatch { key: key@, body: body@, etag: etag.deep_view() },
            StoreCall::PutIfNoneMatch { key, body } => StoreCallSpec::PutIfNoneMatch { key: key@, body: body@ },
            StoreCall::AppendIfMatch { key, offset, body, etag } => StoreCallSpec::AppendIfMatch { key: key@, offset: *offset, body: body@, etag: etag.deep_view() },
            StoreCall::Put { key, body } => StoreCallSpec::Put { key: key@, body: body@ },
            StoreCall::Delete { key } => StoreCallSpec::Delete { key: key@ },
            StoreCall::List { prefix, max_keys } => StoreCallSpec::List { prefix: prefix@, max_keys: *max_keys },
            StoreCall::ListPrefixes { prefix } => StoreCallSpec::ListPrefixes { prefix: prefix@ },
        }
    }
}

/// A store's answer is a value a process takes as it is: its deep view is
/// itself.
impl DeepView for StoreOutcome {
    type V = StoreOutcome;
    open spec fn deep_view(&self) -> StoreOutcome {
        *self
    }
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
