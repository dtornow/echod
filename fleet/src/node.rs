//! The node core: the state a node keeps about the membership and its cache,
//! and the decisions it takes from it, as executable Rust with its
//! specification, in Anvil's shape.
//!
//! Every function here is a pure step: it reads and updates this state and
//! nothing else, and its `ensures` says it computes the specification's
//! function of the same name on the state's view. The fleet model
//! (`cluster.rs`) defines a node's actions *as* those specification
//! functions, so the theorem proved there is about the node this code is.
//! What stays outside, trusted: the shim that calls these functions in the
//! right order against the real bucket, and the bucket itself.

use vstd::hash_map::StringHashMap;
use vstd::prelude::*;

// `str == str` and `String::clone` are the kernel's trusted primitives.
pub use echod_kernel::types::{clone_string, str_eq};

verus! {

pub type Id = Seq<char>;
pub type Origin = Seq<char>;

/// The hash a load balancer and every node agree on. Any function will do;
/// what matters is that every node computes the same one.
pub uninterp spec fn hash(o: Origin) -> nat;

/// FNV-1a over the bytes. Trusted to be a function of the string.
#[verifier::external_body]
pub fn fnv1a(s: &str) -> (r: u64)
    ensures r as nat == hash(s@),
{
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

// ---------------------------------------------------------------------------
// The state and its view
// ---------------------------------------------------------------------------

/// A deadline key in the bucket: what is due for which origin, and a token
/// drawn per arm, so no two arms name one key.
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Key {
    pub origin: String,
    pub at: u64,
    pub token: u64,
}

pub struct AKey {
    pub origin: Origin,
    pub at: nat,
    pub token: nat,
}

impl View for Key {
    type V = AKey;
    open spec fn view(&self) -> AKey {
        AKey { origin: self.origin@, at: self.at as nat, token: self.token as nat }
    }
}

pub open spec fn opt_key(o: Option<Key>) -> Option<AKey> {
    match o {
        Some(k) => Some(k@),
        None => None,
    }
}

pub fn key_eq(a: &Key, b: &Key) -> (r: bool)
    ensures r == (a@ == b@),
{
    str_eq(a.origin.as_str(), b.origin.as_str()) && a.at == b.at && a.token == b.token
}

pub fn clone_key(k: &Key) -> (r: Key)
    ensures r@ == k@,
{
    Key { origin: clone_string(&k.origin), at: k.at, token: k.token }
}

/// The key a node remembers for an origin, and the version of the document
/// it wrote with it. The key is relied on only while the document is still
/// that version: any later write, by anyone, may have replaced the key.
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug))]
pub struct Armed {
    pub key: Key,
    pub etag: String,
}

pub struct AArmed {
    pub key: AKey,
    pub etag: Seq<char>,
}

impl View for Armed {
    type V = AArmed;
    open spec fn view(&self) -> AArmed {
        AArmed { key: self.key@, etag: self.etag@ }
    }
}

/// A cache entry's identity: the version, and when it was filled. The body
/// held for it is used only once a conditional read has confirmed the
/// version is the bucket's.
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug))]
pub struct Entry {
    pub etag: String,
    pub filled_at: u64,
}

pub struct AEntry {
    pub etag: Seq<char>,
    pub filled_at: nat,
}

impl View for Entry {
    type V = AEntry;
    open spec fn view(&self) -> AEntry {
        AEntry { etag: self.etag@, filled_at: self.filled_at as nat }
    }
}

pub struct NodeCore {
    pub id: String,
    pub ttl: u64,
    pub read_any: bool,
    pub epoch: u64,
    pub members: Vec<String>,
    /// The node's clock at its last read of the configuration.
    pub last_read: u64,
    pub cache: StringHashMap<Entry>,
    /// The deadline key this node last armed for each origin, with the
    /// version it wrote, so a commit on that version removes exactly that one.
    pub armed: StringHashMap<Armed>,
}

pub struct ANode {
    pub id: Id,
    pub ttl: nat,
    pub read_any: bool,
    pub epoch: nat,
    pub members: Seq<Id>,
    pub last_read: nat,
    pub cache: Map<Origin, AEntry>,
    pub armed: Map<Origin, AArmed>,
}

impl View for NodeCore {
    type V = ANode;
    open spec fn view(&self) -> ANode {
        ANode {
            id: self.id@,
            ttl: self.ttl as nat,
            read_any: self.read_any,
            epoch: self.epoch as nat,
            members: self.members.deep_view(),
            last_read: self.last_read as nat,
            cache: self.cache@.map_values(|e: Entry| e@),
            armed: self.armed@.map_values(|a: Armed| a@),
        }
    }
}

// ---------------------------------------------------------------------------
// The specification: what each decision and each step means
// ---------------------------------------------------------------------------

/// `hash(o) mod n` over the members in order.
pub open spec fn spec_owner(members: Seq<Id>, o: Origin) -> Option<Id> {
    if members.len() == 0 { None } else { Some(members[(hash(o) % members.len()) as int]) }
}

pub open spec fn spec_fresh(n: ANode, now: nat) -> bool {
    n.read_any && n.last_read + n.ttl >= now
}

/// The node acts as owner of `o`: fresh, and the owner per its members.
/// Routing: nothing the proof relies on.
pub open spec fn spec_acts(n: ANode, o: Origin, now: nat) -> bool {
    &&& spec_fresh(n, now)
    &&& spec_owner(n.members, o) == Some(n.id)
}

/// Take on the configuration read at `now`.
pub open spec fn spec_read_config(n: ANode, now: nat, epoch: nat, members: Seq<Id>) -> ANode {
    ANode {
        read_any: true,
        epoch,
        members,
        last_read: now,
        ..n
    }
}

/// Remember the version of `o` read from, or written to, the bucket at `now`.
pub open spec fn spec_filled(n: ANode, o: Origin, etag: Seq<char>, now: nat) -> ANode {
    ANode { cache: n.cache.insert(o, AEntry { etag, filled_at: now }), ..n }
}

/// Drop what is remembered of `o`.
pub open spec fn spec_forget(n: ANode, o: Origin) -> ANode {
    ANode { cache: n.cache.remove(o), ..n }
}

/// Remember the key armed for `o` and the version written with it, or that
/// none is.
pub open spec fn spec_set_armed(n: ANode, o: Origin, a: Option<AArmed>) -> ANode {
    match a {
        Some(a) => ANode { armed: n.armed.insert(o, a), ..n },
        None => ANode { armed: n.armed.remove(o), ..n },
    }
}

/// A fired key was collected: if it is the one remembered for `o`, forget it.
pub open spec fn spec_collected(n: ANode, o: Origin, k: AKey) -> ANode {
    if n.armed.contains_key(o) && n.armed[o].key == k { ANode { armed: n.armed.remove(o), ..n } } else { n }
}

pub open spec fn opt_armed(o: Option<Armed>) -> Option<AArmed> {
    match o {
        Some(a) => Some(a@),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// The executable node, step for step
// ---------------------------------------------------------------------------

impl NodeCore {
    pub fn new(id: String, ttl: u64) -> (n: NodeCore)
        ensures
            n@ == (ANode {
                id: id@, ttl: ttl as nat, read_any: false, epoch: 0,
                members: Seq::empty(), last_read: 0, cache: Map::empty(), armed: Map::empty(),
            }),
    {
        let n = NodeCore { id, ttl, read_any: false, epoch: 0, members: Vec::new(), last_read: 0, cache: StringHashMap::new(), armed: StringHashMap::new() };
        assert(n@.members =~= Seq::<Id>::empty());
        assert(n@.cache =~= Map::<Origin, AEntry>::empty());
        assert(n@.armed =~= Map::<Origin, AArmed>::empty());
        n
    }

    /// The member that owns `o`, by the members this node holds.
    pub fn owner(&self, o: &str) -> (r: Option<String>)
        ensures r.deep_view() == spec_owner(self@.members, o@),
    {
        if self.members.len() == 0 {
            None
        } else {
            let i = (fnv1a(o) % self.members.len() as u64) as usize;
            assert(i < self.members.len());
            Some(self.members[i].clone())
        }
    }

    pub fn fresh(&self, now: u64) -> (r: bool)
        ensures r == spec_fresh(self@, now as nat),
    {
        self.read_any && self.last_read as u128 + self.ttl as u128 >= now as u128
    }

    pub fn acts(&self, o: &str, now: u64) -> (r: bool)
        ensures r == spec_acts(self@, o@, now as nat),
    {
        if !self.fresh(now) {
            return false;
        }
        match self.owner(o) {
            Some(id) => str_eq(id.as_str(), self.id.as_str()),
            None => false,
        }
    }

    /// Take on the configuration read at `now`.
    pub fn read_config(&mut self, now: u64, epoch: u64, members: Vec<String>)
        ensures final(self)@ == spec_read_config(old(self)@, now as nat, epoch as nat, members.deep_view()),
    {
        self.read_any = true;
        self.epoch = epoch;
        self.members = members;
        self.last_read = now;
    }

    /// Remember the version of `o` read from, or written to, the bucket at `now`.
    pub fn filled(&mut self, o: &str, etag: String, now: u64)
        ensures final(self)@ == spec_filled(old(self)@, o@, etag@, now as nat),
    {
        let ghost before = self@;
        self.cache.insert(o.to_string(), Entry { etag, filled_at: now });
        assert(self@.cache =~= before.cache.insert(o@, AEntry { etag: etag@, filled_at: now as nat }));
    }

    /// Drop what is remembered of `o`.
    pub fn forget(&mut self, o: &str)
        ensures final(self)@ == spec_forget(old(self)@, o@),
    {
        let ghost before = self@;
        self.cache.remove(o);
        assert(self@.cache =~= before.cache.remove(o@));
    }

    /// Remember the key armed for `o` and the version written with it, or
    /// that none is.
    pub fn set_armed(&mut self, o: &str, a: Option<Armed>)
        ensures final(self)@ == spec_set_armed(old(self)@, o@, opt_armed(a)),
    {
        let ghost before = self@;
        match a {
            Some(a) => {
                let ghost aa = a@;
                self.armed.insert(o.to_string(), a);
                assert(self@.armed =~= before.armed.insert(o@, aa));
            }
            None => {
                self.armed.remove(o);
                assert(self@.armed =~= before.armed.remove(o@));
            }
        }
    }

    /// A fired key was collected: if it is the one remembered for `o`, forget it.
    pub fn collected(&mut self, o: &str, k: &Key)
        ensures final(self)@ == spec_collected(old(self)@, o@, k@),
    {
        let ghost before = self@;
        let same = match self.armed.get(o) {
            Some(p) => key_eq(&p.key, k),
            None => false,
        };
        if same {
            self.armed.remove(o);
            assert(self@.armed =~= before.armed.remove(o@));
        }
    }

    /// The key remembered for `o`, if any, with the version written with it.
    pub fn armed_for(&self, o: &str) -> (r: Option<&Armed>)
        ensures
            match r {
                Some(k) => self@.armed.contains_key(o@) && k@ == self@.armed[o@],
                None => !self@.armed.contains_key(o@),
            },
    {
        self.armed.get(o)
    }

    /// What is remembered of `o`, if anything.
    pub fn entry(&self, o: &str) -> (r: Option<&Entry>)
        ensures
            match r {
                Some(e) => self@.cache.contains_key(o@) && e@ == self@.cache[o@],
                None => !self@.cache.contains_key(o@),
            },
    {
        self.cache.get(o)
    }
}

} // verus!
