//! What a node remembers, and what each decision means.
//!
//! Membership, the cache, and the deadline keys a node armed. The functions
//! in `node.rs` ensure they compute these.

use vstd::prelude::*;

verus! {

pub type Id = Seq<char>;
pub type Origin = Seq<char>;

/// The hash a load balancer and every node agree on. Any function will do;
/// what matters is that every node computes the same one. `fnv1a` in
/// `node.rs` ensures it computes this.
pub uninterp spec fn hash(o: Origin) -> nat;

pub struct AKey {
    pub origin: Origin,
    pub at: nat,
    pub token: nat,
}

pub struct AArmed {
    pub key: AKey,
    pub etag: Seq<char>,
}

pub struct AEntry {
    pub etag: Seq<char>,
    pub filled_at: nat,
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

/// `hash(o) mod n` over the members in order.
pub open spec fn spec_owner(members: Seq<Id>, o: Origin) -> Option<Id> {
    if members.len() == 0 { None } else { Some(members[(hash(o) % members.len()) as int]) }
}

pub open spec fn spec_fresh(n: ANode, now: nat) -> bool {
    n.read_any && n.last_read + n.ttl >= now
}

/// The node acts as owner of `o`: fresh, and the owner per its members.
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

} // verus!
