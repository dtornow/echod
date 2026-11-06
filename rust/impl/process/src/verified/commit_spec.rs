//! A commit, as the node decides it: which deadline key to arm before the
//! document is written, which to remove after, and which to remember.
//!
//! `commit.rs`'s `prepare`, `armed`, `to_disarm` and `finish` ensure they
//! compute these.

use vstd::prelude::*;

use super::node_spec::*;

verus! {

pub struct ACommit {
    pub origin: Origin,
    pub deadline: Option<nat>,
    pub changed: bool,
    pub fired: Option<AKey>,
    pub previous: Option<AKey>,
    pub rearm: bool,
    pub armed_now: Option<AKey>,
}

/// Prepare a commit on `o`, having loaded version `etag`: the previous key
/// is the one remembered for `o` if it was armed with that very version
/// and is not the key being fired; a key is armed if the document changed,
/// owes a deadline, and the previous key is not at that instant.
pub open spec fn spec_prepare(n: ANode, o: Origin, etag: Option<Seq<char>>, deadline: Option<nat>, changed: bool, fired: Option<AKey>) -> ACommit {
    let previous = if n.armed.contains_key(o) && Some(n.armed[o].etag) == etag && Some(n.armed[o].key) != fired { Some(n.armed[o].key) } else { None };
    let rearm = changed && match deadline {
        None => false,
        Some(d) => match previous { Some(p) => p.at != d, None => true },
    };
    ACommit { origin: o, deadline, changed, fired, previous, rearm, armed_now: None }
}

pub open spec fn spec_armed(t: ACommit, k: AKey) -> ACommit {
    ACommit { armed_now: Some(k), ..t }
}

/// After the write: the previous key, when it was replaced or the document
/// owes no deadline any more.
pub open spec fn spec_to_disarm(t: ACommit) -> Option<AKey> {
    if t.changed && (t.deadline is None || t.rearm) { t.previous } else { None }
}

/// After the write: the key the node remembers for the origin.
pub open spec fn spec_keep(t: ACommit) -> Option<AKey> {
    if t.deadline is None { None } else if t.rearm { t.armed_now } else { t.previous }
}

/// After the write, at version `etag`: remember the key kept with that version.
pub open spec fn spec_finish(n: ANode, t: ACommit, etag: Seq<char>) -> ANode {
    match spec_keep(t) {
        Some(k) => spec_set_armed(n, t.origin, Some(AArmed { key: k, etag })),
        None => spec_set_armed(n, t.origin, None),
    }
}

pub open spec fn opt_nat(o: Option<u64>) -> Option<nat> {
    match o {
        Some(x) => Some(x as nat),
        None => None,
    }
}

pub open spec fn opt_str(o: Option<&String>) -> Option<Seq<char>> {
    match o {
        Some(s) => Some(s@),
        None => None,
    }
}

} // verus!
