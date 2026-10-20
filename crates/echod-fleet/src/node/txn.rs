//! A commit, as the node decides it: which deadline key to arm before the
//! document is written, which to remove after, and which to remember.
//!
//! The applier runs the store operations; this is the decision between
//! them, in Anvil's shape: each function computes its specification
//! function on the state's view. The fleet model defines a node's commit
//! actions as these functions.
//!
//! The rules: a key is armed for the document's nearest deadline unless the
//! node remembers a key for that very instant, armed with the very version
//! it loaded — a later version, by anyone, may have replaced the key; the
//! key being fired is never the one relied on, so a fired key of this
//! node's can be deleted; after the write, the key replaced or no longer
//! needed is removed, and the key kept is remembered with the version
//! written. A fired key armed by another node is not deleted here: it is
//! collected by the fenced path, a fire that finds nothing due.

use vstd::prelude::*;

use crate::node::core::*;
use echod_kernel::types::*;

verus! {

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug))]
pub struct Txn {
    pub origin: String,
    /// The nearest deadline of the document as it will be written.
    pub deadline: Option<u64>,
    /// Whether the document differs from what was loaded.
    pub changed: bool,
    /// The key whose firing began this, if any.
    pub fired: Option<Key>,
    /// The key the node remembered for the version loaded, unless it is the one fired.
    pub previous: Option<Key>,
    /// Whether a key must be armed before the write.
    pub rearm: bool,
    /// The key armed, once it is.
    pub armed_now: Option<Key>,
}

pub struct ATxn {
    pub origin: Origin,
    pub deadline: Option<nat>,
    pub changed: bool,
    pub fired: Option<AKey>,
    pub previous: Option<AKey>,
    pub rearm: bool,
    pub armed_now: Option<AKey>,
}

impl View for Txn {
    type V = ATxn;
    open spec fn view(&self) -> ATxn {
        ATxn {
            origin: self.origin@,
            deadline: opt_nat(self.deadline),
            changed: self.changed,
            fired: opt_key(self.fired),
            previous: opt_key(self.previous),
            rearm: self.rearm,
            armed_now: opt_key(self.armed_now),
        }
    }
}

// ---------------------------------------------------------------------------
// The specification
// ---------------------------------------------------------------------------

/// Begin a commit on `o`, having loaded version `etag`: the previous key
/// is the one remembered for `o` if it was armed with that very version
/// and is not the key being fired; a key is armed if the document changed,
/// owes a deadline, and the previous key is not at that instant.
pub open spec fn spec_begin(n: ANode, o: Origin, etag: Option<Seq<char>>, deadline: Option<nat>, changed: bool, fired: Option<AKey>) -> ATxn {
    let previous = if n.armed.contains_key(o) && Some(n.armed[o].etag) == etag && Some(n.armed[o].key) != fired { Some(n.armed[o].key) } else { None };
    let rearm = changed && match deadline {
        None => false,
        Some(d) => match previous { Some(p) => p.at != d, None => true },
    };
    ATxn { origin: o, deadline, changed, fired, previous, rearm, armed_now: None }
}

pub open spec fn spec_armed(t: ATxn, k: AKey) -> ATxn {
    ATxn { armed_now: Some(k), ..t }
}

/// After the write: the previous key, when it was replaced or the document
/// owes no deadline any more.
pub open spec fn spec_to_disarm(t: ATxn) -> Option<AKey> {
    if t.changed && (t.deadline is None || t.rearm) { t.previous } else { None }
}

/// After the write: the key the node remembers for the origin.
pub open spec fn spec_keep(t: ATxn) -> Option<AKey> {
    if t.deadline is None { None } else if t.rearm { t.armed_now } else { t.previous }
}

/// After the write, at version `etag`: remember the key kept with that version.
pub open spec fn spec_finish(n: ANode, t: ATxn, etag: Seq<char>) -> ANode {
    match spec_keep(t) {
        Some(k) => spec_set_armed(n, t.origin, Some(AArmed { key: k, etag })),
        None => spec_set_armed(n, t.origin, None),
    }
}

// ---------------------------------------------------------------------------
// Executable
// ---------------------------------------------------------------------------

impl NodeCore {
    pub fn begin(&self, origin: &str, etag: Option<&String>, deadline: Option<u64>, changed: bool, fired: Option<Key>) -> (t: Txn)
        ensures t@ == spec_begin(self@, origin@, opt_str(etag), opt_nat(deadline), changed, opt_key(fired)),
    {
        let previous: Option<Key> = match self.armed.get(origin) {
            Some(a) => {
                let same_version = match etag {
                    Some(e) => str_eq(a.etag.as_str(), e.as_str()),
                    None => false,
                };
                let same_key = match &fired {
                    Some(f) => key_eq(&a.key, f),
                    None => false,
                };
                if same_version && !same_key { Some(clone_key(&a.key)) } else { None }
            }
            None => None,
        };
        let rearm = changed && match deadline {
            None => false,
            Some(d) => match &previous { Some(p) => p.at != d, None => true },
        };
        Txn { origin: origin.to_string(), deadline, changed, fired, previous, rearm, armed_now: None }
    }

    /// After the write, at version `etag`: remember the key kept with it.
    pub fn finish(&mut self, t: &Txn, etag: &String)
        ensures final(self)@ == spec_finish(old(self)@, t@, etag@),
    {
        let keep: Option<Key> = match t.deadline {
            None => None,
            Some(_) => if t.rearm {
                match &t.armed_now { Some(k) => Some(clone_key(k)), None => None }
            } else {
                match &t.previous { Some(k) => Some(clone_key(k)), None => None }
            },
        };
        match keep {
            Some(k) => self.set_armed(t.origin.as_str(), Some(Armed { key: k, etag: clone_string(etag) })),
            None => self.set_armed(t.origin.as_str(), None),
        }
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

impl Txn {
    /// The instant to arm a key at, if one must be armed.
    pub fn arm_at(&self) -> (r: Option<u64>)
        ensures opt_nat(r) == (if self@.rearm { self@.deadline } else { None }),
    {
        if self.rearm { self.deadline } else { None }
    }

    pub fn armed(&mut self, k: Key)
        ensures final(self)@ == spec_armed(old(self)@, k@),
    {
        self.armed_now = Some(k);
    }

    pub fn to_disarm(&self) -> (r: Option<Key>)
        ensures opt_key(r) == spec_to_disarm(self@),
    {
        if self.changed && (self.deadline.is_none() || self.rearm) {
            match &self.previous { Some(k) => Some(clone_key(k)), None => None }
        } else {
            None
        }
    }
}

} // verus!
