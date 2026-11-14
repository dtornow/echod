//! A commit, as the node decides it: which deadline key to arm before the
//! document is written, which to remove after, and which to remember.
//!
//! `handler_docs` runs the store calls; this is the decision between
//! them. Each function ensures it computes the specification in
//! `commit_spec`.
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

use super::node::*;
use super::text::{starts_with, strip_prefix};

#[cfg(verus_keep_ghost)]
use super::commit_spec::*;

verus! {

pub fn commit_document_origin(origin: &str) -> (document: String)
    ensures
        document@ == spec_commit_document_origin(origin@),
{
    match strip_prefix(origin, "w:") {
        Some(document) => document,
        None => match strip_prefix(origin, "s:") {
            Some(document) => document,
            None => origin.to_string(),
        },
    }
}

#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct Commit {
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

#[cfg(verus_keep_ghost)]
impl View for Commit {
    type V = ACommit;
    open spec fn view(&self) -> ACommit {
        ACommit {
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
// Executable
// ---------------------------------------------------------------------------

impl NodeCore {
    pub fn commit_collected(&mut self, origin: &str, key: &Key)
        ensures
            final(self)@
                == spec_commit_collected(old(self)@, origin@, key@),
    {
        self.collected(origin, key);
        let document = commit_document_origin(origin);
        if !str_eq(document.as_str(), origin)
            && !starts_with(document.as_str(), "w:")
            && !starts_with(document.as_str(), "s:")
        {
            self.collected(document.as_str(), key);
        }
    }

    pub fn prepare(&self, origin: &str, etag: Option<&String>, deadline: Option<u64>, changed: bool, fired: Option<Key>) -> (t: Commit)
        ensures t@ == spec_prepare(self@, origin@, opt_str(etag), opt_nat(deadline), changed, opt_key(fired)),
    {
        let document = commit_document_origin(origin);
        let canonical = origin.to_string();
        let remembered = match self.armed.get(&canonical) {
            Some(a) => Some(a),
            None => if str_eq(document.as_str(), origin)
                || starts_with(document.as_str(), "w:")
                || starts_with(document.as_str(), "s:")
            {
                None
            } else {
                self.armed.get(&document)
            },
        };
        let previous: Option<Key> = match remembered {
            Some(a) => {
                let same_version = match etag {
                    Some(e) => str_eq(a.etag.as_str(), e.as_str()),
                    None => false,
                };
                let same_key = match &fired {
                    Some(f) => key_eq(&a.key, f),
                    None => false,
                };
                let compatible_key =
                    str_eq(a.key.origin.as_str(), origin)
                        || (!str_eq(document.as_str(), origin)
                            && str_eq(
                                a.key.origin.as_str(),
                                document.as_str(),
                            ));
                if compatible_key && same_version && !same_key {
                    Some(clone_key(&a.key))
                } else {
                    None
                }
            }
            None => None,
        };
        let rearm = changed && match deadline {
            None => false,
            Some(d) => match &previous { Some(p) => p.at != d, None => true },
        };
        Commit { origin: origin.to_string(), deadline, changed, fired, previous, rearm, armed_now: None }
    }

    /// After the write, at version `etag`: remember the key kept with it.
    pub fn finish(&mut self, t: &Commit, etag: &String)
        ensures final(self)@ == spec_finish(old(self)@, t@, etag@),
    {
        let document = commit_document_origin(t.origin.as_str());
        if !str_eq(document.as_str(), t.origin.as_str())
            && !starts_with(document.as_str(), "w:")
            && !starts_with(document.as_str(), "s:")
        {
            self.set_armed(document.as_str(), None);
        }
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

impl Commit {
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
