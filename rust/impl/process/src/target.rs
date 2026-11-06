//! What a step is run on: an origin's document, or a schedule's.

use vstd::prelude::*;

use crate::verified::node::str_eq;
use crate::verified::text::{concat, copy_string, strip_prefix, text};

verus! {

/// What a step is run on.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Target {
    Origin(String),
    Schedule(String),
}

#[cfg(verus_keep_ghost)]
pub ghost enum TargetSpec {
    Origin(Seq<char>),
    Schedule(Seq<char>),
}

#[cfg(verus_keep_ghost)]
impl DeepView for Target {
    type V = TargetSpec;
    open spec fn deep_view(&self) -> TargetSpec {
        match self {
            Target::Origin(o) => TargetSpec::Origin(o@),
            Target::Schedule(id) => TargetSpec::Schedule(id@),
        }
    }
}

/// The name the keys and the node's decisions go by: the origin, or
/// `sched:<id>`.
pub open spec fn spec_name(t: TargetSpec) -> Seq<char> {
    match t {
        TargetSpec::Origin(o) => o,
        TargetSpec::Schedule(id) => "sched:"@ + id,
    }
}

/// The target a timer key's name says.
pub open spec fn spec_of_name(name: Seq<char>) -> TargetSpec {
    if name.len() >= 6 && name.subrange(0, 6) == "sched:"@ {
        TargetSpec::Schedule(name.subrange(6, name.len() as int))
    } else {
        TargetSpec::Origin(name)
    }
}

impl Target {
    /// The name the keys and the node's decisions go by.
    pub fn name(&self) -> (r: String)
        ensures
            r@ == spec_name(self.deep_view()),
    {
        match self {
            Target::Origin(o) => copy_string(o),
            Target::Schedule(id) => concat("sched:", id.as_str()),
        }
    }

    /// The target a timer key's name (`origin` or `sched:<id>`) says.
    pub fn of_name(name: &str) -> (r: Target)
        ensures
            r.deep_view() == spec_of_name(name@),
    {
        match strip_prefix(name, "sched:") {
            Some(id) => {
                proof {
                    reveal_strlit("sched:");
                    assert(name@.subrange(0, 6) =~= "sched:"@);
                    assert(name@.subrange(6, name@.len() as int) =~= id@);
                }
                Target::Schedule(id)
            },
            None => {
                proof {
                    reveal_strlit("sched:");
                }
                Target::Origin(text(name))
            },
        }
    }

    /// A copy.
    pub fn copy(&self) -> (r: Target)
        ensures
            r == *self,
    {
        match self {
            Target::Origin(o) => Target::Origin(copy_string(o)),
            Target::Schedule(id) => Target::Schedule(copy_string(id)),
        }
    }

    /// `self == other`.
    pub fn same(&self, other: &Target) -> (r: bool)
        ensures
            r == (self.deep_view() == other.deep_view()),
    {
        match (self, other) {
            (Target::Origin(a), Target::Origin(b)) => str_eq(a.as_str(), b.as_str()),
            (Target::Schedule(a), Target::Schedule(b)) => str_eq(a.as_str(), b.as_str()),
            _ => false,
        }
    }

    /// Is this a schedule's document?
    pub fn is_schedule(&self) -> (r: bool)
        ensures
            r == self.deep_view() is Schedule,
    {
        match self {
            Target::Origin(_) => false,
            Target::Schedule(_) => true,
        }
    }
}

} // verus!
