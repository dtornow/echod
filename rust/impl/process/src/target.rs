//! What a step is run on: a workflow document, or a schedule's.

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

/// The in-process name used by keys and decisions. The fixed, disjoint tags
/// make this injective even when a workflow id itself starts with `s:` (or
/// with the legacy `sched:` marker).
pub open spec fn spec_name(t: TargetSpec) -> Seq<char> {
    match t {
        TargetSpec::Origin(o) => "w:"@ + o,
        TargetSpec::Schedule(id) => "s:"@ + id,
    }
}

/// The inverse of the tagged in-process representation.
pub open spec fn spec_of_name(name: Seq<char>) -> TargetSpec {
    if name.len() >= 2 && name.subrange(0, 2) == "s:"@ {
        TargetSpec::Schedule(name.subrange(2, name.len() as int))
    } else if name.len() >= 2 && name.subrange(0, 2) == "w:"@ {
        TargetSpec::Origin(name.subrange(2, name.len() as int))
    } else {
        TargetSpec::Origin(name)
    }
}

pub proof fn lemma_name_injective(left: TargetSpec, right: TargetSpec)
    requires
        spec_name(left) == spec_name(right),
    ensures
        left == right,
{
    reveal_strlit("w:");
    reveal_strlit("s:");
    match (left, right) {
        (TargetSpec::Origin(a), TargetSpec::Origin(b)) => {
            assert((seq!['w', ':'] + a).skip(2) == a);
            assert((seq!['w', ':'] + b).skip(2) == b);
            assert(spec_name(left).skip(2) == a);
            assert(spec_name(right).skip(2) == b);
        },
        (TargetSpec::Schedule(a), TargetSpec::Schedule(b)) => {
            assert((seq!['s', ':'] + a).skip(2) == a);
            assert((seq!['s', ':'] + b).skip(2) == b);
            assert(spec_name(left).skip(2) == a);
            assert(spec_name(right).skip(2) == b);
        },
        (TargetSpec::Origin(_), TargetSpec::Schedule(_)) => {
            assert(spec_name(left)[0] == 'w');
            assert(spec_name(right)[0] == 's');
            assert('w' != 's') by (compute);
        },
        (TargetSpec::Schedule(_), TargetSpec::Origin(_)) => {
            assert(spec_name(left)[0] == 's');
            assert(spec_name(right)[0] == 'w');
            assert('s' != 'w') by (compute);
        },
    }
}

pub proof fn lemma_of_name_inverse(target: TargetSpec)
    ensures
        spec_of_name(spec_name(target)) == target,
{
    reveal_strlit("w:");
    reveal_strlit("s:");
    assert("w:"@ == seq!['w', ':']);
    assert("s:"@ == seq!['s', ':']);
    reveal(spec_name);
    reveal(spec_of_name);
    match target {
        TargetSpec::Origin(value) => {
            assert(spec_name(TargetSpec::Origin(value))
                == seq!['w', ':'] + value);
            assert((seq!['w', ':'] + value).subrange(
                0,
                2,
            ) == seq!['w', ':']);
            assert((seq!['w', ':'] + value).subrange(
                2,
                (seq!['w', ':'] + value).len() as int,
            ) == value);
            assert((seq!['w', ':'] + value).len() >= 2);
            assert((seq!['w', ':'] + value).subrange(0, 2)
                != seq!['s', ':']) by {
                assert((seq!['w', ':'] + value)[0] == 'w');
                assert(seq!['s', ':'][0] == 's');
                assert('w' != 's') by (compute);
            };
            assert(!((seq!['w', ':'] + value).len() >= 2
                && (seq!['w', ':'] + value).subrange(0, 2)
                    == seq!['s', ':']));
            assert((seq!['w', ':'] + value).len() >= 2
                && (seq!['w', ':'] + value).subrange(0, 2)
                    == seq!['w', ':']);
            assert(spec_of_name(seq!['w', ':'] + value)
                == TargetSpec::Origin(
                    (seq!['w', ':'] + value).subrange(
                        2,
                        (seq!['w', ':'] + value).len() as int,
                    ),
                ));
            assert(spec_of_name(spec_name(TargetSpec::Origin(value)))
                == TargetSpec::Origin(value));
        },
        TargetSpec::Schedule(value) => {
            assert(spec_name(TargetSpec::Schedule(value))
                == seq!['s', ':'] + value);
            assert((seq!['s', ':'] + value).subrange(
                0,
                2,
            ) == seq!['s', ':']);
            assert((seq!['s', ':'] + value).subrange(
                2,
                (seq!['s', ':'] + value).len() as int,
            ) == value);
            assert((seq!['s', ':'] + value).len() >= 2);
            assert((seq!['s', ':'] + value).len() >= 2
                && (seq!['s', ':'] + value).subrange(0, 2)
                    == seq!['s', ':']);
            assert(spec_of_name(seq!['s', ':'] + value)
                == TargetSpec::Schedule(
                    (seq!['s', ':'] + value).subrange(
                        2,
                        (seq!['s', ':'] + value).len() as int,
                    ),
                ));
            assert(spec_of_name(spec_name(TargetSpec::Schedule(value)))
                == TargetSpec::Schedule(value));
        },
    }
}

impl Target {
    /// The name the keys and the node's decisions go by.
    pub fn name(&self) -> (r: String)
        ensures
            r@ == spec_name(self.deep_view()),
    {
        match self {
            Target::Origin(o) => concat("w:", o.as_str()),
            Target::Schedule(id) => concat("s:", id.as_str()),
        }
    }

    /// The target a timer key's name (`origin` or `sched:<id>`) says.
    pub fn of_name(name: &str) -> (r: Target)
        ensures
            r.deep_view() == spec_of_name(name@),
    {
        match strip_prefix(name, "s:") {
            Some(id) => {
                proof {
                    reveal_strlit("s:");
                    assert(name@.subrange(0, 2) =~= "s:"@);
                    assert(name@.subrange(2, name@.len() as int) =~= id@);
                }
                Target::Schedule(id)
            },
            None => match strip_prefix(name, "w:") {
                Some(origin) => {
                    proof {
                        reveal_strlit("s:");
                        reveal_strlit("w:");
                        assert(name@.subrange(0, 2) =~= "w:"@);
                        assert(name@.subrange(2, name@.len() as int)
                            =~= origin@);
                    }
                    Target::Origin(origin)
                },
                None => {
                    proof {
                        reveal_strlit("s:");
                        reveal_strlit("w:");
                    }
                    Target::Origin(text(name))
                },
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
