//! An origin's timeout is a deadline key in a time bucket.
//!
//! The implementation (`keys.rs`, `handler_docs`) puts one empty object per
//! origin before the document write: the document's nearest deadline, named
//! by that instant, the origin, a token, and the node that armed it. The
//! key is filed under the bucket the instant falls in,
//! `deadline / bucket_ms * bucket_ms`. The runtime's bucket width is one
//! hour. A key already present for that same instant is kept.
//!
//! [`origins_reflected`] says every origin whose document has a least
//! deadline has a key for that deadline in that bucket. [`commit_origin`]
//! is the commit that establishes it. The shell's wake is when a node next
//! looks at the wheel; it is not this key.

use std::collections::BTreeMap;

/// The runtime's timer bucket width: one hour.
pub const HOUR_MS: u64 = 3_600_000;

/// The start of the bucket `at` falls in. `bucket_ms` is at least 1, as
/// `KeySpace::new` stores it.
pub fn bucket_of(at: u64, bucket_ms: u64) -> u64 {
    let width = bucket_ms.max(1);
    at / width * width
}

/// A deadline key: what is due, for which origin, which arm, which node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimerKey {
    pub deadline: u64,
    pub origin: String,
    pub token: u64,
    pub by: String,
}

/// The timeout buckets, and the nearest deadline each origin was committed with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimeoutStore {
    pub bucket_ms: u64,
    pub nearest: BTreeMap<String, Option<u64>>,
    pub buckets: BTreeMap<u64, Vec<TimerKey>>,
}

impl TimeoutStore {
    pub fn new(bucket_ms: u64) -> Self {
        Self { bucket_ms: bucket_ms.max(1), nearest: BTreeMap::new(), buckets: BTreeMap::new() }
    }

    /// Commit an origin document whose nearest deadline is `nearest`
    /// (`next_deadline` of that document). The key for that instant is in
    /// the bucket the instant falls in.
    pub fn commit_origin(&mut self, origin: &str, nearest: Option<u64>, token: u64, by: &str) {
        self.nearest.insert(origin.to_string(), nearest);
        let Some(at) = nearest else { return };
        let bucket = bucket_of(at, self.bucket_ms);
        let keys = self.buckets.entry(bucket).or_default();
        if keys.iter().any(|k| k.origin == origin && k.deadline == at) {
            return;
        }
        keys.push(TimerKey { deadline: at, origin: origin.to_string(), token, by: by.to_string() });
    }

    /// The keys filed in one bucket.
    pub fn in_bucket(&self, bucket: u64) -> &[TimerKey] {
        self.buckets.get(&bucket).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Every committed origin that owes a deadline has its key in that deadline's bucket.
    pub fn reflected(&self) -> bool {
        self.nearest.iter().all(|(origin, owed)| match owed {
            None => true,
            Some(at) => self.in_bucket(bucket_of(*at, self.bucket_ms)).iter().any(|k| k.origin == *origin && k.deadline == *at),
        })
    }
}

use vstd::prelude::*;

verus! {

/// A deadline key, as the specification sees it.
pub struct ATimerKey {
    pub deadline: nat,
    pub origin: Seq<char>,
    pub token: nat,
    pub by: Seq<char>,
}

/// The start of the bucket `at` falls in.
pub open spec fn spec_bucket_of(at: nat, bucket_ms: nat) -> nat {
    (at / bucket_ms) * bucket_ms
}

/// The keys filed in `bucket`. An absent bucket is empty.
pub open spec fn bucket_keys(buckets: Map<nat, Set<ATimerKey>>, bucket: nat) -> Set<ATimerKey> {
    if buckets.contains_key(bucket) { buckets[bucket] } else { Set::empty() }
}

/// `origin` owes `deadline`, and a key for that pair is in the bucket
/// `deadline` falls in.
pub open spec fn reflected(buckets: Map<nat, Set<ATimerKey>>, bucket_ms: nat, origin: Seq<char>, deadline: nat) -> bool {
    let b = spec_bucket_of(deadline, bucket_ms);
    exists |k: ATimerKey|
        #[trigger] bucket_keys(buckets, b).contains(k) && k.origin == origin && k.deadline == deadline
}

/// Every key sits in the bucket its deadline falls in.
pub open spec fn buckets_well_filed(buckets: Map<nat, Set<ATimerKey>>, bucket_ms: nat) -> bool {
    forall |b: nat, k: ATimerKey|
        buckets.contains_key(b) && buckets[b].contains(k)
            ==> b == spec_bucket_of(k.deadline, bucket_ms)
}

/// Every origin whose document has a least deadline has a key for it in that deadline's bucket.
pub open spec fn origins_reflected(origins: Map<Seq<char>, crate::steps_spec::Doc>, buckets: Map<nat, Set<ATimerKey>>, bucket_ms: nat) -> bool {
    forall |o: Seq<char>, t: nat|
        #[trigger] origins.contains_key(o) && crate::steps_spec::is_next(origins[o], t)
            ==> reflected(buckets, bucket_ms, o, t)
}

/// File `deadline` for `origin` unless a key for that instant is already there.
pub open spec fn arm(buckets: Map<nat, Set<ATimerKey>>, bucket_ms: nat, origin: Seq<char>, deadline: nat, token: nat, by: Seq<char>) -> Map<nat, Set<ATimerKey>> {
    if reflected(buckets, bucket_ms, origin, deadline) {
        buckets
    } else {
        let b = spec_bucket_of(deadline, bucket_ms);
        let k = ATimerKey { deadline, origin, token, by };
        buckets.insert(b, bucket_keys(buckets, b).insert(k))
    }
}

/// Commit `doc` as `origin`. `deadline` is `next_deadline` of that document:
/// `Some(t)` when `t` is the least deadline, `None` when the document owes none.
pub open spec fn commit_origin(
    origins: Map<Seq<char>, crate::steps_spec::Doc>,
    buckets: Map<nat, Set<ATimerKey>>,
    bucket_ms: nat,
    origin: Seq<char>,
    doc: crate::steps_spec::Doc,
    deadline: Option<nat>,
    token: nat,
    by: Seq<char>,
) -> (Map<Seq<char>, crate::steps_spec::Doc>, Map<nat, Set<ATimerKey>>) {
    let origins2 = origins.insert(origin, doc);
    let buckets2 = match deadline {
        Some(t) => arm(buckets, bucket_ms, origin, t, token, by),
        None => buckets,
    };
    (origins2, buckets2)
}

/// A document has one least deadline.
pub proof fn lemma_next_unique(d: crate::steps_spec::Doc, t: nat, u: nat)
    requires
        crate::steps_spec::is_next(d, t),
        crate::steps_spec::is_next(d, u),
    ensures
        t == u,
{
    assert(t <= u);
    assert(u <= t);
}

/// No origins, no keys: nothing is owed, so the buckets reflect every origin.
pub proof fn lemma_no_origins(bucket_ms: nat)
    ensures
        origins_reflected(Map::empty(), Map::empty(), bucket_ms),
        buckets_well_filed(Map::empty(), bucket_ms),
{
}

proof fn lemma_arm_keeps(
    buckets: Map<nat, Set<ATimerKey>>,
    bucket_ms: nat,
    origin: Seq<char>,
    deadline: nat,
    token: nat,
    by: Seq<char>,
    other: Seq<char>,
    at: nat,
)
    requires
        bucket_ms > 0,
        reflected(buckets, bucket_ms, other, at),
    ensures
        reflected(arm(buckets, bucket_ms, origin, deadline, token, by), bucket_ms, other, at),
{
    let armed = arm(buckets, bucket_ms, origin, deadline, token, by);
    if reflected(buckets, bucket_ms, origin, deadline) {
        assert(armed == buckets);
    } else {
        let b = spec_bucket_of(deadline, bucket_ms);
        let k = ATimerKey { deadline, origin, token, by };
        let at_bucket = spec_bucket_of(at, bucket_ms);
        let witness = choose |w: ATimerKey| bucket_keys(buckets, at_bucket).contains(w) && w.origin == other && w.deadline == at;
        assert(bucket_keys(buckets, at_bucket).contains(witness));
        if at_bucket == b {
            assert(bucket_keys(armed, at_bucket) == bucket_keys(buckets, b).insert(k));
            assert(bucket_keys(armed, at_bucket).contains(witness));
        } else {
            assert(bucket_keys(armed, at_bucket) == bucket_keys(buckets, at_bucket));
        }
    }
}

proof fn lemma_arm_files(
    buckets: Map<nat, Set<ATimerKey>>,
    bucket_ms: nat,
    origin: Seq<char>,
    deadline: nat,
    token: nat,
    by: Seq<char>,
)
    requires
        bucket_ms > 0,
    ensures
        reflected(arm(buckets, bucket_ms, origin, deadline, token, by), bucket_ms, origin, deadline),
{
    if !reflected(buckets, bucket_ms, origin, deadline) {
        let b = spec_bucket_of(deadline, bucket_ms);
        let k = ATimerKey { deadline, origin, token, by };
        let armed = arm(buckets, bucket_ms, origin, deadline, token, by);
        assert(bucket_keys(armed, b).contains(k));
    }
}

proof fn lemma_arm_well_filed(
    buckets: Map<nat, Set<ATimerKey>>,
    bucket_ms: nat,
    origin: Seq<char>,
    deadline: nat,
    token: nat,
    by: Seq<char>,
)
    requires
        bucket_ms > 0,
        buckets_well_filed(buckets, bucket_ms),
    ensures
        buckets_well_filed(arm(buckets, bucket_ms, origin, deadline, token, by), bucket_ms),
{
    let armed = arm(buckets, bucket_ms, origin, deadline, token, by);
    if reflected(buckets, bucket_ms, origin, deadline) {
        assert(armed == buckets);
    } else {
        let b = spec_bucket_of(deadline, bucket_ms);
        let k = ATimerKey { deadline, origin, token, by };
        assert forall |bucket: nat, key: ATimerKey|
            armed.contains_key(bucket) && armed[bucket].contains(key)
            implies bucket == spec_bucket_of(key.deadline, bucket_ms) by {
            if bucket != b {
                assert(buckets.contains_key(bucket) && buckets[bucket].contains(key));
            } else if key == k {
                assert(spec_bucket_of(k.deadline, bucket_ms) == b);
            } else {
                assert(buckets.contains_key(b) && buckets[b].contains(key));
            }
        };
    }
}

/// Committing an origin files its nearest deadline in that deadline's bucket,
/// and every origin that was already reflected stays reflected.
pub proof fn lemma_commit_origin(
    origins: Map<Seq<char>, crate::steps_spec::Doc>,
    buckets: Map<nat, Set<ATimerKey>>,
    bucket_ms: nat,
    origin: Seq<char>,
    doc: crate::steps_spec::Doc,
    deadline: Option<nat>,
    token: nat,
    by: Seq<char>,
)
    requires
        bucket_ms > 0,
        origins_reflected(origins, buckets, bucket_ms),
        buckets_well_filed(buckets, bucket_ms),
        match deadline {
            Some(t) => crate::steps_spec::is_next(doc, t),
            None => forall |t: nat| !crate::steps_spec::has_deadline(doc, t),
        },
    ensures
        ({
            let (origins2, buckets2) = commit_origin(origins, buckets, bucket_ms, origin, doc, deadline, token, by);
            &&& origins_reflected(origins2, buckets2, bucket_ms)
            &&& buckets_well_filed(buckets2, bucket_ms)
            &&& origins2.contains_key(origin)
            &&& origins2[origin] == doc
            &&& match deadline {
                Some(t) => reflected(buckets2, bucket_ms, origin, t),
                None => true,
            }
        }),
{
    let (origins2, buckets2) = commit_origin(origins, buckets, bucket_ms, origin, doc, deadline, token, by);
    match deadline {
        Some(t) => {
            lemma_arm_files(buckets, bucket_ms, origin, t, token, by);
            lemma_arm_well_filed(buckets, bucket_ms, origin, t, token, by);
        },
        None => {
            assert(buckets2 == buckets);
        },
    }
    assert forall |o: Seq<char>, t: nat|
        origins2.contains_key(o) && crate::steps_spec::is_next(origins2[o], t)
        implies reflected(buckets2, bucket_ms, o, t) by {
        if o == origin {
            assert(origins2[o] == doc);
            match deadline {
                Some(d) => {
                    lemma_next_unique(doc, t, d);
                    assert(reflected(buckets2, bucket_ms, origin, d));
                },
                None => {
                    assert(!crate::steps_spec::is_next(doc, t));
                },
            }
        } else {
            assert(origins.contains_key(o));
            assert(origins2[o] == origins[o]);
            assert(reflected(buckets, bucket_ms, o, t));
            match deadline {
                Some(d) => lemma_arm_keeps(buckets, bucket_ms, origin, d, token, by, o, t),
                None => {},
            }
        }
    };
}

} // verus!
