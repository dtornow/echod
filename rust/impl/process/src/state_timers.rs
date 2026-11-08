//! The wheel: deadline keys ordered by when they fall due, and the listing
//! that is filling it. Firing them is `handler_timers`.
//!
//! A deadline is an empty object whose key says what is due and when,
//! filed under the time bucket its deadline falls in. Every writer puts
//! the key before the state that arms it and holds it in its wheel after.
//!
//! The wheel is where firing happens. A node lists the bucket in exactly
//! three situations: when it starts, when the configuration changes
//! (ownership is `hash mod n`, so every node's share moved), and when the
//! clock reaches a bucket it has not loaded yet. Each listing takes the
//! keys whose target this node owns and nothing else. Between listings no
//! store call is made to find out what is due: the wheel knows.
//!
//! Firing a key sweeps its target, which is idempotent; the key is deleted
//! only once the sweep has committed, since until then it is the only
//! record that the deadline exists; a sweep that found nothing due
//! rewrites the document first, so that the write fences any commit in
//! flight that armed the key (`handler_docs` and `handler_sched`). A key whose delete failed
//! fires again. A key for a target this node no longer owns is dropped
//! from the wheel unfired; its owner lists it.
//!
//! The wheel is a sequence of `(deadline, key)` in order: by deadline, then
//! by key. Each operation ensures it computes its `spec_*` over that
//! sequence.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use echod_concrete::store::before;

use crate::types::*;
use crate::verified::node::str_eq;
use crate::verified::table::Table;
use crate::verified::text::copy_string;

#[cfg(verus_keep_ghost)]
use echod_concrete::store::spec_before;
#[cfg(verus_keep_ghost)]
use echod_concrete::store::StoreErrorSpec;

verus! {

/// One armed key: when it falls due, and its name in the bucket.
pub type Slot = (u64, String);
pub type SlotSpec = (u64, Seq<char>);

/// Armed keys by deadline.
#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct TimerWheel {
    pub armed: Vec<Slot>,
}

/// `a` comes before `b`: an earlier deadline, or the same deadline and an
/// earlier key.
pub open spec fn spec_slot_before(a: SlotSpec, b: SlotSpec) -> bool {
    a.0 < b.0 || (a.0 == b.0 && spec_before(a.1, b.1))
}

/// `at, key` filed in order; the same key twice is one key.
pub open spec fn spec_arm(s: Seq<SlotSpec>, at: u64, key: Seq<char>) -> Seq<SlotSpec>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![(at, key)]
    } else if s[0] == (at, key) {
        s
    } else if spec_slot_before((at, key), s[0]) {
        seq![(at, key)] + s
    } else {
        seq![s[0]] + spec_arm(s.drop_first(), at, key)
    }
}

/// Everything that is `at, key`, gone.
pub open spec fn spec_disarm(s: Seq<SlotSpec>, at: u64, key: Seq<char>) -> Seq<SlotSpec> {
    s.filter(|e: SlotSpec| e != (at, key))
}

/// How many slots at the front are due at `now`.
pub open spec fn spec_due_count(s: Seq<SlotSpec>, now: u64) -> int
    decreases s.len(),
{
    if s.len() == 0 || s[0].0 > now {
        0
    } else {
        1 + spec_due_count(s.drop_first(), now)
    }
}

/// What is due at `now`, and the wheel without it.
pub open spec fn spec_take_due(s: Seq<SlotSpec>, now: u64) -> (Seq<SlotSpec>, Seq<SlotSpec>) {
    let n = spec_due_count(s, now);
    (s.take(n), s.skip(n))
}

pub open spec fn spec_nearest(s: Seq<SlotSpec>) -> Option<u64> {
    if s.len() == 0 { None } else { Some(s[0].0) }
}

proof fn lemma_due_count_bound(s: Seq<SlotSpec>, now: u64)
    ensures
        0 <= spec_due_count(s, now) <= s.len(),
    decreases s.len(),
{
    if !(s.len() == 0 || s[0].0 > now) {
        lemma_due_count_bound(s.drop_first(), now);
    }
}

/// The count from position `i` on, once the first `i` are all due.
proof fn lemma_due_count_step(s: Seq<SlotSpec>, now: u64, i: int)
    requires
        0 <= i <= s.len(),
        forall|j: int| 0 <= j < i ==> (#[trigger] s[j]).0 <= now,
    ensures
        spec_due_count(s, now) == i + spec_due_count(s.skip(i), now),
    decreases i,
{
    if i == 0 {
        assert(s.skip(0) =~= s);
    } else {
        lemma_due_count_step(s, now, i - 1);
        assert(s.skip(i - 1).drop_first() =~= s.skip(i));
        assert(s.skip(i - 1)[0] == s[i - 1]);
    }
}

/// `spec_arm` past a prefix that comes before the slot.
proof fn lemma_arm_step(s: Seq<SlotSpec>, at: u64, key: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
        forall|j: int| 0 <= j < i ==> #[trigger] s[j] != (at, key) && !spec_slot_before((at, key), s[j]),
    ensures
        spec_arm(s, at, key) == s.take(i) + spec_arm(s.skip(i), at, key),
    decreases i,
{
    if i == 0 {
        assert(s.skip(0) =~= s);
        assert(s.take(0) + spec_arm(s, at, key) =~= spec_arm(s, at, key));
    } else {
        lemma_arm_step(s, at, key, i - 1);
        let rest = s.skip(i - 1);
        assert(rest.drop_first() =~= s.skip(i));
        assert(rest[0] == s[i - 1]);
        assert(s.take(i - 1) + (seq![s[i - 1]] + spec_arm(s.skip(i), at, key)) =~= s.take(i) + spec_arm(s.skip(i), at, key));
    }
}

fn slot_before(a: &Slot, b: &Slot) -> (r: bool)
    ensures
        r == spec_slot_before(a.deep_view(), b.deep_view()),
{
    a.0 < b.0 || (a.0 == b.0 && before(&a.1, &b.1))
}

fn slot_eq(a: &Slot, b: &Slot) -> (r: bool)
    ensures
        r == (a.deep_view() == b.deep_view()),
{
    a.0 == b.0 && str_eq(a.1.as_str(), b.1.as_str())
}

impl TimerWheel {
    pub fn new() -> (r: TimerWheel)
        ensures
            r.deep_view() == (TimerWheelSpec { armed: Seq::empty() }),
    {
        let r = TimerWheel { armed: Vec::new() };
        proof {
            assert(r.armed.deep_view() =~= Seq::<SlotSpec>::empty());
        }
        r
    }

    /// Hold a key. The same key twice is one key.
    pub fn arm(&mut self, at: u64, key: String)
        ensures
            final(self).deep_view().armed == spec_arm(old(self).deep_view().armed, at, key@),
    {
        let ghost s = self.armed.deep_view();
        let slot: Slot = (at, key);
        let mut i = 0;
        while i < self.armed.len()
            invariant
                i <= self.armed.len(),
                s == self.armed.deep_view(),
                s == old(self).deep_view().armed,
                slot.deep_view() == (at, key@),
                forall|j: int| 0 <= j < i ==> #[trigger] s[j] != (at, key@) && !spec_slot_before((at, key@), s[j]),
            decreases self.armed.len() - i,
        {
            if slot_eq(&self.armed[i], &slot) {
                proof {
                    lemma_arm_step(s, at, key@, i as int);
                    assert(s.skip(i as int)[0] == s[i as int]);
                    assert(s.take(i as int) + s.skip(i as int) =~= s);
                }
                return;
            }
            if slot_before(&slot, &self.armed[i]) {
                proof {
                    lemma_arm_step(s, at, key@, i as int);
                    assert(s.skip(i as int)[0] == s[i as int]);
                }
                self.armed.insert(i, slot);
                proof {
                    assert(self.armed.deep_view() =~= s.take(i as int) + (seq![(at, key@)] + s.skip(i as int)));
                }
                return;
            }
            i += 1;
        }
        proof {
            lemma_arm_step(s, at, key@, i as int);
            assert(s.skip(i as int).len() == 0);
        }
        self.armed.push(slot);
        proof {
            assert(self.armed.deep_view() =~= s.take(i as int) + seq![(at, key@)]);
        }
    }

    pub fn disarm(&mut self, at: u64, key: &str)
        ensures
            final(self).deep_view().armed == spec_disarm(old(self).deep_view().armed, at, key@),
    {
        let ghost s = self.armed.deep_view();
        let mut kept: Vec<Slot> = Vec::new();
        let mut i = 0;
        proof {
            reveal(Seq::filter);
            assert(kept.deep_view() =~= Seq::<SlotSpec>::empty());
            assert(s.take(0) =~= Seq::<SlotSpec>::empty());
        }
        while i < self.armed.len()
            invariant
                i <= self.armed.len(),
                s == self.armed.deep_view(),
                kept.deep_view() == spec_disarm(s.take(i as int), at, key@),
            decreases self.armed.len() - i,
        {
            let e = &self.armed[i];
            let ghost k0 = kept.deep_view();
            if !(e.0 == at && str_eq(e.1.as_str(), key)) {
                kept.push((e.0, copy_string(&e.1)));
                proof {
                    assert(kept.deep_view() =~= k0.push(s[i as int]));
                }
            }
            proof {
                reveal(Seq::filter);
                assert(s.take(i as int + 1).drop_last() =~= s.take(i as int));
                assert(s.take(i as int + 1).last() == s[i as int]);
            }
            i += 1;
        }
        proof {
            assert(s.take(i as int) =~= s);
        }
        self.armed = kept;
    }

    /// Everything due at `now`, removed from the wheel.
    pub fn take_due(&mut self, now: u64) -> (r: Vec<Slot>)
        ensures
            (r.deep_view(), final(self).deep_view().armed) == spec_take_due(old(self).deep_view().armed, now),
    {
        let ghost s = self.armed.deep_view();
        let mut n = 0;
        while n < self.armed.len() && self.armed[n].0 <= now
            invariant
                n <= self.armed.len(),
                s == self.armed.deep_view(),
                forall|j: int| 0 <= j < n ==> (#[trigger] s[j]).0 <= now,
            decreases self.armed.len() - n,
        {
            n += 1;
        }
        proof {
            lemma_due_count_step(s, now, n as int);
            if n < self.armed.len() {
                assert(s.skip(n as int)[0] == s[n as int]);
            }
            assert(spec_due_count(s, now) == n);
        }
        let mut due: Vec<Slot> = Vec::new();
        let mut rest: Vec<Slot> = Vec::new();
        let mut i = 0;
        proof {
            assert(due.deep_view() =~= Seq::<SlotSpec>::empty());
        }
        while i < self.armed.len()
            invariant
                i <= self.armed.len(),
                n <= self.armed.len(),
                s == self.armed.deep_view(),
                due.deep_view() == s.take(if i < n { i as int } else { n as int }),
                rest.deep_view() == (if i <= n { Seq::<SlotSpec>::empty() } else { s.subrange(n as int, i as int) }),
            decreases self.armed.len() - i,
        {
            let e = &self.armed[i];
            let ghost d0 = due.deep_view();
            let ghost r0 = rest.deep_view();
            if i < n {
                due.push((e.0, copy_string(&e.1)));
                proof {
                    assert(due.deep_view() =~= d0.push(s[i as int]));
                    assert(s.take(i as int + 1) =~= s.take(i as int).push(s[i as int]));
                }
            } else {
                rest.push((e.0, copy_string(&e.1)));
                proof {
                    assert(rest.deep_view() =~= r0.push(s[i as int]));
                    assert(s.subrange(n as int, i as int + 1) =~= s.subrange(n as int, i as int).push(s[i as int]));
                    if i == n {
                        assert(s.subrange(n as int, n as int) =~= Seq::<SlotSpec>::empty());
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(s.skip(n as int) =~= (if i <= n { Seq::<SlotSpec>::empty() } else { s.subrange(n as int, i as int) }));
        }
        self.armed = rest;
        due
    }

    pub fn nearest(&self) -> (r: Option<u64>)
        ensures
            r == spec_nearest(self.deep_view().armed),
    {
        if self.armed.len() == 0 { None } else { Some(self.armed[0].0) }
    }

    pub fn len(&self) -> (r: usize)
        ensures
            r == self.deep_view().armed.len(),
    {
        self.armed.len()
    }
}

/// How long a deadline waits after its sweep failed to commit.
pub const RETRY_AFTER_MS: u64 = 1_000;
/// How long a failed listing waits before it is tried again.
pub const RELIST_AFTER_MS: u64 = 1_000;
/// How many sweeps run at once, at most.
pub const CONCURRENCY: usize = 16;

/// A listing in progress.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Listing {
    /// The full load: the buckets there are.
    Prefixes { op: OpId, horizon: u64 },
    /// The full load: this node's share of each bucket at or before the horizon.
    Buckets { pending: Table<OpId, u64>, horizon: u64, loaded: usize, failed: Option<StoreError> },
    /// One more bucket, as the clock reached it.
    Extend { op: OpId, bucket: u64 },
    /// A bucket the clock has left, listed again: another node may have armed
    /// a key into it for a target this node owns after this node listed it.
    Relist { op: OpId, bucket: u64 },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ListingSpec {
    Prefixes { op: OpId, horizon: u64 },
    Buckets { pending: Map<OpId, u64>, horizon: u64, loaded: usize, failed: Option<StoreErrorSpec> },
    Extend { op: OpId, bucket: u64 },
    Relist { op: OpId, bucket: u64 },
}

#[cfg(verus_keep_ghost)]
impl DeepView for Listing {
    type V = ListingSpec;
    open spec fn deep_view(&self) -> ListingSpec {
        match self {
            Listing::Prefixes { op, horizon } => ListingSpec::Prefixes { op: *op, horizon: *horizon },
            Listing::Buckets { pending, horizon, loaded, failed } => ListingSpec::Buckets { pending: pending.deep_view(), horizon: *horizon, loaded: *loaded, failed: failed.deep_view() },
            Listing::Extend { op, bucket } => ListingSpec::Extend { op: *op, bucket: *bucket },
            Listing::Relist { op, bucket } => ListingSpec::Relist { op: *op, bucket: *bucket },
        }
    }
}

#[cfg(verus_keep_ghost)]
impl ListingSpec {
    pub open spec fn expects(self, op: OpId) -> bool {
        match self {
            ListingSpec::Prefixes { op: o, .. } | ListingSpec::Extend { op: o, .. } | ListingSpec::Relist { op: o, .. } => o == op,
            ListingSpec::Buckets { pending, .. } => pending.contains_key(op),
        }
    }
}

impl Listing {
    pub fn expects(&self, op: OpId) -> (r: bool)
        ensures
            r == self.deep_view().expects(op),
    {
        match self {
            Listing::Prefixes { op: o, .. } | Listing::Extend { op: o, .. } | Listing::Relist { op: o, .. } => *o == op,
            Listing::Buckets { pending, .. } => pending.contains(&op),
        }
    }
}

#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Timers {
    pub wheel: TimerWheel,
    pub started: bool,
    /// The start of the last bucket this node has listed. `None` until the
    /// first full load succeeds; nothing fires before that.
    pub loaded_through: Option<u64>,
    /// The start of the last bucket listed again after the clock left it.
    /// A key armed into a bucket by another node, for a target this node
    /// owns, after this node listed the bucket ahead of the clock, is found
    /// when the bucket closes: so a deadline is swept within a bucket or two
    /// of falling due, whoever armed it.
    pub closed_through: Option<u64>,
    pub bucket_ms: u64,
    pub reload_pending: bool,
    pub listing: Option<Listing>,
    pub backoff_until: Option<u64>,
    pub inflight: usize,
    /// Due keys waiting for a sweep to end, oldest first.
    pub backlog: Vec<Slot>,
}

pub open spec fn spec_min_opt(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    match (a, b) {
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
        (Some(x), None) => Some(x),
        (None, Some(y)) => Some(y),
        (None, None) => None,
    }
}

fn min_opt(a: Option<u64>, b: Option<u64>) -> (r: Option<u64>)
    ensures
        r == spec_min_opt(a, b),
{
    match (a, b) {
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
        (Some(x), None) => Some(x),
        (None, Some(y)) => Some(y),
        (None, None) => None,
    }
}

pub open spec fn spec_max(a: u64, b: u64) -> u64 {
    if a > b { a } else { b }
}

/// The earliest instant the timers want to look at the clock: a backoff's
/// end, a reload owed, the nearest deadline, or the clock reaching the
/// last bucket loaded.
pub open spec fn spec_wake_at(t: TimersSpec, now: u64) -> Option<u64> {
    if !t.started {
        None
    } else if t.backoff_until is Some {
        t.backoff_until
    } else if t.listing is Some {
        None
    } else if t.reload_pending {
        Some(now)
    } else {
        let closing = match t.closed_through {
            Some(c) => Some(spec_max(c.saturating_add((2 as u64).saturating_mul(t.bucket_ms)), now)),
            None => None,
        };
        let loaded = match t.loaded_through {
            Some(l) => Some(spec_max(l, now)),
            None => None,
        };
        spec_min_opt(spec_min_opt(spec_nearest(t.wheel.armed), loaded), closing)
    }
}

impl Timers {
    pub fn new() -> (r: Timers)
        ensures
            r.deep_view() == spec_timers_new(),
    {
        let r = Timers { wheel: TimerWheel::new(), started: false, loaded_through: None, closed_through: None, bucket_ms: 0, reload_pending: false, listing: None, backoff_until: None, inflight: 0, backlog: Vec::new() };
        proof {
            assert(r.backlog.deep_view() =~= Seq::<SlotSpec>::empty());
        }
        r
    }

    pub fn wake_at(&self, now: u64) -> (r: Option<u64>)
        ensures
            r == spec_wake_at(self.deep_view(), now),
    {
        if !self.started {
            return None;
        }
        if let Some(b) = self.backoff_until {
            return Some(b);
        }
        if self.listing.is_some() {
            return None;
        }
        if self.reload_pending {
            return Some(now);
        }
        // the next bucket to close, two bucket starts past the last closed
        let closing = match self.closed_through {
            Some(c) => {
                let two = c.saturating_add((2 as u64).saturating_mul(self.bucket_ms));
                Some(if two > now { two } else { now })
            },
            None => None,
        };
        let loaded = match self.loaded_through {
            Some(l) => Some(if l > now { l } else { now }),
            None => None,
        };
        min_opt(min_opt(self.wheel.nearest(), loaded), closing)
    }

    /// The next instant the wheel wants a physical wake. The keys stay here;
    /// the wake says only that the wheel is the loop to run.
    pub fn next_wake(&self, now: u64) -> (r: Option<(u64, Armed)>)
        ensures
            r == spec_next_wake(self.deep_view(), now),
    {
        match self.wake_at(now) {
            Some(at) => Some((at, Armed::Wheel)),
            None => None,
        }
    }
}

pub open spec fn spec_timers_new() -> TimersSpec {
    TimersSpec {
        wheel: TimerWheelSpec { armed: Seq::empty() },
        started: false,
        loaded_through: None,
        closed_through: None,
        bucket_ms: 0,
        reload_pending: false,
        listing: None,
        backoff_until: None,
        inflight: 0,
        backlog: Seq::empty(),
    }
}

pub open spec fn spec_next_wake(t: TimersSpec, now: u64) -> Option<(u64, Armed)> {
    match spec_wake_at(t, now) {
        Some(at) => Some((at, Armed::Wheel)),
        None => None,
    }
}

} // verus!
