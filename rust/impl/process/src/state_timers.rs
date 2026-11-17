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
//! The wheel indexes `(deadline, key)` pairs. Due batches preserve deadline
//! order and use the key to break ties; the concrete model states both.


use vstd::prelude::*;
use core::cmp::Ordering;
use std::collections::{BTreeSet, VecDeque};
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::{
    PartialEqSpecImpl, PartialOrdSpecImpl, OrdSpecImpl,
};

use crate::concrete::store::before;

use crate::types::*;
use crate::verified::node::str_eq;
use crate::verified::table::Table;
use crate::verified::text::copy_string;

#[cfg(verus_keep_ghost)]
use echod_concrete_spec::handler::spec_before;
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::StoreErrorSpec;

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionTimerWheelV as TimerWheelSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionTimersV as TimersSpec;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionListingV as ListingSpec;

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_state_timers_spec_slot_before as spec_slot_before,
    production_state_timers_spec_arm as spec_arm,
    production_state_timers_spec_disarm as spec_disarm,
    production_state_timers_spec_take_due as spec_take_due,
    production_state_timers_spec_take_due_n as spec_take_due_n,
    production_state_timers_spec_minimum as spec_minimum,
    production_state_timers_spec_is_first as spec_is_first,
    production_state_timers_spec_nearest as spec_nearest,
    production_state_timers_spec_min_opt as spec_min_opt,
    production_state_timers_spec_max as spec_max,
    production_state_timers_spec_wake_at as spec_wake_at,
    production_state_timers_spec_timers_new as spec_timers_new,
    production_state_timers_spec_next_wake as spec_next_wake,
};

pub use echod_concrete_spec::state::{RETRY_AFTER_MS, RELIST_AFTER_MS, CONCURRENCY, TIMER_WORK_BUDGET};
verus! {
#[cfg(verus_keep_ghost)]
impl DeepView for TimerWheel {
    type V = TimerWheelSpec;
    open spec fn deep_view(&self) -> TimerWheelSpec {
        TimerWheelSpec {
            armed: self.armed@,
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for TimerWheel {
    type V = TimerWheelSpec;
    open spec fn view(&self) -> TimerWheelSpec { self.deep_view() }
}
#[cfg(verus_keep_ghost)]
impl DeepView for Timers {
    type V = TimersSpec;
    open spec fn deep_view(&self) -> TimersSpec {
        TimersSpec {
            wheel: self.wheel.deep_view(),
            started: self.started.deep_view(),
            loaded_through: self.loaded_through.deep_view(),
            closed_through: self.closed_through.deep_view(),
            bucket_ms: self.bucket_ms.deep_view(),
            reload_pending: self.reload_pending.deep_view(),
            listing: self.listing.deep_view(),
            backoff_until: self.backoff_until.deep_view(),
            inflight: self.inflight.deep_view(),
            backlog: self.backlog.deep_view(),
            budget: self.budget,
            rediscover_at: self.rediscover_at,
        }
    }
}
#[cfg(verus_keep_ghost)]
impl View for Timers {
    type V = TimersSpec;
    open spec fn view(&self) -> TimersSpec { self.deep_view() }
}


/// One armed key: when it falls due, and its name in the bucket.
pub type Slot = (u64, String);
pub type SlotSpec = (u64, Seq<char>);

pub struct TimerKey {
    pub at: u64,
    pub key: String,
}

pub open spec fn timer_key_order(a: SlotSpec, b: SlotSpec) -> Ordering {
    if a == b { Ordering::Equal }
    else if spec_slot_before(a, b) { Ordering::Less }
    else { Ordering::Greater }
}

proof fn timer_order_pair(a: SlotSpec, b: SlotSpec)
    ensures
        (timer_key_order(a, b) == Ordering::Less) == (timer_key_order(b, a) == Ordering::Greater),
        (timer_key_order(a, b) == Ordering::Equal) == (a == b),
{
    use echod_concrete_spec::property_proof::{
        lemma_before_irreflexive, lemma_before_transitive, lemma_before_total,
    };
    lemma_before_irreflexive(a.1);
    if a.1 != b.1 { lemma_before_total(a.1, b.1); }
    if spec_before(a.1, b.1) && spec_before(b.1, a.1) {
        lemma_before_transitive(a.1, b.1, a.1);
    }
}

proof fn timer_order_transitive(a: SlotSpec, b: SlotSpec, c: SlotSpec)
    requires timer_key_order(a, b) == Ordering::Less, timer_key_order(b, c) == Ordering::Less,
    ensures timer_key_order(a, c) == Ordering::Less,
{
    if a.0 == b.0 && b.0 == c.0 {
        echod_concrete_spec::property_proof::lemma_before_transitive(a.1, b.1, c.1);
        echod_concrete_spec::property_proof::lemma_before_irreflexive(a.1);
    }
}

proof fn timer_key_obeys_order()
    ensures vstd::laws_cmp::obeys_cmp::<TimerKey>(),
{
    use vstd::laws_cmp::*;
    use vstd::laws_eq::*;
    reveal(obeys_eq_spec_properties);
    reveal(obeys_partial_cmp_spec_properties);
    reveal(obeys_cmp_partial_ord);
    reveal(obeys_cmp_ord);
    assert forall|a: TimerKey, b: TimerKey|
        #[trigger] timer_key_order(a.deep_view(), b.deep_view()) == Ordering::Less
        <==> timer_key_order(b.deep_view(), a.deep_view()) == Ordering::Greater by {
        timer_order_pair(a.deep_view(), b.deep_view());
    };
    assert forall|a: TimerKey, b: TimerKey, c: TimerKey|
        #[trigger] timer_key_order(a.deep_view(), b.deep_view()) == Ordering::Less
        && #[trigger] timer_key_order(b.deep_view(), c.deep_view()) == Ordering::Less
        implies timer_key_order(a.deep_view(), c.deep_view()) == Ordering::Less by {
        timer_order_transitive(a.deep_view(), b.deep_view(), c.deep_view());
    };
    assert forall|a: TimerKey, b: TimerKey, c: TimerKey|
        #[trigger] timer_key_order(a.deep_view(), b.deep_view()) == Ordering::Greater
        && #[trigger] timer_key_order(b.deep_view(), c.deep_view()) == Ordering::Greater
        implies timer_key_order(a.deep_view(), c.deep_view()) == Ordering::Greater by {
        timer_order_pair(b.deep_view(), a.deep_view());
        timer_order_pair(c.deep_view(), b.deep_view());
        timer_order_transitive(c.deep_view(), b.deep_view(), a.deep_view());
        timer_order_pair(c.deep_view(), a.deep_view());
    };
}

fn compare_timer_keys(a: &TimerKey, b: &TimerKey) -> (order: Ordering)
    ensures order == timer_key_order(a.deep_view(), b.deep_view()),
{
    if a.at == b.at && str_eq(a.key.as_str(), b.key.as_str()) {
        Ordering::Equal
    } else if a.at < b.at || (a.at == b.at && before(&a.key, &b.key)) {
        Ordering::Less
    } else {
        Ordering::Greater
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for TimerKey {
    type V = SlotSpec;
    open spec fn deep_view(&self) -> SlotSpec { (self.at, self.key@) }
}

#[cfg(verus_keep_ghost)]
impl PartialEqSpecImpl for TimerKey {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &Self) -> bool {
        self.deep_view() == other.deep_view()
    }
}

impl PartialEq for TimerKey {
    fn eq(&self, other: &Self) -> (same: bool)
        ensures same == (self.deep_view() == other.deep_view()),
    {
        self.at == other.at && str_eq(self.key.as_str(), other.key.as_str())
    }
}

impl Eq for TimerKey {}

#[cfg(verus_keep_ghost)]
impl OrdSpecImpl for TimerKey {
    open spec fn obeys_cmp_spec() -> bool { true }
    open spec fn cmp_spec(&self, other: &Self) -> Ordering {
        timer_key_order(self.deep_view(), other.deep_view())
    }
}

impl Ord for TimerKey {
    fn cmp(&self, other: &Self) -> (order: Ordering)
        ensures order == timer_key_order(self.deep_view(), other.deep_view()),
    {
        compare_timer_keys(self, other)
    }
}

#[cfg(verus_keep_ghost)]
impl PartialOrdSpecImpl for TimerKey {
    open spec fn obeys_partial_cmp_spec() -> bool { true }
    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<Ordering> {
        Some(timer_key_order(self.deep_view(), other.deep_view()))
    }
}

impl PartialOrd for TimerKey {
    fn partial_cmp(&self, other: &Self) -> (order: Option<Ordering>)
        ensures order == Some(timer_key_order(self.deep_view(), other.deep_view())),
    {
        Some(compare_timer_keys(self, other))
    }
}

pub struct TimerIndex {
    keys: BTreeSet<TimerKey>,
}

#[cfg(verus_keep_ghost)]
impl View for TimerIndex {
    type V = Set<SlotSpec>;
    closed spec fn view(&self) -> Self::V { self.keys.deep_view() }
}

proof fn timer_key_ext(a: TimerKey, b: TimerKey)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    echod_types::common::axiom_string_ext(a.key, b.key);
}

impl TimerIndex {
    pub fn new() -> (index: Self)
        ensures index@ == Set::<SlotSpec>::empty(),
    {
        let keys = BTreeSet::new();
        Self { keys }
    }

    pub fn len(&self) -> (count: usize)
        ensures count == self@.len(),
    {
        proof {
            timer_key_obeys_order();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            assert forall|a: TimerKey, b: TimerKey|
                self.keys@.contains(a) && self.keys@.contains(b)
                && a.deep_view() == b.deep_view() implies a == b by {
                timer_key_ext(a, b);
            };
            vstd::set_lib::lemma_map_size(self.keys@, self@, |k: TimerKey| k.deep_view());
        }
        self.keys.len()
    }

    pub fn arm(&mut self, at: u64, key: String)
        ensures final(self)@ == old(self)@.insert((at, key@)),
    {
        proof {
            timer_key_obeys_order();
        }
        let slot = TimerKey { at, key };
        let ghost old = self.keys@;
        self.keys.insert(slot);
        proof {
            assert(self.keys@ == old.insert(slot));
            old.lemma_set_map_insert_commute(slot, |k: TimerKey| k.deep_view());
            assert(self.keys.deep_view() =~= old.map(|k: TimerKey| k.deep_view()).insert((at, key@)));
        }
    }

    pub fn disarm(&mut self, at: u64, key: &str)
        ensures final(self)@ == old(self)@.remove((at, key@)),
    {
        proof { timer_key_obeys_order(); }
        let slot = TimerKey { at, key: crate::verified::text::text(key) };
        let ghost old = self.keys@;
        self.keys.remove(&slot);
        proof {
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            broadcast use vstd::set::Set::lemma_map_contains;
            assert(self.keys@ == old.remove(slot));
            assert forall|k: TimerKey| k.deep_view() == slot.deep_view() implies k == slot by {
                timer_key_ext(k, slot);
            };
            assert forall|value: SlotSpec|
                self.keys.deep_view().contains(value)
                == old.map(|k: TimerKey| k.deep_view()).remove((at, key@)).contains(value) by {
                if self.keys.deep_view().contains(value) {
                    let k = choose|k: TimerKey| self.keys@.contains(k) && k.deep_view() == value;
                    if value == slot.deep_view() { timer_key_ext(k, slot); }
                } else if old.map(|k: TimerKey| k.deep_view()).remove((at, key@)).contains(value) {
                    let k = choose|k: TimerKey| old.contains(k) && k.deep_view() == value;
                    assert(self.keys@.contains(k));
                }
            };
            assert(self.keys.deep_view() =~= old.map(|k: TimerKey| k.deep_view()).remove((at, key@)));
        }
    }

    pub fn first(&self) -> (slot: Option<Slot>)
        ensures
            match slot {
                None => self@.is_empty(),
                Some(k) => self@.contains(k.deep_view())
                    && forall|other: SlotSpec| self@.contains(other)
                        ==> !spec_slot_before(other, k.deep_view()),
            },
    {
        proof {
            timer_key_obeys_order();
            broadcast use vstd::laws_cmp::group_laws_cmp;
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            assert(vstd::std_specs::btree::key_obeys_cmp_spec::<TimerKey>());
            assert(vstd::laws_cmp::obeys_cmp::<&TimerKey>());
        }
        let mut iter = self.keys.iter();
        let ghost items = iter.remaining();
        match iter.next() {
            None => None,
            Some(key) => {
                let slot = (key.at, copy_string(&key.key));
                proof {
                    broadcast use vstd::std_specs::btree::group_btree_axioms;
                    broadcast use vstd::set::Set::lemma_map_contains;
                    assert(items.len() > 0 && items[0] == key);
                    assert(items.unref()[0] == *key);
                    assert(items.unref().contains(*key));
                    items.unref().to_set_ensures();
                    assert(self.keys@.contains(*key));
                    assert forall|other: SlotSpec| self@.contains(other)
                        implies !spec_slot_before(other, slot.deep_view()) by {
                        let raw = choose|raw: TimerKey| self.keys@.contains(raw) && raw.deep_view() == other;
                        assert(items.unref().contains(raw));
                        let j = choose|j: int| 0 <= j < items.len() && *items[j] == raw;
                        if j == 0 {
                            assert(raw.deep_view() == key.deep_view());
                            echod_concrete_spec::property_proof::lemma_before_irreflexive(key.key@);
                        } else {
                            assert(vstd::std_specs::cmp::OrdSpec::cmp_spec(&items[0], &items[j]) == Ordering::Less);
                            timer_order_pair(key.deep_view(), raw.deep_view());
                        }
                    };
                }
                Some(slot)
            },
        }
    }

}

/// Armed keys indexed by deadline, then key.
pub struct TimerWheel {
    pub armed: TimerIndex,
}

proof fn first_is_minimum(s: Set<SlotSpec>, first: SlotSpec)
    requires spec_is_first(s, first),
    ensures first == spec_minimum(s),
{
    assert(exists|k: SlotSpec| spec_is_first(s, k));
    let other = spec_minimum(s);
    assert(spec_is_first(s, other));
    assert(!spec_slot_before(first, other));
    assert(!spec_slot_before(other, first));
    if first.0 == other.0 && first.1 != other.1 {
        echod_concrete_spec::property_proof::lemma_before_total(first.1, other.1);
    }
}

impl TimerWheel {
    pub fn new() -> (r: TimerWheel)
        ensures
            r.deep_view() == (TimerWheelSpec { armed: Set::empty() }),
    {
        TimerWheel { armed: TimerIndex::new() }
    }

    /// Hold a key. The same key twice is one key.
    pub fn arm(&mut self, at: u64, key: String)
        ensures
            final(self).deep_view().armed == spec_arm(old(self).deep_view().armed, at, key@),
    {
        self.armed.arm(at, key);
    }

    pub fn disarm(&mut self, at: u64, key: &str)
        ensures
            final(self).deep_view().armed == spec_disarm(old(self).deep_view().armed, at, key@),
    {
        self.armed.disarm(at, key);
    }

    /// One bounded batch due at `now`, removed in deadline/key order.
    pub fn take_due(&mut self, now: u64, limit: usize) -> (r: VecDeque<Slot>)
        ensures
            r.len() <= limit,
            (r.deep_view(), final(self).deep_view().armed) == spec_take_due(old(self).deep_view().armed, now, limit as nat),
    {
        let ghost start = self.armed@;
        let mut due: VecDeque<Slot> = VecDeque::new();
        let mut fuel = limit;
        while fuel > 0
            invariant
                fuel <= limit,
                due.len() + fuel == limit,
                start == old(self).deep_view().armed,
                spec_take_due(start, now, limit as nat).0 == due.deep_view() + spec_take_due_n(self.armed@, now, fuel as nat).0,
                spec_take_due(start, now, limit as nat).1 == spec_take_due_n(self.armed@, now, fuel as nat).1,
            decreases fuel,
        {
            let slot = match self.armed.first() {
                None => {
                    proof { assert(due.deep_view() + Seq::empty() =~= due.deep_view()); }
                    return due;
                },
                Some(slot) => slot,
            };
            proof { first_is_minimum(self.armed@, slot.deep_view()); }
            if slot.0 > now {
                proof { assert(due.deep_view() + Seq::empty() =~= due.deep_view()); }
                return due;
            }
            self.armed.disarm(slot.0, slot.1.as_str());
            let ghost previous = due.deep_view();
            due.push_back(slot);
            proof { assert(due.deep_view() =~= previous + seq![slot.deep_view()]); }
            fuel -= 1;
        }
        due
    }

    pub fn nearest(&self) -> (r: Option<u64>)
        ensures
            r == spec_nearest(self.deep_view().armed),
    {
        match self.armed.first() {
            None => None,
            Some(slot) => {
                proof { first_is_minimum(self.armed@, slot.deep_view()); }
                Some(slot.0)
            },
        }
    }

    pub fn len(&self) -> (r: usize)
        ensures
            r == self.deep_view().armed.len(),
    {
        self.armed.len()
    }
}

/// How long a deadline waits after its sweep failed to commit.

/// How long a failed listing waits before it is tried again.

/// How many sweeps run at once, at most.


/// A listing in progress.
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
    pub backlog: VecDeque<Slot>,
    pub budget: usize,
    pub rediscover_at: Option<u64>,
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



/// The earliest instant the timers want to look at the clock: a backoff's
/// end, a reload owed, the nearest deadline, or the clock reaching the
/// last bucket loaded.


impl Timers {
    pub fn new() -> (r: Timers)
        ensures
            r.deep_view() == spec_timers_new(),
    {
        let r = Timers { wheel: TimerWheel::new(), started: false, loaded_through: None, closed_through: None, bucket_ms: 0, reload_pending: false, listing: None, backoff_until: None, inflight: 0, backlog: VecDeque::new(), budget: 0, rediscover_at: None };
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
        let due = if self.loaded_through.is_some() && self.inflight < CONCURRENCY {
            if self.backlog.len() > 0 { Some(now) } else { self.wheel.nearest() }
        } else { None };
        if let Some(b) = self.backoff_until {
            return min_opt(due, Some(b));
        }
        if self.listing.is_some() {
            return due;
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
        min_opt(due, min_opt(self.rediscover_at, min_opt(loaded, closing)))
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





} // verus!

#[cfg(test)]
mod tests {
    use super::{Listing, TimerWheel, Timers, CONCURRENCY};

    #[test]
    fn index_preserves_pair_identity_and_deadline_tie_order() {
        let mut wheel = TimerWheel::new();
        wheel.arm(20, "z".into());
        wheel.arm(20, "a".into());
        wheel.arm(10, "same".into());
        wheel.arm(20, "same".into());
        wheel.arm(20, "same".into());
        assert_eq!(wheel.len(), 4);
        wheel.disarm(10, "same");
        assert_eq!(wheel.nearest(), Some(20));
        assert!(wheel.take_due(19, 64).is_empty());
        assert_eq!(wheel.take_due(20, 64), vec![(20, "a".into()), (20, "same".into()), (20, "z".into())]);
        assert_eq!(wheel.nearest(), None);
    }

    #[test]
    fn due_extraction_leaves_a_bounded_continuation() {
        let mut wheel = TimerWheel::new();
        for i in (0..130).rev() {
            wheel.arm(i, format!("key-{i}"));
        }
        assert!(wheel.take_due(200, 0).is_empty());
        assert_eq!(wheel.len(), 130);
        let first = wheel.take_due(200, 64);
        assert_eq!(first.len(), 64);
        assert_eq!(first.front().unwrap().0, 0);
        assert_eq!(first.back().unwrap().0, 63);
        assert_eq!(wheel.nearest(), Some(64));
        assert_eq!(wheel.take_due(200, 64).len(), 64);
        assert_eq!(wheel.take_due(200, 64).len(), 2);
        assert_eq!(wheel.len(), 0);
    }

    #[test]
    fn rediscovery_and_known_due_work_have_independent_wakes() {
        let mut timers = Timers::new();
        timers.started = true;
        timers.loaded_through = Some(7_200_000);
        timers.closed_through = Some(0);
        timers.bucket_ms = 3_600_000;
        timers.rediscover_at = Some(3_900_000);
        assert_eq!(timers.wake_at(3_600_000), Some(3_900_000));
        timers.listing = Some(Listing::Prefixes { op: 1, horizon: 7_200_000 });
        assert_eq!(timers.wake_at(4_000_000), None);
        timers.wheel.arm(4_000_000, "due".into());
        assert_eq!(timers.wake_at(4_000_000), Some(4_000_000));
        timers.inflight = CONCURRENCY;
        assert_eq!(timers.wake_at(4_000_000), None);
        timers.inflight = 0;
        timers.backoff_until = Some(4_001_000);
        assert_eq!(timers.wake_at(4_000_000), Some(4_000_000));
    }
}
