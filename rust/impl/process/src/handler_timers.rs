//! Which keys are due. A due origin goes to the document handler; a due
//! schedule goes to the schedule handler. The listing that fills the wheel
//! lives here too: the wheel decides, the store answers come back here.

use vstd::prelude::*;

use crate::verified::flight::FiredKey;
use crate::verified::node::Key;
use crate::verified::table::Table;
use crate::verified::text::{concat, copy_string};

use crate::handler_docs::{take_opt, Firing, Work};
use crate::keys::TimerEntry;
use crate::state::{Owner, State};
use crate::state_timers::{Listing, CONCURRENCY, RELIST_AFTER_MS, RETRY_AFTER_MS};
use crate::target::Target;
use crate::types::*;

#[cfg(verus_keep_ghost)]
use crate::handler_docs::{spec_submit, FiringSpec, WorkSpec};
#[cfg(verus_keep_ghost)]
use crate::keys::*;
#[cfg(verus_keep_ghost)]
use crate::state::*;
#[cfg(verus_keep_ghost)]
use crate::state_timers::*;
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;
#[cfg(verus_keep_ghost)]
use crate::verified::flight_spec::AFired;
#[cfg(verus_keep_ghost)]
use crate::verified::node::AKey;
#[cfg(verus_keep_ghost)]
use crate::verified::node_spec::spec_owner;
#[cfg(verus_keep_ghost)]
use echod_concrete::store::{StoreErrorSpec, StoreReqSpec};

verus! {

// ---------------------------------------------------------------------------
// Stated
// ---------------------------------------------------------------------------

/// The bucket a node must have loaded at `now`: the one after the current,
/// so a deadline in the next bucket is in the wheel before the clock gets
/// there.
pub open spec fn spec_horizon(s: S, now: u64) -> u64 {
    spec_bucket_of(now.saturating_add(s.keys.bucket_ms), s.keys.bucket_ms)
}

/// Does this node own `target` per the members it holds? No while nobody
/// is a member yet.
pub open spec fn spec_owns(s: S, target: Seq<char>) -> bool {
    spec_owner(s.node.core.members, target) == Some(s.cfg.node_id)
}

pub open spec fn spec_owns_entry(s: S, e: TimerEntrySpec) -> bool {
    spec_owns(s, e.target())
}

pub open spec fn spec_owns_key(s: S, key: Seq<char>) -> bool {
    match spec_parse_timer_key(key) {
        Some(e) => spec_owns_entry(s, e),
        None => false,
    }
}

pub open spec fn spec_with_timers(s: S, t: TimersSpec) -> S {
    S { timers: t, ..s }
}

/// The first configuration is read: load, then fire from the wheel.
#[verifier::opaque]
pub open spec fn spec_timers_start(s: S, now: u64) -> S {
    let s = spec_with_timers(s, TimersSpec { started: true, bucket_ms: s.keys.bucket_ms, reload_pending: true, ..s.timers });
    spec_timers_run(s, now)
}

#[verifier::opaque]
pub open spec fn spec_timers_membership_changed(s: S) -> S {
    spec_with_timers(s, TimersSpec { reload_pending: true, ..s.timers })
}

/// Load what is owed, else fire what is due.
#[verifier::opaque]
pub open spec fn spec_timers_run(s: S, now: u64) -> S {
    if !s.timers.started || s.timers.listing is Some {
        s
    } else if s.timers.backoff_until is Some && now < s.timers.backoff_until->Some_0 {
        s
    } else {
        let s = spec_with_timers(s, TimersSpec { backoff_until: None, ..s.timers });
        if s.timers.reload_pending {
            spec_reload(s, now)
        } else if s.timers.loaded_through is Some && s.timers.loaded_through->Some_0 < spec_horizon(s, now) {
            let bucket = s.timers.loaded_through->Some_0.saturating_add(s.keys.bucket_ms);
            let (s, op) = spec_store(s, StoreReqSpec::List { prefix: spec_bucket_prefix(s.keys.prefix, bucket), max_keys: usize::MAX }, Owner::Timers);
            match op {
                Some(op) => spec_with_timers(s, TimersSpec { listing: Some(ListingSpec::Extend { op, bucket }), ..s.timers }),
                None => s,
            }
        } else if s.timers.closed_through is Some && s.timers.closed_through->Some_0.saturating_add(s.keys.bucket_ms) < spec_bucket_of(now, s.keys.bucket_ms) {
            let bucket = s.timers.closed_through->Some_0.saturating_add(s.keys.bucket_ms);
            let (s, op) = spec_store(s, StoreReqSpec::List { prefix: spec_bucket_prefix(s.keys.prefix, bucket), max_keys: usize::MAX }, Owner::Timers);
            match op {
                Some(op) => spec_with_timers(s, TimersSpec { listing: Some(ListingSpec::Relist { op, bucket }), ..s.timers }),
                None => s,
            }
        } else if s.timers.loaded_through is Some {
            spec_fire_due(s, now)
        } else {
            s
        }
    }
}

/// The full load: every bucket at or before the horizon, this node's
/// share. Keys for targets that are no longer this node's leave the wheel;
/// their owner lists them.
pub open spec fn spec_reload(s: S, now: u64) -> S {
    let horizon = spec_horizon(s, now);
    let armed = s.timers.wheel.armed.filter(|k: SlotSpec| spec_owns_key(s, k.1));
    let s = spec_with_timers(s, TimersSpec { wheel: TimerWheelSpec { armed }, ..s.timers });
    let (s, op) = spec_store(s, StoreReqSpec::ListPrefixes { prefix: spec_timer_prefix(s.keys.prefix) }, Owner::Timers);
    match op {
        Some(op) => spec_with_timers(s, TimersSpec { listing: Some(ListingSpec::Prefixes { op, horizon }), ..s.timers }),
        None => s,
    }
}

/// Take this node's share of a listed bucket into the wheel; `n` counts
/// the keys taken so far.
pub open spec fn spec_take_bucket(s: S, keys: Seq<Seq<char>>, n: nat) -> (S, nat)
    decreases keys.len(),
{
    if keys.len() == 0 {
        (s, n)
    } else {
        let key = keys[0];
        let (s, n) = match spec_parse_timer_key(key) {
            Some(e) => {
                if spec_owns_entry(s, e) {
                    (spec_with_timers(s, TimersSpec { wheel: TimerWheelSpec { armed: spec_arm(s.timers.wheel.armed, e.deadline(), key) }, ..s.timers }), n + 1)
                } else {
                    (s, n)
                }
            },
            None => (s, n),
        };
        spec_take_bucket(s, keys.drop_first(), n)
    }
}

/// List every bucket at or before the horizon; `pending` collects the ops.
pub open spec fn spec_list_buckets(s: S, prefixes: Seq<Seq<char>>, horizon: u64, pending: Map<OpId, u64>) -> (S, Map<OpId, u64>)
    decreases prefixes.len(),
{
    if prefixes.len() == 0 {
        (s, pending)
    } else {
        let (s, pending) = match spec_parse_bucket_prefix(s.keys.prefix, prefixes[0]) {
            Some(bucket) => {
                if bucket <= horizon {
                    let (s, op) = spec_store(s, StoreReqSpec::List { prefix: spec_bucket_prefix(s.keys.prefix, bucket), max_keys: usize::MAX }, Owner::Timers);
                    match op {
                        Some(op) => (s, pending.insert(op, bucket)),
                        None => (s, pending),
                    }
                } else {
                    (s, pending)
                }
            },
            None => (s, pending),
        };
        spec_list_buckets(s, prefixes.drop_first(), horizon, pending)
    }
}

#[verifier::opaque]
pub open spec fn spec_timers_completed(s: S, op: OpId, outcome: StoreRes) -> S {
    match s.timers.listing {
        None => s,
        Some(listing) => {
            if !listing.expects(op) {
                s
            } else {
                let s = spec_with_timers(s, TimersSpec { listing: None, ..s.timers });
                let now = spec_now(s);
                match listing {
                    ListingSpec::Prefixes { horizon, .. } => spec_prefixes_listed(s, horizon, now, outcome),
                    ListingSpec::Buckets { pending, horizon, loaded, failed } => spec_bucket_listed(s, pending.remove(op), horizon, loaded, failed, now, outcome),
                    ListingSpec::Extend { bucket, .. } => spec_extended(s, bucket, now, outcome),
                    ListingSpec::Relist { bucket, .. } => spec_relisted(s, bucket, now, outcome),
                }
            }
        },
    }
}

/// The bucket prefixes are listed: list each bucket up to the horizon.
#[verifier::opaque]
pub open spec fn spec_prefixes_listed(s: S, horizon: u64, now: u64, outcome: StoreRes) -> S {
    match outcome {
        StoreRes::ListPrefixes { result: Ok(prefixes) } => {
            let (s, pending) = spec_list_buckets(s, prefixes.deep_view(), horizon, Map::empty());
            if pending =~= Map::<OpId, u64>::empty() {
                spec_reloaded(s, horizon, 0, now)
            } else {
                spec_with_timers(s, TimersSpec { listing: Some(ListingSpec::Buckets { pending, horizon, loaded: 0, failed: None }), ..s.timers })
            }
        },
        StoreRes::ListPrefixes { result: Err(e) } => spec_listing_failed(s, e.deep_view(), now),
        _ => spec_listing_failed(s, spec_unexpected(), now),
    }
}

/// One bucket of the full load is listed.
#[verifier::opaque]
pub open spec fn spec_bucket_listed(s: S, pending: Map<OpId, u64>, horizon: u64, loaded: usize, failed: Option<StoreErrorSpec>, now: u64, outcome: StoreRes) -> S {
    let (s, loaded, failed) = match outcome {
        StoreRes::List { result: Ok(keys) } => {
            let (s, n) = spec_take_bucket(s, keys.deep_view(), 0);
            (s, loaded.saturating_add(n as usize), failed)
        },
        StoreRes::List { result: Err(e) } => (s, loaded, Some(e.deep_view())),
        _ => (s, loaded, Some(spec_unexpected())),
    };
    if !(pending =~= Map::<OpId, u64>::empty()) {
        spec_with_timers(s, TimersSpec { listing: Some(ListingSpec::Buckets { pending, horizon, loaded, failed }), ..s.timers })
    } else {
        match failed {
            Some(e) => spec_listing_failed(s, e, now),
            None => spec_reloaded(s, horizon, loaded, now),
        }
    }
}

/// The next bucket is listed: the horizon moves.
#[verifier::opaque]
pub open spec fn spec_extended(s: S, bucket: u64, now: u64, outcome: StoreRes) -> S {
    match outcome {
        StoreRes::List { result: Ok(keys) } => {
            let (s, n) = spec_take_bucket(s, keys.deep_view(), 0);
            let s = spec_note(s, NoteSpec::BucketLoaded { bucket, deadlines: n as usize });
            let s = spec_note(s, NoteSpec::TimerListing { ok: true });
            let s = spec_with_timers(s, TimersSpec { loaded_through: Some(bucket), ..s.timers });
            spec_timers_run(s, now)
        },
        StoreRes::List { result: Err(e) } => spec_listing_failed(s, e.deep_view(), now),
        _ => spec_listing_failed(s, spec_unexpected(), now),
    }
}

/// A past bucket is listed again: it is closed.
#[verifier::opaque]
pub open spec fn spec_relisted(s: S, bucket: u64, now: u64, outcome: StoreRes) -> S {
    match outcome {
        StoreRes::List { result: Ok(keys) } => {
            let (s, n) = spec_take_bucket(s, keys.deep_view(), 0);
            let s = spec_note(s, NoteSpec::BucketLoaded { bucket, deadlines: n as usize });
            let s = spec_note(s, NoteSpec::TimerListing { ok: true });
            let s = spec_with_timers(s, TimersSpec { closed_through: Some(bucket), ..s.timers });
            spec_timers_run(s, now)
        },
        StoreRes::List { result: Err(e) } => spec_listing_failed(s, e.deep_view(), now),
        _ => spec_listing_failed(s, spec_unexpected(), now),
    }
}

#[verifier::opaque]
pub open spec fn spec_reloaded(s: S, horizon: u64, loaded: usize, now: u64) -> S {
    let s = spec_with_timers(s, TimersSpec {
        loaded_through: Some(horizon),
        closed_through: Some(spec_bucket_of(now, s.keys.bucket_ms).saturating_sub(s.keys.bucket_ms)),
        reload_pending: false,
        ..s.timers
    });
    let s = spec_note(s, NoteSpec::TimerListing { ok: true });
    let s = spec_note(s, NoteSpec::TimersLoaded { deadlines: loaded, wheel: s.timers.wheel.armed.len() as usize, epoch: s.node.core.epoch as u64 });
    spec_timers_run(s, now)
}

#[verifier::opaque]
pub open spec fn spec_listing_failed(s: S, e: StoreErrorSpec, now: u64) -> S {
    let s = spec_note(s, NoteSpec::TimerListing { ok: false });
    let s = spec_note(s, NoteSpec::ListingFailed { error: spec_error_text(e) });
    spec_with_timers(s, TimersSpec { backoff_until: Some(now.saturating_add(RELIST_AFTER_MS)), ..s.timers })
}

/// Fire what is due, with a bound on how many sweeps run at once.
#[verifier::opaque]
pub open spec fn spec_fire_due(s: S, now: u64) -> S {
    let (due, rest) = spec_take_due(s.timers.wheel.armed, now);
    let s = spec_with_timers(s, TimersSpec { wheel: TimerWheelSpec { armed: rest }, backlog: s.timers.backlog + due, ..s.timers });
    spec_dispatch_due(s, now, s.timers.backlog.len())
}

/// Fire the backlog, oldest first, while a sweep may start. `fuel` bounds
/// the steps: the backlog's length, which a fire never grows.
pub open spec fn spec_dispatch_due(s: S, now: u64, fuel: nat) -> S
    decreases fuel,
{
    if fuel > 0 && s.timers.inflight < CONCURRENCY && s.timers.backlog.len() > 0 {
        let (at, key) = s.timers.backlog[0];
        let s = spec_with_timers(s, TimersSpec { backlog: s.timers.backlog.drop_first(), ..s.timers });
        spec_dispatch_due(spec_timer_fire(s, key, at, now), now, (fuel - 1) as nat)
    } else {
        s
    }
}

/// Fire one key: sweep its target if this node owns it, then collect it.
#[verifier::opaque]
pub open spec fn spec_timer_fire(s: S, key: Seq<char>, at: u64, now: u64) -> S {
    match spec_parse_timer_key(key) {
        None => spec_note(s, NoteSpec::KeyUnparseable { key }),
        Some(entry) => {
            let kind = match entry {
                TimerEntrySpec::Origin { .. } => TimerKind::Origin,
                TimerEntrySpec::Schedule { .. } => TimerKind::Schedule,
            };
            let lag = now.saturating_sub(at);
            let owns = spec_owns_entry(s, entry);
            if !owns || !crate::verified::node_spec::spec_acts(s.node.core, entry.target(), now as nat) {
                let s = if owns {
                    spec_with_timers(s, TimersSpec { wheel: TimerWheelSpec { armed: spec_arm(s.timers.wheel.armed, spec_max(now, at).saturating_add(RETRY_AFTER_MS), key) }, ..s.timers })
                } else {
                    s
                };
                spec_note(s, NoteSpec::TimerFire { kind, outcome: FireOutcome::Deferred, lag_ms: lag })
            } else {
                let s = spec_with_timers(s, TimersSpec { inflight: s.timers.inflight.saturating_add(1), ..s.timers });
                let firing = FiringSpec { key, at, kind, lag };
                match entry {
                    TimerEntrySpec::Origin { origin, deadline, token, by } => {
                        let fired = AFired { key: AKey { origin: "w:"@ + origin, at: deadline as nat, token: token as nat }, by };
                        spec_submit(s, TargetSpec::Origin(origin), WorkSpec::Sweep { fired: Some(fired), now }, Some(firing), false)
                    },
                    TimerEntrySpec::Schedule { id, deadline, token, by } => {
                        let fired = AFired { key: AKey { origin: "s:"@ + id, at: deadline as nat, token: token as nat }, by };
                        spec_submit(s, TargetSpec::Schedule(id), WorkSpec::Fire { schedule: id, fired: Some(fired), now }, Some(firing), false)
                    },
                }
            }
        },
    }
}

/// The flight a key fired is over.
#[verifier::opaque]
pub open spec fn spec_timer_fired(s: S, firing: FiringSpec, now: u64, r: Result<Fired, Seq<char>>) -> S {
    let s = spec_with_timers(s, TimersSpec { inflight: s.timers.inflight.saturating_sub(1), ..s.timers });
    let rearm = spec_max(now, firing.at).saturating_add(RETRY_AFTER_MS);
    let (s, outcome) = match r {
        Ok(Fired::Deleted) => (s, FireOutcome::Deleted),
        Ok(Fired::Kept) => (spec_with_timers(s, TimersSpec { wheel: TimerWheelSpec { armed: spec_arm(s.timers.wheel.armed, rearm, firing.key) }, ..s.timers }), FireOutcome::Kept),
        Err(e) => {
            let s = spec_note(s, NoteSpec::FireFailed { key: firing.key, error: e });
            (spec_with_timers(s, TimersSpec { wheel: TimerWheelSpec { armed: spec_arm(s.timers.wheel.armed, rearm, firing.key) }, ..s.timers }), FireOutcome::Failed)
        },
    };
    let s = spec_note(s, NoteSpec::TimerFire { kind: firing.kind, outcome, lag_ms: firing.lag });
    spec_dispatch_due(s, now, s.timers.backlog.len())
}

/// Allocation exhaustion happens before a fired key can issue its first Store
/// request. Put the key back and undo the in-flight accounting without
/// emitting any external effect.
pub open spec fn spec_timer_op_exhausted(
    s: S,
    firing: FiringSpec,
) -> S {
    let fired_at = firing.at.saturating_add(firing.lag);
    let rearm = spec_max(fired_at, firing.at)
        .saturating_add(RETRY_AFTER_MS);
    spec_with_timers(s, TimersSpec {
        inflight: s.timers.inflight.saturating_sub(1),
        wheel: TimerWheelSpec {
            armed: spec_arm(s.timers.wheel.armed, rearm, firing.key),
        },
        ..s.timers
    })
}

// ---------------------------------------------------------------------------
// Run
// ---------------------------------------------------------------------------

fn max_u64(a: u64, b: u64) -> (r: u64)
    ensures
        r == spec_max(a, b),
{
    if a > b { a } else { b }
}

impl State {
    fn horizon(&self, now: u64) -> (r: u64)
        ensures
            r == spec_horizon(self.deep_view(), now),
    {
        self.keys.bucket_of(now.saturating_add(self.keys.bucket_ms()))
    }

    /// Does this node own `target` per the members it holds? No while
    /// nobody is a member yet.
    pub fn owns(&self, target: &str) -> (r: bool)
        ensures
            r == spec_owns(self.deep_view(), target@),
    {
        match self.node.core.owner(target) {
            Some(o) => crate::verified::node::str_eq(o.as_str(), self.cfg.node_id.as_str()),
            None => false,
        }
    }

    fn owns_entry(&self, e: &TimerEntry) -> (r: bool)
        ensures
            r == spec_owns_entry(self.deep_view(), e.deep_view()),
    {
        self.owns(e.target().as_str())
    }

    fn owns_key(&self, key: &str) -> (r: bool)
        ensures
            r == spec_owns_key(self.deep_view(), key@),
    {
        match self.keys.parse_timer_key(key) {
            Some(e) => self.owns_entry(&e),
            None => false,
        }
    }

    /// The first configuration is read: load, then fire from the wheel.
    pub fn timers_start(&mut self, now: u64)
        ensures
            final(self).deep_view() == spec_timers_start(old(self).deep_view(), now),
    {
        proof {
            reveal(spec_timers_start);
        }
        self.timers.started = true;
        self.timers.bucket_ms = self.keys.bucket_ms();
        self.timers.reload_pending = true;
        self.timers_run(now);
    }

    pub fn timers_membership_changed(&mut self)
        ensures
            final(self).deep_view() == spec_timers_membership_changed(old(self).deep_view()),
    {
        proof {
            reveal(spec_timers_membership_changed);
        }
        self.timers.reload_pending = true;
    }

    /// Load what is owed, else fire what is due. Called whenever time
    /// passed or a listing ended.
    #[verifier::spinoff_prover]
    pub fn timers_run(&mut self, now: u64)
        ensures
            final(self).deep_view() == spec_timers_run(old(self).deep_view(), now),
    {
        proof {
            reveal(spec_timers_run);
        }
        if !self.timers.started || self.timers.listing.is_some() {
            return;
        }
        if let Some(b) = self.timers.backoff_until {
            if now < b {
                return;
            }
        }
        self.timers.backoff_until = None;
        if self.timers.reload_pending {
            self.reload(now);
            return;
        }
        let horizon = self.horizon(now);
        if let Some(through) = self.timers.loaded_through {
            if through < horizon {
                // Bring the loaded range up to the horizon, one bucket at a time.
                let bucket = through.saturating_add(self.keys.bucket_ms());
                let prefix = self.keys.bucket_prefix(bucket);
                if let Some(op) = self.store(StoreReq::List { prefix, max_keys: usize::MAX }, Owner::Timers) {
                    self.timers.listing = Some(Listing::Extend { op, bucket });
                }
                return;
            }
        }
        if let Some(c) = self.timers.closed_through {
            let bucket = c.saturating_add(self.keys.bucket_ms());
            if bucket < self.keys.bucket_of(now) {
                // The clock left a bucket this node listed ahead of time: list
                // it once more, for what others armed into it since.
                let prefix = self.keys.bucket_prefix(bucket);
                if let Some(op) = self.store(StoreReq::List { prefix, max_keys: usize::MAX }, Owner::Timers) {
                    self.timers.listing = Some(Listing::Relist { op, bucket });
                }
                return;
            }
        }
        if self.timers.loaded_through.is_some() {
            self.fire_due(now);
        }
    }

    /// The full load: every bucket at or before the horizon, this node's
    /// share. Keys for targets that are no longer this node's leave the
    /// wheel; their owner lists them.
    fn reload(&mut self, now: u64)
        ensures
            final(self).deep_view() == spec_reload(old(self).deep_view(), now),
    {
        let horizon = self.horizon(now);
        let ghost s0 = self.deep_view();
        let ghost armed = self.timers.wheel.armed.deep_view();
        let mut kept: Vec<crate::state_timers::Slot> = Vec::new();
        let mut i: usize = 0;
        proof {
            reveal(Seq::filter);
            assert(kept.deep_view() =~= Seq::<SlotSpec>::empty());
            assert(armed.take(0) =~= Seq::<SlotSpec>::empty());
        }
        while i < self.timers.wheel.armed.len()
            invariant
                i <= self.timers.wheel.armed.len(),
                *self == *old(self),
                s0 == self.deep_view(),
                armed == self.timers.wheel.armed.deep_view(),
                kept.deep_view() == armed.take(i as int).filter(|k: SlotSpec| spec_owns_key(s0, k.1)),
            decreases self.timers.wheel.armed.len() - i,
        {
            let ghost k0 = kept.deep_view();
            let at = self.timers.wheel.armed[i].0;
            let key = copy_string(&self.timers.wheel.armed[i].1);
            if self.owns_key(key.as_str()) {
                kept.push((at, key));
                proof {
                    assert(kept.deep_view() =~= k0.push(armed[i as int]));
                }
            }
            proof {
                reveal(Seq::filter);
                assert(armed.take(i as int + 1).drop_last() =~= armed.take(i as int));
                assert(armed.take(i as int + 1).last() == armed[i as int]);
            }
            i += 1;
        }
        proof {
            assert(armed.take(i as int) =~= armed);
        }
        self.timers.wheel.armed = kept;
        let prefix = self.keys.timer_prefix();
        if let Some(op) = self.store(StoreReq::ListPrefixes { prefix }, Owner::Timers) {
            self.timers.listing = Some(Listing::Prefixes { op, horizon });
        }
    }

    /// Take this node's share of a listed bucket into the wheel.
    fn take_bucket(&mut self, keys: &Vec<String>) -> (n: usize)
        ensures
            (final(self).deep_view(), n as nat) == spec_take_bucket(old(self).deep_view(), keys.deep_view(), 0),
    {
        let ghost ks = keys.deep_view();
        let ghost s0 = old(self).deep_view();
        let mut n: usize = 0;
        let mut i: usize = 0;
        proof {
            assert(ks.skip(0) =~= ks);
        }
        while i < keys.len()
            invariant
                i <= keys.len(),
                n <= i,
                ks == keys.deep_view(),
                spec_take_bucket(s0, ks, 0) == spec_take_bucket(self.deep_view(), ks.skip(i as int), n as nat),
            decreases keys.len() - i,
        {
            proof {
                assert(ks.skip(i as int).drop_first() =~= ks.skip(i as int + 1));
                assert(ks.skip(i as int)[0] == ks[i as int]);
            }
            let key = copy_string(&keys[i]);
            if let Some(e) = self.keys.parse_timer_key(key.as_str()) {
                if self.owns_entry(&e) {
                    self.timers.wheel.arm(e.deadline(), key);
                    n += 1;
                }
            }
            i += 1;
        }
        proof {
            assert(ks.skip(i as int) =~= Seq::<Seq<char>>::empty());
        }
        n
    }

    /// List every bucket at or before the horizon.
    fn list_buckets(&mut self, prefixes: &Vec<String>, horizon: u64, pending: &mut Table<OpId, u64>)
        ensures
            (final(self).deep_view(), final(pending).deep_view()) == spec_list_buckets(old(self).deep_view(), prefixes.deep_view(), horizon, old(pending).deep_view()),
    {
        let ghost ps = prefixes.deep_view();
        let ghost s0 = old(self).deep_view();
        let ghost p0 = old(pending).deep_view();
        let mut i: usize = 0;
        proof {
            assert(ps.skip(0) =~= ps);
        }
        while i < prefixes.len()
            invariant
                i <= prefixes.len(),
                ps == prefixes.deep_view(),
                spec_list_buckets(s0, ps, horizon, p0) == spec_list_buckets(self.deep_view(), ps.skip(i as int), horizon, pending.deep_view()),
            decreases prefixes.len() - i,
        {
            proof {
                assert(ps.skip(i as int).drop_first() =~= ps.skip(i as int + 1));
                assert(ps.skip(i as int)[0] == ps[i as int]);
            }
            if let Some(bucket) = self.keys.parse_bucket_prefix(prefixes[i].as_str()) {
                if bucket <= horizon {
                    let prefix = self.keys.bucket_prefix(bucket);
                    if let Some(op) = self.store(StoreReq::List { prefix, max_keys: usize::MAX }, Owner::Timers) {
                        pending.insert(op, bucket);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(ps.skip(i as int) =~= Seq::<Seq<char>>::empty());
        }
    }

    pub fn timers_completed(&mut self, op: OpId, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_timers_completed(old(self).deep_view(), op, outcome),
    {
        proof {
            reveal(spec_timers_completed);
        }
        let listing = match take_opt(&mut self.timers.listing) {
            Some(l) => l,
            None => return,
        };
        if !listing.expects(op) {
            self.timers.listing = Some(listing);
            return;
        }
        let now = self.now();
        match listing {
            Listing::Prefixes { horizon, .. } => self.prefixes_listed(horizon, now, outcome),
            Listing::Buckets { mut pending, horizon, loaded, failed } => {
                pending.remove(&op);
                self.bucket_listed(pending, horizon, loaded, failed, now, outcome);
            },
            Listing::Extend { bucket, .. } => self.extended(bucket, now, outcome),
            Listing::Relist { bucket, .. } => self.relisted(bucket, now, outcome),
        }
    }

    /// The bucket prefixes are listed: list each bucket up to the horizon.
    fn prefixes_listed(&mut self, horizon: u64, now: u64, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_prefixes_listed(old(self).deep_view(), horizon, now, outcome),
    {
        proof {
            reveal(spec_prefixes_listed);
        }
        match outcome {
            StoreRes::ListPrefixes { result: Ok(prefixes) } => {
                let mut pending: Table<OpId, u64> = Table::new();
                self.list_buckets(&prefixes, horizon, &mut pending);
                if pending.is_empty() {
                    self.reloaded(horizon, 0, now);
                } else {
                    self.timers.listing = Some(Listing::Buckets { pending, horizon, loaded: 0, failed: None });
                }
            },
            StoreRes::ListPrefixes { result: Err(e) } => self.listing_failed(e, now),
            _ => self.listing_failed(unexpected(), now),
        }
    }

    /// One bucket of the full load is listed.
    fn bucket_listed(&mut self, pending: Table<OpId, u64>, horizon: u64, loaded: usize, failed: Option<StoreError>, now: u64, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_bucket_listed(old(self).deep_view(), pending@, horizon, loaded, failed.deep_view(), now, outcome),
    {
        proof {
            reveal(spec_bucket_listed);
        }
        let (loaded, failed) = match outcome {
            StoreRes::List { result: Ok(keys) } => {
                let n = self.take_bucket(&keys);
                (loaded.saturating_add(n), failed)
            },
            StoreRes::List { result: Err(e) } => (loaded, Some(e)),
            _ => (loaded, Some(unexpected())),
        };
        if !pending.is_empty() {
            self.timers.listing = Some(Listing::Buckets { pending, horizon, loaded, failed });
        } else {
            match failed {
                Some(e) => self.listing_failed(e, now),
                None => self.reloaded(horizon, loaded, now),
            }
        }
    }

    /// The next bucket is listed: the horizon moves.
    fn extended(&mut self, bucket: u64, now: u64, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_extended(old(self).deep_view(), bucket, now, outcome),
    {
        proof {
            reveal(spec_extended);
        }
        match outcome {
            StoreRes::List { result: Ok(keys) } => {
                let n = self.take_bucket(&keys);
                self.note(Note::BucketLoaded { bucket, deadlines: n });
                self.note(Note::TimerListing { ok: true });
                self.timers.loaded_through = Some(bucket);
                self.timers_run(now);
            },
            StoreRes::List { result: Err(e) } => self.listing_failed(e, now),
            _ => self.listing_failed(unexpected(), now),
        }
    }

    /// A past bucket is listed again: it is closed.
    fn relisted(&mut self, bucket: u64, now: u64, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_relisted(old(self).deep_view(), bucket, now, outcome),
    {
        proof {
            reveal(spec_relisted);
        }
        match outcome {
            StoreRes::List { result: Ok(keys) } => {
                let n = self.take_bucket(&keys);
                self.note(Note::BucketLoaded { bucket, deadlines: n });
                self.note(Note::TimerListing { ok: true });
                self.timers.closed_through = Some(bucket);
                self.timers_run(now);
            },
            StoreRes::List { result: Err(e) } => self.listing_failed(e, now),
            _ => self.listing_failed(unexpected(), now),
        }
    }

    fn reloaded(&mut self, horizon: u64, loaded: usize, now: u64)
        ensures
            final(self).deep_view() == spec_reloaded(old(self).deep_view(), horizon, loaded, now),
    {
        proof {
            reveal(spec_reloaded);
        }
        self.timers.loaded_through = Some(horizon);
        // the full load covered every bucket up to now; the current one is
        // listed again when it closes
        self.timers.closed_through = Some(self.keys.bucket_of(now).saturating_sub(self.keys.bucket_ms()));
        self.timers.reload_pending = false;
        self.note(Note::TimerListing { ok: true });
        let wheel = self.timers.wheel.len();
        let epoch = self.node.core.epoch;
        self.note(Note::TimersLoaded { deadlines: loaded, wheel, epoch });
        self.timers_run(now);
    }

    fn listing_failed(&mut self, e: StoreError, now: u64)
        ensures
            final(self).deep_view() == spec_listing_failed(old(self).deep_view(), e.deep_view(), now),
    {
        proof {
            reveal(spec_listing_failed);
        }
        self.note(Note::TimerListing { ok: false });
        self.note(Note::ListingFailed { error: error_text(&e) });
        self.timers.backoff_until = Some(now.saturating_add(RELIST_AFTER_MS));
    }

    /// Fire what is due, with a bound on how many sweeps run at once.
    fn fire_due(&mut self, now: u64)
        ensures
            final(self).deep_view() == spec_fire_due(old(self).deep_view(), now),
    {
        proof {
            reveal(spec_fire_due);
        }
        let ghost b0 = self.timers.backlog.deep_view();
        let mut due = self.timers.wheel.take_due(now);
        let ghost d0 = due.deep_view();
        self.timers.backlog.append(&mut due);
        proof {
            assert(self.timers.backlog.deep_view() =~= b0 + d0);
        }
        self.dispatch_due(now);
    }

    fn dispatch_due(&mut self, now: u64)
        ensures
            final(self).deep_view() == spec_dispatch_due(old(self).deep_view(), now, old(self).timers.backlog@.len()),
    {
        let ghost s0 = old(self).deep_view();
        let fuel = self.timers.backlog.len();
        let mut k: usize = 0;
        while k < fuel && self.timers.inflight < CONCURRENCY && self.timers.backlog.len() > 0
            invariant
                k <= fuel,
                spec_dispatch_due(s0, now, fuel as nat) == spec_dispatch_due(self.deep_view(), now, (fuel - k) as nat),
            decreases fuel - k,
        {
            let ghost s1 = self.deep_view();
            let ghost b0 = self.timers.backlog.deep_view();
            let (at, key) = self.timers.backlog.remove(0);
            proof {
                assert(b0[0] == (at, key@));
                assert(self.timers.backlog.deep_view() =~= b0.drop_first());
                assert(self.deep_view() == spec_with_timers(s1, TimersSpec { backlog: s1.timers.backlog.drop_first(), ..s1.timers }));
            }
            self.timer_fire(key, at, now);
            k += 1;
        }
    }

    /// Fire one key: sweep its target if this node owns it, then collect it.
    fn timer_fire(&mut self, key: String, at: u64, now: u64)
        ensures
            final(self).deep_view() == spec_timer_fire(old(self).deep_view(), key@, at, now),
    {
        proof {
            reveal(spec_timer_fire);
        }
        let entry = match self.keys.parse_timer_key(key.as_str()) {
            Some(e) => e,
            None => {
                self.note(Note::KeyUnparseable { key });
                return;
            },
        };
        let kind = match &entry {
            TimerEntry::Origin { .. } => TimerKind::Origin,
            TimerEntry::Schedule { .. } => TimerKind::Schedule,
        };
        let lag = now.saturating_sub(at);
        let owns = self.owns_entry(&entry);
        if !owns || !self.node.core.acts(entry.target().as_str(), now) {
            // Not this node's to fire, or this node cannot tell. The key
            // stays for whoever owns it; if it is still this node's it is
            // listed again on the next membership change.
            if owns {
                self.timers.wheel.arm(max_u64(now, at).saturating_add(RETRY_AFTER_MS), key);
            }
            self.note(Note::TimerFire { kind, outcome: FireOutcome::Deferred, lag_ms: lag });
            return;
        }
        self.timers.inflight = self.timers.inflight.saturating_add(1);
        let firing = Firing { key, at, kind, lag };
        match entry {
            TimerEntry::Origin { origin, deadline, token, by } => {
                let fired = FiredKey { key: Key { origin: concat("w:", origin.as_str()), at: deadline, token }, by };
                // The document handler sweeps the origin.
                self.submit(Target::Origin(origin), Work::Sweep { fired: Some(fired), now }, Some(firing), false);
            },
            TimerEntry::Schedule { id, deadline, token, by } => {
                let fired = FiredKey { key: Key { origin: concat("s:", id.as_str()), at: deadline, token }, by };
                // The schedule handler runs the occurrence.
                self.submit(Target::Schedule(copy_string(&id)), Work::Fire { schedule: id, fired: Some(fired), now }, Some(firing), false);
            },
        }
    }

    /// The flight a key fired is over.
    pub fn timer_op_exhausted(&mut self, firing: &Firing)
        ensures
            final(self).deep_view()
                == spec_timer_op_exhausted(
                    old(self).deep_view(),
                    firing.deep_view(),
                ),
    {
        self.timers.inflight =
            self.timers.inflight.saturating_sub(1);
        let fired_at = firing.at.saturating_add(firing.lag);
        let rearm = max_u64(fired_at, firing.at)
            .saturating_add(RETRY_AFTER_MS);
        self.timers.wheel.arm(
            rearm,
            copy_string(&firing.key),
        );
    }

    /// The flight a key fired is over.
    pub fn timer_fired(&mut self, firing: Firing, now: u64, r: Result<Fired, String>)
        ensures
            final(self).deep_view() == spec_timer_fired(old(self).deep_view(), firing.deep_view(), now, r.deep_view()),
    {
        proof {
            reveal(spec_timer_fired);
        }
        self.timers.inflight = self.timers.inflight.saturating_sub(1);
        let Firing { key, at, kind, lag } = firing;
        let rearm = max_u64(now, at).saturating_add(RETRY_AFTER_MS);
        let outcome = match r {
            Ok(Fired::Deleted) => FireOutcome::Deleted,
            Ok(Fired::Kept) => {
                // The delete failed: it is collected on its next firing.
                self.timers.wheel.arm(rearm, key);
                FireOutcome::Kept
            },
            Err(e) => {
                self.note(Note::FireFailed { key: copy_string(&key), error: e });
                self.timers.wheel.arm(rearm, key);
                FireOutcome::Failed
            },
        };
        self.note(Note::TimerFire { kind, outcome, lag_ms: lag });
        self.dispatch_due(now);
    }
}

} // verus!
