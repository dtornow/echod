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
use crate::concrete::store::{StoreErrorSpec, StoreReqSpec};

#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_handler_timers_spec_horizon as spec_horizon,
    production_handler_timers_spec_owns as spec_owns,
    production_handler_timers_spec_owns_entry as spec_owns_entry,
    production_handler_timers_spec_owns_key as spec_owns_key,
    production_handler_timers_spec_with_timers as spec_with_timers,
    production_handler_timers_spec_timers_start as spec_timers_start,
    production_handler_timers_spec_timers_membership_changed as spec_timers_membership_changed,
    production_handler_timers_spec_timers_run as spec_timers_run,
    production_handler_timers_spec_reload as spec_reload,
    production_handler_timers_spec_take_bucket as spec_take_bucket,
    production_handler_timers_spec_list_buckets as spec_list_buckets,
    production_handler_timers_spec_timers_completed as spec_timers_completed,
    production_handler_timers_spec_prefixes_listed as spec_prefixes_listed,
    production_handler_timers_spec_bucket_listed as spec_bucket_listed,
    production_handler_timers_spec_extended as spec_extended,
    production_handler_timers_spec_relisted as spec_relisted,
    production_handler_timers_spec_reloaded as spec_reloaded,
    production_handler_timers_spec_listing_failed as spec_listing_failed,
    production_handler_timers_spec_fire_due as spec_fire_due,
    production_handler_timers_spec_dispatch_due as spec_dispatch_due,
    production_handler_timers_spec_timer_fire as spec_timer_fire,
    production_handler_timers_spec_timer_fired as spec_timer_fired,
};

verus! {

// ---------------------------------------------------------------------------
// Stated
// ---------------------------------------------------------------------------

/// The bucket a node must have loaded at `now`: the one after the current,
/// so a deadline in the next bucket is in the wheel before the clock gets
/// there.


/// Does this node own `target` per the members it holds? No while nobody
/// is a member yet.








/// The first configuration is read: load, then fire from the wheel.




/// Load what is owed, else fire what is due.


/// The full load: every bucket at or before the horizon, this node's
/// share. Keys for targets that are no longer this node's leave the wheel;
/// their owner lists them.


/// Take this node's share of a listed bucket into the wheel; `n` counts
/// the keys taken so far.


/// List every bucket at or before the horizon; `pending` collects the ops.




/// The bucket prefixes are listed: list each bucket up to the horizon.


/// One bucket of the full load is listed.


/// The next bucket is listed: the horizon moves.


/// A past bucket is listed again: it is closed.






/// Fire what is due, with a bound on how many sweeps run at once.


/// Fire the backlog, oldest first, while a sweep may start. `fuel` bounds
/// the steps: the backlog's length, which a fire never grows.


/// Fire one key: sweep its target if this node owns it, then collect it.


/// The flight a key fired is over.


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
                let op = self.store(StoreReq::List { prefix, max_keys: usize::MAX }, Owner::Timers);
                self.timers.listing = Some(Listing::Extend { op, bucket });
                return;
            }
        }
        if let Some(c) = self.timers.closed_through {
            let bucket = c.saturating_add(self.keys.bucket_ms());
            if bucket < self.keys.bucket_of(now) {
                // The clock left a bucket this node listed ahead of time: list
                // it once more, for what others armed into it since.
                let prefix = self.keys.bucket_prefix(bucket);
                let op = self.store(StoreReq::List { prefix, max_keys: usize::MAX }, Owner::Timers);
                self.timers.listing = Some(Listing::Relist { op, bucket });
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
        let op = self.store(StoreReq::ListPrefixes { prefix }, Owner::Timers);
        self.timers.listing = Some(Listing::Prefixes { op, horizon });
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
                    let op = self.store(StoreReq::List { prefix, max_keys: usize::MAX }, Owner::Timers);
                    pending.insert(op, bucket);
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
                let fired = FiredKey { key: Key { origin: copy_string(&origin), at: deadline, token }, by };
                // The document handler sweeps the origin.
                self.submit(Target::Origin(origin), Work::Sweep { fired: Some(fired), now }, Some(firing), false);
            },
            TimerEntry::Schedule { id, deadline, token, by } => {
                let fired = FiredKey { key: Key { origin: concat("sched:", id.as_str()), at: deadline, token }, by };
                // The schedule handler runs the occurrence.
                self.submit(Target::Schedule(copy_string(&id)), Work::Fire { schedule: id, fired: Some(fired), now }, Some(firing), false);
            },
        }
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
