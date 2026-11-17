//! Which keys are due. A due origin goes to the document handler; a due
//! schedule goes to the schedule handler. The listing that fills the wheel
//! lives here too: the wheel decides, the store answers come back here.

use vstd::prelude::*;

use crate::verified::flight::FiredKey;
use crate::verified::node::Key;
use crate::verified::text::{concat, copy_string};

use crate::handler_docs::{take_opt, Firing, Work};
use crate::keys::TimerEntry;
use crate::state::{Owner, State};
use crate::state_timers::{AfterListing, Listing, TimerScan, CONCURRENCY, RELIST_AFTER_MS, RETRY_AFTER_MS};
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
    production_handler_timers_spec_start_bucket as spec_start_bucket,
    production_handler_timers_spec_advance_scan as spec_advance_scan,
    production_handler_timers_spec_finish_listing as spec_finish_listing,
    production_handler_timers_spec_apply_listing as spec_apply_listing,
    production_handler_timers_spec_timers_completed as spec_timers_completed,
    production_handler_timers_spec_prefixes_listed as spec_prefixes_listed,
    production_handler_timers_spec_bucket_listed as spec_bucket_listed,
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
        if !self.timers.started {
            return;
        }
        if let Some(b) = self.timers.backoff_until {
            if now < b {
                if self.timers.loaded_through.is_some() { self.fire_due(now); }
                return;
            }
        }
        self.timers.backoff_until = None;
        if let Some(listing) = take_opt(&mut self.timers.listing) {
            match listing {
                Listing::Scan { scan } => self.advance_scan(scan, now),
                Listing::Applying { keys, loaded, after } => self.apply_listing(keys, loaded, after, now),
                Listing::Retry { after } => self.start_bucket(after),
                other => self.timers.listing = Some(other),
            }
            if self.timers.loaded_through.is_some() { self.fire_due(now); }
            return;
        }
        let rediscover = match self.timers.rediscover_at { Some(at) => at <= now, None => false };
        if self.timers.reload_pending || rediscover {
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
        self.timers.rediscover_at = Some(now.saturating_add(self.cfg.timer_rediscovery_ms));
        self.timers.reload_pending = true;
        let prefix = self.keys.timer_prefix();
        let op = self.store(StoreReq::ListPrefixes { prefix }, Owner::Timers);
        self.timers.listing = Some(Listing::Prefixes { op, horizon });
    }

    fn start_bucket(&mut self, after: AfterListing)
        ensures final(self).deep_view() == spec_start_bucket(old(self).deep_view(), after.deep_view()),
    {
        let bucket = match &after {
            AfterListing::Scan { bucket, .. } | AfterListing::Extend { bucket } | AfterListing::Relist { bucket } => *bucket,
        };
        let prefix = self.keys.bucket_prefix(bucket);
        let op = self.store(StoreReq::List { prefix, max_keys: usize::MAX }, Owner::Timers);
        self.timers.listing = Some(match after {
            AfterListing::Scan { bucket, scan } => Listing::Bucket { op, bucket, scan },
            AfterListing::Extend { bucket } => Listing::Extend { op, bucket },
            AfterListing::Relist { bucket } => Listing::Relist { op, bucket },
        });
    }

    fn advance_scan(&mut self, input: TimerScan, now: u64)
        ensures final(self).deep_view() == spec_advance_scan(old(self).deep_view(), input.deep_view(), now, 32),
    {
        let ghost start = old(self).deep_view();
        let ghost original = input.deep_view();
        let mut scan = input;
        let mut fuel: usize = 32;
        while scan.prefixes.len() > 0 && fuel > 0 && self.timers.budget > 0
            invariant
                fuel <= 32,
                start == old(self).deep_view(),
                original == input.deep_view(),
                spec_advance_scan(start, original, now, 32) == spec_advance_scan(self.deep_view(), scan.deep_view(), now, fuel as nat),
            decreases fuel,
        {
            let ghost before = self.deep_view();
            let ghost current = scan.deep_view();
            let ghost previous_fuel = fuel;
            let ghost prefixes = scan.prefixes.deep_view();
            let prefix = scan.prefixes.pop().unwrap();
            proof {
                assert(prefix@ == prefixes.last());
                assert(scan.prefixes.deep_view() =~= prefixes.drop_last());
            }
            self.timers.budget -= 1;
            fuel -= 1;
            if let Some(bucket) = self.keys.parse_bucket_prefix(prefix.as_str()) {
                if bucket <= scan.horizon {
                    proof {
                        assert(spec_advance_scan(before, current, now, previous_fuel as nat)
                            == spec_start_bucket(self.deep_view(), AfterListingSpec::Scan { bucket, scan: scan.deep_view() }));
                    }
                    self.start_bucket(AfterListing::Scan { bucket, scan });
                    return;
                }
            }
        }
        if scan.prefixes.len() == 0 {
            self.reloaded(scan.horizon, scan.loaded, now);
        } else {
            self.timers.listing = Some(Listing::Scan { scan });
        }
    }

    fn finish_listing(&mut self, after: AfterListing, loaded: usize, now: u64)
        ensures final(self).deep_view() == spec_finish_listing(old(self).deep_view(), after.deep_view(), loaded, now),
    {
        match after {
            AfterListing::Scan { mut scan, .. } => {
                scan.loaded = scan.loaded.saturating_add(loaded);
                if scan.prefixes.len() == 0 { self.reloaded(scan.horizon, scan.loaded, now); }
                else { self.timers.listing = Some(Listing::Scan { scan }); }
            },
            AfterListing::Extend { bucket } => {
                self.note(Note::BucketLoaded { bucket, deadlines: loaded });
                self.note(Note::TimerListing { ok: true });
                self.timers.loaded_through = Some(bucket);
            },
            AfterListing::Relist { bucket } => {
                self.note(Note::BucketLoaded { bucket, deadlines: loaded });
                self.note(Note::TimerListing { ok: true });
                self.timers.closed_through = Some(bucket);
            },
        }
    }

    fn apply_listing(&mut self, mut keys: Vec<String>, mut loaded: usize, after: AfterListing, now: u64)
        ensures final(self).deep_view() == spec_apply_listing(old(self).deep_view(), keys.deep_view(), loaded, after.deep_view(), now, 32),
    {
        let ghost start = old(self).deep_view();
        let ghost original = keys.deep_view();
        let ghost original_loaded = loaded;
        let mut fuel: usize = 32;
        while keys.len() > 0 && fuel > 0 && self.timers.budget > 0
            invariant
                fuel <= 32,
                spec_apply_listing(start, original, original_loaded, after.deep_view(), now, 32)
                    == spec_apply_listing(self.deep_view(), keys.deep_view(), loaded, after.deep_view(), now, fuel as nat),
            decreases fuel,
        {
            let ghost before = keys.deep_view();
            let key = keys.pop().unwrap();
            proof {
                assert(key@ == before.last());
                assert(keys.deep_view() =~= before.drop_last());
            }
            self.timers.budget -= 1;
            fuel -= 1;
            if let Some(entry) = self.keys.parse_timer_key(key.as_str()) {
                if self.owns_entry(&entry) {
                    self.timers.wheel.arm(entry.deadline(), key);
                    loaded = loaded.saturating_add(1);
                }
            }
        }
        if keys.len() == 0 { self.finish_listing(after, loaded, now); }
        else { self.timers.listing = Some(Listing::Applying { keys, loaded, after }); }
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
            Listing::Bucket { bucket, scan, .. } => self.bucket_listed(AfterListing::Scan { bucket, scan }, now, outcome),
            Listing::Extend { bucket, .. } => self.bucket_listed(AfterListing::Extend { bucket }, now, outcome),
            Listing::Relist { bucket, .. } => self.bucket_listed(AfterListing::Relist { bucket }, now, outcome),
            _ => {},
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
                self.timers.listing = Some(Listing::Scan { scan: TimerScan { prefixes, horizon, loaded: 0 } });
                self.timers_run(now);
            },
            StoreRes::ListPrefixes { result: Err(e) } => self.listing_failed(e, now),
            _ => self.listing_failed(unexpected(), now),
        }
    }

    fn bucket_listed(&mut self, after: AfterListing, now: u64, outcome: StoreRes)
        ensures
            final(self).deep_view() == spec_bucket_listed(old(self).deep_view(), after.deep_view(), now, outcome),
    {
        proof {
            reveal(spec_bucket_listed);
        }
        match outcome {
            StoreRes::List { result: Ok(keys) } => {
                self.timers.listing = Some(Listing::Applying { keys, loaded: 0, after });
                self.timers_run(now);
            },
            StoreRes::List { result: Err(e) } => {
                self.timers.listing = Some(Listing::Retry { after });
                self.listing_failed(e, now);
            },
            _ => {
                self.timers.listing = Some(Listing::Retry { after });
                self.listing_failed(unexpected(), now);
            },
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
        let limit = if self.timers.inflight < CONCURRENCY && self.timers.backlog.len() == 0 { self.timers.budget / 2 } else { 0 };
        let mut due = self.timers.wheel.take_due(now, limit);
        let ghost d0 = due.deep_view();
        self.timers.budget -= due.len();
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
        while k < fuel && self.timers.budget > 0 && self.timers.inflight < CONCURRENCY && self.timers.backlog.len() > 0
            invariant
                k <= fuel,
                spec_dispatch_due(s0, now, fuel as nat) == spec_dispatch_due(self.deep_view(), now, (fuel - k) as nat),
            decreases fuel - k,
        {
            let ghost s1 = self.deep_view();
            let ghost b0 = self.timers.backlog.deep_view();
            let (at, key) = self.timers.backlog.pop_front().unwrap();
            self.timers.budget -= 1;
            proof {
                assert(b0[0] == (at, key@));
                assert(self.timers.backlog.deep_view() =~= b0.drop_first());
                assert(self.deep_view() == spec_with_timers(s1, TimersSpec { backlog: s1.timers.backlog.drop_first(), budget: (s1.timers.budget - 1) as usize, ..s1.timers }));
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

#[cfg(test)]
mod tests {
    use crate::{Config, State};
    use crate::state_timers::TIMER_WORK_BUDGET;
    use crate::types::{Armed, Effect, Event, StoreError, StoreReq, StoreRes};
    use super::{AfterListing, Listing, TimerScan};

    fn active_state(now: u64) -> State {
        let mut state = State::new(Config::memory("node"));
        state.loops = true;
        state.node.core.read_config(now, 1, vec!["node".into()]);
        state.node.members.next_heartbeat = Some(now + 5_000);
        state.timers.started = true;
        state.timers.bucket_ms = 3_600_000;
        state.timers.loaded_through = Some(3_600_000);
        state.timers.closed_through = Some(0);
        state.timers.rediscover_at = Some(now + 300_000);
        state
    }

    #[test]
    fn bucket_application_yields_to_real_wakes() {
        let now = 3_600_000;
        let mut state = active_state(now);
        let keys = (0..1_000).map(|i| state.keys.timer_key(&format!("origin-{i}"), 7_200_000, 1, "node")).collect();
        state.timers.listing = Some(Listing::Applying { keys, loaded: 0, after: AfterListing::Extend { bucket: 7_200_000 } });
        let mut clock = now;
        let mut applied = 0;
        while state.timers.listing.is_some() {
            let effects = state.on_event(Event::Wake { clock, armed: Armed::Wheel });
            let next = state.timers.wheel.len();
            assert!(next > applied && next - applied <= 32);
            assert!(state.timers.budget >= 32);
            applied = next;
            if state.timers.listing.is_some() {
                let delay = effects.iter().find_map(|effect| match effect {
                    Effect::Wake { after_ms, armed: Armed::Wheel } => Some(*after_ms),
                    _ => None,
                }).expect("application continuation must emit a physical wake");
                assert_eq!(delay, 1);
                clock += delay;
            }
        }
        assert_eq!(applied, 1_000);
        assert_eq!(state.timers.loaded_through, Some(7_200_000));
    }

    #[test]
    fn prefix_processing_is_bounded_and_bucket_retries_preserve_progress() {
        let now = 3_600_000;
        let mut state = active_state(now);
        let mut prefixes = vec![state.keys.bucket_prefix(0), state.keys.bucket_prefix(3_600_000)];
        prefixes.extend((0..100).map(|i| format!("invalid-{i}")));
        state.timers.listing = Some(Listing::Scan { scan: TimerScan { prefixes, horizon: 7_200_000, loaded: 0 } });
        let mut clock = now;
        let (op, request) = loop {
            let effects = state.on_event(Event::Wake { clock, armed: Armed::Wheel });
            let stores: Vec<_> = effects.iter().filter_map(|effect| match effect {
                Effect::Store { op, request: StoreReq::List { prefix, .. } } => Some((*op, prefix.clone())),
                _ => None,
            }).collect();
            assert!(stores.len() <= 1);
            assert!(state.timers.budget >= 32);
            if let Some(store) = stores.into_iter().next() { break store; }
            let delay = effects.iter().find_map(|effect| match effect {
                Effect::Wake { after_ms, armed: Armed::Wheel } => Some(*after_ms),
                _ => None,
            }).expect("prefix continuation must emit a physical wake");
            assert_eq!(delay, 1);
            clock += delay;
        };
        let effects = state.on_event(Event::Wake { clock: clock + 1, armed: Armed::Wheel });
        assert!(!effects.iter().any(|effect| matches!(effect, Effect::Store { .. })));
        clock += 2;
        state.on_event(Event::Store { clock, op, response: StoreRes::List { result: Err(StoreError::Unavailable("retry".into())) } });
        assert!(matches!(state.timers.listing, Some(Listing::Retry { .. })));
        assert_eq!(state.timers.loaded_through, Some(3_600_000));
        assert_eq!(state.timers.backoff_until, Some(clock + 1_000));
        let effects = state.on_event(Event::Wake { clock: clock + 1_000, armed: Armed::Wheel });
        let retried = effects.iter().find_map(|effect| match effect {
            Effect::Store { request: StoreReq::List { prefix, .. }, .. } => Some(prefix),
            _ => None,
        }).unwrap();
        assert_eq!(retried, &request);
        assert!(matches!(state.timers.listing, Some(Listing::Bucket { ref scan, .. }) if scan.prefixes.len() == 1));
    }

    #[test]
    fn repeated_dispatch_shares_the_same_event_budget() {
        let mut state = State::new(Config::memory("node"));
        state.timers.budget = TIMER_WORK_BUDGET;
        for i in 0..1_000 {
            state.timers.backlog.push_back((0, format!("unparseable-{i}")));
        }
        state.dispatch_due(0);
        assert_eq!(state.timers.backlog.len(), 1_000 - TIMER_WORK_BUDGET);
        assert_eq!(state.timers.budget, 0);
        state.dispatch_due(0);
        assert_eq!(state.timers.backlog.len(), 1_000 - TIMER_WORK_BUDGET);
    }

    #[test]
    fn saturated_concurrency_does_not_extract_more_due_keys() {
        let mut state = State::new(Config::memory("node"));
        state.timers.budget = TIMER_WORK_BUDGET;
        state.timers.inflight = super::CONCURRENCY;
        state.timers.wheel.arm(0, "unparseable".into());
        state.fire_due(0);
        assert_eq!(state.timers.wheel.len(), 1);
        assert!(state.timers.backlog.is_empty());
        assert_eq!(state.timers.budget, TIMER_WORK_BUDGET);
    }

    #[test]
    fn rediscovery_coalesces_missed_start_intervals_without_overlap() {
        let mut cfg = Config::memory("node");
        cfg.timer_rediscovery_ms = 2_500;
        let mut state = State::new(cfg);
        state.timers.started = true;
        state.timers.loaded_through = Some(7_200_000);
        state.timers.rediscover_at = Some(3_600_000);
        state.timers.budget = TIMER_WORK_BUDGET;
        state.timers_run(3_600_000);
        assert!(matches!(state.timers.listing, Some(super::Listing::Prefixes { .. })));
        assert_eq!(state.timers.rediscover_at, Some(3_602_500));
        let effects = state.out.len();
        state.timers_run(3_610_000);
        assert_eq!(state.out.len(), effects);
        state.timers.listing = None;
        state.reloaded(7_200_000, 0, 3_610_000);
        assert!(state.timers.listing.is_none());
        assert_eq!(state.timers.wake_at(3_610_000), Some(3_602_500));
        state.timers_run(3_610_001);
        assert!(matches!(state.timers.listing, Some(super::Listing::Prefixes { .. })));
        assert_eq!(state.timers.rediscover_at, Some(3_612_501));
    }
}
