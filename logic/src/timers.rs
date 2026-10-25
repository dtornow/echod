//! Deadlines as keys, held in a wheel, fired by the owner.
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
//! flight that armed the key (`flight.rs`). A key whose delete failed
//! fires again. A key for a target this node no longer owns is dropped
//! from the wheel unfired; its owner lists it.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use echod_kernel::node::Key;

use crate::dispatch::Target;
use crate::flight::{Firing, Work};
use crate::keys::TimerEntry;
use crate::types::*;
use crate::{Owner, State};

/// Armed keys by deadline.
#[derive(Default)]
pub struct TimerWheel {
    armed: BTreeMap<u64, BTreeSet<String>>,
}

impl TimerWheel {
    pub fn new() -> Self {
        Self::default()
    }

    /// Hold a key. The same key twice is one key.
    pub fn arm(&mut self, at: u64, key: String) {
        self.armed.entry(at).or_default().insert(key);
    }

    pub fn disarm(&mut self, at: u64, key: &str) {
        if let Some(set) = self.armed.get_mut(&at) {
            set.remove(key);
            if set.is_empty() {
                self.armed.remove(&at);
            }
        }
    }

    /// Everything due at `now`, removed from the wheel.
    pub fn take_due(&mut self, now: u64) -> Vec<(u64, String)> {
        let mut due = Vec::new();
        while let Some((&at, _)) = self.armed.iter().next() {
            if at > now {
                break;
            }
            let set = self.armed.remove(&at).unwrap_or_default();
            due.extend(set.into_iter().map(|k| (at, k)));
        }
        due
    }

    /// Keep only the keys `keep` accepts.
    pub fn retain(&mut self, mut keep: impl FnMut(&str) -> bool) {
        self.armed.retain(|_, set| {
            set.retain(|k| keep(k));
            !set.is_empty()
        });
    }

    pub fn nearest(&self) -> Option<u64> {
        self.armed.keys().next().copied()
    }

    pub fn len(&self) -> usize {
        self.armed.values().map(BTreeSet::len).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// How long a deadline waits after its sweep failed to commit.
const RETRY_AFTER_MS: u64 = 1_000;
/// How long a failed listing waits before it is tried again.
const RELIST_AFTER_MS: u64 = 1_000;
/// How many sweeps run at once, at most.
const CONCURRENCY: usize = 16;

/// A listing in progress.
enum Listing {
    /// The full load: the buckets there are.
    Prefixes { op: OpId, horizon: u64 },
    /// The full load: this node's share of each bucket at or before the horizon.
    Buckets { pending: HashMap<OpId, u64>, horizon: u64, loaded: usize, failed: Option<StoreError> },
    /// One more bucket, as the clock reached it.
    Extend { op: OpId, bucket: u64 },
    /// A bucket the clock has left, listed again: another node may have armed
    /// a key into it for a target this node owns after this node listed it.
    Relist { op: OpId, bucket: u64 },
}

impl Listing {
    fn expects(&self, op: OpId) -> bool {
        match self {
            Listing::Prefixes { op: o, .. } | Listing::Extend { op: o, .. } | Listing::Relist { op: o, .. } => *o == op,
            Listing::Buckets { pending, .. } => pending.contains_key(&op),
        }
    }
}

pub(crate) struct Timers {
    pub wheel: TimerWheel,
    started: bool,
    /// The start of the last bucket this node has listed. `None` until the
    /// first full load succeeds; nothing fires before that.
    loaded_through: Option<u64>,
    /// The start of the last bucket listed again after the clock left it.
    /// A key armed into a bucket by another node, for a target this node
    /// owns, after this node listed the bucket ahead of the clock, is found
    /// when the bucket closes: so a deadline is swept within a bucket or two
    /// of falling due, whoever armed it.
    closed_through: Option<u64>,
    bucket_ms: u64,
    reload_pending: bool,
    listing: Option<Listing>,
    backoff_until: Option<u64>,
    inflight: usize,
    backlog: VecDeque<(u64, String)>,
}

impl Timers {
    pub fn new() -> Self {
        Self { wheel: TimerWheel::new(), started: false, loaded_through: None, closed_through: None, bucket_ms: 0, reload_pending: false, listing: None, backoff_until: None, inflight: 0, backlog: VecDeque::new() }
    }

    /// The earliest instant the timers want to look at the clock: a
    /// backoff's end, a reload owed, the nearest deadline, or the clock
    /// reaching the last bucket loaded.
    pub fn wake_at(&self, now: u64) -> Option<u64> {
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
        let closing = self.closed_through.map(|c| c.saturating_add(2 * self.bucket_ms).max(now));
        [self.wheel.nearest(), self.loaded_through.map(|t| t.max(now)), closing].into_iter().flatten().min()
    }
}

impl State {
    /// The bucket a node must have loaded at `now`: the one after the
    /// current, so a deadline in the next bucket is in the wheel before the
    /// clock gets there.
    fn horizon(&self, now: u64) -> u64 {
        self.keys.bucket_of(now.saturating_add(self.keys.bucket_ms()))
    }

    fn owns_entry(&self, e: &TimerEntry) -> bool {
        self.owns(e.target())
    }

    fn owns_key(&self, key: &str) -> bool {
        self.keys.parse_timer_key(key).map(|e| self.owns_entry(&e)).unwrap_or(false)
    }

    /// The first configuration is read: load, then fire from the wheel.
    pub(crate) fn timers_start(&mut self, now: u64) {
        self.timers.started = true;
        self.timers.bucket_ms = self.keys.bucket_ms();
        self.timers.reload_pending = true;
        self.timers_run(now);
    }

    pub(crate) fn timers_membership_changed(&mut self) {
        self.timers.reload_pending = true;
    }

    /// Load what is owed, else fire what is due. Called whenever time
    /// passed or a listing ended.
    pub(crate) fn timers_run(&mut self, now: u64) {
        if !self.timers.started || self.timers.listing.is_some() {
            return;
        }
        if let Some(b) = self.timers.backoff_until {
            if now < b {
                return;
            }
            self.timers.backoff_until = None;
        }
        if self.timers.reload_pending {
            self.reload(now);
        } else if let Some(through) = self.timers.loaded_through.filter(|t| *t < self.horizon(now)) {
            // Bring the loaded range up to the horizon, one bucket at a time.
            let bucket = through + self.keys.bucket_ms();
            let op = self.store(StoreCall::List { prefix: self.keys.bucket_prefix(bucket), max_keys: usize::MAX }, Owner::Timers);
            self.timers.listing = Some(Listing::Extend { op, bucket });
        } else if let Some(bucket) = self.timers.closed_through.map(|c| c + self.keys.bucket_ms()).filter(|b| *b < self.keys.bucket_of(now)) {
            // The clock left a bucket this node listed ahead of time: list it
            // once more, for what others armed into it since.
            let op = self.store(StoreCall::List { prefix: self.keys.bucket_prefix(bucket), max_keys: usize::MAX }, Owner::Timers);
            self.timers.listing = Some(Listing::Relist { op, bucket });
        } else if self.timers.loaded_through.is_some() {
            self.fire_due(now);
        }
    }

    /// The full load: every bucket at or before the horizon, this node's
    /// share. Keys for targets that are no longer this node's leave the
    /// wheel; their owner lists them.
    fn reload(&mut self, now: u64) {
        let horizon = self.horizon(now);
        let mut wheel = std::mem::take(&mut self.timers.wheel);
        wheel.retain(|k| self.owns_key(k));
        self.timers.wheel = wheel;
        let op = self.store(StoreCall::ListPrefixes { prefix: self.keys.timer_prefix() }, Owner::Timers);
        self.timers.listing = Some(Listing::Prefixes { op, horizon });
    }

    /// Take this node's share of a listed bucket into the wheel.
    fn take_bucket(&mut self, keys: Vec<String>) -> usize {
        let mut n = 0;
        for key in keys {
            if let Some(e) = self.keys.parse_timer_key(&key) {
                if self.owns_entry(&e) {
                    self.timers.wheel.arm(e.deadline(), key);
                    n += 1;
                }
            }
        }
        n
    }

    pub(crate) fn timers_completed(&mut self, op: OpId, outcome: StoreOutcome) {
        let Some(listing) = self.timers.listing.take() else { return };
        if !listing.expects(op) {
            self.timers.listing = Some(listing);
            return;
        }
        let now = self.now();
        match listing {
            Listing::Prefixes { horizon, .. } => match outcome {
                StoreOutcome::Listed(prefixes) => {
                    let mut pending = HashMap::new();
                    for p in prefixes {
                        let Some(bucket) = self.keys.parse_bucket_prefix(&p) else { continue };
                        if bucket <= horizon {
                            let op = self.store(StoreCall::List { prefix: self.keys.bucket_prefix(bucket), max_keys: usize::MAX }, Owner::Timers);
                            pending.insert(op, bucket);
                        }
                    }
                    if pending.is_empty() {
                        self.reloaded(horizon, 0, now);
                    } else {
                        self.timers.listing = Some(Listing::Buckets { pending, horizon, loaded: 0, failed: None });
                    }
                }
                StoreOutcome::Failed(e) => self.listing_failed(e, now),
                _ => self.listing_failed(unexpected(), now),
            },
            Listing::Buckets { mut pending, horizon, mut loaded, mut failed } => {
                pending.remove(&op);
                match outcome {
                    StoreOutcome::Listed(keys) => loaded += self.take_bucket(keys),
                    StoreOutcome::Failed(e) => failed = Some(e),
                    _ => failed = Some(unexpected()),
                }
                if !pending.is_empty() {
                    self.timers.listing = Some(Listing::Buckets { pending, horizon, loaded, failed });
                } else if let Some(e) = failed {
                    self.listing_failed(e, now);
                } else {
                    self.reloaded(horizon, loaded, now);
                }
            }
            Listing::Extend { bucket, .. } => match outcome {
                StoreOutcome::Listed(keys) => {
                    let n = self.take_bucket(keys);
                    self.note(Note::BucketLoaded { bucket, deadlines: n });
                    self.note(Note::TimerListing { ok: true });
                    self.timers.loaded_through = Some(bucket);
                    self.timers_run(now);
                }
                StoreOutcome::Failed(e) => self.listing_failed(e, now),
                _ => self.listing_failed(unexpected(), now),
            },
            Listing::Relist { bucket, .. } => match outcome {
                StoreOutcome::Listed(keys) => {
                    let n = self.take_bucket(keys);
                    self.note(Note::BucketLoaded { bucket, deadlines: n });
                    self.note(Note::TimerListing { ok: true });
                    self.timers.closed_through = Some(bucket);
                    self.timers_run(now);
                }
                StoreOutcome::Failed(e) => self.listing_failed(e, now),
                _ => self.listing_failed(unexpected(), now),
            },
        }
    }

    fn reloaded(&mut self, horizon: u64, loaded: usize, now: u64) {
        self.timers.loaded_through = Some(horizon);
        // the full load covered every bucket up to now; the current one is
        // listed again when it closes
        self.timers.closed_through = Some(self.keys.bucket_of(now).saturating_sub(self.keys.bucket_ms()));
        self.timers.reload_pending = false;
        self.note(Note::TimerListing { ok: true });
        self.note(Note::TimersLoaded { deadlines: loaded, wheel: self.timers.wheel.len(), epoch: self.core.epoch });
        self.timers_run(now);
    }

    fn listing_failed(&mut self, e: StoreError, now: u64) {
        self.note(Note::TimerListing { ok: false });
        self.note(Note::ListingFailed { error: e.to_string() });
        self.timers.backoff_until = Some(now + RELIST_AFTER_MS);
    }

    /// Fire what is due, with a bound on how many sweeps run at once.
    fn fire_due(&mut self, now: u64) {
        let due = self.timers.wheel.take_due(now);
        self.timers.backlog.extend(due);
        self.dispatch_due(now);
    }

    fn dispatch_due(&mut self, now: u64) {
        while self.timers.inflight < CONCURRENCY {
            let Some((at, key)) = self.timers.backlog.pop_front() else { break };
            self.timer_fire(key, at, now);
        }
    }

    /// Fire one key: sweep its target if this node owns it, then collect it.
    fn timer_fire(&mut self, key: String, at: u64, now: u64) {
        let Some(entry) = self.keys.parse_timer_key(&key) else {
            self.note(Note::KeyUnparseable { key });
            return;
        };
        let kind = match &entry {
            TimerEntry::Origin { .. } => TimerKind::Origin,
            TimerEntry::Schedule { .. } => TimerKind::Schedule,
        };
        let lag = now.saturating_sub(at);
        let owns = self.owns_entry(&entry);
        if !owns || !self.core.acts(entry.target(), now) {
            // Not this node's to fire, or this node cannot tell. The key
            // stays for whoever owns it; if it is still this node's it is
            // listed again on the next membership change.
            if owns {
                self.timers.wheel.arm(now.max(at) + RETRY_AFTER_MS, key);
            }
            self.note(Note::TimerFire { kind, outcome: FireOutcome::Deferred, lag_ms: lag });
            return;
        }
        self.timers.inflight += 1;
        let firing = Firing { key, at, kind, lag };
        match entry {
            TimerEntry::Origin { origin, deadline, token, by } => {
                let fired = FiredKey { key: Key { origin: origin.clone(), at: deadline, token }, by };
                self.submit(Target::Origin(origin), Work::Sweep { fired: Some(fired), now }, Some(firing), false);
            }
            TimerEntry::Schedule { id, deadline, token, by } => {
                let fired = FiredKey { key: Key { origin: format!("sched:{id}"), at: deadline, token }, by };
                self.submit(Target::Schedule(id.clone()), Work::Fire { schedule: id, fired: Some(fired), now }, Some(firing), false);
            }
        }
    }

    /// The flight a key fired is over.
    pub(crate) fn timer_fired(&mut self, firing: Firing, now: u64, r: Result<Fired, resonate_core::Unavailable>) {
        self.timers.inflight = self.timers.inflight.saturating_sub(1);
        let outcome = match r {
            Ok(Fired::Deleted) => FireOutcome::Deleted,
            Ok(Fired::Kept) => {
                // The delete failed: it is collected on its next firing.
                self.timers.wheel.arm(now.max(firing.at) + RETRY_AFTER_MS, firing.key);
                FireOutcome::Kept
            }
            Err(e) => {
                self.note(Note::FireFailed { key: firing.key.clone(), error: e.message });
                self.timers.wheel.arm(now.max(firing.at) + RETRY_AFTER_MS, firing.key);
                FireOutcome::Failed
            }
        };
        self.note(Note::TimerFire { kind: firing.kind, outcome, lag_ms: firing.lag });
        self.dispatch_due(now);
    }
}

fn unexpected() -> StoreError {
    StoreError::Unavailable("the store answered something else".into())
}
