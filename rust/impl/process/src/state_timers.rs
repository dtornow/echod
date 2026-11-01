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

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use crate::types::*;

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

    /// The earliest key, and when it falls due.
    pub fn nearest_key(&self) -> Option<(u64, String)> {
        let (&at, set) = self.armed.iter().next()?;
        Some((at, set.iter().next()?.clone()))
    }

    pub fn len(&self) -> usize {
        self.armed.values().map(BTreeSet::len).sum()
    }
}

/// How long a deadline waits after its sweep failed to commit.
pub(crate) const RETRY_AFTER_MS: u64 = 1_000;
/// How long a failed listing waits before it is tried again.
pub(crate) const RELIST_AFTER_MS: u64 = 1_000;
/// How many sweeps run at once, at most.
pub(crate) const CONCURRENCY: usize = 16;

/// A listing in progress.
pub(crate) enum Listing {
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
    pub(crate) fn expects(&self, op: OpId) -> bool {
        match self {
            Listing::Prefixes { op: o, .. } | Listing::Extend { op: o, .. } | Listing::Relist { op: o, .. } => *o == op,
            Listing::Buckets { pending, .. } => pending.contains_key(&op),
        }
    }
}

pub(crate) struct Timers {
    pub wheel: TimerWheel,
    pub(crate) started: bool,
    /// The start of the last bucket this node has listed. `None` until the
    /// first full load succeeds; nothing fires before that.
    pub(crate) loaded_through: Option<u64>,
    /// The start of the last bucket listed again after the clock left it.
    /// A key armed into a bucket by another node, for a target this node
    /// owns, after this node listed the bucket ahead of the clock, is found
    /// when the bucket closes: so a deadline is swept within a bucket or two
    /// of falling due, whoever armed it.
    pub(crate) closed_through: Option<u64>,
    pub(crate) bucket_ms: u64,
    pub(crate) reload_pending: bool,
    pub(crate) listing: Option<Listing>,
    pub(crate) backoff_until: Option<u64>,
    pub(crate) inflight: usize,
    pub(crate) backlog: VecDeque<(u64, String)>,
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

    /// The next instant the wheel wants a physical wake, and what it is for:
    /// the nearest deadline key when that instant is the key's, otherwise a
    /// listing or a retry, which has no key yet.
    pub fn next_wake(&self, now: u64) -> Option<(u64, crate::types::Armed)> {
        let at = self.wake_at(now)?;
        if let Some((key_at, key)) = self.wheel.nearest_key() {
            if key_at == at {
                return Some((at, crate::types::Armed::Deadline { key }));
            }
        }
        Some((at, crate::types::Armed::Timers))
    }
}

