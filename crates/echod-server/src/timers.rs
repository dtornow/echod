//! Deadlines as objects, fired by the owner from memory.
//!
//! A deadline is an empty object whose key says what is due and when, filed
//! under the time bucket its deadline falls in. Every writer puts the key
//! before the state that arms it and holds it in its wheel after.
//!
//! The wheel is where firing happens. A node lists the bucket in exactly three
//! situations: at startup, when the set of live nodes changes (ownership is
//! `hash mod n`, so every node's share moved), and when the clock reaches a
//! bucket it has not loaded yet. Each listing takes the keys whose target this
//! node owns and nothing else. Between listings no store call is made to find
//! out what is due: the wheel knows.
//!
//! Firing a key sweeps its target, which is idempotent; the key is deleted
//! only once the sweep has committed, since until then it is the only record
//! that the deadline exists. A key for a target this node no longer owns is
//! dropped from the wheel unfired; its owner lists it.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use tokio::sync::Notify;

use crate::applier::Applier;
use crate::keys::{KeySpace, TimerEntry};
use crate::nodes::Nodes;
use crate::schedules::Schedules;
use crate::store::Store;

/// Armed keys by deadline.
pub struct TimerWheel {
    armed: Mutex<BTreeMap<u64, BTreeSet<String>>>,
    nearer: Notify,
}

impl TimerWheel {
    pub fn new() -> Self {
        Self { armed: Mutex::new(BTreeMap::new()), nearer: Notify::new() }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, BTreeMap<u64, BTreeSet<String>>> {
        self.armed.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Hold a key. The same key twice is one key.
    pub fn arm(&self, at: u64, key: String) {
        let mut w = self.lock();
        let nearest = w.keys().next().copied();
        w.entry(at).or_default().insert(key);
        if nearest.map_or(true, |n| at < n) {
            self.nearer.notify_one();
        }
    }

    pub fn disarm(&self, at: u64, key: &str) {
        let mut w = self.lock();
        if let Some(set) = w.get_mut(&at) {
            set.remove(key);
            if set.is_empty() {
                w.remove(&at);
            }
        }
    }

    /// Everything due at `now`, removed from the wheel.
    pub fn take_due(&self, now: u64) -> Vec<(u64, String)> {
        let mut w = self.lock();
        let mut due = Vec::new();
        while let Some((&at, _)) = w.iter().next() {
            if at > now {
                break;
            }
            let set = w.remove(&at).unwrap_or_default();
            due.extend(set.into_iter().map(|k| (at, k)));
        }
        due
    }

    /// Keep only the keys `keep` accepts.
    pub fn retain(&self, mut keep: impl FnMut(&str) -> bool) {
        let mut w = self.lock();
        w.retain(|_, set| {
            set.retain(|k| keep(k));
            !set.is_empty()
        });
    }

    pub fn nearest(&self) -> Option<u64> {
        self.lock().keys().next().copied()
    }

    pub fn len(&self) -> usize {
        self.lock().values().map(BTreeSet::len).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Default for TimerWheel {
    fn default() -> Self {
        Self::new()
    }
}

/// How long a deadline waits after its sweep failed to commit.
const RETRY_AFTER_MS: u64 = 1_000;
/// How long a failed listing waits before it is tried again.
const RELIST_AFTER: Duration = Duration::from_secs(1);

pub struct Timers {
    store: Arc<dyn Store>,
    keys: KeySpace,
    wheel: Arc<TimerWheel>,
    nodes: Arc<Nodes>,
    applier: Arc<Applier>,
    schedules: Arc<Schedules>,
    /// The start of the last bucket this node has listed. `None` until the
    /// first full load succeeds; nothing fires before that.
    loaded_through: Mutex<Option<u64>>,
}

impl Timers {
    pub fn new(store: Arc<dyn Store>, keys: KeySpace, wheel: Arc<TimerWheel>, nodes: Arc<Nodes>, applier: Arc<Applier>, schedules: Arc<Schedules>) -> Self {
        Self { store, keys, wheel, nodes, applier, schedules, loaded_through: Mutex::new(None) }
    }

    pub fn wheel(&self) -> &Arc<TimerWheel> {
        &self.wheel
    }

    /// The bucket a node must have loaded at `now`: the one after the
    /// current, so a deadline in the next bucket is in the wheel before the
    /// clock gets there.
    fn horizon(&self, now: u64) -> u64 {
        self.keys.bucket_of(now.saturating_add(self.keys.bucket_ms()))
    }

    fn loaded_through(&self) -> Option<u64> {
        *self.loaded_through.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn owns(&self, e: &TimerEntry) -> bool {
        self.nodes.owns(e.target())
    }

    fn owns_key(&self, key: &str) -> bool {
        self.keys.parse_timer_key(key).map(|e| self.owns(&e)).unwrap_or(false)
    }

    /// Take this node's share of one bucket into the wheel.
    async fn load_bucket(&self, bucket: u64) -> Result<usize, crate::store::StoreError> {
        let keys = self.store.list(&self.keys.bucket_prefix(bucket), usize::MAX).await?;
        let mut n = 0;
        for key in keys {
            if let Some(e) = self.keys.parse_timer_key(&key) {
                if self.owns(&e) {
                    self.wheel.arm(e.deadline(), key);
                    n += 1;
                }
            }
        }
        Ok(n)
    }

    /// The full load: every bucket at or before the horizon, this node's
    /// share. Run at startup and whenever ownership changes.
    pub async fn reload(&self, now: u64) -> Result<(), crate::store::StoreError> {
        let horizon = self.horizon(now);
        let prefixes = self.store.list_prefixes(&self.keys.timer_prefix()).await?;
        // Keys for targets that are no longer this node's leave the wheel;
        // their owner lists them.
        self.wheel.retain(|k| self.owns_key(k));
        let mut loaded = 0;
        for p in prefixes {
            let Some(bucket) = self.keys.parse_bucket_prefix(&p) else { continue };
            if bucket <= horizon {
                loaded += self.load_bucket(bucket).await?;
            }
        }
        *self.loaded_through.lock().unwrap_or_else(|e| e.into_inner()) = Some(horizon);
        tracing::info!(deadlines = loaded, wheel = self.wheel.len(), epoch = self.nodes.members().epoch, "timers loaded");
        Ok(())
    }

    /// Bring the loaded range up to the horizon, one bucket at a time.
    async fn extend(&self, now: u64) -> Result<(), crate::store::StoreError> {
        let horizon = self.horizon(now);
        loop {
            let Some(through) = self.loaded_through() else { return Ok(()) };
            if through >= horizon {
                return Ok(());
            }
            let next = through + self.keys.bucket_ms();
            let n = self.load_bucket(next).await?;
            tracing::debug!(bucket = next, deadlines = n, "timer bucket loaded");
            *self.loaded_through.lock().unwrap_or_else(|e| e.into_inner()) = Some(next);
        }
    }

    /// Fire one key: sweep its target if this node owns it, then collect it.
    async fn fire(&self, key: &str, at: u64, now: u64) {
        let Some(entry) = self.keys.parse_timer_key(key) else {
            tracing::warn!(key = %key, "unparseable timer key dropped");
            return;
        };
        if !self.owns(&entry) || !self.nodes.acts(entry.target(), now) {
            // Not this node's to fire, or this node cannot tell. The key
            // stays for whoever owns it; if it is still this node's it is
            // listed again on the next membership change.
            if self.owns(&entry) {
                self.wheel.arm(now.max(at) + RETRY_AFTER_MS, key.to_string());
            }
            return;
        }
        let swept = match &entry {
            TimerEntry::Origin { origin, .. } => self.applier.sweep(origin, now).await,
            TimerEntry::Schedule { id, deadline, .. } => self.schedules.fire(id, *deadline, now).await,
        };
        match swept {
            Ok(()) => {
                let target = match &entry {
                    TimerEntry::Origin { origin, .. } => origin.clone(),
                    TimerEntry::Schedule { id, .. } => format!("sched:{id}"),
                };
                self.applier.collected(&target, key);
                if let Err(e) = self.store.delete(key).await {
                    tracing::debug!(key = %key, error = %e, "timer key not collected");
                }
            }
            Err(e) => {
                tracing::warn!(key = %key, error = %e, "sweep failed; the key stays");
                self.wheel.arm(now.max(at) + RETRY_AFTER_MS, key.to_string());
            }
        }
    }

    /// Fire what is due, with a bound on how many sweeps run at once.
    async fn fire_due(self: &Arc<Self>, now: u64) {
        const CONCURRENCY: usize = 16;
        let due = self.wheel.take_due(now);
        for chunk in due.chunks(CONCURRENCY) {
            let mut set = tokio::task::JoinSet::new();
            for (at, key) in chunk.iter().cloned() {
                let me = Arc::clone(self);
                set.spawn(async move { me.fire(&key, at, now).await });
            }
            while set.join_next().await.is_some() {}
        }
    }

    /// The loop: load, then fire from the wheel; list again only on a change
    /// of membership or when the clock reaches an unloaded bucket.
    pub fn spawn(self: Arc<Self>, mut shutdown: tokio::sync::watch::Receiver<bool>) -> tokio::task::JoinHandle<()> {
        tokio::spawn(async move {
            let mut generations = self.nodes.generations();
            generations.borrow_and_update();
            let mut reload_pending = true;
            loop {
                let now = self.nodes.now();
                let mut backoff = None;
                if reload_pending {
                    match self.reload(now).await {
                        Ok(()) => reload_pending = false,
                        Err(e) => {
                            tracing::warn!(error = %e, "timer load failed; will retry");
                            backoff = Some(RELIST_AFTER);
                        }
                    }
                } else if let Err(e) = self.extend(now).await {
                    tracing::warn!(error = %e, "timer bucket listing failed; will retry");
                    backoff = Some(RELIST_AFTER);
                }
                if self.loaded_through().is_some() && !reload_pending {
                    self.fire_due(now).await;
                }
                let now = self.nodes.now();
                let next_bucket = self.loaded_through().map(|t| t.max(now));
                let wake_at = [self.wheel.nearest(), next_bucket].into_iter().flatten().min();
                let wait = match (backoff, wake_at) {
                    (Some(b), _) => b,
                    (None, Some(at)) => Duration::from_millis(at.saturating_sub(now)).max(Duration::from_millis(1)),
                    (None, None) => Duration::from_secs(3600),
                };
                tokio::select! {
                    biased;
                    _ = shutdown.changed() => return,
                    _ = generations.changed() => reload_pending = true,
                    _ = self.wheel.nearer.notified() => {}
                    _ = tokio::time::sleep(wait) => {}
                }
            }
        })
    }
}
