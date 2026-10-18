//! Deadlines as objects, fired by the owner.
//!
//! A deadline is an empty object whose key says what is due and when. Every
//! writer puts the key before the state that arms it and arms it in memory
//! after. The owner of the target fires it: from memory when it wrote the key
//! itself, and from a periodic listing of the timer prefix otherwise — which
//! is how a deadline another node armed, or one a dead node left behind,
//! reaches the node that now owns it. Firing is a sweep of the target, which
//! is idempotent, so a key fired twice costs nothing; the key is deleted after.

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use tokio::sync::Notify;

use crate::applier::Applier;
use crate::keys::{KeySpace, TimerEntry};
use crate::nodes::Nodes;
use crate::schedules::Schedules;
use crate::store::Store;

/// Armed timer keys, nearest first.
pub struct TimerQueue {
    armed: Mutex<BTreeSet<(u64, String)>>,
    nearer: Notify,
}

impl TimerQueue {
    pub fn new() -> Self {
        Self { armed: Mutex::new(BTreeSet::new()), nearer: Notify::new() }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, BTreeSet<(u64, String)>> {
        self.armed.lock().unwrap_or_else(|e| e.into_inner())
    }

    pub fn arm(&self, at: u64, key: String) {
        let mut q = self.lock();
        let nearest = q.iter().next().map(|(d, _)| *d);
        q.insert((at, key));
        if nearest.map_or(true, |n| at < n) {
            self.nearer.notify_one();
        }
    }

    pub fn disarm(&self, at: u64, key: &str) {
        self.lock().remove(&(at, key.to_string()));
    }

    /// Everything due at `now`, removed from the queue.
    pub fn take_due(&self, now: u64) -> Vec<(u64, String)> {
        let mut q = self.lock();
        let due: Vec<(u64, String)> = q.iter().take_while(|(d, _)| *d <= now).cloned().collect();
        for e in &due {
            q.remove(e);
        }
        due
    }

    pub fn nearest(&self) -> Option<u64> {
        self.lock().iter().next().map(|(d, _)| *d)
    }

    pub fn len(&self) -> usize {
        self.lock().len()
    }
}

impl Default for TimerQueue {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Timers {
    store: Arc<dyn Store>,
    keys: KeySpace,
    queue: Arc<TimerQueue>,
    nodes: Arc<Nodes>,
    applier: Arc<Applier>,
    schedules: Arc<Schedules>,
    poll: Duration,
}

impl Timers {
    pub fn new(store: Arc<dyn Store>, keys: KeySpace, queue: Arc<TimerQueue>, nodes: Arc<Nodes>, applier: Arc<Applier>, schedules: Arc<Schedules>, poll: Duration) -> Self {
        Self { store, keys, queue, nodes, applier, schedules, poll }
    }

    /// Fire one key: sweep its target if this node owns it, then collect it.
    async fn fire(&self, key: &str, now: u64) {
        let Some(entry) = self.keys.parse_timer_key(key) else {
            tracing::warn!(key = %key, "unparseable timer key");
            return;
        };
        let owner_key = match &entry {
            TimerEntry::Origin { origin, .. } => origin.clone(),
            TimerEntry::Schedule { id, .. } => id.clone(),
        };
        if !self.nodes.owns(&owner_key) {
            return;
        }
        let swept = match &entry {
            TimerEntry::Origin { origin, .. } => self.applier.sweep(origin, now).await,
            TimerEntry::Schedule { id, deadline } => self.schedules.fire(id, *deadline, now).await,
        };
        match swept {
            Ok(()) => {
                if let Err(e) = self.store.delete(key).await {
                    tracing::debug!(key = %key, error = %e, "timer key not collected");
                }
            }
            Err(e) => {
                tracing::warn!(key = %key, error = %e, "sweep failed; the key stays");
                // Look again a beat later.
                self.queue.arm(now + 1_000, key.to_string());
            }
        }
    }

    /// One round: what memory says is due, and what the bucket says is due.
    pub async fn round(&self, now: u64) {
        for (_, key) in self.queue.take_due(now) {
            self.fire(&key, now).await;
        }
        for shard in 0..self.keys.timer_shards() {
            let prefix = self.keys.timer_shard_prefix(shard);
            let keys = match self.store.list(&prefix, 256).await {
                Ok(k) => k,
                Err(e) => {
                    tracing::warn!(error = %e, "listing timers failed");
                    continue;
                }
            };
            for key in keys {
                match self.keys.parse_timer_key(&key) {
                    Some(e) if e.deadline() <= now => self.fire(&key, now).await,
                    _ => break,
                }
            }
        }
    }

    /// The loop: a round every `poll`, or sooner when memory says so.
    pub fn spawn(self: Arc<Self>, mut shutdown: tokio::sync::watch::Receiver<bool>) -> tokio::task::JoinHandle<()> {
        tokio::spawn(async move {
            loop {
                let now = resonate_core::util::system_time_ms() as u64;
                self.round(now).await;
                let wait = match self.queue.nearest() {
                    Some(d) if d > now => Duration::from_millis(d - now).min(self.poll),
                    Some(_) => Duration::from_millis(10),
                    None => self.poll,
                };
                tokio::select! {
                    _ = tokio::time::sleep(wait) => {}
                    _ = self.queue.nearer.notified() => {}
                    _ = shutdown.changed() => return,
                }
            }
        })
    }
}
