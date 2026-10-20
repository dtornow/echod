//! One request against one origin, serialised and committed.
//!
//! Per origin, one actor at a time: load the document, run the kernel, drain
//! what the step left owed, then commit. The commit is the verified
//! protocol of `echod_fleet::node::txn`, run against the store one operation
//! at a time: the key for the document's nearest deadline is put before the
//! document, the document is written conditionally on the version loaded,
//! the key replaced is removed after, the key kept is remembered with the
//! version written, and the key that fired a sweep is deleted: the write
//! fences every commit still in flight that armed it. A sweep that found
//! nothing due rewrites the document at a new version first, for the same
//! reason, and only then deletes the key. A lost race re-reads and re-decides.
//!
//! The cache holds the last document this node read or wrote for an origin.
//! It is never used without asking the store: every load revalidates with
//! `If-None-Match`, and the body is used only when the store says the
//! version held is current (the fleet's revalidation theorem). Every
//! version read or written, and every entry dropped, is reported to the
//! node, so what it decides on is what the cache holds.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use echod_fleet::node::core::{Armed, Key};
use echod_fleet::node::step;
use echod_kernel::{Config as KernelConfig, OutboxEntry, Schedule, State};
use resonate_core::{ResonateRouter, Unavailable};

use crate::cache::{Cache, Cached};
use crate::doc::{self, Header, Loaded};
use crate::keys::KeySpace;
use crate::metrics::{CacheResult, CommitOutcome, MessageOutcome, Metrics, SweepOutcome, WriteMode};
use crate::nodes::Nodes;
use crate::store::{Etag, Read, Store, StoreError};
use crate::timers::TimerWheel;

/// What became of the key that fired a sweep.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fired {
    /// Deleted from the bucket.
    Deleted,
    /// Still in the bucket: the delete failed. It fires again.
    Kept,
}

/// The key that fired a sweep, and the node that armed it.
#[derive(Debug, Clone)]
pub struct FiredKey {
    pub key: Key,
    pub by: String,
}

pub struct Applier {
    store: Arc<dyn Store>,
    keys: KeySpace,
    cfg: KernelConfig,
    nodes: Arc<Nodes>,
    timers: Arc<TimerWheel>,
    router: Arc<dyn ResonateRouter>,
    server_url: String,
    cache: Arc<dyn Cache>,
    observer: Arc<dyn crate::env::Observer>,
    metrics: Arc<Metrics>,
    tokens: std::sync::atomic::AtomicU64,
    locks: Mutex<HashMap<String, Arc<tokio::sync::Mutex<()>>>>,
    max_retries: u32,
}

/// The document an actor works on, and what it owes afterwards.
struct Working {
    origin: String,
    loaded: Loaded,
    etag: Option<Etag>,
    schedules: Vec<(Schedule, Etag)>,
}

impl Applier {
    pub fn new(
        store: Arc<dyn Store>,
        keys: KeySpace,
        cfg: KernelConfig,
        nodes: Arc<Nodes>,
        timers: Arc<TimerWheel>,
        router: Arc<dyn ResonateRouter>,
        server_url: String,
        cache: Arc<dyn Cache>,
        clock: Arc<dyn crate::env::Clock>,
        observer: Arc<dyn crate::env::Observer>,
        metrics: Arc<Metrics>,
    ) -> Self {
        let seed = crate::keys::fnv1a(&format!("{}/{}", server_url, clock.now())) | 1;
        Self {
            store,
            keys,
            cfg,
            nodes,
            timers,
            router,
            server_url,
            cache,
            observer,
            metrics,
            tokens: std::sync::atomic::AtomicU64::new(seed),
            locks: Mutex::new(HashMap::new()),
            max_retries: 8,
        }
    }

    pub fn kernel_config(&self) -> KernelConfig {
        self.cfg
    }

    fn lock_for(&self, origin: &str) -> Arc<tokio::sync::Mutex<()>> {
        let mut locks = self.locks.lock().unwrap_or_else(|e| e.into_inner());
        Arc::clone(locks.entry(origin.to_string()).or_insert_with(|| Arc::new(tokio::sync::Mutex::new(()))))
    }

    fn cached(&self, origin: &str) -> Option<Cached> {
        self.cache.get(origin)
    }

    /// Remember a document and report its version to the node: read
    /// or wrote.
    fn remember(&self, origin: &str, c: Cached) {
        let (etag, filled_at) = (c.etag.clone(), c.filled_at);
        for evicted in self.cache.put(origin, c) {
            self.nodes.forget(&evicted);
        }
        self.nodes.filled(origin, &etag, filled_at);
    }

    pub fn forget(&self, origin: &str) {
        self.cache.forget(origin);
        self.nodes.forget(origin);
    }

    pub fn cache_stats(&self) -> crate::cache::CacheStats {
        self.cache.stats()
    }

    /// A token no other arm of this node has used.
    fn token(&self) -> u64 {
        self.tokens.fetch_add(0x9e37_79b9_7f4a_7c15, std::sync::atomic::Ordering::Relaxed)
    }

    fn me(&self) -> String {
        self.nodes.id()
    }

    /// The name of a key in the bucket, armed by `by`.
    fn key_name(&self, k: &Key, by: &str) -> String {
        if let Some(id) = k.origin.strip_prefix("sched:") {
            self.keys.sched_timer_key(id, k.at, k.token, by)
        } else {
            self.keys.timer_key(&k.origin, k.at, k.token, by)
        }
    }

    /// Put a deadline key and hold it in the wheel.
    async fn put_key(&self, target: &str, at: u64) -> Result<Key, StoreError> {
        let k = Key { origin: target.to_string(), at, token: self.token() };
        let name = self.key_name(&k, &self.me());
        self.store.put(&name, Vec::new()).await?;
        self.timers.arm(at, name);
        Ok(k)
    }

    /// Delete a deadline key armed by `by`. Best effort: a key that stays
    /// fires again and is collected then.
    async fn delete_key(&self, k: &Key, by: &str) -> bool {
        let name = self.key_name(k, by);
        match self.store.delete(&name).await {
            Ok(()) => {
                self.timers.disarm(k.at, &name);
                true
            }
            Err(e) => {
                tracing::debug!(key = %name, error = %e, "deadline key not deleted; it fires again");
                false
            }
        }
    }

    /// Load an origin's document: revalidated against the store when the
    /// cache holds a version, read in full otherwise. Cache bookkeeping is
    /// on the fleet's time.
    async fn load(&self, origin: &str) -> Result<(Loaded, Option<Etag>), Unavailable> {
        let now = self.nodes.now();
        let key = self.keys.doc_key(origin);
        if let Some(c) = self.cached(origin) {
            match self.store.get_if_none_match(&key, &c.etag).await.map_err(unavailable)? {
                Read::NotModified => {
                    self.metrics.cache(CacheResult::Revalidated);
                    self.remember(origin, Cached { filled_at: now, ..c.clone() });
                    return Ok((c.loaded, Some(c.etag)));
                }
                Read::Absent => {
                    self.metrics.cache(CacheResult::Absent);
                    self.forget(origin);
                    return Ok((Loaded::empty(), None));
                }
                Read::Body(bytes, etag) => {
                    self.metrics.cache(CacheResult::Refreshed);
                    let loaded = doc::decode(&bytes).map_err(Unavailable::new)?;
                    self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone(), filled_at: now });
                    return Ok((loaded, Some(etag)));
                }
            }
        }
        self.metrics.cache(CacheResult::Miss);
        match self.store.get(&key).await.map_err(unavailable)? {
            None => Ok((Loaded::empty(), None)),
            Some((bytes, etag)) => {
                let loaded = doc::decode(&bytes).map_err(Unavailable::new)?;
                self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone(), filled_at: now });
                Ok((loaded, Some(etag)))
            }
        }
    }

    async fn load_schedule(&self, id: &str) -> Result<Option<(Schedule, Etag)>, Unavailable> {
        match self.store.get(&self.keys.sched_key(id)).await.map_err(unavailable)? {
            None => Ok(None),
            Some((bytes, etag)) => {
                let c: Schedule = serde_json::from_slice(&bytes).map_err(|e| Unavailable::new(format!("bad schedule: {e}")))?;
                Ok(Some((c, etag)))
            }
        }
    }

    /// The schedule row as stored, read outside any actor turn.
    pub async fn peek_schedule(&self, id: &str) -> Result<Option<Schedule>, Unavailable> {
        Ok(self.load_schedule(id).await?.map(|(c, _)| c))
    }

    /// Run one step against `origin`'s document, with `schedule` loaded too
    /// when the step touches one; `fired` is the key whose firing this is.
    /// The step returns its answer and whether, being a sweep, it fired
    /// anything. A lost race re-reads and runs the step again, so the step
    /// must decide from the state it is given, which every kernel handler
    /// does. Without an origin only the schedule is loaded.
    pub async fn apply<R, F>(&self, origin: Option<&str>, schedule: Option<&str>, now: u64, fired: Option<FiredKey>, step: F) -> Result<(R, Fired), Unavailable>
    where
        F: Fn(&mut State, u64) -> (R, bool) + Send,
        R: Send,
    {
        let lock_key = origin.map(str::to_string).unwrap_or_else(|| format!("sched:{}", schedule.unwrap_or_default()));
        let lock = self.lock_for(&lock_key);
        let _guard = lock.lock().await;
        for attempt in 0..=self.max_retries {
            let (loaded, etag) = match origin {
                Some(o) => self.load(o).await?,
                None => (Loaded::empty(), None),
            };
            let mut schedules = Vec::new();
            if let Some(id) = schedule {
                if let Some(pair) = self.load_schedule(id).await? {
                    schedules.push(pair);
                }
            }
            let mut w = Working { origin: origin.unwrap_or_default().to_string(), loaded, etag, schedules };
            let mut state = State { objects: w.loaded.rows.clone(), schedules: w.schedules.iter().map(|(c, _)| c.clone()).collect(), outbox: Vec::new() };
            // Decided no earlier than the last step on the document: the
            // kernel is proved for an instant at or after it.
            let now = step::clamp_now(w.loaded.stamp, now);
            let (r, did) = step(&mut state, now);
            step::drain(&mut state, now, &self.cfg);
            match self.commit(&mut w, &state, now, did, fired.as_ref()).await {
                Ok(f) => {
                    self.metrics.commit(CommitOutcome::Committed);
                    return Ok((r, f));
                }
                Err(StoreError::PreconditionFailed) => {
                    self.metrics.commit(CommitOutcome::Raced);
                    tracing::debug!(origin = ?origin, schedule = ?schedule, attempt, "lost a race; re-deciding");
                    if let Some(o) = origin {
                        self.forget(o);
                    }
                    continue;
                }
                Err(e) => {
                    self.metrics.commit(CommitOutcome::Failed);
                    // The write may or may not have landed: trust nothing cached.
                    if let Some(o) = origin {
                        self.forget(o);
                    }
                    return Err(unavailable(e));
                }
            }
        }
        self.metrics.commit(CommitOutcome::Exhausted);
        Err(Unavailable::new("too many races on the document"))
    }

    /// Fire what is due in the origin: deadlines, leases, retries, and the
    /// drains that follow. The sweep behind the key `fired`.
    pub async fn sweep(&self, origin: &str, now: u64, fired: FiredKey) -> Result<Fired, Unavailable> {
        let cfg = self.cfg;
        let handle = self.observer.sweep_begin(&self.nodes.id(), origin, now);
        let r = self.apply(Some(origin), None, now, Some(fired), move |s: &mut State, now: u64| {
            let did = step::sweep(s, now, &cfg);
            (did, did)
        })
        .await;
        self.observer.sweep_end(handle, r.is_ok());
        self.metrics.sweep(match &r {
            Ok((true, _)) => SweepOutcome::Fired,
            Ok((false, _)) => SweepOutcome::Idle,
            Err(_) => SweepOutcome::Failed,
        });
        r.map(|(_, f)| f)
    }

    /// Write the document at a new version, conditionally on the version
    /// loaded: the rows the step changed appended, or the whole document.
    async fn write_doc(&self, w: &mut Working, rows: &[echod_kernel::Promise], changed: &[echod_kernel::Promise], now: u64) -> Result<Etag, StoreError> {
        let fleet_now = self.nodes.now();
        let key = self.keys.doc_key(&w.origin);
        let header = Header { stamp: now, nonce: self.token() };
        let etag = match &w.etag {
            None => {
                let body = doc::encode(&header, rows);
                let etag = self.store.put_if_none_match(&key, body.clone()).await?;
                self.metrics.document_write(WriteMode::Create, body.len());
                self.remember(&w.origin, Cached { loaded: Loaded { rows: rows.to_vec(), row_count: rows.len(), bytes: body.len() as u64, stamp: now }, etag: etag.clone(), filled_at: fleet_now });
                etag
            }
            Some(etag) => {
                let stale_after = w.loaded.row_count + changed.len() - rows.len();
                let append = self.store.supports_append() && self.cfg.compact > 0 && stale_after < self.cfg.compact as usize;
                if append {
                    let body = doc::encode(&header, changed);
                    let new = self.store.append_if_match(&key, w.loaded.bytes, body.clone(), etag).await?;
                    self.metrics.document_write(WriteMode::Append, body.len());
                    self.remember(
                        &w.origin,
                        Cached { loaded: Loaded { rows: rows.to_vec(), row_count: w.loaded.row_count + changed.len(), bytes: w.loaded.bytes + body.len() as u64, stamp: now }, etag: new.clone(), filled_at: fleet_now },
                    );
                    new
                } else {
                    let body = doc::encode(&header, rows);
                    let new = self.store.put_if_match(&key, body.clone(), etag).await?;
                    self.metrics.document_write(WriteMode::Rewrite, body.len());
                    self.remember(&w.origin, Cached { loaded: Loaded { rows: rows.to_vec(), row_count: rows.len(), bytes: body.len() as u64, stamp: now }, etag: new.clone(), filled_at: fleet_now });
                    new
                }
            }
        };
        Ok(etag)
    }

    /// The commit: the verified decisions of `echod_fleet::node::txn`, each
    /// store operation between them.
    async fn commit(&self, w: &mut Working, state: &State, now: u64, did: bool, fired: Option<&FiredKey>) -> Result<Fired, StoreError> {
        let me = self.me();
        let mut outcome = Fired::Kept;
        if !w.origin.is_empty() {
            let changed = doc::changed(&w.loaded.rows, &state.objects);
            let changed_any = did || !changed.is_empty();
            let deadline = step::next_deadline(&state.objects);
            let mut txn = self.nodes.begin(&w.origin, w.etag.as_ref(), deadline, changed_any, fired.map(|f| f.key.clone()));
            if changed_any {
                // (1) the key for the new deadline, before the state that arms it
                if let Some(at) = txn.arm_at() {
                    let k = self.put_key(&w.origin, at).await?;
                    txn.armed(k);
                }
                // (2) the document
                let etag = self.write_doc(w, &state.objects, &changed, now).await?;
                // (3) the key replaced, or no longer needed
                if let Some(p) = txn.to_disarm() {
                    self.delete_key(&p, &me).await;
                }
                // (4) the key kept, with the version written
                self.nodes.finish(&txn, &etag);
                // (5) the key fired: the write that just landed fences every
                // commit that armed it and has not written yet
                if let Some(f) = fired {
                    self.nodes.collected(&w.origin, &f.key);
                    if self.delete_key(&f.key, &f.by).await {
                        outcome = Fired::Deleted;
                    }
                }
            } else if let Some(f) = fired {
                // Nothing was due: rewrite the document at a new version, so
                // that no commit in flight that armed this key can land on
                // the version it loaded; then the key goes.
                self.write_doc(w, &state.objects, &[], now).await?;
                self.nodes.collected(&w.origin, &f.key);
                if self.delete_key(&f.key, &f.by).await {
                    outcome = Fired::Deleted;
                }
            }
        }

        // schedules: each its own object, with its own key
        for c in &state.schedules {
            let before = w.schedules.iter().find(|(b, _)| b.id == c.id);
            let body = serde_json::to_vec(c).expect("a schedule serialises");
            let target = format!("sched:{}", c.id);
            match before {
                Some((b, etag)) => {
                    if serde_json::to_vec(b).ok() != Some(body.clone()) {
                        let previous = self.nodes.armed_for(&target).filter(|a| a.etag == etag.0);
                        let rearm = previous.as_ref().map_or(true, |p| p.key.at != c.next_run_at);
                        let mut key = previous.as_ref().map(|p| p.key.clone());
                        if rearm {
                            key = Some(self.put_key(&target, c.next_run_at).await?);
                        }
                        let new = self.store.put_if_match(&self.keys.sched_key(&c.id), body, etag).await?;
                        if rearm {
                            if let Some(p) = &previous {
                                self.delete_key(&p.key, &me).await;
                            }
                        }
                        self.nodes.set_armed(&target, key.map(|k| Armed { key: k, etag: new.0.clone() }));
                    }
                }
                None => {
                    let k = self.put_key(&target, c.next_run_at).await?;
                    let new = self.store.put_if_none_match(&self.keys.sched_key(&c.id), body).await?;
                    self.nodes.set_armed(&target, Some(Armed { key: k, etag: new.0.clone() }));
                }
            }
        }
        for (b, _) in &w.schedules {
            if !state.schedules.iter().any(|c| c.id == b.id) {
                self.store.delete(&self.keys.sched_key(&b.id)).await?;
                let target = format!("sched:{}", b.id);
                if let Some(p) = self.nodes.armed_for(&target) {
                    self.delete_key(&p.key, &me).await;
                }
                self.nodes.set_armed(&target, None);
            }
        }

        // the outbox, after the commit
        for e in &state.outbox {
            self.send(e).await;
        }
        Ok(outcome)
    }

    async fn send(&self, e: &OutboxEntry) {
        let (address, msg) = crate::wire::message_out(e, &self.server_url);
        let started = std::time::Instant::now();
        let outcome = match self.router.route(&address, &msg).await {
            Ok(()) => MessageOutcome::Delivered,
            Err(err) => {
                tracing::warn!(address = %address, error = %err, "message not delivered");
                match err.cause {
                    resonate_core::Cause::Unroutable => MessageOutcome::Unroutable,
                    resonate_core::Cause::Delivery => MessageOutcome::Failed,
                }
            }
        };
        let kind = match &msg {
            resonate_core::types::Message::Execute(_) => "execute",
            resonate_core::types::Message::Unblock(_) => "unblock",
        };
        self.metrics.message(kind, outcome, started);
    }
}

pub fn unavailable(e: StoreError) -> Unavailable {
    Unavailable::new(e.to_string())
}
