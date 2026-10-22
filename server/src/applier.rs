//! One request against one document, serialised and committed.
//!
//! Per document, one actor at a time: load it, run the kernel, drain what
//! the step left owed, then commit. A document is an origin's objects or a
//! schedule's row; both kinds go through the one commit, the verified
//! protocol of `echod_fleet::txn`, run against the store one
//! operation at a time: the key for the document's nearest deadline is put
//! before the document, the document is written conditionally on the
//! version loaded, the key replaced is removed after, the key kept is
//! remembered with the version written, and the key that fired is deleted:
//! the write fences every commit still in flight that armed it. A fire that
//! found nothing due rewrites the document at a new version first, for the
//! same reason, and only then deletes the key. A lost race re-reads and
//! re-decides.
//!
//! A schedule's key fires on two documents: the schedule's row decides the
//! occurrence's promise, the kernel's `process_schedule` runs on the row
//! beside the promise's origin, and the origin is committed first, then
//! the schedule with the key fired — the fleet model's `Fire`, with its
//! pending half. A crash between the two refires the occurrence, which the
//! kernel makes a no-op on the promise and an advance on the schedule.
//!
//! The cache holds the last document this node read or wrote for an origin.
//! It is never used without asking the store: every load revalidates with
//! `If-None-Match`, and the body is used only when the store says the
//! version held is current (the fleet's revalidation theorem). Every
//! version read or written, and every entry dropped, is reported to the
//! node, so what it decides on is what the cache holds. A schedule's
//! document is not cached.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use echod_fleet::node::Key;
use echod_fleet::step;
use echod_kernel::{Config as KernelConfig, Occurrence, OutboxEntry, Promise, Schedule, ScheduleTimeoutReq, State};
use resonate_core::{util, ResonateRouter, Unavailable};

use crate::cache::{Cache, Cached};
use crate::doc::{self, Header, Loaded, Row};
use crate::keys::{origin_of, KeySpace};
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

/// What a step is run on.
#[derive(Clone, Debug)]
pub enum Target {
    Origin(String),
    Schedule(String),
}

impl Target {
    /// The name the keys and the node's decisions go by: the origin, or
    /// `sched:<id>`.
    pub fn name(&self) -> String {
        match self {
            Target::Origin(o) => o.clone(),
            Target::Schedule(id) => format!("sched:{id}"),
        }
    }
}

/// The document an actor works on, and what it owes afterwards.
struct Working<R: Row> {
    /// The target's name.
    target: String,
    /// The object's key.
    key: String,
    loaded: Loaded<R>,
    etag: Option<Etag>,
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
    async fn load_origin(&self, origin: &str) -> Result<Working<Promise>, Unavailable> {
        let now = self.nodes.now();
        let key = self.keys.doc_key(origin);
        let w = |loaded: Loaded<Promise>, etag: Option<Etag>| Working { target: origin.to_string(), key: key.clone(), loaded, etag };
        if let Some(c) = self.cached(origin) {
            match self.store.get_if_none_match(&key, &c.etag).await.map_err(unavailable)? {
                Read::NotModified => {
                    self.metrics.cache(CacheResult::Revalidated);
                    self.remember(origin, Cached { filled_at: now, ..c.clone() });
                    return Ok(w(c.loaded, Some(c.etag)));
                }
                Read::Absent => {
                    self.metrics.cache(CacheResult::Absent);
                    self.forget(origin);
                    return Ok(w(Loaded::empty(), None));
                }
                Read::Body(bytes, etag) => {
                    self.metrics.cache(CacheResult::Refreshed);
                    let loaded = doc::decode(&bytes).map_err(Unavailable::new)?;
                    self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone(), filled_at: now });
                    return Ok(w(loaded, Some(etag)));
                }
            }
        }
        self.metrics.cache(CacheResult::Miss);
        match self.store.get(&key).await.map_err(unavailable)? {
            None => Ok(w(Loaded::empty(), None)),
            Some((bytes, etag)) => {
                let loaded = doc::decode(&bytes).map_err(Unavailable::new)?;
                self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone(), filled_at: now });
                Ok(w(loaded, Some(etag)))
            }
        }
    }

    /// Load a schedule's document, read in full: not cached.
    async fn load_schedule(&self, id: &str) -> Result<Working<Schedule>, Unavailable> {
        let key = self.keys.sched_key(id);
        let target = Target::Schedule(id.to_string()).name();
        match self.store.get(&key).await.map_err(unavailable)? {
            None => Ok(Working { target, key, loaded: Loaded::empty(), etag: None }),
            Some((bytes, etag)) => {
                let loaded = doc::decode(&bytes).map_err(Unavailable::new)?;
                Ok(Working { target, key, loaded, etag: Some(etag) })
            }
        }
    }

    /// Run one step against a document; `fired` is the key whose firing
    /// this is. The step returns its answer and whether, being a sweep, it
    /// fired anything. A lost race re-reads and runs the step again, so the
    /// step must decide from the state it is given, which every kernel
    /// handler does.
    pub async fn apply<R, F>(&self, target: &Target, now: u64, fired: Option<FiredKey>, step: F) -> Result<(R, Fired), Unavailable>
    where
        F: Fn(&mut State, u64) -> (R, bool) + Send,
        R: Send,
    {
        let lock = self.lock_for(&target.name());
        let _guard = lock.lock().await;
        for attempt in 0..=self.max_retries {
            let (r, committed, outbox) = match target {
                Target::Origin(o) => {
                    let mut w = self.load_origin(o).await?;
                    let mut state = Promise::state_of(&w.loaded.rows);
                    // Decided no earlier than the last step on the document:
                    // the kernel is proved for an instant at or after it.
                    let now = step::clamp_now(w.loaded.stamp, now);
                    let (r, did) = step(&mut state, now);
                    step::drain(&mut state, now, &self.cfg);
                    let c = self.commit(&mut w, &state.objects, now, did, fired.as_ref()).await;
                    (r, c, state.outbox)
                }
                Target::Schedule(id) => {
                    let mut w = self.load_schedule(id).await?;
                    let mut state = Schedule::state_of(&w.loaded.rows);
                    let now = step::clamp_now(w.loaded.stamp, now);
                    let (r, did) = step(&mut state, now);
                    step::drain(&mut state, now, &self.cfg);
                    let c = self.commit(&mut w, &state.schedules, now, did, fired.as_ref()).await;
                    (r, c, state.outbox)
                }
            };
            match committed {
                Ok(f) => {
                    self.metrics.commit(CommitOutcome::Committed);
                    for e in &outbox {
                        self.send(e).await;
                    }
                    return Ok((r, f));
                }
                Err(StoreError::PreconditionFailed) => {
                    self.metrics.commit(CommitOutcome::Raced);
                    tracing::debug!(target = %target.name(), attempt, "lost a race; re-deciding");
                    if let Target::Origin(o) = target {
                        self.forget(o);
                    }
                    continue;
                }
                Err(e) => {
                    self.metrics.commit(CommitOutcome::Failed);
                    // The write may or may not have landed: trust nothing cached.
                    if let Target::Origin(o) = target {
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
        let r = self.apply(&Target::Origin(origin.to_string()), now, Some(fired), move |s: &mut State, now: u64| {
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

    /// The promise id an occurrence expands to.
    pub fn expand(template: &str, id: &str, at: u64) -> String {
        template.replace("{{.id}}", id).replace("{{.timestamp}}", &at.to_string())
    }

    /// Fire schedule `id` behind the key `fired`: its due occurrence, if
    /// any, as a promise in the occurrence's origin, then the schedule
    /// advanced, each its own commit, in that order. A schedule not due, or
    /// gone, is rewritten unchanged so the key can be collected behind the
    /// write.
    pub async fn fire(&self, id: &str, now: u64, fired: FiredKey) -> Result<Fired, Unavailable> {
        let cfg = self.cfg;
        let sched_lock = self.lock_for(&Target::Schedule(id.to_string()).name());
        let _sched_guard = sched_lock.lock().await;
        for attempt in 0..=self.max_retries {
            let mut ws = self.load_schedule(id).await?;
            let t1 = step::clamp_now(ws.loaded.stamp, now);
            // the decision is the step module's: a row due at the instant, or none
            let due = step::schedule_due(&Schedule::state_of(&ws.loaded.rows), t1).map(|i| ws.loaded.rows[i].clone());
            let Some(c) = due else {
                // a sweep of the schedule's document that finds nothing due
                let rows = ws.loaded.rows.clone();
                let handle = self.observer.sweep_begin(&self.nodes.id(), &ws.target, t1);
                let r = self.commit(&mut ws, &rows, t1, false, Some(&fired)).await;
                self.observer.sweep_end(handle, r.is_ok());
                match r {
                    Ok(f) => {
                        self.metrics.commit(CommitOutcome::Committed);
                        return Ok(f);
                    }
                    Err(StoreError::PreconditionFailed) => {
                        self.metrics.commit(CommitOutcome::Raced);
                        continue;
                    }
                    Err(e) => {
                        self.metrics.commit(CommitOutcome::Failed);
                        return Err(unavailable(e));
                    }
                }
            };
            let at = c.next_run_at;
            let promise_id = Self::expand(&c.promise_id, id, at);
            let origin = origin_of(&promise_id).to_string();
            let next = util::compute_next_cron(&c.cron, at as i64).max(at as i64 + 1) as u64;
            let req = ScheduleTimeoutReq { schedule: id.to_string(), occurrences: vec![Occurrence { at, promise_id }], next_run_at: next };
            let origin_lock = self.lock_for(&origin);
            let _origin_guard = origin_lock.lock().await;
            let mut wo = self.load_origin(&origin).await?;
            let t = step::clamp_now(wo.loaded.stamp, t1);
            let mut state = State { objects: wo.loaded.rows.clone(), schedules: ws.loaded.rows.clone(), outbox: Vec::new() };
            state.process_schedule(&req, t, &cfg);
            step::drain(&mut state, t, &cfg);
            // the origin first: the occurrence's promise
            let handle = self.observer.fire_begin(&self.nodes.id(), &origin, t, &c, at, &req.occurrences[0].promise_id, next);
            let r = self.commit(&mut wo, &state.objects, t, false, None).await;
            self.observer.fire_end(handle, r.is_ok());
            match r {
                Ok(_) => {
                    self.metrics.commit(CommitOutcome::Committed);
                    for e in &state.outbox {
                        self.send(e).await;
                    }
                }
                Err(StoreError::PreconditionFailed) => {
                    self.metrics.commit(CommitOutcome::Raced);
                    tracing::debug!(schedule = %id, origin = %origin, attempt, "lost a race; re-deciding");
                    self.forget(&origin);
                    continue;
                }
                Err(e) => {
                    self.metrics.commit(CommitOutcome::Failed);
                    self.forget(&origin);
                    return Err(unavailable(e));
                }
            }
            // then the schedule, advanced, with the key fired
            let handle = self.observer.advance_begin(&self.nodes.id(), id, t, at, next);
            let r = self.commit(&mut ws, &state.schedules, t, false, Some(&fired)).await;
            self.observer.advance_end(handle, r.is_ok());
            match r {
                Ok(f) => {
                    self.metrics.commit(CommitOutcome::Committed);
                    return Ok(f);
                }
                Err(StoreError::PreconditionFailed) => {
                    self.metrics.commit(CommitOutcome::Raced);
                    tracing::debug!(schedule = %id, attempt, "lost a race on the schedule; re-deciding");
                    continue;
                }
                Err(e) => {
                    self.metrics.commit(CommitOutcome::Failed);
                    return Err(unavailable(e));
                }
            }
        }
        self.metrics.commit(CommitOutcome::Exhausted);
        Err(Unavailable::new("too many races on the schedule"))
    }

    /// Write the document at a new version, conditionally on the version
    /// loaded: the rows the step changed appended, or the whole document.
    async fn write_doc<R: Row>(&self, w: &mut Working<R>, rows: &[R], changed: &[R], now: u64) -> Result<Etag, StoreError> {
        let fleet_now = self.nodes.now();
        let header = Header { stamp: now, nonce: self.token() };
        let etag = match &w.etag {
            None => {
                let body = doc::encode(&header, rows);
                let etag = self.store.put_if_none_match(&w.key, body.clone()).await?;
                self.metrics.document_write(WriteMode::Create, body.len());
                (etag, rows.len(), body.len() as u64)
            }
            Some(etag) => {
                // a row gone — a schedule deleted — cannot be appended; the
                // document is rewritten without it
                let removed = w.loaded.rows.iter().any(|q| !rows.iter().any(|p| p.id() == q.id()));
                let stale_after = (w.loaded.row_count + changed.len()).saturating_sub(rows.len());
                let append = !removed && self.store.supports_append() && self.cfg.compact > 0 && stale_after < self.cfg.compact as usize;
                if append {
                    let body = doc::encode(&header, changed);
                    let new = self.store.append_if_match(&w.key, w.loaded.bytes, body.clone(), etag).await?;
                    self.metrics.document_write(WriteMode::Append, body.len());
                    (new, w.loaded.row_count + changed.len(), w.loaded.bytes + body.len() as u64)
                } else {
                    let body = doc::encode(&header, rows);
                    let new = self.store.put_if_match(&w.key, body.clone(), etag).await?;
                    self.metrics.document_write(WriteMode::Rewrite, body.len());
                    (new, rows.len(), body.len() as u64)
                }
            }
        };
        let (etag, row_count, bytes) = etag;
        // an origin's document is remembered as written; a schedule's is not cached
        if let Some(rows) = R::promises(rows) {
            self.remember(&w.target, Cached { loaded: Loaded { rows, row_count, bytes, stamp: now }, etag: etag.clone(), filled_at: fleet_now });
        }
        Ok(etag)
    }

    /// The commit: the verified decisions of `echod_fleet::txn`, each
    /// store operation between them. `did` is whether a sweep fired
    /// anything; `fired` the key whose firing this is.
    async fn commit<R: Row>(&self, w: &mut Working<R>, rows: &[R], now: u64, did: bool, fired: Option<&FiredKey>) -> Result<Fired, StoreError> {
        let me = self.me();
        let mut outcome = Fired::Kept;
        let changed = doc::changed(&w.loaded.rows, rows);
        let changed_any = did || !changed.is_empty() || rows.len() != w.loaded.rows.len();
        let deadline = step::next_deadline(&R::state_of(rows));
        let mut txn = self.nodes.prepare(&w.target, w.etag.as_ref(), deadline, changed_any, fired.map(|f| f.key.clone()));
        if changed_any {
            // (1) the key for the new deadline, before the state that arms it
            if let Some(at) = txn.arm_at() {
                let k = self.put_key(&w.target, at).await?;
                txn.armed(k);
            }
            // (2) the document
            let etag = self.write_doc(w, rows, &changed, now).await?;
            // (3) the key replaced, or no longer needed
            if let Some(p) = txn.to_disarm() {
                self.delete_key(&p, &me).await;
            }
            // (4) the key kept, with the version written
            self.nodes.finish(&txn, &etag);
            // (5) the key fired: the write that just landed fences every
            // commit that armed it and has not written yet
            if let Some(f) = fired {
                self.nodes.collected(&w.target, &f.key);
                if self.delete_key(&f.key, &f.by).await {
                    outcome = Fired::Deleted;
                }
            }
        } else if let Some(f) = fired {
            // Nothing was due: rewrite the document at a new version, so
            // that no commit in flight that armed this key can land on
            // the version it loaded; then the key goes.
            self.write_doc(w, rows, &[], now).await?;
            self.nodes.collected(&w.target, &f.key);
            if self.delete_key(&f.key, &f.by).await {
                outcome = Fired::Deleted;
            }
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
