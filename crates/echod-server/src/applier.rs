//! One request against one origin, serialised and committed.
//!
//! Per origin, one actor at a time: load the document, run the kernel, drain
//! what the step left owed, write what changed, arm the next deadline, hand
//! the outbox to the router. The write is conditional on the version read; a
//! lost race re-reads and re-decides.
//!
//! The cache holds the last document this node read or wrote for an origin.
//! Whether it may be used without asking the store is the verified node's
//! decision (`Nodes::trusts`): the acting owner trusts an entry filled while
//! it acted, since every write to the origin goes through the owner. Anyone
//! else revalidates it with `If-None-Match` before use. Every version read
//! or written, and every entry dropped, is reported to the node, so what it
//! decides on is what the cache holds.
//!
//! A commit that moves an origin's nearest deadline writes the new deadline
//! key before the document and removes the previous key, the one this node
//! armed, after it. The key's token is drawn per arm, so the removal can never
//! land on a key another arm wrote for the same instant.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use crate::cache::{Armed, Cache, Cached};

use echod_kernel::{Config as KernelConfig, OutboxEntry, Promise, Schedule, State};
use resonate_core::{ResonateRouter, Unavailable};

use crate::doc::{self, Loaded};
use crate::keys::KeySpace;
use crate::nodes::Nodes;
use crate::store::{Etag, Read, Store, StoreError};
use crate::timers::TimerWheel;

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

    fn armed_for(&self, target: &str) -> Option<Armed> {
        self.cache.armed(target)
    }

    fn set_armed(&self, target: &str, a: Option<Armed>) {
        self.cache.set_armed(target, a);
    }

    /// A fired key was collected: if it is the one this node remembers for
    /// `target`, forget it, so the next commit arms afresh.
    pub fn collected(&self, target: &str, key: &str) {
        if self.cache.armed(target).map(|a| a.key) == Some(key.to_string()) {
            self.cache.set_armed(target, None);
        }
    }

    /// Write a deadline key and hold it in the wheel. Returns what was armed.
    async fn arm(&self, key: String, at: u64) -> Result<Armed, StoreError> {
        self.store.put(&key, Vec::new()).await?;
        self.timers.arm(at, key.clone());
        Ok(Armed { at, key })
    }

    /// Remove a deadline key this node armed. Best effort: a key that stays
    /// fires into a sweep with nothing due and is collected then.
    async fn disarm(&self, a: &Armed) {
        if self.store.delete(&a.key).await.is_ok() {
            self.timers.disarm(a.at, &a.key);
        }
    }

    /// Load an origin's document: from the cache when the node trusts the
    /// version it holds, revalidated against the store otherwise. Cache
    /// bookkeeping is on the fleet's time, the frame the membership rules
    /// are stated in.
    async fn load(&self, origin: &str) -> Result<(Loaded, Option<Etag>), Unavailable> {
        let now = self.nodes.now();
        let key = self.keys.doc_key(origin);
        if let Some(c) = self.cached(origin) {
            if self.nodes.trusts(origin, now).as_ref() == Some(&c.etag) {
                return Ok((c.loaded, Some(c.etag)));
            }
            match self.store.get_if_none_match(&key, &c.etag).await.map_err(unavailable)? {
                Read::NotModified => {
                    self.remember(origin, Cached { filled_at: now, ..c.clone() });
                    return Ok((c.loaded, Some(c.etag)));
                }
                Read::Absent => {
                    self.forget(origin);
                    return Ok((Loaded { rows: vec![], row_count: 0, bytes: 0 }, None));
                }
                Read::Body(bytes, etag) => {
                    let loaded = doc::decode(&bytes).map_err(Unavailable::new)?;
                    self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone(), filled_at: now });
                    return Ok((loaded, Some(etag)));
                }
            }
        }
        match self.store.get(&key).await.map_err(unavailable)? {
            None => Ok((Loaded { rows: vec![], row_count: 0, bytes: 0 }, None)),
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
    /// when the step touches one. A lost race re-reads and runs the step
    /// again, so the step must decide from the state it is given, which every
    /// kernel handler does. Without an origin only the schedule is loaded.
    pub async fn apply<R, F>(&self, origin: Option<&str>, schedule: Option<&str>, now: u64, step: F) -> Result<R, Unavailable>
    where
        F: Fn(&mut State, u64) -> R + Send,
        R: Send,
    {
        let lock_key = origin.map(str::to_string).unwrap_or_else(|| format!("sched:{}", schedule.unwrap_or_default()));
        let lock = self.lock_for(&lock_key);
        let _guard = lock.lock().await;
        for attempt in 0..=self.max_retries {
            let (loaded, etag) = match origin {
                Some(o) => self.load(o).await?,
                None => (Loaded { rows: vec![], row_count: 0, bytes: 0 }, None),
            };
            let mut schedules = Vec::new();
            if let Some(id) = schedule {
                if let Some(pair) = self.load_schedule(id).await? {
                    schedules.push(pair);
                }
            }
            let mut w = Working { origin: origin.unwrap_or_default().to_string(), loaded, etag, schedules };
            let mut state = State { objects: w.loaded.rows.clone(), schedules: w.schedules.iter().map(|(c, _)| c.clone()).collect(), outbox: Vec::new() };
            let now = crate::step::clamp_now(&state.objects, now);
            let r = step(&mut state, now);
            self.drain(&mut state, now);
            match self.commit(&mut w, &state, now).await {
                Ok(()) => return Ok(r),
                Err(StoreError::PreconditionFailed) => {
                    tracing::debug!(origin = ?origin, schedule = ?schedule, attempt, "lost a race; re-deciding");
                    if let Some(o) = origin {
                        self.forget(o);
                    }
                    continue;
                }
                Err(e) => {
                    // The write may or may not have landed: trust nothing cached.
                    if let Some(o) = origin {
                        self.forget(o);
                    }
                    return Err(unavailable(e));
                }
            }
        }
        Err(Unavailable::new("too many races on the document"))
    }

    /// Fire what is due in the origin: deadlines, leases, retries, and the
    /// drains that follow. The sweep behind a timer.
    pub async fn sweep(&self, origin: &str, now: u64) -> Result<(), Unavailable> {
        let cfg = self.cfg;
        let handle = self.observer.sweep_begin(&self.nodes.id(), origin, now);
        let r = self.apply(Some(origin), None, now, move |s: &mut State, now: u64| crate::step::sweep(s, now, &cfg)).await;
        self.observer.sweep_end(handle, r.is_ok());
        r
    }

    fn drain(&self, s: &mut State, now: u64) {
        crate::step::drain(s, now, &self.cfg)
    }

    /// The nearest deadline the document owes a timer for.
    pub fn next_deadline(rows: &[Promise]) -> Option<u64> {
        crate::step::next_deadline(rows)
    }

    /// Write what the step changed: the timer first, the document, the
    /// schedules, then the old timer; and hand over the outbox.
    async fn commit(&self, w: &mut Working, state: &State, _now: u64) -> Result<(), StoreError> {
        let now = self.nodes.now();
        let changed = doc::changed(&w.loaded.rows, &state.objects);
        let new_deadline = Self::next_deadline(&state.objects);

        if !changed.is_empty() {
            // (1) the new timer, before the state that arms it. Re-armed even
            // when the deadline did not move, if this node holds no key for
            // it: the key may be another node's, or lost with a restart.
            let previous = self.armed_for(&w.origin);
            let rearm = match (&new_deadline, &previous) {
                (None, _) => false,
                (Some(at), Some(p)) => *at != p.at,
                (Some(_), None) => true,
            };
            let mut armed_now = previous.clone();
            if rearm {
                let at = new_deadline.expect("a deadline");
                armed_now = Some(self.arm(self.keys.timer_key(&w.origin, at, self.token()), at).await?);
            }
            // (2) the document
            let key = self.keys.doc_key(&w.origin);
            let etag = match &w.etag {
                None => {
                    let body = doc::encode(&state.objects);
                    let etag = self.store.put_if_none_match(&key, body.clone()).await?;
                    self.remember(&w.origin, Cached { loaded: Loaded { rows: state.objects.clone(), row_count: state.objects.len(), bytes: body.len() as u64 }, etag: etag.clone(), filled_at: now });
                    etag
                }
                Some(etag) => {
                    let stale_after = w.loaded.row_count + changed.len() - state.objects.len();
                    let append = self.store.supports_append() && self.cfg.compact > 0 && stale_after < self.cfg.compact as usize;
                    if append {
                        let body = doc::encode(&changed);
                        let new = self.store.append_if_match(&key, w.loaded.bytes, body.clone(), etag).await?;
                        self.remember(
                            &w.origin,
                            Cached { loaded: Loaded { rows: state.objects.clone(), row_count: w.loaded.row_count + changed.len(), bytes: w.loaded.bytes + body.len() as u64 }, etag: new.clone(), filled_at: now },
                        );
                        new
                    } else {
                        let body = doc::encode(&state.objects);
                        let new = self.store.put_if_match(&key, body.clone(), etag).await?;
                        self.remember(&w.origin, Cached { loaded: Loaded { rows: state.objects.clone(), row_count: state.objects.len(), bytes: body.len() as u64 }, etag: new.clone(), filled_at: now });
                        new
                    }
                }
            };
            let _ = etag;
            // (3) the old timer: exactly the key this node armed before
            if new_deadline.is_none() || rearm {
                if let Some(p) = &previous {
                    self.disarm(p).await;
                }
                if new_deadline.is_none() {
                    armed_now = None;
                }
            }
            self.set_armed(&w.origin, armed_now);
        }

        // schedules: each its own object
        for c in &state.schedules {
            let before = w.schedules.iter().find(|(b, _)| b.id == c.id);
            let body = serde_json::to_vec(c).expect("a schedule serialises");
            let target = format!("sched:{}", c.id);
            match before {
                Some((b, etag)) => {
                    if serde_json::to_vec(b).ok() != Some(body.clone()) {
                        let previous = self.armed_for(&target);
                        let rearm = previous.as_ref().map_or(true, |p| p.at != c.next_run_at);
                        let mut armed_now = previous.clone();
                        if rearm {
                            armed_now = Some(self.arm(self.keys.sched_timer_key(&c.id, c.next_run_at, self.token()), c.next_run_at).await?);
                        }
                        self.store.put_if_match(&self.keys.sched_key(&c.id), body, etag).await?;
                        if rearm {
                            if let Some(p) = &previous {
                                self.disarm(p).await;
                            }
                        }
                        self.set_armed(&target, armed_now);
                    }
                }
                None => {
                    let armed = self.arm(self.keys.sched_timer_key(&c.id, c.next_run_at, self.token()), c.next_run_at).await?;
                    self.store.put_if_none_match(&self.keys.sched_key(&c.id), body).await?;
                    self.set_armed(&target, Some(armed));
                }
            }
        }
        for (b, _) in &w.schedules {
            if !state.schedules.iter().any(|c| c.id == b.id) {
                self.store.delete(&self.keys.sched_key(&b.id)).await?;
                let target = format!("sched:{}", b.id);
                if let Some(p) = self.armed_for(&target) {
                    self.disarm(&p).await;
                }
                self.set_armed(&target, None);
            }
        }

        // the outbox, after the commit
        for e in &state.outbox {
            self.send(e).await;
        }
        Ok(())
    }

    async fn send(&self, e: &OutboxEntry) {
        let (address, msg) = crate::wire::message_out(e, &self.server_url);
        if let Err(err) = self.router.route(&address, &msg).await {
            tracing::warn!(address = %address, error = %err, "message not delivered");
        }
    }
}

pub fn unavailable(e: StoreError) -> Unavailable {
    Unavailable::new(e.to_string())
}
