//! One request against one origin, serialised and committed.
//!
//! Per origin, one actor at a time: load the document, run the kernel, drain
//! what the step left owed, write what changed, arm the next deadline, hand
//! the outbox to the router. The write is conditional on the version read; a
//! lost race re-reads and re-decides.
//!
//! The cache holds the last document this node read or wrote for an origin.
//! The owner of an origin trusts it: every write to the origin goes through
//! the owner. Any other node revalidates it with `If-None-Match` before use.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use echod_kernel::{Config as KernelConfig, OutboxEntry, Promise, PromiseState, Schedule, State, TaskState};
use resonate_core::{ResonateRouter, Unavailable};

use crate::doc::{self, Loaded};
use crate::keys::KeySpace;
use crate::nodes::Nodes;
use crate::store::{Etag, Read, Store, StoreError};
use crate::timers::TimerQueue;

/// A document this node has seen, and the version it saw.
#[derive(Clone)]
pub struct Cached {
    pub loaded: Loaded,
    pub etag: Etag,
}

pub struct Applier {
    store: Arc<dyn Store>,
    keys: KeySpace,
    cfg: KernelConfig,
    nodes: Arc<Nodes>,
    timers: Arc<TimerQueue>,
    router: Arc<dyn ResonateRouter>,
    server_url: String,
    cache: Mutex<HashMap<String, Cached>>,
    cache_entries: usize,
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
        timers: Arc<TimerQueue>,
        router: Arc<dyn ResonateRouter>,
        server_url: String,
        cache_entries: usize,
    ) -> Self {
        Self {
            store,
            keys,
            cfg,
            nodes,
            timers,
            router,
            server_url,
            cache: Mutex::new(HashMap::new()),
            cache_entries: cache_entries.max(1),
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
        self.cache.lock().unwrap_or_else(|e| e.into_inner()).get(origin).cloned()
    }

    fn remember(&self, origin: &str, c: Cached) {
        let mut cache = self.cache.lock().unwrap_or_else(|e| e.into_inner());
        if cache.len() >= self.cache_entries && !cache.contains_key(origin) {
            // Crude but bounded: drop an arbitrary entry.
            if let Some(k) = cache.keys().next().cloned() {
                cache.remove(&k);
            }
        }
        cache.insert(origin.to_string(), c);
    }

    pub fn forget(&self, origin: &str) {
        self.cache.lock().unwrap_or_else(|e| e.into_inner()).remove(origin);
    }

    /// Load an origin's document: from the cache when this node owns the
    /// origin, revalidated against the store otherwise.
    async fn load(&self, origin: &str) -> Result<(Loaded, Option<Etag>), Unavailable> {
        let key = self.keys.doc_key(origin);
        if let Some(c) = self.cached(origin) {
            if self.nodes.owns(origin) {
                return Ok((c.loaded, Some(c.etag)));
            }
            match self.store.get_if_none_match(&key, &c.etag).await.map_err(unavailable)? {
                Read::NotModified => return Ok((c.loaded, Some(c.etag))),
                Read::Absent => {
                    self.forget(origin);
                    return Ok((Loaded { rows: vec![], row_count: 0, bytes: 0 }, None));
                }
                Read::Body(bytes, etag) => {
                    let loaded = doc::decode(&bytes).map_err(Unavailable::new)?;
                    self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone() });
                    return Ok((loaded, Some(etag)));
                }
            }
        }
        match self.store.get(&key).await.map_err(unavailable)? {
            None => Ok((Loaded { rows: vec![], row_count: 0, bytes: 0 }, None)),
            Some((bytes, etag)) => {
                let loaded = doc::decode(&bytes).map_err(Unavailable::new)?;
                self.remember(origin, Cached { loaded: loaded.clone(), etag: etag.clone() });
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
        F: Fn(&mut State) -> R + Send,
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
            let r = step(&mut state);
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
        self.apply(Some(origin), None, now, move |s: &mut State| {
            let ids: Vec<String> = s.objects.iter().map(|p| p.id.clone()).collect();
            for id in ids {
                s.process_promise_timeout(&echod_kernel::PromiseTimeoutReq { id: id.clone() }, now, &cfg);
                s.process_lease_timeout(&echod_kernel::TaskLeaseTimeoutReq { id: id.clone() }, now, &cfg);
                s.process_retry_timeout(&echod_kernel::TaskRetryTimeoutReq { id }, now, &cfg);
            }
        })
        .await
    }

    /// Discharge every settled promise's callbacks and listeners, then fire
    /// every retry that is due — the internal steps a request leaves owed.
    fn drain(&self, s: &mut State, now: u64) {
        let cfg = self.cfg;
        let mut rounds = 0;
        loop {
            rounds += 1;
            let mut did = false;
            let owed: Vec<(String, Vec<String>, Vec<String>)> = s
                .objects
                .iter()
                .filter(|p| p.state != PromiseState::Pending)
                .filter(|p| !p.callbacks.is_empty() || !p.listeners.is_empty())
                .map(|p| (p.id.clone(), p.callbacks.clone(), p.listeners.clone()))
                .collect();
            for (awaited, callbacks, listeners) in owed {
                for awaiter in callbacks {
                    s.process_callback(&echod_kernel::PromiseRegisterCallbackReq { awaited: awaited.clone(), awaiter }, now, &cfg);
                    did = true;
                }
                for address in listeners {
                    s.process_listener(&echod_kernel::PromiseRegisterListenerReq { awaited: awaited.clone(), address }, now, &cfg);
                    did = true;
                }
            }
            let due: Vec<String> = s
                .objects
                .iter()
                .filter(|p| p.state == PromiseState::Pending)
                .filter(|p| p.task.as_ref().map(|t| t.state == TaskState::Pending && t.retry_timeout_at.map(|d| d <= now).unwrap_or(false)).unwrap_or(false))
                .map(|p| p.id.clone())
                .collect();
            for id in due {
                s.process_retry_timeout(&echod_kernel::TaskRetryTimeoutReq { id }, now, &cfg);
                did = true;
            }
            if !did || rounds > 64 {
                return;
            }
        }
    }

    /// The nearest deadline the document owes a timer for.
    pub fn next_deadline(rows: &[Promise]) -> Option<u64> {
        let mut min: Option<u64> = None;
        let mut note = |d: u64| min = Some(min.map_or(d, |m| m.min(d)));
        for p in rows {
            if p.state == PromiseState::Pending && echod_kernel::tags::exec_otype(&p.tags) != echod_kernel::tags::OType::Internal {
                note(p.timeout_at);
            }
            if let Some(t) = &p.task {
                if let Some(d) = t.retry_timeout_at {
                    note(d);
                }
                if let Some(d) = t.lease_timeout_at {
                    note(d);
                }
            }
        }
        min
    }

    /// Write what the step changed: the timer first, the document, the
    /// schedules, then the old timer; and hand over the outbox.
    async fn commit(&self, w: &mut Working, state: &State, _now: u64) -> Result<(), StoreError> {
        let changed = doc::changed(&w.loaded.rows, &state.objects);
        let old_deadline = Self::next_deadline(&w.loaded.rows);
        let new_deadline = Self::next_deadline(&state.objects);

        if !changed.is_empty() {
            // (1) the new timer, before the state that arms it
            if new_deadline != old_deadline {
                if let Some(at) = new_deadline {
                    let key = self.keys.timer_key(&w.origin, at);
                    self.store.put(&key, Vec::new()).await?;
                    self.timers.arm(at, key);
                }
            }
            // (2) the document
            let key = self.keys.doc_key(&w.origin);
            let etag = match &w.etag {
                None => {
                    let body = doc::encode(&state.objects);
                    let etag = self.store.put_if_none_match(&key, body.clone()).await?;
                    self.remember(&w.origin, Cached { loaded: Loaded { rows: state.objects.clone(), row_count: state.objects.len(), bytes: body.len() as u64 }, etag: etag.clone() });
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
                            Cached { loaded: Loaded { rows: state.objects.clone(), row_count: w.loaded.row_count + changed.len(), bytes: w.loaded.bytes + body.len() as u64 }, etag: new.clone() },
                        );
                        new
                    } else {
                        let body = doc::encode(&state.objects);
                        let new = self.store.put_if_match(&key, body.clone(), etag).await?;
                        self.remember(&w.origin, Cached { loaded: Loaded { rows: state.objects.clone(), row_count: state.objects.len(), bytes: body.len() as u64 }, etag: new.clone() });
                        new
                    }
                }
            };
            let _ = etag;
            // (3) the old timer
            if new_deadline != old_deadline {
                if let Some(at) = old_deadline {
                    let key = self.keys.timer_key(&w.origin, at);
                    if self.store.delete(&key).await.is_ok() {
                        self.timers.disarm(at, &key);
                    }
                }
            }
        }

        // schedules: each its own object
        for c in &state.schedules {
            let before = w.schedules.iter().find(|(b, _)| b.id == c.id);
            let body = serde_json::to_vec(c).expect("a schedule serialises");
            match before {
                Some((b, etag)) => {
                    if serde_json::to_vec(b).ok() != Some(body.clone()) {
                        if b.next_run_at != c.next_run_at {
                            let key = self.keys.sched_timer_key(&c.id, c.next_run_at);
                            self.store.put(&key, Vec::new()).await?;
                            self.timers.arm(c.next_run_at, key);
                        }
                        self.store.put_if_match(&self.keys.sched_key(&c.id), body, etag).await?;
                        if b.next_run_at != c.next_run_at {
                            let key = self.keys.sched_timer_key(&c.id, b.next_run_at);
                            if self.store.delete(&key).await.is_ok() {
                                self.timers.disarm(b.next_run_at, &key);
                            }
                        }
                    }
                }
                None => {
                    let key = self.keys.sched_timer_key(&c.id, c.next_run_at);
                    self.store.put(&key, Vec::new()).await?;
                    self.timers.arm(c.next_run_at, key);
                    self.store.put_if_none_match(&self.keys.sched_key(&c.id), body).await?;
                }
            }
        }
        for (b, _) in &w.schedules {
            if !state.schedules.iter().any(|c| c.id == b.id) {
                self.store.delete(&self.keys.sched_key(&b.id)).await?;
                let key = self.keys.sched_timer_key(&b.id, b.next_run_at);
                if self.store.delete(&key).await.is_ok() {
                    self.timers.disarm(b.next_run_at, &key);
                }
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
