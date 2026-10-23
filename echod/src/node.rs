//! The executor: the core's effects, performed.
//!
//! One `State` behind one lock. Every event goes through `apply`, which
//! takes the lock, runs the core's one step, drops the lock, and performs
//! what came out: a store call is spawned and its answer comes back as
//! `Completed`; a reply wakes the request waiting for it; a message is
//! pushed; a wake resets the one timer; a note goes to the metrics, the
//! log, and whoever listens. The core never waits, so the lock is held
//! for a step and no longer, and nothing here decides anything.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, Weak};
use std::time::Duration;

use async_trait::async_trait;
use echod_logic::members::Membership;
use echod_logic::types::{Effect, Event, Note, RequestId};
use echod_logic::State;
use resonate_core::types::{Message, RequestEnvelope, ResponseEnvelope};
use resonate_core::{ResonateRouter, ResonateServer, Unavailable};
use tokio::sync::{oneshot, watch};

use crate::config::Config;
use crate::env::{Clock, NoNotes, Notes, SystemClock};
use crate::metrics::{self, MessageOutcome, Metrics};
use crate::push::Router;
use crate::store::{self, Store};

/// The header every answer carries: which node answered.
pub const NODE: &str = "x-echod-node";

type Reply = Result<ResponseEnvelope, Unavailable>;

pub struct Node {
    me: Weak<Node>,
    cfg: Config,
    id: String,
    state: Mutex<State>,
    store: Arc<dyn Store>,
    router: Arc<dyn ResonateRouter>,
    clock: Arc<dyn Clock>,
    notes: Arc<dyn Notes>,
    metrics: Arc<Metrics>,
    replies: Mutex<HashMap<RequestId, oneshot::Sender<Reply>>>,
    next_request: AtomicU64,
    /// When the core next wants a tick, as the wake task reads it.
    wake: watch::Sender<Option<tokio::time::Instant>>,
    stopped: watch::Sender<bool>,
    crashed: watch::Sender<bool>,
    tasks: Mutex<Vec<tokio::task::JoinHandle<()>>>,
}

impl Node {
    /// A node over `store` with HTTP push as its only transport.
    pub fn new(cfg: Config, store: Arc<dyn Store>) -> Arc<Self> {
        let router: Arc<dyn ResonateRouter> = Arc::new(Router::http_push());
        Self::with_router(cfg, store, router)
    }

    pub fn with_router(cfg: Config, store: Arc<dyn Store>, router: Arc<dyn ResonateRouter>) -> Arc<Self> {
        Self::with_env(cfg, store, router, Arc::new(SystemClock), Arc::new(NoNotes))
    }

    /// A node whose clock and listener are supplied: what a simulation
    /// builds.
    pub fn with_env(cfg: Config, store: Arc<dyn Store>, router: Arc<dyn ResonateRouter>, clock: Arc<dyn Clock>, notes: Arc<dyn Notes>) -> Arc<Self> {
        let keys = echod_logic::keys::KeySpace::new(&cfg.prefix, cfg.timer_bucket_ms);
        // Every call on the bucket goes through the meter.
        let metrics = Metrics::new();
        let appendable = store.supports_append();
        let store: Arc<dyn Store> = Arc::new(metrics::MeteredStore::new(store, keys, Arc::clone(&metrics)));
        let id = cfg.node_id.clone().unwrap_or_else(|| format!("{:016x}", echod_logic::keys::fnv1a(&format!("{}/{}", cfg.node_url(), clock.now()))));
        let state = State::new(cfg.logic(id.clone(), appendable));
        let (wake, _) = watch::channel(None);
        let (stopped, _) = watch::channel(false);
        let (crashed, _) = watch::channel(false);
        let node = Arc::new_cyclic(|me| Node {
            me: me.clone(),
            cfg,
            id,
            state: Mutex::new(state),
            store,
            router,
            clock,
            notes,
            metrics,
            replies: Mutex::new(HashMap::new()),
            next_request: AtomicU64::new(1),
            wake,
            stopped,
            crashed,
            tasks: Mutex::new(Vec::new()),
        });
        // The gauges: read when scraped, from the state as it is then.
        let weak = Arc::downgrade(&node);
        node.metrics.set_snapshot(move || weak.upgrade().map(|n| n.lock().snapshot()).unwrap_or_default());
        node
    }

    fn me(&self) -> Arc<Node> {
        self.me.upgrade().expect("the node outlives its tasks")
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// What this node counts and measures.
    pub fn metrics(&self) -> &Arc<Metrics> {
        &self.metrics
    }

    pub fn config(&self) -> &Config {
        &self.cfg
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    pub fn url(&self) -> String {
        self.cfg.node_url()
    }

    pub fn clock(&self) -> &Arc<dyn Clock> {
        &self.clock
    }

    /// Whether this node acts as owner of what the members make it the
    /// owner of: fresh, in a configuration with members.
    pub fn acting(&self) -> bool {
        self.lock().acting()
    }

    pub fn membership(&self) -> Membership {
        self.lock().membership()
    }

    /// The member that owns `target`, by the members this node holds.
    pub fn owner(&self, target: &str) -> Option<String> {
        self.lock().owner(target)
    }

    /// Fires when the node has crashed.
    pub fn crashed(&self) -> watch::Receiver<bool> {
        self.crashed.subscribe()
    }

    /// Die: nothing more is applied, nothing is announced, nothing is
    /// flushed; whoever waits for an answer gets none. For a simulation; a
    /// crashed node is dropped.
    pub async fn crash(&self) {
        let _ = self.crashed.send(true);
        let tasks: Vec<_> = self.tasks.lock().unwrap_or_else(|e| e.into_inner()).drain(..).collect();
        for t in tasks {
            t.abort();
        }
        self.replies.lock().unwrap_or_else(|e| e.into_inner()).clear();
    }

    // -----------------------------------------------------------------------
    // The step, and the effects
    // -----------------------------------------------------------------------

    /// One event through the core, and its effects performed.
    pub fn apply(&self, event: Event) {
        if *self.crashed.borrow() {
            return;
        }
        let (effects, stopped) = {
            let mut s = self.lock();
            let effects = s.on_event(event);
            (effects, s.stopped())
        };
        for e in effects {
            self.perform(e);
        }
        if stopped {
            let _ = self.stopped.send(true);
        }
    }

    fn perform(&self, e: Effect) {
        match e {
            Effect::Store { op, call } => {
                let node = self.me();
                let store = Arc::clone(&self.store);
                let mut crashed = self.crashed();
                tokio::spawn(async move {
                    tokio::select! {
                        biased;
                        _ = crashed.changed() => {}
                        outcome = store::call(&*store, call) => {
                            let clock = node.clock.now();
                            node.apply(Event::Completed { op, outcome, clock });
                        }
                    }
                });
            }
            Effect::Reply { id, response } => {
                if let Some(tx) = self.replies.lock().unwrap_or_else(|e| e.into_inner()).remove(&id) {
                    let _ = tx.send(response);
                }
            }
            Effect::Send { address, message } => {
                let node = self.me();
                tokio::spawn(async move { node.send(address, message).await });
            }
            Effect::Wake { after_ms } => {
                let _ = self.wake.send(Some(tokio::time::Instant::now() + Duration::from_millis(after_ms)));
            }
            Effect::Note(n) => {
                self.metrics.note(&n);
                log(&n);
                self.notes.note(&self.id, &n);
            }
        }
    }

    async fn send(&self, address: String, msg: Message) {
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
            Message::Execute(_) => "execute",
            Message::Unblock(_) => "unblock",
        };
        self.metrics.message(kind, outcome, started);
    }

    /// The one timer: sleeps until the instant the core last asked for,
    /// then ticks; a new ask resets it.
    fn spawn_wake(self: &Arc<Self>) -> tokio::task::JoinHandle<()> {
        let node = Arc::clone(self);
        let mut rx = self.wake.subscribe();
        tokio::spawn(async move {
            loop {
                let at = *rx.borrow_and_update();
                match at {
                    None => {
                        if rx.changed().await.is_err() {
                            return;
                        }
                    }
                    Some(at) => {
                        tokio::select! {
                            biased;
                            r = rx.changed() => {
                                if r.is_err() {
                                    return;
                                }
                            }
                            _ = tokio::time::sleep_until(at) => {
                                let _ = node.wake.send_replace(None);
                                let clock = node.clock.now();
                                node.apply(Event::Tick { clock });
                            }
                        }
                    }
                }
            }
        })
    }
}

/// The notes a log line wants.
fn log(n: &Note) {
    match n {
        Note::ConfigurationRead { epoch, members } => tracing::info!(epoch, ?members, "configuration read"),
        Note::ConfigurationWritten { epoch, members } => tracing::info!(epoch, ?members, "configuration written"),
        Note::TimersLoaded { deadlines, wheel, epoch } => tracing::info!(deadlines, wheel, epoch, "timers loaded"),
        Note::BucketLoaded { bucket, deadlines } => tracing::debug!(bucket, deadlines, "timer bucket loaded"),
        Note::Raced { target, attempt } => tracing::debug!(%target, attempt, "lost a race; re-deciding"),
        Note::KeyNotDeleted { key, error } => tracing::debug!(%key, %error, "deadline key not deleted; it fires again"),
        Note::KeyUnparseable { key } => tracing::warn!(%key, "unparseable timer key dropped"),
        Note::FireFailed { key, error } => tracing::warn!(%key, %error, "sweep failed; the key stays"),
        Note::RefreshFailed { error } => tracing::warn!(%error, "node heartbeat failed"),
        Note::ListingFailed { error } => tracing::warn!(%error, "timer listing failed; will retry"),
        Note::MessageUndeliverable { address } => tracing::warn!(%address, "message undeliverable"),
        _ => {}
    }
}

#[async_trait]
impl ResonateServer for Node {
    /// Start: announce, list, read the configuration; then, unless the
    /// clock belongs to the caller, keep going on the one timer.
    async fn init(&self, debug: bool) -> Result<(), Unavailable> {
        let clock = self.clock.now();
        if !debug {
            let handle = self.me().spawn_wake();
            self.tasks.lock().unwrap_or_else(|e| e.into_inner()).push(handle);
        }
        self.apply(Event::Start { clock, loops: !debug });
        Ok(())
    }

    /// Stop: the announcement is withdrawn, the timer stops. Requests in
    /// flight are answered.
    async fn stop(&self) -> Result<(), Unavailable> {
        let mut stopped = self.stopped.subscribe();
        let clock = self.clock.now();
        self.apply(Event::Stop { clock });
        if !*stopped.borrow_and_update() {
            let _ = tokio::time::timeout(Duration::from_secs(5), stopped.changed()).await;
        }
        let tasks: Vec<_> = self.tasks.lock().unwrap_or_else(|e| e.into_inner()).drain(..).collect();
        for t in tasks {
            t.abort();
        }
        Ok(())
    }

    /// Ready to serve: the store answers, and this node has read a
    /// configuration naming it, so it fires deadlines as the members
    /// intend. It would answer correctly before that.
    async fn ready(&self) -> bool {
        self.store.ready().await && self.acting()
    }

    async fn process(&self, req: &RequestEnvelope) -> Result<ResponseEnvelope, Unavailable> {
        let started = std::time::Instant::now();
        let id = self.next_request.fetch_add(1, Ordering::Relaxed);
        let (tx, rx) = oneshot::channel();
        self.replies.lock().unwrap_or_else(|e| e.into_inner()).insert(id, tx);
        let clock = self.clock.now();
        self.apply(Event::Request { id, envelope: req.clone(), clock });
        let r = match rx.await {
            Ok(r) => r,
            Err(_) => Err(Unavailable::new("node crashed")),
        };
        let status = match &r {
            Ok(resp) => resp.head.status.clamp(0, u16::MAX as i32) as u16,
            Err(_) => 503,
        };
        self.metrics.request(&req.kind, status, started);
        r
    }
}
