//! The `ResonateServer`: dispatch, forwarding, lifecycle.
//!
//! A request names an origin. If this node owns the origin, it runs the
//! request; otherwise it forwards the request to the owner over HTTP and
//! relays the answer, so one node writes each origin and its cache stays
//! truthful. Forwarding is an optimisation: a node that gets a request it does
//! not own and cannot forward runs it anyway, revalidating its cache first,
//! and the conditional write keeps it correct.

use std::sync::Arc;
use std::time::Duration;

use async_trait::async_trait;
use echod_kernel as k;
use resonate_core::types::{self as w, RequestEnvelope, ResponseEnvelope};
use resonate_core::{util, ResonateRouter, ResonateServer, Unavailable};
use serde::de::DeserializeOwned;
use validator::Validate;

use crate::applier::Applier;
use crate::config::Config;
use crate::env::{Clock, HttpPeers, Peers, SystemClock};
use crate::keys::{origin_of, KeySpace};
use crate::metrics::{self, Metrics, Route};
use crate::nodes::Nodes;
use crate::push::Router;
use crate::schedules::Schedules;
use crate::store::{self, Store};
use crate::timers::{TimerWheel, Timers};
use crate::wire;

pub use crate::env::FORWARDED;
/// The header every answer carries: which node answered.
pub const NODE: &str = "x-echod-node";

pub struct Server {
    cfg: Config,
    store: Arc<dyn Store>,
    nodes: Arc<Nodes>,
    applier: Arc<Applier>,
    timers: Arc<Timers>,
    clock: Arc<dyn Clock>,
    peers: Arc<dyn Peers>,
    metrics: Arc<Metrics>,
    shutdown: tokio::sync::watch::Sender<bool>,
    crashed: tokio::sync::watch::Sender<bool>,
    tasks: tokio::sync::Mutex<Vec<tokio::task::JoinHandle<()>>>,
}

impl Server {
    /// A server over `store` with HTTP push as its only transport.
    pub fn new(cfg: Config, store: Arc<dyn Store>) -> Arc<Self> {
        let router: Arc<dyn ResonateRouter> = Arc::new(Router::http_push());
        Self::with_router(cfg, store, router)
    }

    pub fn with_router(cfg: Config, store: Arc<dyn Store>, router: Arc<dyn ResonateRouter>) -> Arc<Self> {
        Self::with_env(cfg, store, router, Arc::new(SystemClock), Arc::new(HttpPeers::new()), Arc::new(crate::env::NoObserver))
    }

    /// A server whose clock, peers and observer are supplied: what a
    /// simulation builds.
    pub fn with_env(cfg: Config, store: Arc<dyn Store>, router: Arc<dyn ResonateRouter>, clock: Arc<dyn Clock>, peers: Arc<dyn Peers>, observer: Arc<dyn crate::env::Observer>) -> Arc<Self> {
        let keys = KeySpace::new(&cfg.prefix, cfg.timer_bucket_ms);
        // Every call on the bucket goes through the meter.
        let metrics = Metrics::new();
        let store: Arc<dyn Store> = Arc::new(metrics::MeteredStore::new(store, keys.clone(), Arc::clone(&metrics)));
        let url = cfg.url.clone().unwrap_or_else(|| format!("http://{}", cfg.bind.replace("0.0.0.0", "127.0.0.1")));
        let id = cfg.node_id.clone().unwrap_or_else(|| format!("{:016x}", crate::keys::fnv1a(&format!("{}/{}", url, clock.now()))));
        let nodes = Arc::new(Nodes::new(Arc::clone(&store), keys.clone(), id, url.clone(), Duration::from_millis(cfg.heartbeat_ms), cfg.node_ttl_ms, Arc::clone(&clock), Arc::clone(&metrics)));
        let wheel = Arc::new(TimerWheel::new());
        let cache: Arc<dyn crate::cache::Cache> = Arc::new(crate::cache::MemoryCache::new(cfg.cache_entries, cfg.cache_bytes));
        let applier = Arc::new(Applier::new(Arc::clone(&store), keys.clone(), cfg.kernel(), Arc::clone(&nodes), Arc::clone(&wheel), router, url, Arc::clone(&cache), Arc::clone(&clock), observer, Arc::clone(&metrics)));
        let schedules = Arc::new(Schedules::new(Arc::clone(&applier)));
        let timers = Arc::new(Timers::new(Arc::clone(&store), keys, Arc::clone(&wheel), Arc::clone(&nodes), Arc::clone(&applier), schedules, Arc::clone(&metrics)));
        // The gauges: read when scraped, from the state as it is then.
        {
            let (nodes, cache, wheel) = (Arc::clone(&nodes), Arc::clone(&cache), Arc::clone(&wheel));
            metrics.set_snapshot(move || {
                let m = nodes.members();
                let c = cache.stats();
                metrics::Snapshot {
                    cache_entries: c.entries as u64,
                    cache_bytes: c.bytes,
                    cache_evictions: c.evictions,
                    epoch: m.epoch,
                    members: m.members.len() as u64,
                    fresh: nodes.fresh(nodes.now()),
                    acting: nodes.acting(),
                    timers_armed: wheel.len() as u64,
                }
            });
        }
        let (shutdown, _) = tokio::sync::watch::channel(false);
        let (crashed, _) = tokio::sync::watch::channel(false);
        Arc::new(Self { cfg, store, nodes, applier, timers, clock, peers, metrics, shutdown, crashed, tasks: tokio::sync::Mutex::new(Vec::new()) })
    }

    /// What this node counts and measures.
    pub fn metrics(&self) -> &Arc<Metrics> {
        &self.metrics
    }

    pub fn config(&self) -> &Config {
        &self.cfg
    }

    pub fn nodes(&self) -> &Arc<Nodes> {
        &self.nodes
    }

    /// Whether this node may act as a member right now: its view is fresh.
    pub fn serving(&self) -> bool {
        self.nodes.fresh(self.nodes.now())
    }

    /// Whether this node acts as owner of what the members make it the
    /// owner of: fresh, in a configuration with members.
    pub fn acting(&self) -> bool {
        self.nodes.acting()
    }

    pub fn timers(&self) -> &Arc<Timers> {
        &self.timers
    }

    pub fn applier(&self) -> &Arc<Applier> {
        &self.applier
    }

    /// The clock a request sees.
    fn now(&self, req: &RequestEnvelope) -> u64 {
        match (self.cfg.debug, req.head.debug_time) {
            (true, Some(t)) => t.max(0) as u64,
            _ => self.nodes.now(),
        }
    }

    pub fn clock(&self) -> &Arc<dyn Clock> {
        &self.clock
    }

    /// Die: every background task is aborted where it stands, nothing is
    /// announced, nothing is flushed. For a simulation; a crashed server
    /// answers nothing more and is dropped.
    pub async fn crash(&self) {
        let _ = self.crashed.send(true);
        let tasks: Vec<_> = self.tasks.lock().await.drain(..).collect();
        for t in tasks {
            t.abort();
        }
    }

    /// Fires when the server has crashed.
    pub fn crashed(&self) -> tokio::sync::watch::Receiver<bool> {
        self.crashed.subscribe()
    }

    /// Run `req` here, or at the owner of `origin`. Returns the answer and
    /// the id of the node that produced it.
    pub async fn process_from(&self, req: &RequestEnvelope, forwarded: bool) -> Result<(ResponseEnvelope, String), Unavailable> {
        let started = std::time::Instant::now();
        let (r, route) = self.route(req, forwarded).await;
        let status = match &r {
            Ok((resp, _)) => resp.head.status.clamp(0, u16::MAX as i32) as u16,
            Err(_) => 503,
        };
        self.metrics.request(&req.kind, route, status, started);
        r
    }

    /// `process_from`, and where the request ran.
    async fn route(&self, req: &RequestEnvelope, forwarded: bool) -> (Result<(ResponseEnvelope, String), Unavailable>, Route) {
        let here = if forwarded { Route::Relayed } else { Route::Local };
        let now = self.now(req);
        let me = self.nodes.id();
        let origin = match origin_of_request(req) {
            Ok(Some(o)) => o,
            Ok(None) => return (self.dispatch(req, None, now).await.map(|resp| (resp, me)), here),
            Err(e) => return (Ok((ResponseEnvelope::error(req.kind.clone(), req.head.corr_id.clone(), 400, &e), me)), here),
        };
        // Forward to the node the members make the owner, for its cache and
        // its wheel; serve here otherwise. Safety does not depend on which
        // node writes: every write is conditional on the version loaded.
        if !forwarded && self.cfg.forward {
            if let Some(owner) = self.nodes.owner(&origin).filter(|o| o.id != me) {
                let started = std::time::Instant::now();
                let r = self.peers.forward(&owner.url, &me, req).await;
                self.metrics.forward(if r.is_ok() { metrics::ForwardOutcome::Answered } else { metrics::ForwardOutcome::Unavailable }, started);
                return (r.map(|resp| (resp, owner.id)), Route::Forwarded);
            }
        }
        (self.dispatch(req, Some(origin), now).await.map(|resp| (resp, me)), here)
    }

    async fn dispatch(&self, req: &RequestEnvelope, origin: Option<String>, now: u64) -> Result<ResponseEnvelope, Unavailable> {
        let kind = req.kind.clone();
        let corr = req.head.corr_id.clone();
        let cfg = self.applier.kernel_config();
        let err = |status: u16, msg: &str| Ok(ResponseEnvelope::error(kind.clone(), corr.clone(), status as i32, msg));
        macro_rules! parsed {
            ($t:ty) => {
                match parse::<$t>(&req.data) {
                    Ok(v) => v,
                    Err(m) => return err(400, &m),
                }
            };
        }
        // A request about a schedule names no document; the rest name one.
        let doc: Option<&str> = origin.as_deref().filter(|_| !kind.starts_with("schedule."));
        macro_rules! run {
            ($schedule:expr, $step:expr) => {{
                let step = $step;
                self.applier.apply(doc, $schedule, now, None, move |s: &mut k::State, now: u64| (step(s, now), false)).await?.0
            }};
        }
        // The envelope to the kernel's request: the protocol's checks, then
        // one call, `handle`, which the fleet model's `Begin` names.
        let (q, schedule, action_kind): (k::Request, Option<String>, Option<String>) = match kind.as_str() {
            "promise.get" => {
                let d = parsed!(w::PromiseGetData);
                (k::Request::PromiseGet(k::PromiseGetReq { id: d.id }), None, None)
            }
            "promise.create" => {
                let d = parsed!(w::PromiseCreateData);
                match wire::create_in(&d) {
                    Ok(q) => (k::Request::PromiseCreate(q), None, None),
                    Err(m) => return err(400, &m),
                }
            }
            "promise.settle" => {
                let d = parsed!(w::PromiseSettleData);
                (k::Request::PromiseSettle(wire::settle_in_req(&d)), None, None)
            }
            "promise.register_callback" => {
                let d = parsed!(w::PromiseRegisterCallbackData);
                (k::Request::PromiseRegisterCallback(k::PromiseRegisterCallbackReq { awaited: d.awaited, awaiter: d.awaiter }), None, None)
            }
            "promise.register_listener" => {
                let d = parsed!(w::PromiseRegisterListenerData);
                if !resonate_core::is_valid_address(&d.address) {
                    return err(400, "Address must be a URI with a scheme");
                }
                (k::Request::PromiseRegisterListener(k::PromiseRegisterListenerReq { awaited: d.awaited, address: d.address }), None, None)
            }
            "task.get" => {
                let d = parsed!(w::TaskGetData);
                (k::Request::TaskGet(k::TaskGetReq { id: d.id }), None, None)
            }
            "task.create" => {
                let d = parsed!(w::TaskCreateData);
                let action = match wire::create_in(&d.action.data) {
                    Ok(q) => q,
                    Err(m) => return err(400, &m),
                };
                let ttl = match wire::nat(d.ttl, "ttl") {
                    Ok(v) => v,
                    Err(m) => return err(400, &m),
                };
                (k::Request::TaskCreate(k::TaskCreateReq { pid: d.pid, ttl, action }), None, None)
            }
            "task.acquire" => {
                let d = parsed!(w::TaskAcquireData);
                let (version, ttl) = match (wire::nat(d.version, "version"), wire::nat(d.ttl, "ttl")) {
                    (Ok(v), Ok(t)) => (v, t),
                    (Err(m), _) | (_, Err(m)) => return err(400, &m),
                };
                (k::Request::TaskAcquire(k::TaskAcquireReq { id: d.id, version, pid: d.pid, ttl }), None, None)
            }
            "task.release" => {
                let d = parsed!(w::TaskReleaseData);
                let version = match wire::nat(d.version, "version") {
                    Ok(v) => v,
                    Err(m) => return err(400, &m),
                };
                (k::Request::TaskRelease(k::TaskReleaseReq { id: d.id, version }), None, None)
            }
            "task.fulfill" => {
                let d = parsed!(w::TaskFulfillData);
                let version = match wire::nat(d.version, "version") {
                    Ok(v) => v,
                    Err(m) => return err(400, &m),
                };
                let q = k::TaskFulfillReq {
                    id: d.id,
                    version,
                    action: k::PromiseSettleReq { id: d.action.data.id, state: wire::settle_in(d.action.data.state), value: wire::value_in(&d.action.data.value) },
                };
                (k::Request::TaskFulfill(q), None, None)
            }
            "task.suspend" => {
                let d = parsed!(w::TaskSuspendData);
                let version = match wire::nat(d.version, "version") {
                    Ok(v) => v,
                    Err(m) => return err(400, &m),
                };
                let actions = d.actions.into_iter().map(|a| k::PromiseRegisterCallbackReq { awaited: a.data.awaited, awaiter: a.data.awaiter }).collect();
                (k::Request::TaskSuspend(k::TaskSuspendReq { id: d.id, version, actions }), None, None)
            }
            "task.fence" => {
                let d = parsed!(w::TaskFenceData);
                let version = match wire::nat(d.version, "version") {
                    Ok(v) => v,
                    Err(m) => return err(400, &m),
                };
                // A fence and its action commit as one write on one document,
                // so the action must live in the task's origin.
                if let Some(aid) = d.action.data.get("id").and_then(|v| v.as_str()) {
                    if origin_of(aid) != origin_of(&d.id) {
                        return err(400, "Action must belong to the task's origin");
                    }
                }
                let action = match d.action.kind.as_str() {
                    "promise.create" => match parse::<w::PromiseCreateData>(&d.action.data).and_then(|c| wire::create_in(&c)) {
                        Ok(c) => k::TaskFenceAction::Create(c),
                        Err(m) => return err(400, &m),
                    },
                    "promise.settle" => match parse::<w::PromiseSettleData>(&d.action.data) {
                        Ok(c) => k::TaskFenceAction::Settle(wire::settle_in_req(&c)),
                        Err(m) => return err(400, &m),
                    },
                    other => return err(400, &format!("Unsupported fence action: {other}")),
                };
                (k::Request::TaskFence(k::TaskFenceReq { id: d.id, version, action }), None, Some(d.action.kind))
            }
            "task.heartbeat" => {
                let d = parsed!(w::TaskHeartbeatData);
                let mut tasks = Vec::with_capacity(d.tasks.len());
                for t in d.tasks {
                    match wire::nat(t.version, "version") {
                        Ok(v) => tasks.push(k::TaskRef { id: t.id, version: v }),
                        Err(m) => return err(400, &m),
                    }
                }
                (k::Request::TaskHeartbeat(k::TaskHeartbeatReq { pid: d.pid, tasks }), None, None)
            }
            "task.halt" => {
                let d = parsed!(w::TaskHaltData);
                (k::Request::TaskHalt(k::TaskHaltReq { id: d.id }), None, None)
            }
            "task.continue" => {
                let d = parsed!(w::TaskContinueData);
                (k::Request::TaskContinue(k::TaskContinueReq { id: d.id }), None, None)
            }
            "schedule.get" => {
                let d = parsed!(w::ScheduleGetData);
                (k::Request::ScheduleGet(k::ScheduleGetReq { id: d.id.clone() }), Some(d.id), None)
            }
            "schedule.create" => {
                let d = parsed!(w::ScheduleCreateData);
                if !util::is_valid_cron(&d.cron) {
                    return err(400, "Invalid cron expression");
                }
                let promise_timeout = match wire::nat(d.promise_timeout, "promiseTimeout") {
                    Ok(v) => v,
                    Err(m) => return err(400, &m),
                };
                let next = util::compute_next_cron(&d.cron, now as i64).max(now as i64 + 1) as u64;
                let id = d.id.clone();
                let q = k::ScheduleCreateReq {
                    id: d.id,
                    cron: d.cron,
                    promise_id: d.promise_id,
                    promise_timeout,
                    promise_param: wire::value_in(&d.promise_param),
                    promise_tags: wire::create_tags(&d.promise_tags),
                    next_run_at: next,
                };
                (k::Request::ScheduleCreate(q), Some(id), None)
            }
            "schedule.delete" => {
                let d = parsed!(w::ScheduleDeleteData);
                (k::Request::ScheduleDelete(k::ScheduleDeleteReq { id: d.id.clone() }), Some(d.id), None)
            }
            "promise.search" | "task.search" | "schedule.search" => return err(403, "Search operations are not supported"),
            "debug.reset" | "debug.snap" | "debug.tick" => return err(403, "Debug operations are not supported"),
            _ => return err(400, &format!("Unknown request kind: {kind}")),
        };
        let r = run!(schedule.as_deref(), |s: &mut k::State, now: u64| s.handle(&q, now, &cfg));
        Ok(wire::response_out(&kind, &corr, action_kind.as_deref(), &r))
    }
}


/// Parse and validate a request's `data`.
fn parse<T: DeserializeOwned + Validate>(data: &serde_json::Value) -> Result<T, String> {
    let v: T = serde_json::from_value(data.clone()).map_err(|e| format!("Invalid request data: {e}"))?;
    v.validate().map_err(|e| w::format_validation_errors(&e))?;
    Ok(v)
}

/// The document a request is about. `None` for a request that has none.
/// Schedules are their own objects; the one they fire into is decided when
/// they fire, so a schedule request's "origin" is the schedule's id.
pub fn origin_of_request(req: &RequestEnvelope) -> Result<Option<String>, String> {
    let d = &req.data;
    let id = |k: &str| d.get(k).and_then(|v| v.as_str()).map(|s| s.to_string());
    let origin = match req.kind.as_str() {
        "promise.get" | "promise.create" | "promise.settle" | "task.get" | "task.acquire" | "task.release" | "task.fulfill" | "task.suspend" | "task.fence" | "task.halt" | "task.continue" => {
            id("id").map(|s| origin_of(&s).to_string())
        }
        "promise.register_callback" | "promise.register_listener" => id("awaited").map(|s| origin_of(&s).to_string()),
        "task.create" => d.pointer("/action/data/id").and_then(|v| v.as_str()).map(|s| origin_of(s).to_string()),
        "task.heartbeat" => d.pointer("/tasks/0/id").and_then(|v| v.as_str()).map(|s| origin_of(s).to_string()),
        "schedule.get" | "schedule.create" | "schedule.delete" => id("id"),
        _ => return Ok(None),
    };
    match origin {
        Some(o) if !o.is_empty() => Ok(Some(o)),
        _ => Err("Request data does not name an id".to_string()),
    }
}

#[async_trait]
impl ResonateServer for Server {
    async fn init(&self, debug: bool) -> Result<(), Unavailable> {
        let now = self.nodes.now();
        self.nodes.refresh(now).await.map_err(store::unavailable_err)?;
        if debug {
            return Ok(());
        }
        let rx = self.shutdown.subscribe();
        let mut tasks = self.tasks.lock().await;
        tasks.push(Arc::clone(&self.nodes).spawn(rx.clone()));
        tasks.push(Arc::clone(&self.timers).spawn(rx));
        Ok(())
    }

    async fn stop(&self) -> Result<(), Unavailable> {
        let _ = self.shutdown.send(true);
        let tasks: Vec<_> = self.tasks.lock().await.drain(..).collect();
        for t in tasks {
            let _ = t.await;
        }
        self.nodes.leave().await;
        Ok(())
    }

    /// Ready to serve: the store answers, and this node has read a
    /// configuration naming it, so it forwards and fires deadlines as the
    /// members intend. It would answer correctly before that; it would
    /// not route.
    async fn ready(&self) -> bool {
        self.store.ready().await && self.acting()
    }

    async fn process(&self, req: &RequestEnvelope) -> Result<ResponseEnvelope, Unavailable> {
        self.process_from(req, false).await.map(|(resp, _)| resp)
    }
}
