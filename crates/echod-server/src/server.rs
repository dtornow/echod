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
use serde_json::json;
use validator::Validate;

use crate::applier::Applier;
use crate::config::Config;
use crate::keys::{origin_of, KeySpace};
use crate::nodes::Nodes;
use crate::push::Router;
use crate::schedules::Schedules;
use crate::store::{self, Store};
use crate::timers::{TimerWheel, Timers};
use crate::wire;

/// The header a forwarded request carries, so the owner never forwards it on.
pub const FORWARDED: &str = "x-echod-forwarded";
/// The header every answer carries: which node answered.
pub const NODE: &str = "x-echod-node";

pub struct Server {
    cfg: Config,
    store: Arc<dyn Store>,
    nodes: Arc<Nodes>,
    applier: Arc<Applier>,
    timers: Arc<Timers>,
    client: reqwest::Client,
    shutdown: tokio::sync::watch::Sender<bool>,
    tasks: tokio::sync::Mutex<Vec<tokio::task::JoinHandle<()>>>,
}

impl Server {
    /// A server over `store` with HTTP push as its only transport.
    pub fn new(cfg: Config, store: Arc<dyn Store>) -> Arc<Self> {
        let router: Arc<dyn ResonateRouter> = Arc::new(Router::http_push());
        Self::with_router(cfg, store, router)
    }

    pub fn with_router(cfg: Config, store: Arc<dyn Store>, router: Arc<dyn ResonateRouter>) -> Arc<Self> {
        let keys = KeySpace::new(&cfg.prefix, cfg.timer_bucket_ms);
        let url = cfg.url.clone().unwrap_or_else(|| format!("http://{}", cfg.bind.replace("0.0.0.0", "127.0.0.1")));
        let id = cfg.node_id.clone().unwrap_or_else(|| format!("{:016x}", crate::keys::fnv1a(&format!("{}/{}", url, util::system_time_ms()))));
        let nodes = Arc::new(Nodes::new(Arc::clone(&store), keys.clone(), id, url.clone(), Duration::from_millis(cfg.heartbeat_ms), cfg.node_ttl_ms));
        let wheel = Arc::new(TimerWheel::new());
        let cache: Arc<dyn crate::cache::Cache> = Arc::new(crate::cache::MemoryCache::new(cfg.cache_entries, cfg.cache_bytes));
        let applier = Arc::new(Applier::new(Arc::clone(&store), keys.clone(), cfg.kernel(), Arc::clone(&nodes), Arc::clone(&wheel), router, url, cache));
        let schedules = Arc::new(Schedules::new(Arc::clone(&applier)));
        let timers = Arc::new(Timers::new(Arc::clone(&store), keys, wheel, Arc::clone(&nodes), Arc::clone(&applier), schedules));
        let (shutdown, _) = tokio::sync::watch::channel(false);
        let client = reqwest::Client::builder().connect_timeout(Duration::from_secs(2)).timeout(Duration::from_secs(30)).build().expect("an HTTP client");
        Arc::new(Self { cfg, store, nodes, applier, timers, client, shutdown, tasks: tokio::sync::Mutex::new(Vec::new()) })
    }

    pub fn config(&self) -> &Config {
        &self.cfg
    }

    pub fn nodes(&self) -> &Arc<Nodes> {
        &self.nodes
    }

    pub fn timers(&self) -> &Arc<Timers> {
        &self.timers
    }

    pub fn applier(&self) -> &Arc<Applier> {
        &self.applier
    }

    /// The clock a request sees.
    fn now(&self, req: &RequestEnvelope) -> u64 {
        let debug_time = if self.cfg.debug { req.head.debug_time } else { None };
        util::resolve_time(debug_time).max(0) as u64
    }

    /// Run `req` here, or at the owner of `origin`. Returns the answer and
    /// the id of the node that produced it.
    pub async fn process_from(&self, req: &RequestEnvelope, forwarded: bool) -> Result<(ResponseEnvelope, String), Unavailable> {
        let now = self.now(req);
        let me = self.nodes.id().to_string();
        let origin = match origin_of_request(req) {
            Ok(Some(o)) => o,
            Ok(None) => return Ok((self.dispatch(req, None, now).await?, me)),
            Err(e) => return Ok((ResponseEnvelope::error(req.kind.clone(), req.head.corr_id.clone(), 400, &e), me)),
        };
        if !forwarded && self.cfg.forward && !self.nodes.owns(&origin) {
            if let Some(owner) = self.nodes.owner(&origin) {
                match self.forward(&owner.url, req).await {
                    Ok(resp) => return Ok((resp, owner.id)),
                    Err(e) => tracing::warn!(owner = %owner.id, error = %e, "forwarding failed; serving here"),
                }
            }
        }
        Ok((self.dispatch(req, Some(origin), now).await?, me))
    }

    async fn forward(&self, url: &str, req: &RequestEnvelope) -> Result<ResponseEnvelope, Unavailable> {
        let body = json!({
            "kind": req.kind,
            "head": { "corrId": req.head.corr_id, "version": req.head.version, "auth": req.head.auth, "resonate:debug_time": req.head.debug_time },
            "data": req.data,
        });
        let resp = self.client.post(url).header(FORWARDED, self.nodes.id()).json(&body).send().await.map_err(|e| Unavailable::new(e.to_string()))?;
        if resp.status().as_u16() == 503 {
            return Err(Unavailable::new("owner unavailable"));
        }
        #[derive(serde::Deserialize)]
        struct Wire {
            kind: String,
            head: Head,
            data: serde_json::Value,
        }
        #[derive(serde::Deserialize)]
        struct Head {
            #[serde(rename = "corrId")]
            corr_id: String,
            status: i32,
        }
        let w: Wire = resp.json().await.map_err(|e| Unavailable::new(e.to_string()))?;
        Ok(ResponseEnvelope::new(w.kind, w.head.corr_id, w.head.status, w.data))
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
            ($schedule:expr, $step:expr) => {
                self.applier.apply(doc, $schedule, now, $step).await?
            };
        }
        match kind.as_str() {
            "promise.get" => {
                let d = parsed!(w::PromiseGetData);
                let r = run!(None, |s: &mut k::State| s.promise_get(&k::PromiseGetReq { id: d.id.clone() }, now, &cfg));
                Ok(wire::promise_res(&kind, &corr, &r))
            }
            "promise.create" => {
                let d = parsed!(w::PromiseCreateData);
                let q = match wire::create_in(&d) {
                    Ok(q) => q,
                    Err(m) => return err(400, &m),
                };
                let r = run!(None, |s: &mut k::State| s.promise_create(&q, now, &cfg));
                Ok(wire::promise_res(&kind, &corr, &r))
            }
            "promise.settle" => {
                let d = parsed!(w::PromiseSettleData);
                let q = wire::settle_in_req(&d);
                let r = run!(None, |s: &mut k::State| s.promise_settle(&q, now, &cfg));
                Ok(wire::promise_res(&kind, &corr, &r))
            }
            "promise.register_callback" => {
                let d = parsed!(w::PromiseRegisterCallbackData);
                let q = k::PromiseRegisterCallbackReq { awaited: d.awaited, awaiter: d.awaiter };
                let r = run!(None, |s: &mut k::State| s.promise_register_callback(&q, now, &cfg));
                Ok(wire::promise_res(&kind, &corr, &r))
            }
            "promise.register_listener" => {
                let d = parsed!(w::PromiseRegisterListenerData);
                if !resonate_core::is_valid_address(&d.address) {
                    return err(400, "Address must be a URI with a scheme");
                }
                let q = k::PromiseRegisterListenerReq { awaited: d.awaited, address: d.address };
                let r = run!(None, |s: &mut k::State| s.promise_register_listener(&q, now, &cfg));
                Ok(wire::promise_res(&kind, &corr, &r))
            }
            "task.get" => {
                let d = parsed!(w::TaskGetData);
                let r = run!(None, |s: &mut k::State| s.task_get(&k::TaskGetReq { id: d.id.clone() }, now, &cfg));
                match &r.task {
                    Some(t) => Ok(wire::status_res(&kind, &corr, r.status, json!({ "task": wire::task_out(t) }))),
                    None => Ok(wire::status_res(&kind, &corr, r.status, json!({}))),
                }
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
                let q = k::TaskCreateReq { pid: d.pid, ttl, action };
                let r = run!(None, |s: &mut k::State| s.task_create(&q, now, &cfg));
                Ok(wire::claim_res(&kind, &corr, &r))
            }
            "task.acquire" => {
                let d = parsed!(w::TaskAcquireData);
                let (version, ttl) = match (wire::nat(d.version, "version"), wire::nat(d.ttl, "ttl")) {
                    (Ok(v), Ok(t)) => (v, t),
                    (Err(m), _) | (_, Err(m)) => return err(400, &m),
                };
                let q = k::TaskAcquireReq { id: d.id, version, pid: d.pid, ttl };
                let r = run!(None, |s: &mut k::State| s.task_acquire(&q, now, &cfg));
                Ok(wire::claim_res(&kind, &corr, &r))
            }
            "task.release" => {
                let d = parsed!(w::TaskReleaseData);
                let version = match wire::nat(d.version, "version") {
                    Ok(v) => v,
                    Err(m) => return err(400, &m),
                };
                let q = k::TaskReleaseReq { id: d.id, version };
                let r = run!(None, |s: &mut k::State| s.task_release(&q, now, &cfg));
                Ok(wire::status_res(&kind, &corr, r.status, json!({})))
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
                let r = run!(None, |s: &mut k::State| s.task_fulfill(&q, now, &cfg));
                Ok(wire::promise_res(&kind, &corr, &r))
            }
            "task.suspend" => {
                let d = parsed!(w::TaskSuspendData);
                let version = match wire::nat(d.version, "version") {
                    Ok(v) => v,
                    Err(m) => return err(400, &m),
                };
                let actions = d.actions.into_iter().map(|a| k::PromiseRegisterCallbackReq { awaited: a.data.awaited, awaiter: a.data.awaiter }).collect();
                let q = k::TaskSuspendReq { id: d.id, version, actions };
                let r = run!(None, |s: &mut k::State| s.task_suspend(&q, now, &cfg));
                Ok(wire::status_res(&kind, &corr, r.status, json!({ "preload": [] })))
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
                let action_kind = d.action.kind.clone();
                let q = k::TaskFenceReq { id: d.id, version, action };
                let r = run!(None, |s: &mut k::State| s.task_fence(&q, now, &cfg));
                match &r.action {
                    Some(k::TaskFenceInnerRes::Create(p)) | Some(k::TaskFenceInnerRes::Settle(p)) => {
                        let inner = wire::promise_res(&action_kind, &corr, p);
                        Ok(wire::status_res(&kind, &corr, r.status, json!({ "action": inner, "preload": [] })))
                    }
                    None => Ok(wire::status_res(&kind, &corr, r.status, json!({}))),
                }
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
                let q = k::TaskHeartbeatReq { pid: d.pid, tasks };
                let r = run!(None, |s: &mut k::State| s.task_heartbeat(&q, now, &cfg));
                Ok(wire::status_res(&kind, &corr, r.status, json!({})))
            }
            "task.halt" => {
                let d = parsed!(w::TaskHaltData);
                let r = run!(None, |s: &mut k::State| s.task_halt(&k::TaskHaltReq { id: d.id.clone() }, now, &cfg));
                Ok(wire::status_res(&kind, &corr, r.status, json!({})))
            }
            "task.continue" => {
                let d = parsed!(w::TaskContinueData);
                let r = run!(None, |s: &mut k::State| s.task_continue(&k::TaskContinueReq { id: d.id.clone() }, now, &cfg));
                Ok(wire::status_res(&kind, &corr, r.status, json!({})))
            }
            "schedule.get" => {
                let d = parsed!(w::ScheduleGetData);
                let id = d.id.clone();
                let r = run!(Some(&id), |s: &mut k::State| s.schedule_get(&k::ScheduleGetReq { id: d.id.clone() }, now, &cfg));
                Ok(schedule_res(&kind, &corr, &r))
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
                let r = run!(Some(&id), |s: &mut k::State| s.schedule_create(&q, now, &cfg));
                Ok(schedule_res(&kind, &corr, &r))
            }
            "schedule.delete" => {
                let d = parsed!(w::ScheduleDeleteData);
                let id = d.id.clone();
                let r = run!(Some(&id), |s: &mut k::State| s.schedule_delete(&k::ScheduleDeleteReq { id: d.id.clone() }, now, &cfg));
                Ok(wire::status_res(&kind, &corr, r.status, json!({})))
            }
            "promise.search" | "task.search" | "schedule.search" => err(403, "Search operations are not supported"),
            "debug.reset" | "debug.snap" | "debug.tick" => err(403, "Debug operations are not supported"),
            _ => err(400, &format!("Unknown request kind: {kind}")),
        }
    }
}

fn schedule_res(kind: &str, corr: &str, r: &k::ScheduleRes) -> ResponseEnvelope {
    match &r.schedule {
        Some(c) => wire::status_res(kind, corr, r.status, json!({ "schedule": wire::schedule_out(c) })),
        None => wire::status_res(kind, corr, r.status, json!({})),
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
        let now = util::system_time_ms() as u64;
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

    async fn ready(&self) -> bool {
        self.store.ready().await
    }

    async fn process(&self, req: &RequestEnvelope) -> Result<ResponseEnvelope, Unavailable> {
        self.process_from(req, false).await.map(|(resp, _)| resp)
    }
}
