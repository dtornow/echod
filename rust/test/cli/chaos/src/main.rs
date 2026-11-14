//! echod-chaos: the system as deployed, under faults that are real.
//!
//! The nodes are `echod` processes in containers over a bucket, each behind
//! a `chaos-agent` (`agent.rs`). Clients drive every request kind of the
//! protocol at them over HTTP, as the simulator's generator draws them,
//! while a chaos task kills nodes, stops them, freezes them, cuts them off
//! the store or the clients or the worker, isolates them, and slows their
//! network. The store is left alone: it is where the truth is kept, and the
//! faults are everything around it.
//!
//! Then the faults are lifted, the fleet is given time to settle, every id
//! is read once more, and the bucket is read directly; and what the clients
//! saw, what the worker received and what the bucket holds are checked
//! against the guarantees that hold whatever the faults:
//!
//! - A promise's state never goes back: once a client has seen it settled,
//!   no later request sees it pending, and no two clients see it settled
//!   two ways. A task's version never goes back, and fulfilled is final.
//! - What a client was told exists, exists: every id answered 200 reads 200
//!   at the end.
//! - Every deadline fires: no promise is pending past its timeout once the
//!   fleet has had time, and no expired timer key is left in the bucket.
//! - Every `unblock` the worker received names a promise settled the way the
//!   message says; every `execute` names a task that exists; a task still
//!   unclaimed at the end was offered again once the fleet healed.
//! - The bucket's documents decode, and hold what the clients were last told.
//! - Once healed, every node answers, acts, and sees the whole fleet.
//!
//! Delivery of messages is at most once by design (`push.rs`), so a lost
//! `unblock` is reported, not held against the system.
//!
//! ```shell
//! scripts/chaos.sh                       # compose up, run, report, down
//! scripts/chaos.sh --seed 7 --duration-secs 120
//! ```

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use axum::routing::post;
use axum::{Json, Router};
use clap::Parser;
use echod::store::{ObjectStoreStore, Store};
use echod_sim::rng::Rng;
mod wire;
use echod_sim::workload::{Generator, Seen};
use serde::Serialize;
use serde_json::{json, Value};
use wire::encode;

#[derive(Debug, Parser, Clone)]
#[command(
    name = "echod-chaos",
    about = "echod as deployed, under real faults",
    version
)]
struct Args {
    /// The nodes' hostnames, comma separated.
    #[arg(
        long,
        env = "CHAOS_NODES",
        value_delimiter = ',',
        default_value = "n1,n2,n3"
    )]
    nodes: Vec<String>,
    #[arg(long, default_value_t = 8001)]
    node_port: u16,
    #[arg(long, default_value_t = 7000)]
    agent_port: u16,
    /// The store's hostname, for partitions.
    #[arg(long, env = "CHAOS_STORE_HOST", default_value = "s3")]
    store_host: String,
    /// This process's hostname as the nodes reach it: the worker, and the
    /// clients.
    #[arg(long, env = "CHAOS_SELF_HOST", default_value = "chaos")]
    self_host: String,
    #[arg(long, default_value = "0.0.0.0:9100")]
    worker_bind: String,
    #[arg(long, default_value_t = 9100)]
    worker_port: u16,
    /// The bucket, read directly at the end.
    #[arg(long, env = "ECHOD_STORE", default_value = "s3://echod")]
    store: String,
    #[arg(long, env = "ECHOD_ENDPOINT")]
    endpoint: Option<String>,
    #[arg(long, env = "ECHOD_REGION")]
    region: Option<String>,
    /// The nodes' `ECHOD_PREFIX`.
    #[arg(long, env = "ECHOD_PREFIX", default_value = "")]
    prefix: String,
    /// The nodes' `ECHOD_TIMER_BUCKET`, for how long a deadline may take.
    #[arg(long, env = "ECHOD_TIMER_BUCKET", default_value_t = 2_000)]
    timer_bucket_ms: u64,
    /// The nodes' `ECHOD_NODE_TTL`: a pause longer than this loses the seat.
    #[arg(long, env = "ECHOD_NODE_TTL", default_value_t = 2_000)]
    node_ttl_ms: u64,

    #[arg(long, env = "CHAOS_SEED", default_value_t = 1)]
    seed: u64,
    /// How long the clients run, before the fleet is healed and settled.
    #[arg(long, env = "CHAOS_DURATION_SECS", default_value_t = 60)]
    duration_secs: u64,
    #[arg(long, default_value_t = 6)]
    clients: u32,
    #[arg(long, default_value_t = 6)]
    origins: u64,
    #[arg(long, default_value_t = 3)]
    promises_per_origin: u64,
    /// Promise timeouts fall within this many ms of their creation: long
    /// enough, against the clients' rate, for a task to be offered, taken
    /// and worked before its promise times out.
    #[arg(long, default_value_t = 8_000)]
    timeout_ms: u64,
    #[arg(long, default_value_t = 4_000)]
    ttl_ms: u64,
    /// A client's pause between requests, at most.
    #[arg(long, default_value_t = 60)]
    think_ms: u64,
    /// The generator draws from a few origins; every this many seconds the
    /// clients move on to fresh ones, so a run of a minute is not one
    /// promise's lifetime stretched over it. Old ids stay in play through
    /// what the clients have seen.
    #[arg(long, default_value_t = 8)]
    epoch_secs: u64,
    /// A fault every so often, give or take half.
    #[arg(long, env = "CHAOS_EVERY_MS", default_value_t = 1_500)]
    chaos_every_ms: u64,
    /// No faults: the same run on a healthy fleet.
    #[arg(long, env = "CHAOS_NONE", default_value_t = false)]
    no_chaos: bool,
    /// How long the healed fleet is given before the final reads.
    #[arg(long, default_value_t = 12)]
    settle_secs: u64,
    /// Where the report goes, as JSON, besides stderr.
    #[arg(long, env = "CHAOS_REPORT")]
    report: Option<std::path::PathBuf>,
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

/// One attempt of one request, as the client saw it.
#[derive(Clone, Debug)]
struct Obs {
    client: String,
    kind: String,
    node: String,
    sent: u64,
    got: u64,
    /// `None`: no answer, or an answer that says nothing happened for sure
    /// (503), which may have taken effect all the same.
    status: Option<u16>,
    data: Value,
}

#[derive(Clone, Debug)]
struct Msg {
    at: u64,
    kind: String,
    body: Value,
}

struct Run {
    args: Args,
    http: reqwest::Client,
    obs: Mutex<Vec<Obs>>,
    msgs: Mutex<Vec<Msg>>,
    /// Nodes that failed a request lately, and until when they are avoided.
    suspect: Mutex<HashMap<String, Instant>>,
    stop: AtomicBool,
    /// Cleared when the host turns out to have no netem (`sch_netem` not
    /// loaded): the fault is then left out, once said.
    netem: AtomicBool,
    sent: AtomicU64,
    faults: Mutex<BTreeMap<String, u64>>,
    /// Every id a request named, for the final reads.
    named: Mutex<BTreeSet<String>>,
    started: Instant,
    worker_url: String,
}

#[derive(Default, Serialize)]
struct Report {
    seed: u64,
    ok: bool,
    chaos: bool,
    duration_secs: u64,
    ids_named: usize,
    requests: u64,
    answered: u64,
    unanswered: u64,
    by_kind_200: BTreeMap<String, u64>,
    messages: BTreeMap<String, u64>,
    faults: BTreeMap<String, u64>,
    agents: BTreeMap<String, Value>,
    promises_settled: usize,
    promises_timed_out: usize,
    listeners_pending: usize,
    unblocks: usize,
    documents: usize,
    violations: Vec<String>,
}

#[tokio::main]
async fn main() {
    let args = Args::parse();
    if args.nodes.is_empty()
        || args.clients == 0
        || args.origins == 0
        || args.promises_per_origin == 0
        || args.chaos_every_ms < 2
    {
        eprintln!(
            "chaos: nodes, clients and id pools must be nonempty; --chaos-every-ms must be >= 2"
        );
        std::process::exit(2);
    }
    let http = reqwest::Client::builder()
        .connect_timeout(Duration::from_secs(1))
        .timeout(Duration::from_secs(3))
        .build()
        .expect("client");
    let worker_url = format!("http://{}:{}/", args.self_host, args.worker_port);
    let run = Arc::new(Run {
        args: args.clone(),
        http,
        obs: Mutex::new(Vec::new()),
        msgs: Mutex::new(Vec::new()),
        suspect: Mutex::new(HashMap::new()),
        stop: AtomicBool::new(false),
        netem: AtomicBool::new(true),
        sent: AtomicU64::new(0),
        faults: Mutex::new(BTreeMap::new()),
        named: Mutex::new(BTreeSet::new()),
        started: Instant::now(),
        worker_url,
    });

    run.serve_worker().await;
    eprintln!("chaos: waiting for {} nodes", args.nodes.len());
    if let Err(e) = run.wait_healthy(Duration::from_secs(90)).await {
        eprintln!("chaos: the fleet never came up: {e}");
        std::process::exit(2);
    }
    if !args.no_chaos {
        for (node, status) in run.agent_status().await {
            if status["owned_test_node"] != true {
                eprintln!("chaos: refusing faults on unowned node {node}");
                std::process::exit(2);
            }
        }
    }
    eprintln!(
        "chaos: fleet up; seed {} for {} s, chaos {}",
        args.seed,
        args.duration_secs,
        if args.no_chaos { "off" } else { "on" }
    );

    let mut rng = Rng::new(args.seed);
    let mut tasks = Vec::new();
    for i in 0..args.clients {
        tasks.push(tokio::spawn(
            Arc::clone(&run).client(format!("c{i}"), rng.fork()),
        ));
    }
    let chaos = if args.no_chaos {
        None
    } else {
        Some(tokio::spawn(Arc::clone(&run).chaos(rng.fork())))
    };
    tokio::time::sleep(Duration::from_secs(args.duration_secs)).await;
    run.stop.store(true, Ordering::Relaxed);
    for t in tasks {
        t.await.expect("client task");
    }
    if let Some(c) = chaos {
        c.await.expect("chaos task");
    }

    eprintln!("chaos: healing");
    let heal_errors = run.heal_all().await;
    let healed_at = now_ms();
    let health = run.wait_healthy(Duration::from_secs(60)).await;
    eprintln!("chaos: settling for {} s", args.settle_secs);
    tokio::time::sleep(Duration::from_secs(args.settle_secs)).await;
    let finals = run.final_reads(&mut rng).await;
    let agents = run.agent_status().await;

    let mut report = Report {
        seed: args.seed,
        chaos: !args.no_chaos,
        duration_secs: args.duration_secs,
        ..Default::default()
    };
    report.violations.extend(heal_errors);
    if let Err(e) = health {
        report
            .violations
            .push(format!("the healed fleet did not come back: {e}"));
    }
    run.check(&finals, healed_at, &mut report).await;
    report.agents = agents;
    report.faults = run.faults.lock().unwrap().clone();
    report.ok = report.violations.is_empty();
    let text = serde_json::to_string_pretty(&report).unwrap();
    println!("{text}");
    if let Some(p) = &args.report {
        std::fs::write(p, &text).expect("write chaos report");
    }
    for v in &report.violations {
        eprintln!("VIOLATION: {v}");
    }
    eprintln!("chaos: {}", if report.ok { "ok" } else { "FAILED" });
    std::process::exit(if report.ok { 0 } else { 1 });
}

impl Run {
    fn node_url(&self, node: &str) -> String {
        format!("http://{node}:{}/", self.args.node_port)
    }

    fn agent_url(&self, node: &str, op: &str) -> String {
        format!("http://{node}:{}/{op}", self.args.agent_port)
    }

    // -----------------------------------------------------------------------
    // The worker: whatever is pushed to it, it keeps
    // -----------------------------------------------------------------------

    async fn serve_worker(self: &Arc<Self>) {
        let me = Arc::clone(self);
        let app = Router::new().route(
            "/",
            post(move |Json(v): Json<Value>| {
                let me = Arc::clone(&me);
                async move {
                    let kind = v["kind"].as_str().unwrap_or("?").to_string();
                    me.msgs.lock().unwrap().push(Msg {
                        at: now_ms(),
                        kind,
                        body: v,
                    });
                    axum::http::StatusCode::OK
                }
            }),
        );
        let listener = tokio::net::TcpListener::bind(&self.args.worker_bind)
            .await
            .expect("worker port");
        tokio::spawn(async move { axum::serve(listener, app).await.expect("worker") });
    }

    // -----------------------------------------------------------------------
    // Health
    // -----------------------------------------------------------------------

    /// Every node answers `/metrics`, acts, and counts the whole fleet.
    async fn wait_healthy(&self, within: Duration) -> Result<(), String> {
        let start = Instant::now();
        let n = self.args.nodes.len() as f64;
        loop {
            let mut bad = Vec::new();
            for node in &self.args.nodes {
                match self
                    .http
                    .get(format!("{}metrics", self.node_url(node)))
                    .send()
                    .await
                {
                    Ok(r) if r.status().is_success() => {
                        let text = r.text().await.unwrap_or_default();
                        let acting = sample(&text, "echod_node_acting ");
                        let members = sample(&text, "echod_members ");
                        if acting != 1.0 || members != n {
                            bad.push(format!("{node}: acting {acting} members {members}"));
                        }
                    }
                    Ok(r) => bad.push(format!("{node}: HTTP {}", r.status())),
                    Err(e) => bad.push(format!("{node}: {e}")),
                }
            }
            if bad.is_empty() {
                return Ok(());
            }
            if start.elapsed() > within {
                return Err(bad.join("; "));
            }
            tokio::time::sleep(Duration::from_millis(500)).await;
        }
    }

    // -----------------------------------------------------------------------
    // Clients
    // -----------------------------------------------------------------------

    fn generator(&self) -> Generator {
        Generator {
            origins: self.args.origins,
            promises_per_origin: self.args.promises_per_origin,
            schedules: false,
            timeout_ms: self.args.timeout_ms,
            ttl_ms: self.args.ttl_ms,
        }
    }

    async fn client(self: Arc<Self>, name: String, mut rng: Rng) {
        let gen = self.generator();
        let mut seen = Seen::default();
        let mut offered = 0;
        while !self.stop.load(Ordering::Relaxed) {
            // What the worker was offered, every client knows, as a worker
            // acquiring the task it was handed would.
            {
                let msgs = self.msgs.lock().unwrap();
                for m in &msgs[offered.min(msgs.len())..] {
                    if m.kind == "execute" {
                        wire::note(&mut seen, &m.body["data"]);
                    }
                }
                offered = msgs.len();
            }
            let req = gen.next(&mut rng, &seen, now_ms());
            let (kind, mut data) = encode(&req, &self.worker_url);
            shift_ids(&mut data, self.args.origins, self.epoch_base());
            if let Some(data) = self.issue(&name, kind, &data, &mut rng, 8).await {
                wire::note(&mut seen, &data);
            }
            tokio::time::sleep(Duration::from_millis(rng.range(0, self.args.think_ms))).await;
        }
    }

    /// The origins this epoch's fresh ids are moved to: past the generator's
    /// own, so an id a client has seen is never moved again.
    fn epoch_base(&self) -> u64 {
        let epoch = self.started.elapsed().as_secs() / self.args.epoch_secs.max(1);
        self.args.origins * (1 + epoch)
    }

    /// A node to send to: one not lately found dead, if there is one.
    fn pick(&self, rng: &mut Rng) -> String {
        let now = Instant::now();
        let mut suspect = self.suspect.lock().unwrap();
        suspect.retain(|_, until| *until > now);
        let fine: Vec<&String> = self
            .args
            .nodes
            .iter()
            .filter(|n| !suspect.contains_key(*n))
            .collect();
        if fine.is_empty() {
            rng.pick(&self.args.nodes).clone()
        } else {
            (*rng.pick(&fine)).clone()
        }
    }

    /// One request, retried on another node when no answer comes, each
    /// attempt its own observation. The answer's data, if one came.
    async fn issue(
        &self,
        client: &str,
        kind: &str,
        data: &Value,
        rng: &mut Rng,
        attempts: u32,
    ) -> Option<Value> {
        {
            let mut named = self.named.lock().unwrap();
            ids_in(data, &mut |id| {
                named.insert(id.to_string());
            });
        }
        for attempt in 1..=attempts {
            let node = self.pick(rng);
            let n = self.sent.fetch_add(1, Ordering::Relaxed);
            let body = json!({ "kind": kind, "head": { "corrId": format!("{client}-{n}"), "version": "2026-04-01" }, "data": data });
            let sent = now_ms();
            let answer = self
                .http
                .post(self.node_url(&node))
                .json(&body)
                .send()
                .await;
            let mut obs = Obs {
                client: client.to_string(),
                kind: kind.to_string(),
                node: node.clone(),
                sent,
                got: 0,
                status: None,
                data: Value::Null,
            };
            let outcome = match answer {
                Ok(r) => {
                    let status = r.status().as_u16();
                    let v: Value = r.json().await.unwrap_or(Value::Null);
                    if status == 503 {
                        None
                    } else {
                        obs.status = Some(status);
                        obs.data = v["data"].clone();
                        Some(obs.data.clone())
                    }
                }
                Err(_) => None,
            };
            obs.got = now_ms();
            self.obs.lock().unwrap().push(obs);
            if outcome.is_some() {
                return outcome;
            }
            self.suspect
                .lock()
                .unwrap()
                .insert(node, Instant::now() + Duration::from_millis(800));
            if attempt == attempts {
                break;
            }
            let base = (50u64 << (attempt - 1).min(4)).min(800);
            tokio::time::sleep(Duration::from_millis(base + rng.range(1, 50))).await;
        }
        None
    }

    /// Every id the run named, read until answered.
    async fn final_reads(&self, rng: &mut Rng) -> BTreeMap<String, (Option<Value>, Option<Value>)> {
        let mut out = BTreeMap::new();
        let named: Vec<String> = self.named.lock().unwrap().iter().cloned().collect();
        for id in named {
            let p = self
                .issue("final", "promise.get", &json!({ "id": id }), rng, 60)
                .await;
            let t = self
                .issue("final", "task.get", &json!({ "id": id }), rng, 60)
                .await;
            if p.is_none() || t.is_none() {
                eprintln!("chaos: {id}: no answer to the final read");
            }
            out.insert(id, (p, t));
        }
        out
    }

    // -----------------------------------------------------------------------
    // Chaos
    // -----------------------------------------------------------------------

    async fn agent(&self, node: &str, op: &str, query: &[(&str, String)]) -> bool {
        let r = self
            .http
            .post(self.agent_url(node, op))
            .query(query)
            .send()
            .await;
        match r {
            Ok(r) if r.status().is_success() => true,
            Ok(r) => {
                eprintln!(
                    "chaos: {node} {op}: HTTP {} {}",
                    r.status(),
                    r.text().await.unwrap_or_default()
                );
                false
            }
            Err(e) => {
                eprintln!("chaos: {node} {op}: {e}");
                false
            }
        }
    }

    fn count(&self, fault: &str) {
        *self
            .faults
            .lock()
            .unwrap()
            .entry(fault.to_string())
            .or_default() += 1;
    }

    /// A fault every so often on a node not under one already; each is
    /// lifted after its while.
    async fn chaos(self: Arc<Self>, mut rng: Rng) {
        let busy: Arc<Mutex<BTreeSet<String>>> = Arc::new(Mutex::new(BTreeSet::new()));
        let every = self.args.chaos_every_ms;
        let mut faults = tokio::task::JoinSet::new();
        while !self.stop.load(Ordering::Relaxed) {
            tokio::time::sleep(Duration::from_millis(
                rng.range(every / 2, every + every / 2),
            ))
            .await;
            if self.stop.load(Ordering::Relaxed) {
                break;
            }
            let free: Vec<String> = self
                .args
                .nodes
                .iter()
                .filter(|n| !busy.lock().unwrap().contains(*n))
                .cloned()
                .collect();
            if free.is_empty() {
                continue;
            }
            let node = rng.pick(&free).clone();
            let me = Arc::clone(&self);
            let busy2 = Arc::clone(&busy);
            busy.lock().unwrap().insert(node.clone());
            let roll = rng.below(100);
            let mut r2 = rng.fork();
            faults.spawn(async move {
                let ttl = me.args.node_ttl_ms;
                let hold = |lo: u64, hi: u64, r: &mut Rng| Duration::from_millis(r.range(lo, hi));
                let store = me.args.store_host.clone();
                let myself = me.args.self_host.clone();
                let worker_port = me.args.worker_port.to_string();
                let node_port = me.args.node_port.to_string();
                match roll {
                    // Killed outright; back after a while, cache and wheel gone.
                    0..=19 => {
                        let after = r2.range(0, 3_000);
                        eprintln!("chaos: {node}: crash, back in {after} ms");
                        if me.agent(&node, "crash", &[("after_ms", after.to_string())]).await {
                            me.count("crash");
                        }
                        tokio::time::sleep(Duration::from_millis(after + 500)).await;
                    }
                    // Asked to stop: it withdraws its seat and leaves.
                    20..=29 => {
                        let after = r2.range(500, 3_000);
                        eprintln!("chaos: {node}: stop, back in {after} ms");
                        if me.agent(&node, "stop", &[("after_ms", after.to_string())]).await {
                            me.count("stop");
                        }
                        tokio::time::sleep(Duration::from_millis(after + 500)).await;
                    }
                    // Frozen, sometimes past its TTL: it comes back believing
                    // it still owns what it owned.
                    30..=44 => {
                        let d = hold(300, 3 * ttl, &mut r2);
                        eprintln!("chaos: {node}: pause for {d:?}");
                        if me.agent(&node, "pause", &[]).await {
                            me.count("pause");
                            tokio::time::sleep(d).await;
                            me.agent(&node, "resume", &[]).await;
                        }
                    }
                    // Cut off the store: every load and write times out.
                    45..=59 => {
                        let d = hold(1_000, 6_000, &mut r2);
                        eprintln!("chaos: {node}: partition from the store for {d:?}");
                        if me.agent(&node, "partition", &[("hosts", store.clone())]).await {
                            me.count("partition_store");
                            tokio::time::sleep(d).await;
                            me.agent(&node, "heal", &[]).await;
                        }
                    }
                    // Cut off the worker: pushes fail.
                    60..=69 => {
                        let d = hold(1_000, 5_000, &mut r2);
                        eprintln!("chaos: {node}: partition from the worker for {d:?}");
                        if me.agent(&node, "partition", &[("hosts", myself.clone()), ("port", worker_port.clone()), ("dir", "out".into())]).await {
                            me.count("partition_worker");
                            tokio::time::sleep(d).await;
                            me.agent(&node, "heal", &[]).await;
                        }
                    }
                    // Cut off the clients: it keeps its seat and fires its
                    // deadlines, unreachable.
                    70..=79 => {
                        let d = hold(1_000, 5_000, &mut r2);
                        eprintln!("chaos: {node}: partition from the clients for {d:?}");
                        if me.agent(&node, "partition", &[("hosts", myself.clone()), ("port", node_port.clone()), ("dir", "in".into())]).await {
                            me.count("partition_clients");
                            tokio::time::sleep(d).await;
                            me.agent(&node, "heal", &[]).await;
                        }
                    }
                    // Alone: no store, no clients, no worker.
                    80..=84 => {
                        let d = hold(1_000, 5_000, &mut r2);
                        eprintln!("chaos: {node}: isolated for {d:?}");
                        if me.agent(&node, "partition", &[("hosts", format!("{store},{myself}"))]).await {
                            me.count("isolate");
                            tokio::time::sleep(d).await;
                            me.agent(&node, "heal", &[]).await;
                        }
                    }
                    // Slow and lossy.
                    _ if me.netem.load(Ordering::Relaxed) => {
                        let (delay, jitter, loss) = (r2.range(50, 400), r2.range(0, 100), r2.range(0, 15));
                        let d = hold(2_000, 8_000, &mut r2);
                        eprintln!("chaos: {node}: netem delay {delay}±{jitter} ms loss {loss}% for {d:?}");
                        if me.agent(&node, "netem", &[("delay_ms", delay.to_string()), ("jitter_ms", jitter.to_string()), ("loss", loss.to_string())]).await {
                            me.count("netem");
                            tokio::time::sleep(d).await;
                            me.agent(&node, "heal", &[]).await;
                        } else if me.netem.swap(false, Ordering::Relaxed) {
                            eprintln!("chaos: no netem here (is sch_netem loaded on the host?); leaving it out");
                        }
                    }
                    _ => {}
                }
                busy2.lock().unwrap().remove(&node);
            });
        }
        while let Some(result) = faults.join_next().await {
            result.expect("fault task");
        }
    }

    async fn heal_all(&self) -> Vec<String> {
        let mut errors = Vec::new();
        for node in &self.args.nodes {
            if !self.agent(node, "heal", &[]).await {
                errors.push(format!("{node}: heal failed"));
            }
        }
        errors
    }

    async fn agent_status(&self) -> BTreeMap<String, Value> {
        let mut out = BTreeMap::new();
        for node in &self.args.nodes {
            let v = match self.http.get(self.agent_url(node, "")).send().await {
                Ok(r) => r.json().await.unwrap_or(Value::Null),
                Err(e) => json!({ "error": e.to_string() }),
            };
            out.insert(node.clone(), v);
        }
        out
    }

    // -----------------------------------------------------------------------
    // The check
    // -----------------------------------------------------------------------

    async fn check(
        &self,
        finals: &BTreeMap<String, (Option<Value>, Option<Value>)>,
        healed_at: u64,
        report: &mut Report,
    ) {
        let obs = self.obs.lock().unwrap().clone();
        let msgs = self.msgs.lock().unwrap().clone();
        let grace = 2 * self.args.timer_bucket_ms + 3_000;
        let v = &mut report.violations;

        report.ids_named = finals.len();
        report.requests = obs.len() as u64;
        report.answered = obs.iter().filter(|o| o.status.is_some()).count() as u64;
        report.unanswered = report.requests - report.answered;
        for o in obs.iter().filter(|o| o.status == Some(200)) {
            *report.by_kind_200.entry(o.kind.clone()).or_default() += 1;
        }
        for m in &msgs {
            *report.messages.entry(m.kind.clone()).or_default() += 1;
        }
        if !report.by_kind_200.contains_key("promise.create")
            && !report.by_kind_200.contains_key("task.create")
        {
            v.push("workload never successfully created a promise or task".into());
        }

        // Every promise and task a client was shown, in the order the
        // answers came.
        let mut sightings: Vec<Sighting> = Vec::new();
        for o in obs.iter().filter(|o| o.status == Some(200)) {
            for p in promises_in(&o.data) {
                sightings.push(Sighting::promise(o, &p));
            }
            for t in tasks_in(&o.data) {
                sightings.push(Sighting::task(o, &t));
            }
        }
        sightings.sort_by_key(|s| (s.got, s.sent));

        // 1. States never go back, and a settled state is one state.
        let (regressions, settled) = regressions(&sightings);
        v.extend(regressions);
        report.promises_settled = settled.len();

        // 2. What was shown exists; 3. every deadline fired.
        let known: BTreeSet<&String> = sightings
            .iter()
            .filter(|s| matches!(s.what, What::Promise(_)))
            .map(|s| &s.id)
            .collect();
        let final_at = now_ms();
        let mut final_state: HashMap<String, String> = HashMap::new();
        let mut final_task: HashMap<String, (String, u64)> = HashMap::new();
        for (id, (p, t)) in finals {
            let Some(p) = p else {
                v.push(format!("{id}: no final read"));
                continue;
            };
            match p.get("promise") {
                Some(pr) => {
                    let state = pr["state"].as_str().unwrap_or("?").to_string();
                    let timeout_at = pr["timeoutAt"].as_u64().unwrap_or(u64::MAX);
                    if state == "pending" && timeout_at.saturating_add(grace) < final_at {
                        v.push(format!(
                            "{id}: pending at {final_at}, {} ms past its timeout {timeout_at}",
                            final_at - timeout_at
                        ));
                    }
                    if state == "rejected_timedout" {
                        report.promises_timed_out += 1;
                    }
                    final_state.insert(id.clone(), state);
                }
                None => {
                    if known.contains(id) {
                        v.push(format!(
                            "{id}: shown to a client, not there at the end: {p}"
                        ));
                    }
                }
            }
            if let Some(task) = t.as_ref().and_then(|t| t.get("task")) {
                final_task.insert(
                    id.clone(),
                    (
                        task["state"].as_str().unwrap_or("?").to_string(),
                        task["version"].as_u64().unwrap_or(0),
                    ),
                );
            }
        }

        // 4. Messages name what is there.
        let mut unblocked: BTreeSet<String> = BTreeSet::new();
        let mut executed_after_heal: BTreeSet<String> = BTreeSet::new();
        for m in &msgs {
            match m.kind.as_str() {
                "unblock" => {
                    let id = m.body["data"]["promise"]["id"]
                        .as_str()
                        .unwrap_or("?")
                        .to_string();
                    let state = m.body["data"]["promise"]["state"].as_str().unwrap_or("?");
                    report.unblocks += 1;
                    unblocked.insert(id.clone());
                    match final_state.get(&id) {
                        Some(f) if f == state => {}
                        Some(f) => v.push(format!("unblock for {id} says {state}; it ended {f}")),
                        None if finals.contains_key(&id) => {
                            v.push(format!("unblock for {id}, which is not there"))
                        }
                        None => {}
                    }
                    if state == "pending" {
                        v.push(format!("unblock for {id} with it pending"));
                    }
                }
                "execute" => {
                    let id = m.body["data"]["task"]["id"]
                        .as_str()
                        .unwrap_or("?")
                        .to_string();
                    if finals.contains_key(&id) && !final_task.contains_key(&id) {
                        v.push(format!("execute for {id}, which has no task"));
                    }
                    if m.at > healed_at {
                        executed_after_heal.insert(id);
                    }
                }
                _ => {}
            }
        }
        // A task unclaimed at the end, its promise still open, is offered
        // again every retry timeout: the healed fleet must have offered it.
        for (id, (state, _)) in &final_task {
            if state == "pending"
                && final_state.get(id).is_some_and(|s| s == "pending")
                && !executed_after_heal.contains(id)
            {
                v.push(format!(
                    "task {id}: pending at the end, never offered after the fleet healed"
                ));
            }
        }
        // Listeners: delivery is at most once, so a lost unblock is counted,
        // not held against the system.
        let listened: BTreeSet<String> = obs
            .iter()
            .filter(|o| {
                o.kind == "promise.register_listener"
                    && o.status == Some(200)
                    && o.data["promise"]["state"] == "pending"
            })
            .filter_map(|o| o.data["promise"]["id"].as_str().map(str::to_string))
            .collect();
        report.listeners_pending = listened.len();
        let lost = listened
            .iter()
            .filter(|id| {
                final_state.get(*id).is_some_and(|s| s != "pending") && !unblocked.contains(*id)
            })
            .count();
        if lost > 0 {
            eprintln!("chaos: {lost} of {} listened-for promises settled with no unblock received (at-most-once delivery)", listened.len());
        }

        // 5. The bucket: every document decodes and agrees with the end.
        match self.read_bucket().await {
            Ok((docs, timers)) => {
                report.documents = docs.len();
                let read_at = now_ms();
                for (origin, rows) in &docs {
                    for p in rows {
                        if echod_logic::keys::origin_of(&p.id) != origin {
                            v.push(format!("document {origin} holds {}", p.id));
                        }
                        let state = state_name(&p.state);
                        if let Some(f) = final_state.get(&p.id) {
                            let fine = f == state || (f == "pending" && state != "pending");
                            if !fine {
                                v.push(format!(
                                    "{}: read {f} at the end, the bucket holds {state}",
                                    p.id
                                ));
                            }
                        }
                        if state == "pending" && p.timeout_at.saturating_add(grace) < read_at {
                            v.push(format!(
                                "{}: pending in the bucket {} ms past its timeout",
                                p.id,
                                read_at - p.timeout_at
                            ));
                        }
                    }
                }
                // 6. No expired key is left: every deadline was fired and collected.
                for (key, deadline) in &timers {
                    if deadline + grace < read_at {
                        v.push(format!(
                            "timer key {key} is {} ms past due and still there",
                            read_at - deadline
                        ));
                    }
                }
            }
            Err(e) => v.push(format!("the bucket could not be read: {e}")),
        }
    }

    /// Every origin's rows, and every timer key with its deadline.
    async fn read_bucket(
        &self,
    ) -> Result<
        (
            BTreeMap<String, Vec<echod_types::PromiseRecord>>,
            Vec<(String, u64)>,
        ),
        String,
    > {
        let store = ObjectStoreStore::from_url(
            &self.args.store,
            self.args.endpoint.as_deref(),
            self.args.region.as_deref(),
        )?;
        let keys = echod_logic::keys::KeySpace::new(&self.args.prefix, self.args.timer_bucket_ms);
        let mut docs = BTreeMap::new();
        for key in store
            .list(&format!("{}wf/", self.args.prefix), usize::MAX)
            .await
            .map_err(|e| format!("{e:?}"))?
        {
            let Some((bytes, _)) = store.get(&key).await.map_err(|e| format!("{e:?}"))? else {
                continue;
            };
            let loaded =
                echod_logic::doc::decode_origin(&bytes).map_err(|e| format!("{key}: {e}"))?;
            let origin = key
                .rsplit('/')
                .next()
                .and_then(echod_logic::keys::decode_key)
                .unwrap_or_default();
            let echod_logic::concrete::Doc::Origin(objects) = loaded.doc else {
                return Err(format!("{key}: not an origin document"));
            };
            docs.insert(
                origin,
                objects
                    .into_entries()
                    .into_iter()
                    .map(|(id, obj)| {
                        let p = obj.promise;
                        echod_types::PromiseRecord {
                            id,
                            state: p.state,
                            param: p.param,
                            value: p.value,
                            tags: p.tags,
                            timeout_at: p.timeout_at,
                            created_at: p.created_at,
                            settled_at: p.settled_at,
                        }
                    })
                    .collect(),
            );
        }
        let mut timers = Vec::new();
        for key in store
            .list(&keys.timer_prefix(), usize::MAX)
            .await
            .map_err(|e| format!("{e:?}"))?
        {
            if let Some(e) = keys.parse_timer_key(&key) {
                timers.push((key, e.deadline()));
            }
        }
        Ok((docs, timers))
    }
}

enum What {
    Promise(String),
    Task(String, u64),
}

struct Sighting {
    id: String,
    sent: u64,
    got: u64,
    who: String,
    what: What,
}

impl Sighting {
    fn promise(o: &Obs, p: &Value) -> Self {
        Self {
            id: p["id"].as_str().unwrap_or("?").to_string(),
            sent: o.sent,
            got: o.got,
            who: format!("{} via {} ({})", o.client, o.node, o.kind),
            what: What::Promise(p["state"].as_str().unwrap_or("?").to_string()),
        }
    }
    fn task(o: &Obs, t: &Value) -> Self {
        Self {
            id: t["id"].as_str().unwrap_or("?").to_string(),
            sent: o.sent,
            got: o.got,
            who: format!("{} via {} ({})", o.client, o.node, o.kind),
            what: What::Task(
                t["state"].as_str().unwrap_or("?").to_string(),
                t["version"].as_u64().unwrap_or(0),
            ),
        }
    }
}

/// Promise states never go back and settle one way; task versions never go
/// back and fulfilled is final. Two sightings are ordered only when one was
/// sent after the other was answered; concurrent ones may come either way.
/// Besides the violations: every promise seen settled, with when and how.
fn regressions(sightings: &[Sighting]) -> (Vec<String>, HashMap<String, (u64, String, String)>) {
    let mut v = Vec::new();
    // The first settled sighting of each promise: when it was answered, how,
    // by whom.
    let mut settled: HashMap<String, (u64, String, String)> = HashMap::new();
    let mut fulfilled: HashMap<String, (u64, String)> = HashMap::new();
    // Every task sighting so far: (answered at, version, who).
    let mut versions: HashMap<String, Vec<(u64, u64, String)>> = HashMap::new();
    for s in sightings {
        match &s.what {
            What::Promise(state) => {
                if let Some((got, prior, who)) = settled.get(&s.id) {
                    if state == "pending" && s.sent > *got {
                        v.push(format!(
                            "{}: {who} saw it {prior} by {got}, then {} saw it pending at {}",
                            s.id, s.who, s.sent
                        ));
                    } else if state != "pending" && state != prior {
                        v.push(format!(
                            "{}: settled two ways: {prior} ({who}) and {state} ({})",
                            s.id, s.who
                        ));
                    }
                }
                if state != "pending" && !settled.contains_key(&s.id) {
                    settled.insert(s.id.clone(), (s.got, state.clone(), s.who.clone()));
                }
            }
            What::Task(state, version) => {
                let seen = versions.entry(s.id.clone()).or_default();
                if let Some((got, v0, who)) = seen
                    .iter()
                    .filter(|(got, _, _)| *got < s.sent)
                    .max_by_key(|(_, v, _)| *v)
                {
                    if *version < *v0 {
                        v.push(format!("task {}: {who} saw version {v0} by {got}, then {} saw version {version} at {}", s.id, s.who, s.sent));
                    }
                }
                seen.push((s.got, *version, s.who.clone()));
                if let Some((got, who)) = fulfilled.get(&s.id) {
                    if state != "fulfilled" && s.sent > *got {
                        v.push(format!("task {}: {who} saw it fulfilled by {got}, then {} saw it {state} at {}", s.id, s.who, s.sent));
                    }
                }
                if state == "fulfilled" && !fulfilled.contains_key(&s.id) {
                    fulfilled.insert(s.id.clone(), (s.got, s.who.clone()));
                }
            }
        }
    }
    (v, settled)
}

/// Every id named in a request's data: `id`, `awaited`, `awaiter`, a
/// heartbeat's `tasks[].id`, a fenced action's `data.id`.
fn ids_in(v: &Value, f: &mut dyn FnMut(&str)) {
    match v {
        Value::Object(m) => {
            for (k, x) in m {
                match (k.as_str(), x) {
                    ("id" | "awaited" | "awaiter", Value::String(s)) => f(s),
                    _ => ids_in(x, f),
                }
            }
        }
        Value::Array(xs) => xs.iter().for_each(|x| ids_in(x, f)),
        _ => {}
    }
}

/// The generator's ids, `o<k>:<n>` with `k` below `window`, moved to
/// origin `base + k`. Ids at or past the window, which the clients saw
/// answered in an earlier epoch, are left as they are.
fn shift_ids(v: &mut Value, window: u64, base: u64) {
    match v {
        Value::String(s) => {
            if let Some((k, rest)) = s.strip_prefix('o').and_then(|r| r.split_once(':')) {
                if let Ok(k) = k.parse::<u64>() {
                    if k < window {
                        *s = format!("o{}:{rest}", base + k);
                    }
                }
            }
        }
        Value::Object(m) => m.values_mut().for_each(|x| shift_ids(x, window, base)),
        Value::Array(xs) => xs.iter_mut().for_each(|x| shift_ids(x, window, base)),
        _ => {}
    }
}

/// The promise records in an answer: `promise`, and a fence's inner answer.
fn promises_in(data: &Value) -> Vec<Value> {
    let mut out = Vec::new();
    if let Some(p) = data.get("promise").filter(|p| p.get("id").is_some()) {
        out.push(p.clone());
    }
    if data["head"]["status"] == 200 {
        out.extend(promises_in(&data["data"]));
    }
    out
}

fn tasks_in(data: &Value) -> Vec<Value> {
    let mut out = Vec::new();
    if let Some(t) = data.get("task").filter(|t| t.get("id").is_some()) {
        out.push(t.clone());
    }
    if data["head"]["status"] == 200 {
        out.extend(tasks_in(&data["data"]));
    }
    out
}

fn state_name(s: &echod_types::PromiseState) -> &'static str {
    match s {
        echod_types::PromiseState::Pending => "pending",
        echod_types::PromiseState::Resolved => "resolved",
        echod_types::PromiseState::Rejected => "rejected",
        echod_types::PromiseState::RejectedCanceled => "rejected_canceled",
        echod_types::PromiseState::RejectedTimedout => "rejected_timedout",
    }
}

/// The value of the one sample `prefix` starts, or 0 if there is none.
fn sample(text: &str, prefix: &str) -> f64 {
    text.lines()
        .find_map(|l| l.strip_prefix(prefix))
        .and_then(|rest| rest.trim().split(' ').next())
        .and_then(|v| v.parse().ok())
        .unwrap_or(0.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(id: &str, sent: u64, got: u64, state: &str) -> Sighting {
        Sighting {
            id: id.into(),
            sent,
            got,
            who: "t".into(),
            what: What::Promise(state.into()),
        }
    }

    fn t(id: &str, sent: u64, got: u64, state: &str, version: u64) -> Sighting {
        Sighting {
            id: id.into(),
            sent,
            got,
            who: "t".into(),
            what: What::Task(state.into(), version),
        }
    }

    #[test]
    fn a_settled_promise_seen_pending_afterwards_is_a_regression() {
        let fine = [
            p("a", 1, 2, "pending"),
            p("a", 3, 4, "resolved"),
            p("a", 5, 6, "resolved"),
        ];
        assert!(regressions(&fine).0.is_empty());
        let concurrent = [p("a", 3, 4, "resolved"), p("a", 2, 5, "pending")];
        assert!(
            regressions(&concurrent).0.is_empty(),
            "sent before the other was answered: either order"
        );
        let back = [p("a", 3, 4, "resolved"), p("a", 5, 6, "pending")];
        assert_eq!(regressions(&back).0.len(), 1);
        let two_ways = [p("a", 3, 4, "resolved"), p("a", 1, 9, "rejected")];
        assert_eq!(
            regressions(&two_ways).0.len(),
            1,
            "settled two ways, concurrent or not"
        );
    }

    #[test]
    fn a_task_version_never_goes_back_and_fulfilled_is_final() {
        let fine = [
            t("a", 1, 2, "pending", 0),
            t("a", 3, 4, "acquired", 1),
            t("a", 2, 5, "pending", 0),
            t("a", 6, 7, "fulfilled", 1),
        ];
        assert!(
            regressions(&fine).0.is_empty(),
            "the version 0 sighting was concurrent with the acquire"
        );
        let back = [t("a", 1, 2, "acquired", 2), t("a", 3, 4, "pending", 1)];
        assert_eq!(regressions(&back).0.len(), 1);
        // The highest version answered before this one was sent counts, not
        // the latest answered.
        let hidden = [
            t("a", 1, 10, "acquired", 5),
            t("a", 9, 12, "pending", 3),
            t("a", 13, 14, "pending", 4),
        ];
        assert_eq!(regressions(&hidden).0.len(), 1);
        let unfulfilled = [t("a", 1, 2, "fulfilled", 3), t("a", 3, 4, "acquired", 3)];
        assert_eq!(regressions(&unfulfilled).0.len(), 1);
    }

    #[test]
    fn ids_are_shifted_once_and_found_everywhere() {
        let mut v = json!({ "id": "o2:1", "awaited": "o7:3.1", "tasks": [{ "id": "o0:2" }], "action": { "data": { "id": "o5:1.1" } }, "pid": "p1" });
        shift_ids(&mut v, 6, 60);
        assert_eq!(v["id"], "o62:1");
        assert_eq!(
            v["awaited"], "o7:3.1",
            "already past the window: left alone"
        );
        assert_eq!(v["tasks"][0]["id"], "o60:2");
        assert_eq!(v["action"]["data"]["id"], "o65:1.1");
        let mut named = Vec::new();
        ids_in(&v, &mut |id| named.push(id.to_string()));
        named.sort();
        assert_eq!(named, ["o60:2", "o62:1", "o65:1.1", "o7:3.1"]);
    }

    #[test]
    fn a_fence_answers_with_its_action_inside() {
        let data = json!({ "task": { "id": "o1:1", "state": "acquired", "version": 2 }, "head": { "status": 200 }, "data": { "promise": { "id": "o1:1.1", "state": "pending" } } });
        assert_eq!(promises_in(&data).len(), 1);
        assert_eq!(tasks_in(&data).len(), 1);
        let refused = json!({ "head": { "status": 409 }, "data": { "promise": { "id": "x", "state": "pending" } } });
        assert!(
            promises_in(&refused).is_empty(),
            "a refused action's record is not a sighting"
        );
    }
}
