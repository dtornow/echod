//! echod-diff: echod against the Resonate reference server, both over
//! HTTP, on one seeded request stream.
//!
//! Two processes are started, the reference (`resonate dev --debug`, SQLite
//! in memory) and echod (`--debug`, an in-memory store), and one sink the
//! workers' messages are pushed to. Every step builds one request, sends
//! it to each in turn, and compares what came back: the response, the
//! messages pushed while it was answered, and the `debug.snap` of the
//! whole state afterwards. Time is `head.debug_time` and moves only
//! through `debug.tick`, so both run at the same instants; the sweep each
//! runs on a tick is where the deadlines are compared.
//!
//! The stream is the reference's own differential's (`gen.rs`). A run
//! stops at its coverage plateau or at the step cap, and reports every
//! divergence it met by class, with the first example of each. A
//! snapshot divergence ends the episode, since the two states have
//! parted; a response or message divergence is recorded and the run goes
//! on, since the states may still agree.
//!
//! What is compared modulo known differences: `preload` is dropped from
//! responses (echod answers an empty one), `head.serverUrl` from execute
//! messages (each stamps its own URL), and an internal promise past its
//! deadline is projected as expired in both snapshots, as the reference's
//! harness does, since echod expires it when it sweeps and the reference
//! when it is next read. One more, where the reference departs from the
//! specification: when a task is fulfilled the reference deletes it from
//! every promise's callbacks, pending ones included, which the catalogue's
//! `monotone_promise_callbacks_grow_while_pending` forbids; echod removes
//! a callback only when it is consumed, as the specification's internal
//! step does. Such callbacks are dropped from both snapshots before the
//! comparison, and `--strict-callbacks` keeps them. Everything else must
//! be identical.
//!
//! ```text
//! echod-diff --resonate <bin> --echod target/release/echod --seeds 5
//! ```

mod gen;

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use axum::routing::post;
use axum::{Json, Router};
use clap::Parser;
use echod_sim::rng::Rng;
use resonate_core::types::PROTOCOL_VERSION;
use serde_json::{json, Value};

use crate::gen::{Ids, Model, ALL_OPS};

#[derive(Parser, Debug)]
#[command(name = "echod-diff", about = "echod against the Resonate reference server, over HTTP")]
struct Cli {
    /// The reference server binary (`resonate`).
    #[arg(long)]
    resonate: PathBuf,
    /// The echod binary.
    #[arg(long, default_value = "target/release/echod")]
    echod: PathBuf,
    /// The first seed.
    #[arg(long, default_value_t = 1)]
    seed: u64,
    /// How many seeds, one after another.
    #[arg(long, default_value_t = 1)]
    seeds: u64,
    /// Steps per seed, at most.
    #[arg(long, default_value_t = 200_000)]
    max_steps: usize,
    /// Steps before everything is reset.
    #[arg(long, default_value_t = 200)]
    episode: usize,
    /// Batches of 200 steps with no new coarse signature before a seed stops.
    #[arg(long, default_value_t = 20)]
    plateau: usize,
    /// How long a sink must stay quiet before a step's messages are taken, ms.
    #[arg(long, default_value_t = 10)]
    quiet_ms: u64,
    /// Stop at the first divergence, with full detail.
    #[arg(long, default_value_t = false)]
    stop: bool,
    /// Print every request.
    #[arg(long, default_value_t = false)]
    trace: bool,
    /// Count a differing error reason as a divergence.
    #[arg(long, default_value_t = false)]
    strict_reasons: bool,
    /// Keep the callbacks of fulfilled tasks in the comparison.
    #[arg(long, default_value_t = false)]
    strict_callbacks: bool,
    /// Where the servers' logs go.
    #[arg(long, default_value = "target/echod-diff")]
    logs: PathBuf,
}

// ---------------------------------------------------------------------------
// The processes, the sink, the client
// ---------------------------------------------------------------------------

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

struct Server {
    name: &'static str,
    url: String,
    child: Child,
}

impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn spawn(name: &'static str, mut cmd: Command, url: String, logs: &PathBuf) -> Server {
    std::fs::create_dir_all(logs).expect("a log directory");
    let out = std::fs::File::create(logs.join(format!("{name}.log"))).expect("a log file");
    let err = out.try_clone().expect("a log file");
    // The servers push to the sink on localhost: no proxy may stand between.
    for v in ["HTTP_PROXY", "HTTPS_PROXY", "http_proxy", "https_proxy", "ALL_PROXY", "all_proxy"] {
        cmd.env_remove(v);
    }
    let child = cmd.stdout(Stdio::from(out)).stderr(Stdio::from(err)).stdin(Stdio::null()).spawn().unwrap_or_else(|e| panic!("cannot start {name}: {e}"));
    Server { name, url, child }
}

/// The messages pushed to the harness's worker, in the order they came.
#[derive(Default)]
struct Sink {
    got: Mutex<Vec<Value>>,
}

impl Sink {
    fn count(&self) -> usize {
        self.got.lock().unwrap().len()
    }
    fn take(&self) -> Vec<Value> {
        self.got.lock().unwrap().drain(..).collect()
    }
}

async fn start_sink(sink: Arc<Sink>) -> String {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let url = format!("http://127.0.0.1:{}/", listener.local_addr().unwrap().port());
    let app = Router::new().route(
        "/",
        post(move |Json(v): Json<Value>| {
            let sink = Arc::clone(&sink);
            async move {
                sink.got.lock().unwrap().push(v);
                axum::http::StatusCode::OK
            }
        }),
    );
    tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
    url
}

struct Client {
    http: reqwest::Client,
}

impl Client {
    fn new() -> Self {
        Self { http: reqwest::Client::builder().no_proxy().timeout(Duration::from_secs(30)).build().expect("an HTTP client") }
    }

    async fn send(&self, s: &Server, kind: &str, data: &Value, now: i64, corr: &str) -> (u16, Value) {
        let body = json!({ "kind": kind, "head": { "corrId": corr, "version": PROTOCOL_VERSION, "resonate:debug_time": now }, "data": data });
        let resp = self.http.post(&s.url).json(&body).send().await.unwrap_or_else(|e| panic!("{}: no answer for {kind}: {e}", s.name));
        let status = resp.status().as_u16();
        let v: Value = resp.json().await.unwrap_or_else(|e| panic!("{}: not an envelope for {kind}: {e}", s.name));
        let head_status = v["head"]["status"].as_u64().map(|s| s as u16).unwrap_or(status);
        (head_status, v["data"].clone())
    }

    async fn wait_ready(&self, s: &Server) {
        let start = Instant::now();
        loop {
            let body = json!({ "kind": "promise.get", "head": { "corrId": "ready", "version": PROTOCOL_VERSION, "resonate:debug_time": 1 }, "data": { "id": "ready:probe" } });
            if let Ok(r) = self.http.post(&s.url).json(&body).send().await {
                if r.status().as_u16() < 500 {
                    return;
                }
            }
            assert!(start.elapsed() < Duration::from_secs(60), "{} did not come up at {}", s.name, s.url);
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    }
}

// ---------------------------------------------------------------------------
// Comparison
// ---------------------------------------------------------------------------

/// Response data as compared: `preload` dropped wherever it is, lists of
/// records sorted by id.
fn normalize_resp(v: &mut Value) {
    match v {
        Value::Object(o) => {
            o.remove("preload");
            for (k, x) in o.iter_mut() {
                if matches!(k.as_str(), "promises" | "tasks" | "schedules") {
                    if let Some(a) = x.as_array_mut() {
                        sort_by_id(a);
                    }
                }
                normalize_resp(x);
            }
        }
        Value::Array(a) => a.iter_mut().for_each(normalize_resp),
        _ => {}
    }
}

fn sort_by_id(arr: &mut [Value]) {
    arr.sort_by_key(|v| v.get("id").and_then(|x| x.as_str()).map(str::to_string).unwrap_or_else(|| v.to_string()));
}

/// Messages as compared: each server's own URL dropped, then sorted.
fn normalize_msgs(mut msgs: Vec<Value>) -> Vec<Value> {
    for m in &mut msgs {
        if let Some(h) = m.get_mut("head").and_then(|h| h.as_object_mut()) {
            h.remove("serverUrl");
        }
    }
    msgs.sort_by_key(|m| {
        let kind = m["kind"].as_str().unwrap_or("");
        match kind {
            "execute" => format!("0_execute_{}_{}", m["data"]["task"]["id"].as_str().unwrap_or(""), m["data"]["task"]["version"]),
            "unblock" => format!("1_unblock_{}_{}", m["data"]["promise"]["id"].as_str().unwrap_or(""), m["data"]["promise"]["state"].as_str().unwrap_or("")),
            _ => format!("2_{kind}_{m}"),
        }
    });
    msgs
}

/// A snapshot as compared: messages dropped, every list sorted, and the
/// internal promises past their deadline projected as expired.
fn normalize_snap(mut snap: Value, now: i64, strict_callbacks: bool) -> Value {
    if !strict_callbacks {
        let fulfilled: HashSet<String> = snap["tasks"].as_array().map(|ts| ts.iter().filter(|t| t["state"].as_str() == Some("fulfilled")).filter_map(|t| t["id"].as_str().map(str::to_string)).collect()).unwrap_or_default();
        if let Some(cbs) = snap.get_mut("callbacks").and_then(|v| v.as_array_mut()) {
            cbs.retain(|c| !c["awaiter"].as_str().is_some_and(|a| fulfilled.contains(a)));
        }
    }
    if let Some(o) = snap.as_object_mut() {
        o.remove("messages");
        for (_, v) in o.iter_mut() {
            if let Some(a) = v.as_array_mut() {
                a.sort_by_key(|x| x.to_string());
            }
        }
    }
    project(&mut snap, now);
    if let Some(o) = snap.as_object_mut() {
        for (_, v) in o.iter_mut() {
            if let Some(a) = v.as_array_mut() {
                a.sort_by_key(|x| x.to_string());
            }
        }
    }
    snap
}

/// The specification's `Object.project`, narrowed to internal promises:
/// the one kind whose expiry a backend may write down whenever it likes,
/// since nothing arms it, nothing awaits it and nothing runs it. See the
/// reference's `diff/port.rs`.
fn project(snap: &mut Value, now: i64) {
    let Some(obj) = snap.as_object_mut() else { return };
    let mut expired: HashSet<String> = HashSet::new();
    if let Some(promises) = obj.get_mut("promises").and_then(|v| v.as_array_mut()) {
        for p in promises.iter_mut() {
            if internal(p) && expire(p, now) {
                expired.insert(p["id"].as_str().unwrap_or("").to_string());
            }
        }
    }
    if expired.is_empty() {
        return;
    }
    for (key, field) in [("tasks", "id"), ("promiseTimeouts", "id"), ("callbacks", "awaiter"), ("listeners", "id")] {
        if let Some(rows) = obj.get(key).and_then(|v| v.as_array()) {
            for r in rows {
                if let Some(id) = r[field].as_str() {
                    assert!(!expired.contains(id), "internal promise {id} is past its deadline, yet `{key}` holds a row for it");
                }
            }
        }
    }
}

fn internal(p: &Value) -> bool {
    let tags = &p["tags"];
    tags["resonate:target"].is_null() && tags["resonate:external"].as_str() != Some("true") && tags["resonate:scope"].as_str() != Some("global") && tags["resonate:timer"].as_str() != Some("true")
}

fn expire(p: &mut Value, now: i64) -> bool {
    let pending = p["state"].as_str() == Some("pending");
    let due = p["timeoutAt"].as_i64().is_some_and(|t| t <= now);
    if !(pending && due) {
        return false;
    }
    let timer = p["tags"]["resonate:timer"].as_str() == Some("true");
    let timeout_at = p["timeoutAt"].clone();
    p["state"] = json!(if timer { "resolved" } else { "rejected_timedout" });
    p["settledAt"] = timeout_at;
    true
}

/// The paths at which two JSON values differ, array indices erased, so
/// divergences of one shape fall into one class.
fn diff_paths(a: &Value, b: &Value, path: &str, out: &mut Vec<String>) {
    match (a, b) {
        (Value::Object(x), Value::Object(y)) => {
            let keys: HashSet<&String> = x.keys().chain(y.keys()).collect();
            let mut keys: Vec<&String> = keys.into_iter().collect();
            keys.sort();
            for k in keys {
                match (x.get(k), y.get(k)) {
                    (Some(p), Some(q)) => diff_paths(p, q, &format!("{path}/{k}"), out),
                    _ => out.push(format!("{path}/{k}")),
                }
            }
        }
        (Value::Array(x), Value::Array(y)) => {
            if x.len() != y.len() {
                out.push(format!("{path}[len]"));
            }
            for (p, q) in x.iter().zip(y.iter()) {
                diff_paths(p, q, &format!("{path}[]"), out);
            }
        }
        _ => {
            if a != b {
                out.push(path.to_string());
            }
        }
    }
}

fn short(v: &Value, max: usize) -> String {
    let s = v.to_string();
    if s.len() > max {
        format!("{}…", &s[..max])
    } else {
        s
    }
}

/// The coarse class the plateau counts on: which collections are present.
fn plateau_class(snap: &Value) -> u8 {
    let mut c = 0u8;
    for (i, key) in ["promises", "tasks", "callbacks", "listeners", "promiseTimeouts", "taskTimeouts"].iter().enumerate() {
        if snap.get(key).and_then(|v| v.as_array()).is_some_and(|a| !a.is_empty()) {
            c |= 1 << i;
        }
    }
    c
}

/// The rich class the report counts: which promise and task states are
/// present, and which collections.
fn state_class(snap: &Value) -> u32 {
    let mut c = 0u32;
    let present = |key: &str, states: &[&str]| -> u32 {
        let mut bits = 0u32;
        if let Some(rows) = snap.get(key).and_then(|v| v.as_array()) {
            for r in rows {
                if let Some(i) = r["state"].as_str().and_then(|s| states.iter().position(|x| *x == s)) {
                    bits |= 1 << i;
                }
            }
        }
        bits
    };
    c |= present("promises", &["pending", "resolved", "rejected", "rejected_canceled", "rejected_timedout"]);
    c |= present("tasks", &["pending", "acquired", "suspended", "halted", "fulfilled"]) << 5;
    for (i, key) in ["callbacks", "listeners", "promiseTimeouts", "taskTimeouts"].iter().enumerate() {
        if snap.get(key).and_then(|v| v.as_array()).is_some_and(|a| !a.is_empty()) {
            c |= 1 << (10 + i);
        }
    }
    c
}

// ---------------------------------------------------------------------------
// The run
// ---------------------------------------------------------------------------

struct Divergence {
    class: String,
    first: String,
    count: usize,
    steps: Vec<(u64, usize)>,
}

struct Run<'a> {
    cli: &'a Cli,
    client: Client,
    reference: Server,
    echod: Server,
    sink: Arc<Sink>,
    worker: String,
    divergences: BTreeMap<String, Divergence>,
    /// Error reasons: the reference's text for a status against echod's,
    /// by kind and status. Reported apart: the protocol fixes the status,
    /// not the words.
    reasons: BTreeMap<(String, u16, String), (String, usize)>,
    corr: u64,
}

const T0: i64 = 1_000_000_000;
const BATCH: usize = 200;

/// Operations whose 2xx may push a message, so the sink is given time.
fn may_emit(kind: &str) -> bool {
    !matches!(kind, "promise.get" | "task.get" | "schedule.get" | "task.heartbeat" | "debug.snap" | "debug.reset")
}

impl<'a> Run<'a> {
    fn corr(&mut self) -> String {
        self.corr += 1;
        format!("d{}", self.corr)
    }

    /// Messages pushed since the last take, once the sink has been quiet
    /// for a moment.
    async fn drain(&self, wait: bool) -> Vec<Value> {
        if wait {
            let mut last = self.sink.count();
            let mut quiet = 0;
            // at least two quiet intervals, so a push that is on its way lands
            while quiet < 2 {
                tokio::time::sleep(Duration::from_millis(self.cli.quiet_ms)).await;
                let n = self.sink.count();
                if n == last {
                    quiet += 1;
                } else {
                    last = n;
                    quiet = 0;
                }
            }
        }
        self.sink.take()
    }

    /// One request to both, each answered and its messages taken before
    /// the next is asked.
    async fn step(&mut self, kind: &str, data: &Value, now: i64) -> ((u16, Value, Vec<Value>), (u16, Value, Vec<Value>)) {
        let corr = self.corr();
        let (sa, mut da) = self.client.send(&self.reference, kind, data, now, &corr).await;
        let ma = self.drain(sa < 300 && may_emit(kind)).await;
        let (sb, mut db) = self.client.send(&self.echod, kind, data, now, &corr).await;
        let mb = self.drain(sb < 300 && may_emit(kind)).await;
        normalize_resp(&mut da);
        normalize_resp(&mut db);
        ((sa, da, normalize_msgs(ma)), (sb, db, normalize_msgs(mb)))
    }

    async fn snaps(&mut self, now: i64) -> (Value, Value) {
        let corr = self.corr();
        let (sa, a) = self.client.send(&self.reference, "debug.snap", &json!({}), now, &corr).await;
        let (sb, b) = self.client.send(&self.echod, "debug.snap", &json!({}), now, &corr).await;
        assert_eq!(sa, 200, "reference debug.snap: {a}");
        assert_eq!(sb, 200, "echod debug.snap: {b}");
        (a, b)
    }

    async fn reset(&mut self) {
        let corr = self.corr();
        let (sa, _) = self.client.send(&self.reference, "debug.reset", &json!({}), T0, &corr).await;
        let (sb, b) = self.client.send(&self.echod, "debug.reset", &json!({}), T0, &corr).await;
        assert_eq!(sa, 200, "reference debug.reset");
        assert_eq!(sb, 200, "echod debug.reset: {b}");
        self.drain(true).await;
    }

    fn record(&mut self, seed: u64, step: usize, kind: &str, what: &str, paths: &[String], detail: String) -> bool {
        let class = format!("{kind} {what} @ {}", if paths.is_empty() { "?".to_string() } else { paths.join(",") });
        let fresh = !self.divergences.contains_key(&class);
        let d = self.divergences.entry(class.clone()).or_insert_with(|| Divergence { class: class.clone(), first: detail, count: 0, steps: Vec::new() });
        d.count += 1;
        if d.steps.len() < 5 {
            d.steps.push((seed, step));
        }
        if fresh {
            eprintln!("[diverge] seed={seed} step={step} {class}");
        }
        fresh
    }

    /// One seed: episodes until the plateau or the cap.
    async fn seed(&mut self, seed: u64) -> (usize, usize, usize, Vec<&'static str>) {
        let mut rng = Rng::new(seed);
        let mut model = Model::default();
        let mut now = T0;
        let mut covered: HashMap<String, usize> = HashMap::new();
        let mut total = 0usize;
        let mut rich: HashSet<(String, u16, u32)> = HashSet::new();
        let mut coarse: HashSet<(String, u16, u8)> = HashSet::new();
        let mut plateau = 0usize;
        let mut in_episode = self.cli.episode; // the first step resets
        let mut episodes = 0usize;
        let worker = self.worker.clone();
        let ids = Ids { worker: &worker };
        let started = Instant::now();

        'outer: loop {
            let before = coarse.len();
            for _ in 0..BATCH {
                if total >= self.cli.max_steps {
                    break 'outer;
                }
                if in_episode >= self.cli.episode {
                    self.reset().await;
                    model.reset();
                    now = T0;
                    in_episode = 0;
                    episodes += 1;
                }
                in_episode += 1;
                let op = gen::pick_op(&mut rng, &model, &covered);
                let (kind, data, now_after) = gen::build(op, &mut rng, &model, now, &ids);
                let pre_class = {
                    let (a, _) = self.snaps(now).await;
                    (plateau_class(&a), state_class(&a))
                };
                now = now_after;
                total += 1;
                if self.cli.trace {
                    eprintln!("[step] seed={seed} step={total} now={now} {kind} {data}");
                }

                let ((sa, da, ma), (sb, db, mb)) = self.step(kind, &data, now).await;
                if sa < 300 {
                    covered.entry(kind.to_string()).or_insert(total);
                    model.schedule_answered(kind, if kind == "schedule.delete" { &data } else { &da });
                }
                rich.insert((kind.to_string(), sa, pre_class.1));
                coarse.insert((kind.to_string(), sa, pre_class.0));

                let mut stop = false;
                let reason_only = sa == sb && sa >= 400 && da.is_string() && db.is_string() && da != db;
                if reason_only {
                    let e = self.reasons.entry((kind.to_string(), sa, da.as_str().unwrap_or("").to_string())).or_insert_with(|| (db.as_str().unwrap_or("").to_string(), 0));
                    e.1 += 1;
                    if self.cli.strict_reasons {
                        let detail = format!("request {kind} now={now} {data}\n  reference: {sa} {da}\n  echod:     {sb} {db}");
                        stop |= self.record(seed, total, kind, "reason", &[], detail) && self.cli.stop;
                    }
                } else if sa != sb || da != db {
                    let mut paths = Vec::new();
                    if sa != sb {
                        paths.push(format!("status {sa}/{sb}"));
                    }
                    diff_paths(&da, &db, "", &mut paths);
                    let detail = format!("request {kind} now={now} {data}\n  reference: {sa} {}\n  echod:     {sb} {}", short(&da, 700), short(&db, 700));
                    stop |= self.record(seed, total, kind, "response", &paths, detail) && self.cli.stop;
                }
                if ma != mb {
                    let mut paths = Vec::new();
                    diff_paths(&Value::Array(ma.clone()), &Value::Array(mb.clone()), "", &mut paths);
                    let detail = format!("request {kind} now={now} {data}\n  reference pushed: {}\n  echod pushed:     {}", short(&Value::Array(ma), 900), short(&Value::Array(mb), 900));
                    stop |= self.record(seed, total, kind, "messages", &paths, detail) && self.cli.stop;
                }
                let (a, b) = self.snaps(now).await;
                let strict = self.cli.strict_callbacks;
                let (a, b) = (normalize_snap(a, now, strict), normalize_snap(b, now, strict));
                if a != b {
                    let mut paths = Vec::new();
                    diff_paths(&a, &b, "", &mut paths);
                    let detail = format!("request {kind} now={now} {data}\n  reference: {}\n  echod:     {}", short(&a, 1500), short(&b, 1500));
                    stop |= self.record(seed, total, kind, "snapshot", &paths, detail) && self.cli.stop;
                    // the states have parted: a new episode
                    in_episode = self.cli.episode;
                } else {
                    model.read(&a);
                }
                if stop {
                    break 'outer;
                }
            }
            let new = coarse.len().saturating_sub(before);
            let all_covered = covered.len() == ALL_OPS.len();
            if all_covered {
                plateau = if new == 0 { plateau + 1 } else { 0 };
            }
            eprintln!(
                "[seed {seed}] {total} steps, {episodes} episodes, {} coarse / {} rich signatures, {} ops covered, plateau {plateau}/{}, {} divergence classes, {:.0}s",
                coarse.len(),
                rich.len(),
                covered.len(),
                self.cli.plateau,
                self.divergences.len(),
                started.elapsed().as_secs_f64()
            );
            if all_covered && plateau >= self.cli.plateau {
                break 'outer;
            }
        }
        let missing: Vec<&'static str> = ALL_OPS.iter().copied().filter(|op| !covered.contains_key(*op)).collect();
        (total, coarse.len(), rich.len(), missing)
    }
}

#[tokio::main]
async fn main() {
    let cli = Cli::parse();
    let sink = Arc::new(Sink::default());
    let worker = start_sink(Arc::clone(&sink)).await;

    let p1 = free_port();
    let p2 = free_port();
    let server_url = format!("http://localhost:{p1}");
    let mut cmd = Command::new(&cli.resonate);
    cmd.args(["dev", "--debug", "--level", "warn", "--server-bind", "127.0.0.1", "--server-port", &p1.to_string(), "--server-url", &server_url, "--tasks-retry-timeout", "30000", "--console-enabled", "false", "--observability-metrics-enabled", "false", "--transports-http-poll-enabled", "false"]);
    let reference = spawn("resonate", cmd, format!("http://127.0.0.1:{p1}/"), &cli.logs);
    let mut cmd = Command::new(&cli.echod);
    cmd.args(["--debug", "--bind", &format!("127.0.0.1:{p2}"), "--url", &server_url, "--node-id", "diff", "--retry-timeout", "30000", "--compact", "0"]);
    cmd.env("RUST_LOG", "warn");
    let echod = spawn("echod", cmd, format!("http://127.0.0.1:{p2}/"), &cli.logs);

    let client = Client::new();
    client.wait_ready(&reference).await;
    client.wait_ready(&echod).await;
    eprintln!("[diff] reference at {}, echod at {}, worker at {}", reference.url, echod.url, worker);

    let mut run = Run { cli: &cli, client, reference, echod, sink, worker, divergences: BTreeMap::new(), reasons: BTreeMap::new(), corr: 0 };
    let mut total = 0usize;
    let mut missing_any: Vec<(u64, Vec<&'static str>)> = Vec::new();
    for seed in cli.seed..cli.seed + cli.seeds {
        let (steps, coarse, rich, missing) = run.seed(seed).await;
        total += steps;
        eprintln!("[seed {seed}] done: {steps} steps, {coarse} coarse / {rich} rich signatures{}", if missing.is_empty() { String::new() } else { format!(", never 2xx: {missing:?}") });
        if !missing.is_empty() {
            missing_any.push((seed, missing));
        }
        if cli.stop && !run.divergences.is_empty() {
            break;
        }
    }

    println!("\n{} steps over {} seed(s); {} divergence class(es)", total, cli.seeds, run.divergences.len());
    for d in run.divergences.values() {
        println!("\n== {} ({} times; e.g. seed/step {:?})\n{}", d.class, d.count, d.steps, d.first);
    }
    for (seed, missing) in &missing_any {
        println!("\nseed {seed}: never answered 2xx: {missing:?}");
    }
    if !run.reasons.is_empty() {
        println!("\nerror reasons that differ (status agreed; the words did not):");
        println!("{:<28} {:>4}  {:<48} {:<24} {:>6}", "kind", "st", "reference", "echod", "times");
        for ((kind, status, a), (b, n)) in &run.reasons {
            println!("{kind:<28} {status:>4}  {a:<48} {b:<24} {n:>6}");
        }
    }
    let ok = run.divergences.is_empty() && missing_any.is_empty();
    if ok {
        println!("\nPARITY: every response, message and snapshot agreed");
    }
    // `exit` skips the destructors that stop the servers
    drop(run);
    if !ok {
        std::process::exit(1);
    }
}
