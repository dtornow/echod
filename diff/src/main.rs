//! echod-diff: echod against the Resonate reference server, both over
//! HTTP, on one seeded request stream.
//!
//! Two isolated processes are started, the external reference server
//! (SQLite in memory) and echod (an isolated in-memory-store prefix), plus
//! one sink for worker messages. Every step sends one request to each and
//! compares only public observations: the response and messages pushed while
//! it was answered. The planner learns records from those responses.
//!
//! The stream is the reference's own differential's (`gen.rs`). A run
//! stops at its coverage plateau or at the step cap, and reports every
//! divergence it met by class, with the first example of each. A
//! response or message divergence is recorded and the run continues.
//!
//! What is compared modulo known differences: `preload` is dropped from
//! responses (echod answers an empty one), `head.serverUrl` from execute
//! messages (each stamps its own URL). Error reasons are compared word for word unless
//! `--lax-reasons` tables them instead. One more, where the reference departs from the
//! specification: when a task is fulfilled the reference deletes it from
//! every promise's callbacks, pending ones included, which the catalogue's
//! `monotone_promise_callbacks_grow_while_pending` forbids; echod removes
//! a callback only when it is consumed, as the specification's internal
//! step does. Internal collections are not inspected by this tool.
//!
//! ```text
//! echod-diff --resonate <bin> --echod target/release/echod --seeds 5
//! ```

mod gen;
mod harness;

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};

use clap::Parser;
use echod_sim::rng::Rng;
use serde_json::Value;

use crate::gen::{Ids, Model, ALL_OPS};
use crate::harness::{free_port, spawn_echod, spawn_reference, start_sink, Client, Server, Sink};

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
    /// Report a differing error reason as a table entry, not a divergence.
    #[arg(long, default_value_t = false)]
    lax_reasons: bool,
    /// Where the servers' logs go.
    #[arg(long, default_value = "target/echod-diff")]
    logs: PathBuf,
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

const BATCH: usize = 200;

/// Operations whose 2xx may push a message, so the sink is given time.
fn may_emit(kind: &str) -> bool {
    !matches!(kind, "promise.get" | "task.get" | "schedule.get" | "task.heartbeat")
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
    async fn step(&mut self, kind: &str, data: &Value) -> ((u16, Value, Vec<Value>), (u16, Value, Vec<Value>)) {
        let corr = self.corr();
        let (sa, mut da) = self.client.send(&self.reference, kind, data, &corr).await;
        let ma = self.drain(sa < 300 && may_emit(kind)).await;
        let (sb, mut db) = self.client.send(&self.echod, kind, data, &corr).await;
        let mb = self.drain(sb < 300 && may_emit(kind)).await;
        normalize_resp(&mut da);
        normalize_resp(&mut db);
        ((sa, da, normalize_msgs(ma)), (sb, db, normalize_msgs(mb)))
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

    /// One seed: public requests until the plateau or the cap.
    async fn seed(&mut self, seed: u64) -> (usize, usize, usize, Vec<&'static str>) {
        let mut rng = Rng::new(seed);
        let mut model = Model::default();
        let mut now = resonate_core::util::system_time_ms();
        let mut covered: HashMap<String, usize> = HashMap::new();
        let mut total = 0usize;
        let mut rich: HashSet<(String, u16, String)> = HashSet::new();
        let mut coarse: HashSet<(String, u16)> = HashSet::new();
        let mut plateau = 0usize;
        let worker = self.worker.clone();
        let ids = Ids { worker: &worker };
        let started = Instant::now();

        'outer: loop {
            let before = coarse.len();
            for _ in 0..BATCH {
                if total >= self.cli.max_steps {
                    break 'outer;
                }
                now = now.max(resonate_core::util::system_time_ms());
                let op = gen::pick_op(&mut rng, &model, &covered);
                let (kind, data, now_after) = gen::build(op, &mut rng, &model, now, &ids);
                now = now_after;
                total += 1;
                if self.cli.trace {
                    eprintln!("[step] seed={seed} step={total} now={now} {kind} {data}");
                }

                let ((sa, da, ma), (sb, db, mb)) = self.step(kind, &data).await;
                if sa < 300 {
                    covered.entry(kind.to_string()).or_insert(total);
                }
                model.observe(kind, &data, sa, &da);
                let shape = da.as_object().map(|o| o.keys().cloned().collect::<Vec<_>>().join(",")).unwrap_or_else(|| da.to_string());
                rich.insert((kind.to_string(), sa, shape));
                coarse.insert((kind.to_string(), sa));

                let mut stop = false;
                let reason_only = sa == sb && sa >= 400 && da.is_string() && db.is_string() && da != db;
                if reason_only {
                    let e = self.reasons.entry((kind.to_string(), sa, da.as_str().unwrap_or("").to_string())).or_insert_with(|| (db.as_str().unwrap_or("").to_string(), 0));
                    e.1 += 1;
                    if !self.cli.lax_reasons {
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
                "[seed {seed}] {total} steps, {} coarse / {} rich signatures, {} ops covered, plateau {plateau}/{}, {} divergence classes, {:.0}s",
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
    let server_url = format!("http://localhost:{p1}");
    let reference = spawn_reference(&cli.resonate, p1, &server_url, &cli.logs);
    let echod = spawn_echod(&cli.echod, &server_url, 30_000, &cli.logs);

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
        println!("\nPARITY: every response and message agreed");
    }
    // `exit` skips the destructors that stop the servers
    drop(run);
    if !ok {
        std::process::exit(1);
    }
}
