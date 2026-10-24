//! echod-accordant: echod driven by the Resonate model of `dtornow/accordant`,
//! over HTTP, and every trace checked against that model.
//!
//! The model (`accordant`'s `examples/resonate`) is an executable
//! specification in Verus of the Resonate protocol as the C# spec had it:
//! what every request does, what runs on its own (a deadline, a lease, a
//! resume), what the server dispatches. Its fuzz example drives the model
//! itself; this drives echod. A run resets echod, then takes the model's
//! own actions (`Explore::suggest`, steered by what the model has seen
//! least, or `Explore::arbitrary`, random) one at a time: a request is sent
//! with the run's clock as `head.debug_time` and its answer recorded; a
//! clock move is recorded and then handed to echod as `debug.tick`, so the
//! sweep runs at the instant the model's timers fire; every `execute` the
//! sink receives is recorded as a dispatch. Then the model's `finish`
//! actions: read everything, move the clock past every deadline, read
//! again. The trace is checked with certificates, and the marks of the
//! execution that explains it are the coverage.
//!
//! What is dropped before checking: `unblock` messages (the model has no
//! listener dispatch), `preload` and the records the model does not carry.
//! echod runs with a retry timeout no run reaches, since the model has no
//! redispatch of an unclaimed task. Two places where the model, a port of
//! the C# specification, and echod, which follows the Lean one, say
//! different things by design are translated or left out: `task.create`
//! on an existing id answers both records in the Lean specification and
//! the task's alone in the C# one, so the answer is read as the model
//! types it; and a fence that creates a promise in another origin (the C#
//! spec's detached create) is refused by the Lean specification and by
//! echod, so such fences are not sent. One more: the model's `task.create`
//! has no branch for a deadline already passed, which `promise.create` has
//! (born settled, the task fulfilled); echod has it for both, as the Lean
//! specification does, so a `task.create` past its deadline is not sent.
//!
//! ```text
//! echod-accordant --echod ../../target/release/echod [--runs 200] [--requests 30]
//! ```

#[path = "../../src/harness.rs"]
mod harness;

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use accordant::{marks, Action, Checker, Choices, Config, Event, Explore, Keyed, Tried, Verdict, Violation};
use clap::Parser;
use resonate::{Create, Dispatch, Fenced, PMap, PSet, PState, Promise, PromiseRec, Request, Resonate, Response, Server as Model, TState, Tags, Task, TaskRec, MARKS, TASK_CREATE_TTL};
use serde_json::{json, Value};

use crate::harness::{spawn_echod, start_sink, Client, Server, Sink};

#[derive(Parser, Debug)]
#[command(name = "echod-accordant", about = "echod driven by accordant's Resonate model, over HTTP")]
struct Cli {
    #[arg(long, default_value = "../../target/release/echod")]
    echod: PathBuf,
    /// Runs per mode (random, guided).
    #[arg(long, default_value_t = 200)]
    runs: u64,
    /// Actions per run, besides the model's finishing reads.
    #[arg(long, default_value_t = 30)]
    requests: usize,
    /// The first seed.
    #[arg(long, default_value_t = 1)]
    seed: u64,
    /// How long the sink must stay quiet before a step's messages are taken, ms.
    #[arg(long, default_value_t = 10)]
    quiet_ms: u64,
    /// Print every event of every run.
    #[arg(long, default_value_t = false)]
    trace: bool,
    #[arg(long, default_value = "../../target/echod-diff")]
    logs: PathBuf,
}

type Trace = Vec<Event<Request, Response, Dispatch>>;

const T0: u64 = 1_000_000;
const WORKER_SELF: &str = "worker-self";

// ---------------------------------------------------------------------------
// The model's vocabulary on the wire
// ---------------------------------------------------------------------------

fn tags(target: bool, external: bool, timer: bool, worker: &str) -> Value {
    let mut t = serde_json::Map::new();
    if target {
        t.insert("resonate:target".into(), json!(worker));
    }
    if external {
        t.insert("resonate:external".into(), json!("true"));
    }
    if timer {
        t.insert("resonate:timer".into(), json!("true"));
    }
    Value::Object(t)
}

fn value(data: &Option<String>) -> Value {
    match data {
        Some(d) => json!({ "data": d }),
        None => json!({}),
    }
}

fn create_data(c: &Create, worker: &str) -> Value {
    json!({ "id": c.id, "timeoutAt": c.timeout_at, "param": value(&c.data), "tags": tags(c.target, c.external, c.timer, worker) })
}

/// The request as the protocol carries it: kind and data.
fn encode(req: &Request, worker: &str) -> (&'static str, Value) {
    match req {
        Request::CreatePromise(c) => ("promise.create", create_data(c, worker)),
        Request::GetPromise(id) => ("promise.get", json!({ "id": id })),
        Request::SettlePromise(s) => ("promise.settle", json!({ "id": s.id, "state": s.state, "value": value(&s.data) })),
        Request::RegisterCallback { awaited, awaiter } => ("promise.register_callback", json!({ "awaited": awaited, "awaiter": awaiter })),
        Request::RegisterListener { awaited, address } => ("promise.register_listener", json!({ "awaited": awaited, "address": address })),
        Request::GetTask(id) => ("task.get", json!({ "id": id })),
        Request::CreateTask { id, timeout_at, data, target } => (
            "task.create",
            json!({ "pid": WORKER_SELF, "ttl": TASK_CREATE_TTL, "action": { "kind": "promise.create", "head": {}, "data": { "id": id, "timeoutAt": timeout_at, "param": value(data), "tags": tags(*target, false, false, worker) } } }),
        ),
        Request::AcquireTask { id, version, pid, ttl } => ("task.acquire", json!({ "id": id, "version": version, "pid": pid, "ttl": ttl })),
        Request::ReleaseTask { id, version } => ("task.release", json!({ "id": id, "version": version })),
        Request::FulfillTask { id, version, state, data } => ("task.fulfill", json!({ "id": id, "version": version, "action": { "kind": "promise.settle", "head": {}, "data": { "id": id, "state": state, "value": value(data) } } })),
        Request::HeartbeatTask { id, version, pid } => ("task.heartbeat", json!({ "pid": pid, "tasks": [{ "id": id, "version": version }] })),
        Request::SuspendTask { id, version, awaited } => (
            "task.suspend",
            json!({ "id": id, "version": version, "actions": awaited.iter().map(|a| json!({ "kind": "promise.register_callback", "head": {}, "data": { "awaited": a, "awaiter": id } })).collect::<Vec<_>>() }),
        ),
        Request::FenceTask { id, version, action } => {
            let action = match action {
                Fenced::Create(c) => json!({ "kind": "promise.create", "head": {}, "data": create_data(c, worker) }),
                Fenced::Settle(s) => json!({ "kind": "promise.settle", "head": {}, "data": { "id": s.id, "state": s.state, "value": value(&s.data) } }),
            };
            ("task.fence", json!({ "id": id, "version": version, "action": action }))
        }
    }
}

fn pstate(s: &str) -> Option<PState> {
    Some(match s {
        "pending" => PState::Pending,
        "resolved" => PState::Resolved,
        "rejected" => PState::Rejected,
        "rejected_canceled" => PState::Canceled,
        "rejected_timedout" => PState::TimedOut,
        _ => return None,
    })
}

fn tstate(s: &str) -> Option<TState> {
    Some(match s {
        "pending" => TState::Pending,
        "acquired" => TState::Acquired,
        "suspended" => TState::Suspended,
        "fulfilled" => TState::Fulfilled,
        _ => return None,
    })
}

fn prec(p: &Value) -> Option<PromiseRec> {
    let t = &p["tags"];
    Some(PromiseRec {
        id: p["id"].as_str()?.to_string(),
        state: pstate(p["state"].as_str()?)?,
        param: p["param"]["data"].as_str().map(str::to_string),
        value: p["value"]["data"].as_str().map(str::to_string),
        timeout_at: p["timeoutAt"].as_u64()?,
        created_at: p["createdAt"].as_u64()?,
        settled_at: p["settledAt"].as_u64(),
        tags: Tags { target: !t["resonate:target"].is_null(), external: t["resonate:external"].as_str() == Some("true"), timer: t["resonate:timer"].as_str() == Some("true") },
    })
}

fn trec(t: &Value) -> Option<TaskRec> {
    Some(TaskRec { id: t["id"].as_str()?.to_string(), state: tstate(t["state"].as_str()?)?, version: t["version"].as_u64()? as u32, pid: t["pid"].as_str().map(str::to_string), ttl: t["ttl"].as_u64() })
}

/// The answer as the model types it. A record the model does not know
/// (a halted task) is a status. `existed`: whether a `task.create` found
/// its id, which decides between the model's two shapes for it.
fn decode(kind: &str, status: u16, data: &Value, existed: bool) -> Response {
    if status != 200 {
        return Response::Status(status);
    }
    let body = if kind == "task.fence" { &data["action"]["data"] } else { data };
    match (prec(&body["promise"]), trec(&body["task"])) {
        (Some(p), Some(t)) if kind == "task.create" && !existed => Response::Created(p, t),
        (_, Some(t)) if matches!(kind, "task.get" | "task.acquire" | "task.create") => Response::Task(t),
        (Some(p), _) => Response::Promise(p),
        _ => Response::Status(status),
    }
}

/// The model's state, from echod's snapshot: what the suggestions read.
fn model_state(snap: &Value) -> Model {
    let mut promises: PMap<Promise> = PMap::empty();
    let mut callbacks: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for c in snap["callbacks"].as_array().into_iter().flatten() {
        if let (Some(a), Some(w)) = (c["awaited"].as_str(), c["awaiter"].as_str()) {
            callbacks.entry(a.to_string()).or_default().push(w.to_string());
        }
    }
    for p in snap["promises"].as_array().into_iter().flatten() {
        let Some(r) = prec(p) else { continue };
        let mut cbs = PSet::empty();
        for w in callbacks.get(&r.id).into_iter().flatten() {
            cbs.insert(w.clone());
        }
        promises.insert(
            r.id.clone(),
            Promise { state: r.state, value: r.value, param: r.param, timeout_at: r.timeout_at, created_at: r.created_at, settled_at: r.settled_at, target: r.tags.target, external_tag: r.tags.external, timer_tag: r.tags.timer, callbacks: cbs },
        );
    }
    let mut leases: BTreeMap<String, u64> = BTreeMap::new();
    for t in snap["taskTimeouts"].as_array().into_iter().flatten() {
        if t["type"].as_u64() == Some(1) {
            if let (Some(id), Some(at)) = (t["id"].as_str(), t["timeout"].as_u64()) {
                leases.insert(id.to_string(), at);
            }
        }
    }
    let mut tasks: PMap<Task> = PMap::empty();
    for t in snap["tasks"].as_array().into_iter().flatten() {
        let Some(r) = trec(t) else { continue };
        let acquired_at = match (leases.get(&r.id), r.ttl) {
            (Some(at), Some(ttl)) => at.saturating_sub(ttl),
            _ => 0,
        };
        tasks.insert(r.id.clone(), Task { state: r.state, version: r.version, pid: r.pid, ttl: r.ttl, acquired_at });
    }
    Model { promises, tasks }
}

// ---------------------------------------------------------------------------
// Driving
// ---------------------------------------------------------------------------

struct Driver {
    client: Client,
    echod: Server,
    sink: Arc<Sink>,
    worker: String,
    quiet_ms: u64,
    corr: u64,
}

impl Driver {
    async fn drain(&self) -> Vec<Value> {
        let mut last = self.sink.count();
        let mut quiet = 0;
        while quiet < 2 {
            tokio::time::sleep(Duration::from_millis(self.quiet_ms)).await;
            let n = self.sink.count();
            if n == last {
                quiet += 1;
            } else {
                last = n;
                quiet = 0;
            }
        }
        self.sink.take()
    }

    /// Everything the sink got, as the model's dispatches; `unblock`s are not its.
    async fn dispatches(&self) -> Vec<Dispatch> {
        self.drain()
            .await
            .into_iter()
            .filter(|m| m["kind"] == "execute")
            .filter_map(|m| Some(Dispatch::Execute { id: m["data"]["task"]["id"].as_str()?.to_string(), version: m["data"]["task"]["version"].as_u64()? as u32 }))
            .collect()
    }

    async fn send(&mut self, kind: &str, data: &Value, now: u64) -> (u16, Value) {
        self.corr += 1;
        let corr = format!("a{}", self.corr);
        self.client.send(&self.echod, kind, data, now as i64, &corr).await
    }

    async fn snap(&mut self, now: u64) -> Model {
        let (status, data) = self.send("debug.snap", &json!({}), now).await;
        assert_eq!(status, 200, "debug.snap: {data}");
        model_state(&data)
    }

    /// One action: taken, and everything observed appended to the trace.
    /// `state` is the model's state before it, as the snapshot gave it.
    async fn act(&mut self, a: Action<Request>, state: &Model, now: &mut u64, call: &mut u64, trace: &mut Trace) {
        match a {
            Action::Clock(at) => {
                if at <= *now {
                    return;
                }
                *now = at;
                trace.push(Event::Clock { at });
                let (status, data) = self.send("debug.tick", &json!({ "time": at }), at).await;
                assert_eq!(status, 200, "debug.tick: {data}");
                for d in self.dispatches().await {
                    trace.push(Event::Receive { msg: d });
                }
            }
            Action::Request(req) => {
                *call += 1;
                let existed = match &req {
                    Request::CreateTask { id, .. } => state.promises.contains_key(id),
                    _ => false,
                };
                let (kind, data) = encode(&req, &self.worker);
                trace.push(Event::Invoke { call: *call, req: req.clone() });
                let (status, body) = self.send(kind, &data, *now).await;
                let res = decode(kind, status, &body, existed);
                // what the request made the server send comes before its answer
                // is observed, as the model has it: the dispatch is the step's
                for d in self.dispatches().await {
                    trace.push(Event::Receive { msg: d });
                }
                trace.push(Event::Return { call: *call, res });
            }
        }
    }

    /// One run: echod reset, `requests` actions from the model, then its
    /// finishing reads. Returns the trace as a client saw it.
    async fn run(&mut self, requests: usize, guided: bool, choices: &mut Choices) -> Trace {
        let (status, _) = self.send("debug.reset", &json!({}), T0).await;
        assert_eq!(status, 200);
        self.drain().await;
        let mut trace: Trace = vec![Event::Clock { at: T0 }];
        let mut now = T0;
        let mut call: u64 = 0;
        for _ in 0..requests {
            let state = self.snap(now).await;
            let a = if guided {
                let suggested: Vec<(Action<Request>, &'static str)> = Resonate.suggest(&state, now).into_iter().filter(|(a, _)| !detached(a) && !stillborn(a, now)).collect();
                // one time in four, anything; otherwise a suggestion taken least
                if suggested.is_empty() || choices.pick(4) == 0 {
                    Resonate.arbitrary(&state, now, &mut |n| choices.pick(n))
                } else {
                    let labels: Vec<&'static str> = suggested.iter().map(|(_, why)| *why).collect();
                    suggested[choices.pick_labeled(&labels)].0.clone()
                }
            } else {
                Resonate.arbitrary(&state, now, &mut |n| choices.pick(n))
            };
            if detached(&a) || stillborn(&a, now) {
                continue;
            }
            self.act(a, &state, &mut now, &mut call, &mut trace).await;
        }
        let state = self.snap(now).await;
        for a in Resonate.finish(&state, now) {
            self.act(a, &state, &mut now, &mut call, &mut trace).await;
        }
        trace
    }
}

/// A fence that creates a promise in another origin: the C# spec's detached
/// create, which the Lean specification and echod refuse.
fn detached(a: &Action<Request>) -> bool {
    match a {
        Action::Request(Request::FenceTask { id, action: Fenced::Create(c), .. }) => origin(id) != origin(&c.id),
        _ => false,
    }
}

/// A task created already past its deadline: a branch the model does not
/// have.
fn stillborn(a: &Action<Request>, now: u64) -> bool {
    matches!(a, Action::Request(Request::CreateTask { timeout_at, .. }) if *timeout_at <= now)
}

fn origin(id: &str) -> &str {
    id.split_once(':').map_or(id, |(o, _)| o)
}

// ---------------------------------------------------------------------------
// Checking
// ---------------------------------------------------------------------------

enum Outcome {
    Ok(BTreeSet<&'static str>),
    Ko(Violation),
    Unknown(Violation),
}

fn check(trace: &Trace) -> Outcome {
    let mut c: Checker<Keyed<Resonate>> = Checker::with_footprints(Resonate, Model::default(), Config { certify: true, ..Config::default() });
    match Verdict::from(c.check_certified(trace.clone())) {
        Verdict::Ok(cert) => Outcome::Ok(marks(&Resonate, Model::default(), trace, &cert).expect("the certificate replays")),
        Verdict::Ko(v) => Outcome::Ko(v),
        Verdict::Unknown(v) => Outcome::Unknown(v),
    }
}

fn show(trace: &Trace, upto: usize) -> String {
    let mut out = String::new();
    for (i, e) in trace.iter().enumerate().take(upto + 1) {
        let line = match e {
            Event::Invoke { call, req } => format!("call {call:>2} → {req:?}"),
            Event::Return { call, res } => format!("call {call:>2} ← {res:?}"),
            Event::Receive { msg } => format!("        ⇐ {msg:?}"),
            Event::Clock { at } => format!("        ⏲ clock {at}"),
        };
        out.push_str(&format!("{i:>3}  {line}\n"));
    }
    out
}

#[tokio::main]
async fn main() {
    let cli = Cli::parse();
    let sink = Arc::new(Sink::default());
    let worker = start_sink(Arc::clone(&sink)).await;
    // no redispatch within any run: the model has none
    let echod = spawn_echod(&cli.echod, "http://localhost:8001", 1_000_000_000_000, &cli.logs);
    let client = Client::new();
    client.wait_ready(&echod).await;
    eprintln!("[accordant] echod at {}, worker at {worker}", echod.url);
    let mut d = Driver { client, echod, sink, worker, quiet_ms: cli.quiet_ms, corr: 0 };

    let mut table: BTreeMap<&str, [usize; 2]> = MARKS.iter().map(|m| (*m, [0, 0])).collect();
    println!("{} runs of {} requests each against echod\n", cli.runs, cli.requests);
    println!("{:<8} {:>4} {:>4} {:>8} {:>9} {:>14}", "mode", "ok", "ko", "unknown", "marks", "first ko (seed)");
    let mut examples: Vec<String> = Vec::new();
    let mut kos_total = 0;
    for (k, guided) in [false, true].into_iter().enumerate() {
        let (mut ok, mut ko, mut unknown, mut first_ko) = (0, 0, 0, None);
        let tried = Tried::default();
        let mut classes: BTreeMap<String, (usize, String)> = BTreeMap::new();
        for seed in cli.seed..cli.seed + cli.runs {
            let mut choices = Choices::random(seed).learning(&tried);
            let trace = d.run(cli.requests, guided, &mut choices).await;
            if cli.trace {
                eprintln!("[run seed={seed} guided={guided}]\n{}", show(&trace, trace.len()));
            }
            match check(&trace) {
                Outcome::Ok(seen) => {
                    ok += 1;
                    for m in seen {
                        table.get_mut(m).expect("a declared mark")[k] += 1;
                    }
                }
                Outcome::Ko(v) => {
                    ko += 1;
                    first_ko.get_or_insert(seed);
                    // the class: the event no execution explains
                    let class = match trace.get(v.index) {
                        Some(Event::Return { call, res }) => {
                            let req = trace.iter().find_map(|e| match e {
                                Event::Invoke { call: c, req } if c == call => Some(req),
                                _ => None,
                            });
                            format!("{} ← {res:?}", req.map(|r| short_req(r)).unwrap_or_default())
                        }
                        Some(Event::Receive { msg }) => format!("⇐ {msg:?}"),
                        Some(Event::Clock { .. }) => "clock".to_string(),
                        Some(Event::Invoke { req, .. }) => format!("→ {}", short_req(req)),
                        None => "end".to_string(),
                    };
                    let e = classes.entry(class).or_insert_with(|| (0, format!("seed {seed}: {}\n{}", v.reason, show(&trace, v.index))));
                    e.0 += 1;
                }
                Outcome::Unknown(v) => {
                    unknown += 1;
                    eprintln!("unknown (seed {seed}): {v}");
                }
            }
        }
        kos_total += ko;
        let covered = table.values().filter(|n| n[k] > 0).count();
        let mode = if guided { "guided" } else { "random" };
        let first = first_ko.map_or("-".to_string(), |s| s.to_string());
        println!("{mode:<8} {ok:>4} {ko:>4} {unknown:>8} {:>9} {first:>14}", format!("{covered}/{}", MARKS.len()));
        for (class, (n, example)) in classes {
            examples.push(format!("[{mode}] {n} run(s) stop at: {class}\n{example}"));
        }
    }
    println!("\n{:<45} {:>7} {:>7}", "mark (runs that reached it)", "random", "guided");
    for (m, [a, b]) in &table {
        println!("{m:<45} {a:>7} {b:>7}");
    }
    for e in &examples {
        println!("\n{e}");
    }
    drop(d);
    if kos_total > 0 {
        std::process::exit(1);
    }
}

fn short_req(r: &Request) -> String {
    let s = format!("{r:?}");
    s.split(|c: char| c == '(' || c == ' ').next().unwrap_or(&s).to_string()
}
