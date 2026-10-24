//! echod-accordant: echod driven by the Resonate model of `dtornow/accordant`,
//! over HTTP, and every trace checked against that model.
//!
//! The model (`accordant`'s `examples/resonate`) is an executable
//! specification in Verus of the Resonate protocol as the Lean specification
//! has it: what every request does, what runs on its own (a deadline, a lease,
//! a resume, a redispatch, a schedule's occurrence), what the server sends.
//! Its fuzz example drives the model itself; this drives echod. A run resets
//! echod, then takes the model's own actions (`Explore::suggest`, steered by
//! what the model has seen least, or `Explore::arbitrary`, random) one at a
//! time: a request is sent with the run's clock as `head.debug_time` and its
//! answer recorded; a clock move is recorded and then handed to echod as
//! `debug.tick`, so the sweep runs at the instant the model's timers fire;
//! every `execute` and `unblock` the sink receives is recorded as a dispatch.
//! Then the model's `finish` actions: read everything, delete the schedules,
//! move the clock past every deadline, read again. The trace is checked with
//! certificates, and the marks of the execution that explains it are the
//! coverage.
//!
//! The model and echod are meant to say the same thing everywhere, so
//! nothing is translated: a fence that creates a promise in another origin
//! (a detached workflow, the create first and then the fence's check) is sent
//! as any other request, and `task.create` in every state too. One request is
//! not sent: a timer created with a target (by a create, a fence or a
//! schedule), which echod accepts with the target dropped (a concession to
//! the SDKs' sleep) and the model refuses, as the Lean specification does. What is dropped before checking: `preload`
//! and the records the model does not carry (a promise's param and value are
//! strings here, not values with headers). echod runs with the model's retry
//! timeout, so redispatches happen in both at the same instants.
//!
//! ```text
//! echod-accordant --echod ../../target/release/echod [--runs 200] [--requests 30] [--retry-timeout 5000]
//! ```

#[path = "../../src/harness.rs"]
mod harness;

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use accordant::{marks, Action, Checker, Choices, Config, Event, Explore, Keyed, Tried, Verdict, Violation};
use clap::Parser;
use resonate::{Create, Dispatch, Fenced, PMap, PSet, PState, Promise, PromiseRec, Request, Resonate, Response, Schedule, Server as Model, TState, Tags, Task, TaskRec, MARKS};
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
    /// How long a pending task waits before it is offered again, ms: echod's
    /// `--retry-timeout` and the model's `retry_timeout`.
    #[arg(long, default_value_t = 5_000)]
    retry_timeout: u64,
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

// ---------------------------------------------------------------------------
// The model's vocabulary on the wire
// ---------------------------------------------------------------------------

fn tags(t: &Tags, worker: &str) -> Value {
    let mut m = serde_json::Map::new();
    if t.target {
        m.insert("resonate:target".into(), json!(worker));
    }
    if t.external {
        m.insert("resonate:external".into(), json!("true"));
    }
    if t.timer {
        m.insert("resonate:timer".into(), json!("true"));
    }
    if let Some(d) = t.delay {
        m.insert("resonate:delay".into(), json!(d.to_string()));
    }
    Value::Object(m)
}

fn value(data: &Option<String>) -> Value {
    match data {
        Some(d) => json!({ "data": d }),
        None => json!({}),
    }
}

fn create_data(c: &Create, worker: &str) -> Value {
    json!({ "id": c.id, "timeoutAt": c.timeout_at, "param": value(&c.data), "tags": tags(&c.tags, worker) })
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
        Request::CreateTask { pid, ttl, action } => ("task.create", json!({ "pid": pid, "ttl": ttl, "action": { "kind": "promise.create", "head": {}, "data": create_data(action, worker) } })),
        Request::AcquireTask { id, version, pid, ttl } => ("task.acquire", json!({ "id": id, "version": version, "pid": pid, "ttl": ttl })),
        Request::ReleaseTask { id, version } => ("task.release", json!({ "id": id, "version": version })),
        Request::FulfillTask { id, version, state, data } => ("task.fulfill", json!({ "id": id, "version": version, "action": { "kind": "promise.settle", "head": {}, "data": { "id": id, "state": state, "value": value(data) } } })),
        Request::HeartbeatTask { pid, tasks } => ("task.heartbeat", json!({ "pid": pid, "tasks": tasks.iter().map(|t| json!({ "id": t.id, "version": t.version })).collect::<Vec<_>>() })),
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
        Request::HaltTask(id) => ("task.halt", json!({ "id": id })),
        Request::ContinueTask(id) => ("task.continue", json!({ "id": id })),
        Request::CreateSchedule(c) => (
            "schedule.create",
            json!({ "id": c.id, "cron": c.cron, "promiseId": c.promise_id, "promiseTimeout": c.promise_timeout, "promiseParam": value(&c.promise_param), "promiseTags": tags(&c.promise_tags, worker) }),
        ),
        Request::GetSchedule(id) => ("schedule.get", json!({ "id": id })),
        Request::DeleteSchedule(id) => ("schedule.delete", json!({ "id": id })),
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
        "halted" => TState::Halted,
        "fulfilled" => TState::Fulfilled,
        _ => return None,
    })
}

fn tags_in(t: &Value) -> Tags {
    Tags {
        target: !t["resonate:target"].is_null(),
        external: t["resonate:external"].as_str() == Some("true"),
        timer: t["resonate:timer"].as_str() == Some("true"),
        delay: t["resonate:delay"].as_str().and_then(|d| d.parse().ok()),
    }
}

fn prec(p: &Value) -> Option<PromiseRec> {
    Some(PromiseRec {
        id: p["id"].as_str()?.to_string(),
        state: pstate(p["state"].as_str()?)?,
        param: p["param"]["data"].as_str().map(str::to_string),
        value: p["value"]["data"].as_str().map(str::to_string),
        timeout_at: p["timeoutAt"].as_u64()?,
        created_at: p["createdAt"].as_u64()?,
        settled_at: p["settledAt"].as_u64(),
        tags: tags_in(&p["tags"]),
    })
}

fn trec(t: &Value) -> Option<TaskRec> {
    Some(TaskRec {
        id: t["id"].as_str()?.to_string(),
        state: tstate(t["state"].as_str()?)?,
        version: t["version"].as_u64()? as u32,
        pid: t["pid"].as_str().map(str::to_string),
        ttl: t["ttl"].as_u64(),
        resumes: t["resumes"].as_u64().unwrap_or(0) as u32,
    })
}

fn srec(c: &Value) -> Option<Schedule> {
    Some(Schedule {
        id: c["id"].as_str()?.to_string(),
        cron: c["cron"].as_str()?.to_string(),
        promise_id: c["promiseId"].as_str()?.to_string(),
        promise_timeout: c["promiseTimeout"].as_u64()?,
        promise_param: c["promiseParam"]["data"].as_str().map(str::to_string),
        promise_tags: tags_in(&c["promiseTags"]),
        created_at: c["createdAt"].as_u64()?,
        next_run_at: c["nextRunAt"].as_u64()?,
        last_run_at: c["lastRunAt"].as_u64(),
    })
}

/// The answer as the model types it.
fn decode(kind: &str, status: u16, data: &Value) -> Response {
    if status != 200 {
        return Response::Status(status);
    }
    // a fence answers 200 with its action's own envelope inside; the model
    // types the fence as that action's status
    if kind == "task.fence" {
        if let Some(inner) = data["action"]["head"]["status"].as_u64() {
            if inner != 200 {
                return Response::Status(inner as u16);
            }
        }
    }
    let body = if kind == "task.fence" { &data["action"]["data"] } else { data };
    if kind.starts_with("schedule.") {
        return match srec(&body["schedule"]) {
            Some(c) => Response::Schedule(c),
            None => Response::Status(status),
        };
    }
    match (prec(&body["promise"]), trec(&body["task"])) {
        (Some(p), Some(t)) => Response::Both(p, t),
        (None, Some(t)) => Response::Task(t),
        (Some(p), None) => Response::Promise(p),
        (None, None) => Response::Status(status),
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
    let mut listeners: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for l in snap["listeners"].as_array().into_iter().flatten() {
        if let (Some(id), Some(a)) = (l["id"].as_str(), l["address"].as_str()) {
            listeners.entry(id.to_string()).or_default().push(a.to_string());
        }
    }
    for p in snap["promises"].as_array().into_iter().flatten() {
        let Some(r) = prec(p) else { continue };
        let mut cbs = PSet::empty();
        for w in callbacks.get(&r.id).into_iter().flatten() {
            cbs.insert(w.clone());
        }
        let mut ls = PSet::empty();
        for a in listeners.get(&r.id).into_iter().flatten() {
            ls.insert(a.clone());
        }
        promises.insert(
            r.id.clone(),
            Promise { state: r.state, value: r.value, param: r.param, timeout_at: r.timeout_at, created_at: r.created_at, settled_at: r.settled_at, tags: r.tags, callbacks: cbs, listeners: ls },
        );
    }
    let mut leases: BTreeMap<String, u64> = BTreeMap::new();
    let mut retries: BTreeMap<String, u64> = BTreeMap::new();
    for t in snap["taskTimeouts"].as_array().into_iter().flatten() {
        if let (Some(id), Some(at)) = (t["id"].as_str(), t["timeout"].as_u64()) {
            match t["type"].as_u64() {
                Some(1) => leases.insert(id.to_string(), at),
                Some(0) => retries.insert(id.to_string(), at),
                _ => None,
            };
        }
    }
    let mut tasks: PMap<Task> = PMap::empty();
    for t in snap["tasks"].as_array().into_iter().flatten() {
        let Some(r) = trec(t) else { continue };
        let acquired_at = match (leases.get(&r.id), r.ttl) {
            (Some(at), Some(ttl)) => at.saturating_sub(ttl),
            _ => 0,
        };
        // the count is what the record carries; the ids are not
        let resumes = (0..r.resumes).map(|i| format!("resume-{i}")).collect();
        tasks.insert(r.id.clone(), Task { state: r.state, version: r.version, pid: r.pid, ttl: r.ttl, acquired_at, retry_at: retries.get(&r.id).copied(), resumes });
    }
    let mut schedules: PMap<Schedule> = PMap::empty();
    for c in snap["schedules"].as_array().into_iter().flatten() {
        if let Some(c) = srec(c) {
            schedules.insert(c.id.clone(), c);
        }
    }
    Model { promises, tasks, schedules }
}

// ---------------------------------------------------------------------------
// Driving
// ---------------------------------------------------------------------------

struct Driver {
    client: Client,
    echod: Server,
    sink: Arc<Sink>,
    worker: String,
    model: Resonate,
    quiet_ms: u64,
    corr: u64,
}

impl Driver {
    async fn drain(&self) -> Vec<(String, Value)> {
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
        self.sink.take_addressed()
    }

    /// Everything the sink got, as the model's dispatches.
    async fn dispatches(&self) -> Vec<Dispatch> {
        self.drain()
            .await
            .into_iter()
            .filter_map(|(address, m)| match m["kind"].as_str()? {
                "execute" => Some(Dispatch::Execute { id: m["data"]["task"]["id"].as_str()?.to_string(), version: m["data"]["task"]["version"].as_u64()? as u32 }),
                "unblock" => Some(Dispatch::Unblock { address, promise: prec(&m["data"]["promise"])? }),
                _ => None,
            })
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

    /// echod's one concession to the SDKs as they are: a timer created with a
    /// target (a sleep) is accepted with its target dropped, where the Lean
    /// specification and the model refuse it. Such creates are not sent.
    fn conceded(a: &Action<Request>) -> bool {
        let timer_with_target = |c: &Create| c.tags.timer && c.tags.target;
        match a {
            Action::Request(Request::CreatePromise(c)) => timer_with_target(c),
            Action::Request(Request::FenceTask { action: Fenced::Create(c), .. }) => timer_with_target(c),
            Action::Request(Request::CreateSchedule(c)) => c.promise_tags.timer && c.promise_tags.target,
            _ => false,
        }
    }

    /// A listener's address the sink answers at: the model's addresses under
    /// `http://listener/` are given the sink's host, so the unblock comes back
    /// and names the address it went to. Other schemes are left as they are:
    /// nothing receives them, which the model allows.
    fn addressed(&self, a: Action<Request>) -> Action<Request> {
        match a {
            Action::Request(Request::RegisterListener { awaited, address }) if address.starts_with("http://listener/") => {
                let address = format!("{}{}", self.worker, address.trim_start_matches("http://"));
                Action::Request(Request::RegisterListener { awaited, address })
            }
            a => a,
        }
    }

    /// One action: taken, and everything observed appended to the trace.
    async fn act(&mut self, a: Action<Request>, now: &mut u64, call: &mut u64, trace: &mut Trace) {
        if Self::conceded(&a) {
            return;
        }
        match self.addressed(a) {
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
                let (kind, data) = encode(&req, &self.worker);
                trace.push(Event::Invoke { call: *call, req: req.clone() });
                let (status, body) = self.send(kind, &data, *now).await;
                let res = decode(kind, status, &body);
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
                let suggested = self.model.suggest(&state, now);
                // one time in four, anything; otherwise a suggestion taken least
                if suggested.is_empty() || choices.pick(4) == 0 {
                    self.model.arbitrary(&state, now, &mut |n| choices.pick(n))
                } else {
                    let labels: Vec<&'static str> = suggested.iter().map(|(_, why)| *why).collect();
                    suggested[choices.pick_labeled(&labels)].0.clone()
                }
            } else {
                self.model.arbitrary(&state, now, &mut |n| choices.pick(n))
            };
            self.act(a, &mut now, &mut call, &mut trace).await;
        }
        let state = self.snap(now).await;
        for a in self.model.finish(&state, now) {
            self.act(a, &mut now, &mut call, &mut trace).await;
        }
        trace
    }
}

// ---------------------------------------------------------------------------
// Checking
// ---------------------------------------------------------------------------

enum Outcome {
    Ok(BTreeSet<&'static str>),
    Ko(Violation),
    Unknown(Violation),
}

fn check(model: &Resonate, trace: &Trace) -> Outcome {
    let m = Resonate { retry_timeout: model.retry_timeout };
    let mut c: Checker<Keyed<Resonate>> = Checker::with_footprints(m, Model::default(), Config { certify: true, ..Config::default() });
    match Verdict::from(c.check_certified(trace.clone())) {
        Verdict::Ok(cert) => Outcome::Ok(marks(model, Model::default(), trace, &cert).expect("the certificate replays")),
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
    let echod = spawn_echod(&cli.echod, "http://localhost:8001", cli.retry_timeout, &cli.logs);
    let client = Client::new();
    client.wait_ready(&echod).await;
    eprintln!("[accordant] echod at {}, worker at {worker}", echod.url);
    let model = Resonate { retry_timeout: cli.retry_timeout };
    let mut d = Driver { client, echod, sink, worker, model, quiet_ms: cli.quiet_ms, corr: 0 };

    let mut table: BTreeMap<&str, [usize; 2]> = MARKS.iter().map(|m| (*m, [0, 0])).collect();
    println!("{} runs of {} requests each against echod, retry timeout {} ms\n", cli.runs, cli.requests, cli.retry_timeout);
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
            match check(&d.model, &trace) {
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
    println!("\n{:<50} {:>7} {:>7}", "mark (runs that reached it)", "random", "guided");
    for (m, [a, b]) in &table {
        println!("{m:<50} {a:>7} {b:>7}");
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
