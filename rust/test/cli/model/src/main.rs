//! echod-model: echod driven by the Resonate model,
//! over HTTP, and every trace checked against that model.
//!
//! The model (`echod_abstract_spec`, the Echod abstract model) is an executable
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
//! echod-model --echod target/release/echod [--runs 200] [--requests 30] [--retry-timeout 5000]
//! ```

#[path = "../../diff/src/harness.rs"]
mod harness;
mod wire;
mod choices;

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use clap::Parser;
use echod_rover_exec::{check as check_trace, marks, CheckConfig};
use echod_abstract_spec::types::{PromiseRegisterListenerReq, Request, TaskFenceAction};
use echod_abstract_spec::{Dispatch, ServerConfig};
use echod_abstract_exec::{
    arbitrary, finish, history_rank, history_responses, rover_trace, suggest,
    Action, HistoryEvent, EchodAbstractExec, Store as AbstractStore, MARKS,
};
use serde_json::{json, Value};

use crate::harness::{spawn_echod, start_sink, Client, Server, Sink};
use crate::wire::{decode, encode, model_state, prec};
use crate::choices::{Choices, Tried};

#[derive(Parser, Debug)]
#[command(name = "echod-model", about = "echod driven by the Resonate model, over HTTP")]
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
type Trace = Vec<HistoryEvent>;

const T0: u64 = 1_000_000;

// ---------------------------------------------------------------------------
// Driving
// ---------------------------------------------------------------------------

struct Driver {
    client: Client,
    echod: Server,
    sink: Arc<Sink>,
    worker: String,
    model: ServerConfig,
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
                "execute" => Some(Dispatch::Execute { id: m["data"]["task"]["id"].as_str()?.to_string(), version: m["data"]["task"]["version"].as_u64()? }),
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

    async fn snap(&mut self, now: u64) -> AbstractStore {
        let (status, data) = self.send("debug.snap", &json!({}), now).await;
        assert_eq!(status, 200, "debug.snap: {data}");
        model_state(&data)
    }

    /// echod's one concession to the SDKs as they are: a timer created with a
    /// target (a sleep) is accepted with its target dropped, where the Lean
    /// specification and the model refuse it. Such creates are not sent.
    fn conceded(a: &Action<Request>) -> bool {
        let timer_with_target = |tags: &[(String, String)]| {
            let timer = tags.iter().any(|(k, v)| k == "resonate:timer" && v == "true");
            let target = tags.iter().any(|(k, _)| k == "resonate:target");
            timer && target
        };
        match a {
            Action::Request(Request::PromiseCreate(c)) => timer_with_target(&c.tags),
            Action::Request(Request::TaskFence(f)) => matches!(&f.action, TaskFenceAction::Create(c) if timer_with_target(&c.tags)),
            Action::Request(Request::ScheduleCreate(c)) => timer_with_target(&c.promise_tags),
            _ => false,
        }
    }

    /// A listener's address the sink answers at: the model's addresses under
    /// `http://listener/` are given the sink's host, so the unblock comes back
    /// and names the address it went to. Other schemes are left as they are:
    /// nothing receives them, which the model allows.
    fn addressed(&self, a: Action<Request>) -> Action<Request> {
        match a {
            Action::Request(Request::PromiseRegisterListener(PromiseRegisterListenerReq { awaited, address })) if address.starts_with("http://listener/") => {
                let address = format!("{}{}", self.worker, address.trim_start_matches("http://"));
                Action::Request(Request::PromiseRegisterListener(PromiseRegisterListenerReq { awaited, address }))
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
                trace.push(HistoryEvent::Clock { at });
                let (status, data) = self.send("debug.tick", &json!({ "time": at }), at).await;
                assert_eq!(status, 200, "debug.tick: {data}");
                for d in self.dispatches().await {
                    trace.push(HistoryEvent::Receive { msg: d });
                }
            }
            Action::Request(req) => {
                *call += 1;
                let (kind, data) = encode(&req, &self.worker);
                trace.push(HistoryEvent::Invoke { call: *call, req: req.clone() });
                let (status, body) = self.send(kind, &data, *now).await;
                let res = decode(kind, status, &body);
                // what the request made the server send comes before its answer
                // is observed, as the model has it: the dispatch is the step's
                for d in self.dispatches().await {
                    trace.push(HistoryEvent::Receive { msg: d });
                }
                trace.push(HistoryEvent::Return { call: *call, res });
            }
        }
    }

    /// One run: echod reset, `requests` actions from the model, then its
    /// finishing reads. Returns the trace as a client saw it.
    async fn run(&mut self, requests: usize, guided: bool, choices: &mut Choices) -> Trace {
        let (status, _) = self.send("debug.reset", &json!({}), T0).await;
        assert_eq!(status, 200);
        self.drain().await;
        let mut trace: Trace = vec![HistoryEvent::Clock { at: T0 }];
        let mut now = T0;
        let mut call: u64 = 0;
        for _ in 0..requests {
            let state = self.snap(now).await;
            let a = if guided {
                let suggested = suggest(&state, now);
                // one time in four, anything; otherwise a suggestion taken least
                if suggested.is_empty() || choices.pick(4) == 0 {
                    arbitrary(&state, now, &mut |n| choices.pick(n))
                } else {
                    let labels: Vec<&'static str> = suggested.iter().map(|(_, why)| *why).collect();
                    suggested[choices.pick_labeled(&labels)].0.clone()
                }
            } else {
                arbitrary(&state, now, &mut |n| choices.pick(n))
            };
            self.act(a, &mut now, &mut call, &mut trace).await;
        }
        let state = self.snap(now).await;
        for a in finish(&state, now) {
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
    Unknown(Violation),
}

struct Violation {
    reason: String,
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.reason)
    }
}

fn check(model: &ServerConfig, trace: &Trace) -> Outcome {
    let config = ServerConfig { retry_timeout: model.retry_timeout };
    let events = rover_trace(trace);
    let expected = history_responses(trace);
    match check_trace(
        &EchodAbstractExec,
        &config,
        &events,
        CheckConfig::for_trace_len(events.len()),
        |event, action, sent| history_rank(event, action, sent, &expected),
    ) {
        Some(certificate) => Outcome::Ok(
            marks(&EchodAbstractExec, &config, &certificate).expect("the certificate replays"),
        ),
        None => Outcome::Unknown(Violation {
            reason: "bounded Rover search found no certificate".into(),
        }),
    }
}

fn show(trace: &Trace, upto: usize) -> String {
    let mut out = String::new();
    for (i, e) in trace.iter().enumerate().take(upto + 1) {
        let line = match e {
            HistoryEvent::Invoke { call, req } => format!("call {call:>2} → {req:?}"),
            HistoryEvent::Return { call, res } => format!("call {call:>2} ← {res:?}"),
            HistoryEvent::Receive { msg } => format!("        ⇐ {msg:?}"),
            HistoryEvent::Clock { at } => format!("        ⏲ clock {at}"),
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
    eprintln!("[model] echod at {}, worker at {worker}", echod.url);
    // `debug.tick` lets every due step land before the next request: fires are exact.
    let model = ServerConfig { retry_timeout: cli.retry_timeout };
    let mut d = Driver { client, echod, sink, worker, model, quiet_ms: cli.quiet_ms, corr: 0 };

    let mut table: BTreeMap<&str, [usize; 2]> = MARKS.iter().map(|m| (*m, [0, 0])).collect();
    println!("{} runs of {} requests each against echod, retry timeout {} ms\n", cli.runs, cli.requests, cli.retry_timeout);
    println!("{:<8} {:>4} {:>8} {:>9}", "mode", "ok", "unknown", "marks");
    for (k, guided) in [false, true].into_iter().enumerate() {
        let (mut ok, mut unknown) = (0, 0);
        let tried = Tried::default();
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
                Outcome::Unknown(v) => {
                    unknown += 1;
                    eprintln!("unknown (seed {seed}): {v}");
                }
            }
        }
        let covered = table.values().filter(|n| n[k] > 0).count();
        let mode = if guided { "guided" } else { "random" };
        println!("{mode:<8} {ok:>4} {unknown:>8} {:>9}", format!("{covered}/{}", MARKS.len()));
    }
    println!("\n{:<50} {:>7} {:>7}", "mark (runs that reached it)", "random", "guided");
    for (m, [a, b]) in &table {
        println!("{m:<50} {a:>7} {b:>7}");
    }
    drop(d);
}
