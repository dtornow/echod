//! echod-accordant: echod driven by the Resonate model of `dtornow/accordant`,
//! over HTTP, and every trace checked against that model.
//!
//! The model (`accordant`'s `examples/resonate`) is an executable
//! specification in Verus of the Resonate protocol as the Lean specification
//! has it: what every request does, what runs on its own (a deadline, a lease,
//! a resume, a redispatch, a schedule's occurrence), what the server sends.
//! Its fuzz example drives the model itself; this drives an isolated echod
//! process per run. Requests, responses, and every `execute` and `unblock`
//! received by the sink form the trace. Production timers run normally;
//! short model clock moves wait for wall time, while long synthetic jumps
//! are skipped. The trace is checked with certificates, and the marks of the
//! execution that explains it are the coverage.
//!
//! The model and echod are meant to say the same thing everywhere, so
//! nothing is translated: a fence that creates a promise in another origin
//! (a detached workflow, the fence's check first and then the create) is sent
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
mod wire;

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use accordant::{
    marks, Action, Checker, Choices, Config, Event, Explore, Keyed, Tried, Verdict, Violation,
};
use clap::Parser;
use resonate::{Create, Dispatch, Fenced, Request, Resonate, Response, Server as Model, MARKS};
use serde_json::Value;

use crate::harness::{spawn_echod, start_sink, Client, Server, Sink};
use crate::wire::{decode, encode, prec};

#[derive(Parser, Debug)]
#[command(
    name = "echod-accordant",
    about = "echod driven by accordant's Resonate model, over HTTP"
)]
struct Cli {
    #[arg(long, default_value = "../../target/release/echod")]
    echod: PathBuf,
    /// Runs per mode (random, guided).
    #[arg(long, default_value_t = 200)]
    runs: u64,
    /// Actions per isolated run.
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
                "execute" => Some(Dispatch::Execute {
                    id: m["data"]["task"]["id"].as_str()?.to_string(),
                    version: m["data"]["task"]["version"].as_u64()? as u32,
                }),
                "unblock" => Some(Dispatch::Unblock {
                    address,
                    promise: prec(&m["data"]["promise"])?,
                }),
                _ => None,
            })
            .collect()
    }

    async fn send(&mut self, kind: &str, data: &Value, now: u64) -> (u16, Value) {
        self.corr += 1;
        let corr = format!("a{}", self.corr);
        let _ = now;
        self.client.send(&self.echod, kind, data, &corr).await
    }

    /// echod's one concession to the SDKs as they are: a timer created with a
    /// target (a sleep) is accepted with its target dropped, where the Lean
    /// specification and the model refuse it. Such creates are not sent.
    fn conceded(a: &Action<Request>) -> bool {
        let timer_with_target = |c: &Create| c.tags.timer && c.tags.target;
        match a {
            Action::Request(Request::CreatePromise(c)) => timer_with_target(c),
            Action::Request(Request::FenceTask {
                action: Fenced::Create(c),
                ..
            }) => timer_with_target(c),
            Action::Request(Request::CreateSchedule(c)) => {
                c.promise_tags.timer && c.promise_tags.target
            }
            _ => false,
        }
    }

    /// A listener's address the sink answers at: the model's addresses under
    /// `http://listener/` are given the sink's host, so the unblock comes back
    /// and names the address it went to. Other schemes are left as they are:
    /// nothing receives them, which the model allows.
    fn addressed(&self, a: Action<Request>) -> Action<Request> {
        match a {
            Action::Request(Request::RegisterListener { awaited, address })
                if address.starts_with("http://listener/") =>
            {
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
                let wait = at - *now;
                if wait > 5_000 {
                    return;
                }
                tokio::time::sleep(Duration::from_millis(wait)).await;
                *now = resonate_core::util::system_time_ms().max(0) as u64;
                trace.push(Event::Clock { at: *now });
                for d in self.dispatches().await {
                    trace.push(Event::Receive { msg: d });
                }
            }
            Action::Request(req) => {
                *call += 1;
                let (kind, data) = encode(&req, &self.worker);
                trace.push(Event::Invoke {
                    call: *call,
                    req: req.clone(),
                });
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

    /// One isolated-process run as a client saw it.
    async fn run(&mut self, requests: usize, guided: bool, choices: &mut Choices) -> Trace {
        let mut now = resonate_core::util::system_time_ms().max(0) as u64;
        let mut trace: Trace = vec![Event::Clock { at: now }];
        let mut call: u64 = 0;
        let state = Model::default();
        for _ in 0..requests {
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
    let m = Resonate {
        retry_timeout: model.retry_timeout,
        fire_within: model.fire_within,
    };
    let mut c: Checker<Keyed<Resonate>> = Checker::with_footprints(
        m,
        Model::default(),
        Config {
            certify: true,
            ..Config::default()
        },
    );
    match Verdict::from(c.check_certified(trace.clone())) {
        Verdict::Ok(cert) => Outcome::Ok(
            marks(model, Model::default(), trace, &cert).expect("the certificate replays"),
        ),
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
    let mut table: BTreeMap<&str, [usize; 2]> = MARKS.iter().map(|m| (*m, [0, 0])).collect();
    println!(
        "{} runs of {} requests each against echod, retry timeout {} ms\n",
        cli.runs, cli.requests, cli.retry_timeout
    );
    println!(
        "{:<8} {:>4} {:>4} {:>8} {:>9} {:>14}",
        "mode", "ok", "ko", "unknown", "marks", "first ko (seed)"
    );
    let mut examples: Vec<String> = Vec::new();
    let mut kos_total = 0;
    for (k, guided) in [false, true].into_iter().enumerate() {
        let (mut ok, mut ko, mut unknown, mut first_ko) = (0, 0, 0, None);
        let tried = Tried::default();
        let mut classes: BTreeMap<String, (usize, String)> = BTreeMap::new();
        for seed in cli.seed..cli.seed + cli.runs {
            let sink = Arc::new(Sink::default());
            let worker = start_sink(Arc::clone(&sink)).await;
            let echod = spawn_echod(
                &cli.echod,
                "http://localhost:8001",
                cli.retry_timeout,
                &cli.logs,
            );
            let client = Client::new();
            client.wait_ready(&echod).await;
            let model = Resonate {
                retry_timeout: cli.retry_timeout,
                fire_within: 5_000,
            };
            let mut d = Driver {
                client,
                echod,
                sink,
                worker,
                model,
                quiet_ms: cli.quiet_ms,
                corr: 0,
            };
            let mut choices = Choices::random(seed).learning(&tried);
            let trace = d.run(cli.requests, guided, &mut choices).await;
            if cli.trace {
                eprintln!(
                    "[run seed={seed} guided={guided}]\n{}",
                    show(&trace, trace.len())
                );
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
                            format!(
                                "{} ← {res:?}",
                                req.map(|r| short_req(r)).unwrap_or_default()
                            )
                        }
                        Some(Event::Receive { msg }) => format!("⇐ {msg:?}"),
                        Some(Event::Clock { .. }) => "clock".to_string(),
                        Some(Event::Invoke { req, .. }) => format!("→ {}", short_req(req)),
                        None => "end".to_string(),
                    };
                    let e = classes.entry(class).or_insert_with(|| {
                        (
                            0,
                            format!("seed {seed}: {}\n{}", v.reason, show(&trace, v.index)),
                        )
                    });
                    e.0 += 1;
                }
                Outcome::Unknown(v) => {
                    unknown += 1;
                    eprintln!("unknown (seed {seed}): {v}");
                }
            }
            drop(d);
        }
        kos_total += ko;
        let covered = table.values().filter(|n| n[k] > 0).count();
        let mode = if guided { "guided" } else { "random" };
        let first = first_ko.map_or("-".to_string(), |s| s.to_string());
        println!(
            "{mode:<8} {ok:>4} {ko:>4} {unknown:>8} {:>9} {first:>14}",
            format!("{covered}/{}", MARKS.len())
        );
        for (class, (n, example)) in classes {
            examples.push(format!("[{mode}] {n} run(s) stop at: {class}\n{example}"));
        }
    }
    println!(
        "\n{:<50} {:>7} {:>7}",
        "mark (runs that reached it)", "random", "guided"
    );
    for (m, [a, b]) in &table {
        println!("{m:<50} {a:>7} {b:>7}");
    }
    for e in &examples {
        println!("\n{e}");
    }
    if kos_total > 0 {
        std::process::exit(1);
    }
}

fn short_req(r: &Request) -> String {
    let s = format!("{r:?}");
    s.split(|c: char| c == '(' || c == ' ')
        .next()
        .unwrap_or(&s)
        .to_string()
}
