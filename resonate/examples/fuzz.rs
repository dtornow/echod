//! A fuzz driver for Resonate, with the spec as server, oracle and guide.
//!
//! * Server: `accordant::Sim` runs a model as a server, choosing at random
//!   among everything the model allows (outcomes, when work runs, delivery
//!   order). Run the spec itself, or the spec with a bug planted.
//! * Oracle: a checker follows what clients observe and answers OK, KO or
//!   UNKNOWN.
//! * Guide: in `guided` mode, most requests come from the model's suggestions
//!   for the states the checker thinks the server may be in (fence at the held
//!   version, clock to a lease end, ...), the least tried reason first; the
//!   rest are random.
//! * Each run ends with the server idle and a client reading every object, so
//!   work the spec lets the server put off has to have happened.
//! * Coverage: each accepted run comes with a certificate, an execution that
//!   explains it; the marks along that execution are what the run covered.
//!
//! ```text
//! cargo run --release -p resonate --example fuzz -- [runs] [--steps N] [--bug stale-fence|lease-forever]
//! CROSS=1 ...   # also check every trace with the partitioned and depth-first checkers
//! ```

use std::collections::{BTreeMap, HashMap};

use accordant::{marks, CallId, Checker, Config, Event, ExternalOutcome, InternalOutcome, Keyed, Marks, Model, Sim, Time, Verdict};
use resonate::*;

/// The spec with a bug planted, or not.
struct Server {
    bug: Bug,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Bug {
    None,
    /// A fence at a stale version goes through, as if it held the task.
    StaleFence,
    /// A lease never expires: an abandoned task is never handed out again.
    LeaseForever,
}

impl Model for Server {
    type State = resonate::Server;
    type External = Request;
    type Response = Response;
    type Internal = Internal;
    type Dispatch = Dispatch;

    fn external(&self, op: &Request, s: &Self::State) -> Vec<ExternalOutcome<Self>> {
        let op = match (self.bug, op) {
            (Bug::StaleFence, Request::FenceTask { id, version: _, action }) => match s.tasks.get(id) {
                Some(t) => Request::FenceTask { id: id.clone(), version: t.version, action: action.clone() },
                None => op.clone(),
            },
            _ => op.clone(),
        };
        lift(Model::external(&Resonate, &op, s))
    }

    fn internal(&self, ids: &Internal, s: &Self::State) -> Vec<InternalOutcome<Self>> {
        let outs = Model::internal(&Resonate, ids, s);
        if self.bug == Bug::LeaseForever && outs.iter().any(|o| !o.send.is_empty()) {
            return vec![InternalOutcome { next: s.clone(), spawn: Vec::new(), send: Vec::new() }];
        }
        outs.into_iter().map(|o| InternalOutcome { next: o.next, spawn: o.spawn, send: o.send }).collect()
    }

    fn now(&self, s: &Self::State) -> Time {
        s.now
    }
}

fn lift(outs: Vec<ExternalOutcome<Resonate>>) -> Vec<ExternalOutcome<Server>> {
    outs.into_iter().map(|o| ExternalOutcome { next: o.next, res: o.res, spawn: o.spawn, send: o.send }).collect()
}

struct Rng(u64);

impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n.max(1) as u64) as usize
    }

    fn pick<'a, T>(&mut self, v: &'a [T]) -> &'a T {
        &v[self.next(v.len())]
    }
}

enum Outcome {
    Ok(std::collections::BTreeSet<&'static str>),
    Ko(String),
    Unknown(String),
}

/// One run: a client sends `steps` requests, at most three in flight, while the
/// server steps at random; the checker follows.
fn run(server: &Server, guided: bool, seed: u64, steps: usize, tried: &mut HashMap<&'static str, usize>) -> Outcome {
    let mut r = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let mut sim = Sim::new(server, resonate::Server::default(), seed);
    let mut c = Checker::with_footprints(Resonate, resonate::Server::default(), Config { certify: true, ..Config::default() });
    let mut clock: Time = 0;
    let mut call: CallId = 0;
    let mut events: Vec<Event<Request, Response, Dispatch>> = Vec::new();
    let mut observe = |c: &mut Checker<Keyed<Resonate>>, e: Event<Request, Response, Dispatch>| -> Result<(), accordant::Violation> {
        events.push(e.clone());
        c.observe(e)
    };
    let mut sent = 0;
    let verdict = (|| {
        while sent < steps || sim.open_calls() > 0 {
            if sent < steps && sim.open_calls() < 3 && r.next(2) == 0 {
                let req = if guided && r.next(4) != 0 {
                    // The suggestion whose reason was tried least, across runs.
                    let s = c.suggestions(8);
                    let least = s.iter().map(|(_, why)| tried.get(why).copied().unwrap_or(0)).min();
                    let s: Vec<_> = s.into_iter().filter(|(_, why)| Some(tried.get(why).copied().unwrap_or(0)) == least).collect();
                    if s.is_empty() {
                        arbitrary(&mut |n| r.next(n), clock)
                    } else {
                        let (req, why) = r.pick(&s).clone();
                        *tried.entry(why).or_default() += 1;
                        req
                    }
                } else {
                    arbitrary(&mut |n| r.next(n), clock)
                };
                if let Request::AdvanceClock(t) = req {
                    clock = clock.max(t);
                }
                call += 1;
                sent += 1;
                let e = sim.invoke(call, req);
                observe(&mut c, e)?;
            } else if let Some(e) = sim.step() {
                observe(&mut c, e)?;
            } else if sent >= steps {
                break;
            }
        }
        for e in sim.settle() {
            observe(&mut c, e)?;
        }
        // The server goes idle; then a client reads everything. A step the spec
        // may put off (a lease expiring) can't be put off past this.
        sim.quiesce();
        c.assert_idle()?;
        for id in IDS {
            for req in [Request::GetTask(id.to_string()), Request::GetPromise(id.to_string())] {
                call += 1;
                let e = sim.invoke(call, req);
                observe(&mut c, e)?;
                for e in sim.settle() {
                    observe(&mut c, e)?;
                }
            }
        }
        c.certified()
    })();
    if std::env::var("DUMP").is_ok_and(|d| d == seed.to_string()) {
        for (i, e) in events.iter().enumerate() {
            eprintln!("{i}: {e:?}");
        }
        for (name, cfg) in [
            ("plain", Config { footprints: false, subsume: false, ..Config::default() }),
            ("footprints", Config { subsume: false, ..Config::default() }),
            ("subsume", Config { footprints: false, ..Config::default() }),
        ] {
            let mut p = Checker::new(Resonate, resonate::Server::default(), cfg);
            eprintln!("{name}: {:?}", p.check(events.clone()).map(|_| ()).map_err(|v| v.index));
        }
        let mut f = Checker::with_footprints(Resonate, resonate::Server::default(), Config::default());
        eprintln!("keyed: {:?}", f.check(events.clone()).map(|_| ()).map_err(|v| v.index));
        let mut d = Checker::with_footprints(Resonate, resonate::Server::default(), Config::default());
        eprintln!("dfs: {:?}", d.check_complete(&events).map(|_| ()).map_err(|v| v.index));
    }
    // With no bug, every trace is valid: the simulator only makes moves the
    // replay behind `certify` allows. Every checker mode must accept it.
    if server.bug == Bug::None && std::env::var("CROSS").is_ok() {
        let mut g = Checker::with_partitions(Resonate, resonate::Server::default(), Config::default());
        let mut d = Checker::with_footprints(Resonate, resonate::Server::default(), Config::default());
        let (g, d) = (g.check(events.clone()).map(|_| ()), d.check_complete(&events).map(|_| ()));
        for (name, r) in [("partitioned", g), ("dfs", d)] {
            if let Err(v) = r {
                return Outcome::Ko(format!("{name} rejects a valid trace (seed {seed}): {v}"));
            }
        }
    }
    match Verdict::from(verdict) {
        Verdict::Ok(moves) => Outcome::Ok(marks(&Resonate, resonate::Server::default(), moves).expect("the certificate replays")),
        Verdict::Ko(v) => Outcome::Ko(format!("{v}")),
        Verdict::Unknown(v) => Outcome::Unknown(format!("{v}")),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |name: &str| args.iter().position(|a| a == name).map(|i| args[i + 1].clone());
    let runs: u64 = args.first().and_then(|a| a.parse().ok()).unwrap_or(200);
    let steps: usize = flag("--steps").map_or(30, |s| s.parse().expect("--steps N"));
    let bug = match flag("--bug").as_deref() {
        None => Bug::None,
        Some("stale-fence") => Bug::StaleFence,
        Some("lease-forever") => Bug::LeaseForever,
        Some(b) => panic!("unknown bug {b}"),
    };
    let server = Server { bug };
    let all = Resonate.all_marks();
    let mut table: BTreeMap<&str, [usize; 2]> = all.iter().map(|m| (*m, [0, 0])).collect();
    println!("{runs} runs of {steps} requests each, server bug: {bug:?}\n");
    println!("{:<8} {:>4} {:>4} {:>8} {:>9} {:>13}", "mode", "ok", "ko", "unknown", "marks", "first ko (run)");
    for (k, guided) in [false, true].into_iter().enumerate() {
        let (mut ok, mut ko, mut unknown, mut first_ko) = (0, 0, 0, None);
        let mut example = None;
        let mut tried = HashMap::new();
        for seed in 1..=runs {
            match run(&server, guided, seed, steps, &mut tried) {
                Outcome::Ok(seen) => {
                    ok += 1;
                    for m in seen {
                        table.get_mut(m).expect("a declared mark")[k] += 1;
                    }
                }
                Outcome::Ko(v) => {
                    ko += 1;
                    first_ko.get_or_insert(seed);
                    example.get_or_insert(v);
                }
                Outcome::Unknown(v) => {
                    unknown += 1;
                    eprintln!("unknown: {v}");
                }
            }
        }
        let covered = table.values().filter(|n| n[k] > 0).count();
        let mode = if guided { "guided" } else { "random" };
        let first = first_ko.map_or("-".to_string(), |s| s.to_string());
        println!("{mode:<8} {ok:>4} {ko:>4} {unknown:>8} {:>9} {first:>13}", format!("{covered}/{}", all.len()));
        if let Some(v) = example {
            println!("         first KO: {}", v.lines().next().unwrap_or(""));
        }
    }
    println!("\n{:<40} {:>7} {:>7}", "mark (runs that reached it)", "random", "guided");
    for (m, [a, b]) in &table {
        println!("{m:<40} {a:>7} {b:>7}");
    }
}
