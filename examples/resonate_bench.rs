//! The workloads of resonate-specification `valid/lean/experiments.lean`, on the
//! Rust checker: `length` (k workflows back to back) and `fanout` (n promises
//! armed to expire before one final read). Responses are recorded first from the
//! model itself, as Lean's `recordFrom` does, and only the check is timed.
//!
//! cargo run --release --example resonate_bench -- [length|fanout|fanout-nocone] n...
//!
//! `-flat` and `-certified` variants (`length-flat`, `length-certified`) check in
//! one factor, without partitions; `-certified` also backs the verdict with a
//! certificate.

#[path = "../tests/resonate/spec.rs"]
#[allow(dead_code)]
mod spec;

use std::time::Instant;

use accordant::{Checker, Config, Event, Time};
use spec::*;

const FAR: Time = 1_000_000_000;

fn create(id: &str, timeout_at: Time, external: bool, target: bool) -> Request {
    Request::CreatePromise(Create { id: id.into(), timeout_at, data: None, external, target, timer: false })
}

/// One workflow on a fresh pair, as Lean's `workflow i t0 t1`.
fn workflow(i: u64, t0: Time, t1: Time) -> Vec<(Request, Time)> {
    let (a, x) = (format!("o:a{i}"), format!("o:x{i}"));
    vec![
        (create(&a, FAR, true, false), t0),
        (create(&x, FAR, false, true), t0),
        (Request::AcquireTask { id: x.clone(), version: 0, pid: "p".into(), ttl: 50 }, t0),
        (Request::SuspendTask { id: x.clone(), version: 1, awaited: vec![a.clone()] }, t0),
        (Request::SettlePromise(Settle { id: a, state: "resolved".into(), data: None }), t1),
        // the resume is hidden: the checker has to find it
        (Request::AcquireTask { id: x.clone(), version: 1, pid: "p".into(), ttl: 50 }, t1),
        (Request::FulfillTask { id: x, version: 2, state: "resolved".into(), data: None }, t1),
    ]
}

fn length(k: u64) -> Vec<(Request, Time)> {
    (0..k).flat_map(|i| workflow(i, 10 + i * 10, 15 + i * 10)).collect()
}

fn fanout(n: u64) -> Vec<(Request, Time)> {
    let mut s: Vec<_> = (0..n).map(|i| (create(&format!("o:a{i}"), 20 + i, true, false), 10)).collect();
    s.push((Request::GetPromise("o:a0".into()), 500));
    s
}

/// Runs the script against the model, taking a successful answer where the
/// model allows one: the trace an honest server would produce.
fn record(script: &[(Request, Time)]) -> Vec<Event<Request, Response, Dispatch>> {
    let mut c = Checker::with_partitions(Resonate, Server::default(), Config::default());
    let mut trace = Vec::new();
    let mut now = 0;
    let mut call = 0u64;
    let mut ops = Vec::new();
    for (op, t) in script {
        if *t > now {
            // The driver moves the server's clock first.
            ops.push(Request::AdvanceClock(*t));
            now = *t;
        }
        ops.push(op.clone());
    }
    for op in ops {
        let allowed = c.allowed(&op);
        let res = allowed.iter().find(|r| r.status() == 200).unwrap_or(&allowed[0]).clone();
        c.call(call, op.clone(), res.clone()).unwrap();
        trace.push(Event::Invoke { call, req: op });
        trace.push(Event::Return { call, res });
        call += 1;
    }
    trace
}

#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Partitioned,
    Flat,
    Certified,
}

fn check(trace: &[Event<Request, Response, Dispatch>], footprints: bool, mode: Mode) -> (bool, std::time::Duration, accordant::Stats) {
    let t0 = Instant::now();
    let cfg = Config { footprints, max_explore: 10_000_000, max_width: 1 << 20, ..Config::default() };
    if mode == Mode::Partitioned {
        let mut c = Checker::with_partitions(Resonate, Server::default(), cfg);
        let ok = c.check(trace.iter().cloned()).is_ok();
        return (ok, t0.elapsed(), c.stats.clone());
    }
    let mut c = Checker::with_footprints(Resonate, Server::default(), cfg);
    let ok = match mode {
        Mode::Certified => c.check_certified(trace.iter().cloned()).map_err(|v| eprintln!("{v}")).is_ok(),
        _ => c.check(trace.iter().cloned()).is_ok(),
    };
    (ok, t0.elapsed(), c.stats.clone())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (kind, sizes) = args.split_first().expect("usage: [length|fanout|fanout-nocone] n...");
    for n in sizes.iter().map(|s| s.parse::<u64>().unwrap()) {
        let (base, mode) = match kind.split_once('-') {
            Some((b, "flat")) => (b, Mode::Flat),
            Some((b, "certified")) => (b, Mode::Certified),
            _ => (kind.as_str(), Mode::Partitioned),
        };
        let (script, footprints) = match base {
            "length" => (length(n), true),
            "fanout" => (fanout(n), true),
            "fanout-nocone" => (fanout(n), false),
            _ => panic!("unknown workload {kind}"),
        };
        let trace = record(&script);
        let (ok, dt, st) = check(&trace, footprints, mode);
        println!(
            "{kind:<14} n={n:<6} events={:<6} {}  {:>9.3}ms  explored={} width={}",
            script.len(),
            if ok { "ADMISSIBLE" } else { "REFUTED" },
            dt.as_secs_f64() * 1e3,
            st.explored,
            st.max_width
        );
    }
}

