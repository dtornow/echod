// Times porcupine-rs on Porcupine's histories, the check only (parsing is done
// first), repeated for about 200ms per history.
#[path = "../test_data/jepsen_loader.rs"]
#[allow(dead_code)]
mod jepsen_loader;
#[path = "../test_data/kv_loader.rs"]
#[allow(dead_code)]
mod kv_loader;

use std::collections::HashMap;
use std::time::{Duration, Instant};

fn time(mut f: impl FnMut() -> bool) -> (bool, Duration) {
    let t0 = Instant::now();
    let mut runs = 0;
    let mut r = false;
    while runs == 0 || t0.elapsed() < Duration::from_millis(200) {
        r = f();
        runs += 1;
    }
    (r, t0.elapsed() / runs)
}

fn main() {
    let expected: HashMap<u32, bool> = std::fs::read_to_string("../../expected_etcd.txt")
        .unwrap()
        .lines()
        .map(|l| {
            let (n, v) = l.split_once(' ').unwrap();
            (n.parse().unwrap(), v == "true")
        })
        .collect();
    let mut total = Duration::ZERO;
    let mut wrong = 0;
    for n in 0..=102u32 {
        let events = jepsen_loader::load_jepsen_log(n);
        let (r, dt) = time(|| porcupine_rs::check_events(&events));
        let ok = r;
        let mark = match expected.get(&n) {
            Some(w) if *w == ok => "",
            Some(_) => {
                wrong += 1;
                "  MISMATCH"
            }
            None => "  (no expected verdict)",
        };
        total += dt;
        println!("etcd_{n:03}  events={:<5} {:<5} {:>10.3}ms{mark}", events.len(), r, dt.as_secs_f64() * 1e3);
    }
    println!("etcd: 103 histories, {:.1}ms in total, {wrong} verdicts differ", total.as_secs_f64() * 1e3);
    for (name, want) in [("c01-ok", true), ("c01-bad", false), ("c10-ok", true), ("c10-bad", false), ("c50-ok", true), ("c50-bad", false)] {
        let events = kv_loader::load_kv_log(name);
        let (r, dt) = time(|| porcupine_rs::check_events(&events));
        let mark = if r == want { "" } else { "  MISMATCH" };
        println!("kv {name:<8} events={:<5} {:<5} {:>10.3}ms{mark}", events.len(), r, dt.as_secs_f64() * 1e3);
    }
}
