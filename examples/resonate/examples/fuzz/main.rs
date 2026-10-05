//! Fuzzing Resonate with `accordant::drive`: drive a server (the spec, or the
//! spec with a bug planted), record what happens, and check the recorded trace
//! against the spec. Coverage is the marks along the execution that explains
//! each accepted trace.
//!
//! ```text
//! cargo run --release -p resonate --example fuzz -- [runs] [--requests N] [--bug stale-fence|lease-forever]
//! CROSS=1 ...   # also check every trace with the partitioned and depth-first checkers
//! ```

mod driver;

use std::collections::BTreeMap;

use accordant::{drive, Choices, Drive, Tried};
use driver::{check, show, Bug, Outcome, Server};
use resonate::*;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |name: &str| args.iter().position(|a| a == name).map(|i| args[i + 1].clone());
    let runs: u64 = args.first().and_then(|a| a.parse().ok()).unwrap_or(200);
    let requests: usize = flag("--requests").map_or(30, |s| s.parse().expect("--requests N"));
    let bug = flag("--bug").map_or(Bug::None, |b| Bug::parse(&b));
    let cross = bug == Bug::None && std::env::var("CROSS").is_ok();
    let server = Server { bug };
    let mut table: BTreeMap<&str, [usize; 2]> = MARKS.iter().map(|m| (*m, [0, 0])).collect();
    println!("{runs} runs of {requests} requests each, server bug: {bug:?}\n");
    println!("{:<8} {:>4} {:>4} {:>8} {:>9} {:>13}", "mode", "ok", "ko", "unknown", "marks", "first ko (run)");
    for (k, guided) in [false, true].into_iter().enumerate() {
        let cfg = Drive { requests, concurrency: 3, guided };
        let (mut ok, mut ko, mut unknown, mut first_ko) = (0, 0, 0, None);
        let mut example = None;
        // Across runs: which suggestions were taken least, so rare ones get their turn.
        let tried = Tried::default();
        for seed in 1..=runs {
            let run = drive(&server, resonate::Server::default(), &cfg, Choices::random(seed).learning(&tried));
            match check(&run.trace, cross) {
                Outcome::Ok(seen) => {
                    ok += 1;
                    for m in seen {
                        table.get_mut(m).expect("a declared mark")[k] += 1;
                    }
                }
                Outcome::Ko(v) => {
                    ko += 1;
                    first_ko.get_or_insert(seed);
                    example.get_or_insert(format!(
                        "{} ({} choices recorded)\n{}",
                        v.reason,
                        run.choices.len(),
                        show(&run.trace, v.index)
                    ));
                }
                Outcome::Unknown(v) => {
                    unknown += 1;
                    eprintln!("unknown (seed {seed}): {v}\n{}", show(&run.trace, v.index));
                }
            }
        }
        let covered = table.values().filter(|n| n[k] > 0).count();
        let mode = if guided { "guided" } else { "random" };
        let first = first_ko.map_or("-".to_string(), |s| s.to_string());
        println!("{mode:<8} {ok:>4} {ko:>4} {unknown:>8} {:>9} {first:>13}", format!("{covered}/{}", MARKS.len()));
        if let Some(v) = example {
            println!("\nfirst KO ({mode}), up to the event no execution explains:\n{v}");
        }
    }
    println!("\n{:<45} {:>7} {:>7}", "mark (runs that reached it)", "random", "guided");
    for (m, [a, b]) in &table {
        println!("{m:<45} {a:>7} {b:>7}");
    }
}
