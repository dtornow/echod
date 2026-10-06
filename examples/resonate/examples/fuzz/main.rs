//! Fuzzing Resonate with `accordant::drive`: drive a server (the spec, or the
//! spec with a bug planted), record what happens, and check the recorded trace
//! against the spec. Coverage is the marks along the execution that explains
//! each accepted trace.
//!
//! ```text
//! cargo run --release -p resonate --example fuzz -- [runs] [--requests N] [--bug stale-fence|lease-forever|stale-acquire] [--check complete|online] [--seed N] [--prove N]
//! CROSS=1 ...   # also check every trace with the partitioned and depth-first checkers
//! ```

mod driver;

use std::collections::BTreeMap;

use accordant::{drive, Choices, Drive, Tried};
use driver::{check, prove, show, Bug, Check, Outcome, Server};
use resonate::*;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |name: &str| args.iter().position(|a| a == name).map(|i| args[i + 1].clone());
    let runs: u64 = args.first().and_then(|a| a.parse().ok()).unwrap_or(200);
    let requests: usize = flag("--requests").map_or(30, |s| s.parse().expect("--requests N"));
    let bug = flag("--bug").map_or(Bug::None, |b| Bug::parse(&b));
    let cross = bug == Bug::None && std::env::var("CROSS").is_ok();
    // `--prove N`: prove each KO with `accordant::refute`, up to N configurations per event.
    let prove_limit: Option<usize> = flag("--prove").map(|n| n.parse().expect("--prove N"));
    let how = flag("--check").map_or(Check::Complete, |c| Check::parse(&c));
    let server = Server { bug };
    const MODES: [(&str, bool, bool); 4] = [("random", false, false), ("guided", true, false), ("informed", false, true), ("both", true, true)];
    let mut table: BTreeMap<&str, [usize; 4]> = MARKS.iter().map(|m| (*m, [0; 4])).collect();
    println!("{runs} runs of {requests} requests each, server bug: {bug:?}, checked {how:?}\n");
    println!("{:<8} {:>4} {:>4} {:>8} {:>9} {:>13}", "mode", "ok", "ko", "unknown", "marks", "first ko (run)");
    for (k, (mode, guided, informed)) in MODES.into_iter().enumerate() {
        let cfg = Drive { requests, concurrency: 3, guided, informed };
        let (mut ok, mut ko, mut unknown, mut first_ko) = (0, 0, 0, None);
        let (mut proved, mut proved_len, mut prove_time) = (0, Vec::new(), std::time::Duration::ZERO);
        let mut example = None;
        // Across runs: which suggestions were taken least, so rare ones get their turn.
        let tried = Tried::default();
        // `--seed N` checks run N alone. Earlier runs are still driven, unchecked:
        // what they tried steers run N's choices.
        let only: Option<u64> = flag("--seed").map(|s| s.parse().expect("--seed N"));
        for seed in 1..=only.unwrap_or(runs) {
            let run = drive(&server, resonate::Server::default(), &cfg, Choices::random(seed).learning(&tried));
            if only.is_some_and(|n| seed < n) {
                continue;
            }
            match check(&run.trace, how, cross) {
                Outcome::Ok(seen) => {
                    ok += 1;
                    for m in seen {
                        table.get_mut(m).expect("a declared mark")[k] += 1;
                    }
                }
                Outcome::Ko(v) => {
                    ko += 1;
                    if let Some(limit) = prove_limit {
                        let t = std::time::Instant::now();
                        match prove(&run.trace, limit) {
                            Some(n) => {
                                proved += 1;
                                proved_len.push(n);
                            }
                            None => eprintln!("not proved (seed {seed}): over {limit} configurations"),
                        }
                        prove_time += t.elapsed();
                    }
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
        let first = first_ko.map_or("-".to_string(), |s| s.to_string());
        println!("{mode:<8} {ok:>4} {ko:>4} {unknown:>8} {:>9} {first:>13}", format!("{covered}/{}", MARKS.len()));
        if prove_limit.is_some() && ko > 0 {
            proved_len.sort();
            let median = proved_len.get(proved_len.len() / 2).copied().unwrap_or(0);
            println!("         proved {proved}/{ko} KOs invalid (at event: median {median}, max {}), {:.1?}", proved_len.last().copied().unwrap_or(0), prove_time);
        }
        if let Some(v) = example {
            println!("\nfirst KO ({mode}), up to the event no execution explains:\n{v}");
        }
    }
    println!("\n{:<45} {:>7} {:>7} {:>8} {:>7}", "mark (runs that reached it)", "random", "guided", "informed", "both");
    for (m, [a, b, c, d]) in &table {
        println!("{m:<45} {a:>7} {b:>7} {c:>8} {d:>7}");
    }
}
