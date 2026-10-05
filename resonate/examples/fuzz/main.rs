//! A fuzz driver for Resonate, with the spec as server, oracle and guide, and
//! choices from a seeded generator.
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

mod driver;

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap};

use accordant::{Marks, Time};
use driver::{run, show, Bug, Choices, Outcome, Server};
use resonate::*;

struct Seeded<'t> {
    rng: Cell<u64>,
    guided: bool,
    /// How often each suggestion's reason was taken, across runs.
    tried: &'t RefCell<HashMap<&'static str, usize>>,
}

impl Choices for Seeded<'_> {
    fn pick(&self, n: usize) -> usize {
        let mut r = self.rng.get();
        r ^= r << 13;
        r ^= r >> 7;
        r ^= r << 17;
        self.rng.set(r);
        (r % n as u64) as usize
    }

    fn request(&self, clock: Time, suggestions: &[(Request, &'static str)]) -> Request {
        if self.guided && !suggestions.is_empty() && self.pick(4) != 0 {
            // The suggestion whose reason was taken least.
            let mut tried = self.tried.borrow_mut();
            let count = |why: &&str| tried.get(why).copied().unwrap_or(0);
            let least = suggestions.iter().map(|(_, why)| count(why)).min().expect("not empty");
            let fewest: Vec<_> = suggestions.iter().filter(|(_, why)| count(why) == least).collect();
            let (req, why) = fewest[self.pick(fewest.len())].clone();
            *tried.entry(why).or_default() += 1;
            return req;
        }
        arbitrary(&mut |n| self.pick(n), clock)
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |name: &str| args.iter().position(|a| a == name).map(|i| args[i + 1].clone());
    let runs: u64 = args.first().and_then(|a| a.parse().ok()).unwrap_or(200);
    let steps: usize = flag("--steps").map_or(30, |s| s.parse().expect("--steps N"));
    let bug = flag("--bug").map_or(Bug::None, |b| Bug::parse(&b));
    let cross = bug == Bug::None && std::env::var("CROSS").is_ok();
    let server = Server { bug };
    let all = Resonate.all_marks();
    let mut table: BTreeMap<&str, [usize; 2]> = all.iter().map(|m| (*m, [0, 0])).collect();
    println!("{runs} runs of {steps} requests each, server bug: {bug:?}\n");
    println!("{:<8} {:>4} {:>4} {:>8} {:>9} {:>13}", "mode", "ok", "ko", "unknown", "marks", "first ko (run)");
    for (k, guided) in [false, true].into_iter().enumerate() {
        let (mut ok, mut ko, mut unknown, mut first_ko) = (0, 0, 0, None);
        let mut example = None;
        let tried = RefCell::new(HashMap::new());
        for seed in 1..=runs {
            let choices = Seeded { rng: Cell::new(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1), guided, tried: &tried };
            match run(&server, &choices, steps, cross) {
                Outcome::Ok(seen) => {
                    ok += 1;
                    for m in seen {
                        table.get_mut(m).expect("a declared mark")[k] += 1;
                    }
                }
                Outcome::Ko(v, t) => {
                    ko += 1;
                    first_ko.get_or_insert(seed);
                    example.get_or_insert(format!("{}\n{}", v.reason, show(&t, v.index)));
                }
                Outcome::Unknown(v, t) => {
                    unknown += 1;
                    eprintln!("unknown: {v}\n{}", show(&t, v.index));
                }
            }
        }
        let covered = table.values().filter(|n| n[k] > 0).count();
        let mode = if guided { "guided" } else { "random" };
        let first = first_ko.map_or("-".to_string(), |s| s.to_string());
        println!("{mode:<8} {ok:>4} {ko:>4} {unknown:>8} {:>9} {first:>13}", format!("{covered}/{}", all.len()));
        if let Some(v) = example {
            println!("\nfirst KO ({mode}), up to the event no execution explains:\n{v}");
        }
    }
    println!("\n{:<40} {:>7} {:>7}", "mark (runs that reached it)", "random", "guided");
    for (m, [a, b]) in &table {
        println!("{m:<40} {a:>7} {b:>7}");
    }
}
