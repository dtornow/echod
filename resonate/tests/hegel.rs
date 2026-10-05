//! The fuzz driver (`common/driver.rs`) with choices from Hegel: every
//! decision, which request a client sends and which move the server makes, is
//! a draw Hegel records. When a run fails, Hegel shrinks it: it deletes
//! requests (each is a span), lowers values, and replays until the failure is
//! as small as it gets, and the oracle that says it fails is the checker.
//!
//! `HEGEL_STATISTICS=1 cargo test --release -p resonate --test hegel -- --nocapture`
//! shows how often each mark was reached.

#[path = "common/driver.rs"]
mod driver;

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use accordant::Time;
use driver::{run, show, Bug, Choices, Outcome, Server};
use hegel::generators as gs;
use hegel::{Settings, TestCase};
use resonate::*;

fn below(tc: &TestCase, n: usize) -> usize {
    tc.draw_silent(gs::integers::<usize>().min_value(0).max_value(n - 1))
}

/// How a guided run picks among the model's suggestions. Every policy is a
/// function of the run's own draws, so Hegel can replay and shrink it: a count
/// kept across runs (as `examples/fuzz.rs` keeps) would make a replay diverge.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Guide {
    /// Any suggestion, uniformly: reasons with many suggestions (one per
    /// promise) crowd out the rare ones (one per held task).
    Uniform,
    /// A reason first, uniformly over the distinct reasons; then a suggestion
    /// with that reason.
    ByReason,
    /// A reason first, among those taken least so far in this run.
    LeastTried,
}

/// One request: a span of its own, so the shrinker can delete it whole. The
/// reason it was suggested for, if it was.
#[hegel::composite]
fn request(
    tc: &TestCase,
    clock: Time,
    suggestions: Vec<(Request, &'static str)>,
    guide: Option<Guide>,
    taken: BTreeMap<&'static str, usize>,
) -> (Request, Option<&'static str>) {
    if let Some(guide) = guide {
        if !suggestions.is_empty() && tc.draw_silent(gs::weighted_booleans(0.75)) {
            let mut reasons: Vec<&'static str> = suggestions.iter().map(|(_, why)| *why).collect();
            reasons.sort();
            reasons.dedup();
            if guide == Guide::LeastTried {
                let count = |why: &&str| taken.get(why).copied().unwrap_or(0);
                let least = reasons.iter().map(count).min().expect("not empty");
                reasons.retain(|why| count(why) == least);
            }
            let pool: Vec<&Request> = match guide {
                Guide::Uniform => suggestions.iter().map(|(r, _)| r).collect(),
                _ => {
                    let why = reasons[below(tc, reasons.len())];
                    suggestions.iter().filter(|(_, w)| *w == why).map(|(r, _)| r).collect()
                }
            };
            let req = pool[below(tc, pool.len())].clone();
            let why = suggestions.iter().find(|(r, _)| *r == req).map(|(_, w)| *w);
            return (req, why);
        }
    }
    (arbitrary(&mut |n| below(tc, n), clock), None)
}

struct FromHegel<'t> {
    tc: &'t TestCase,
    guide: Option<Guide>,
    /// How often each reason was taken in this run.
    taken: RefCell<BTreeMap<&'static str, usize>>,
}

impl Choices for FromHegel<'_> {
    fn pick(&self, n: usize) -> usize {
        below(self.tc, n)
    }

    fn request(&self, clock: Time, suggestions: &[(Request, &'static str)]) -> Request {
        let taken = self.taken.borrow().clone();
        let (req, why) = self.tc.draw_silent(request(clock, suggestions.to_vec(), self.guide, taken));
        if let Some(why) = why {
            *self.taken.borrow_mut().entry(why).or_default() += 1;
        }
        req
    }
}

/// The guide the tests use.
const GUIDE: Guide = Guide::Uniform;

/// One test case: guided or not, and how many requests, are draws too.
fn fuzz(tc: &TestCase, bug: Bug) -> Outcome {
    fuzz_with(tc, bug, GUIDE)
}

fn fuzz_with(tc: &TestCase, bug: Bug, guide: Guide) -> Outcome {
    let guide = tc.draw_silent(gs::booleans()).then_some(guide);
    let steps = tc.draw_silent(gs::integers::<usize>().min_value(1).max_value(40));
    let choices = FromHegel { tc, guide, taken: RefCell::default() };
    let outcome = run(&Server { bug }, &choices, steps, bug == Bug::None);
    if let Outcome::Ok(marks) = &outcome {
        for m in marks {
            tc.event(m);
        }
        // Steer toward runs that reach many behaviors.
        tc.target(marks.len() as f64);
    }
    outcome
}

/// Every run against the spec itself is valid (the simulator only makes moves
/// the replay behind `certify` allows), so every checker must accept it.
#[hegel::test(test_cases = 200, database = None)]
fn the_checkers_accept_every_run_of_the_spec(tc: TestCase) {
    match fuzz(&tc, Bug::None) {
        Outcome::Ok(_) => {}
        Outcome::Ko(v, t) => panic!("a valid trace rejected: {v}\n{}", show(&t, v.index)),
        Outcome::Unknown(v, t) => panic!("the checker gave up: {v}\n{}", show(&t, v.index)),
    }
}

/// What a search found: the test case it first failed on, and the trace it
/// shrank the failure to.
struct Found {
    first: usize,
    events: usize,
    trace: String,
}

/// Runs Hegel, from `seed`, against a server with `bug` planted.
fn search(bug: Bug, seed: u64, guide: Guide) -> Option<Found> {
    #[derive(Default)]
    struct Seen {
        cases: usize,
        first: Option<usize>,
        // The last failure Hegel runs: after shrinking, the minimal one.
        last: Option<(usize, String)>,
    }
    let seen: Arc<Mutex<Seen>> = Arc::default();
    let log = seen.clone();
    let settings = Settings::new().test_cases(1000).database(None).print_blob(false).seed(Some(seed));
    let failed = std::panic::catch_unwind(|| {
        hegel::Hegel::new(move |tc: TestCase| {
            let outcome = fuzz_with(&tc, bug, guide);
            let mut s = log.lock().unwrap();
            s.cases += 1;
            if let Outcome::Ko(v, t) = outcome {
                let n = s.cases;
                s.first.get_or_insert(n);
                s.last = Some((v.index + 1, format!("{}\n{}", v.reason, show(&t, v.index))));
                drop(s);
                panic!("{bug:?}: the checker rejects the trace");
            }
        })
        .settings(settings)
        .run()
    });
    let mut s = seen.lock().unwrap();
    failed.is_err().then(|| {
        let (events, trace) = s.last.take().expect("a failing trace");
        Found { first: s.first.expect("a first failure"), events, trace }
    })
}

/// Searches are deterministic for a seed; these seeds find the bug in 1000
/// test cases (`how_often_hegel_finds_each_bug` measures the rest).
fn find(bug: Bug, seed: u64) -> (usize, String) {
    let f = search(bug, seed, GUIDE).unwrap_or_else(|| panic!("Hegel did not find {bug:?} from seed {seed}"));
    (f.events, f.trace)
}

/// How often a search finds each bug, over seeds: `cargo test --release -p
/// resonate --test hegel -- --ignored --nocapture`.
#[test]
#[ignore]
fn how_often_hegel_finds_each_bug() {
    let guides: Vec<Guide> = match std::env::var("GUIDE").as_deref() {
        Ok("uniform") => vec![Guide::Uniform],
        Ok("by-reason") => vec![Guide::ByReason],
        Ok("least-tried") => vec![Guide::LeastTried],
        _ => vec![Guide::Uniform, Guide::ByReason, Guide::LeastTried],
    };
    for bug in [Bug::StaleFence, Bug::LeaseForever] {
        for &guide in &guides {
            let found: Vec<Option<Found>> = (1..=20).map(|seed| search(bug, seed, guide)).collect();
            let firsts: Vec<usize> = found.iter().flatten().map(|f| f.first).collect();
            let mut sorted = firsts.clone();
            sorted.sort();
            let median = sorted.get(sorted.len() / 2).map_or("-".into(), |m| m.to_string());
            let seeds: Vec<usize> = found.iter().enumerate().filter(|(_, f)| f.is_some()).map(|(i, _)| i + 1).collect();
            println!(
                "{bug:?} {guide:?}: found from {}/20 seeds {seeds:?}, first failing case: median {median}, all {firsts:?}",
                seeds.len()
            );
        }
    }
}

#[test]
fn hegel_finds_and_shrinks_a_stale_fence() {
    let (n, trace) = find(Bug::StaleFence, 2);
    println!("stale fence, shrunk to {n} events:\n{trace}");
    assert!(n <= 6, "not shrunk: {n} events\n{trace}");
}

#[test]
fn hegel_finds_and_shrinks_a_lease_that_never_expires() {
    let (n, trace) = find(Bug::LeaseForever, 11);
    println!("lease never expires, shrunk to {n} events:\n{trace}");
    assert!(n <= 20, "not shrunk: {n} events\n{trace}");
}
