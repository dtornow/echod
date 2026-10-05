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

use std::sync::{Arc, Mutex};

use accordant::Time;
use driver::{run, show, Bug, Choices, Outcome, Server};
use hegel::generators as gs;
use hegel::{Settings, TestCase};
use resonate::*;

fn below(tc: &TestCase, n: usize) -> usize {
    tc.draw_silent(gs::integers::<usize>().min_value(0).max_value(n - 1))
}

/// One request: a span of its own, so the shrinker can delete it whole.
#[hegel::composite]
fn request(tc: &TestCase, clock: Time, suggestions: Vec<(Request, &'static str)>, guided: bool) -> Request {
    if guided && !suggestions.is_empty() && tc.draw_silent(gs::weighted_booleans(0.75)) {
        return suggestions[below(tc, suggestions.len())].0.clone();
    }
    arbitrary(&mut |n| below(tc, n), clock)
}

struct FromHegel<'t> {
    tc: &'t TestCase,
    guided: bool,
}

impl Choices for FromHegel<'_> {
    fn pick(&self, n: usize) -> usize {
        below(self.tc, n)
    }

    fn request(&self, clock: Time, suggestions: &[(Request, &'static str)]) -> Request {
        self.tc.draw_silent(request(clock, suggestions.to_vec(), self.guided))
    }
}

/// One test case: guided or not, and how many requests, are draws too.
fn fuzz(tc: &TestCase, bug: Bug) -> Outcome {
    let guided = tc.draw_silent(gs::booleans());
    let steps = tc.draw_silent(gs::integers::<usize>().min_value(1).max_value(40));
    let outcome = run(&Server { bug }, &FromHegel { tc, guided }, steps, bug == Bug::None);
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

/// Runs Hegel, from `seed`, against a server with `bug` planted; returns the
/// minimal trace it shrank the failure to, (events, trace), if it found one.
fn search(bug: Bug, seed: u64) -> Option<(usize, String)> {
    // The last failure Hegel runs: after shrinking, the minimal one.
    let minimal: Arc<Mutex<Option<(usize, String)>>> = Arc::default();
    let last = minimal.clone();
    let settings = Settings::new().test_cases(1000).database(None).print_blob(false).seed(Some(seed));
    let found = std::panic::catch_unwind(|| {
        hegel::Hegel::new(move |tc: TestCase| {
            if let Outcome::Ko(v, t) = fuzz(&tc, bug) {
                *last.lock().unwrap() = Some((v.index + 1, format!("{}\n{}", v.reason, show(&t, v.index))));
                panic!("{bug:?}: the checker rejects the trace");
            }
        })
        .settings(settings)
        .run()
    });
    let minimal = minimal.lock().unwrap().take();
    found.is_err().then(|| minimal.expect("a failing trace"))
}

/// Searches are deterministic for a seed; these seeds find the bug in 1000
/// test cases (`how_often_hegel_finds_each_bug` measures the rest).
fn find(bug: Bug, seed: u64) -> (usize, String) {
    search(bug, seed).unwrap_or_else(|| panic!("Hegel did not find {bug:?} from seed {seed}"))
}

/// How often a search finds each bug, over seeds: `cargo test --release -p
/// resonate --test hegel -- --ignored --nocapture`.
#[test]
#[ignore]
fn how_often_hegel_finds_each_bug() {
    for bug in [Bug::StaleFence, Bug::LeaseForever] {
        let found: Vec<_> = (1..=20).map(|seed| search(bug, seed).map(|(n, _)| n)).collect();
        let hits: Vec<(usize, usize)> = found.iter().enumerate().filter_map(|(i, n)| n.map(|n| (i + 1, n))).collect();
        println!("{bug:?}: found from {}/20 seeds, (seed, events): {hits:?}", hits.len());
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
