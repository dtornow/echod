//! Every trace the simulator produces is valid: it only makes moves the replay
//! behind `certify` allows. So every checker mode must accept it, and the
//! certificate the checker finds must replay. This found three ways the
//! checker used to reject valid traces:
//!
//! * a call in flight that reads the clock, while the clock moves (footprints);
//! * a settle in flight whose resume explains a dispatch (footprints miss the
//!   work a step starts);
//! * a clock move broadcast to partitions that no factor held yet.

use accordant::{certify, drive, Checker, Choices, Config, Drive, Event};
use accordant::rover::resonate::*;

/// A run of the spec, driven at random and recorded.
fn trace(seed: u64, requests: usize) -> Vec<Event<Request, Response, Dispatch>> {
    drive(&Resonate::default(), Server::default(), &Drive { requests, concurrency: 3, guided: seed.is_multiple_of(2) }, Choices::random(seed)).trace
}

#[test]
fn every_mode_accepts_what_the_simulator_does() {
    for seed in 1..=300 {
        let t = trace(seed, 40);
        let ok = |r: Result<(), accordant::Violation>, mode: &str| {
            if let Err(v) = r {
                panic!("seed {seed}: {mode} rejects a valid trace: {v}");
            }
        };
        let mut c = Checker::new(Resonate::default(), Server::default(), Config::default());
        ok(c.check(t.clone()).map(|_| ()), "plain");
        let mut c = Checker::with_partitions(Resonate::default(), Server::default(), Config::default());
        ok(c.check(t.clone()).map(|_| ()), "partitioned");
        let mut c = Checker::with_footprints(Resonate::default(), Server::default(), Config::default());
        ok(c.check_complete(&t).map(|_| ()), "depth-first");
        let mut c = Checker::with_footprints(Resonate::default(), Server::default(), Config { certify: true, ..Config::default() });
        match c.check_certified(t.clone()) {
            Ok(cert) => assert_eq!(certify(&Resonate::default(), Server::default(), &t, &cert), Ok(()), "seed {seed}"),
            Err(v) => panic!("seed {seed}: certified rejects a valid trace: {v}"),
        }
    }
}
