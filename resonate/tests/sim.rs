//! Every trace the simulator produces is valid: it only makes moves the replay
//! behind `certify` allows. So every checker mode must accept it, and the
//! certificate the checker finds must replay. This found three ways the
//! checker used to reject valid traces:
//!
//! * a call in flight that reads the clock, while the clock moves (footprints);
//! * a settle in flight whose resume explains a dispatch (footprints miss the
//!   work a step starts);
//! * a clock move broadcast to partitions that no factor held yet.

use accordant::{certify, CallId, Checker, Config, Event, Sim, Time};
use resonate::*;

fn trace(seed: u64, steps: usize) -> Vec<Event<Request, Response, Dispatch>> {
    let mut rng = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    let mut next = move |n: usize| {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        (rng % n as u64) as usize
    };
    let mut sim = Sim::new(&Resonate, Server::default(), seed);
    let (mut out, mut clock, mut call, mut sent): (Vec<_>, Time, CallId, usize) = (Vec::new(), 0, 0, 0);
    while sent < steps {
        if sim.open_calls() < 3 && next(2) == 0 {
            let req = arbitrary(&mut next, clock);
            if let Request::AdvanceClock(t) = req {
                clock = clock.max(t);
            }
            call += 1;
            sent += 1;
            out.push(sim.invoke(call, req));
        } else {
            out.extend(sim.step());
        }
    }
    out.extend(sim.settle());
    out
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
        let mut c = Checker::new(Resonate, Server::default(), Config::default());
        ok(c.check(t.clone()).map(|_| ()), "plain");
        let mut c = Checker::with_partitions(Resonate, Server::default(), Config::default());
        ok(c.check(t.clone()).map(|_| ()), "partitioned");
        let mut c = Checker::with_footprints(Resonate, Server::default(), Config::default());
        ok(c.check_complete(&t).map(|_| ()), "depth-first");
        let mut c = Checker::with_footprints(Resonate, Server::default(), Config { certify: true, ..Config::default() });
        match c.check_certified(t.clone()) {
            Ok(moves) => assert_eq!(certify(&Resonate, Server::default(), moves).expect("replays"), t, "seed {seed}"),
            Err(v) => panic!("seed {seed}: certified rejects a valid trace: {v}"),
        }
    }
}
