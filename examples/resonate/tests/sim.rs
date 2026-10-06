//! Every trace the simulator produces is valid: it only makes moves the replay
//! behind `certify` allows. So every checker mode must accept it, and the
//! certificate the checker finds must replay. This found four ways the
//! checker used to reject valid traces:
//!
//! * a call in flight that reads the clock, while the clock moves (footprints);
//! * a settle in flight whose resume explains a dispatch (footprints miss the
//!   work a step starts);
//! * a clock move broadcast to partitions that no factor held yet;
//! * a call in flight that reads the clock only once other work in flight on
//!   its keys has happened (an acquire after a release), while the clock moves.

use accordant::{certify, drive, Checker, Choices, Config, Drive, Event};
use resonate::*;

/// A run of the spec, driven at random and recorded.
fn trace(seed: u64, requests: usize) -> Vec<Event<Request, Response, Dispatch>> {
    drive(&Resonate, Server::default(), &Drive { requests, concurrency: 3, guided: seed.is_multiple_of(2), informed: seed % 3 == 0 }, Choices::random(seed)).trace
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
            Ok(cert) => assert_eq!(certify(&Resonate, Server::default(), &t, &cert), Ok(()), "seed {seed}"),
            Err(v) => panic!("seed {seed}: certified rejects a valid trace: {v}"),
        }
    }
}

/// A task is held; a release and an acquire of it are in flight while the
/// clock moves past the lease the acquire would take. Taking effect in that
/// order before the move, they lease the task until 10, the move reclaims it,
/// and both dispatches follow. Alone, the acquire fails (the task is held),
/// so it looks as if it commutes with the clock; it doesn't once the release
/// has happened. 10,000-request fuzz runs found this.
#[test]
fn a_call_that_reads_the_clock_once_another_has_happened() {
    let id = || "t:1".to_string();
    let promise = PromiseRec {
        id: id(),
        state: PState::Pending,
        param: None,
        value: None,
        timeout_at: 100,
        created_at: 0,
        settled_at: None,
        tags: Tags { target: true, external: false, timer: false },
    };
    let task = TaskRec { id: id(), state: TState::Acquired, version: 1, pid: Some("worker-self".into()), ttl: Some(TASK_CREATE_TTL) };
    let t = vec![
        Event::Invoke { call: 1, req: Request::CreateTask { id: id(), timeout_at: 100, data: None, target: true } },
        Event::Return { call: 1, res: Response::Created(promise, task) },
        Event::Invoke { call: 2, req: Request::ReleaseTask { id: id(), version: 1 } },
        Event::Invoke { call: 3, req: Request::AcquireTask { id: id(), version: 1, pid: "w1".into(), ttl: 10 } },
        Event::Invoke { call: 4, req: Request::AdvanceClock(11) },
        Event::Return { call: 4, res: Response::Status(200) },
        Event::Receive { msg: Dispatch::Execute { id: id(), version: 1 } },
        Event::Receive { msg: Dispatch::Execute { id: id(), version: 2 } },
    ];
    let mut c = Checker::with_footprints(Resonate, Server::default(), Config { certify: true, ..Config::default() });
    let cert = c.check_certified(t.clone()).unwrap_or_else(|v| panic!("rejects a valid trace: {v}"));
    assert_eq!(certify(&Resonate, Server::default(), &t, &cert), Ok(()));
    let mut c = Checker::with_partitions(Resonate, Server::default(), Config::default());
    assert!(c.check(t.clone()).is_ok(), "partitioned");
    let mut c = Checker::with_footprints(Resonate, Server::default(), Config::default());
    assert!(c.check_complete(&t).is_ok(), "depth-first");
}
