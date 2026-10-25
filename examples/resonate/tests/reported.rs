//! A server that reports its own steps (`Resonate { reported: true }`): the
//! model runs nothing on its own and takes each step as `Request::Step` at
//! the instant the server ran it. A client may then read between the instant
//! something fell due and the step that did it, and the model shows what the
//! server showed. A promise past its deadline settles when a request reads
//! it or a sweep gets to it.

use accordant::{Checker, Config, Event};
use resonate::*;

const FAR: u64 = 9_000_000_000_000;

fn create(id: &str, timeout_at: u64, target: bool) -> Request {
    Request::CreatePromise(Create { id: id.into(), timeout_at, data: None, tags: Tags { target, external: !target, timer: false, delay: None } })
}

struct T {
    c: Checker<accordant::Grouped<Resonate>>,
    call: u64,
}

impl T {
    fn new(now: u64) -> Self {
        let mut c = Checker::with_partitions(Resonate { retry_timeout: 5_000, reported: true }, Server::default(), Config::default()).dominating(dominates);
        c.clock(now).unwrap();
        T { c, call: 0 }
    }
    fn at(&mut self, now: u64) {
        self.c.clock(now).unwrap();
    }
    fn call(&mut self, req: Request, pred: impl Fn(&Response) -> bool, what: &str) {
        self.call += 1;
        let allowed = self.c.allowed(&req);
        let res = allowed.iter().find(|r| pred(r)).cloned().unwrap_or_else(|| panic!("{what}: none of {allowed:?} fits"));
        self.c.call(self.call, req, res).unwrap_or_else(|v| panic!("{what}: {v}"));
    }
    fn step(&mut self, st: Step) {
        self.call += 1;
        self.c.call(self.call, Request::Step(st), Response::Status(200)).unwrap_or_else(|v| panic!("step: {v}"));
    }
    fn recv(&mut self, msg: Dispatch) {
        self.c.receive(msg).unwrap_or_else(|v| panic!("receive: {v}"));
    }
}

fn task_state(s: TState) -> impl Fn(&Response) -> bool {
    move |r| matches!(r, Response::Task(t) | Response::Both(_, t) if t.state == s)
}

fn status(code: u16) -> impl Fn(&Response) -> bool {
    move |r| *r == Response::Status(code)
}

#[test]
fn a_lease_holds_past_its_end_until_the_sweep_that_reclaims_it() {
    let mut t = T::new(1_000_000);
    t.call(create("o:1", FAR, true), |r| matches!(r, Response::Promise(_)), "create");
    // the create's own drain dispatches the task
    t.step(Step::Drain(vec!["o:1".into()]));
    t.recv(Dispatch::Execute { id: "o:1".into(), version: 0 });
    t.call(Request::AcquireTask { id: "o:1".into(), version: 0, pid: "w".into(), ttl: 1_000 }, task_state(TState::Acquired), "acquire");
    t.at(1_002_000);
    // past the lease's end, still held: no sweep yet, and a drain leaves the
    // lease alone
    t.call(Request::GetTask("o:1".into()), task_state(TState::Acquired), "read held");
    t.step(Step::Drain(vec!["o:1".into()]));
    t.call(Request::GetTask("o:1".into()), task_state(TState::Acquired), "still held");
    t.step(Step::Objects(vec!["o:1".into()]));
    // the sweep reclaimed it and dispatched it again, in one step
    t.recv(Dispatch::Execute { id: "o:1".into(), version: 1 });
    t.call(Request::GetTask("o:1".into()), task_state(TState::Pending), "read reclaimed");
    // no retry of the model's own: five seconds on, nothing happens without a step
    t.at(1_008_000);
    t.call(Request::GetTask("o:1".into()), task_state(TState::Pending), "still pending");
    assert_eq!(t.c.width(), 1);
}

#[test]
fn a_fire_in_two_steps_shows_the_schedule_not_yet_advanced_in_between() {
    let mut t = T::new(1_000_000);
    let sched = ScheduleCreate {
        id: "s".into(),
        cron: "* * * * * *".into(),
        promise_id: "o:{{.id}}.{{.timestamp}}".into(),
        promise_timeout: 3_000,
        promise_param: None,
        promise_tags: Tags { target: true, external: false, timer: false, delay: None },
    };
    t.call(Request::CreateSchedule(sched), |r| matches!(r, Response::Schedule(c) if c.next_run_at == 1_001_000), "create schedule");
    t.at(1_001_500);
    // due, not fired: a reporting server fires when it gets to it
    t.call(Request::GetSchedule("s".into()), |r| matches!(r, Response::Schedule(c) if c.next_run_at == 1_001_000 && c.last_run_at.is_none()), "read due");
    t.call(Request::GetPromise("o:s.1001000".into()), status(404), "no occurrence yet");
    t.step(Step::Fire { schedule: "s".into(), at: 1_001_000, promise: "o:s.1001000".into() });
    t.step(Step::Objects(vec!["o:s.1001000".into()]));
    t.recv(Dispatch::Execute { id: "o:s.1001000".into(), version: 0 });
    // the occurrence exists as of its instant; the run is not recorded yet
    t.call(Request::GetPromise("o:s.1001000".into()), |r| matches!(r, Response::Promise(p) if p.created_at == 1_001_000), "occurrence");
    t.call(Request::GetSchedule("s".into()), |r| matches!(r, Response::Schedule(c) if c.next_run_at == 1_001_000 && c.last_run_at.is_none()), "read between");
    t.step(Step::Advance { schedule: "s".into(), at: 1_001_000 });
    t.call(Request::GetSchedule("s".into()), |r| matches!(r, Response::Schedule(c) if c.next_run_at == 1_002_000 && c.last_run_at == Some(1_001_000)), "read advanced");
    // a stale advance (the schedule moved on) does nothing
    t.step(Step::Advance { schedule: "s".into(), at: 1_001_000 });
    t.call(Request::GetSchedule("s".into()), |r| matches!(r, Response::Schedule(c) if c.next_run_at == 1_002_000), "unchanged");
    assert_eq!(t.c.width(), 1);
}

#[test]
fn a_deadline_is_read_as_passed_and_kept_so() {
    // Past its deadline with no step reported: a read projects it, as Lean
    // reads it, and the server keeps the reading; its callbacks are served
    // by the drain that follows, not before.
    let mut t = T::new(1_000_000);
    t.call(create("o:a", 1_000_500, false), |r| matches!(r, Response::Promise(_)), "create a");
    t.call(create("o:r", FAR, true), |r| matches!(r, Response::Promise(_)), "create r");
    t.step(Step::Drain(vec!["o:a".into(), "o:r".into()]));
    t.recv(Dispatch::Execute { id: "o:r".into(), version: 0 });
    t.call(Request::AcquireTask { id: "o:r".into(), version: 0, pid: "w".into(), ttl: 10_000 }, task_state(TState::Acquired), "acquire r");
    t.call(Request::SuspendTask { id: "o:r".into(), version: 1, awaited: vec!["o:a".into()] }, status(200), "suspend r on a");
    t.at(1_001_000);
    // a drain does not time anything out: r stays suspended
    t.step(Step::Drain(vec!["o:a".into(), "o:r".into()]));
    t.call(Request::GetTask("o:r".into()), task_state(TState::Suspended), "still suspended");
    // reading a settles it; the read's drain then resumes r
    t.call(Request::GetPromise("o:a".into()), |r| matches!(r, Response::Promise(p) if p.state == PState::TimedOut && p.settled_at == Some(1_000_500)), "timed out");
    t.step(Step::Drain(vec!["o:a".into(), "o:r".into()]));
    t.recv(Dispatch::Execute { id: "o:r".into(), version: 1 });
    t.call(Request::GetTask("o:r".into()), task_state(TState::Pending), "resumed");
    assert_eq!(t.c.width(), 1);
}

#[test]
fn a_sweep_drains_in_rounds() {
    // The awaited promise times out in the sweep; its awaiter, suspended on
    // it, resumes and is dispatched in the same step, as a draining sweep does.
    let mut t = T::new(1_000_000);
    t.call(create("o:a", 1_000_500, false), |r| matches!(r, Response::Promise(_)), "create a");
    t.call(create("o:r", FAR, true), |r| matches!(r, Response::Promise(_)), "create r");
    t.step(Step::Objects(vec!["o:a".into(), "o:r".into()]));
    t.recv(Dispatch::Execute { id: "o:r".into(), version: 0 });
    t.call(Request::AcquireTask { id: "o:r".into(), version: 0, pid: "w".into(), ttl: 10_000 }, task_state(TState::Acquired), "acquire r");
    t.call(Request::SuspendTask { id: "o:r".into(), version: 1, awaited: vec!["o:a".into()] }, status(200), "suspend r on a");
    t.at(1_001_000);
    t.call(Request::GetTask("o:r".into()), task_state(TState::Suspended), "still suspended");
    t.step(Step::Objects(vec!["o:r".into(), "o:a".into()]));
    t.recv(Dispatch::Execute { id: "o:r".into(), version: 1 });
    t.call(Request::GetTask("o:r".into()), task_state(TState::Pending), "resumed and dispatched");
    assert_eq!(t.c.width(), 1);
}

#[test]
fn an_unreported_step_is_not_assumed() {
    // Without the sweep, the model never reclaims the lease: a read seeing it
    // pending is refused.
    let mut t = T::new(1_000_000);
    t.call(create("o:1", FAR, true), |r| matches!(r, Response::Promise(_)), "create");
    t.step(Step::Objects(vec!["o:1".into()]));
    t.recv(Dispatch::Execute { id: "o:1".into(), version: 0 });
    t.call(Request::AcquireTask { id: "o:1".into(), version: 0, pid: "w".into(), ttl: 1_000 }, task_state(TState::Acquired), "acquire");
    t.at(1_002_000);
    let r = t.c.call(99, Request::GetTask("o:1".into()), Response::Task(TaskRec { id: "o:1".into(), state: TState::Pending, version: 1, pid: None, ttl: None, resumes: 0 }));
    assert!(r.is_err(), "a reclaim nobody reported");
}

#[test]
fn the_dominance_order_changes_no_verdict() {
    // Every random run of the spec, checked with and without the model's
    // order: the same verdict, and the certificate replays.
    use accordant::{certify, drive, Choices, Drive};
    for seed in 1..=60 {
        let tr = drive(&Resonate::default(), Server::default(), &Drive { requests: 40, concurrency: 3, guided: seed % 2 == 0 }, Choices::random(seed)).trace;
        let plain = Checker::with_footprints(Resonate::default(), Server::default(), Config::default()).check(tr.clone()).is_ok();
        let mut c = Checker::with_footprints(Resonate::default(), Server::default(), Config { certify: true, ..Config::default() }).dominating(dominates);
        match c.check_certified(tr.clone()) {
            Ok(cert) => {
                assert!(plain, "seed {seed}");
                assert_eq!(certify(&Resonate::default(), Server::default(), &tr, &cert), Ok(()), "seed {seed}");
            }
            Err(v) => assert!(!plain, "seed {seed}: the order refuses what the plain checker takes: {v}"),
        }
    }
    let _ = Event::<Request, Response, Dispatch>::Clock { at: 0 };
}
