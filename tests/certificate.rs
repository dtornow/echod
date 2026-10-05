//! `certify` on its own: it replays a trace with the silent steps a
//! certificate puts before each event, and fails at the first event whose steps
//! the system can't make.

use accordant::{certify, Checker, Config, Event, ExternalOutcome, InternalOutcome, Model, Silent, Time};

/// `Incr` adds one and answers the new value; `Arm` sets a timer at 5 that
/// resets the counter; `Advance` moves the clock. The state is (clock, count).
struct Counter;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Req {
    Incr,
    Arm,
    Advance(Time),
}

impl Model for Counter {
    type State = (Time, u64);
    type External = Req;
    type Response = u64;
    type Internal = ();
    type Dispatch = ();

    fn external(&self, req: &Req, &(now, n): &(Time, u64)) -> Vec<ExternalOutcome<Self>> {
        match req {
            Req::Incr => vec![ExternalOutcome::new(n + 1, (now, n + 1))],
            Req::Arm => vec![ExternalOutcome::same(n, &(now, n)).timer(5, ())],
            Req::Advance(t) => vec![ExternalOutcome::new(n, (*t, n))],
        }
    }

    fn internal(&self, _: &(), &(now, _): &(Time, u64)) -> Vec<InternalOutcome<Self>> {
        vec![InternalOutcome::new((now, 0))]
    }

    fn now(&self, s: &(Time, u64)) -> Time {
        s.0
    }
}

type Ev = Event<Req, u64, ()>;

fn call(call: u64, req: Req, res: u64) -> [Ev; 2] {
    [Event::Invoke { call, req }, Event::Return { call, res }]
}

/// The call takes effect (its only outcome) just before its return.
fn effect(call: u64) -> [Vec<Silent>; 2] {
    [vec![], vec![Silent::Effect { call, j: 0 }]]
}

#[test]
fn a_certificate_explains_its_trace() {
    assert_eq!(certify(&Counter, (0, 0), &call(7, Req::Incr, 1), &effect(7)), Ok(()));
}

#[test]
fn certify_rejects_steps_the_system_cant_make() {
    // The response must match the outcome.
    assert_eq!(certify(&Counter, (0, 0), &call(7, Req::Incr, 2), &effect(7)), Err(1));
    // A call must take effect before it is answered.
    assert_eq!(certify(&Counter, (0, 0), &call(7, Req::Incr, 1), &[vec![], vec![]]), Err(1));
    // There is no second outcome.
    assert_eq!(certify(&Counter, (0, 0), &call(7, Req::Incr, 1), &[vec![], vec![Silent::Effect { call: 7, j: 1 }]]), Err(1));
    // A call id is in use until its response.
    let twice = [Event::Invoke { call: 7, req: Req::Incr }, Event::Invoke { call: 7, req: Req::Incr }];
    assert_eq!(certify(&Counter, (0, 0), &twice, &[vec![], vec![]]), Err(1));
    // Every event needs its entry, even an empty one.
    assert_eq!(certify(&Counter, (0, 0), &call(7, Req::Incr, 1), &[vec![]]), Err(1));
}

#[test]
fn certify_keeps_timers_on_time() {
    let trace = [call(1, Req::Arm, 0), call(2, Req::Advance(6), 0)].concat();
    let run = Silent::Run { i: 0, j: 0 };
    let effect2 = Silent::Effect { call: 2, j: 0 };
    // Before 5 the timer can't run.
    assert_eq!(certify(&Counter, (0, 0), &trace, &[vec![], vec![Silent::Effect { call: 1, j: 0 }, run], vec![], vec![]]), Err(1));
    // Past 5 it is overdue: it runs before anything else, even the clock
    // request's response.
    let late = |before_return: Vec<Silent>| [effect(1).to_vec(), vec![vec![], before_return]].concat();
    assert_eq!(certify(&Counter, (0, 0), &trace, &late(vec![effect2])), Err(3));
    assert_eq!(certify(&Counter, (0, 0), &trace, &late(vec![effect2, run])), Ok(()));
}

#[test]
fn the_checker_certifies_what_it_accepts() {
    let trace: Vec<_> = [
        call(1, Req::Arm, 0),
        call(2, Req::Incr, 1),
        call(3, Req::Advance(9), 1),
        call(4, Req::Incr, 1), // the timer reset the counter at 5
    ]
    .concat();
    let cert = Checker::new(Counter, (0, 0), Config::default()).check_certified(trace.clone()).unwrap();
    assert_eq!(cert.len(), trace.len(), "one entry per event");
    assert!(cert.iter().flatten().any(|s| *s == Silent::Run { i: 0, j: 0 }));
    assert_eq!(certify(&Counter, (0, 0), &trace, &cert), Ok(()));
}
