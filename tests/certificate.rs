//! `certify` on its own: it replays a trace with the silent steps a
//! certificate puts before each event, and fails at the first event whose steps
//! the system can't make.

use accordant::{certify, Checker, Config, Event, ExternalOutcome, InternalOutcome, Model, Silent, Time};

/// `Incr` adds one and answers the new value; `Arm` sets a timer at 5 that
/// resets the counter. The clock is the trace's (`Event::Clock`).
struct Counter;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Req {
    Incr,
    Arm,
}

impl Model for Counter {
    type State = u64;
    type External = Req;
    type Response = u64;
    type Internal = ();
    type Dispatch = ();

    fn external(&self, req: &Req, &n: &u64, _: Time) -> Vec<ExternalOutcome<Self>> {
        match req {
            Req::Incr => vec![ExternalOutcome::new(n + 1, n + 1)],
            Req::Arm => vec![ExternalOutcome::same(n, &n).timer(5, ())],
        }
    }

    fn internal(&self, _: &(), _: &u64, _: Time) -> Vec<InternalOutcome<Self>> {
        vec![InternalOutcome::new(0)]
    }
}

type Ev = Event<Req, u64, ()>;

fn call(call: u64, req: Req, res: u64) -> [Ev; 2] {
    [Event::Invoke { call, req }, Event::Return { call, res }]
}

fn clock(at: Time) -> [Ev; 1] {
    [Event::Clock { at }]
}

/// The call takes effect (its only outcome) just before its return.
fn effect(call: u64) -> [Vec<Silent>; 2] {
    [vec![], vec![Silent::Effect { call, j: 0 }]]
}

#[test]
fn a_certificate_explains_its_trace() {
    assert_eq!(certify(&Counter, 0, &call(7, Req::Incr, 1), &effect(7)), Ok(()));
}

#[test]
fn certify_rejects_steps_the_system_cant_make() {
    // The response must match the outcome.
    assert_eq!(certify(&Counter, 0, &call(7, Req::Incr, 2), &effect(7)), Err(1));
    // A call must take effect before it is answered.
    assert_eq!(certify(&Counter, 0, &call(7, Req::Incr, 1), &[vec![], vec![]]), Err(1));
    // There is no second outcome.
    assert_eq!(certify(&Counter, 0, &call(7, Req::Incr, 1), &[vec![], vec![Silent::Effect { call: 7, j: 1 }]]), Err(1));
    // A call id is in use until its response.
    let twice = [Event::Invoke { call: 7, req: Req::Incr }, Event::Invoke { call: 7, req: Req::Incr }];
    assert_eq!(certify(&Counter, 0, &twice, &[vec![], vec![]]), Err(1));
    // Every event needs its entry, even an empty one.
    assert_eq!(certify(&Counter, 0, &call(7, Req::Incr, 1), &[vec![]]), Err(1));
    // The clock doesn't move back.
    assert_eq!(certify(&Counter, 0, &[clock(6), clock(5)].concat(), &[vec![], vec![]]), Err(1));
}

#[test]
fn certify_keeps_timers_on_time() {
    // Arm at 5; the clock moves to 6; then an increment.
    let trace = [call(1, Req::Arm, 0).to_vec(), clock(6).to_vec(), call(2, Req::Incr, 1).to_vec()].concat();
    let run = Silent::Run { i: 0, j: 0 };
    let effect2 = Silent::Effect { call: 2, j: 0 };
    // Before 5 the timer can't run.
    let early = [vec![], vec![Silent::Effect { call: 1, j: 0 }, run], vec![], vec![], vec![effect2]];
    assert_eq!(certify(&Counter, 0, &trace, &early), Err(1));
    // At 6 it is overdue: it runs before anything else is observed, the next
    // request included.
    let late = |before_invoke: Vec<Silent>, before_return: Vec<Silent>| {
        [effect(1).to_vec(), vec![vec![], before_invoke, before_return]].concat()
    };
    assert_eq!(certify(&Counter, 0, &trace, &late(vec![], vec![run, effect2])), Err(3));
    assert_eq!(certify(&Counter, 0, &trace, &late(vec![run], vec![effect2])), Ok(()));
}

#[test]
fn the_checker_certifies_what_it_accepts() {
    let trace: Vec<_> = [
        call(1, Req::Arm, 0).to_vec(),
        call(2, Req::Incr, 1).to_vec(),
        clock(9).to_vec(),
        call(3, Req::Incr, 1).to_vec(), // the timer reset the counter at 5
    ]
    .concat();
    let cert = Checker::new(Counter, 0, Config::default()).check_certified(trace.clone()).unwrap();
    assert_eq!(cert.len(), trace.len(), "one entry per event");
    assert!(cert.iter().flatten().any(|s| *s == Silent::Run { i: 0, j: 0 }));
    assert_eq!(certify(&Counter, 0, &trace, &cert), Ok(()));
}
