//! `certify` on its own: it replays a certificate and fails on the first move
//! the system can't make.

use accordant::{certify, Checker, Config, Event, ExternalOutcome, InternalOutcome, Model, Move, Time};

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

fn incr(call: u64, res: u64) -> Vec<Move<Req, u64>> {
    vec![Move::Invoke { call, req: Req::Incr }, Move::Effect { call, j: 0 }, Move::Return { call, res }]
}

fn advance(call: u64, t: Time, res: u64) -> Vec<Move<Req, u64>> {
    vec![Move::Invoke { call, req: Req::Advance(t) }, Move::Effect { call, j: 0 }, Move::Return { call, res }]
}

#[test]
fn a_certificate_shows_its_trace() {
    let shown = certify(&Counter, (0, 0), incr(7, 1)).unwrap();
    assert_eq!(shown, vec![Event::Invoke { call: 7, req: Req::Incr }, Event::Return { call: 7, res: 1 }]);
}

#[test]
fn certify_rejects_illegal_moves() {
    // The response must match the outcome.
    let mut wrong = incr(7, 1);
    wrong[2] = Move::Return { call: 7, res: 2 };
    assert_eq!(certify(&Counter, (0, 0), wrong), Err(2));
    // A call must take effect before it is answered.
    assert_eq!(certify(&Counter, (0, 0), vec![Move::Invoke { call: 7, req: Req::Incr }, Move::Return { call: 7, res: 1 }]), Err(1));
    // There is no second outcome.
    assert_eq!(certify(&Counter, (0, 0), vec![Move::Invoke { call: 7, req: Req::Incr }, Move::Effect { call: 7, j: 1 }]), Err(1));
    // A call id is in use until its response.
    assert_eq!(certify(&Counter, (0, 0), vec![Move::Invoke { call: 7, req: Req::Incr }, Move::Invoke { call: 7, req: Req::Incr }]), Err(1));
}

#[test]
fn certify_keeps_timers_on_time() {
    let arm = vec![Move::Invoke { call: 1, req: Req::Arm }, Move::Effect { call: 1, j: 0 }, Move::Return { call: 1, res: 0 }];
    // Before 5 the timer can't run.
    let early = [arm.clone(), vec![Move::Run { i: 0, j: 0 }]].concat();
    assert_eq!(certify(&Counter, (0, 0), early), Err(3));
    // Past 5 it is overdue: it runs before anything else, even the clock
    // request's response.
    let mut late = [arm.clone(), advance(2, 6, 0)].concat();
    assert_eq!(certify(&Counter, (0, 0), late.clone()), Err(5));
    late.insert(5, Move::Run { i: 0, j: 0 });
    assert!(certify(&Counter, (0, 0), late).is_ok());
}

#[test]
fn the_checker_certifies_what_it_accepts() {
    let call = |call, req, res| [Event::Invoke { call, req }, Event::Return { call, res }];
    let trace: Vec<_> = [
        call(1, Req::Arm, 0),
        call(2, Req::Incr, 1),
        call(3, Req::Advance(9), 1),
        call(4, Req::Incr, 1), // the timer reset the counter at 5
    ]
    .concat();
    let moves = Checker::new(Counter, (0, 0), Config::default()).check_certified(trace.clone()).unwrap();
    assert!(moves.contains(&Move::Run { i: 0, j: 0 }));
    assert_eq!(certify(&Counter, (0, 0), moves).unwrap(), trace);
}
