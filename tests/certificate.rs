//! `certify` on its own: it replays a certificate and fails on the first move
//! the system can't make.

use accordant::{certify, Checker, Config, Event, ExternalOutcome, InternalOutcome, Model, Move, Time};

/// `Incr` adds one and answers the new value; `Arm` sets a timer at 5 that
/// resets the counter.
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

    fn external(&self, req: &Req, n: &u64, _now: Time) -> Vec<ExternalOutcome<Self>> {
        match req {
            Req::Incr => vec![ExternalOutcome::new(n + 1, n + 1)],
            Req::Arm => vec![ExternalOutcome::same(*n, n).timer(5, ())],
        }
    }

    fn internal(&self, _: &(), _n: &u64, _now: Time) -> Vec<InternalOutcome<Self>> {
        vec![InternalOutcome::new(0)]
    }
}

fn incr(call: u64) -> Vec<Move<Req, u64>> {
    vec![Move::Invoke { call, req: Req::Incr }, Move::Effect { call, j: 0 }, Move::Return { call, res: 1 }]
}

#[test]
fn a_certificate_shows_its_trace() {
    let shown = certify(&Counter, 0, incr(7)).unwrap();
    assert_eq!(shown, vec![Event::Invoke { at: 0, call: 7, req: Req::Incr }, Event::Return { at: 0, call: 7, res: 1 }]);
}

#[test]
fn certify_rejects_illegal_moves() {
    // The response must match the outcome.
    let mut wrong = incr(7);
    wrong[2] = Move::Return { call: 7, res: 2 };
    assert_eq!(certify(&Counter, 0, wrong), Err(2));
    // A call must take effect before it is answered.
    assert_eq!(certify(&Counter, 0, vec![Move::Invoke { call: 7, req: Req::Incr }, Move::Return { call: 7, res: 1 }]), Err(1));
    // There is no second outcome.
    assert_eq!(certify(&Counter, 0, vec![Move::Invoke { call: 7, req: Req::Incr }, Move::Effect { call: 7, j: 1 }]), Err(1));
    // A call id is in use until its response.
    assert_eq!(certify(&Counter, 0, vec![Move::Invoke { call: 7, req: Req::Incr }, Move::Invoke { call: 7, req: Req::Incr }]), Err(1));
}

#[test]
fn certify_keeps_timers_on_time() {
    let arm = vec![Move::Invoke { call: 1, req: Req::Arm }, Move::Effect { call: 1, j: 0 }, Move::Return { call: 1, res: 0 }];
    // Time can't skip the timer at 5.
    let skip = [arm.clone(), vec![Move::Advance { to: 6 }]].concat();
    assert_eq!(certify(&Counter, 0, skip), Err(3));
    // At 5 the timer is overdue: it runs before anything is observed.
    let mut late = [arm.clone(), vec![Move::Advance { to: 5 }], incr(2)].concat();
    assert_eq!(certify(&Counter, 0, late.clone()), Err(4));
    late.insert(4, Move::Run { i: 0, j: 0 });
    assert!(certify(&Counter, 0, late).is_ok());
}

#[test]
fn the_checker_certifies_what_it_accepts() {
    let trace = vec![
        Event::Invoke { at: 0, call: 1, req: Req::Arm },
        Event::Return { at: 0, call: 1, res: 0 },
        Event::Invoke { at: 3, call: 2, req: Req::Incr },
        Event::Return { at: 3, call: 2, res: 1 },
        Event::Invoke { at: 9, call: 3, req: Req::Incr },
        Event::Return { at: 9, call: 3, res: 1 }, // the timer reset the counter at 5
    ];
    let moves = Checker::new(Counter, 0, Config::default()).check_certified(trace.clone()).unwrap();
    assert!(moves.contains(&Move::Run { i: 0, j: 0 }));
    assert_eq!(certify(&Counter, 0, moves).unwrap(), trace);
}
