//! Time is the model's: a clock in its state, moved by an `Advance` request.
//! Deadlines are on that clock, and the checker enforces them.

use accordant::{Checker, Config, Event, ExternalOutcome, InternalOutcome, Model, Time};

/// `Start` arms a timer at 5 (`A`); when it fires, `A` gives `B` 2 more time
/// units. `B` records the time it ran; `Read` answers that. `Order` arms two
/// timers, `X` at 4 and `Y` at 3, which log their names.
struct Chain;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
struct State {
    now: Time,
    ran: Option<Time>,
    log: Vec<Work>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Req {
    Advance(Time),
    Start,
    Order,
    Read,
    Log,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Res {
    Ok,
    Ran(Option<Time>),
    Log(Vec<Work>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Work {
    A,
    B,
    X,
    Y,
}

impl Model for Chain {
    type State = State;
    type External = Req;
    type Response = Res;
    type Internal = Work;
    type Dispatch = ();

    fn external(&self, req: &Req, s: &State) -> Vec<ExternalOutcome<Self>> {
        vec![match req {
            Req::Advance(t) => ExternalOutcome::new(Res::Ok, State { now: s.now.max(*t), ..s.clone() }),
            Req::Start => ExternalOutcome::same(Res::Ok, s).timer(5, Work::A),
            Req::Order => ExternalOutcome::same(Res::Ok, s).timer(4, Work::X).timer(3, Work::Y),
            Req::Read => ExternalOutcome::same(Res::Ran(s.ran), s),
            Req::Log => ExternalOutcome::same(Res::Log(s.log.clone()), s),
        }]
    }

    fn internal(&self, w: &Work, s: &State) -> Vec<InternalOutcome<Self>> {
        vec![match w {
            Work::A => InternalOutcome::same(s).timer(s.now + 2, Work::B),
            Work::B => InternalOutcome::new(State { ran: Some(s.now), ..s.clone() }),
            Work::X | Work::Y => {
                let mut n = s.clone();
                n.log.push(w.clone());
                InternalOutcome::new(n)
            }
        }]
    }

    fn now(&self, s: &State) -> Time {
        s.now
    }
}

fn calls(script: &[(Req, Res)]) -> Vec<Event<Req, Res, ()>> {
    let mut trace = Vec::new();
    for (i, (req, res)) in script.iter().enumerate() {
        trace.push(Event::Invoke { call: i as u64, req: req.clone() });
        trace.push(Event::Return { call: i as u64, res: res.clone() });
    }
    trace
}

fn accepts(script: &[(Req, Res)]) -> bool {
    Checker::new(Chain, State::default(), Config::default()).check_certified(calls(script)).is_ok()
}

#[test]
fn a_timer_passed_in_a_jump_runs_right_after_it() {
    // A fires at 5 and sets B for 7. The clock then jumps to 10: B runs right
    // after the jump, at 10, before anything else.
    let read = |ran| [(Req::Start, Res::Ok), (Req::Advance(5), Res::Ok), (Req::Advance(10), Res::Ok), (Req::Read, Res::Ran(ran))];
    assert!(accepts(&read(Some(10))));
    assert!(!accepts(&read(Some(5))), "B is a timer at 7: it can't run at 5");
    assert!(!accepts(&read(None)), "B is overdue at 10: it ran before the read");
    assert!(!accepts(&read(Some(7))), "the clock never read 7");
}

#[test]
fn a_timer_does_not_fire_early() {
    let read = |ran| [(Req::Start, Res::Ok), (Req::Advance(4), Res::Ok), (Req::Read, Res::Ran(ran))];
    assert!(accepts(&read(None)));
    assert!(!accepts(&read(Some(4))), "A fires at 5, so B can't have run");
}

#[test]
fn timers_passed_in_one_jump_fire_in_deadline_order() {
    let log = |l| [(Req::Order, Res::Ok), (Req::Advance(10), Res::Ok), (Req::Log, Res::Log(l))];
    assert!(accepts(&log(vec![Work::Y, Work::X])));
    assert!(!accepts(&log(vec![Work::X, Work::Y])));
}
