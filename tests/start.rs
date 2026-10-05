//! Work a model starts with: components whose behavior comes from internal
//! work alone, from the first state on.

#[path = "common/certified.rs"]
mod certified;
use certified::Certified;

use accordant::{Checker, Config, Event, ExternalOutcome, InternalOutcome, Model, Plain, Sched, Time};

/// Sends one ping, on its own; takes no requests at all.
struct Once;

impl Model for Once {
    type State = ();
    type External = ();
    type Response = ();
    type Internal = ();
    type Dispatch = &'static str;

    fn internal(&self, _: &(), s: &()) -> Vec<InternalOutcome<Self>> {
        vec![InternalOutcome::same(s).send("ping")]
    }

    fn start(&self, _: &()) -> Vec<Sched<()>> {
        vec![Sched::Later(())]
    }
}

fn once() -> Certified<Plain<Once>> {
    Certified(Checker::new(Once, (), Config { certify: true, ..Config::default() }))
}

#[test]
fn a_model_with_no_requests_sends_what_it_starts_with() {
    let mut c = once();
    c.receive("ping").unwrap();
    assert!(once().check(vec![Event::Receive { msg: "ping" }, Event::Receive { msg: "ping" }]).is_err(), "one ping only");
}

#[test]
fn work_it_starts_with_must_run_by_idle() {
    let mut c = once();
    c.assert_idle().unwrap();
    c.receive("ping").unwrap();
}

/// Sends a ping every 10, starting at 10. The driver moves the clock.
struct Periodic;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct Advance(Time);

impl Model for Periodic {
    type State = Time;
    type External = Advance;
    type Response = ();
    type Internal = ();
    type Dispatch = Time;

    fn external(&self, Advance(t): &Advance, now: &Time) -> Vec<ExternalOutcome<Self>> {
        vec![ExternalOutcome::new((), (*t).max(*now))]
    }

    /// A tick sends the time and sets the next one.
    fn internal(&self, _: &(), now: &Time) -> Vec<InternalOutcome<Self>> {
        vec![InternalOutcome::same(now).send(*now).timer(now + 10, ())]
    }

    fn now(&self, now: &Time) -> Time {
        *now
    }

    fn start(&self, _: &Time) -> Vec<Sched<()>> {
        vec![Sched::Timer(10, ())]
    }
}

fn periodic() -> Certified<Plain<Periodic>> {
    Certified(Checker::new(Periodic, 0, Config { certify: true, ..Config::default() }))
}

#[test]
fn a_periodic_component_ticks_on_the_clock() {
    let mut c = periodic();
    c.call(1, Advance(10), ()).unwrap();
    c.call(2, Advance(20), ()).unwrap();
    c.receive(10).unwrap();
    c.receive(20).unwrap();
    assert!(c.receive(30).is_err(), "the clock is at 20: no tick at 30 yet");
}

#[test]
fn a_tick_passed_in_a_jump_runs_once_right_after_it() {
    // The clock jumps from 0 to 25: the tick due at 10 runs right after the
    // jump, on the clock as it reads then, and sets the next for 35.
    let mut c = periodic();
    c.call(1, Advance(25), ()).unwrap();
    assert!(periodic().check(vec![
        Event::Invoke { call: 1, req: Advance(25) },
        Event::Return { call: 1, res: () },
        Event::Receive { msg: 10 },
    ]).is_err());
    c.receive(25).unwrap();
}

#[test]
fn a_periodic_component_does_not_tick_early() {
    let mut c = periodic();
    c.call(1, Advance(9), ()).unwrap();
    assert!(c.receive(10).is_err());
}
