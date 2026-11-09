//! Executable examples for the Rust + Verus Rover world.

use echod_rover::rover::comm::{BoundaryEvent, ProcessEvent};
use echod_rover::rover::{RoverExec, RoverSpec};
use RoverExec::{check, replay, Action, CheckConfig, ProcResult};
use echod_rover::Time;
use vstd::prelude::View;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Pid {
    Outside,
    Service,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Message {
    Add(u64),
    Value(u64),
}

struct Counter;
struct CounterSpec;
struct SpecOnlyProc;
#[allow(dead_code)] // read only by the erased View specification
struct CounterProc(u64);

#[derive(Clone, Debug, PartialEq, Eq)]
struct CounterState(u64);

impl View for CounterState {
    type V = CounterProc;
}

impl RoverSpec::Proc for SpecOnlyProc {
    type Config = ();
    type Pid = ();
    type Message = ();
}

impl RoverSpec::Proc for CounterProc {
    type Config = ();
    type Pid = Pid;
    type Message = Message;
}

impl RoverExec::Proc for CounterState {
    type Spec = CounterProc;

    fn on_event(
        &self,
        _: &(),
        _: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> Vec<ProcResult<Self>> {
        match event {
            ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Add(amount),
            } => {
                let next = self.0 + amount;
                vec![ProcResult {
                    state: CounterState(next),
                    send: vec![(Pid::Outside, Message::Value(next))],
                }]
            }
            _ => Vec::new(),
        }
    }
}

/// A mathematical model need not provide executable state or transitions.
struct SpecOnly;

impl RoverSpec::Spec for SpecOnly {
    type Config = ();
    type Pid = ();
    type Proc = SpecOnlyProc;
    type Message = ();
    type Boundary = ();
}

impl RoverSpec::Spec for CounterSpec {
    type Config = ();
    type Pid = Pid;
    type Proc = CounterProc;
    type Message = Message;
    type Boundary = Event;
}

impl RoverExec::Spec for Counter {
    type Spec = CounterSpec;
    type Proc = CounterState;

    fn outside(&self) -> Pid {
        Pid::Outside
    }

    fn initial(&self, _: &()) -> Vec<(Pid, CounterState)> {
        vec![(Pid::Service, CounterState(0))]
    }

    fn injectable(&self, _: &(), message: &Message) -> bool {
        matches!(message, Message::Add(_))
    }

}

type Event = BoundaryEvent<Pid, Message>;

#[test]
fn a_specification_does_not_need_an_executable_realization() {
    fn accepts_spec<S: RoverSpec::Spec>(_: S) {}
    accepts_spec(SpecOnly);
}

#[test]
fn an_executable_realization_names_its_distinct_specification() {
    fn accepts_exec<E: RoverExec::Spec<Spec = CounterSpec>>(_: E) {}
    accepts_exec(Counter);
}

fn input(at: Time, amount: u64) -> Event {
    Event::Input {
        recipient: Pid::Service,
        at,
        message: Message::Add(amount),
    }
}

fn output(at: Time, value: u64) -> Event {
    Event::Output {
        sender: Pid::Service,
        at,
        message: Message::Value(value),
    }
}

#[test]
fn check_finds_and_replays_a_valid_trace() {
    let trace = [input(0, 3), output(1, 3)];
    let certificate = check(
        &Counter,
        &(),
        &trace,
        CheckConfig::for_trace_len(trace.len()),
    )
    .expect("valid trace");

    assert_eq!(certificate.len(), 3);
    assert!(matches!(certificate[1], Action::Process { outcome: 0, .. }));
    assert_eq!(replay(&Counter, &(), &trace, &certificate), Ok(()));
}

#[test]
fn check_rejects_an_output_the_model_never_sent() {
    let trace = [input(0, 3), output(1, 4)];
    assert!(check(
        &Counter,
        &(),
        &trace,
        CheckConfig::for_trace_len(trace.len())
    )
    .is_none());
}

#[test]
fn append_only_delivery_can_be_duplicated() {
    // The same injected request is received twice. Receiving never consumes
    // its network envelope, so the two hidden steps produce values 2 and 4.
    let trace = [input(0, 2), output(1, 2), output(2, 4)];
    assert!(check(&Counter, &(), &trace, CheckConfig { max_steps: 6 }).is_some());
}

#[test]
fn append_only_output_can_be_observed_twice() {
    let trace = [input(0, 2), output(1, 2), output(2, 2)];
    assert!(check(&Counter, &(), &trace, CheckConfig { max_steps: 4 }).is_some());
}

#[test]
fn outputs_can_be_observed_in_a_different_order() {
    let trace = [input(0, 1), input(0, 10), output(1, 11), output(2, 1)];
    assert!(check(&Counter, &(), &trace, CheckConfig { max_steps: 8 }).is_some());
}

#[test]
fn replay_rejects_nonmonotone_time() {
    let trace = [input(2, 1), output(1, 1)];
    assert!(check(&Counter, &(), &trace, CheckConfig { max_steps: 4 }).is_none());
}

#[test]
fn a_bound_limits_search_without_claiming_invalidity() {
    let trace = [input(0, 3), output(1, 3)];
    assert!(check(&Counter, &(), &trace, CheckConfig { max_steps: 2 }).is_none());
    assert!(check(&Counter, &(), &trace, CheckConfig { max_steps: 3 }).is_some());
}

#[test]
fn independent_replay_rejects_a_bad_outcome_index() {
    let trace = [input(0, 3), output(1, 3)];
    let certificate = vec![
        Action::Inject {
            recipient: Pid::Service,
            at: 0,
            message: Message::Add(3),
        },
        Action::Process {
            slot: 0,
            process: Pid::Service,
            at: 1,
            event: ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Add(3),
            },
            outcome: 1,
        },
        Action::Observe {
            sender: Pid::Service,
            at: 1,
            message: Message::Value(3),
        },
    ];

    assert_eq!(replay(&Counter, &(), &trace, &certificate), Err(1));
}

#[test]
fn injection_checks_the_boundary_policy_and_recipient() {
    let noninjectable = [Event::Input {
        recipient: Pid::Service,
        at: 0,
        message: Message::Value(7),
    }];
    let outside = [Event::Input {
        recipient: Pid::Outside,
        at: 0,
        message: Message::Add(7),
    }];

    assert!(check(&Counter, &(), &noninjectable, CheckConfig { max_steps: 1 }).is_none());
    assert!(check(&Counter, &(), &outside, CheckConfig { max_steps: 1 }).is_none());
}
