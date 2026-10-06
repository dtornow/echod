//! `refute` proves a trace invalid: its answer `Some(k)` is verified to mean no
//! execution of the model shows the trace. A valid trace is never refuted, and
//! past its limit it answers `None`.

use accordant::{refute, Checker, Config, Event, ExternalOutcome, InternalOutcome, Model, Time};

/// A register: `Write(v)` sets it, `Read` answers it.
struct Register;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Req {
    Write(u8),
    Read,
}

impl Model for Register {
    type State = u8;
    type External = Req;
    type Response = u8;
    type Internal = ();
    type Dispatch = ();

    fn external(&self, req: &Req, s: &u8) -> Vec<ExternalOutcome<Self>> {
        match req {
            Req::Write(v) => vec![ExternalOutcome::new(*v, *v)],
            Req::Read => vec![ExternalOutcome::same(*s, s)],
        }
    }

    fn internal(&self, _: &(), _: &u8) -> Vec<InternalOutcome<Self>> {
        Vec::new()
    }

    fn now(&self, _: &u8) -> Time {
        0
    }
}

type Trace = Vec<Event<Req, u8, ()>>;

/// Writes of 1..=n in flight, never answered, then a read answering `read`.
fn writes_then_read(n: u8, read: u8) -> Trace {
    let mut t: Trace = (1..=n).map(|v| Event::Invoke { call: v as u64, req: Req::Write(v) }).collect();
    t.push(Event::Invoke { call: 100, req: Req::Read });
    t.push(Event::Return { call: 100, res: read });
    t
}

/// Two writes in flight; reads, one after the other, see 1, then 2, then 1:
/// once 2 is read after 1, the write of 1 has taken effect before the write of
/// 2, and can't take effect again.
fn flip_flop() -> Trace {
    let mut t: Trace = vec![Event::Invoke { call: 1, req: Req::Write(1) }, Event::Invoke { call: 2, req: Req::Write(2) }];
    for (call, res) in [(10, 1), (11, 2), (12, 1)] {
        t.push(Event::Invoke { call, req: Req::Read });
        t.push(Event::Return { call, res });
    }
    t
}

fn rejects(t: &Trace) -> bool {
    Checker::new(Register, 0, Config::default()).check(t.clone()).is_err()
}

#[test]
fn an_invalid_trace_is_refuted_at_the_event_nothing_explains() {
    let t = writes_then_read(4, 9);
    assert!(rejects(&t));
    assert_eq!(refute(&Register, 0, &t, 10_000), Some(t.len() - 1), "no write wrote 9");

    let t = flip_flop();
    assert!(rejects(&t));
    assert_eq!(refute(&Register, 0, &t, 10_000), Some(t.len() - 1));
}

#[test]
fn a_valid_trace_is_never_refuted() {
    for read in 0..=4 {
        let t = writes_then_read(4, read);
        assert!(!rejects(&t));
        assert_eq!(refute(&Register, 0, &t, 10_000), None, "read {read}");
    }
}

#[test]
fn past_its_limit_it_cannot_tell() {
    // Six writes in flight: 2^6 subsets of them taken effect, in any order.
    let t = writes_then_read(6, 9);
    assert_eq!(refute(&Register, 0, &t, 10), None);
    assert!(refute(&Register, 0, &t, 100_000).is_some());
}
