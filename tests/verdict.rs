//! The checker's three answers: a valid trace is `Ok`, an invalid one `Ko`, and
//! one it couldn't decide within its budget `Unknown`.

use accordant::{Checker, Config, Event, ExternalOutcome, Model, Verdict};

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
}

/// Many writes in flight, never answered, then a read: which value it sees
/// depends on which writes took effect, in which order.
fn trace(read: u8) -> Vec<Event<Req, u8, ()>> {
    let mut t: Vec<_> = (1..=8).map(|v| Event::Invoke { call: v as u64, req: Req::Write(v) }).collect();
    t.push(Event::Invoke { call: 100, req: Req::Read });
    t.push(Event::Return { call: 100, res: read });
    t
}

fn verdict(read: u8, cfg: Config) -> Verdict<()> {
    Checker::new(Register, 0, cfg).check(trace(read)).map(|_| ()).into()
}

#[test]
fn three_answers() {
    assert!(verdict(5, Config::default()).is_ok());
    assert!(verdict(9, Config::default()).is_ko(), "no write wrote 9");
    let tiny = Config { max_explore: 3, ..Config::default() };
    match verdict(9, tiny) {
        Verdict::Unknown(v) => assert!(v.reason.starts_with("gave up"), "{v}"),
        other => panic!("expected Unknown, got {other:?}"),
    }
}
