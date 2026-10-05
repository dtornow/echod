//! Deadlines of work spawned while the clock is moving.

use accordant::{Checker, Config, Event, ExternalOutcome, InternalOutcome, Model, Time};

/// `Start` arms a timer at 5 (`A`); when it fires, `A` gives `B` 2 more time
/// units. `B` records when it ran; `Read` answers that.
struct Chain;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Req {
    Start,
    Read,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Work {
    A,
    B,
}

impl Model for Chain {
    type State = Option<Time>;
    type External = Req;
    type Response = Option<Time>;
    type Internal = Work;
    type Dispatch = ();

    fn external(&self, req: &Req, s: &Option<Time>, _now: Time) -> Vec<ExternalOutcome<Self>> {
        match req {
            Req::Start => vec![ExternalOutcome::same(None, s).timer(5, Work::A)],
            Req::Read => vec![ExternalOutcome::same(*s, s)],
        }
    }

    fn internal(&self, w: &Work, _s: &Option<Time>, now: Time) -> Vec<InternalOutcome<Self>> {
        match w {
            Work::A => vec![InternalOutcome::new(None).within(2, Work::B)],
            Work::B => vec![InternalOutcome::new(Some(now))],
        }
    }
}

fn read_at_10(ran: Time) -> bool {
    let trace = vec![
        Event::Invoke { at: 0, call: 1, req: Req::Start },
        Event::Return { at: 0, call: 1, res: None },
        Event::Invoke { at: 10, call: 2, req: Req::Read },
        Event::Return { at: 10, call: 2, res: Some(ran) },
    ];
    Checker::new(Chain, None, Config::default()).check_certified(trace).is_ok()
}

#[test]
fn work_spawned_mid_tick_meets_its_deadline() {
    // A fires at 5, so B runs somewhere in [5, 7].
    for t in [5, 7] {
        assert!(read_at_10(t), "B may run at {t}");
    }
    for t in [4, 8, 9, 10] {
        assert!(!read_at_10(t), "B may not run at {t}");
    }
    // Valid, but the checker only stops the clock where something is due or
    // observed (5, 7, 10), so it never tries B at 6. Incomplete, not unsound.
    assert!(!read_at_10(6));
}


