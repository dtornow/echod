//! Identical work started twice runs twice: pending work is a multiset, as in
//! the Lean semantics, not a set.

#[path = "common/certified.rs"]
mod certified;
use certified::Certified;

use echod_rover::{Checker, Config, ExternalOutcome, InternalOutcome, Keyed, Model, Plain, Time};

/// `Bump` starts the same increment twice; `Read` answers the counter.
struct Twice;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Req {
    Bump,
    Read,
}

impl Model for Twice {
    type State = u32;
    type External = Req;
    type Response = u32;
    type Internal = ();
    type Dispatch = ();

    fn external(&self, req: &Req, n: &u32, _: Time) -> Vec<ExternalOutcome<Self>> {
        match req {
            Req::Bump => vec![ExternalOutcome::same(0, n).later(()).later(())],
            Req::Read => vec![ExternalOutcome::same(*n, n)],
        }
    }

    fn internal(&self, _: &(), n: &u32, _: Time) -> Vec<InternalOutcome<Self>> {
        vec![InternalOutcome::new(n + 1)]
    }

    fn due(&self, _: &u32, _: Time) -> Vec<echod_rover::Sched<()>> {
        Vec::new()
    }
}

impl echod_rover::Footprint for Twice {
    type Key = ();

    fn external_touches(&self, _: &Req) -> echod_rover::Touches<()> {
        echod_rover::Touches::one(())
    }

    fn internal_touches(&self, _: &()) -> echod_rover::Touches<()> {
        echod_rover::Touches::one(())
    }
}

fn plain() -> Certified<Plain<Twice>> {
    Certified(Checker::new(Twice, 0, Config { certify: true, ..Config::default() }))
}

fn keyed() -> Certified<Keyed<Twice>> {
    Certified(Checker::with_footprints(Twice, 0, Config { certify: true, ..Config::default() }))
}

#[test]
fn work_started_twice_runs_twice() {
    // Both increments may have run by the read, and no more than both.
    let mut c = plain();
    c.call(1, Req::Bump, 0).unwrap();
    assert!(c.call(2, Req::Read, 3).is_err(), "only two increments were started");
    c.call(3, Req::Read, 2).unwrap();

    let mut c = keyed();
    c.call(1, Req::Bump, 0).unwrap();
    c.call(2, Req::Read, 1).unwrap(); // one has run, one is pending
    c.call(3, Req::Read, 2).unwrap();
    assert!(c.call(4, Req::Read, 3).is_err());
}
