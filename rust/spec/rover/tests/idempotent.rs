//! A request that changes nothing in one state and something in another, with
//! the same answer either way: a `Raise` of a flag already raised answers
//! `Done` like a `Raise` that raises it. The checker remembers the answer a
//! call could get where it changes nothing (an early answer) rather than
//! placing the call; the call may still take effect later, after other work
//! on its keys. Both must stay candidates.

use echod_rover::{Checker, Config, ExternalOutcome, Footprint, InternalOutcome, Model, Time, Touches};

struct Flag;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Req {
    Raise,
    Lower,
    Get,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Res {
    Done,
    Is(bool),
}

impl Model for Flag {
    type State = bool;
    type External = Req;
    type Response = Res;
    type Internal = ();
    type Dispatch = ();

    fn external(&self, req: &Req, s: &bool, _: Time) -> Vec<ExternalOutcome<Self>> {
        vec![match req {
            Req::Raise => ExternalOutcome::new(Res::Done, true),
            Req::Lower => ExternalOutcome::new(Res::Done, false),
            Req::Get => ExternalOutcome::same(Res::Is(*s), s),
        }]
    }

    fn internal(&self, _: &(), s: &bool, _: Time) -> Vec<InternalOutcome<Self>> {
        vec![InternalOutcome::same(s)]
    }
}

impl Footprint for Flag {
    type Key = ();

    fn external_touches(&self, _: &Req) -> Touches<()> {
        Touches::one(())
    }

    fn internal_touches(&self, _: &()) -> Touches<()> {
        Touches::one(())
    }
}

/// Raised; then a lower and a raise in flight together, both answered. The
/// flag may be up (the raise came last) or down (the lower did).
fn raise_and_lower_in_flight() -> Vec<Checker<echod_rover::Keyed<Flag>>> {
    let mut out = Vec::new();
    for _ in 0..2 {
        let mut c = Checker::with_footprints(Flag, false, Config::default());
        c.call(1, Req::Raise, Res::Done).unwrap();
        c.invoke(2, Req::Lower).unwrap();
        c.invoke(3, Req::Raise).unwrap();
        c.ret(3, Res::Done).unwrap(); // changed nothing, or came after the lower
        c.ret(2, Res::Done).unwrap();
        out.push(c);
    }
    out
}

#[test]
fn an_idempotent_request_may_take_effect_after_a_concurrent_one() {
    let mut cs = raise_and_lower_in_flight();
    cs[0].call(4, Req::Get, Res::Is(true)).unwrap_or_else(|v| panic!("the raise may have come last: {v}"));
    cs[1].call(4, Req::Get, Res::Is(false)).unwrap_or_else(|v| panic!("the lower may have come last: {v}"));
}

#[test]
fn an_unanswered_idempotent_request_is_not_forced() {
    let mut c = Checker::with_footprints(Flag, false, Config::default());
    c.call(1, Req::Raise, Res::Done).unwrap();
    c.invoke(2, Req::Raise).unwrap(); // never answered
    c.call(3, Req::Lower, Res::Done).unwrap();
    c.call(4, Req::Get, Res::Is(false)).unwrap();
    c.call(5, Req::Get, Res::Is(true)).unwrap(); // the open raise landed late
    assert!(c.call(6, Req::Get, Res::Is(false)).is_err(), "nothing lowers it again");
}
