//! Driving a model and recording the choices: a run is valid, and replaying
//! its choices reproduces it.

use accordant::{certify, drive, Checker, Choice, Choices, Config, Drive, Event, Explore, ExternalOutcome, InternalOutcome, Model, Time, Tried};

/// A mailbox: `Put(v)` stores `v` and, later, sends it to a client; `Get`
/// reads what is stored.
struct Mailbox;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Req {
    Put(u8),
    Get,
}

impl Model for Mailbox {
    type State = Option<u8>;
    type External = Req;
    type Response = Option<u8>;
    type Internal = u8;
    type Dispatch = u8;

    fn external(&self, req: &Req, s: &Option<u8>) -> Vec<ExternalOutcome<Self>> {
        match req {
            Req::Put(v) => vec![ExternalOutcome::new(*s, Some(*v)).later(*v).mark("put")],
            Req::Get => vec![ExternalOutcome::same(*s, s).mark("get")],
        }
    }

    fn internal(&self, v: &u8, s: &Option<u8>) -> Vec<InternalOutcome<Self>> {
        vec![InternalOutcome::same(s).send(*v).mark("sent")]
    }

    fn now(&self, _: &Option<u8>) -> Time {
        0
    }
}

impl Explore for Mailbox {
    fn suggest(&self, s: &Option<u8>) -> Vec<(Req, &'static str)> {
        match s {
            Some(v) => vec![(Req::Put(v.wrapping_add(1)), "put the next value")],
            None => vec![(Req::Put(0), "put the first value")],
        }
    }

    fn arbitrary(&self, _: &Option<u8>, pick: &mut dyn FnMut(usize) -> usize) -> Req {
        if pick(2) == 0 { Req::Get } else { Req::Put(pick(4) as u8) }
    }

    /// Acts on the oldest value it was sent: puts it again, offset by 100 so
    /// a test can tell a request built from the inbox.
    fn informed(&self, _: &Option<u8>, inbox: &mut Vec<u8>, _: &mut dyn FnMut(usize) -> usize) -> Option<Req> {
        (!inbox.is_empty()).then(|| Req::Put(100 + inbox.remove(0) % 100))
    }

    fn finish(&self, _: &Option<u8>) -> Vec<Req> {
        vec![Req::Get]
    }
}

#[test]
fn a_driven_run_is_valid() {
    for seed in 1..=50 {
        let run = drive(&Mailbox, None, &Drive::default(), Choices::random(seed));
        let cert = Checker::new(Mailbox, None, Config::default())
            .check_certified(run.trace.clone())
            .unwrap_or_else(|v| panic!("seed {seed}: {v}"));
        assert_eq!(certify(&Mailbox, None, &run.trace, &cert), Ok(()));
        assert!(!run.choices.is_empty());
        assert!(run.choices.iter().all(|c| c.k < c.n && c.n > 1));
    }
}

#[test]
fn replaying_the_choices_reproduces_the_run() {
    for seed in 1..=50 {
        let run = drive(&Mailbox, None, &Drive::default(), Choices::random(seed));
        let again = drive(&Mailbox, None, &Drive::default(), Choices::replay(&run.choices));
        assert_eq!(again.trace, run.trace, "seed {seed}");
        assert_eq!(again.choices, run.choices, "seed {seed}");
    }
}

#[test]
fn edited_choices_still_drive_a_valid_run() {
    let run = drive(&Mailbox, None, &Drive::default(), Choices::random(7));
    // Keep the first half of the decisions; the rest become the first
    // alternative, as a shrinker would try.
    let half: Vec<Choice> = run.choices[..run.choices.len() / 2].to_vec();
    let shorter = drive(&Mailbox, None, &Drive::default(), Choices::replay(&half));
    assert!(Checker::new(Mailbox, None, Config::default()).check_certified(shorter.trace).is_ok());
}

#[test]
fn a_run_that_learned_across_runs_replays_without_the_memory() {
    // The memory only steers which index a random choice takes; the index is
    // what is recorded, so a replay needs nothing else.
    let tried = Tried::default();
    for seed in 1..=20 {
        let run = drive(&Mailbox, None, &Drive::default(), Choices::random(seed).learning(&tried));
        let again = drive(&Mailbox, None, &Drive::default(), Choices::replay(&run.choices));
        assert_eq!(again.trace, run.trace, "seed {seed}");
    }
    assert!(tried.count("put the first value") > 0);
}

#[test]
fn an_informed_run_acts_on_what_it_was_sent_and_replays() {
    let cfg = Drive { informed: true, ..Drive::default() };
    let mut acted = false;
    for seed in 1..=50 {
        let run = drive(&Mailbox, None, &cfg, Choices::random(seed));
        let cert = Checker::new(Mailbox, None, Config::default())
            .check_certified(run.trace.clone())
            .unwrap_or_else(|v| panic!("seed {seed}: {v}"));
        assert_eq!(certify(&Mailbox, None, &run.trace, &cert), Ok(()));
        let again = drive(&Mailbox, None, &cfg, Choices::replay(&run.choices));
        assert_eq!(again.trace, run.trace, "seed {seed}");
        acted |= run.trace.iter().any(|e| matches!(e, Event::Invoke { req: Req::Put(v), .. } if *v >= 100));
    }
    assert!(acted, "no request was built from a dispatch");
}
