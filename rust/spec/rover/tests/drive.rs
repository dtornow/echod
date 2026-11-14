//! Driving a model and recording the choices: a run is valid, and replaying
//! its choices reproduces it.

use echod_rover::{certify, drive, Action, Checker, Choice, Choices, Config, Drive, Explore, ExternalOutcome, InternalOutcome, Model, Time, Tried};

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

    fn external(&self, req: &Req, s: &Option<u8>, _: Time) -> Vec<ExternalOutcome<Self>> {
        match req {
            Req::Put(v) => vec![ExternalOutcome::new(*s, Some(*v)).later(*v).mark("put")],
            Req::Get => vec![ExternalOutcome::same(*s, s).mark("get")],
        }
    }

    fn internal(&self, v: &u8, s: &Option<u8>, _: Time) -> Vec<InternalOutcome<Self>> {
        vec![InternalOutcome::same(s).send(*v).mark("sent")]
    }

    fn due(&self, _: &Option<u8>, _: Time) -> Vec<echod_rover::Sched<u8>> {
        Vec::new()
    }
}

impl Explore for Mailbox {
    fn suggest(&self, s: &Option<u8>, _: Time) -> Vec<(Action<Req>, &'static str)> {
        match s {
            Some(v) => vec![(Action::Request(Req::Put(v.wrapping_add(1))), "put the next value")],
            None => vec![(Action::Request(Req::Put(0)), "put the first value")],
        }
    }

    fn arbitrary(&self, _: &Option<u8>, now: Time, pick: &mut dyn FnMut(usize) -> usize) -> Action<Req> {
        match pick(3) {
            0 => Action::Request(Req::Get),
            1 => Action::Request(Req::Put(pick(4) as u8)),
            _ => Action::Clock(now + pick(3) as Time),
        }
    }

    fn finish(&self, _: &Option<u8>, _: Time) -> Vec<Action<Req>> {
        vec![Action::Request(Req::Get)]
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
