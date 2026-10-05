//! The fuzz driver. Every decision of a run (whether the client sends a
//! request now, which request, which move the server makes) comes from a
//! `Choices`: a seeded generator today; a recorded list of choices is what a
//! shrinker would replay and cut down.
//!
//! A client sends requests to a simulated server, the spec or the spec with a
//! bug planted; a checker follows what the client observes. A run ends with the
//! server idle and a client reading every object. An accepted run comes with a
//! certificate, and the marks along it are what the run covered.

use std::collections::BTreeSet;
use std::fmt::Write;

use accordant::{marks, CallId, Checker, Config, Event, ExternalOutcome, InternalOutcome, Keyed, Model, Sim, Time, Verdict, Violation};
use resonate::*;

/// The spec with a bug planted, or not.
pub struct Server {
    pub bug: Bug,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Bug {
    None,
    /// A fence at a stale version goes through, as if it held the task.
    StaleFence,
    /// A lease never expires: an abandoned task is never handed out again.
    LeaseForever,
}

impl Bug {
    pub fn parse(s: &str) -> Bug {
        match s {
            "none" => Bug::None,
            "stale-fence" => Bug::StaleFence,
            "lease-forever" => Bug::LeaseForever,
            _ => panic!("unknown bug {s}: none, stale-fence or lease-forever"),
        }
    }
}

impl Model for Server {
    type State = resonate::Server;
    type External = Request;
    type Response = Response;
    type Internal = Internal;
    type Dispatch = Dispatch;

    fn external(&self, op: &Request, s: &Self::State) -> Vec<ExternalOutcome<Self>> {
        let op = match (self.bug, op) {
            (Bug::StaleFence, Request::FenceTask { id, version: _, action }) => match s.tasks.get(id) {
                Some(t) => Request::FenceTask { id: id.clone(), version: t.version, action: action.clone() },
                None => op.clone(),
            },
            _ => op.clone(),
        };
        Model::external(&Resonate, &op, s)
            .into_iter()
            .map(|o| ExternalOutcome { next: o.next, resp: o.resp, work: o.work, send: o.send })
            .collect()
    }

    fn internal(&self, ids: &Internal, s: &Self::State) -> Vec<InternalOutcome<Self>> {
        let outs = Model::internal(&Resonate, ids, s);
        if self.bug == Bug::LeaseForever && outs.iter().any(|o| !o.send.is_empty()) {
            return vec![InternalOutcome { next: s.clone(), work: Vec::new(), send: Vec::new() }];
        }
        outs.into_iter().map(|o| InternalOutcome { next: o.next, work: o.work, send: o.send }).collect()
    }

    fn now(&self, s: &Self::State) -> Time {
        s.now
    }
}

/// Where a run's decisions come from.
pub trait Choices {
    /// A number below `n`: which move the server makes, whether the client
    /// sends a request now.
    fn pick(&self, n: usize) -> usize;

    /// The next request, given the latest time the clock was moved to and the
    /// model's suggestions for the states the server may be in.
    fn request(&self, clock: Time, suggestions: &[(Request, &'static str)]) -> Request;
}

pub type Trace = Vec<Event<Request, Response, Dispatch>>;

pub enum Outcome {
    /// Accepted, with the marks of the execution that explains it.
    Ok(BTreeSet<&'static str>),
    Ko(Violation, Trace),
    Unknown(Violation, Trace),
}

/// One run: a client sends `steps` requests, at most three in flight, while the
/// server makes its own moves; then the server goes idle and a client reads
/// everything. `cross`: also check the trace with the partitioned and
/// depth-first checkers (only meaningful against the spec itself, where every
/// trace is valid).
pub fn run(server: &Server, choices: &dyn Choices, steps: usize, cross: bool) -> Outcome {
    let mut sim = Sim::with_choices(server, resonate::Server::default(), |n| if n == 1 { 0 } else { choices.pick(n) });
    let mut c = Checker::with_footprints(Resonate, resonate::Server::default(), Config { certify: true, ..Config::default() });
    let mut events: Trace = Vec::new();
    let (mut clock, mut call, mut sent): (Time, CallId, usize) = (0, 0, 0);
    let mut observe = |c: &mut Checker<Keyed<Resonate>>, e: Event<Request, Response, Dispatch>| -> Result<(), Violation> {
        events.push(e.clone());
        c.observe(e)
    };
    let verdict = (|| {
        while sent < steps || sim.open_calls() > 0 {
            if sent < steps && sim.open_calls() < 3 && choices.pick(2) == 0 {
                let req = choices.request(clock, &c.suggestions(8));
                if let Request::AdvanceClock(t) = req {
                    clock = clock.max(t);
                }
                call += 1;
                sent += 1;
                let e = sim.invoke(call, req);
                observe(&mut c, e)?;
            } else if let Some(e) = sim.step() {
                observe(&mut c, e)?;
            } else if sent >= steps {
                break;
            }
        }
        for e in sim.settle() {
            observe(&mut c, e)?;
        }
        // The server goes idle; then a client reads everything. A step the spec
        // may put off (a lease expiring) can't be put off past this.
        sim.quiesce();
        c.assert_idle()?;
        for id in IDS {
            for req in [Request::GetTask(id.to_string()), Request::GetPromise(id.to_string())] {
                call += 1;
                let e = sim.invoke(call, req);
                observe(&mut c, e)?;
                for e in sim.settle() {
                    observe(&mut c, e)?;
                }
            }
        }
        c.certified()
    })();
    if cross {
        let mut g = Checker::with_partitions(Resonate, resonate::Server::default(), Config::default());
        let mut d = Checker::with_footprints(Resonate, resonate::Server::default(), Config::default());
        for (name, r) in [("partitioned", g.check(events.clone()).map(|_| ())), ("depth-first", d.check_complete(&events).map(|_| ()))] {
            if let Err(mut v) = r {
                v.reason = format!("{name} checker: {}", v.reason);
                return Outcome::Ko(v, events);
            }
        }
    }
    match Verdict::from(verdict) {
        Verdict::Ok(moves) => Outcome::Ok(marks(&Resonate, resonate::Server::default(), moves).expect("the certificate replays")),
        Verdict::Ko(v) => Outcome::Ko(v, events),
        Verdict::Unknown(v) => Outcome::Unknown(v, events),
    }
}

/// A trace as a client saw it, one event per line, up to the event the
/// checker stopped at.
pub fn show(trace: &Trace, upto: usize) -> String {
    let mut out = String::new();
    for (i, e) in trace.iter().enumerate().take(upto + 1) {
        let line = match e {
            Event::Invoke { call, req } => format!("call {call:>2} → {req:?}"),
            Event::Return { call, res } => format!("call {call:>2} ← {res:?}"),
            Event::Receive { msg } => format!("        ⇐ {msg:?}"),
        };
        let _ = writeln!(out, "{i:>3}  {line}");
    }
    out
}
