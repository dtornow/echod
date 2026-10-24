//! What the fuzz example adds to `accordant::drive`: Resonate with a bug
//! planted (the system the driver runs), and checking a recorded trace against
//! the spec itself.

use std::collections::BTreeSet;
use std::fmt::Write;

use accordant::{marks, Action, Checker, Config, Event, Explore, ExternalOutcome, InternalOutcome, Keyed, Model, Time, Verdict, Violation};
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

    fn external(&self, op: &Request, s: &Self::State, now: Time) -> Vec<ExternalOutcome<Self>> {
        let op = match (self.bug, op) {
            (Bug::StaleFence, Request::FenceTask { id, version: _, action }) => match s.tasks.get(id) {
                Some(t) => Request::FenceTask { id: id.clone(), version: t.version, action: action.clone() },
                None => op.clone(),
            },
            _ => op.clone(),
        };
        Model::external(&Resonate::default(), &op, s, now)
            .into_iter()
            .map(|o| ExternalOutcome { next: o.next, resp: o.resp, work: o.work, send: o.send, marks: o.marks })
            .collect()
    }

    fn internal(&self, ids: &Internal, s: &Self::State, now: Time) -> Vec<InternalOutcome<Self>> {
        let outs = Model::internal(&Resonate::default(), ids, s, now);
        if self.bug == Bug::LeaseForever && outs.iter().any(|o| !o.send.is_empty()) {
            return vec![InternalOutcome::same(s)];
        }
        outs.into_iter().map(|o| InternalOutcome { next: o.next, work: o.work, send: o.send, marks: o.marks }).collect()
    }
}

/// The same actions as the spec: the bug is in what the server does, not in
/// what a client sends.
impl Explore for Server {
    fn suggest(&self, s: &Self::State, now: Time) -> Vec<(Action<Request>, &'static str)> {
        Resonate::default().suggest(s, now)
    }

    fn arbitrary(&self, s: &Self::State, now: Time, pick: &mut dyn FnMut(usize) -> usize) -> Action<Request> {
        Resonate::default().arbitrary(s, now, pick)
    }

    fn finish(&self, s: &Self::State, now: Time) -> Vec<Action<Request>> {
        Resonate::default().finish(s, now)
    }
}

pub type Trace = Vec<Event<Request, Response, Dispatch>>;

pub enum Outcome {
    /// Accepted, with the marks of the execution that explains it.
    Ok(BTreeSet<&'static str>),
    Ko(Violation),
    Unknown(Violation),
}

/// Checks a recorded trace against the spec. `cross`: also with the
/// partitioned and depth-first checkers (only meaningful when the trace came
/// from the spec itself, where every trace is valid).
pub fn check(trace: &Trace, cross: bool) -> Outcome {
    let mut c: Checker<Keyed<Resonate>> = Checker::with_footprints(Resonate::default(), resonate::Server::default(), Config { certify: true, ..Config::default() });
    let verdict = c.check_certified(trace.clone());
    if cross {
        let mut g = Checker::with_partitions(Resonate::default(), resonate::Server::default(), Config::default());
        let mut d = Checker::with_footprints(Resonate::default(), resonate::Server::default(), Config::default());
        for (name, r) in [("partitioned", g.check(trace.clone()).map(|_| ())), ("depth-first", d.check_complete(trace).map(|_| ()))] {
            if let Err(mut v) = r {
                v.reason = format!("{name} checker: {}", v.reason);
                return Outcome::Ko(v);
            }
        }
    }
    match Verdict::from(verdict) {
        Verdict::Ok(cert) => Outcome::Ok(marks(&Resonate::default(), resonate::Server::default(), trace, &cert).expect("the certificate replays")),
        Verdict::Ko(v) => Outcome::Ko(v),
        Verdict::Unknown(v) => Outcome::Unknown(v),
    }
}

/// A trace as a client saw it, one event per line, up to event `upto`.
pub fn show(trace: &Trace, upto: usize) -> String {
    let mut out = String::new();
    for (i, e) in trace.iter().enumerate().take(upto + 1) {
        let line = match e {
            Event::Invoke { call, req } => format!("call {call:>2} → {req:?}"),
            Event::Return { call, res } => format!("call {call:>2} ← {res:?}"),
            Event::Receive { msg } => format!("        ⇐ {msg:?}"),
            Event::Clock { at } => format!("        ⏲ clock {at}"),
        };
        let _ = writeln!(out, "{i:>3}  {line}");
    }
    out
}
