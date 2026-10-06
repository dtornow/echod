//! What the fuzz example adds to `accordant::drive`: Resonate with a bug
//! planted (the system the driver runs), and checking a recorded trace against
//! the spec itself.

use std::collections::BTreeSet;
use std::fmt::Write;

use accordant::{marks, Checker, Config, Event, Explore, ExternalOutcome, InternalOutcome, Keyed, Model, Time, Verdict, Violation};
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
    /// An acquire at a stale version goes through: a worker acting on an
    /// old offer runs a task someone else already ran.
    StaleAcquire,
}

impl Bug {
    pub fn parse(s: &str) -> Bug {
        match s {
            "none" => Bug::None,
            "stale-fence" => Bug::StaleFence,
            "lease-forever" => Bug::LeaseForever,
            "stale-acquire" => Bug::StaleAcquire,
            _ => panic!("unknown bug {s}: none, stale-fence, lease-forever or stale-acquire"),
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
            (Bug::StaleAcquire, Request::AcquireTask { id, version: _, pid, ttl }) => match s.tasks.get(id) {
                Some(t) => Request::AcquireTask { id: id.clone(), version: t.version, pid: pid.clone(), ttl: *ttl },
                None => op.clone(),
            },
            _ => op.clone(),
        };
        Model::external(&Resonate, &op, s)
            .into_iter()
            .map(|o| ExternalOutcome { next: o.next, resp: o.resp, work: o.work, send: o.send, marks: o.marks })
            .collect()
    }

    fn internal(&self, ids: &Internal, s: &Self::State) -> Vec<InternalOutcome<Self>> {
        let outs = Model::internal(&Resonate, ids, s);
        if self.bug == Bug::LeaseForever && outs.iter().any(|o| !o.send.is_empty()) {
            return vec![InternalOutcome::same(s)];
        }
        outs.into_iter().map(|o| InternalOutcome { next: o.next, work: o.work, send: o.send, marks: o.marks }).collect()
    }

    fn now(&self, s: &Self::State) -> Time {
        s.now
    }
}

/// The same requests as the spec: the bug is in what the server does, not in
/// what a client sends.
impl Explore for Server {
    fn suggest(&self, s: &Self::State) -> Vec<(Request, &'static str)> {
        Resonate.suggest(s)
    }

    fn arbitrary(&self, s: &Self::State, pick: &mut dyn FnMut(usize) -> usize) -> Request {
        Resonate.arbitrary(s, pick)
    }

    fn informed(&self, s: &Self::State, inbox: &mut Vec<Dispatch>, pick: &mut dyn FnMut(usize) -> usize) -> Option<Request> {
        Resonate.informed(s, inbox, pick)
    }

    fn finish(&self, s: &Self::State) -> Vec<Request> {
        Resonate.finish(s)
    }
}

pub type Trace = Vec<Event<Request, Response, Dispatch>>;

/// How a recorded trace is checked.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Check {
    /// One event at a time, every explanation kept, as a monitor would
    /// ([`Checker::check`]).
    Online,
    /// The run is over, so the whole trace is known: depth first, committing
    /// to one explanation and backtracking ([`Checker::check_complete`]).
    /// Long runs need it: at 10,000 requests the online profile outgrows
    /// `max_width`.
    Complete,
}

impl Check {
    pub fn parse(s: &str) -> Check {
        match s {
            "online" => Check::Online,
            "complete" => Check::Complete,
            _ => panic!("unknown check {s}: online or complete"),
        }
    }
}

pub enum Outcome {
    /// Accepted, with the marks of the execution that explains it.
    Ok(BTreeSet<&'static str>),
    Ko(Violation),
    Unknown(Violation),
}

/// Checks a recorded trace against the spec. `cross`: also with the
/// partitioned and depth-first checkers (only meaningful when the trace came
/// from the spec itself, where every trace is valid).
pub fn check(trace: &Trace, how: Check, cross: bool) -> Outcome {
    let mut c: Checker<Keyed<Resonate>> = Checker::with_footprints(Resonate, resonate::Server::default(), Config { certify: true, ..Config::default() });
    let verdict = match how {
        Check::Online => c.check_certified(trace.clone()),
        Check::Complete => c.check_complete(trace).map(|_| ()).and_then(|()| c.certified()),
    };
    if cross {
        let mut g = Checker::with_partitions(Resonate, resonate::Server::default(), Config::default());
        let mut d = Checker::with_footprints(Resonate, resonate::Server::default(), Config::default());
        for (name, r) in [("partitioned", g.check(trace.clone()).map(|_| ())), ("depth-first", d.check_complete(trace).map(|_| ()))] {
            if let Err(mut v) = r {
                v.reason = format!("{name} checker: {}", v.reason);
                return Outcome::Ko(v);
            }
        }
    }
    match Verdict::from(verdict) {
        Verdict::Ok(cert) => Outcome::Ok(marks(&Resonate, resonate::Server::default(), trace, &cert).expect("the certificate replays")),
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
        };
        let _ = writeln!(out, "{i:>3}  {line}");
    }
    out
}
