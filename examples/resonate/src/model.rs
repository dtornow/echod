//! The glue between the verified spec and the checker: plain Rust, outside
//! Verus. It converts outcomes to `accordant`'s types and says which ids a
//! request touches and which origin an id belongs to. None of it decides what
//! the server does.

use std::collections::BTreeSet;

use accordant::{ExternalOutcome, Footprint, InternalOutcome, Model, Partitioned, Sched, Time, Touches};

use crate::spec::*;

/// An internal step: the server processes these objects and does whatever is
/// due on them (a promise past its deadline times out, a task past its lease is
/// reclaimed, a suspended task whose awaited promise settled resumes). What is
/// due is read from the state and the clock, not from the step.
///
/// The step names every object it may touch, so its footprint is exact. A
/// promise deadline or a lease end is `{id}`; a resume is `{awaited, awaiter}`.
pub type Internal = BTreeSet<Id>;

pub fn on(ids: &[&str]) -> Internal {
    ids.iter().map(|i| i.to_string()).collect()
}

pub(crate) fn origin(id: &str) -> &str {
    id.split_once(':').map_or(id, |(o, _)| o)
}

/// Any absolute URL: a scheme, a colon, and a non-empty rest with no whitespace.
/// Stands in for C#'s `Uri.TryCreate(.., Absolute)` plus its scheme regex.
pub(crate) fn address_valid(addr: &str) -> bool {
    let a = addr.trim();
    let Some((scheme, rest)) = a.split_once(':') else { return false };
    let mut cs = scheme.chars();
    cs.next().is_some_and(|c| c.is_ascii_alphabetic())
        && cs.all(|c| c.is_ascii_alphanumeric() || "+.-".contains(c))
        && !rest.is_empty()
        && !rest.chars().any(char::is_whitespace)
}

fn sched(w: Work) -> Sched<Internal> {
    match w {
        Work::Later(ids) => Sched::Later(ids.into_iter().collect()),
        Work::Timer(at, ids) => Sched::Timer(at, ids.into_iter().collect()),
    }
}

impl Model for Resonate {
    type State = Server;
    type External = Request;
    type Response = Response;
    type Internal = Internal;
    type Dispatch = Dispatch;

    fn external(&self, op: &Request, s: &Server, now: Time) -> Vec<ExternalOutcome<Self>> {
        Resonate::external(self, op, s, now)
            .into_iter()
            .map(|o| ExternalOutcome { next: o.next, resp: o.resp, work: o.work.into_iter().map(sched).collect(), send: o.send, marks: o.marks })
            .collect()
    }

    fn internal(&self, ids: &Internal, s: &Server, now: Time) -> Vec<InternalOutcome<Self>> {
        let ids: Vec<Id> = ids.iter().cloned().collect();
        let o = Resonate::internal(self, &ids, s, now);
        vec![InternalOutcome { next: o.next, work: o.work.into_iter().map(sched).collect(), send: o.send, marks: o.marks }]
    }
}

impl Footprint for Resonate {
    type Key = Id;

    fn external_touches(&self, op: &Request) -> Touches<Id> {
        let ks = |v: &[&Id]| Touches::Only(v.iter().map(|k| (*k).clone()).collect());
        match op {
            Request::CreatePromise(c) => ks(&[&c.id]),
            Request::SettlePromise(st) => ks(&[&st.id]),
            Request::GetPromise(id)
            | Request::GetTask(id)
            | Request::CreateTask { id, .. }
            | Request::AcquireTask { id, .. }
            | Request::ReleaseTask { id, .. }
            | Request::FulfillTask { id, .. }
            | Request::HeartbeatTask { id, .. } => ks(&[id]),
            // A request refused for crossing origins is refused on the ids alone and
            // reads nothing, so its footprint stays in one origin.
            Request::RegisterCallback { awaited, awaiter } if origin(awaited) != origin(awaiter) => ks(&[awaited]),
            Request::RegisterCallback { awaited, awaiter } => ks(&[awaited, awaiter]),
            Request::RegisterListener { awaited, .. } => ks(&[awaited]),
            Request::SuspendTask { id, awaited, .. } if awaited.iter().any(|a| origin(a) != origin(id)) => ks(&[id]),
            Request::SuspendTask { id, awaited, .. } => {
                let mut v: Vec<&Id> = awaited.iter().collect();
                v.push(id);
                ks(&v)
            }
            Request::FenceTask { id, action: Fenced::Settle(st), .. } if origin(&st.id) != origin(id) => ks(&[id]),
            // A detached create: the one request that spans two origins.
            Request::FenceTask { id, action, .. } => ks(&[id, action.target()]),
        }
    }

    fn internal_touches(&self, ids: &Internal) -> Touches<Id> {
        Touches::Only(ids.iter().cloned().collect())
    }

    fn dispatch_touches(&self, msg: &Dispatch) -> Touches<Id> {
        match msg {
            Dispatch::Execute { id, .. } => Touches::one(id.clone()),
        }
    }
}

impl Partitioned for Resonate {
    type Group = String;

    /// Ids of different origins never interact, except through a detached create
    /// (`FenceTask` creating in another origin). Its footprint spans origins and
    /// merges the partitions; the checker splits them again once the candidates
    /// are independent.
    fn group(&self, id: &Id) -> String {
        origin(id).to_string()
    }

    fn restrict(&self, s: &Server, keep: &dyn Fn(&Id) -> bool) -> Server {
        let mine = |k: &Id| keep(&origin(k).to_string());
        Server {
            promises: s.promises.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
            tasks: s.tasks.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
        }
    }

    fn join(&self, a: &Server, b: &Server) -> Server {
        let mut n = a.clone();
        for (k, v) in b.promises.iter() {
            n.promises.insert(k.clone(), v.clone());
        }
        for (k, v) in b.tasks.iter() {
            n.tasks.insert(k.clone(), v.clone());
        }
        n
    }
}
