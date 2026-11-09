//! History-checker footprints and partitions.
//!
//! This says which keys a request touches and which origin a key belongs to.
//! `timeout_work` is the list of steps a timeout may run; the handler decides
//! which of them do anything.

use vstd::prelude::*;

use echod_rover::{Footprint, Partitioned, Sched, Touches};
use echod_types::{Request, TaskFenceAction};

use super::super::machine::*;
use super::super::trusted::expand;

/// What a footprint names: a promise with its task, a schedule, or a whole
/// origin (what a schedule's future occurrences will touch).
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Key {
    Object(Id),
    Schedule(Id),
    Origin(String),
}

impl Key {
    fn group(&self) -> String {
        match self {
            Key::Object(id) | Key::Schedule(id) => origin(id).to_string(),
            Key::Origin(o) => o.clone(),
        }
    }
}

pub(crate) fn origin(id: &str) -> &str {
    echod_types::origin_of(id)
}

/// The origin every occurrence of a schedule's promise template expands to,
/// if it is one: `None` when the template's origin part carries the
/// timestamp, so each occurrence lands in an origin of its own.
fn template_origin(template: &str, schedule: &str) -> Option<String> {
    let t = template.replace("{{.id}}", schedule);
    let o = origin(&t);
    if o.contains("{{.timestamp}}") {
        None
    } else {
        Some(o.to_string())
    }
}

pub fn next_cron(cron: &str, after_ms: u64) -> u64 {
    echod_cron::next_run_at(cron, after_ms)
}

// ------------------------------------------------------------------ the traits

impl Default for ServerConfig {
    /// Lean's `ServerConfig.retryTimeout`: 5000. Schedules fire at the instant.
    fn default() -> Self {
        ServerConfig { retry_timeout: 5_000 }
    }
}

impl Footprint for ServerConfig {
    type Key = Key;

    fn external_touches(&self, op: &Request) -> Touches<Key> {
        let ks = |v: &[&Id]| Touches::Only(v.iter().map(|k| Key::Object((*k).clone())).collect());
        match op {
            Request::PromiseCreate(c) => ks(&[&c.id]),
            Request::PromiseSettle(st) => ks(&[&st.id]),
            Request::TaskCreate(t) => ks(&[&t.action.id]),
            Request::PromiseGet(q) => ks(&[&q.id]),
            Request::TaskGet(q) => ks(&[&q.id]),
            Request::TaskAcquire(q) => ks(&[&q.id]),
            Request::TaskRelease(q) => ks(&[&q.id]),
            Request::TaskFulfill(q) => ks(&[&q.id]),
            Request::TaskHalt(q) => ks(&[&q.id]),
            Request::TaskContinue(q) => ks(&[&q.id]),
            Request::TaskFenceCheck(q) => ks(&[&q.id]),
            Request::TaskHeartbeat(h) => {
                let v: Vec<&Id> = h.tasks.iter().map(|t| &t.id).collect();
                ks(&v)
            }
            // A request refused for crossing origins is refused on the ids alone and
            // reads nothing, so its footprint stays in one origin.
            Request::PromiseRegisterCallback(c) if origin(&c.awaited) != origin(&c.awaiter) => ks(&[&c.awaited]),
            Request::PromiseRegisterCallback(c) => ks(&[&c.awaited, &c.awaiter]),
            Request::PromiseRegisterListener(c) => ks(&[&c.awaited]),
            Request::TaskSuspend(s) if s.actions.iter().any(|a| origin(&a.awaited) != origin(&s.id)) => ks(&[&s.id]),
            Request::TaskSuspend(s) => {
                let mut v: Vec<&Id> = s.actions.iter().map(|a| &a.awaited).collect();
                v.push(&s.id);
                ks(&v)
            }
            Request::TaskFence(f) => match &f.action {
                TaskFenceAction::Settle(st) if origin(&st.id) != origin(&f.id) => ks(&[&f.id]),
                TaskFenceAction::Settle(st) => ks(&[&f.id, &st.id]),
                TaskFenceAction::Create(c) => ks(&[&f.id, &c.id]),
            },
            // A schedule's occurrences will touch the origin its template names.
            Request::ScheduleCreate(c) => match template_origin(&c.promise_id, &c.id) {
                Some(o) => Touches::Only(vec![Key::Schedule(c.id.clone()), Key::Origin(o)]),
                None => Touches::Everything,
            },
            Request::ScheduleGet(q) => Touches::one(Key::Schedule(q.id.clone())),
            Request::ScheduleDelete(q) => Touches::one(Key::Schedule(q.id.clone())),
        }
    }

    fn internal_touches(&self, step: &Work) -> Touches<Key> {
        match step {
            Work::PromiseTimeout(id) | Work::TaskLeaseTimeout(id) | Work::TaskRetryTimeout(id) | Work::Listener { awaited: id, .. } => {
                Touches::one(Key::Object(id.clone()))
            }
            Work::Callback { awaited, awaiter } => Touches::Only(vec![Key::Object(awaited.clone()), Key::Object(awaiter.clone())]),
            Work::ScheduleTimeout { id, promise } => Touches::Only(vec![Key::Schedule(id.clone()), Key::Object(promise.clone())]),
            Work::Occurrence { promise, .. } => Touches::one(Key::Object(promise.clone())),
        }
    }

    fn state_spans(&self, s: &Store) -> Vec<Touches<Key>> {
        s.schedules
            .iter()
            .map(|(id, c)| match template_origin(&c.promise_id, id) {
                Some(o) => Touches::Only(vec![Key::Schedule(id.clone()), Key::Origin(o)]),
                None => Touches::Everything,
            })
            .collect()
    }

    fn dispatch_touches(&self, msg: &Dispatch) -> Touches<Key> {
        match msg {
            Dispatch::Execute { id, .. } => Touches::one(Key::Object(id.clone())),
            Dispatch::Unblock { promise, .. } => Touches::one(Key::Object(promise.id.clone())),
        }
    }
}

impl Partitioned for ServerConfig {
    type Group = String;

    /// Ids of different origins never interact, except a schedule whose
    /// template names another origin. That footprint spans origins and merges
    /// the partitions; the checker splits them again once the candidates are
    /// independent. A fence that names another origin is refused.
    fn group(&self, key: &Key) -> String {
        key.group()
    }

    fn restrict(&self, s: &Store, keep: &dyn Fn(&String) -> bool) -> Store {
        let mine = |k: &Id| keep(&origin(k).to_string());
        Store {
            promises: s.promises.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
            tasks: s.tasks.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
            schedules: s.schedules.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
        }
    }

    fn join(&self, a: &Store, b: &Store) -> Store {
        let mut n = a.clone();
        for (k, v) in b.promises.iter() {
            n.promises.insert(k.clone(), v.clone());
        }
        for (k, v) in b.tasks.iter() {
            n.tasks.insert(k.clone(), v.clone());
        }
        for (k, v) in b.schedules.iter() {
            n.schedules.insert(k.clone(), v.clone());
        }
        n
    }
}

// The checker calls this from inside `verus!`; Verus sees the signature alone.
verus! {

/// The steps an object or schedule offers, keeping those the handler will
/// perform. Occurrences are not here: a schedule step queues those, and the
/// queue is the only one. The handler is the guard.
#[verifier::external_body]
pub fn timeout_work(m: &ServerConfig, s: &Store, now: Time) -> Vec<Sched<Work>> {
    timeout_work_plain(m, s, now)
}

} // verus!

fn timeout_work_plain(m: &ServerConfig, s: &Store, now: Time) -> Vec<Sched<Work>> {
    let mut v = Vec::new();
    for (id, p) in s.promises.iter() {
        runs(m, s, now, &mut v, Sched::Timer(p.timeout_at, Work::PromiseTimeout(id.clone())));
        for awaiter in p.callbacks.to_vec() {
            runs(m, s, now, &mut v, Sched::Later(Work::Callback { awaited: id.clone(), awaiter }));
        }
        for address in p.listeners.to_vec() {
            runs(m, s, now, &mut v, Sched::Later(Work::Listener { awaited: id.clone(), address }));
        }
    }
    for (id, t) in s.tasks.iter() {
        runs(m, s, now, &mut v, Sched::Timer(t.lease_timeout_at(), Work::TaskLeaseTimeout(id.clone())));
        if let Some(r) = t.retry_timeout_at {
            runs(m, s, now, &mut v, Sched::Timer(r, Work::TaskRetryTimeout(id.clone())));
        }
    }
    for (id, c) in s.schedules.iter() {
        let promise = expand(&c.promise_id, id, c.next_run_at);
        runs(m, s, now, &mut v, Sched::Timer(c.next_run_at, Work::ScheduleTimeout { id: id.clone(), promise }));
    }
    v
}

fn runs(m: &ServerConfig, s: &Store, now: Time, v: &mut Vec<Sched<Work>>, step: Sched<Work>) {
    if !m.process_work(step.req(), s, now).not_due {
        v.push(step);
    }
}
