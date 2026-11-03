//! The glue between the verified model and the checker: plain Rust, outside
//! Verus. It says which keys a request touches and which origin a key belongs
//! to, and holds the cron engine the spec trusts. None of it decides what the
//! server does: the `Model` impl itself is verified, in `spec.rs`.

use echod_rover::{Footprint, Partitioned, Sched, Touches};
use echod_types::{Request, TaskFenceAction, TaskState};

use super::exec::*;

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

pub(crate) fn cron_valid(cron: &str) -> bool {
    echod_cron::valid(cron)
}

pub fn next_cron(cron: &str, after_ms: u64) -> u64 {
    echod_cron::next_run_at(cron, after_ms)
}

pub(crate) fn expand(template: &str, id: &str, at: u64) -> String {
    template.replace("{{.id}}", id).replace("{{.timestamp}}", &at.to_string())
}

// ------------------------------------------------------------------ the traits

impl Default for Resonate {
    /// Lean's `ServerConfig.retryTimeout`: 5000. Schedules fire at the instant.
    fn default() -> Self {
        Resonate { retry_timeout: 5_000, fire_within: 0 }
    }
}

impl Footprint for Resonate {
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
            Work::PromiseTimeout(id) | Work::Lease(id) | Work::Retry(id) | Work::Listener { awaited: id, .. } => {
                Touches::one(Key::Object(id.clone()))
            }
            Work::Callback { awaited, awaiter } => Touches::Only(vec![Key::Object(awaited.clone()), Key::Object(awaiter.clone())]),
            Work::Schedule { id, promise } => Touches::Only(vec![Key::Schedule(id.clone()), Key::Object(promise.clone())]),
            Work::Occurrence { promise, .. } => Touches::one(Key::Object(promise.clone())),
        }
    }

    fn state_spans(&self, s: &Server) -> Vec<Touches<Key>> {
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

impl Partitioned for Resonate {
    type Group = String;

    /// Ids of different origins never interact, except through a detached create
    /// (`FenceTask` creating in another origin) and a schedule whose template
    /// names another origin. Their footprints span origins and merge the
    /// partitions; the checker splits them again once the candidates are
    /// independent.
    fn group(&self, key: &Key) -> String {
        key.group()
    }

    fn restrict(&self, s: &Server, keep: &dyn Fn(&String) -> bool) -> Server {
        let mine = |k: &Id| keep(&origin(k).to_string());
        Server {
            promises: s.promises.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
            tasks: s.tasks.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
            schedules: s.schedules.iter().filter(|(k, _)| mine(k)).map(|(k, v)| (k.clone(), v.clone())).collect(),
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
        for (k, v) in b.schedules.iter() {
            n.schedules.insert(k.clone(), v.clone());
        }
        n
    }
}

/// What the maps and the clock make due, one item each. Occurrences are not
/// here: a schedule step queues those, and the queue is the only one.
pub fn due(_m: &Resonate, s: &Server, now: Time) -> Vec<Sched<Work>> {
    let mut v = Vec::new();
    for (id, p) in s.promises.iter() {
        if p.live() && now >= p.timeout_at {
            v.push(Sched::Timer(p.timeout_at, Work::PromiseTimeout(id.clone())));
        }
        if !p.live() {
            for awaiter in p.callbacks.to_vec() {
                v.push(Sched::Later(Work::Callback { awaited: id.clone(), awaiter }));
            }
            for address in p.listeners.to_vec() {
                v.push(Sched::Later(Work::Listener { awaited: id.clone(), address }));
            }
        }
    }
    for (id, t) in s.tasks.iter() {
        if t.state == TaskState::Acquired && now >= t.lease_expires() {
            v.push(Sched::Timer(t.lease_expires(), Work::Lease(id.clone())));
        }
        if t.state == TaskState::Pending {
            if let Some(r) = t.retry_at {
                let live = s.promises.get(id).is_some_and(|p| p.live());
                if r <= now && live {
                    v.push(Sched::Timer(r, Work::Retry(id.clone())));
                }
            }
        }
    }
    for (id, c) in s.schedules.iter() {
        if c.next_run_at <= now {
            let promise = expand(&c.promise_id, id, c.next_run_at);
            v.push(Sched::Timer(c.next_run_at, Work::Schedule { id: id.clone(), promise }));
        }
    }
    v
}
