//! The glue between the verified spec and the checker: plain Rust, outside
//! Verus. It converts outcomes to `accordant`'s types, says which keys a
//! request touches and which origin a key belongs to, and holds the cron
//! engine the spec trusts. None of it decides what the server does.

use std::collections::BTreeSet;

use accordant::{ExternalOutcome, Footprint, InternalOutcome, Model, Partitioned, Sched, Time, Touches};

use crate::spec::*;

/// An internal step, as the checker schedules it. `On`: the server processes
/// these objects and does whatever is due on them (a promise past its deadline
/// times out, a task past its lease is reclaimed, a suspended task whose awaited
/// promise settled resumes, a pending task due for a retry is dispatched, a
/// settled promise's listeners are told). What is due is read from the state and
/// the clock, not from the step. `Fire`: a schedule's occurrence.
///
/// The step names every object it may touch, so its footprint is exact. A
/// promise deadline, a lease end or a retry is `{id}`; a resume is `{awaited,
/// awaiter}`; a fire is the schedule and the promise it creates.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Internal {
    On(BTreeSet<Id>),
    Fire { schedule: Id, at: Time, promise: Id },
}

pub fn on(ids: &[&str]) -> Internal {
    Internal::On(ids.iter().map(|i| i.to_string()).collect())
}

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
    id.split_once(':').map_or(id, |(o, _)| o)
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

// --------------------------------------------------------------- the cron engine
//
// What the reference server does (`resonate-core/src/util.rs`): five fields get
// a leading `0` for the seconds; the next occurrence is the first strictly
// after `after`, in whole seconds. The `cron` crate names no instant past the
// year 2099; a later `after` is read at the latest year up to 2099 with the
// same month, day and weekday, and the answer shifted back.

fn normalize_cron(cron: &str) -> String {
    if cron.split_whitespace().count() == 5 {
        format!("0 {}", cron.trim())
    } else {
        cron.trim().to_string()
    }
}

pub(crate) fn cron_valid(cron: &str) -> bool {
    use std::str::FromStr;
    cron::Schedule::from_str(&normalize_cron(cron)).is_ok()
}

pub(crate) fn next_cron(cron: &str, after_ms: u64) -> u64 {
    use chrono::{Datelike, Timelike};
    use std::str::FromStr;
    let fallback = after_ms.saturating_add(60_000).max(after_ms + 1);
    let Ok(schedule) = cron::Schedule::from_str(&normalize_cron(cron)) else { return fallback };
    let after_secs = (after_ms / 1000) as i64;
    let Some(after_dt) = chrono::DateTime::from_timestamp(after_secs, 0) else { return fallback };
    const MAX_CRON_YEAR: i32 = 2099;
    let (ref_dt, delta_secs) = if after_dt.year() <= MAX_CRON_YEAR {
        (after_dt, 0i64)
    } else {
        let naive = after_dt.naive_utc();
        let (month, day, hour, minute, second) = (naive.month(), naive.day(), naive.hour(), naive.minute(), naive.second());
        let weekday = naive.weekday();
        let leap_day = month == 2 && day == 29;
        let equiv = (1970i32..=MAX_CRON_YEAR).rev().find_map(|y| {
            if leap_day && chrono::NaiveDate::from_ymd_opt(y, 2, 29).is_none() {
                return None;
            }
            chrono::NaiveDate::from_ymd_opt(y, month, day).filter(|d| d.weekday() == weekday).and_then(|d| d.and_hms_opt(hour, minute, second)).map(|dt| dt.and_utc().timestamp())
        });
        match equiv.and_then(|secs| chrono::DateTime::from_timestamp(secs, 0).map(|dt| (dt, after_secs - secs))) {
            Some(x) => x,
            None => (after_dt, 0),
        }
    };
    match schedule.after(&ref_dt).next() {
        Some(next) => {
            let ms = (next.timestamp() + delta_secs).saturating_mul(1000);
            if ms < 0 {
                fallback
            } else {
                (ms as u64).max(after_ms + 1)
            }
        }
        None => fallback,
    }
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

fn step(s: Step) -> Internal {
    match s {
        Step::Objects(ids) => Internal::On(ids.into_iter().collect()),
        Step::Fire { schedule, at, promise } => Internal::Fire { schedule, at, promise },
    }
}

fn sched(w: Work) -> Sched<Internal> {
    match w {
        Work::Later(s) => Sched::Later(step(s)),
        Work::Timer(at, s) => Sched::Timer(at, step(s)),
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

    fn internal(&self, step: &Internal, s: &Server, now: Time) -> Vec<InternalOutcome<Self>> {
        let o = match step {
            Internal::On(ids) => {
                let ids: Vec<Id> = ids.iter().cloned().collect();
                Resonate::internal(self, &ids, s, now)
            }
            Internal::Fire { schedule, at, promise } => Resonate::fire(self, schedule, *at, promise, s, now),
        };
        if o.pending {
            return Vec::new(); // not yet: the work stays
        }
        vec![InternalOutcome { next: o.next, work: o.work.into_iter().map(sched).collect(), send: o.send, marks: o.marks }]
    }
}

impl Footprint for Resonate {
    type Key = Key;

    fn external_touches(&self, op: &Request) -> Touches<Key> {
        let ks = |v: &[&Id]| Touches::Only(v.iter().map(|k| Key::Object((*k).clone())).collect());
        match op {
            Request::CreatePromise(c) => ks(&[&c.id]),
            Request::SettlePromise(st) => ks(&[&st.id]),
            Request::CreateTask { action, .. } => ks(&[&action.id]),
            Request::GetPromise(id)
            | Request::GetTask(id)
            | Request::AcquireTask { id, .. }
            | Request::ReleaseTask { id, .. }
            | Request::FulfillTask { id, .. }
            | Request::HaltTask(id)
            | Request::ContinueTask(id) => ks(&[id]),
            Request::HeartbeatTask { tasks, .. } => {
                let v: Vec<&Id> = tasks.iter().map(|t| &t.id).collect();
                ks(&v)
            }
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
            // A schedule's occurrences will touch the origin its template names.
            Request::CreateSchedule(c) => match template_origin(&c.promise_id, &c.id) {
                Some(o) => Touches::Only(vec![Key::Schedule(c.id.clone()), Key::Origin(o)]),
                None => Touches::Everything,
            },
            Request::GetSchedule(id) | Request::DeleteSchedule(id) => Touches::one(Key::Schedule(id.clone())),
        }
    }

    fn internal_touches(&self, step: &Internal) -> Touches<Key> {
        match step {
            Internal::On(ids) => Touches::Only(ids.iter().map(|id| Key::Object(id.clone())).collect()),
            Internal::Fire { schedule, promise, .. } => Touches::Only(vec![Key::Schedule(schedule.clone()), Key::Object(promise.clone())]),
        }
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
