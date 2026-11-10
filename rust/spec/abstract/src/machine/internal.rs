//! Mathematical internal-work transitions.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]
use vstd::prelude::*;
use echod_rover::rover::comm::Sched;
use echod_types::{PromiseState, TaskState, Value};
use super::*;
use super::super::trusted::*;
use super::super::view::*;

verus! {
// ---------------------------------------------------------------------------
// Work, as a specification
// ---------------------------------------------------------------------------

pub open spec fn spec_noop(s: StoreV) -> InOutV {
    InOutV { next: s, work: Seq::empty(), send: Seq::empty(), not_due: true }
}

pub open spec fn spec_did(next: StoreV, work: Seq<Sched<InternalV>>, send: Seq<DispatchV>) -> InOutV {
    InOutV { next, work, send, not_due: false }
}

pub open spec fn spec_unchanged(s: StoreV) -> InOutV {
    InOutV { next: s, work: Seq::empty(), send: Seq::empty(), not_due: false }
}

pub open spec fn spec_body(item: Sched<InternalV>) -> InternalV {
    match item {
        Sched::Later(work) => work,
        Sched::Timer(_, work) => work,
    }
}

pub open spec fn spec_process_work(config: ServerConfig, step: InternalV, s: StoreV, now: Time) -> InOutV {
    match step {
        InternalV::PromiseTimeout(id) => {
            if !s.promises.contains_key(id) {
                spec_noop(s)
            } else {
                let stored = s.promises[id];
                let q = spec_project_promise(stored, now);
                if q.state == stored.state && q.settled_at == stored.settled_at {
                    spec_noop(s)
                } else {
                    let tasks = if s.tasks.contains_key(id) {
                        s.tasks.insert(id, spec_project_task(s.tasks[id], q))
                    } else {
                        s.tasks
                    };
                    spec_did(StoreV { promises: s.promises.insert(id, q), tasks, ..s }, Seq::empty(), Seq::empty())
                }
            }
        },
        InternalV::Callback { awaited, awaiter } => spec_callback(s, awaited, awaiter, now),
        InternalV::Listener { awaited, address } => spec_listener(s, awaited, address, now),
        InternalV::TaskLeaseTimeout(id) => spec_lease(s, id, now),
        InternalV::TaskRetryTimeout(id) => spec_retry(config, s, id, now),
        InternalV::ScheduleTimeout { id, .. } => spec_schedule_step(s, id, now),
        InternalV::Occurrence { promise, at, timeout, param, tags } => {
            spec_create_if_absent(s, promise, at, timeout, param, tags, now)
        },
    }
}

pub open spec fn spec_callback(s: StoreV, awaited: Seq<char>, awaiter: Seq<char>, now: Time) -> InOutV {
    if !s.promises.contains_key(awaited) {
        spec_noop(s)
    } else {
        let projected = spec_project_promise(s.promises[awaited], now);
        if projected.state == PromiseState::Pending || !projected.callbacks.contains(awaiter) {
            spec_noop(s)
        } else {
            let since = match projected.settled_at {
                Some(t) => t,
                None => 0,
            };
            let q = PromiseV { callbacks: projected.callbacks.remove(awaiter), ..projected };
            spec_callback_apply(s, awaited, awaiter, q, since, now)
        }
    }
}

pub open spec fn spec_callback_apply(
    s: StoreV,
    awaited: Seq<char>,
    awaiter: Seq<char>,
    q: PromiseV,
    since: Time,
    now: Time,
) -> InOutV {
    let tasks0 = if s.tasks.contains_key(awaited) {
        s.tasks.insert(awaited, spec_project_task(s.tasks[awaited], q))
    } else {
        s.tasks
    };
    let tasks = if !s.tasks.contains_key(awaiter) {
        tasks0
    } else {
        let stored = s.tasks[awaiter];
        let t = if s.promises.contains_key(awaiter) {
            spec_project_task(stored, spec_project_promise(s.promises[awaiter], now))
        } else {
            stored
        };
        match t.state {
            TaskState::Suspended => tasks0.insert(awaiter, TaskV {
                state: TaskState::Pending,
                resumes: seq![awaited],
                retry_timeout_at: Some(since),
                ..t
            }),
            TaskState::Fulfilled => tasks0,
            _ => {
                if t.resumes.contains(awaited) {
                    tasks0
                } else {
                    tasks0.insert(awaiter, TaskV { resumes: t.resumes.push(awaited), ..t })
                }
            },
        }
    };
    spec_did(StoreV { promises: s.promises.insert(awaited, q), tasks, ..s }, Seq::empty(), Seq::empty())
}

pub open spec fn spec_listener(s: StoreV, awaited: Seq<char>, address: Seq<char>, now: Time) -> InOutV {
    if !s.promises.contains_key(awaited) {
        spec_noop(s)
    } else {
        let projected = spec_project_promise(s.promises[awaited], now);
        if projected.state == PromiseState::Pending || !projected.listeners.contains(address) {
            spec_noop(s)
        } else {
            let rec = spec_promise_record(spec_string(awaited), projected);
            let q = PromiseV { listeners: projected.listeners.remove(address), ..projected };
            let tasks = if s.tasks.contains_key(awaited) {
                s.tasks.insert(awaited, spec_project_task(s.tasks[awaited], q))
            } else {
                s.tasks
            };
            spec_did(
                StoreV { promises: s.promises.insert(awaited, q), tasks, ..s },
                Seq::empty(),
                seq![DispatchV::Unblock { address, promise: rec }],
            )
        }
    }
}

pub open spec fn spec_lease(s: StoreV, id: Seq<char>, now: Time) -> InOutV {
    if !s.tasks.contains_key(id) {
        spec_noop(s)
    } else {
        let t = s.tasks[id];
        let pending = s.promises.contains_key(id)
            && spec_project_promise(s.promises[id], now).state == PromiseState::Pending;
        if t.state != TaskState::Acquired || now < spec_lease_at(t) || !pending {
            spec_noop(s)
        } else {
            let u = spec_unlease(t, TaskState::Pending, Some(now));
            spec_did(StoreV { tasks: s.tasks.insert(id, u), ..s }, Seq::empty(), Seq::empty())
        }
    }
}

pub open spec fn spec_retry(config: ServerConfig, s: StoreV, id: Seq<char>, now: Time) -> InOutV {
    let live = s.promises.contains_key(id)
        && spec_project_promise(s.promises[id], now).state == PromiseState::Pending;
    if !s.tasks.contains_key(id) {
        spec_noop(s)
    } else {
        let t = s.tasks[id];
        let due = match t.retry_timeout_at {
            Some(r) => r <= now,
            None => false,
        };
        if t.state != TaskState::Pending || !due || !live {
            spec_noop(s)
        } else {
            let again = sat_add(now, config.retry_timeout);
            let u = TaskV { retry_timeout_at: Some(again), ..t };
            spec_did(
                StoreV { tasks: s.tasks.insert(id, u), ..s },
                Seq::empty(),
                seq![DispatchV::Execute { id, version: t.version }],
            )
        }
    }
}

pub open spec fn spec_schedule_step(s: StoreV, id: Seq<char>, now: Time) -> InOutV {
    if !s.schedules.contains_key(id) {
        spec_noop(s)
    } else {
        let c = s.schedules[id];
        if c.next_run_at > now {
            spec_noop(s)
        } else {
            let at = c.next_run_at;
            let promise = spec_expand(c.promise_id, id, at);
            let d = ScheduleV {
                last_run_at: Some(at),
                next_run_at: spec_next_cron(c.cron, at),
                ..c
            };
            let occ = Sched::Timer(at, InternalV::Occurrence {
                promise,
                at,
                timeout: c.promise_timeout,
                param: c.promise_param,
                tags: c.promise_tags,
            });
            spec_did(StoreV { schedules: s.schedules.insert(id, d), ..s }, seq![occ], Seq::empty())
        }
    }
}

pub open spec fn spec_create_if_absent(
    s: StoreV,
    promise: Seq<char>,
    at: Time,
    timeout: Time,
    param: Value,
    tags: echod_types::Tags,
    now: Time,
) -> InOutV {
    if now < at {
        spec_noop(s)
    } else if s.promises.contains_key(promise) {
        spec_unchanged(s)
    } else {
        let timeout_at = sat_add(at, timeout);
        let (p, task) = spec_new_object(timeout_at, at, now, param, tags, spec_has_target(tags) && !spec_is_timer(tags));
        let promises = s.promises.insert(promise, p);
        let tasks = match task {
            Some(t) => s.tasks.insert(promise, t),
            None => s.tasks,
        };
        spec_did(StoreV { promises, tasks, ..s }, Seq::empty(), Seq::empty())
    }
}


} // verus!
