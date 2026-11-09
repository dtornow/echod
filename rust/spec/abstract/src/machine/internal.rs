//! One handler per internal step. The handler does nothing when the step is
//! not due. A deadline writes the projected promise back.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_rover::Sched;
#[cfg(verus_keep_ghost)]
use echod_types::origin;
use echod_types::{PromiseGetReq, PromiseState, Request, TaskState, Value, MAX_TIME};

use super::super::trusted::*;
#[cfg(verus_keep_ghost)]
use super::super::view::{
    group_views, lift_dispatch, sat_add, sends, spec_keys, strs, DispatchV, InOutV, InternalV,
    PromiseV, ScheduleV, StoreV, TaskV,
};
#[cfg(verus_keep_ghost)]
use super::{
    lemma_string_of, lemma_tags_ext, lemma_value_ext, spec_has_target, spec_is_timer,
    spec_lease_at, spec_new_object, spec_project_promise, spec_project_task, spec_promise_record,
    spec_string, spec_unlease,
};
use super::{
    contains, copy_store, expand, has_target, is_timer, mk, new_object, next_cron, Dispatch, Id, InOut, Promise, ServerConfig, Store, Task, Time, Work,
};

verus! {

impl ServerConfig {

    /// Not due. `pending` keeps the checker from treating it as a step that
    /// ran and changed nothing, which a derived item would otherwise repeat.
    fn noop(&self, s: &Store) -> (r: InOut)
        ensures
            r@ == spec_noop(s@),
    {
        broadcast use group_views;
        let r = InOut { next: copy_store(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), not_due: true };
        proof { assert(r@ =~~= spec_noop(s@)); }
        r
    }

    /// Write the promise back as a read at `now` sees it.
    pub(crate) fn process_promise_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_process_work(*self, InternalV::PromiseTimeout(id@), s@, now),
    {
        broadcast use group_views;
        let Some(stored) = s.promises.get(id) else { return self.noop(s) };
        let q = stored.project(now);
        if q.state == stored.state && q.settled_at == stored.settled_at {
            return self.noop(s);
        }
        let mut n = copy_store(s);
        if let Some(t) = s.tasks.get(id) {
            n.tasks.insert(id.clone(), t.project(&q));
        }
        n.promises.insert(id.clone(), copy(&q));
        let mark = if is_timer(&q.tags) { mk("timer promise resolved") } else { mk("promise timed out") };
        let r = InOut { next: n, work: Vec::new(), send: Vec::new(), marks: vec![mark], not_due: false };
        proof { assert(r@ =~~= spec_process_work(*self, InternalV::PromiseTimeout(id@), s@, now)); }
        r
    }

    /// A suspended task resumes when a promise it awaits has settled; any
    /// other task is told. The callback is spent either way. The awaited
    /// promise is written as it reads, with the callback removed.
    pub(crate) fn process_callback(&self, awaited: &Id, awaiter: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_callback(s@, awaited@, awaiter@, now),
    {
        broadcast use group_views;
        let Some(stored) = s.promises.get(awaited) else { return self.noop(s) };
        let projected = stored.project(now);
        if projected.state == PromiseState::Pending || !projected.callbacks.contains(awaiter) {
            return self.noop(s);
        }
        let _since = match projected.settled_at {
            Some(t) => t,
            None => 0,
        };
        let mut n = copy_store(s);
        let mut marks = Vec::new();
        let mut q = projected;
        q.callbacks.remove(awaiter);
        if let Some(t) = s.tasks.get(awaited) {
            n.tasks.insert(awaited.clone(), t.project(&q));
        }
        n.promises.insert(awaited.clone(), q);
        if let Some(stored_task) = s.tasks.get(awaiter) {
            let t = match s.promises.get(awaiter) {
                Some(w) => stored_task.project(&w.project(now)),
                None => copy(stored_task),
            };
            match t.state {
                TaskState::Suspended => {
                    let mut u = t;
                    u.state = TaskState::Pending;
                    u.resumes = Vec::new();
                    u.resumes.push(awaited.clone());
                    assert(strs(u.resumes@) =~= seq![awaited@]);
                    u.retry_timeout_at = Some(now);
                    n.tasks.insert(awaiter.clone(), u);
                    marks.push(mk("task resumed"));
                },
                TaskState::Fulfilled => {},
                _ => {
                    if !contains(&t.resumes, awaited) {
                        let mut u = t;
                        u.resumes.push(awaited.clone());
                        n.tasks.insert(awaiter.clone(), u);
                        marks.push(mk("resume noted on a running task"));
                    }
                },
            }
        }
        let r = InOut { next: n, work: Vec::new(), send: Vec::new(), marks, not_due: false };
        proof { assert(r@ =~~= spec_callback(s@, awaited@, awaiter@, now)); }
        r
    }

    pub(crate) fn process_listener(&self, awaited: &Id, address: &str, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_listener(s@, awaited@, address@, now),
    {
        broadcast use group_views;
        let Some(stored) = s.promises.get(awaited) else { return self.noop(s) };
        let projected = stored.project(now);
        let addr = address.to_owned();
        if projected.state == PromiseState::Pending || !projected.listeners.contains(&addr) {
            return self.noop(s);
        }
        let rec = projected.to_record(awaited);
        proof { lemma_string_of(*awaited); }
        let mut n = copy_store(s);
        let mut q = projected;
        q.listeners.remove(&addr);
        if let Some(t) = s.tasks.get(awaited) {
            n.tasks.insert(awaited.clone(), t.project(&q));
        }
        n.promises.insert(awaited.clone(), q);
        let mut send = Vec::new();
        send.push(Dispatch::Unblock { address: addr, promise: rec });
        assert(sends(send@) =~= seq![DispatchV::Unblock { address: address@, promise: rec }]);
        let r = InOut { next: n, work: Vec::new(), send, marks: vec![mk("listeners told")], not_due: false };
        proof { assert(r@ =~~= spec_listener(s@, awaited@, address@, now)); }
        r
    }

    pub(crate) fn process_lease_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_lease(s@, id@, now),
    {
        broadcast use group_views;
        let Some(t) = s.tasks.get(id) else { return self.noop(s) };
        let pending = match s.promises.get(id) {
            Some(p) => p.project(now).state == PromiseState::Pending,
            None => false,
        };
        if t.state != TaskState::Acquired || now < t.lease_timeout_at() || !pending {
            return self.noop(s);
        }
        let mut n = copy_store(s);
        let mut u = copy(t);
        u.unlease(TaskState::Pending, Some(now));
        n.tasks.insert(id.clone(), u);
        let r = InOut { next: n, work: Vec::new(), send: Vec::new(), marks: vec![mk("lease expired")], not_due: false };
        proof { assert(r@ =~~= spec_lease(s@, id@, now)); }
        r
    }

    pub(crate) fn process_retry_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_retry(*self, s@, id@, now),
    {
        broadcast use group_views;
        let live = match s.promises.get(id) {
            Some(p) => p.project(now).state == PromiseState::Pending,
            None => false,
        };
        let Some(t) = s.tasks.get(id) else { return self.noop(s) };
        let due = match t.retry_timeout_at {
            Some(r) => r <= now,
            None => false,
        };
        if t.state != TaskState::Pending || !due || !live {
            return self.noop(s);
        }
        let again = now.saturating_add(self.retry_timeout);
        let mut n = copy_store(s);
        let mut u = copy(t);
        u.retry_timeout_at = Some(again);
        let version = u.version;
        n.tasks.insert(id.clone(), u);
        let mut send = Vec::new();
        send.push(Dispatch::Execute { id: id.clone(), version });
        assert(sends(send@) =~= seq![DispatchV::Execute { id: id@, version }]);
        let r = InOut { next: n, work: Vec::new(), send, marks: vec![mk("task dispatched")], not_due: false };
        proof { assert(r@ =~~= spec_retry(*self, s@, id@, now)); }
        r
    }

    /// Record the run at `next_run_at` and queue the occurrence. The promise
    /// is a later item, on its own origin.
    pub(crate) fn process_schedule(&self, id: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_schedule_step(s@, id@, now),
    {
        broadcast use group_views;
        let Some(c) = s.schedules.get(id) else { return self.noop(s) };
        if c.next_run_at > now {
            return self.noop(s);
        }
        let at_ = c.next_run_at;
        if at_ > MAX_TIME {
            return self.noop(s);
        }
        let promise = expand(&c.promise_id, id, at_);
        let mut n = copy_store(s);
        let mut d = copy(c);
        d.last_run_at = Some(at_);
        d.next_run_at = next_cron(&c.cron, at_);
        n.schedules.insert(id.clone(), d);
        let param = c.promise_param.dup();
        let tags = echod_types::clone_tags(&c.promise_tags);
        proof {
            lemma_value_ext(param, c.promise_param);
            lemma_tags_ext(tags, c.promise_tags);
        }
        let occ = Work::Occurrence { promise, at: at_, timeout: c.promise_timeout, param, tags };
        let mut work = Vec::new();
        work.push(occ);
        let r = InOut { next: n, work, send: Vec::new(), marks: vec![mk("schedule advanced")], not_due: false };
        proof { assert(r@ =~~= spec_schedule_step(s@, id@, now)); }
        r
    }

    /// Create the occurrence's promise as of `at`. A promise already there is
    /// left as it is. One whose deadline has passed by `now` is born settled.
    pub(crate) fn create_if_absent(&self, promise: &Id, at_: Time, timeout: Time, param: &Value, tags: &echod_types::Tags, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_create_if_absent(s@, promise@, at_, timeout, *param, *tags, now),
    {
        broadcast use group_views;
        if now < at_ {
            return self.noop(s);
        }
        if s.promises.contains_key(promise) {
            let r = InOut { next: copy_store(s), work: Vec::new(), send: Vec::new(), marks: vec![mk("schedule: occurrence exists")], not_due: false };
            proof { assert(r@ =~~= spec_unchanged(s@)); }
            return r;
        }
        let timeout_at = at_.saturating_add(timeout);
        let live_now = timeout_at > now;
        let (p, task) = new_object(timeout_at, at_, now, param, tags, has_target(tags) && !is_timer(tags));
        let mut n = copy_store(s);
        n.promises.insert(promise.clone(), p);
        if let Some(task) = task {
            n.tasks.insert(promise.clone(), task);
        }
        let mark = if live_now { mk("schedule fired") } else { mk("schedule fired past the occurrence's deadline") };
        let r = InOut { next: n, work: Vec::new(), send: Vec::new(), marks: vec![mark], not_due: false };
        proof { assert(r@ =~~= spec_create_if_absent(s@, promise@, at_, timeout, *param, *tags, now)); }
        r
    }

    /// One internal item. Schedules and queued occurrences remain
    /// independent from workflow timeout work.
    pub fn process_work(&self, step: &Work, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_process_work(*self, step@, s@, now),
    {
        match step {
            Work::PromiseTimeout(id) => self.process_promise_timeout(id, s, now),
            Work::Callback { awaited, awaiter } =>
                self.process_callback(awaited, awaiter, s, now),
            Work::Listener { awaited, address } => self.process_listener(awaited, address, s, now),
            Work::TaskLeaseTimeout(id) => self.process_lease_timeout(id, s, now),
            Work::TaskRetryTimeout(id) => self.process_retry_timeout(id, s, now),
            Work::ScheduleTimeout { id, .. } => self.process_schedule(id, s, now),
            Work::Occurrence { promise, at, timeout, param, tags } => self.create_if_absent(promise, *at, *timeout, param, tags, s, now),
        }
    }
}

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

pub open spec fn spec_promise_timeout(s: StoreV, id: Seq<char>, now: Time) -> InOutV {
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
            spec_did(
                StoreV { promises: s.promises.insert(id, q), tasks, ..s },
                Seq::empty(),
                Seq::empty(),
            )
        }
    }
}

pub open spec fn spec_body(item: Sched<InternalV>) -> InternalV {
    match item {
        Sched::Later(work) => work,
        Sched::Timer(_, work) => work,
    }
}

pub open spec fn spec_process_work(config: ServerConfig, step: InternalV, s: StoreV, now: Time) -> InOutV {
    match step {
        InternalV::PromiseTimeout(id) => spec_promise_timeout(s, id, now),
        InternalV::Callback { awaited, awaiter } =>
            spec_callback(s, awaited, awaiter, now),
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
                retry_timeout_at: Some(now),
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
        if c.next_run_at > now || c.next_run_at > MAX_TIME {
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
