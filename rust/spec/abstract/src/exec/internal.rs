//! One handler per internal step. The handler does nothing when the step is
//! not due. A deadline writes the projected promise back.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use echod_types::{PromiseState, TaskState, Value};

use super::super::collections::*;

use super::{
    contains, copy_store, delay_of, expand, has_target, is_timer, mk, next_cron, next_offer, Dispatch, Id, InOut, Promise, ServerConfig, Store, Task, Time, Work,
};

verus! {

impl ServerConfig {

    /// Not due. `pending` keeps the checker from treating it as a step that
    /// ran and changed nothing, which a derived item would otherwise repeat.
    fn noop(&self, s: &Store) -> (r: InOut) {
        InOut { next: copy_store(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), not_due: true }
    }

    /// Write the promise back as a read at `now` sees it.
    pub(super) fn process_promise_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut) {
        let Some(stored) = s.promises.get(id) else { return self.noop(s) };
        let q = stored.project(now);
        if q.state == stored.state && q.settled_at == stored.settled_at {
            return self.noop(s);
        }
        let mut n = copy_store(s);
        if let Some(t) = s.tasks.get(id) {
            n.tasks.insert(id.clone(), t.project(&q));
        }
        n.promises.insert(id.clone(), q.clone());
        let mark = if is_timer(&q.tags) { mk("timer promise resolved") } else { mk("promise timed out") };
        InOut { next: n, work: Vec::new(), send: Vec::new(), marks: vec![mark], not_due: false }
    }

    /// A suspended task resumes when a promise it awaits has settled; any
    /// other task is told. The callback is spent either way. The awaited
    /// promise is written as it reads, with the callback removed.
    pub(super) fn process_callback(&self, awaited: &Id, awaiter: &Id, s: &Store, now: Time) -> (r: InOut) {
        let Some(stored) = s.promises.get(awaited) else { return self.noop(s) };
        let projected = stored.project(now);
        if projected.state == PromiseState::Pending || !projected.callbacks.contains(awaiter) {
            return self.noop(s);
        }
        let since = match projected.settled_at {
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
            let awaiter_promise = s.promises.get(awaiter).map(|w| w.project(now));
            let t = match &awaiter_promise {
                Some(w) => stored_task.project(w),
                None => copy(stored_task),
            };
            match t.state {
                TaskState::Suspended => {
                    let mut u = t;
                    u.state = TaskState::Pending;
                    u.resumes = vec![awaited.clone()];
                    u.retry_timeout_at = Some(since);
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
        InOut { next: n, work: Vec::new(), send: Vec::new(), marks, not_due: false }
    }

    pub(super) fn process_listener(&self, awaited: &Id, address: &str, s: &Store, now: Time) -> (r: InOut) {
        let Some(stored) = s.promises.get(awaited) else { return self.noop(s) };
        let projected = stored.project(now);
        let addr = address.to_string();
        if projected.state == PromiseState::Pending || !projected.listeners.contains(&addr) {
            return self.noop(s);
        }
        let rec = projected.to_record(awaited);
        let mut n = copy_store(s);
        let mut q = projected;
        q.listeners.remove(&addr);
        if let Some(t) = s.tasks.get(awaited) {
            n.tasks.insert(awaited.clone(), t.project(&q));
        }
        n.promises.insert(awaited.clone(), q);
        let send = vec![Dispatch::Unblock { address: addr, promise: rec }];
        InOut { next: n, work: Vec::new(), send, marks: vec![mk("listeners told")], not_due: false }
    }

    pub(super) fn process_lease_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut) {
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
        u.release(t.lease_timeout_at());
        n.tasks.insert(id.clone(), u);
        InOut { next: n, work: Vec::new(), send: Vec::new(), marks: vec![mk("lease expired")], not_due: false }
    }

    pub(super) fn process_retry_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut) {
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
        let again = match t.retry_timeout_at {
            Some(r) => next_offer(r, now, self.retry_timeout),
            None => now.saturating_add(self.retry_timeout),
        };
        let mut n = copy_store(s);
        let mut u = copy(t);
        u.retry_timeout_at = Some(again);
        let version = u.version;
        n.tasks.insert(id.clone(), u);
        let send = vec![Dispatch::Execute { id: id.clone(), version }];
        InOut { next: n, work: Vec::new(), send, marks: vec![mk("task dispatched")], not_due: false }
    }

    /// Record the run at `next_run_at` and queue the occurrence. The promise
    /// is a later item, on its own origin.
    pub(super) fn process_schedule(&self, id: &Id, s: &Store, now: Time) -> (r: InOut) {
        let Some(c) = s.schedules.get(id) else { return self.noop(s) };
        if c.next_run_at > now {
            return InOut { next: copy_store(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), not_due: true };
        }
        let at_ = c.next_run_at;
        let promise = expand(&c.promise_id, id, at_);
        let mut n = copy_store(s);
        let mut d = copy(c);
        d.last_run_at = Some(at_);
        d.next_run_at = next_cron(&c.cron, at_);
        n.schedules.insert(id.clone(), d);
        let occ = Work::Occurrence {
            promise,
            at: at_,
            timeout: c.promise_timeout,
            param: c.promise_param.dup(),
            tags: echod_types::clone_tags(&c.promise_tags),
        };
        let mut work = Vec::new();
        work.push(occ);
        InOut { next: n, work, send: Vec::new(), marks: vec![mk("schedule advanced")], not_due: false }
    }

    /// Create the occurrence's promise as of `at`. A promise already there is
    /// left as it is. One whose deadline has passed by `now` is born settled.
    pub(super) fn create_if_absent(&self, promise: &Id, at_: Time, timeout: Time, param: &Value, tags: &echod_types::Tags, s: &Store, now: Time) -> (r: InOut) {
        if now < at_ {
            return InOut { next: copy_store(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), not_due: true };
        }
        if s.promises.contains_key(promise) {
            return InOut { next: copy_store(s), work: Vec::new(), send: Vec::new(), marks: vec![mk("schedule: occurrence exists")], not_due: false };
        }
        let timeout_at = at_.saturating_add(timeout);
        let timer = is_timer(tags);
        let target = has_target(tags);
        let delay = delay_of(tags);
        let live_now = timeout_at > now;
        let live_at = timeout_at > at_;
        let born = if live_now { PromiseState::Pending } else if timer { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
        let p = Promise {
            state: born,
            value: Value::empty(),
            param: param.dup(),
            timeout_at,
            created_at: if live_at { at_ } else { timeout_at },
            settled_at: if live_now { None } else { Some(timeout_at) },
            tags: echod_types::clone_tags(tags),
            callbacks: PSet::empty(),
            listeners: PSet::empty(),
        };
        let mut n = copy_store(s);
        n.promises.insert(promise.clone(), p);
        if target && !timer {
            let due = match delay {
                Some(d) => if d > at_ { d } else { at_ },
                None => at_,
            };
            let state = if live_now { TaskState::Pending } else { TaskState::Fulfilled };
            let retry_timeout_at = if live_now { Some(due) } else { None };
            n.tasks.insert(promise.clone(), Task { state, version: 0, pid: None, ttl: None, acquired_at: 0, retry_timeout_at, resumes: Vec::new() });
        }
        let mark = if live_now { mk("schedule fired") } else { mk("schedule fired past the occurrence's deadline") };
        InOut { next: n, work: Vec::new(), send: Vec::new(), marks: vec![mark], not_due: false }
    }
}

} // verus!
