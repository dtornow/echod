//! One handler per due item. A deadline, a callback, a listener, a lease, a
//! retry, a schedule, or one queued occurrence.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use echod_types::{PromiseState, TaskState, Value};

use super::super::collections::*;

use super::{
    contains, copy_server, delay_of, expand, has_target, is_timer, mk, next_cron, next_offer, prec, settle, Dispatch, Id, InOut, Promise, Resonate, Server, Task, Time, Work,
};

verus! {

impl Resonate {

    /// Not due. `pending` keeps the checker from treating it as a step that
    /// ran and changed nothing, which a derived item would otherwise repeat.
    fn noop(&self, s: &Server) -> (r: InOut) {
        InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: true }
    }

    pub(super) fn promise_timeout(&self, id: &Id, s: &Server, now: Time) -> (r: InOut) {
        let found = match s.promises.get(id) {
            Some(p) => Some(copy(p)),
            None => None,
        };
        let Some(p) = found else { return self.noop(s) };
        if !p.live() || now < p.timeout_at {
            return self.noop(s);
        }
        let timer = is_timer(&p.tags);
        let state = if timer { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
        let mut n = copy_server(s);
        settle(&mut n, id, state, &Value::empty(), p.timeout_at);
        let mark = if timer { mk("timer promise resolved") } else { mk("promise timed out") };
        InOut { next: n, work: Vec::new(), send: Vec::new(), marks: vec![mark], pending: false }
    }

    /// A suspended task resumes when a promise it awaits has settled; any
    /// other task is told. The callback is spent either way.
    pub(super) fn callback(&self, awaited: &Id, awaiter: &Id, s: &Server, _now: Time) -> (r: InOut) {
        let due = match s.promises.get(awaited) {
            Some(p) => !p.live() && p.callbacks.contains(awaiter),
            None => false,
        };
        if !due {
            return self.noop(s);
        }
        let since = match s.promises.get(awaited) {
            Some(p) => match p.settled_at {
                Some(t) => t,
                None => 0,
            },
            None => 0,
        };
        let mut n = copy_server(s);
        let mut marks = Vec::new();
        if let Some(p) = n.promises.get(awaited) {
            let mut q = copy(p);
            q.callbacks.remove(awaiter);
            n.promises.insert(awaited.clone(), q);
        }
        if let Some(t) = n.tasks.get(awaiter) {
            match t.state {
                TaskState::Suspended => {
                    let mut u = copy(t);
                    u.state = TaskState::Pending;
                    u.resumes = vec![awaited.clone()];
                    u.retry_at = Some(since);
                    n.tasks.insert(awaiter.clone(), u);
                    marks.push(mk("task resumed"));
                },
                TaskState::Fulfilled => {},
                _ => {
                    if !contains(&t.resumes, awaited) {
                        let mut u = copy(t);
                        u.resumes.push(awaited.clone());
                        n.tasks.insert(awaiter.clone(), u);
                        marks.push(mk("resume noted on a running task"));
                    }
                },
            }
        }
        InOut { next: n, work: Vec::new(), send: Vec::new(), marks, pending: false }
    }

    pub(super) fn listener(&self, awaited: &Id, address: &str, s: &Server, _now: Time) -> (r: InOut) {
        let found = match s.promises.get(awaited) {
            Some(p) => Some(copy(p)),
            None => None,
        };
        let Some(p) = found else { return self.noop(s) };
        let addr = address.to_string();
        if p.live() || !p.listeners.contains(&addr) {
            return self.noop(s);
        }
        let rec = prec(awaited, &p);
        let mut n = copy_server(s);
        if let Some(q0) = n.promises.get(awaited) {
            let mut q = copy(q0);
            q.listeners.remove(&addr);
            n.promises.insert(awaited.clone(), q);
        }
        let send = vec![Dispatch::Unblock { address: addr, promise: rec }];
        InOut { next: n, work: Vec::new(), send, marks: vec![mk("listeners told")], pending: false }
    }

    pub(super) fn lease(&self, id: &Id, s: &Server, now: Time) -> (r: InOut) {
        let Some(t) = s.tasks.get(id) else { return self.noop(s) };
        if t.state != TaskState::Acquired || now < t.lease_expires() {
            return self.noop(s);
        }
        let mut n = copy_server(s);
        let mut u = copy(t);
        u.release(t.lease_expires());
        n.tasks.insert(id.clone(), u);
        InOut { next: n, work: Vec::new(), send: Vec::new(), marks: vec![mk("lease expired")], pending: false }
    }

    pub(super) fn retry(&self, id: &Id, s: &Server, now: Time) -> (r: InOut) {
        let live = match s.promises.get(id) {
            Some(p) => p.live(),
            None => false,
        };
        let Some(t) = s.tasks.get(id) else { return self.noop(s) };
        let due = match t.retry_at {
            Some(r) => r <= now,
            None => false,
        };
        if t.state != TaskState::Pending || !due || !live {
            return self.noop(s);
        }
        let again = match t.retry_at {
            Some(r) => next_offer(r, now, self.retry_timeout),
            None => now.saturating_add(self.retry_timeout),
        };
        let mut n = copy_server(s);
        let mut u = copy(t);
        u.retry_at = Some(again);
        let version = u.version;
        n.tasks.insert(id.clone(), u);
        let send = vec![Dispatch::Execute { id: id.clone(), version }];
        InOut { next: n, work: Vec::new(), send, marks: vec![mk("task dispatched")], pending: false }
    }

    /// Record the run at `next_run_at` and queue the occurrence. The promise
    /// is a later item, on its own origin.
    pub(super) fn schedule(&self, id: &Id, s: &Server, now: Time) -> (r: InOut) {
        let Some(c) = s.schedules.get(id) else { return self.noop(s) };
        if c.next_run_at > now {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: true };
        }
        let at_ = c.next_run_at;
        let promise = expand(&c.promise_id, id, at_);
        let mut n = copy_server(s);
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
        InOut { next: n, work, send: Vec::new(), marks: vec![mk("schedule advanced")], pending: false }
    }

    /// Create the occurrence's promise as of `at`. A promise already there is
    /// left as it is. One whose deadline has passed by `now` is born settled.
    pub(super) fn occurrence(&self, promise: &Id, at_: Time, timeout: Time, param: &Value, tags: &echod_types::Tags, s: &Server, now: Time) -> (r: InOut) {
        if now < at_ {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: true };
        }
        if s.promises.contains_key(promise) {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: vec![mk("schedule: occurrence exists")], pending: false };
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
        let mut n = copy_server(s);
        n.promises.insert(promise.clone(), p);
        if target && !timer {
            let due = match delay {
                Some(d) => if d > at_ { d } else { at_ },
                None => at_,
            };
            let state = if live_now { TaskState::Pending } else { TaskState::Fulfilled };
            let retry_at = if live_now { Some(due) } else { None };
            n.tasks.insert(promise.clone(), Task { state, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at, resumes: Vec::new() });
        }
        let mark = if live_now { mk("schedule fired") } else { mk("schedule fired past the occurrence's deadline") };
        InOut { next: n, work: Vec::new(), send: Vec::new(), marks: vec![mark], pending: false }
    }
}

} // verus!
