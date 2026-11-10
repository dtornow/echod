//! One handler per internal step. The handler does nothing when the step is
//! not due. A deadline writes the projected promise back.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_abstract_spec::machine::internal::*;
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::Sched;
#[cfg(verus_keep_ghost)]
use echod_types::origin;
use echod_types::{PromiseState, TaskState, Value};

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
    Machine,
};

verus! {

impl<'cfg> Machine<'cfg> {
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
    fn process_promise_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_process_work(*self.0, InternalV::PromiseTimeout(id@), s@, now),
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
        proof { assert(r@ =~~= spec_process_work(*self.0, InternalV::PromiseTimeout(id@), s@, now)); }
        r
    }

    /// A suspended task resumes when a promise it awaits has settled; any
    /// other task is told. The callback is spent either way. The awaited
    /// promise is written as it reads, with the callback removed.
    fn process_callback(&self, awaited: &Id, awaiter: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_callback(s@, awaited@, awaiter@, now),
    {
        broadcast use group_views;
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
        let r = InOut { next: n, work: Vec::new(), send: Vec::new(), marks, not_due: false };
        proof { assert(r@ =~~= spec_callback(s@, awaited@, awaiter@, now)); }
        r
    }

    fn process_listener(&self, awaited: &Id, address: &str, s: &Store, now: Time) -> (r: InOut)
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

    fn process_lease_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut)
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

    fn process_retry_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_retry(*self.0, s@, id@, now),
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
        let again = now.saturating_add(self.0.retry_timeout);
        let mut n = copy_store(s);
        let mut u = copy(t);
        u.retry_timeout_at = Some(again);
        let version = u.version;
        n.tasks.insert(id.clone(), u);
        let mut send = Vec::new();
        send.push(Dispatch::Execute { id: id.clone(), version });
        assert(sends(send@) =~= seq![DispatchV::Execute { id: id@, version }]);
        let r = InOut { next: n, work: Vec::new(), send, marks: vec![mk("task dispatched")], not_due: false };
        proof { assert(r@ =~~= spec_retry(*self.0, s@, id@, now)); }
        r
    }

    /// Record the run at `next_run_at` and queue the occurrence. The promise
    /// is a later item, on its own origin.
    fn process_schedule(&self, id: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_schedule_step(s@, id@, now),
    {
        broadcast use group_views;
        let Some(c) = s.schedules.get(id) else { return self.noop(s) };
        if c.next_run_at > now {
            return self.noop(s);
        }
        let at_ = c.next_run_at;
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
    fn create_if_absent(&self, promise: &Id, at_: Time, timeout: Time, param: &Value, tags: &echod_types::Tags, s: &Store, now: Time) -> (r: InOut)
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

    /// One due item at `now`: a deadline, a callback, a listener, a lease, a
    /// retry, a schedule, or one queued occurrence.
    /// One work item: `spec_process_work`.
    pub(crate) fn process_work(&self, step: &Work, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_process_work(*self.0, step@, s@, now),
    {
        match step {
            Work::PromiseTimeout(id) => self.process_promise_timeout(id, s, now),
            Work::Callback { awaited, awaiter } => self.process_callback(awaited, awaiter, s, now),
            Work::Listener { awaited, address } => self.process_listener(awaited, address, s, now),
            Work::TaskLeaseTimeout(id) => self.process_lease_timeout(id, s, now),
            Work::TaskRetryTimeout(id) => self.process_retry_timeout(id, s, now),
            Work::ScheduleTimeout { id, .. } => self.process_schedule(id, s, now),
            Work::Occurrence { promise, at, timeout, param, tags } => self.create_if_absent(promise, *at, *timeout, param, tags, s, now),
        }
    }
}

} // verus!
