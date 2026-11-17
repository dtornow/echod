//! Executable autonomous-work handlers. The handler does nothing when the step is
//! not due. A deadline writes the projected promise back.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;
use echod_types::{MAX_TIME, MAX_VERSION, deadline_bounded};
#[cfg(verus_keep_ghost)]
use echod_types::spec_deadline_bounded;

#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::*;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::handler::*;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::property_proof::*;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::handler::*;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::property_proof::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::{lemma_tags_ext, lemma_value_ext};
use echod_types::{Dispatch, DispatchV};
use echod_abstract_spec::state::{Id, Time};
use echod_abstract_spec::rover::{Config};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::Sched;
#[cfg(verus_keep_ghost)]
use echod_types::origin;
use echod_types::{PromiseState, TaskState, Value};

use crate::collections::*;
use crate::runtime::*;
#[cfg(verus_keep_ghost)]
use crate::projection::{group_views as group_exec_views, sends};
use crate::state::{
    contains, copy_store, has_target, is_timer, mk, new_object, Handlers, InOut, Promise, Store,
    Task, Work,
};

verus! {

impl<'cfg> Handlers<'cfg> {
    pub(crate) fn bulk_timed_origin(&self, s: &Store, document: &Id, now: Time) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_bulk_timed_origin(*self.0, s@, document@, now),
    {
        let keys = self.timed_origin_keys(s, document);
        let (projected, mut send) = self.project_timed_keys(s, &keys, now);
        let (resumed, mut callbacks) = self.drain_timed_callback_keys(&projected, &keys, now);
        let (next, mut listeners) = self.drain_timed_listener_keys(&resumed, &keys, now);
        let ghost offers = send@;
        let ghost callback_sends = callbacks@;
        let ghost listener_sends = listeners@;
        send.append(&mut callbacks);
        proof { assert(sends(send@) =~= sends(offers) + sends(callback_sends)); }
        let ghost before_listeners = send@;
        send.append(&mut listeners);
        proof { assert(sends(send@) =~= sends(before_listeners) + sends(listener_sends)); }
        (next, send)
    }

    pub(crate) fn drain_timed_callback_keys(&self, s: &Store, keys: &Vec<Id>, now: Time) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_drain_timed_callback_keys(*self.0, s@, strs(keys@), keys.len() as nat, now),
    {
        let mut current = copy_store(s);
        let mut send: Vec<Dispatch> = Vec::new();
        let mut i = 0;
        while i < keys.len()
            invariant
                i <= keys.len(),
                (current@, sends(send@)) == spec_drain_timed_callback_keys(*self.0, s@, strs(keys@), i as nat, now),
            decreases keys.len() - i,
        {
            let (next, mut more) = self.drain_timed_callbacks(&current, &keys[i], now);
            let ghost before = send@;
            let ghost added = more@;
            send.append(&mut more);
            proof { assert(sends(send@) =~= sends(before) + sends(added)); }
            current = next;
            i += 1;
        }
        (current, send)
    }

    pub(crate) fn drain_timed_listener_keys(&self, s: &Store, keys: &Vec<Id>, now: Time) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_drain_timed_listener_keys(s@, strs(keys@), keys.len() as nat, now),
    {
        let mut current = copy_store(s);
        let mut send: Vec<Dispatch> = Vec::new();
        let mut i = 0;
        while i < keys.len()
            invariant
                i <= keys.len(),
                (current@, sends(send@)) == spec_drain_timed_listener_keys(s@, strs(keys@), i as nat, now),
            decreases keys.len() - i,
        {
            let (next, mut more) = self.drain_timed_listeners(&current, &keys[i], now);
            let ghost before = send@;
            let ghost added = more@;
            send.append(&mut more);
            proof { assert(sends(send@) =~= sends(before) + sends(added)); }
            current = next;
            i += 1;
        }
        (current, send)
    }

    pub(crate) fn drain_timed_callbacks(&self, s: &Store, awaited: &Id, now: Time) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_drain_timed_callbacks(*self.0, s@, awaited@, now),
    {
        broadcast use group_exec_views;
        match s.promises.get(awaited) {
            Some(promise) if promise.state != PromiseState::Pending => {
                let plan = promise.callbacks.to_vec();
                self.drain_timed_callback_plan(s, awaited, &plan, now)
            },
            _ => (copy_store(s), Vec::new()),
        }
    }

    pub(crate) fn drain_timed_listeners(&self, s: &Store, awaited: &Id, now: Time) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_drain_timed_listeners(s@, awaited@, now),
    {
        broadcast use group_exec_views;
        match s.promises.get(awaited) {
            Some(promise) if promise.state != PromiseState::Pending => {
                let plan = promise.listeners.to_vec();
                self.drain_timed_listener_plan(s, awaited, &plan, now)
            },
            _ => (copy_store(s), Vec::new()),
        }
    }

    pub(crate) fn drain_timed_callback_plan(
        &self, s: &Store, awaited: &Id, awaiters: &Vec<Id>, now: Time,
    ) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_drain_timed_callback_plan(*self.0, s@, awaited@, strs(awaiters@), awaiters.len() as nat, now),
    {
        let mut current = copy_store(s);
        let mut send: Vec<Dispatch> = Vec::new();
        let mut i = 0;
        while i < awaiters.len()
            invariant
                i <= awaiters.len(),
                (current@, sends(send@)) == spec_drain_timed_callback_plan(*self.0, s@, awaited@, strs(awaiters@), i as nat, now),
            decreases awaiters.len() - i,
        {
            let (next, mut more) = self.drain_timed_callback(&current, awaited, &awaiters[i], now);
            let ghost prior_sends = send@;
            let ghost more_sends = more@;
            send.append(&mut more);
            proof { assert(sends(send@) =~= sends(prior_sends) + sends(more_sends)); }
            current = next;
            i += 1;
        }
        (current, send)
    }

    pub(crate) fn drain_timed_listener_plan(
        &self, s: &Store, awaited: &Id, addresses: &Vec<String>, now: Time,
    ) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_drain_timed_listener_plan(s@, awaited@, strs(addresses@), addresses.len() as nat, now),
    {
        let mut current = copy_store(s);
        let mut send: Vec<Dispatch> = Vec::new();
        let mut i = 0;
        while i < addresses.len()
            invariant
                i <= addresses.len(),
                (current@, sends(send@)) == spec_drain_timed_listener_plan(s@, awaited@, strs(addresses@), i as nat, now),
            decreases addresses.len() - i,
        {
            let mut next = self.process_listener(awaited, addresses[i].as_str(), &current, now);
            let ghost prior_sends = send@;
            let ghost more_sends = next.send@;
            send.append(&mut next.send);
            proof { assert(sends(send@) =~= sends(prior_sends) + sends(more_sends)); }
            current = next.next;
            i += 1;
        }
        (current, send)
    }

    pub(crate) fn drain_timed_callback(&self, s: &Store, awaited: &Id, awaiter: &Id, now: Time) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_drain_timed_callback(*self.0, s@, awaited@, awaiter@, now),
    {
        broadcast use group_exec_views;
        let suspended = match s.tasks.get(awaiter) {
            Some(task) => task.state == TaskState::Suspended,
            None => false,
        };
        let callback = self.process_callback(awaited, awaiter, s, now);
        if suspended {
            let retry = self.process_retry_timeout(awaiter, &callback.next, now);
            (retry.next, retry.send)
        } else {
            (callback.next, callback.send)
        }
    }

    pub(crate) fn timed_origin_keys(&self, s: &Store, document: &Id) -> (result: Vec<Id>)
        ensures strs(result@) == spec_timed_origin_keys(s@, document@),
    {
        broadcast use group_exec_views;
        let keys = s.promises.keys();
        proof {
            assert forall|id: Seq<char>| strs(keys@).contains(id) == #[trigger] s.promises@.contains_key(id) by {
                if strs(keys@).contains(id) {
                    let j = choose|j: int| 0 <= j < strs(keys@).len() && strs(keys@)[j] == id;
                    assert(keys@[j]@ == id);
                } else if s.promises@.contains_key(id) {
                    let j = choose|j: int| 0 <= j < keys.len() && keys@[j]@ == id;
                    assert(strs(keys@)[j] == id);
                }
            };
            assert(strs(keys@).to_set() =~= s@.promises.dom());
        }
        let mut selected: PMap<u8> = PMap::empty();
        let mut i = 0;
        while i < keys.len()
            invariant
                i <= keys.len(),
                strs(keys@).to_set() == s@.promises.dom(),
                forall|id: Seq<char>| #[trigger] selected@.contains_key(id)
                    == (strs(keys@).take(i as int).contains(id) && origin(id) == origin(document@)),
            decreases keys.len() - i,
        {
            proof { assert(strs(keys@).take(i as int + 1) =~= strs(keys@).take(i as int).push(keys@[i as int]@)); }
            let ghost previous = selected@;
            let matches = echod_types::same_origin(&keys[i], document);
            assert(matches == (origin(keys@[i as int]@) == origin(document@)));
            if matches {
                selected.insert(keys[i].clone(), 0);
            }
            proof {
                assert forall|id: Seq<char>| #[trigger] selected@.contains_key(id)
                    == (strs(keys@).take(i as int + 1).contains(id) && origin(id) == origin(document@)) by {
                    assert(previous.contains_key(id)
                        == (strs(keys@).take(i as int).contains(id) && origin(id) == origin(document@)));
                    if strs(keys@).take(i as int + 1).contains(id) {
                        let j = choose|j: int| 0 <= j < i + 1 && #[trigger] strs(keys@).take(i as int + 1)[j] == id;
                        if j < i {
                            assert(strs(keys@).take(i as int)[j] == id);
                        } else {
                            assert(id == keys@[i as int]@);
                        }
                    }
                    if strs(keys@).take(i as int).contains(id) {
                        let j = choose|j: int| 0 <= j < i && #[trigger] strs(keys@).take(i as int)[j] == id;
                        assert(strs(keys@).take(i as int + 1)[j] == id);
                    } else if id == keys@[i as int]@ {
                        assert(strs(keys@).take(i as int + 1)[i as int] == id);
                    }
                    assert(strs(keys@).take(i as int + 1).contains(id)
                        == (strs(keys@).take(i as int).contains(id) || id == keys@[i as int]@));
                    if id != keys@[i as int]@ {
                        assert(selected@.contains_key(id) == previous.contains_key(id));
                    } else {
                        assert(selected@.contains_key(id) == (previous.contains_key(id) || matches));
                    }
                };
            }
            i += 1;
        }
        proof {
            assert(strs(keys@).take(i as int) =~= strs(keys@));
            assert(selected@.dom() =~= s@.promises.dom().filter(|id: Seq<char>| origin(id) == origin(document@)));
        }
        selected.keys()
    }

    pub(crate) fn project_timed_origin(&self, s: &Store, document: &Id, now: Time) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_project_timed_origin(*self.0, s@, document@, now),
    {
        let keys = self.timed_origin_keys(s, document);
        self.project_timed_keys(s, &keys, now)
    }

    pub(crate) fn project_timed_keys(&self, s: &Store, keys: &Vec<Id>, now: Time) -> (result: (Store, Vec<Dispatch>))
        ensures (result.0@, sends(result.1@)) == spec_project_timed_keys(*self.0, s@, strs(keys@), keys.len() as nat, now),
    {
        broadcast use group_exec_views;
        let mut current = copy_store(s);
        let mut send: Vec<Dispatch> = Vec::new();
        let mut i = 0;
        while i < keys.len()
            invariant
                i <= keys.len(),
                (current@, sends(send@)) == spec_project_timed_keys(*self.0, s@, strs(keys@), i as nat, now),
            decreases keys.len() - i,
        {
            let mut next = self.project_timed_key(&current, &keys[i], now);
            let ghost prior_sends = send@;
            let ghost more_sends = next.send@;
            send.append(&mut next.send);
            proof { assert(sends(send@) =~= sends(prior_sends) + sends(more_sends)); }
            current = next.next;
            i += 1;
        }
        (current, send)
    }

    pub(crate) fn project_timed_key(&self, s: &Store, id: &Id, now: Time) -> (result: InOut)
        ensures result@ == spec_project_timed_key(*self.0, s@, id@, now),
    {
        broadcast use group_exec_views;
        let promise = match s.promises.get(id) {
            Some(promise) => promise,
            None => return self.noop(s),
        };
        if promise.state != PromiseState::Pending {
            return self.noop(s);
        }
        if promise.timeout_at <= now {
            return self.process_promise_timeout(id, s, now);
        }
        let task = match s.tasks.get(id) {
            Some(task) => task,
            None => return self.noop(s),
        };
        if task.state == TaskState::Acquired && task.lease_timeout_at() <= now {
            let released = self.process_lease_timeout(id, s, now);
            self.process_retry_timeout(id, &released.next, now)
        } else if task.state == TaskState::Pending && match task.retry_timeout_at { Some(at) => at <= now, None => false } {
            self.process_retry_timeout(id, s, now)
        } else {
            self.noop(s)
        }
    }

    /// Not due. `pending` keeps the checker from treating it as a step that
    /// ran and changed nothing, which a derived item would otherwise repeat.
    fn noop(&self, s: &Store) -> (r: InOut)
        ensures
            r@ == spec_noop(s@),
    {
        broadcast use group_exec_views;
        let r = InOut { next: copy_store(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), not_due: true };
        proof { assert(r@ =~~= spec_noop(s@)); }
        r
    }

    /// Write the promise back as a read at `now` sees it.
    fn process_promise_timeout(&self, id: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_process_work(*self.0, InternalV::PromiseTimeout(id@), s@, now),
    {
        broadcast use group_exec_views;
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
    pub(crate) fn process_callback(&self, awaited: &Id, awaiter: &Id, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_callback(s@, awaited@, awaiter@, now),
    {
        broadcast use group_exec_views;
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

    fn process_listener(&self, awaited: &Id, address: &str, s: &Store, now: Time) -> (r: InOut)
        ensures
            r@ == spec_listener(s@, awaited@, address@, now),
    {
        broadcast use group_exec_views;
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
        broadcast use group_exec_views;
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
        broadcast use group_exec_views;
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
        broadcast use group_exec_views;
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
        broadcast use group_exec_views;
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
