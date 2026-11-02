//! Timeout handlers. A deadline, a lease, a callback, a retry, listeners,
//! and a schedule's fire or advance.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use echod_types::{PromiseState, Schedule, TaskState, Value};

use super::super::collections::*;

#[cfg(verus_keep_ghost)]
use echod_rover::Sched;
#[cfg(verus_keep_ghost)]
use super::super::spec::{Chars, DispatchV, InternalV, group_views, sat_add, sends, strs, works};

use super::{
    at, contains, copy_server, copy_step, delay_of, has_target, ids1, ids2, is_timer, mk, marked, next_offer, prec, push_all, settle, settled_work, Dispatch, Id, InOut, Promise, Resonate, Server, Step, Task, Time, Work,
};

verus! {

impl Resonate {

    /// A suspended task resumes when a promise it awaits has settled; any
    /// other task is told, when it next runs (Lean's `resumeOne`). The
    /// callback is spent either way.
    fn resume(&self, n: &mut Server, awaited: &Id, awaiter: &Id, now: Time, marks: &mut Vec<&'static str>)
        
    {
        broadcast use group_views;
        // the resumed task's first offer: when the awaited settled (Lean's `since`)
        let since = match n.promises.get(awaited) {
            Some(p) => match p.settled_at {
                Some(t) => t,
                None => now,
            },
            None => now,
        };
        match n.promises.get(awaited) {
            Some(p) => {
                let mut q = copy(p);
                q.callbacks.remove(awaiter);
                n.promises.insert(awaited.clone(), q);
            },
            None => {},
        }
        match n.tasks.get(awaiter) {
            Some(t) => {
                match t.state {
                    TaskState::Suspended => {
                        let mut u = copy(t);
                        u.state = TaskState::Pending;
                        u.resumes = ids1(awaited);
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
            },
            None => {},
        }
    }

    /// Internal work on `ids` runs in `s` at time `now`: whatever is due on
    /// them happens, in the order the Lean specification's steps become
    /// enabled: a promise past its deadline settles; a callback on a settled
    /// promise resumes its awaiter; a lease past its end is reclaimed; a
    /// settled promise's listeners are told; a pending task whose retry is due
    /// is offered to a worker, and the next retry armed.
    pub(super) fn objects(&self, ids: &Vec<Id>, s: &Server, now: Time) -> (r: InOut)
        
    {
        broadcast use group_views;
        let ghost idv = strs(ids@);
        let mut n = copy_server(s);
        let mut work = Vec::new();
        let mut send = Vec::new();
        let mut marks = Vec::new();
        // A promise past its deadline times out (a timer promise resolves).
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
            decreases ids.len() - i,
        {
            proof {
                assert(idv.take(i + 1) =~= idv.take(i as int).push(idv[i as int]));
                assert(idv.take(i + 1).drop_last() =~= idv.take(i as int));
            }
            let id = &ids[i];
            let found = match n.promises.get(id) {
                Some(p) => Some(copy(p)),
                None => None,
            };
            match found {
                Some(p) => {
                    if p.live() && now >= p.timeout_at {
                        let timer = is_timer(&p.tags);
                        let state = if timer { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
                        marks.push(if timer { mk("timer promise resolved") } else { mk("promise timed out") });
                        let r = settled_work(&p, id);
                        let empty = Value::empty();
                        settle(&mut n, id, state, &empty, p.timeout_at);
                        push_all(&mut work, &r);
                    }
                },
                None => {},
            }
            i += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        let ghost n1 = n@;
        let ghost work1 = works(work@);
        // A callback on a settled promise is spent: its awaiter resumes.
        let mut a = 0;
        while a < ids.len()
            invariant
                a <= ids.len(),
                idv == strs(ids@),
                works(work@) == work1,
            decreases ids.len() - a,
        {
            proof {
                assert(idv.take(a + 1) =~= idv.take(a as int).push(idv[a as int]));
                assert(idv.take(a + 1).drop_last() =~= idv.take(a as int));
            }
            let ghost na = n@;
            let mut w = 0;
            while w < ids.len()
                invariant
                    w <= ids.len(),
                    a < ids.len(),
                    idv == strs(ids@),
                    works(work@) == work1,
                decreases ids.len() - w,
            {
                proof {
                    assert(idv.take(w + 1) =~= idv.take(w as int).push(idv[w as int]));
                    assert(idv.take(w + 1).drop_last() =~= idv.take(w as int));
                }
                let awaited = &ids[a];
                let awaiter = &ids[w];
                let due = match n.promises.get(awaited) {
                    Some(p) => !p.live() && p.callbacks.contains(awaiter),
                    None => false,
                };
                if due {
                    self.resume(&mut n, awaited, awaiter, now, &mut marks);
                }
                w += 1;
            }
            proof {
                assert(idv.take(ids.len() as int) =~= idv);
            }
            a += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        let ghost n2 = n@;
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
            decreases ids.len() - i,
        {
            proof {
                assert(idv.take(i + 1) =~= idv.take(i as int).push(idv[i as int]));
                assert(idv.take(i + 1).drop_last() =~= idv.take(i as int));
            }

            let id = &ids[i];
            assert(idv[i as int] == id@);

            match n.tasks.get(id) {
                Some(t) => {
                    if t.state == TaskState::Acquired && now >= t.lease_expires() {
                        let mut u = copy(t);
                        u.release(t.lease_expires());

                        let ghost nt = n.tasks@;
                        n.tasks.insert(id.clone(), u);
                        assert(n.tasks@ == nt.insert(id@, u));

                        marks.push(mk("lease expired"));
                    }
                },
                None => {},
            }
            // A settled promise's listeners are told, once.
            let found = match n.promises.get(id) {
                Some(p) => Some(copy(p)),
                None => None,
            };
            match found {
                Some(p) => {
                    if !p.live() {
                        let addrs = p.listeners.to_vec();
                        assert(strs(addrs@).len() == addrs@.len());
                        proof {
                            axiom_pset_seq(p.listeners@);
                        }
                        assert(pset_seq(p.listeners@).len() == p.listeners@.len());
                        assert(addrs@.len() == p@.listeners.len());
                        if addrs.len() > 0 {
                            let rec = prec(id, &p);
                            let ghost ls = pset_seq(p.listeners@);
                            let ghost send0 = sends(send@);
                            let mut j = 0;
                            while j < addrs.len()
                                invariant
                                    j <= addrs.len(),
                                    strs(addrs@) == ls,
                                    sends(send@) == send0 + ls.take(j as int).map_values(|a: Chars| DispatchV::Unblock { address: a, promise: rec@ }),
                                decreases addrs.len() - j,
                            {
                                let ghost before = sends(send@);
                                let d = Dispatch::Unblock { address: addrs[j].clone(), promise: copy(&rec) };
                                assert(ls[j as int] == addrs@[j as int]@);
                                assert(d@ == (DispatchV::Unblock { address: ls[j as int], promise: rec@ }));
                                send.push(d);
                                proof {
                                    assert(sends(send@) == before.push(d@));
                                    assert(ls.take(j + 1) =~= ls.take(j as int).push(ls[j as int]));
                                    let g = |a: Chars| DispatchV::Unblock { address: a, promise: rec@ };
                                    assert(ls.take(j + 1).map_values(g) == ls.take(j as int).map_values(g).push(g(ls[j as int])));
                                    assert(send0 + ls.take(j as int).map_values(g).push(g(ls[j as int])) =~= (send0 + ls.take(j as int).map_values(g)).push(g(ls[j as int])));
                                }
                                j += 1;
                            }
                            proof {
                                assert(ls.take(addrs.len() as int) =~= ls);
                            }
                            let mut q = copy(&p);
                            q.listeners = PSet::empty();

                            let ghost np = n.promises@;
                            n.promises.insert(id.clone(), q);
                            assert(n.promises@ == np.insert(id@, q));

                            assert(n.promises@.map_values(|p: Promise| p@) == np.map_values(|p: Promise| p@).insert(id@, q@));
                            marks.push(mk("listeners told"));
                        }
                    }
                },
                None => {},
            }
            // A pending task whose retry is due is offered to a worker, and
            // the next offer armed. Not once its promise is settled: the task
            // is done.
            let live = match n.promises.get(id) {
                Some(p) => p.live(),
                None => false,
            };
            match n.tasks.get(id) {
                Some(t) => {
                    let due = match t.retry_at {
                        Some(r) => r <= now,
                        None => false,
                    };
                    if t.state == TaskState::Pending && due && live {
                        let mut u = copy(t);
                        let again = match t.retry_at {
                            Some(r) => next_offer(r, now, self.retry_timeout),
                            None => now.saturating_add(self.retry_timeout),
                        };
                        u.retry_at = Some(again);
                        let version = u.version;

                        n.tasks.insert(id.clone(), u);

                        let ghost before_s = sends(send@);
                        let ghost before_w = works(work@);
                        let d = Dispatch::Execute { id: id.clone(), version };
                        send.push(d);
                        let w = at(again, id);
                        work.push(w);
                        assert(sends(send@) == before_s.push(d@));
                        assert(works(work@) == before_w.push(w@));
                        marks.push(mk("task dispatched"));

                    }
                },
                None => {},
            }

            i += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        InOut { next: n, work, send, marks, pending: false }
    }

    /// The work that fires `schedule`'s occurrence at `at`: later, from `at`
    /// on, and a timer at `at + fire_within`, by which it is owed. Whichever
    /// runs first fires it; the other finds the schedule moved on and does
    /// nothing. With `fire_within` zero, the timer alone.
    pub(super) fn arm_fire(&self, work: &mut Vec<Work>, schedule: &Id, at_: Time, template: &String)
        
    {
        broadcast use group_views;
        let step = Step::Fire { schedule: schedule.clone(), at: at_, promise: expand(template, schedule, at_) };
        if self.fire_within > 0 {
            work.push(Work::Later(copy_step(&step)));
        }
        work.push(Work::Timer(at_.saturating_add(self.fire_within), step));
    }

    /// A schedule's occurrence at `at` fires, from `at` on: the promise it
    /// names is created, if absent, as of `at`; the schedule records the run
    /// and arms the next, at once when fires are exact, else by a step of its
    /// own (`advance`) owed within the window. The clock may be past `at`
    /// (the server got to it late, or jumped over several occurrences): a
    /// promise whose deadline has passed by `now` is born settled, as Lean's
    /// read-time projection would show it, and starts nothing. A schedule
    /// that is gone, or no longer expects this occurrence, fires nothing;
    /// before its instant it cannot fire yet.
    pub(super) fn fire(&self, schedule: &Id, at_: Time, promise: &Id, s: &Server, now: Time) -> (r: InOut)
        
    {
        broadcast use group_views;
        let c = match s.schedules.get(schedule) {
            Some(c) => c,
            None => return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: false },
        };
        // Not this occurrence: the schedule moved on, or was deleted and
        // created again under another template (same template: the same
        // occurrence, and this work does what the new schedule's would).
        if c.next_run_at != at_ || expand(&c.promise_id, schedule, at_) != *promise {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: false };
        }
        if now < at_ {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: true };
        }
        let ghost cv = c@;
        assert(s@.schedules[schedule@] == cv);
        let mut marks = Vec::new();
        let mut work = Vec::new();
        let mut n = copy_server(s);
        if s.promises.contains_key(promise) {
            marks.push(mk("schedule: occurrence exists"));
            assert(n@ == s@);
            assert(works(work@) == Seq::<Sched<InternalV>>::empty());
        } else {
            let timeout_at = at_.saturating_add(c.promise_timeout);
            let tags = echod_types::clone_tags(&c.promise_tags);
            let timer = is_timer(&tags);
            let target = has_target(&tags);
            let delay = delay_of(&tags);
            // Born live at `at`, or settled at its deadline: the deadline is
            // `at` itself when the timeout is zero, else before `now`.
            let live_now = timeout_at > now;
            let live_at = timeout_at > at_;
            let born = if live_now { PromiseState::Pending } else if timer { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
            let p = Promise {
                state: born,
                value: Value::empty(),
                param: c.promise_param.dup(),
                timeout_at,
                created_at: if live_at { at_ } else { timeout_at },
                settled_at: if live_now { None } else { Some(timeout_at) },
                tags: echod_types::clone_tags(&tags),
                callbacks: PSet::empty(),
                listeners: PSet::empty(),
            };
            n.promises.insert(promise.clone(), p);
            if live_now {
                work.push(at(timeout_at, promise));
            }
            if target && !timer {
                let due = match delay {
                    Some(d) => if d > at_ { d } else { at_ },
                    None => at_,
                };
                let state = if live_now { TaskState::Pending } else { TaskState::Fulfilled };
                let retry_at = if live_now { Some(due) } else { None };
                n.tasks.insert(promise.clone(), Task { state, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at, resumes: Vec::new() });
                if live_now {
                    work.push(at(due, promise));
                }
            }
            marks.push(if live_now { mk("schedule fired") } else { mk("schedule fired past the occurrence's deadline") });
            assert(n@.promises == s@.promises.insert(promise@, p@));
            assert(n@.schedules == s@.schedules);

        }
        let ghost n1v = n@;
        let ghost work1v = works(work@);
        if self.fire_within == 0 {
            Resonate::record_run(&mut n, c, schedule, at_);

            self.arm_fire(&mut work, schedule, next_cron(&c.cron, at_), &c.promise_id);

        } else {
            let step = Step::Advance { schedule: schedule.clone(), at: at_, promise: promise.clone() };
            let ghost sv = step@;
            work.push(Work::Later(copy_step(&step)));
            work.push(Work::Timer(at_.saturating_add(self.fire_within), step));
            assert(works(work@) == work1v + seq![Sched::Later(sv), Sched::Timer(sat_add(at_, self.fire_within), sv)]) by {
                assert(works(work@) =~= work1v + seq![Sched::Later(sv), Sched::Timer(sat_add(at_, self.fire_within), sv)]);
            }
        }
        InOut { next: n, work, send: Vec::new(), marks, pending: false }
    }

    /// The schedule records its run at `at` and arms the next.
    fn record_run(n: &mut Server, c: &Schedule, schedule: &Id, at_: Time)
        
    {
        broadcast use group_views;
        let mut d = copy(c);
        d.last_run_at = Some(at_);
        d.next_run_at = next_cron(&c.cron, at_);
        n.schedules.insert(schedule.clone(), d);
    }

    /// The second half of a sweeping server's fire: the run at `at` recorded
    /// on `schedule` and the next occurrence armed. A schedule that is gone,
    /// or has moved on (the fire refired and advanced already), is left as it
    /// is.
    pub(super) fn advance(&self, schedule: &Id, at_: Time, promise: &Id, s: &Server, now: Time) -> (r: InOut)
        
    {
        broadcast use group_views;
        let c = match s.schedules.get(schedule) {
            Some(c) => c,
            None => return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: false },
        };
        if c.next_run_at != at_ || expand(&c.promise_id, schedule, at_) != *promise {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: false };
        }
        if now < at_ {
            return InOut { next: copy_server(s), work: Vec::new(), send: Vec::new(), marks: Vec::new(), pending: true };
        }
        let mut n = copy_server(s);
        let mut work = Vec::new();
        Resonate::record_run(&mut n, c, schedule, at_);
        self.arm_fire(&mut work, schedule, next_cron(&c.cron, at_), &c.promise_id);
        InOut { next: n, work, send: Vec::new(), marks: marked(mk("schedule advanced")), pending: false }
    }

}

} // verus!
