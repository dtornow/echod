//! Request handlers. A promise, a task, or a schedule changes here, and the
//! `ensures` on each handler is that transition.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use echod_types::{
    PromiseCreateReq, PromiseSettleReq, PromiseState, Response, Schedule, ScheduleCreateReq, TaskFenceAction, TaskFenceCheckReq, TaskFenceInnerRes, TaskRef, TaskState, TaskSuspendReq, Value,
};

use super::super::collections::*;
use super::super::spec::MAX_VERSION;

#[cfg(verus_keep_ghost)]
use super::super::spec::{ServerV, TaskV, all_in_origin, distinct, group_views, sends, strs, works};

use super::{
    at, claim_res, contains, copy_server, delay_of, echo, fence_res, has_target, is_timer, mk, marked, one, prec, promise_res, schedule_res, settle, settled_work, status, status_res, task_get_res, trec, Id, Out, Promise, Resonate, Server, Task, Time, Work,
};

#[cfg(verus_keep_ghost)]
use super::{promise_ok, response_ok, server_ok};

verus! {

impl Resonate {
    /// Property 1: every promise `promise_create` creates has it, every
    /// response has it if the state had it, and every promise that had it keeps it.
    ///
    /// Frame: it touches only the promise and task it creates. Every other
    /// promise and task is as it was, schedules are as they were, and an
    /// existing id changes nothing.
    ///
    /// `fenced`: the create is a fence's action (for the marks). `now` is the
    /// instant the promise is created at: the clock, or an occurrence's instant
    /// for a schedule's fire.
    pub fn promise_create(&self, req: &PromiseCreateReq, fenced: bool, s: &Server, now: Time) -> (outs: Vec<Out>)
        ensures
            forall|i: int|
                0 <= i < outs.len() ==> {
                    &&& (server_ok(*s) ==> server_ok(#[trigger] outs[i].next))
                    &&& (server_ok(*s) ==> response_ok(outs[i].resp))
                    &&& (!s.promises@.contains_key(req.id@) && outs[i].next.promises@.contains_key(req.id@)
                        ==> promise_ok(outs[i].next.promises@[req.id@]))
                    // the frame
                    &&& outs[i].next.promises@.remove(req.id@) == s.promises@.remove(req.id@)
                    &&& outs[i].next.tasks@.remove(req.id@) == s.tasks@.remove(req.id@)
                    &&& outs[i].next.schedules@ == s.schedules@
                    &&& (s.promises@.contains_key(req.id@) ==> outs[i].next.promises@ == s.promises@
                        && outs[i].next.tasks@ == s.tasks@)
                },

    {
        broadcast use group_views;
        if is_timer(&req.tags) && has_target(&req.tags) {
            return status(promise_res(400, None), mk("create: timer with target (400)"), s);
        }
        if let Some(d) = delay_of(&req.tags) {
            if d >= req.timeout_at {
                return status(promise_res(400, None), mk("create: delay past the deadline (400)"), s);
            }
            if !has_target(&req.tags) {
                return status(promise_res(400, None), mk("create: delay without a target (400)"), s);
            }
        }
        match s.promises.get(&req.id) {
            Some(p) => {
                proof {
                    if server_ok(*s) {
                        assert(promise_ok(s.promises@[req.id@]));
                    }
                }
                return echo(promise_res(200, Some(prec(&req.id, p))), mk("create: id exists (echo)"), s);
            },
            None => {},
        }
        let live = req.timeout_at > now;
        let born = if live {
            PromiseState::Pending
        } else if is_timer(&req.tags) {
            PromiseState::Resolved
        } else {
            PromiseState::RejectedTimedout
        };
        let p = Promise {
            state: born,
            value: Value::empty(),
            param: req.param.dup(),
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: echod_types::clone_tags(&req.tags),
            callbacks: PSet::empty(),
            listeners: PSet::empty(),
        };
        let rec = prec(&req.id, &p);
        let mut n = copy_server(s);
        n.promises.insert(req.id.clone(), p);
        let mut work = Vec::new();
        if live {
            work.push(at(req.timeout_at, &req.id));
        }
        if has_target(&req.tags) {
            // A live targeted promise's task is runnable: offered to a worker
            // at once, or at its delay.
            let due = match delay_of(&req.tags) {
                Some(d) => if d > now { d } else { now },
                None => now,
            };
            let state = if live { TaskState::Pending } else { TaskState::Fulfilled };
            let retry_at = if live { Some(due) } else { None };
            let task = Task { state, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at, resumes: Vec::new() };
            n.tasks.insert(req.id.clone(), task);
            if live {
                work.push(at(due, &req.id));
            }
        }
        proof {
            if server_ok(*s) {
                assert forall|k: Seq<char>| #[trigger] n.promises@.contains_key(k) implies promise_ok(
                    n.promises@[k],
                ) by {
                    if k != req.id@ {
                        assert(s.promises@.contains_key(k));
                    }
                }
            }
        }
        proof {
            assert(n.promises@.remove(req.id@) =~= s.promises@.remove(req.id@));
            assert(n.tasks@.remove(req.id@) =~= s.tasks@.remove(req.id@));
        }

        let mut marks = Vec::new();
        marks.push(match (fenced, live) {
            (false, true) => mk("promise created"),
            (false, false) => mk("promise created past its deadline"),
            (true, true) => mk("fence: promise created"),
            (true, false) => mk("fence: promise created past its deadline"),
        });
        if live && has_target(&req.tags) {
            marks.push(mk("task created pending"));
        }
        let outs = one(Out { resp: promise_res(200, Some(rec)), next: n, work, send: Vec::new(), marks });

        outs
    }

    pub(super) fn promise_settle(&self, req: &PromiseSettleReq, fenced: bool, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        if !req.state.settable() {
            return status(promise_res(400, None), mk("settle: not a settled state (400)"), s);
        }
        let p = match s.promises.get(&req.id) {
            Some(p) => p,
            None => return status(promise_res(404, None), mk("settle: no such promise (404)"), s),
        };
        if !p.live() {
            return echo(promise_res(200, Some(prec(&req.id, p))), mk("settle: already settled (echo)"), s);
        }
        let work = settled_work(p, &req.id);
        let mut n = copy_server(s);
        settle(&mut n, &req.id, req.state, &req.value, now);
        let res = match n.promises.get(&req.id) {
            Some(q) => promise_res(200, Some(prec(&req.id, q))),
            None => promise_res(500, None), // unreachable: the promise exists
        };
        let mut marks = Vec::new();
        marks.push(if fenced { mk("fence: promise settled") } else { mk("promise settled") });
        if work.len() > 0 {
            marks.push(mk("settled with callbacks or listeners"));
        }
        one(Out { resp: res, next: n, work, send: Vec::new(), marks })
    }

    /// The checks every task.* mutation shares: exists, acquired, own promise live,
    /// version matches. `Ok` is the task.
    fn held<'a>(&self, s: &'a Server, id: &Id, version: u64) -> (r: Result<&'a Task, u16>)
        
    {
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => {
                assert(!s@.tasks.contains_key(id@));

                return Err(404);
            },
        };
        assert(s@.tasks.contains_key(id@));
        assert(s@.tasks[id@] == t@);
        let live = match s.promises.get(id) {
            Some(p) => p.live(),
            None => false,  // unreachable: a task's promise exists
        };

        if t.state != TaskState::Acquired || !live || t.version != version {
            return Err(409);
        }

        Ok(t)
    }

    pub(super) fn task_create(&self, pid: &String, ttl: Time, req: &PromiseCreateReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        if !has_target(&req.tags) || is_timer(&req.tags) {
            return status(claim_res(400, None, None), mk("task.create: not runnable, or a timer (400)"), s);
        }
        if delay_of(&req.tags).is_some() {
            return status(claim_res(400, None, None), mk("task.create: action with a delay (400)"), s);
        }
        match s.promises.get(&req.id) {
            Some(p) => {
                if !has_target(&p.tags) {
                    return status(claim_res(422, None, None), mk("task.create: promise exists, not a target (422)"), s);
                }
                let t = match s.tasks.get(&req.id) {
                    Some(t) => t,
                    None => return status(claim_res(409, None, None), mk("task.create: target without a task (409)"), s),  // unreachable
                };
                return match t.state {
                    TaskState::Fulfilled => echo(claim_res(200, Some(trec(&req.id, t)), Some(prec(&req.id, p))), mk("task.create: task done (echo)"), s),
                    TaskState::Pending => {
                        if t.version >= MAX_VERSION as u64 {
                            return status(claim_res(409, None, None), mk("task.create: version at its cap (409)"), s);
                        }
                        let mut n = copy_server(s);
                        let mut u = copy(t);
                        u.acquire(t.version + 1, pid.clone(), ttl, now);
                        let rec = claim_res(200, Some(trec(&req.id, &u)), Some(prec(&req.id, p)));
                        n.tasks.insert(req.id.clone(), u);
                        let mut work = Vec::new();
                        work.push(at(now.saturating_add(ttl), &req.id));

                        assert(n@ == (ServerV { tasks: s@.tasks.insert(req.id@, u@), ..s@ }));
                        one(Out { resp: rec, next: n, work, send: Vec::new(), marks: marked(mk("task.create: pending task acquired")) })
                    },
                    _ => status(claim_res(409, None, None), mk("task.create: task held, suspended or halted (409)"), s),
                };
            },
            None => {},
        }
        let live = req.timeout_at > now;
        let p = Promise {
            state: if live { PromiseState::Pending } else { PromiseState::RejectedTimedout },
            value: Value::empty(),
            param: req.param.dup(),
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: echod_types::clone_tags(&req.tags),
            callbacks: PSet::empty(),
            listeners: PSet::empty(),
        };
        let mut t = Task { state: TaskState::Fulfilled, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Vec::new() };
        let mut work = Vec::new();
        if live {
            // Acquired by the caller right away: nothing to dispatch.
            t.acquire(1, pid.clone(), ttl, now);
            work.push(at(req.timeout_at, &req.id));
            work.push(at(now.saturating_add(ttl), &req.id));
        }

        let res = claim_res(200, Some(trec(&req.id, &t)), Some(prec(&req.id, &p)));
        let ghost pv = p@;
        let ghost tv = t@;
        let mut n = copy_server(s);
        n.promises.insert(req.id.clone(), p);
        n.tasks.insert(req.id.clone(), t);
        assert(n@ == (ServerV { promises: s@.promises.insert(req.id@, pv), tasks: s@.tasks.insert(req.id@, tv), ..s@ }));
        let mark = if live { mk("task created") } else { mk("task created past its deadline") };
        one(Out { resp: res, next: n, work, send: Vec::new(), marks: marked(mark) })
    }

    pub(super) fn task_suspend(&self, req: &TaskSuspendReq, s: &Server) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        let id = &req.id;
        let version = req.version;
        let ids: Vec<Id> = req.actions.iter().map(|a| a.awaited.clone()).collect();
        let ghost idv = strs(ids@);
        assert(idv.len() == ids@.len());
        if ids.len() == 0 || contains(&ids, id) {
            return status(status_res(400), mk("suspend: no awaited, or itself (400)"), s);
        }
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
                forall|a: int, b: int| 0 <= a < b < idv.len() && a < i ==> idv[a] != idv[b],
                forall|a: int| 0 <= a < i ==> origin(#[trigger] idv[a]) == origin(id@),
            decreases ids.len() - i,
        {
            let mut j = i + 1;
            while j < ids.len()
                invariant
                    i < j <= ids.len(),
                    idv == strs(ids@),
                    forall|b: int| i < b < j ==> idv[i as int] != idv[b],
                decreases ids.len() - j,
            {
                if ids[i] == ids[j] {
                    assert(idv[i as int] == ids@[i as int]@);
                    assert(idv[j as int] == ids@[j as int]@);
                    assert(idv[i as int] == idv[j as int]);
                    assert(!distinct(idv));
                    return status(status_res(400), mk("suspend: awaited twice (400)"), s);
                }
                j += 1;
            }
            if !same_origin(&ids[i], id) {
                assert(idv[i as int] == ids@[i as int]@);
                assert(origin(idv[i as int]) != origin(id@));
                assert(!all_in_origin(idv, id@));
                return status(status_res(400), mk("suspend: awaited in another origin (400)"), s);
            }
            i += 1;
        }
        assert(distinct(idv));
        assert(all_in_origin(idv, id@));
        let t = match self.held(s, id, version) {
            Err(code) => return status(status_res(code), if code == 404 { mk("suspend: no such task (404)") } else { mk("suspend: not held (409)") }, s),
            Ok(t) => t,
        };
        let mut settled = false;
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
                idv.len() > 0 && !idv.contains(id@) && distinct(idv) && all_in_origin(idv, id@),
                u16>(t@),
                forall|a: int| 0 <= a < i ==> s@.promises.contains_key(#[trigger] idv[a]),
            decreases ids.len() - i,
        {
            assert(idv[i as int] == ids@[i as int]@);
            match s.promises.get(&ids[i]) {
                None => {
                    assert(!s@.promises.contains_key(idv[i as int]));

                    return status(status_res(422), mk("suspend: awaited missing (422)"), s);
                },
                Some(p) => {
                    assert(s@.promises[idv[i as int]] == p@);
                    if !p.external() {
                        return status(status_res(422), mk("suspend: awaited not external (422)"), s);
                    }
                    let ghost was = settled;
                    settled = settled || !p.live();

                },
            }
            i += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        let mut n = copy_server(s);
        let mut u = copy(t);

        if settled {
            // The task stays acquired and runs on; what it was told has been seen.
            u.resumes = Vec::new();
            assert(u@ == (TaskV { resumes: Seq::empty(), ..t@ }));
            n.tasks.insert(id.clone(), u);
            assert(n@ == (ServerV { tasks: s@.tasks.insert(id@, TaskV { resumes: Seq::empty(), ..t@ }), ..s@ }));
            let r = one(Out { resp: status_res(300), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("suspend: awaited already settled (300)")) });

            return r;
        }
        u.state = TaskState::Suspended;
        u.pid = None;
        u.ttl = None;
        u.acquired_at = 0;
        u.retry_at = None;
        u.resumes = Vec::new();
        n.tasks.insert(id.clone(), u);
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
                n@.tasks == s@.tasks.insert(id@, TaskV { state: TaskState::Suspended, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Seq::empty(), ..t@ }),
                n@.schedules == s@.schedules,
            decreases ids.len() - i,
        {
            proof {
                assert(idv.take(i + 1) =~= idv.take(i as int).push(idv[i as int]));
                assert(idv.take(i + 1).drop_last() =~= idv.take(i as int));
            }
            assert(idv[i as int] == ids@[i as int]@);
            match n.promises.get(&ids[i]) {
                Some(p) => {
                    let mut q = copy(p);
                    q.callbacks.insert(id.clone());
                    n.promises.insert(ids[i].clone(), q);
                },
                None => {},
            }
            i += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }

        let r = one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task suspended")) });

        r
    }

    pub(super) fn task_fence(&self, req: &echod_types::TaskFenceReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        let id = &req.id;
        let version = req.version;
        let target = match &req.action {
            TaskFenceAction::Create(c) => &c.id,
            TaskFenceAction::Settle(st) => &st.id,
        };
        if target == id {
            return status(fence_res(400, None), mk("fence: targets its own task (400)"), s);
        }
        match &req.action {
            TaskFenceAction::Settle(st) => {
                if !same_origin(&st.id, id) {
                    return status(fence_res(400, None), mk("fence: settle in another origin (400)"), s);
                }
            },
            TaskFenceAction::Create(c) => {
                if !same_origin(&c.id, id) {
                    return self.task_fence_detached(id, version, c, s, now);
                }
            },
        }
        match self.held(s, id, version) {
            Err(code) => return status(fence_res(code, None), if code == 404 { mk("fence: no such task (404)") } else { mk("fence: not held, or stale version (409)") }, s),
            Ok(_) => {},
        }
        let create = matches!(req.action, TaskFenceAction::Create(_));
        let inner = match &req.action {
            TaskFenceAction::Create(c) => self.promise_create(c, true, s, now),
            TaskFenceAction::Settle(st) => self.promise_settle(st, true, s, now),
        };
        self.wrap_fence(inner, create)
    }

    /// The action's promise response, inside a fence that held.
    fn wrap_fence(&self, mut outs: Vec<Out>, create: bool) -> (r: Vec<Out>) {
        if outs.len() == 1 {
            let o = outs.remove(0);
            let Out { resp, next, work, send, marks } = o;
            let resp = match resp {
                Response::Promise(p) => {
                    let action = if create { TaskFenceInnerRes::Create(p) } else { TaskFenceInnerRes::Settle(p) };
                    fence_res(200, Some(action))
                },
                other => other,
            };
            return one(Out { resp, next, work, send, marks });
        }
        outs
    }

    /// A fence that creates a promise in another origin: a detached workflow.
    /// The create goes first, as a request of its own in its origin; then the
    /// fence's check on the task decides the answer. A stale fence still
    /// leaves the promise created.
    fn task_fence_detached(&self, id: &Id, version: u64, c: &PromiseCreateReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        let mut outs = self.promise_create(c, true, s, now);

        if outs.len() != 1 {
            return outs;  // unreachable: a create has one outcome
        }
        let o = outs.pop().unwrap();
        let ghost ov = o@;

        let Out { resp, next, work, send, mut marks } = o;
        assert(next@ == ov.next);
        assert(works(work@) == ov.work);
        assert(sends(send@) == ov.send);
        let inner = match resp {
            Response::Promise(p) => p,
            other => return one(Out { resp: other, next, work, send, marks }),
        };
        match self.held(&next, id, version) {
            Err(code) => {
                marks.push(if code == 404 { mk("fence: detached create, no such task (404)") } else { mk("fence: detached create, not held (409)") });
                let r = one(Out { resp: fence_res(code, None), next, work, send, marks });

                r
            },
            Ok(_) => {
                marks.push(mk("fence: detached create"));
                let r = one(Out { resp: fence_res(200, Some(TaskFenceInnerRes::Create(inner))), next, work, send, marks });

                r
            },
        }
    }

    pub(super) fn task_heartbeat(&self, pid: &String, refs: &Vec<TaskRef>, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        let ghost rv = refs@.map_values(|r: TaskRef| r@);
        let mut i = 1;
        while i < refs.len()
            invariant
                1 <= i,
                rv == refs@.map_values(|r: TaskRef| r@),
                forall|j: int| 1 <= j < i ==> origin(#[trigger] rv[j].id) == origin(rv[0].id),
            decreases refs.len() - i,
        {
            if !same_origin(&refs[i].id, &refs[0].id) {
                assert(rv[i as int] == refs@[i as int]@);
                assert(rv[0] == refs@[0]@);
                assert(origin(rv[i as int].id) != origin(rv[0].id));

                return status(status_res(400), mk("heartbeat: tasks in several origins (400)"), s);
            }
            i += 1;
        }

        let mut n = copy_server(s);
        let mut work = Vec::new();
        let mut extended = false;
        let mut i = 0;
        while i < refs.len()
            invariant
                i <= refs.len(),
                rv == refs@.map_values(|r: TaskRef| r@),
            decreases refs.len() - i,
        {
            proof {
                assert(rv.take(i + 1) =~= rv.take(i as int).push(rv[i as int]));
                assert(rv.take(i + 1).drop_last() =~= rv.take(i as int));
            }
            let r = &refs[i];
            assert(rv[i as int] == r@);

            match self.held(s, &r.id, r.version) {
                Ok(t) => {
                    let mine = match &t.pid {
                        Some(holder) => *holder == *pid,
                        None => false,
                    };
                    assert(mine == (t@.pid is Some && t@.pid.unwrap() == pid@));
                    if mine {
                        let mut u = copy(t);
                        u.acquired_at = now;
                        assert(u@ == (TaskV { acquired_at: now, ..t@ }));
                        let expires = u.lease_expires();

                        let ghost nt = n.tasks@;
                        n.tasks.insert(r.id.clone(), u);
                        assert(n.tasks@ == nt.insert(r.id@, u));
                        assert(n.tasks@.map_values(|t: Task| t@) == nt.map_values(|t: Task| t@).insert(r.id@, u@));

                        let ghost before = works(work@);
                        let w = at(expires, &r.id);
                        work.push(w);
                        assert(works(work@) == before.push(w@));
                        extended = true;

                    }
                },
                Err(_) => {},
            }
            i += 1;
        }
        proof {
            assert(rv.take(refs.len() as int) =~= rv);
        }
        // Always 200: a heartbeat says nothing about what it kept.
        let mark = if extended { mk("lease extended") } else { mk("heartbeat: nothing held by this worker") };
        one(Out { resp: status_res(200), next: n, work, send: Vec::new(), marks: marked(mark) })
    }

    pub(super) fn schedule_create(&self, req: &ScheduleCreateReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        if has_colon(&req.id) {
            return status(schedule_res(400, None), mk("schedule: id with a colon (400)"), s);
        }
        if !has_target(&req.promise_tags) {
            return status(schedule_res(400, None), mk("schedule: promises without a target (400)"), s);
        }
        if is_timer(&req.promise_tags) && has_target(&req.promise_tags) {
            return status(schedule_res(400, None), mk("schedule: timer with target (400)"), s);
        }
        if !cron_valid(&req.cron) || req.next_run_at < now {
            return status(schedule_res(400, None), mk("schedule: invalid cron (400)"), s);
        }
        match s.schedules.get(&req.id) {
            Some(c) => return echo(schedule_res(200, Some(c.dup())), mk("schedule: id exists (echo)"), s),
            None => {},
        }
        let c = Schedule {
            id: req.id.clone(),
            cron: req.cron.clone(),
            promise_id: req.promise_id.clone(),
            promise_timeout: req.promise_timeout,
            promise_param: req.promise_param.dup(),
            promise_tags: echod_types::clone_tags(&req.promise_tags),
            created_at: now,
            next_run_at: req.next_run_at,
            last_run_at: None,
        };
        let rec = schedule_res(200, Some(c.dup()));
        let mut n = copy_server(s);
        n.schedules.insert(req.id.clone(), c);
        let mut work = Vec::new();
        self.arm_fire(&mut work, &req.id, req.next_run_at, &req.promise_id);
        one(Out { resp: rec, next: n, work, send: Vec::new(), marks: marked(mk("schedule created")) })
    }

    /// `task.fence` with no action: the check alone, after a detached create.
    pub(super) fn task_fence_check(&self, req: &TaskFenceCheckReq, s: &Server) -> (outs: Vec<Out>) {
        match self.held(s, &req.id, req.version) {
            Err(code) => status(status_res(code), if code == 404 { mk("fence: no such task (404)") } else { mk("fence: not held, or stale version (409)") }, s),
            Ok(_) => status(status_res(200), mk("fence check"), s),
        }
    }

    pub(super) fn promise_register_callback(&self, awaited: &Id, awaiter: &Id, s: &Server) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        if *awaited == *awaiter || !same_origin(awaited, awaiter) {
            return status(promise_res(400, None), mk("callback: itself or another origin (400)"), s);
        }
        let p = match s.promises.get(awaited) {
            Some(p) => p,
            None => return status(promise_res(404, None), mk("callback: no awaited promise (404)"), s),
        };
        let w = match s.promises.get(awaiter) {
            Some(w) => w,
            None => return status(promise_res(422, None), mk("callback: no awaiter promise (422)"), s),
        };
        if !s.tasks.contains_key(awaiter) || !p.external() {
            return status(promise_res(422, None), mk("callback: awaiter no task, or awaited not external (422)"), s);
        }
        let res = promise_res(200, Some(prec(awaited, p)));
        if !p.live() || !w.live() {
            return echo(res, mk("callback: one of them settled (echo)"), s);
        }
        let mut n = copy_server(s);
        let mut q = copy(p);
        q.callbacks.insert(awaiter.clone());
        n.promises.insert(awaited.clone(), q);
        one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("callback registered")) })
    }

    pub(super) fn promise_register_listener(&self, awaited: &Id, address: &String, s: &Server) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        if !address_valid(address) {
            return status(promise_res(400, None), mk("listener: bad address (400)"), s);
        }
        let p = match s.promises.get(awaited) {
            None => return status(promise_res(404, None), mk("listener: no such promise (404)"), s),
            Some(p) => p,
        };
        if !p.external() {
            return status(promise_res(422, None), mk("listener: promise not external (422)"), s);
        }
        let res = promise_res(200, Some(prec(awaited, p)));
        if !p.live() {
            return echo(res, mk("listener: promise settled (echo)"), s);
        }
        let mut n = copy_server(s);
        let mut q = copy(p);
        q.listeners.insert(address.clone());
        n.promises.insert(awaited.clone(), q);
        one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("listener registered")) })
    }

    pub(super) fn task_acquire(&self, id: &Id, version: u64, pid: &String, ttl: Time, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return status(claim_res(404, None, None), mk("acquire: no such task (404)"), s),
        };
        let p = match s.promises.get(id) {
            Some(p) => p,
            None => return status(claim_res(404, None, None), mk("acquire: no such task (404)"), s),  // unreachable
        };
        if t.state != TaskState::Pending || !p.live() || t.version != version || t.version >= MAX_VERSION as u64 {
            return status(claim_res(409, None, None), mk("acquire: not pending, or stale version (409)"), s);
        }
        let mut n = copy_server(s);
        let mut u = copy(t);
        u.acquire(t.version + 1, pid.clone(), ttl, now);
        let rec = claim_res(200, Some(trec(id, &u)), Some(prec(id, p)));
        n.tasks.insert(id.clone(), u);
        let mut work = Vec::new();
        work.push(at(now.saturating_add(ttl), id));
        one(Out { resp: rec, next: n, work, send: Vec::new(), marks: marked(mk("task acquired")) })
    }

    pub(super) fn task_release(&self, id: &Id, version: u64, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        match self.held(s, id, version) {
            Err(code) => status(status_res(code), if code == 404 { mk("release: no such task (404)") } else { mk("release: not held (409)") }, s),
            Ok(t) => {
                let mut n = copy_server(s);
                let mut u = copy(t);
                u.release(now);
                n.tasks.insert(id.clone(), u);
                let mut work = Vec::new();
                work.push(at(now, id));
                one(Out { resp: status_res(200), next: n, work, send: Vec::new(), marks: marked(mk("task released")) })
            },
        }
    }

    pub(super) fn task_fulfill(&self, id: &Id, version: u64, action: &PromiseSettleReq, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        if !action.state.settable() {
            return status(promise_res(400, None), mk("fulfill: not a settled state (400)"), s);
        }
        match self.held(s, id, version) {
            Err(code) => return status(promise_res(code, None), if code == 404 { mk("fulfill: no such task (404)") } else { mk("fulfill: not held (409)") }, s),
            Ok(_) => {},
        }
        let work = match s.promises.get(id) {
            Some(p) => settled_work(p, id),
            None => Vec::new(),
        };
        let mut n = copy_server(s);
        settle(&mut n, id, action.state, &action.value, now);
        let res = match n.promises.get(id) {
            Some(q) => promise_res(200, Some(prec(id, q))),
            None => promise_res(500, None), // unreachable: held checked the promise
        };
        one(Out { resp: res, next: n, work, send: Vec::new(), marks: marked(mk("task fulfilled")) })
    }

    pub(super) fn task_halt(&self, id: &Id, s: &Server) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return status(status_res(404), mk("halt: no such task (404)"), s),
        };
        match t.state {
            TaskState::Fulfilled => status(status_res(409), mk("halt: task done (409)"), s),
            TaskState::Halted => status(status_res(200), mk("halt: already halted (echo)"), s),
            _ => {
                let mut n = copy_server(s);
                let mut u = copy(t);
                u.state = TaskState::Halted;
                u.pid = None;
                u.ttl = None;
                u.acquired_at = 0;
                u.retry_at = None;
                n.tasks.insert(id.clone(), u);
                one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task halted")) })
            },
        }
    }

    pub(super) fn task_continue(&self, id: &Id, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return status(status_res(404), mk("continue: no such task (404)"), s),
        };
        let live = match s.promises.get(id) {
            Some(p) => p.live(),
            None => false,
        };
        if t.state != TaskState::Halted || !live {
            return status(status_res(409), mk("continue: not halted (409)"), s);
        }
        let mut n = copy_server(s);
        let mut u = copy(t);
        u.state = TaskState::Pending;
        u.retry_at = Some(now);
        n.tasks.insert(id.clone(), u);
        let mut work = Vec::new();
        work.push(at(now, id));
        one(Out { resp: status_res(200), next: n, work, send: Vec::new(), marks: marked(mk("task continued")) })
    }

    pub(super) fn schedule_delete(&self, id: &Id, s: &Server) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        match s.schedules.get(id) {
            None => status(status_res(404), mk("delete schedule: none (404)"), s),
            Some(_) => {
                let mut n = copy_server(s);
                n.schedules.remove(id);
                one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("schedule deleted")) })
            },
        }
    }

}

} // verus!
