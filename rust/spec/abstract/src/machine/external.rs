//! Request handlers. A promise, a task, or a schedule changes here, and the
//! `ensures` on each handler is that transition.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use echod_types::{
    PromiseCreateReq, PromiseRecord, PromiseRegisterCallbackReq, PromiseSettleReq, PromiseState,
    Request, Response, Schedule, ScheduleCreateReq, TaskFenceAction, TaskFenceCheckReq,
    TaskFenceInnerRes, TaskFenceReq, TaskRecord, TaskRef, TaskState, TaskSuspendReq, Value,
};

use super::super::trusted::*;
use echod_rover::certificate::trusted::copy;
#[cfg(verus_keep_ghost)]
use echod_types::{origin, same_origin_spec};
#[cfg(verus_keep_ghost)]
use super::super::view::{
    all_in_origin, distinct, group_views, lift_dispatch, sat_add, sends, strs, works, DispatchV,
    InOutV, OutV, PromiseV, ScheduleV,
};
use super::super::view::{StoreV, TaskV};
#[cfg(verus_keep_ghost)]
use super::super::view::spec_keys;
#[cfg(verus_keep_ghost)]
use super::{
    spec_acquire, spec_claim_res, spec_empty_value, spec_has_target, spec_is_timer,
    spec_external, spec_fence_res, spec_fulfill, spec_is_global, spec_new_object, spec_out,
    spec_project_promise, spec_project_task, spec_promise_record, spec_promise_res,
    spec_schedule_res, spec_schedule_value, spec_settle, spec_status_res, spec_string,
    spec_task_get_res, spec_task_record, spec_unlease,
};

use super::{
    claim_res, contains, copy_store, echo, fence_res, has_target, is_timer, marked, mk, new_object,
    next_cron, one, promise_res, schedule_res, settle, status, status_res, task_get_res, Id, Out,
    Promise, ServerConfig, Store, Task, Time,
};

#[cfg(verus_keep_ghost)]
use super::{promise_ok, response_ok, server_ok};

verus! {

impl ServerConfig {
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
    pub fn promise_create(&self, req: &PromiseCreateReq, fenced: bool, s: &Store, now: Time) -> (outs: Vec<Out>)
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
        match s.promises.get(&req.id) {
            Some(p) => {
                proof {
                    if server_ok(*s) {
                        assert(promise_ok(s.promises@[req.id@]));
                    }
                }
                let seen = p.project(now);
                return echo(promise_res(200, Some(seen.to_record(&req.id))), mk("create: id exists (echo)"), s);
            },
            None => {},
        }
        let live = req.timeout_at > now;
        let (p, task) = new_object(req.timeout_at, now, now, &req.param, &req.tags, has_target(&req.tags));
        let rec = p.to_record(&req.id);
        let mut n = copy_store(s);
        n.promises.insert(req.id.clone(), p);
        if let Some(task) = task {
            n.tasks.insert(req.id.clone(), task);
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
        let outs = one(Out { resp: promise_res(200, Some(rec)), next: n, work: Vec::new(), send: Vec::new(), marks });

        outs
    }

    pub(crate) fn promise_settle(&self, req: &PromiseSettleReq, fenced: bool, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        if !req.state.settable() {
            return status(promise_res(400, None), mk("settle: not a settled state (400)"), s);
        }
        let stored = match s.promises.get(&req.id) {
            Some(p) => p,
            None => return status(promise_res(404, None), mk("settle: no such promise (404)"), s),
        };
        let p = stored.project(now);
        if p.state != PromiseState::Pending {
            return echo(promise_res(200, Some(p.to_record(&req.id))), mk("settle: already settled (echo)"), s);
        }
        let noted = !p.callbacks.to_vec().is_empty() || !p.listeners.to_vec().is_empty();
        let mut n = copy_store(s);
        settle(&mut n, &req.id, req.state, &req.value, now);
        let res = match n.promises.get(&req.id) {
            Some(q) => promise_res(200, Some(q.to_record(&req.id))),
            None => promise_res(500, None), // unreachable: the promise exists
        };
        let mut marks = Vec::new();
        marks.push(if fenced { mk("fence: promise settled") } else { mk("promise settled") });
        if noted {
            marks.push(mk("settled with callbacks or listeners"));
        }
        one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks })
    }

    /// The checks every task.* mutation shares: exists, acquired, own promise live,
    /// version matches. `Ok` is the task.
    /// Acquired, own promise still pending as of `now`, version matches.
    /// `Ok` is the stored task, which agrees with its projection.
    fn held<'a>(&self, s: &'a Store, id: &Id, version: u64, now: Time) -> (r: Result<&'a Task, u16>)

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
        let seen = match s.promises.get(id) {
            Some(p) => t.project(&p.project(now)).state,
            None => t.state,
        };
        let live = match s.promises.get(id) {
            Some(p) => p.project(now).state == PromiseState::Pending,
            None => false,
        };

        if seen != TaskState::Acquired || !live || t.version != version {
            return Err(409);
        }

        Ok(t)
    }

    pub(crate) fn task_create(&self, pid: &String, ttl: Time, req: &PromiseCreateReq, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        if !has_target(&req.tags) || is_timer(&req.tags) {
            return status(claim_res(400, None, None), mk("task.create: not runnable, or a timer (400)"), s);
        }
        match s.promises.get(&req.id) {
            Some(p) => {
                if !has_target(&p.tags) {
                    return status(claim_res(422, None, None), mk("task.create: promise exists, not a target (422)"), s);
                }
                let stored_task = match s.tasks.get(&req.id) {
                    Some(t) => t,
                    None => return status(claim_res(409, None, None), mk("task.create: target without a task (409)"), s),  // unreachable
                };
                let seen_p = p.project(now);
                let seen_t = stored_task.project(&seen_p);
                return match seen_t.state {
                    TaskState::Fulfilled => echo(claim_res(200, Some(seen_t.to_record(&req.id)), Some(seen_p.to_record(&req.id))), mk("task.create: task done (echo)"), s),
                    TaskState::Pending => {
                        let mut n = copy_store(s);
                        let mut u = copy(stored_task);
                        u.acquire(stored_task.version.saturating_add(1), pid.clone(), ttl, now);
                        let rec = claim_res(200, Some(u.to_record(&req.id)), Some(seen_p.to_record(&req.id)));
                        n.tasks.insert(req.id.clone(), u);

                        assert(n@ == (StoreV { tasks: s@.tasks.insert(req.id@, u@), ..s@ }));
                        one(Out { resp: rec, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task.create: pending task acquired")) })
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
        let mut t = Task { state: TaskState::Fulfilled, version: 0, pid: None, ttl: None, acquired_at: 0, retry_timeout_at: None, resumes: Vec::new() };
        if live {
            // Acquired by the caller right away: nothing to dispatch.
            t.acquire(1, pid.clone(), ttl, now);
        }

        let res = claim_res(200, Some(t.to_record(&req.id)), Some(p.to_record(&req.id)));
        let ghost pv = p@;
        let ghost tv = t@;
        let mut n = copy_store(s);
        n.promises.insert(req.id.clone(), p);
        n.tasks.insert(req.id.clone(), t);
        assert(n@ == (StoreV { promises: s@.promises.insert(req.id@, pv), tasks: s@.tasks.insert(req.id@, tv), ..s@ }));
        let mark = if live { mk("task created") } else { mk("task created past its deadline") };
        one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mark) })
    }

    pub(crate) fn task_suspend(&self, req: &TaskSuspendReq, s: &Store, now: Time) -> (outs: Vec<Out>)

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
        let t = match self.held(s, id, version, now) {
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
                        return status(status_res(422), mk("suspend: awaited not awaitable (422)"), s);
                    }
                    let ghost was = settled;
                    settled = settled || p.project(now).state != PromiseState::Pending;

                },
            }
            i += 1;
        }
        proof {
            assert(idv.take(ids.len() as int) =~= idv);
        }
        let mut n = copy_store(s);
        let mut u = copy(t);

        if settled {
            // The task stays acquired and runs on; what it was told has been seen.
            u.resumes = Vec::new();
            assert(u@ == (TaskV { resumes: Seq::empty(), ..t@ }));
            n.tasks.insert(id.clone(), u);
            assert(n@ == (StoreV { tasks: s@.tasks.insert(id@, TaskV { resumes: Seq::empty(), ..t@ }), ..s@ }));
            let r = one(Out { resp: status_res(300), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("suspend: awaited already settled (300)")) });

            return r;
        }
        u.state = TaskState::Suspended;
        u.pid = None;
        u.ttl = None;
        u.acquired_at = 0;
        u.retry_timeout_at = None;
        u.resumes = Vec::new();
        n.tasks.insert(id.clone(), u);
        let mut i = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                idv == strs(ids@),
                n@.tasks == s@.tasks.insert(id@, TaskV { state: TaskState::Suspended, pid: None, ttl: None, acquired_at: 0, retry_timeout_at: None, resumes: Seq::empty(), ..t@ }),
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

    pub(crate) fn task_fence(&self, req: &echod_types::TaskFenceReq, s: &Store, now: Time) -> (outs: Vec<Out>)

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
                    return status(fence_res(400, None), mk("fence: create in another origin (400)"), s);
                }
            },
        }
        match self.held(s, id, version, now) {
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

    pub(crate) fn task_heartbeat(&self, pid: &String, refs: &Vec<TaskRef>, s: &Store, now: Time) -> (outs: Vec<Out>)

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

        let mut n = copy_store(s);
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

            match self.held(s, &r.id, r.version, now) {
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

                        let ghost nt = n.tasks@;
                        n.tasks.insert(r.id.clone(), u);
                        assert(n.tasks@ == nt.insert(r.id@, u));
                        assert(n.tasks@.map_values(|t: Task| t@) == nt.map_values(|t: Task| t@).insert(r.id@, u@));
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
        one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mark) })
    }

    pub(crate) fn schedule_create(&self, req: &ScheduleCreateReq, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        if is_timer(&req.promise_tags) && has_target(&req.promise_tags) {
            return status(schedule_res(400, None), mk("schedule: timer with target (400)"), s);
        }
        match s.schedules.get(&req.id) {
            Some(c) => return echo(schedule_res(200, Some(c.dup())), mk("schedule: id exists (echo)"), s),
            None => {},
        }
        // `next_run_at` is the server's: the first instant the cron names
        // strictly after now. The request does not carry it.
        let next_run_at = next_cron(&req.cron, now);
        let c = Schedule {
            id: req.id.clone(),
            cron: req.cron.clone(),
            promise_id: req.promise_id.clone(),
            promise_timeout: req.promise_timeout,
            promise_param: req.promise_param.dup(),
            promise_tags: echod_types::clone_tags(&req.promise_tags),
            created_at: now,
            next_run_at,
            last_run_at: None,
        };
        let rec = schedule_res(200, Some(c.dup()));
        let mut n = copy_store(s);
        n.schedules.insert(req.id.clone(), c);
        one(Out { resp: rec, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("schedule created")) })
    }

    /// `task.fence` with no action: the check alone.
    pub(crate) fn task_fence_check(&self, req: &TaskFenceCheckReq, s: &Store, now: Time) -> (outs: Vec<Out>) {
        match self.held(s, &req.id, req.version, now) {
            Err(code) => status(status_res(code), if code == 404 { mk("fence: no such task (404)") } else { mk("fence: not held, or stale version (409)") }, s),
            Ok(_) => status(status_res(200), mk("fence check"), s),
        }
    }

    pub(crate) fn promise_register_callback(&self, awaited: &Id, awaiter: &Id, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        if *awaited == *awaiter || !same_origin(awaited, awaiter) {
            return status(promise_res(400, None), mk("callback: itself or another origin (400)"), s);
        }
        let stored = match s.promises.get(awaited) {
            Some(p) => p,
            None => return status(promise_res(404, None), mk("callback: no awaited promise (404)"), s),
        };
        let stored_w = match s.promises.get(awaiter) {
            Some(w) => w,
            None => return status(promise_res(422, None), mk("callback: no awaiter promise (422)"), s),
        };
        let p = stored.project(now);
        let w = stored_w.project(now);
        if !has_target(&w.tags) || !p.external() {
            return status(promise_res(422, None), mk("callback: awaiter not runnable, or awaited not awaitable (422)"), s);
        }
        let res = promise_res(200, Some(p.to_record(awaited)));
        if p.state != PromiseState::Pending || w.state != PromiseState::Pending {
            return echo(res, mk("callback: one of them settled (echo)"), s);
        }
        let mut n = copy_store(s);
        let mut q = p;
        q.callbacks.insert(awaiter.clone());
        n.promises.insert(awaited.clone(), q);
        one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("callback registered")) })
    }

    pub(crate) fn promise_register_listener(&self, awaited: &Id, address: &String, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        let stored = match s.promises.get(awaited) {
            None => return status(promise_res(404, None), mk("listener: no such promise (404)"), s),
            Some(p) => p,
        };
        let p = stored.project(now);
        if !p.external() {
            return status(promise_res(422, None), mk("listener: promise not awaitable (422)"), s);
        }
        let res = promise_res(200, Some(p.to_record(awaited)));
        if p.state != PromiseState::Pending {
            return echo(res, mk("listener: promise settled (echo)"), s);
        }
        let mut n = copy_store(s);
        let mut q = p;
        q.listeners.insert(address.clone());
        n.promises.insert(awaited.clone(), q);
        one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("listener registered")) })
    }

    pub(crate) fn task_acquire(&self, id: &Id, version: u64, pid: &String, ttl: Time, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return status(claim_res(404, None, None), mk("acquire: no such task (404)"), s),
        };
        let stored_p = match s.promises.get(id) {
            Some(p) => p,
            None => return status(claim_res(404, None, None), mk("acquire: no such task (404)"), s),  // unreachable
        };
        let p = stored_p.project(now);
        let seen = t.project(&p);
        if seen.state != TaskState::Pending || p.state != PromiseState::Pending || t.version != version {
            return status(claim_res(409, None, None), mk("acquire: not pending, or stale version (409)"), s);
        }
        let mut n = copy_store(s);
        let mut u = copy(t);
        u.acquire(t.version.saturating_add(1), pid.clone(), ttl, now);
        let rec = claim_res(200, Some(u.to_record(id)), Some(p.to_record(id)));
        n.tasks.insert(id.clone(), u);
        one(Out { resp: rec, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task acquired")) })
    }

    pub(crate) fn task_release(&self, id: &Id, version: u64, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        match self.held(s, id, version, now) {
            Err(code) => status(status_res(code), if code == 404 { mk("release: no such task (404)") } else { mk("release: not held (409)") }, s),
            Ok(t) => {
                let mut n = copy_store(s);
                let mut u = copy(t);
                u.unlease(TaskState::Pending, Some(now));
                n.tasks.insert(id.clone(), u);
                one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task released")) })
            },
        }
    }

    pub(crate) fn task_fulfill(&self, id: &Id, version: u64, action: &PromiseSettleReq, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        if !action.state.settable() {
            return status(promise_res(400, None), mk("fulfill: not a settled state (400)"), s);
        }
        match self.held(s, id, version, now) {
            Err(code) => return status(promise_res(code, None), if code == 404 { mk("fulfill: no such task (404)") } else { mk("fulfill: not held (409)") }, s),
            Ok(_) => {},
        }
        let mut n = copy_store(s);
        settle(&mut n, id, action.state, &action.value, now);
        let res = match n.promises.get(id) {
            Some(q) => promise_res(200, Some(q.to_record(id))),
            None => promise_res(500, None), // unreachable: held checked the promise
        };
        one(Out { resp: res, next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task fulfilled")) })
    }

    pub(crate) fn task_halt(&self, id: &Id, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return status(status_res(404), mk("halt: no such task (404)"), s),
        };
        let seen = match s.promises.get(id) {
            Some(p) => t.project(&p.project(now)).state,
            None => t.state,
        };
        match seen {
            TaskState::Fulfilled => status(status_res(409), mk("halt: task done (409)"), s),
            TaskState::Halted => status(status_res(200), mk("halt: already halted (echo)"), s),
            _ => {
                let mut n = copy_store(s);
                let mut u = copy(t);
                u.unlease(TaskState::Halted, None);
                n.tasks.insert(id.clone(), u);
                one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task halted")) })
            },
        }
    }

    pub(crate) fn task_continue(&self, id: &Id, s: &Store, now: Time) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        let t = match s.tasks.get(id) {
            Some(t) => t,
            None => return status(status_res(404), mk("continue: no such task (404)"), s),
        };
        let live = match s.promises.get(id) {
            Some(p) => p.project(now).state == PromiseState::Pending,
            None => false,
        };
        if t.state != TaskState::Halted || !live {
            return status(status_res(409), mk("continue: not halted (409)"), s);
        }
        let mut n = copy_store(s);
        let mut u = copy(t);
        u.state = TaskState::Pending;
        u.retry_timeout_at = Some(now);
        n.tasks.insert(id.clone(), u);
        one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("task continued")) })
    }

    pub(crate) fn schedule_delete(&self, id: &Id, s: &Store) -> (outs: Vec<Out>)

    {
        broadcast use group_views;
        match s.schedules.get(id) {
            None => status(status_res(404), mk("delete schedule: none (404)"), s),
            Some(_) => {
                let mut n = copy_store(s);
                n.schedules.remove(id);
                one(Out { resp: status_res(200), next: n, work: Vec::new(), send: Vec::new(), marks: marked(mk("schedule deleted")) })
            },
        }
    }

    /// A request takes effect in `s` at time `now`: every allowed outcome.
    pub fn handler(&self, op: &Request, s: &Store, now: Time) -> (outs: Vec<Out>)
    {
        broadcast use group_views;
        match op {
            Request::PromiseCreate(c) => self.promise_create(c, false, s, now),
            Request::PromiseGet(q) => match s.promises.get(&q.id) {
                None => status(promise_res(404, None), mk("get promise: none (404)"), s),
                Some(p) => {
                    let seen = p.project(now);
                    echo(promise_res(200, Some(seen.to_record(&q.id))), mk("get promise"), s)
                },
            },
            Request::PromiseSettle(st) => self.promise_settle(st, false, s, now),
            Request::PromiseRegisterCallback(q) => self.promise_register_callback(&q.awaited, &q.awaiter, s, now),
            Request::PromiseRegisterListener(q) => self.promise_register_listener(&q.awaited, &q.address, s, now),
            Request::TaskGet(q) => match s.tasks.get(&q.id) {
                None => status(task_get_res(404, None), mk("get task: none (404)"), s),
                Some(t) => {
                    let seen = match s.promises.get(&q.id) {
                        Some(p) => t.project(&p.project(now)),
                        None => copy(t),
                    };
                    echo(task_get_res(200, Some(seen.to_record(&q.id))), mk("get task"), s)
                },
            },
            Request::TaskCreate(q) => self.task_create(&q.pid, q.ttl, &q.action, s, now),
            Request::TaskAcquire(q) => self.task_acquire(&q.id, q.version, &q.pid, q.ttl, s, now),
            Request::TaskRelease(q) => self.task_release(&q.id, q.version, s, now),
            Request::TaskFulfill(q) => self.task_fulfill(&q.id, q.version, &q.action, s, now),
            Request::TaskHeartbeat(q) => self.task_heartbeat(&q.pid, &q.tasks, s, now),
            Request::TaskSuspend(q) => self.task_suspend(q, s, now),
            Request::TaskFence(q) => self.task_fence(q, s, now),
            Request::TaskFenceCheck(q) => self.task_fence_check(q, s, now),
            Request::TaskHalt(q) => self.task_halt(&q.id, s, now),
            Request::TaskContinue(q) => self.task_continue(&q.id, s, now),
            Request::ScheduleCreate(c) => self.schedule_create(c, s, now),
            Request::ScheduleGet(q) => match s.schedules.get(&q.id) {
                None => status(schedule_res(404, None), mk("get schedule: none (404)"), s),
                Some(c) => echo(schedule_res(200, Some(c.dup())), mk("get schedule"), s),
            },
            Request::ScheduleDelete(q) => self.schedule_delete(&q.id, s),
        }
    }
}

// ---------------------------------------------------------------------------
// Requests, as a specification
// ---------------------------------------------------------------------------

#[allow(dead_code)]
pub enum SpecHeld {
    Ok(TaskV),
    Missing,
    Stale,
}

pub open spec fn spec_held(s: StoreV, id: Seq<char>, version: u64, now: Time) -> SpecHeld {
    if !s.tasks.contains_key(id) {
        SpecHeld::Missing
    } else {
        let t = s.tasks[id];
        let seen = if s.promises.contains_key(id) {
            spec_project_task(t, spec_project_promise(s.promises[id], now)).state
        } else {
            t.state
        };
        let live = s.promises.contains_key(id)
            && spec_project_promise(s.promises[id], now).state == PromiseState::Pending;
        if seen != TaskState::Acquired || !live || t.version != version {
            SpecHeld::Stale
        } else {
            SpecHeld::Ok(t)
        }
    }
}

pub open spec fn spec_promise_create(req: PromiseCreateReq, s: StoreV, now: Time) -> Seq<OutV> {
    if spec_is_timer(req.tags) && spec_has_target(req.tags) {
        spec_out(spec_promise_res(400, None), s)
    } else if s.promises.contains_key(req.id@) {
        let seen = spec_project_promise(s.promises[req.id@], now);
        spec_out(spec_promise_res(200, Some(spec_promise_record(req.id, seen))), s)
    } else {
        let (p, task) = spec_new_object(req.timeout_at, now, now, req.param, req.tags, spec_has_target(req.tags));
        let rec = spec_promise_record(req.id, p);
        let promises = s.promises.insert(req.id@, p);
        let tasks = match task {
            Some(t) => s.tasks.insert(req.id@, t),
            None => s.tasks,
        };
        spec_out(spec_promise_res(200, Some(rec)), StoreV { promises, tasks, ..s })
    }
}

pub open spec fn spec_promise_settle(req: PromiseSettleReq, s: StoreV, now: Time) -> Seq<OutV> {
    if !req.state.spec_settable() {
        spec_out(spec_promise_res(400, None), s)
    } else if !s.promises.contains_key(req.id@) {
        spec_out(spec_promise_res(404, None), s)
    } else {
        let p = spec_project_promise(s.promises[req.id@], now);
        if p.state != PromiseState::Pending {
            spec_out(spec_promise_res(200, Some(spec_promise_record(req.id, p))), s)
        } else {
            let n = spec_settle(s, req.id@, req.state, req.value, now);
            let res = if n.promises.contains_key(req.id@) {
                spec_promise_res(200, Some(spec_promise_record(req.id, n.promises[req.id@])))
            } else {
                spec_promise_res(500, None)
            };
            spec_out(res, n)
        }
    }
}

pub open spec fn spec_task_create(pid: String, ttl: Time, req: PromiseCreateReq, s: StoreV, now: Time) -> Seq<OutV> {
    if !spec_has_target(req.tags) || spec_is_timer(req.tags) {
        spec_out(spec_claim_res(400, None, None), s)
    } else if s.promises.contains_key(req.id@) {
        let p = s.promises[req.id@];
        if !spec_has_target(p.tags) {
            spec_out(spec_claim_res(422, None, None), s)
        } else if !s.tasks.contains_key(req.id@) {
            spec_out(spec_claim_res(409, None, None), s)
        } else {
            let seen_p = spec_project_promise(p, now);
            let stored = s.tasks[req.id@];
            let seen_t = spec_project_task(stored, seen_p);
            match seen_t.state {
                TaskState::Fulfilled => spec_out(
                    spec_claim_res(200, Some(spec_task_record(req.id, seen_t)), Some(spec_promise_record(req.id, seen_p))),
                    s,
                ),
                TaskState::Pending => {
                    let u = spec_acquire(stored, sat_add(stored.version, 1), pid@, ttl, now);
                    let n = StoreV { tasks: s.tasks.insert(req.id@, u), ..s };
                    spec_out(
                        spec_claim_res(200, Some(spec_task_record(req.id, u)), Some(spec_promise_record(req.id, seen_p))),
                        n,
                    )
                },
                _ => spec_out(spec_claim_res(409, None, None), s),
            }
        }
    } else {
        let live = req.timeout_at > now;
        let p = PromiseV {
            state: if live { PromiseState::Pending } else { PromiseState::RejectedTimedout },
            value: spec_empty_value(),
            param: req.param,
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: req.tags,
            callbacks: Set::empty(),
            listeners: Set::empty(),
        };
        let born = TaskV {
            state: TaskState::Fulfilled,
            version: 0,
            pid: None,
            ttl: None,
            acquired_at: 0,
            retry_timeout_at: None,
            resumes: Seq::empty(),
        };
        let t = if live { spec_acquire(born, 1, pid@, ttl, now) } else { born };
        let n = StoreV {
            promises: s.promises.insert(req.id@, p),
            tasks: s.tasks.insert(req.id@, t),
            ..s
        };
        spec_out(
            spec_claim_res(200, Some(spec_task_record(req.id, t)), Some(spec_promise_record(req.id, p))),
            n,
        )
    }
}

pub open spec fn spec_awaited(actions: Seq<PromiseRegisterCallbackReq>) -> Seq<Seq<char>> {
    actions.map_values(|a: PromiseRegisterCallbackReq| a.awaited@)
}

pub open spec fn spec_callbacks(
    promises: Map<Seq<char>, PromiseV>,
    ids: Seq<Seq<char>>,
    awaiter: Seq<char>,
    i: int,
) -> Map<Seq<char>, PromiseV>
    decreases ids.len() - i,
{
    if i < 0 || i >= ids.len() {
        promises
    } else {
        let id = ids[i];
        let q = PromiseV { callbacks: promises[id].callbacks.insert(awaiter), ..promises[id] };
        spec_callbacks(promises.insert(id, q), ids, awaiter, i + 1)
    }
}

pub open spec fn spec_any_settled(s: StoreV, ids: Seq<Seq<char>>, now: Time, i: int) -> bool
    decreases ids.len() - i,
{
    if i < 0 || i >= ids.len() {
        false
    } else if !s.promises.contains_key(ids[i]) {
        false
    } else {
        spec_project_promise(s.promises[ids[i]], now).state != PromiseState::Pending
            || spec_any_settled(s, ids, now, i + 1)
    }
}

pub open spec fn spec_suspend(req_id: String, version: u64, actions: Seq<PromiseRegisterCallbackReq>, s: StoreV, now: Time) -> Seq<OutV> {
    let ids = spec_awaited(actions);
    let id = req_id@;
    if ids.len() == 0 || ids.contains(id) || !distinct(ids) || !all_in_origin(ids, id) {
        spec_out(spec_status_res(400), s)
    } else {
        match spec_held(s, id, version, now) {
            SpecHeld::Missing => spec_out(spec_status_res(404), s),
            SpecHeld::Stale => spec_out(spec_status_res(409), s),
            SpecHeld::Ok(t) => {
                if exists|i: int| 0 <= i < ids.len() && !s.promises.contains_key(ids[i]) {
                    spec_out(spec_status_res(422), s)
                } else if exists|i: int|
                    0 <= i < ids.len() && !spec_external(s.promises[ids[i]])
                {
                    spec_out(spec_status_res(422), s)
                } else if spec_any_settled(s, ids, now, 0) {
                    let u = TaskV { resumes: Seq::empty(), ..t };
                    spec_out(spec_status_res(300), StoreV { tasks: s.tasks.insert(id, u), ..s })
                } else {
                    let u = TaskV {
                        state: TaskState::Suspended,
                        pid: None,
                        ttl: None,
                        acquired_at: 0,
                        retry_timeout_at: None,
                        resumes: Seq::empty(),
                        ..t
                    };
                    let tasks = s.tasks.insert(id, u);
                    let promises = spec_callbacks(s.promises, ids, id, 0);
                    spec_out(spec_status_res(200), StoreV { promises, tasks, ..s })
                }
            },
        }
    }
}

pub open spec fn spec_wrap_fence(outs: Seq<OutV>, create: bool) -> Seq<OutV> {
    if outs.len() != 1 {
        outs
    } else {
        let o = outs[0];
        match o.resp {
            Response::Promise(inner) => {
                let action = if create { TaskFenceInnerRes::Create(inner) } else { TaskFenceInnerRes::Settle(inner) };
                seq![OutV { resp: spec_fence_res(200, Some(action)), ..o }]
            },
            _ => outs,
        }
    }
}

pub open spec fn spec_fence(req: TaskFenceReq, s: StoreV, now: Time) -> Seq<OutV> {
    let id = req.id;
    let target = match req.action {
        TaskFenceAction::Create(c) => c.id,
        TaskFenceAction::Settle(st) => st.id,
    };
    if target@ == id@ {
        spec_out(spec_fence_res(400, None), s)
    } else {
        match req.action {
            TaskFenceAction::Settle(st) if !same_origin_spec(st.id@, id@) => {
                spec_out(spec_fence_res(400, None), s)
            },
            TaskFenceAction::Create(c) if !same_origin_spec(c.id@, id@) => {
                spec_out(spec_fence_res(400, None), s)
            },
            action => match spec_held(s, id@, req.version, now) {
                SpecHeld::Missing => spec_out(spec_fence_res(404, None), s),
                SpecHeld::Stale => spec_out(spec_fence_res(409, None), s),
                SpecHeld::Ok(_) => {
                    let create = match action {
                        TaskFenceAction::Create(_) => true,
                        TaskFenceAction::Settle(_) => false,
                    };
                    let inner = match action {
                        TaskFenceAction::Create(c) => spec_promise_create(c, s, now),
                        TaskFenceAction::Settle(st) => spec_promise_settle(st, s, now),
                    };
                    spec_wrap_fence(inner, create)
                },
            },
        }
    }
}

pub open spec fn spec_refs_one_origin(refs: Seq<TaskRef>, j: int) -> bool
    decreases refs.len() - j,
{
    if j < 1 || j >= refs.len() {
        true
    } else {
        origin(refs[j].id@) == origin(refs[0].id@) && spec_refs_one_origin(refs, j + 1)
    }
}

pub open spec fn spec_extend(
    s: StoreV,
    pid: Seq<char>,
    refs: Seq<TaskRef>,
    now: Time,
    i: int,
    tasks: Map<Seq<char>, TaskV>,
) -> Map<Seq<char>, TaskV>
    decreases refs.len() - i,
{
    if i < 0 || i >= refs.len() {
        tasks
    } else {
        let id = refs[i].id@;
        let next = match spec_held(s, id, refs[i].version, now) {
            SpecHeld::Ok(t) if t.pid == Some(pid) => {
                tasks.insert(id, TaskV { acquired_at: now, ..t })
            },
            _ => tasks,
        };
        spec_extend(s, pid, refs, now, i + 1, next)
    }
}

pub open spec fn spec_heartbeat(pid: String, refs: Seq<TaskRef>, s: StoreV, now: Time) -> Seq<OutV> {
    if refs.len() > 0 && !spec_refs_one_origin(refs, 1) {
        spec_out(spec_status_res(400), s)
    } else {
        let tasks = spec_extend(s, pid@, refs, now, 0, s.tasks);
        spec_out(spec_status_res(200), StoreV { tasks, ..s })
    }
}

pub open spec fn spec_schedule_create(req: ScheduleCreateReq, s: StoreV, now: Time) -> Seq<OutV> {
    if spec_is_timer(req.promise_tags) && spec_has_target(req.promise_tags) {
        spec_out(spec_schedule_res(400, None), s)
    } else if s.schedules.contains_key(req.id@) {
        spec_out(spec_schedule_res(200, Some(spec_schedule_value(s.schedules[req.id@]))), s)
    } else {
        let next_run_at = spec_next_cron(req.cron@, now);
        let c = ScheduleV {
            id: req.id@,
            cron: req.cron@,
            promise_id: req.promise_id@,
            promise_timeout: req.promise_timeout,
            promise_param: req.promise_param,
            promise_tags: req.promise_tags,
            created_at: now,
            next_run_at,
            last_run_at: None,
        };
        let rec = Schedule {
            id: req.id,
            cron: req.cron,
            promise_id: req.promise_id,
            promise_timeout: req.promise_timeout,
            promise_param: req.promise_param,
            promise_tags: req.promise_tags,
            created_at: now,
            next_run_at,
            last_run_at: None,
        };
        spec_out(spec_schedule_res(200, Some(rec)), StoreV { schedules: s.schedules.insert(req.id@, c), ..s })
    }
}

pub open spec fn spec_register_callback(awaited: String, awaiter: String, s: StoreV, now: Time) -> Seq<OutV> {
    if awaited@ == awaiter@ || !same_origin_spec(awaited@, awaiter@) {
        spec_out(spec_promise_res(400, None), s)
    } else if !s.promises.contains_key(awaited@) {
        spec_out(spec_promise_res(404, None), s)
    } else if !s.promises.contains_key(awaiter@) {
        spec_out(spec_promise_res(422, None), s)
    } else {
        let p = spec_project_promise(s.promises[awaited@], now);
        let w = spec_project_promise(s.promises[awaiter@], now);
        let res = spec_promise_res(200, Some(spec_promise_record(awaited, p)));
        if !spec_has_target(w.tags) || !spec_external(p) {
            spec_out(spec_promise_res(422, None), s)
        } else if p.state != PromiseState::Pending || w.state != PromiseState::Pending {
            spec_out(res, s)
        } else {
            let q = PromiseV { callbacks: p.callbacks.insert(awaiter@), ..p };
            spec_out(res, StoreV { promises: s.promises.insert(awaited@, q), ..s })
        }
    }
}

pub open spec fn spec_register_listener(awaited: String, address: String, s: StoreV, now: Time) -> Seq<OutV> {
    if !s.promises.contains_key(awaited@) {
        spec_out(spec_promise_res(404, None), s)
    } else {
        let p = spec_project_promise(s.promises[awaited@], now);
        if !spec_external(p) {
            spec_out(spec_promise_res(422, None), s)
        } else {
            let res = spec_promise_res(200, Some(spec_promise_record(awaited, p)));
            if p.state != PromiseState::Pending {
                spec_out(res, s)
            } else {
                let q = PromiseV { listeners: p.listeners.insert(address@), ..p };
                spec_out(res, StoreV { promises: s.promises.insert(awaited@, q), ..s })
            }
        }
    }
}

pub open spec fn spec_task_acquire(id: String, version: u64, pid: String, ttl: Time, s: StoreV, now: Time) -> Seq<OutV> {
    if !s.tasks.contains_key(id@) || !s.promises.contains_key(id@) {
        spec_out(spec_claim_res(404, None, None), s)
    } else {
        let t = s.tasks[id@];
        let p = spec_project_promise(s.promises[id@], now);
        let seen = spec_project_task(t, p);
        if seen.state != TaskState::Pending || p.state != PromiseState::Pending || t.version != version {
            spec_out(spec_claim_res(409, None, None), s)
        } else {
            let u = spec_acquire(t, sat_add(t.version, 1), pid@, ttl, now);
            spec_out(
                spec_claim_res(200, Some(spec_task_record(id, u)), Some(spec_promise_record(id, p))),
                StoreV { tasks: s.tasks.insert(id@, u), ..s },
            )
        }
    }
}

pub open spec fn spec_task_release(id: String, version: u64, s: StoreV, now: Time) -> Seq<OutV> {
    match spec_held(s, id@, version, now) {
        SpecHeld::Missing => spec_out(spec_status_res(404), s),
        SpecHeld::Stale => spec_out(spec_status_res(409), s),
        SpecHeld::Ok(t) => {
            let u = spec_unlease(t, TaskState::Pending, Some(now));
            spec_out(spec_status_res(200), StoreV { tasks: s.tasks.insert(id@, u), ..s })
        },
    }
}

pub open spec fn spec_task_fulfill(id: String, version: u64, action: PromiseSettleReq, s: StoreV, now: Time) -> Seq<OutV> {
    if !action.state.spec_settable() {
        spec_out(spec_promise_res(400, None), s)
    } else {
        match spec_held(s, id@, version, now) {
            SpecHeld::Missing => spec_out(spec_promise_res(404, None), s),
            SpecHeld::Stale => spec_out(spec_promise_res(409, None), s),
            SpecHeld::Ok(_) => {
                let n = spec_settle(s, id@, action.state, action.value, now);
                let res = if n.promises.contains_key(id@) {
                    spec_promise_res(200, Some(spec_promise_record(id, n.promises[id@])))
                } else {
                    spec_promise_res(500, None)
                };
                spec_out(res, n)
            },
        }
    }
}

pub open spec fn spec_task_halt(id: String, s: StoreV, now: Time) -> Seq<OutV> {
    if !s.tasks.contains_key(id@) {
        spec_out(spec_status_res(404), s)
    } else {
        let t = s.tasks[id@];
        let seen = if s.promises.contains_key(id@) {
            spec_project_task(t, spec_project_promise(s.promises[id@], now)).state
        } else {
            t.state
        };
        match seen {
            TaskState::Fulfilled => spec_out(spec_status_res(409), s),
            TaskState::Halted => spec_out(spec_status_res(200), s),
            _ => {
                let u = spec_unlease(t, TaskState::Halted, None);
                spec_out(spec_status_res(200), StoreV { tasks: s.tasks.insert(id@, u), ..s })
            },
        }
    }
}

pub open spec fn spec_task_continue(id: String, s: StoreV, now: Time) -> Seq<OutV> {
    if !s.tasks.contains_key(id@) {
        spec_out(spec_status_res(404), s)
    } else {
        let t = s.tasks[id@];
        let live = s.promises.contains_key(id@)
            && spec_project_promise(s.promises[id@], now).state == PromiseState::Pending;
        if t.state != TaskState::Halted || !live {
            spec_out(spec_status_res(409), s)
        } else {
            let u = TaskV { state: TaskState::Pending, retry_timeout_at: Some(now), ..t };
            spec_out(spec_status_res(200), StoreV { tasks: s.tasks.insert(id@, u), ..s })
        }
    }
}

pub open spec fn spec_handler(_config: ServerConfig, op: Request, s: StoreV, now: Time) -> Seq<OutV> {
    match op {
        Request::PromiseCreate(c) => spec_promise_create(c, s, now),
        Request::PromiseGet(q) => {
            if !s.promises.contains_key(q.id@) {
                spec_out(spec_promise_res(404, None), s)
            } else {
                let seen = spec_project_promise(s.promises[q.id@], now);
                spec_out(spec_promise_res(200, Some(spec_promise_record(q.id, seen))), s)
            }
        },
        Request::PromiseSettle(st) => spec_promise_settle(st, s, now),
        Request::PromiseRegisterCallback(q) => spec_register_callback(q.awaited, q.awaiter, s, now),
        Request::PromiseRegisterListener(q) => spec_register_listener(q.awaited, q.address, s, now),
        Request::TaskGet(q) => {
            if !s.tasks.contains_key(q.id@) {
                spec_out(spec_task_get_res(404, None), s)
            } else {
                let t = s.tasks[q.id@];
                let seen = if s.promises.contains_key(q.id@) {
                    spec_project_task(t, spec_project_promise(s.promises[q.id@], now))
                } else {
                    t
                };
                spec_out(spec_task_get_res(200, Some(spec_task_record(q.id, seen))), s)
            }
        },
        Request::TaskCreate(q) => spec_task_create(q.pid, q.ttl, q.action, s, now),
        Request::TaskAcquire(q) => spec_task_acquire(q.id, q.version, q.pid, q.ttl, s, now),
        Request::TaskRelease(q) => spec_task_release(q.id, q.version, s, now),
        Request::TaskFulfill(q) => spec_task_fulfill(q.id, q.version, q.action, s, now),
        Request::TaskHeartbeat(q) => spec_heartbeat(q.pid, q.tasks@, s, now),
        Request::TaskSuspend(q) => spec_suspend(q.id, q.version, q.actions@, s, now),
        Request::TaskFence(q) => spec_fence(q, s, now),
        Request::TaskFenceCheck(q) => match spec_held(s, q.id@, q.version, now) {
            SpecHeld::Missing => spec_out(spec_status_res(404), s),
            SpecHeld::Stale => spec_out(spec_status_res(409), s),
            SpecHeld::Ok(_) => spec_out(spec_status_res(200), s),
        },
        Request::TaskHalt(q) => spec_task_halt(q.id, s, now),
        Request::TaskContinue(q) => spec_task_continue(q.id, s, now),
        Request::ScheduleCreate(c) => spec_schedule_create(c, s, now),
        Request::ScheduleGet(q) => {
            if !s.schedules.contains_key(q.id@) {
                spec_out(spec_schedule_res(404, None), s)
            } else {
                spec_out(spec_schedule_res(200, Some(spec_schedule_value(s.schedules[q.id@]))), s)
            }
        },
        Request::ScheduleDelete(q) => {
            if !s.schedules.contains_key(q.id@) {
                spec_out(spec_status_res(404), s)
            } else {
                spec_out(spec_status_res(200), StoreV { schedules: s.schedules.remove(q.id@), ..s })
            }
        },
    }
}

} // verus!
