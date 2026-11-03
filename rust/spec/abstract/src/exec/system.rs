//! The match. `run` is one request. `run_work` is one due item.

use vstd::prelude::*;

use echod_types::Request;

#[cfg(verus_keep_ghost)]
use super::super::spec::group_views;

use super::{
    echo, mk, prec, promise_res, schedule_res, status, task_get_res, trec, InOut, Out, Resonate, Server, Time, Work,
};

verus! {

impl Resonate {

    /// A request takes effect in `s` at time `now`: every allowed outcome.
    pub fn run(&self, op: &Request, s: &Server, now: Time) -> (outs: Vec<Out>)
        
    {
        broadcast use group_views;
        match op {
            Request::PromiseCreate(c) => self.promise_create(c, false, s, now),
            Request::PromiseGet(q) => match s.promises.get(&q.id) {
                None => status(promise_res(404, None), mk("get promise: none (404)"), s),
                Some(p) => echo(promise_res(200, Some(prec(&q.id, p))), mk("get promise"), s),
            },
            Request::PromiseSettle(st) => self.promise_settle(st, false, s, now),
            Request::PromiseRegisterCallback(q) => self.promise_register_callback(&q.awaited, &q.awaiter, s),
            Request::PromiseRegisterListener(q) => self.promise_register_listener(&q.awaited, &q.address, s),
            Request::TaskGet(q) => match s.tasks.get(&q.id) {
                None => status(task_get_res(404, None), mk("get task: none (404)"), s),
                Some(t) => echo(task_get_res(200, Some(trec(&q.id, t))), mk("get task"), s),
            },
            Request::TaskCreate(q) => self.task_create(&q.pid, q.ttl, &q.action, s, now),
            Request::TaskAcquire(q) => self.task_acquire(&q.id, q.version, &q.pid, q.ttl, s, now),
            Request::TaskRelease(q) => self.task_release(&q.id, q.version, s, now),
            Request::TaskFulfill(q) => self.task_fulfill(&q.id, q.version, &q.action, s, now),
            Request::TaskHeartbeat(q) => self.task_heartbeat(&q.pid, &q.tasks, s, now),
            Request::TaskSuspend(q) => self.task_suspend(q, s),
            Request::TaskFence(q) => self.task_fence(q, s, now),
            Request::TaskFenceCheck(q) => self.task_fence_check(q, s),
            Request::TaskHalt(q) => self.task_halt(&q.id, s),
            Request::TaskContinue(q) => self.task_continue(&q.id, s, now),
            Request::ScheduleCreate(c) => self.schedule_create(c, s, now),
            Request::ScheduleGet(q) => match s.schedules.get(&q.id) {
                None => status(schedule_res(404, None), mk("get schedule: none (404)"), s),
                Some(c) => echo(schedule_res(200, Some(c.dup())), mk("get schedule"), s),
            },
            Request::ScheduleDelete(q) => self.schedule_delete(&q.id, s),
        }
    }

    /// One due item at `now`: a deadline, a callback, a listener, a lease, a
    /// retry, a schedule, or one queued occurrence.
    pub fn run_work(&self, step: &Work, s: &Server, now: Time) -> (r: InOut) {
        match step {
            Work::PromiseTimeout(id) => self.promise_timeout(id, s, now),
            Work::Callback { awaited, awaiter } => self.callback(awaited, awaiter, s, now),
            Work::Listener { awaited, address } => self.listener(awaited, address, s, now),
            Work::Lease(id) => self.lease(id, s, now),
            Work::Retry(id) => self.retry(id, s, now),
            Work::Schedule { id, .. } => self.schedule(id, s, now),
            Work::Occurrence { promise, at, timeout, param, tags } => self.occurrence(promise, *at, *timeout, param, tags, s, now),
        }
    }
}

} // verus!
