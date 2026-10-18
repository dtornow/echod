//! External steps: the schedule handlers.

use vstd::prelude::*;

use crate::external::*;
use crate::object::clone_tags;
use crate::properties::*;
use crate::store::{AState, State};
use crate::types::*;

verus! {

impl Schedule {
    pub fn dup(&self) -> (r: Schedule)
        ensures r@ == self@,
    {
        Schedule {
            id: self.id.clone(),
            cron: self.cron.clone(),
            promise_id: self.promise_id.clone(),
            promise_timeout: self.promise_timeout,
            promise_param: self.promise_param.dup(),
            promise_tags: clone_tags(&self.promise_tags),
            next_run_at: self.next_run_at,
            last_run_at: self.last_run_at,
            created_at: self.created_at,
        }
    }
}

impl State {
    /// `schedule.get`.
    pub fn schedule_get(&mut self, req: &ScheduleGetReq, now: u64, cfg: &Config) -> (r: ScheduleRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 404,
    {
        proof { crate::frame::lemma_noop(now as nat, self@); }
        match self.find_schedule(&req.id) {
            None => ScheduleRes { status: 404, schedule: None },
            Some(i) => ScheduleRes { status: 200, schedule: Some(self.schedules[i].dup()) },
        }
    }

    /// `schedule.create`. `req.next_run_at` is `nextCron cron now`, from the
    /// caller's cron engine; it must not precede `now`.
    pub fn schedule_create(&mut self, req: &ScheduleCreateReq, now: u64, cfg: &Config) -> (r: ScheduleRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 400,
    {
        let ghost a = self@;
        if crate::tags::exec_timer_targeted(&req.promise_tags) || req.promise_timeout > MAX_TIME || req.next_run_at < now {
            proof { crate::frame::lemma_noop(now as nat, a); }
            return ScheduleRes { status: 400, schedule: None };
        }
        match self.find_schedule(&req.id) {
            Some(i) => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                ScheduleRes { status: 200, schedule: Some(self.schedules[i].dup()) }
            }
            None => {
                let c = Schedule {
                    id: req.id.clone(),
                    cron: req.cron.clone(),
                    promise_id: req.promise_id.clone(),
                    promise_timeout: req.promise_timeout,
                    promise_param: req.promise_param.dup(),
                    promise_tags: clone_tags(&req.promise_tags),
                    next_run_at: req.next_run_at,
                    last_run_at: None,
                    created_at: now,
                };
                let out = c.dup();
                self.push_schedule(c);
                proof { lemma_schedule_create_legal(now as nat, a, self@, req.id@); }
                ScheduleRes { status: 200, schedule: Some(out) }
            }
        }
    }

    /// `schedule.delete`.
    pub fn schedule_delete(&mut self, req: &ScheduleDeleteReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 404,
    {
        let ghost a = self@;
        match self.find_schedule(&req.id) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                StatusRes { status: 404 }
            }
            Some(i) => {
                self.remove_schedule(i);
                proof { lemma_schedule_delete_legal(now as nat, a, self@, req.id@); }
                StatusRes { status: 200 }
            }
        }
    }
}

/// A schedule row written or removed, objects and outbox untouched.
pub proof fn lemma_schedule_create_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        !a.schedules.contains_key(id),
        b.schedules.contains_key(id),
        b.schedules[id].id == id,
        b.schedules[id].created_at == now,
        b.schedules[id].last_run_at is None,
        b.schedules[id].next_run_at >= now,
        !crate::tags::timer_targeted(b.schedules[id].promise_tags),
        b.schedules[id].promise_timeout <= MAX_TIME as nat,
        forall|x: Seq<char>| x != id ==>
            (a.schedules.contains_key(x) <==> #[trigger] b.schedules.contains_key(x))
            && (a.schedules.contains_key(x) ==> a.schedules[x] == b.schedules[x]),
        b.objects == a.objects,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_sched(now, b, id));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| false, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| x == id);
}

pub proof fn lemma_schedule_delete_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        !b.schedules.contains_key(id),
        forall|x: Seq<char>| x != id ==>
            (a.schedules.contains_key(x) <==> #[trigger] b.schedules.contains_key(x))
            && (a.schedules.contains_key(x) ==> a.schedules[x] == b.schedules[x]),
        b.objects == a.objects,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| false, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| x == id);
}

} // verus!
