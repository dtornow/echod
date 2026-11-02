//! External steps: the request handlers.
//!
//! Each handler is `spec/02-abstract/external.lean`'s, under the
//! materialising reading (`mat = true`): a read projects the object at `now`
//! and persists what the projection moved. Every handler takes `now` and
//! the configuration, and ensures the whole catalogue: `inv` on the state it
//! leaves and `legal` on the pair. The promise handlers, then the schedule
//! handlers, then the task handlers: first those that touch one object, then
//! `task.fence`, which runs a promise handler on behalf of a task,
//! `task.heartbeat`, which refreshes many leases, and `task.suspend`, which
//! registers a task on many promises.
//!
//! The spec functions the contracts name are `echod_concrete::spec`. The
//! lemmas the bodies invoke are `echod_concrete::external_proof`.

use vstd::prelude::*;

use super::object::*;
use super::store::*;
use super::store_proof::*;
use super::tags::OType;
use super::types::*;

#[cfg(verus_keep_ghost)]
use super::external_proof::*;
#[cfg(verus_keep_ghost)]
use super::properties::*;
#[cfg(verus_keep_ghost)]
use super::properties_proof::*;
#[cfg(verus_keep_ghost)]
use super::spec::*;

verus! {

/// What every handler requires of its inputs.
pub open spec fn pre(s: State, now: u64, retry_timeout: u64) -> bool {
    &&& s.wf()
    &&& inv(now as nat, s@)
    &&& now <= MAX_TIME
    &&& 0 < retry_timeout <= MAX_TIME
}

/// What every handler ensures of its outputs.
pub open spec fn post(a: State, b: State, now: u64) -> bool {
    &&& b.wf()
    &&& inv(now as nat, b@)
    &&& legal(now as nat, a@, b@)
}


impl State {
    /// Any request: the handler for its kind. Computes `spec_handle`.
    pub fn handle(&mut self, req: &Request, now: u64, retry_timeout: u64) -> (r: Response)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_handle(old(self)@, req@, now as nat).0,
            r@ == spec_handle(old(self)@, req@, now as nat).1,
    {
        match req {
            Request::PromiseGet(q) => Response::Promise(self.promise_get(q, now, retry_timeout)),
            Request::PromiseCreate(q) => Response::Promise(self.promise_create(q, now, retry_timeout)),
            Request::PromiseSettle(q) => Response::Promise(self.promise_settle(q, now, retry_timeout)),
            Request::PromiseRegisterCallback(q) => Response::Promise(self.promise_register_callback(q, now, retry_timeout)),
            Request::PromiseRegisterListener(q) => Response::Promise(self.promise_register_listener(q, now, retry_timeout)),
            Request::ScheduleGet(q) => Response::Schedule(self.schedule_get(q, now, retry_timeout)),
            Request::ScheduleCreate(q) => Response::Schedule(self.schedule_create(q, now, retry_timeout)),
            Request::ScheduleDelete(q) => Response::Status(self.schedule_delete(q, now, retry_timeout)),
            Request::TaskGet(q) => Response::TaskGet(self.task_get(q, now, retry_timeout)),
            Request::TaskCreate(q) => Response::TaskClaim(self.task_create(q, now, retry_timeout)),
            Request::TaskAcquire(q) => Response::TaskClaim(self.task_acquire(q, now, retry_timeout)),
            Request::TaskFulfill(q) => Response::Promise(self.task_fulfill(q, now, retry_timeout)),
            Request::TaskRelease(q) => Response::Status(self.task_release(q, now, retry_timeout)),
            Request::TaskHalt(q) => Response::Status(self.task_halt(q, now, retry_timeout)),
            Request::TaskContinue(q) => Response::Status(self.task_continue(q, now, retry_timeout)),
            Request::TaskFence(q) => Response::TaskFence(self.task_fence(q, now, retry_timeout)),
            Request::TaskFenceCheck(q) => Response::Status(self.task_fence_check(q, now, retry_timeout)),
            Request::TaskHeartbeat(q) => Response::Status(self.task_heartbeat(q, now, retry_timeout)),
            Request::TaskSuspend(q) => Response::Status(self.task_suspend(q, now, retry_timeout)),
        }
    }

    /// `readObject`: find the object, project it at `now`, persist the
    /// projection. Returns its row index.
    pub fn read_object(&mut self, id: &String, now: u64) -> (r: Option<usize>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).schedules == old(self).schedules,
            final(self).outbox == old(self).outbox,
            final(self)@.schedules == old(self)@.schedules,
            final(self)@.outbox == old(self)@.outbox,
            match r {
                None => {
                    &&& !old(self)@.objects.contains_key(id@)
                    &&& *final(self) == *old(self)
                },
                Some(i) => {
                    &&& i < final(self).objects@.len()
                    &&& final(self).objects@ == old(self).objects@.update(i as int, final(self).objects@[i as int])
                    &&& old(self).objects@[i as int].id@ == id@
                    &&& final(self).objects@[i as int]@ == old(self).objects@[i as int]@.project(now as nat)
                    &&& final(self).objects@[i as int].id@ == id@
                    &&& old(self)@.objects.contains_key(id@)
                    &&& final(self).objects@[i as int]@ == old(self)@.objects[id@].project(now as nat)
                    &&& final(self)@.objects == old(self)@.objects.insert(id@, old(self)@.objects[id@].project(now as nat))
                },
            },
    {
        match self.find_object(id) {
            None => None,
            Some(i) => {
                let ghost before = self.objects@;
                proof {
                    self.lemma_object_at(i as int);
                }
                self.objects[i].project(now);
                proof {
                    super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
                }
                Some(i)
            }
        }
    }

    /// `promise.get`.
    pub fn promise_get(&mut self, req: &PromiseGetReq, now: u64, retry_timeout: u64) -> (r: PromiseRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_get(old(self)@, req@, now as nat).0,
            r@ == spec_promise_get(old(self)@, req@, now as nat).1,
            match r.promise {
                None => r.status == 404 && !old(self)@.objects.contains_key(req.id@),
                Some(p) => r.status == 200 && old(self)@.objects.contains_key(req.id@)
                    && p@ == old(self)@.objects[req.id@].project(now as nat).to_record(),
            },
    {
        let ghost a = self@;
        match self.read_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                PromiseRes { status: 404, promise: None }
            }
            Some(i) => {
                let rec = self.objects[i].to_record();
                proof {
                    lemma_project_legal(now as nat, a, self@, req.id@);
                }
                PromiseRes { status: 200, promise: Some(rec) }
            }
        }
    }

    /// `promise.create`.
    pub fn promise_create(&mut self, req: &PromiseCreateReq, now: u64, retry_timeout: u64) -> (r: PromiseRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_create(old(self)@, req@, now as nat).0,
            r@ == spec_promise_create(old(self)@, req@, now as nat).1,
            touches_only(old(self)@, final(self)@, |z: Seq<char>| z == req.id@),
            r.status == 200 || r.status == 400,
    {
        let ghost a = self@;
        if super::tags::exec_timer_targeted(&req.tags) || req.timeout_at > MAX_TIME {
            proof { super::properties_proof::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        match self.read_object(&req.id, now) {
            Some(i) => {
                let rec = self.objects[i].to_record();
                proof { lemma_project_legal(now as nat, a, self@, req.id@); }
                PromiseRes { status: 200, promise: Some(rec) }
            }
            None => {
                let p = create_promise(req, now);
                let rec = p.to_record();
                self.push_object(p);
                proof { lemma_create_legal(now as nat, a, self@, req@); }
                PromiseRes { status: 200, promise: Some(rec) }
            }
        }
    }

    /// `promise.settle`.
    pub fn promise_settle(&mut self, req: &PromiseSettleReq, now: u64, retry_timeout: u64) -> (r: PromiseRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_settle(old(self)@, req@, now as nat).0,
            r@ == spec_promise_settle(old(self)@, req@, now as nat).1,
            touches_only(old(self)@, final(self)@, |z: Seq<char>| z == req.id@),
            r.status == 200 || r.status == 400 || r.status == 404,
    {
        let ghost a = self@;
        if !req.state.settable() {
            proof { super::properties_proof::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        match self.read_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                PromiseRes { status: 404, promise: None }
            }
            Some(i) => {
                if self.objects[i].state == PromiseState::Pending {
                    let ghost before = self.objects@;
                    self.objects[i].settle(req.state, req.value.dup(), now);
                    proof {
                        super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
                        assert(self@.objects =~= a.objects.insert(req.id@, a.objects[req.id@].project(now as nat).settle(req.state, req.value@, now as nat)));
                        lemma_settle_legal(now as nat, a, self@, req.id@, req.state, req.value@);
                    }
                    let rec = self.objects[i].to_record();
                    PromiseRes { status: 200, promise: Some(rec) }
                } else {
                    let rec = self.objects[i].to_record();
                    proof { lemma_project_legal(now as nat, a, self@, req.id@); }
                    PromiseRes { status: 200, promise: Some(rec) }
                }
            }
        }
    }

    /// `promise.callback`: register `awaiter` to be resumed when `awaited` settles.
    pub fn promise_register_callback(&mut self, req: &PromiseRegisterCallbackReq, now: u64, retry_timeout: u64) -> (r: PromiseRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_register_callback(old(self)@, req@, now as nat).0,
            r@ == spec_promise_register_callback(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 422,
    {
        let ghost a = self@;
        if req.awaited == req.awaiter || !super::types::same_origin(&req.awaited, &req.awaiter) {
            proof { super::properties_proof::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        let i = match self.read_object(&req.awaited, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return PromiseRes { status: 404, promise: None };
            }
            Some(i) => i,
        };
        let ghost a1 = self@;
        let j = match self.read_object(&req.awaiter, now) {
            None => {
                proof { lemma_project_legal(now as nat, a, self@, req.awaited@); }
                return PromiseRes { status: 422, promise: None };
            }
            Some(j) => j,
        };
        proof {
            assert(i != j);
            self.lemma_object_at(i as int);
            self.lemma_object_at(j as int);
            assert(self@.objects[req.awaited@] == a.objects[req.awaited@].project(now as nat));
            assert(self@.objects[req.awaiter@] == a.objects[req.awaiter@].project(now as nat));
            lemma_project_many(now as nat, a, self@, |x: Seq<char>| x == req.awaited@ || x == req.awaiter@);
        }
        if self.objects[j].otype() != OType::Runnable || !self.objects[i].otype().is_awaitable() {
            return PromiseRes { status: 422, promise: None };
        }
        if self.objects[i].state == PromiseState::Pending && self.objects[j].state == PromiseState::Pending {
            let ghost a2 = self@;
            let ghost before = self.objects@;
            self.objects[i].add_callback(&req.awaiter);
            proof {
                let x = req.awaited@;
                let y = req.awaiter@;
                assert(a.objects[x].project(now as nat).state == PromiseState::Pending);
                assert(a.objects[y].project(now as nat).state == PromiseState::Pending);
                assert(a2.objects[x] == a.objects[x]);
                assert(a2.objects[y] == a.objects[y]);
                super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
                assert(self@.objects =~= a.objects.insert(x, a.objects[x].add_callback(y)));
                lemma_add_callback_legal(now as nat, a, self@, x, y);
                assert(a2.objects =~= spec_read(spec_read(a, x, now as nat), y, now as nat).objects);
                assert(self@.objects =~= spec_promise_register_callback(a, req@, now as nat).0.objects);
            }
        }
        let rec = self.objects[i].to_record();
        PromiseRes { status: 200, promise: Some(rec) }
    }

    /// `promise.listener`: register `address` to be told when `awaited` settles.
    pub fn promise_register_listener(&mut self, req: &PromiseRegisterListenerReq, now: u64, retry_timeout: u64) -> (r: PromiseRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_promise_register_listener(old(self)@, req@, now as nat).0,
            r@ == spec_promise_register_listener(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404 || r.status == 422,
    {
        let ghost a = self@;
        let i = match self.read_object(&req.awaited, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return PromiseRes { status: 404, promise: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.awaited@);
        }
        if !self.objects[i].otype().is_awaitable() {
            return PromiseRes { status: 422, promise: None };
        }
        if self.objects[i].state == PromiseState::Pending {
            let ghost before = self.objects@;
            self.objects[i].add_listener(&req.address);
            proof {
                let x = req.awaited@;
                assert(a.objects[x].project(now as nat).state == PromiseState::Pending);
                assert(a.objects[x].project(now as nat) == a.objects[x]);
                super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
                assert(self@.objects =~= a.objects.insert(x, a.objects[x].add_listener(req.address@)));
                lemma_add_listener_legal(now as nat, a, self@, x, req.address@);
            }
        }
        let rec = self.objects[i].to_record();
        PromiseRes { status: 200, promise: Some(rec) }
    }
}

impl State {
    /// `schedule.get`.
    pub fn schedule_get(&mut self, req: &ScheduleGetReq, now: u64, retry_timeout: u64) -> (r: ScheduleRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_schedule_get(old(self)@, req@, now as nat).0,
            r@ == spec_schedule_get(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404,
    {
        proof { super::properties_proof::lemma_noop(now as nat, self@); }
        match self.find_schedule(&req.id) {
            None => ScheduleRes { status: 404, schedule: None },
            Some(i) => {
                proof { self.lemma_schedule_at(i as int); }
                ScheduleRes { status: 200, schedule: Some(self.schedules[i].dup()) }
            }
        }
    }

    /// `schedule.create`. `req.next_run_at` is `nextCron cron now`, from the
    /// caller's cron engine; it must not precede `now`.
    pub fn schedule_create(&mut self, req: &ScheduleCreateReq, now: u64, retry_timeout: u64) -> (r: ScheduleRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_schedule_create(old(self)@, req@, now as nat).0,
            r@ == spec_schedule_create(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400,
    {
        let ghost a = self@;
        if super::tags::exec_timer_targeted(&req.promise_tags) || req.promise_timeout > MAX_TIME || req.next_run_at < now {
            proof { super::properties_proof::lemma_noop(now as nat, a); }
            return ScheduleRes { status: 400, schedule: None };
        }
        match self.find_schedule(&req.id) {
            Some(i) => {
                proof {
                    super::properties_proof::lemma_noop(now as nat, a);
                    self.lemma_schedule_at(i as int);
                }
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
    pub fn schedule_delete(&mut self, req: &ScheduleDeleteReq, now: u64, retry_timeout: u64) -> (r: StatusRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_schedule_delete(old(self)@, req@, now as nat).0,
            r@ == spec_schedule_delete(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404,
    {
        let ghost a = self@;
        match self.find_schedule(&req.id) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                StatusRes { status: 404 }
            }
            Some(i) => {
                proof { self.lemma_schedule_at(i as int); }
                self.remove_schedule(i);
                proof {
                    lemma_schedule_delete_legal(now as nat, a, self@, req.id@);
                    assert(self@ == spec_schedule_delete(a, req@, now as nat).0);
                }
                StatusRes { status: 200 }
            }
        }
    }
}

impl State {
    /// `readTaskObject`: the object, if it has a task; projected at `now`.
    pub fn read_task_object(&mut self, id: &String, now: u64) -> (r: Option<usize>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).schedules == old(self).schedules,
            final(self).outbox == old(self).outbox,
            final(self)@.schedules == old(self)@.schedules,
            final(self)@.outbox == old(self)@.outbox,
            match r {
                None => {
                    &&& *final(self) == *old(self)
                    &&& !old(self)@.has_task(id@)
                },
                Some(i) => {
                    &&& i < final(self).objects@.len()
                    &&& final(self).objects@ == old(self).objects@.update(i as int, final(self).objects@[i as int])
                    &&& old(self).objects@[i as int].id@ == id@
                    &&& final(self).objects@[i as int]@ == old(self).objects@[i as int]@.project(now as nat)
                    &&& final(self).objects@[i as int].id@ == id@
                    &&& old(self)@.objects.contains_key(id@)
                    &&& old(self)@.objects[id@].task is Some
                    &&& final(self).objects@[i as int]@ == old(self)@.objects[id@].project(now as nat)
                    &&& final(self)@.objects == old(self)@.objects.insert(id@, old(self)@.objects[id@].project(now as nat))
                },
            },
    {
        match self.find_object(id) {
            None => None,
            Some(i) => {
                proof { self.lemma_object_at(i as int); }
                if self.objects[i].task.is_none() {
                    return None;
                }
                let ghost before = self.objects@;
                self.objects[i].project(now);
                proof {
                    super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
                }
                Some(i)
            }
        }
    }

    /// `task.get`.
    pub fn task_get(&mut self, req: &TaskGetReq, now: u64, retry_timeout: u64) -> (r: TaskGetRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_get(old(self)@, req@, now as nat).0,
            r@ == spec_task_get(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404,
    {
        let ghost a = self@;
        match self.read_task_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                TaskGetRes { status: 404, task: None }
            }
            Some(i) => {
                proof {
                    lemma_project_legal(now as nat, a, self@, req.id@);
                    assert(self@ == spec_read_task(a, req.id@, now as nat));
                }
                match &self.objects[i].task {
                    None => TaskGetRes { status: 404, task: None },
                    Some(t) => TaskGetRes { status: 200, task: Some(t.to_record(&self.objects[i].id)) },
                }
            }
        }
    }

    /// `task.create`.
    pub fn task_create(&mut self, req: &TaskCreateReq, now: u64, retry_timeout: u64) -> (r: TaskClaimRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_create(old(self)@, req@, now as nat).0,
            r@ == spec_task_create(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 409 || r.status == 422,
    {
        let ghost a = self@;
        let act = &req.action;
        if super::tags::exec_otype(&act.tags) != OType::Runnable || super::tags::exec_timer_targeted(&act.tags)
            || act.timeout_at > MAX_TIME || req.ttl > MAX_TIME {
            proof { super::properties_proof::lemma_noop(now as nat, a); }
            return TaskClaimRes { status: 400, task: None, promise: None };
        }
        match self.read_object(&act.id, now) {
            None => {
                if act.timeout_at > now {
                    let p = create_promise_acquired(act, &req.pid, req.ttl, now);
                    let rec = p.to_record();
                    let trec = match &p.task { Some(t) => Some(t.to_record(&p.id)), None => None };
                    self.push_object(p);
                    proof { lemma_create_acquired_legal(now as nat, a, self@, act@, req.pid@, req.ttl as nat); }
                    TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
                } else {
                    let p = create_promise(act, now);
                    let rec = p.to_record();
                    let trec = match &p.task { Some(t) => Some(t.to_record(&p.id)), None => None };
                    self.push_object(p);
                    proof { lemma_create_legal(now as nat, a, self@, act@); }
                    TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
                }
            }
            Some(i) => {
                proof {
                    self.lemma_object_at(i as int);
                    lemma_project_legal(now as nat, a, self@, act.id@);
                    assert(self@ == spec_read(a, act.id@, now as nat));
                }
                if self.objects[i].otype() != OType::Runnable {
                    return TaskClaimRes { status: 422, task: None, promise: None };
                }
                let (state, version) = match &self.objects[i].task {
                    None => { return TaskClaimRes { status: 409, task: None, promise: None }; }
                    Some(t) => (t.state, t.version),
                };
                if state == TaskState::Fulfilled {
                    let rec = self.objects[i].to_record();
                    let trec = match &self.objects[i].task { Some(t) => Some(t.to_record(&self.objects[i].id)), None => None };
                    return TaskClaimRes { status: 200, task: trec, promise: Some(rec) };
                }
                if state != TaskState::Pending || version >= MAX_VERSION {
                    return TaskClaimRes { status: 409, task: None, promise: None };
                }
                let ghost before = self.objects@;
                self.objects[i].task_acquire(&req.pid, req.ttl, now);
                proof {
                    let x = act.id@;
                    super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
                    lemma_projected_task_identity(now as nat, a, x);
                    assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().acquire(req.pid@, req.ttl as nat, now as nat))));
                    lemma_acquire_legal(now as nat, a, self@, x, req.pid@, req.ttl as nat);
                    assert(self@.objects =~= spec_task_create(a, req@, now as nat).0.objects);
                }
                let rec = self.objects[i].to_record();
                let trec = match &self.objects[i].task { Some(t) => Some(t.to_record(&self.objects[i].id)), None => None };
                TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
            }
        }
    }

    /// `task.acquire`.
    pub fn task_acquire(&mut self, req: &TaskAcquireReq, now: u64, retry_timeout: u64) -> (r: TaskClaimRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_acquire(old(self)@, req@, now as nat).0,
            r@ == spec_task_acquire(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        if req.ttl > MAX_TIME {
            proof { super::properties_proof::lemma_noop(now as nat, a); }
            return TaskClaimRes { status: 400, task: None, promise: None };
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return TaskClaimRes { status: 404, task: None, promise: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return TaskClaimRes { status: 404, task: None, promise: None }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Pending || self.objects[i].state != PromiseState::Pending
            || version != req.version || version >= MAX_VERSION {
            return TaskClaimRes { status: 409, task: None, promise: None };
        }
        let ghost before = self.objects@;
        self.objects[i].task_acquire(&req.pid, req.ttl, now);
        proof {
            let x = req.id@;
            super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().acquire(req.pid@, req.ttl as nat, now as nat))));
            lemma_acquire_legal(now as nat, a, self@, x, req.pid@, req.ttl as nat);
            assert(self@.objects =~= spec_task_acquire(a, req@, now as nat).0.objects);
        }
        let rec = self.objects[i].to_record();
        let trec = match &self.objects[i].task { Some(t) => Some(t.to_record(&self.objects[i].id)), None => None };
        TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
    }

    /// `task.fulfill`.
    pub fn task_fulfill(&mut self, req: &TaskFulfillReq, now: u64, retry_timeout: u64) -> (r: PromiseRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_fulfill(old(self)@, req@, now as nat).0,
            r@ == spec_task_fulfill(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        if !req.action.state.settable() {
            proof { super::properties_proof::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return PromiseRes { status: 404, promise: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return PromiseRes { status: 404, promise: None }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return PromiseRes { status: 409, promise: None };
        }
        let ghost before = self.objects@;
        self.objects[i].settle(req.action.state, req.action.value.dup(), now);
        proof {
            let x = req.id@;
            super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].project(now as nat).settle(req.action.state, req.action.value@, now as nat)));
            lemma_settle_legal(now as nat, a, self@, x, req.action.state, req.action.value@);
            assert(self@.objects =~= spec_task_fulfill(a, req@, now as nat).0.objects);
        }
        let rec = self.objects[i].to_record();
        PromiseRes { status: 200, promise: Some(rec) }
    }

    /// `task.release`.
    pub fn task_release(&mut self, req: &TaskReleaseReq, now: u64, retry_timeout: u64) -> (r: StatusRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_release(old(self)@, req@, now as nat).0,
            r@ == spec_task_release(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return StatusRes { status: 409 };
        }
        let ghost before = self.objects@;
        self.objects[i].task_release(now);
        proof {
            let x = req.id@;
            super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().release(now as nat))));
            lemma_release_legal(now as nat, a, self@, x, now as nat);
            assert(self@.objects =~= spec_task_release(a, req@, now as nat).0.objects);
        }
        StatusRes { status: 200 }
    }

    /// `task.halt`.
    pub fn task_halt(&mut self, req: &TaskHaltReq, now: u64, retry_timeout: u64) -> (r: StatusRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_halt(old(self)@, req@, now as nat).0,
            r@ == spec_task_halt(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let state = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => t.state,
        };
        if state == TaskState::Fulfilled {
            return StatusRes { status: 409 };
        }
        if state == TaskState::Halted {
            return StatusRes { status: 200 };
        }
        let ghost before = self.objects@;
        self.objects[i].task_halt();
        proof {
            let x = req.id@;
            super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().halt())));
            lemma_halt_legal(now as nat, a, self@, x);
            assert(self@.objects =~= spec_task_halt(a, req@, now as nat).0.objects);
        }
        StatusRes { status: 200 }
    }

    /// `task.continue`.
    pub fn task_continue(&mut self, req: &TaskContinueReq, now: u64, retry_timeout: u64) -> (r: StatusRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_continue(old(self)@, req@, now as nat).0,
            r@ == spec_task_continue(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let state = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => t.state,
        };
        if state != TaskState::Halted || self.objects[i].state != PromiseState::Pending {
            return StatusRes { status: 409 };
        }
        let ghost before = self.objects@;
        self.objects[i].task_continue(now);
        proof {
            let x = req.id@;
            super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().continue_(now as nat))));
            lemma_continue_legal(now as nat, a, self@, x);
            assert(self@.objects =~= spec_task_continue(a, req@, now as nat).0.objects);
        }
        StatusRes { status: 200 }
    }
}

impl State {
    /// `task.fence`.
    pub fn task_fence(&mut self, req: &TaskFenceReq, now: u64, retry_timeout: u64) -> (r: TaskFenceRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_fence(old(self)@, req@, now as nat).0,
            r@ == spec_task_fence(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let target: &String = match &req.action {
            TaskFenceAction::Create(c) => &c.id,
            TaskFenceAction::Settle(c) => &c.id,
        };
        if *target == req.id || !super::types::same_origin(target, &req.id) {
            proof { super::properties_proof::lemma_noop(now as nat, a); }
            return TaskFenceRes { status: 400, action: None };
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return TaskFenceRes { status: 404, action: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return TaskFenceRes { status: 404, action: None }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return TaskFenceRes { status: 409, action: None };
        }
        let ghost a1 = self@;
        let inner = match &req.action {
            TaskFenceAction::Create(c) => TaskFenceInnerRes::Create(self.promise_create(c, now, retry_timeout)),
            TaskFenceAction::Settle(c) => TaskFenceInnerRes::Settle(self.promise_settle(c, now, retry_timeout)),
        };
        proof { lemma_fence_legal(now as nat, a, a1, self@, req.id@, target@); }
        TaskFenceRes { status: 200, action: Some(inner) }
    }

    /// `task.fence` with no action: the check alone, for a fence whose create
    /// ran first on another origin's document.
    pub fn task_fence_check(&mut self, req: &TaskFenceCheckReq, now: u64, retry_timeout: u64) -> (r: StatusRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_fence_check(old(self)@, req@, now as nat).0,
            r@ == spec_task_fence_check(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
            assert(self@ == spec_read_task(a, req.id@, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return StatusRes { status: 409 };
        }
        StatusRes { status: 200 }
    }

    /// `task.heartbeat`.
    pub fn task_heartbeat(&mut self, req: &TaskHeartbeatReq, now: u64, retry_timeout: u64) -> (r: StatusRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_heartbeat(old(self)@, req@, now as nat).0,
            r@ == spec_task_heartbeat(old(self)@, req@, now as nat).1,
            r.status == 200,
    {
        let ghost a = self@;
        let ghost pid = req.pid@;
        let ghost refs: Seq<ATaskRef> = req.tasks.deep_view();
        let mut k: usize = 0;
        while k < req.tasks.len()
            invariant
                a == old(self)@,
                k <= refs.len(),
                refs == req.tasks.deep_view(),
                pid == req.pid@,
                now <= MAX_TIME,
                inv(now as nat, a),
                self.wf(),
                self@ == spec_heartbeat_fold(a, pid, refs, k as int, now as nat),
            decreases refs.len() - k,
        {
            let ghost s0 = self@;
            let ghost r = refs[k as int];
            proof {
                lemma_spec_heartbeat_fold_inv(now as nat, a, pid, refs, k as int);
                assert(r == req.tasks@[k as int]@);
            }
            let x = &req.tasks[k].id;
            match self.read_task_object(x, now) {
                None => {
                    proof { assert(self@ == spec_heartbeat_one(s0, pid, r, now as nat)); }
                }
                Some(i) => {
                    proof {
                        self.lemma_object_at(i as int);
                        lemma_project_legal(now as nat, s0, self@, x@);
                        assert(self@ == spec_read_task(s0, x@, now as nat));
                    }
                    let ok = match &self.objects[i].task {
                        Some(t) => t.state == TaskState::Acquired && t.version == req.tasks[k].version
                            && (match &t.pid { Some(p) => *p == req.pid, None => false })
                            && self.objects[i].state == PromiseState::Pending,
                        None => false,
                    };
                    if ok {
                        let ghost s1 = self@;
                        let ghost before = self.objects@;
                        proof {
                            lemma_projected_task_identity(now as nat, s0, x@);
                            lemma_inv_pointwise(now as nat, s1);
                            assert(inv_obj(now as nat, s1, x@));
                        }
                        self.objects[i].task_heartbeat(now);
                        proof {
                            super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
                            assert(self@.objects =~= s1.objects.insert(x@, s1.objects[x@].with_task(s1.objects[x@].task.unwrap().heartbeat(now as nat))));
                            assert(self@ == spec_heartbeat_one(s0, pid, r, now as nat));
                        }
                    } else {
                        proof { assert(self@ == spec_heartbeat_one(s0, pid, r, now as nat)); }
                    }
                }
            }
            proof { assert(self@ == spec_heartbeat_fold(a, pid, refs, k as int + 1, now as nat)); }
            k += 1;
        }
        proof { lemma_spec_task_heartbeat(now as nat, a, req@); }
        StatusRes { status: 200 }
    }

    /// `task.suspend`.
    pub fn task_suspend(&mut self, req: &TaskSuspendReq, now: u64, retry_timeout: u64) -> (r: StatusRes)
        requires
            pre(*old(self), now, retry_timeout),
        ensures
            post(*old(self), *final(self), now),
            final(self)@ == spec_task_suspend(old(self)@, req@, now as nat).0,
            r@ == spec_task_suspend(old(self)@, req@, now as nat).1,
            r.status == 200 || r.status == 300 || r.status == 400 || r.status == 404 || r.status == 409 || r.status == 422,
    {
        let ghost a = self@;
        let ghost acts: Seq<APromiseRegisterCallbackReq> = req.actions.deep_view();
        let ghost id = req.id@;
        let n = req.actions.len();
        proof {
            assert(acts == req@.actions);
            assert forall|j: int| 0 <= j < acts.len() implies #[trigger] acts[j].awaited == req.actions@[j].awaited@ by {}
        }
        let crosses = awaits_self_or_crosses(&req.actions, &req.id);
        let twice = awaits_twice(&req.actions);
        if n == 0 || crosses || twice {
            proof {
                super::properties_proof::lemma_noop(now as nat, a);
                assert(!suspend_doors(acts, id));
            }
            return StatusRes { status: 400 };
        }
        proof { assert(suspend_doors(acts, id)); }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { super::properties_proof::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, id);
            assert(self@ == spec_read_task(a, id, now as nat));
        }
        let (state, version) = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return StatusRes { status: 409 };
        }
        // the state the check loop reads from: the task object, projected, which was the identity
        let ghost rb = self@;
        let ghost t0 = rb.objects[id].task.unwrap();
        proof {
            lemma_projected_task_identity(now as nat, a, id);
            assert(suspend_base(now as nat, a, id));
            assert(self.objects@[i as int]@ == a.objects[id]);
            assert(rb.objects =~= a.objects);
            assert(rb == a);
            assert(spec_read_task(a, id, now as nat) == a);
            assert(t0.version == req.version);
            assert forall|x: Seq<char>| !awaited_touched(acts, 0, x) implies #[trigger] unchanged_at(a, self@, x) by {}
            assert forall|j: int| 0 <= j < n implies rb.objects.contains_key(#[trigger] acts[j].awaited) == a.objects.contains_key(acts[j].awaited)
                && (a.objects.contains_key(acts[j].awaited) ==> rb.objects[acts[j].awaited] == a.objects[acts[j].awaited]) by {}
        }
        // checkAwaited
        let mut settled = false;
        let mut k: usize = 0;
        while k < n
            invariant
                a == old(self)@,
                k <= n,
                n == acts.len(),
                acts == req.actions.deep_view(),
                forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == req.actions@[j].awaited@,
                id == req.id@,
                now <= MAX_TIME,
                suspend_base(now as nat, a, id),
                suspend_doors(acts, id),
                rb == a,
                spec_read_task(a, id, now as nat) == a,
                t0 == a.objects[id].task.unwrap(),
                t0.version == req.version,
                self.wf(),
                inv(now as nat, self@),
                self@.schedules == a.schedules,
                self@.outbox == a.outbox,
                i < self.objects@.len(),
                self.objects@[i as int].id@ == id,
                self.objects@[i as int]@ == a.objects[id],
                self@ == spec_awaited_read(rb, acts, k as int, now as nat),
                first_failing(rb, acts, k as int) is None,
                forall|x: Seq<char>| !awaited_touched(acts, k as int, x) ==> #[trigger] unchanged_at(a, self@, x),
                forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int, x) ==>
                    a.objects.contains_key(x)
                    && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x].project(now as nat),
                forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int, x) ==> a.objects[x].otype().awaitable(),
                settled == exists|j: int| 0 <= j < k && a.objects[#[trigger] acts[j].awaited].project(now as nat).state != PromiseState::Pending,
            decreases n - k,
        {
            let ghost s0 = self@;
            let w = &req.actions[k].awaited;
            proof {
                assert(acts[k as int].awaited == w@);
                assert(w@ != id);
            }
            let j = match self.read_object(w, now) {
                None => {
                    proof {
                        let ids = |x: Seq<char>| awaited_touched(acts, k as int, x);
                        assert forall|x: Seq<char>| #[trigger] ids(x) implies
                            a.objects.contains_key(x) && self@.objects.contains_key(x)
                            && self@.objects[x] == a.objects[x].project(now as nat) by {
                            assert(awaited_touched(acts, k as int, x));
                        }
                        assert forall|x: Seq<char>| !ids(x) implies
                            (a.objects.contains_key(x) <==> #[trigger] self@.objects.contains_key(x))
                            && (a.objects.contains_key(x) ==> a.objects[x] == self@.objects[x]) by {
                            assert(!awaited_touched(acts, k as int, x));
                            assert(unchanged_at(a, self@, x));
                        }
                        lemma_project_many(now as nat, a, self@, ids);
                        // the check failed here: nothing at `w`
                        if awaited_touched(acts, k as int, w@) {
                            assert(s0.objects.contains_key(w@));
                            assert(false);
                        }
                        assert(unchanged_at(a, s0, w@));
                        assert(!rb.objects.contains_key(w@));
                        assert(awaited_fails(rb, acts[k as int]));
                        lemma_first_failing_at(rb, acts, k as int, n as int);
                        assert(self@ == spec_task_suspend(a, req@, now as nat).0);
                    }
                    return StatusRes { status: 422 };
                }
                Some(j) => j,
            };
            proof {
                self.lemma_object_at(j as int);
                lemma_project_legal(now as nat, s0, self@, w@);
                assert(j != i);
                // the shape after this read, relative to `a`
                if awaited_touched(acts, k as int, w@) {
                    lemma_project_idem(a.objects[w@], now as nat);
                } else {
                    assert(unchanged_at(a, s0, w@));
                }
                assert(self@.objects[w@] == a.objects[w@].project(now as nat));
                assert(a.objects.contains_key(w@));
                assert(self@ == spec_awaited_read(rb, acts, k as int + 1, now as nat));
                assert forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int + 1, x) implies
                    a.objects.contains_key(x)
                    && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x].project(now as nat) by {
                    if x == w@ {
                    } else {
                        let jj = choose|jj: int| 0 <= jj < k as int + 1 && #[trigger] acts[jj].awaited == x;
                        assert(jj < k as int);
                        assert(awaited_touched(acts, k as int, x));
                    }
                }
                assert forall|x: Seq<char>| !awaited_touched(acts, k as int + 1, x) implies #[trigger] unchanged_at(a, self@, x) by {
                    assert(!awaited_touched(acts, k as int, x));
                    assert(acts[k as int].awaited != x);
                    assert(unchanged_at(a, s0, x));
                }
            }
            if !self.objects[j].otype().is_awaitable() {
                proof {
                    // The lemma's preconditions, stated on the closure it is
                    // handed, so the match does not rest on trigger luck.
                    let ids = |x: Seq<char>| awaited_touched(acts, k as int + 1, x);
                    assert forall|x: Seq<char>| #[trigger] ids(x) implies
                        a.objects.contains_key(x) && self@.objects.contains_key(x)
                        && self@.objects[x] == a.objects[x].project(now as nat) by {
                        assert(awaited_touched(acts, k as int + 1, x));
                    }
                    assert forall|x: Seq<char>| !ids(x) implies
                        (a.objects.contains_key(x) <==> #[trigger] self@.objects.contains_key(x))
                        && (a.objects.contains_key(x) ==> a.objects[x] == self@.objects[x]) by {
                        assert(!awaited_touched(acts, k as int + 1, x));
                        assert(unchanged_at(a, self@, x));
                    }
                    lemma_project_many(now as nat, a, self@, ids);
                    // the check failed here: not awaitable
                    assert(a.objects[w@].otype() == self@.objects[w@].otype());
                    assert(awaited_fails(rb, acts[k as int]));
                    lemma_first_failing_at(rb, acts, k as int, n as int);
                    assert(self@ == spec_task_suspend(a, req@, now as nat).0);
                }
                return StatusRes { status: 422 };
            }
            proof {
                assert(a.objects[w@].otype() == self@.objects[w@].otype());
                assert(!awaited_fails(rb, acts[k as int]));
                assert(first_failing(rb, acts, k as int + 1) is None);
                assert forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int + 1, x) implies a.objects[x].otype().awaitable() by {
                    if x != w@ {
                        let jj = choose|jj: int| 0 <= jj < k as int + 1 && #[trigger] acts[jj].awaited == x;
                        assert(jj < k as int);
                        assert(awaited_touched(acts, k as int, x));
                    }
                }
            }
            if self.objects[j].state != PromiseState::Pending {
                settled = true;
            }
            proof {
                assert(a.objects[acts[k as int].awaited].project(now as nat).state == self@.objects[w@].state);
            }
            k += 1;
        }
        proof {
            assert(settled == any_settled(rb, acts, now as nat));
        }
        if settled {
            let ghost s_prev = self@;
            let ghost before = self.objects@;
            proof { self.lemma_object_at(i as int); }
            self.objects[i].task_clear_resumes();
            proof {
                super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
                let ghost b = self@;
                assert(b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().clear_resumes()));
                assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
                    a.objects.contains_key(x) && x != id
                    && b.objects.contains_key(x) && b.objects[x] == a.objects[x].project(now as nat) by {
                    assert(awaited_touched(acts, n as int, x));
                    let jj = choose|jj: int| 0 <= jj < n && #[trigger] acts[jj].awaited == x;
                    assert(s_prev.objects.contains_key(x) && s_prev.objects[x] == a.objects[x].project(now as nat));
                }
                assert forall|x: Seq<char>| !awaited_of(acts, x) && x != id implies #[trigger] unchanged_at(a, b, x) by {
                    assert(!awaited_touched(acts, n as int, x));
                    assert(unchanged_at(a, s_prev, x));
                    assert(b.objects.contains_key(x) == s_prev.objects.contains_key(x));
                }
                lemma_suspend_300_legal(now as nat, a, b, id, acts);
                assert(s_prev.objects[id] == a.objects[id]);
                assert(b.objects =~= s_prev.objects.insert(id, s_prev.objects[id].with_task(t0.clear_resumes())));
                assert(b == spec_task_suspend(a, req@, now as nat).0);
            }
            return StatusRes { status: 300 };
        }
        // registerAwaited: every awaited promise is pending, so its projection was the identity
        let ghost c = self@;
        proof {
            assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
                a.objects.contains_key(x) && a.objects[x].otype().awaitable()
                && a.objects[x].state == PromiseState::Pending && a.objects[x].timeout_at > now
                && x != id && super::types::same_origin_spec(x, id)
                && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x] by {
                assert(awaited_touched(acts, n as int, x));
                let jj = choose|jj: int| 0 <= jj < n && #[trigger] acts[jj].awaited == x;
                assert(a.objects[acts[jj].awaited].project(now as nat).state == PromiseState::Pending);
            }
            assert forall|j: int| 0 <= j < n implies self@.objects.contains_key(#[trigger] acts[j].awaited)
                && self@.objects[acts[j].awaited] == a.objects[acts[j].awaited] by {
                assert(awaited_touched(acts, n as int, acts[j].awaited));
                assert(awaited_of(acts, acts[j].awaited));
            }
            assert forall|x: Seq<char>| !awaited_of(acts, x) implies #[trigger] unchanged_at(a, self@, x) by {
                assert(!awaited_touched(acts, n as int, x));
            }
        }
        k = 0;
        while k < n
            invariant
                a == old(self)@,
                k <= n,
                n == acts.len(),
                acts == req.actions.deep_view(),
                forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == req.actions@[j].awaited@,
                id == req.id@,
                now <= MAX_TIME,
                suspend_base(now as nat, a, id),
                suspend_doors(acts, id),
                rb == a,
                spec_read_task(a, id, now as nat) == a,
                t0 == a.objects[id].task.unwrap(),
                t0.version == req.version,
                c == spec_awaited_read(rb, acts, n as int, now as nat),
                first_failing(rb, acts, n as int) is None,
                !any_settled(rb, acts, now as nat),
                self.wf(),
                inv(now as nat, self@),
                self@.schedules == a.schedules,
                self@.outbox == a.outbox,
                i < self.objects@.len(),
                self.objects@[i as int].id@ == id,
                self.objects@[i as int]@ == a.objects[id],
                self@ == spec_awaited_register(c, acts, k as int, id),
                forall|x: Seq<char>| !awaited_of(acts, x) ==> #[trigger] unchanged_at(a, self@, x),
                forall|x: Seq<char>| #[trigger] awaited_of(acts, x) ==>
                    a.objects.contains_key(x) && a.objects[x].otype().awaitable()
                    && a.objects[x].state == PromiseState::Pending && a.objects[x].timeout_at > now
                    && x != id && super::types::same_origin_spec(x, id),
                forall|j: int| 0 <= j < k ==> self@.objects.contains_key(#[trigger] acts[j].awaited)
                    && self@.objects[acts[j].awaited] == a.objects[acts[j].awaited].add_callback(id),
                forall|j: int| k <= j < n ==> self@.objects.contains_key(#[trigger] acts[j].awaited)
                    && self@.objects[acts[j].awaited] == a.objects[acts[j].awaited],
            decreases n - k,
        {
            let ghost s0 = self@;
            let w = &req.actions[k].awaited;
            proof {
                assert(acts[k as int].awaited == w@);
                assert(awaited_of(acts, w@));
                assert(s0.objects.contains_key(w@));
            }
            let j = match self.find_object(w) {
                None => {
                    proof { assert(false); }
                    return StatusRes { status: 422 };
                }
                Some(j) => j,
            };
            proof {
                self.lemma_object_at(j as int);
                assert(j != i);
                assert(s0.objects[w@] == a.objects[w@]);
                assert(unchanged_at(a, s0, id));
                assert(s0.objects[id] == a.objects[id]);
            }
            let ghost before = self.objects@;
            self.objects[j].add_callback(&req.id);
            proof {
                super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), j as int, self.objects@[j as int]);
                assert(self@.objects =~= s0.objects.insert(w@, s0.objects[w@].add_callback(id)));
                assert(self@ == spec_awaited_register(c, acts, k as int + 1, id));
                assert(a.objects[w@].project(now as nat) == a.objects[w@]);
                assert(a.objects[id].project(now as nat) == a.objects[id]);
                lemma_inv_pointwise(now as nat, s0);
                assert(inv_obj(now as nat, s0, id));
                assert(s0.objects[id].otype() == OType::Runnable);
                lemma_add_callback_legal(now as nat, s0, self@, w@, id);
                let ghost b = self@;
                assert forall|jj: int| 0 <= jj < k as int + 1 implies b.objects.contains_key(#[trigger] acts[jj].awaited)
                    && b.objects[acts[jj].awaited] == a.objects[acts[jj].awaited].add_callback(id) by {
                    if jj < k as int {
                        assert(acts[jj].awaited != w@);
                    }
                }
                assert forall|jj: int| k as int + 1 <= jj < n implies b.objects.contains_key(#[trigger] acts[jj].awaited)
                    && b.objects[acts[jj].awaited] == a.objects[acts[jj].awaited] by {
                    assert(acts[jj].awaited != w@);
                }
                assert forall|x: Seq<char>| !awaited_of(acts, x) implies #[trigger] unchanged_at(a, b, x) by {
                    assert(unchanged_at(a, s0, x));
                    assert(x != w@);
                }
            }
            k += 1;
        }
        let ghost s_prev = self@;
        let ghost before = self.objects@;
        proof { self.lemma_object_at(i as int); }
        self.objects[i].task_suspend();
        proof {
            super::store_proof::lemma_fold_update(before, super::store::obj_key(), super::store::obj_val(), i as int, self.objects@[i as int]);
            let ghost b = self@;
            assert(b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().suspend()));
            assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
                b.objects.contains_key(x) && b.objects[x] == a.objects[x].add_callback(id) by {
                assert(awaited_touched(acts, n as int, x));
                let jj = choose|jj: int| 0 <= jj < n && #[trigger] acts[jj].awaited == x;
                assert(s_prev.objects.contains_key(x) && s_prev.objects[x] == a.objects[x].add_callback(id));
            }
            assert forall|x: Seq<char>| !awaited_of(acts, x) && x != id implies #[trigger] unchanged_at(a, b, x) by {
                assert(unchanged_at(a, s_prev, x));
                assert(b.objects.contains_key(x) == s_prev.objects.contains_key(x));
            }
            lemma_suspend_legal(now as nat, a, b, id, acts);
            assert(s_prev.objects[id] == a.objects[id]);
            assert(b.objects =~= s_prev.objects.insert(id, s_prev.objects[id].with_task(t0.suspend())));
            assert(b == spec_task_suspend(a, req@, now as nat).0);
        }
        StatusRes { status: 200 }
    }
}

// ---------------------------------------------------------------------------
// Door checks
// ---------------------------------------------------------------------------

/// Does any action await the task itself, or a promise of another origin?
pub fn awaits_self_or_crosses(actions: &Vec<PromiseRegisterCallbackReq>, id: &String) -> (r: bool)
    ensures
        r == exists|j: int| 0 <= j < actions.deep_view().len()
            && (#[trigger] actions.deep_view()[j].awaited == id@ || !super::types::same_origin_spec(actions.deep_view()[j].awaited, id@)),
{
    let ghost acts: Seq<APromiseRegisterCallbackReq> = actions.deep_view();
    proof {
        assert forall|j: int| 0 <= j < acts.len() implies #[trigger] acts[j].awaited == actions@[j].awaited@ by {}
    }
    let mut k: usize = 0;
    while k < actions.len()
        invariant
            acts == actions.deep_view(),
            forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == actions@[j].awaited@,
            k <= acts.len(),
            forall|j: int| 0 <= j < k ==>
                #[trigger] acts[j].awaited != id@ && super::types::same_origin_spec(acts[j].awaited, id@),
        decreases acts.len() - k,
    {
        if actions[k].awaited == *id || !super::types::same_origin(&actions[k].awaited, id) {
            proof { assert(acts[k as int].awaited == actions@[k as int].awaited@); }
            return true;
        }
        k += 1;
    }
    false
}

/// Does any promise appear twice?
pub fn awaits_twice(actions: &Vec<PromiseRegisterCallbackReq>) -> (r: bool)
    ensures r == !awaited_distinct(actions.deep_view()),
{
    let ghost acts: Seq<APromiseRegisterCallbackReq> = actions.deep_view();
    proof {
        assert forall|j: int| 0 <= j < acts.len() implies #[trigger] acts[j].awaited == actions@[j].awaited@ by {}
    }
    let mut k: usize = 0;
    while k < actions.len()
        invariant
            acts == actions.deep_view(),
            forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == actions@[j].awaited@,
            k <= acts.len(),
            forall|i: int, j: int| 0 <= i < k && 0 <= j < acts.len()
                && #[trigger] acts[i].awaited == #[trigger] acts[j].awaited ==> i == j,
        decreases acts.len() - k,
    {
        let mut m: usize = 0;
        while m < actions.len()
            invariant
                acts == actions.deep_view(),
                forall|j: int| 0 <= j < acts.len() ==> #[trigger] acts[j].awaited == actions@[j].awaited@,
                k < acts.len(),
                m <= acts.len(),
                forall|i: int, j: int| 0 <= i < k && 0 <= j < acts.len()
                    && #[trigger] acts[i].awaited == #[trigger] acts[j].awaited ==> i == j,
                forall|j: int| 0 <= j < m && j != k ==> #[trigger] acts[j].awaited != acts[k as int].awaited,
            decreases acts.len() - m,
        {
            if m != k && actions[m].awaited == actions[k].awaited {
                proof {
                    assert(acts[m as int].awaited == acts[k as int].awaited);
                    assert(!awaited_distinct(acts));
                }
                return true;
            }
            m += 1;
        }
        k += 1;
    }
    false
}

} // verus!
