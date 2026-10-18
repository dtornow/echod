//! External steps: the task handlers that touch one object.
//!
//! `task.get`, `task.create`, `task.acquire`, `task.fulfill`, `task.release`,
//! `task.halt`, `task.continue`. The ones that touch several objects —
//! `task.fence`, `task.heartbeat`, `task.suspend` — are in `external_task2`.

use vstd::prelude::*;

use crate::external::*;
use crate::object::*;
use crate::properties::*;
use crate::store::{AState, State};
use crate::tags::OType;
use crate::types::*;

verus! {

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
                    crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                }
                Some(i)
            }
        }
    }

    /// `task.get`.
    pub fn task_get(&mut self, req: &TaskGetReq, now: u64, cfg: &Config) -> (r: TaskGetRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 404,
    {
        let ghost a = self@;
        match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                TaskGetRes { status: 404, task: None }
            }
            Some(i) => {
                proof { lemma_project_legal(now as nat, a, self@, req.id@); }
                match &self.objects[i].task {
                    None => TaskGetRes { status: 404, task: None },
                    Some(t) => TaskGetRes { status: 200, task: Some(t.to_record(&self.objects[i].id)) },
                }
            }
        }
    }

    /// `task.create`.
    pub fn task_create(&mut self, req: &TaskCreateReq, now: u64, cfg: &Config) -> (r: TaskClaimRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 400 || r.status == 409 || r.status == 422,
    {
        let ghost a = self@;
        let act = &req.action;
        if crate::tags::exec_otype(&act.tags) != OType::Runnable || crate::tags::exec_timer_targeted(&act.tags)
            || act.timeout_at > MAX_TIME || req.ttl > MAX_TIME {
            proof { crate::frame::lemma_noop(now as nat, a); }
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
                if state != TaskState::Pending || version >= MAX_TIME {
                    return TaskClaimRes { status: 409, task: None, promise: None };
                }
                let ghost before = self.objects@;
                self.objects[i].task_acquire(&req.pid, req.ttl, now);
                proof {
                    let x = act.id@;
                    crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                    lemma_projected_task_identity(now as nat, a, x);
                    assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().acquire(req.pid@, req.ttl as nat, now as nat))));
                    lemma_acquire_legal(now as nat, a, self@, x, req.pid@, req.ttl as nat);
                }
                let rec = self.objects[i].to_record();
                let trec = match &self.objects[i].task { Some(t) => Some(t.to_record(&self.objects[i].id)), None => None };
                TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
            }
        }
    }

    /// `task.acquire`.
    pub fn task_acquire(&mut self, req: &TaskAcquireReq, now: u64, cfg: &Config) -> (r: TaskClaimRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        if req.ttl > MAX_TIME {
            proof { crate::frame::lemma_noop(now as nat, a); }
            return TaskClaimRes { status: 400, task: None, promise: None };
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                return TaskClaimRes { status: 404, task: None, promise: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
        }
        let (state, version) = match &self.objects[i].task {
            None => { return TaskClaimRes { status: 404, task: None, promise: None }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Pending || self.objects[i].state != PromiseState::Pending
            || version != req.version || version >= MAX_TIME {
            return TaskClaimRes { status: 409, task: None, promise: None };
        }
        let ghost before = self.objects@;
        self.objects[i].task_acquire(&req.pid, req.ttl, now);
        proof {
            let x = req.id@;
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().acquire(req.pid@, req.ttl as nat, now as nat))));
            lemma_acquire_legal(now as nat, a, self@, x, req.pid@, req.ttl as nat);
        }
        let rec = self.objects[i].to_record();
        let trec = match &self.objects[i].task { Some(t) => Some(t.to_record(&self.objects[i].id)), None => None };
        TaskClaimRes { status: 200, task: trec, promise: Some(rec) }
    }

    /// `task.fulfill`.
    pub fn task_fulfill(&mut self, req: &TaskFulfillReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        if !req.action.state.settable() {
            proof { crate::frame::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                return PromiseRes { status: 404, promise: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
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
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].project(now as nat).settle(req.action.state, req.action.value@, now as nat)));
            lemma_settle_legal(now as nat, a, self@, x, req.action.state, req.action.value@);
        }
        let rec = self.objects[i].to_record();
        PromiseRes { status: 200, promise: Some(rec) }
    }

    /// `task.release`.
    pub fn task_release(&mut self, req: &TaskReleaseReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
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
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().release(now as nat))));
            lemma_release_legal(now as nat, a, self@, x);
        }
        StatusRes { status: 200 }
    }

    /// `task.halt`.
    pub fn task_halt(&mut self, req: &TaskHaltReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
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
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().halt())));
            lemma_halt_legal(now as nat, a, self@, x);
        }
        StatusRes { status: 200 }
    }

    /// `task.continue`.
    pub fn task_continue(&mut self, req: &TaskContinueReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
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
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            lemma_projected_task_identity(now as nat, a, x);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().continue_(now as nat))));
            lemma_continue_legal(now as nat, a, self@, x);
        }
        StatusRes { status: 200 }
    }
}

// ---------------------------------------------------------------------------
// Proofs
// ---------------------------------------------------------------------------

/// A projected object whose task is not fulfilled is the object itself: its
/// promise is pending and ahead of its deadline.
pub proof fn lemma_projected_task_identity(now: nat, a: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].project(now).task.unwrap().state != TaskState::Fulfilled,
    ensures
        a.objects[id].project(now) == a.objects[id],
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        a.objects[id].project(now).task.unwrap() == a.objects[id].task.unwrap(),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    if p.state != PromiseState::Pending {
        assert(consistent_settled_promise_has_fulfilled_task_at(now, p));
        assert(false);
    }
    if p.timeout_at <= now {
        assert(false);
    }
}

/// The common part of every single-task-edit step: the object keeps its
/// callbacks, listeners, tags and promise, so the pointers into and out of it
/// are what they were.
proof fn lemma_task_edit_frame(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        b.objects[id].callbacks == a.objects[id].callbacks,
        b.objects[id].listeners == a.objects[id].listeners,
        b.objects[id].tags == a.objects[id].tags,
        forall|z: Seq<char>| z != id ==>
            (a.objects.contains_key(z) <==> #[trigger] b.objects.contains_key(z))
            && (a.objects.contains_key(z) ==> a.objects[z] == b.objects[z]),
    ensures
        forall|i: int| 0 <= i < a.objects[id].callbacks.len() ==>
            b.objects[id].callbacks.contains(#[trigger] a.objects[id].callbacks[i]),
        forall|i: int| 0 <= i < a.objects[id].listeners.len() ==>
            b.objects[id].listeners.contains(#[trigger] a.objects[id].listeners[i]),
        consistent_callback_awaiter_is_targeted_at(now, b, b.objects[id]),
        forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
            && #[trigger] a.objects[w].callbacks.contains(z)
            ==> b.objects.contains_key(w) && b.objects[w].callbacks.contains(z),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let q = b.objects[id];
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        if p.callbacks[i] != id {
            assert(b.objects.contains_key(p.callbacks[i]));
        }
    }
}

/// `task.create` on a fresh id ahead of its deadline.
pub proof fn lemma_create_acquired_legal(now: nat, a: AState, b: AState, req: APromiseCreateReq, pid: Seq<char>, ttl: nat)
    requires
        inv(now, a),
        !a.objects.contains_key(req.id),
        crate::tags::otype(req.tags) == OType::Runnable,
        !crate::tags::timer_targeted(req.tags),
        req.timeout_at > now,
        req.timeout_at <= MAX_TIME as nat,
        ttl <= MAX_TIME as nat,
        b.objects == a.objects.insert(req.id, spec_create_acquired(req, pid, ttl, now)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    let id = req.id;
    let q = spec_create_acquired(req, pid, ttl, now);
    assert(b.objects[id] == q);
    assert(q.callbacks.len() == 0);
    assert(!q.callbacks.contains(id));
    assert(q.project_promise(now) == q);
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, set![id], Set::empty(), Set::empty(), Set::empty());
}

/// `task.acquire`, and `task.create` on an existing pending task.
pub proof fn lemma_acquire_legal(now: nat, a: AState, b: AState, id: Seq<char>, pid: Seq<char>, ttl: nat)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Pending,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        a.objects[id].task.unwrap().version < MAX_TIME as nat,
        ttl <= MAX_TIME as nat,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().acquire(pid, ttl, now))),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.acquire(pid, ttl, now);
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert(u.resumes.len() == 0);
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    crate::frame::lemma_step(now, a, b, set![id], Set::empty(), Set::empty(), Set::empty());
}

/// `task.release`, and the lease timeout.
pub proof fn lemma_release_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Acquired,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().release(now))),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.release(now);
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    crate::frame::lemma_step(now, a, b, set![id], Set::empty(), Set::empty(), Set::empty());
}

/// `task.halt` on a task that is neither fulfilled nor halted.
pub proof fn lemma_halt_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state != TaskState::Fulfilled,
        a.objects[id].task.unwrap().state != TaskState::Halted,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().halt())),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.halt();
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    crate::frame::lemma_step(now, a, b, set![id], Set::empty(), Set::empty(), Set::empty());
}

/// `task.continue` on a halted task.
pub proof fn lemma_continue_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Halted,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().continue_(now))),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.continue_(now);
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    crate::frame::lemma_step(now, a, b, set![id], Set::empty(), Set::empty(), Set::empty());
}

} // verus!
