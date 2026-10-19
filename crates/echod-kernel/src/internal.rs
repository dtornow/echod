//! Internal steps: what the server does on its own initiative.
//!
//! `spec/02-abstract/internal.lean`: the promise timeout, the callback drain,
//! the listener drain, the lease timeout, the retry dispatch, and the
//! schedule. Each ensures the catalogue and, being a sweeper, the two
//! sweeper entries of `internal_legal`.
//!
//! Two places this kernel departs from the Lean text, each because the text
//! would break a catalogue entry:
//!
//! - `processSchedule` creates a promise "as of" its occurrence `t`. When
//!   `t + promiseTimeout <= now` that is a pending task on a promise already
//!   dead at `now`, which `preserved_no_dead_dispatch` forbids. The kernel
//!   births such a promise dead instead — the state Lean would reach on the
//!   next touch — and materialises an existing object at `now`, not `t`.
//! - `processLeaseTimeout` and `processRetryTimeout` read without
//!   materialising (`viewTaskObject`). The kernel does the same: it tests
//!   the stored object for the conditions the projected one would satisfy.

use vstd::prelude::*;

use crate::external::*;
use crate::external_proof::*;
use crate::object::*;
use crate::properties::*;
use crate::store::{AState, State};
use crate::tags::OType;
use crate::types::*;

verus! {

/// What every internal step ensures: the catalogue, and the sweeper entries.
pub open spec fn ipost(a: State, b: State, now: u64) -> bool {
    &&& post(a, b, now)
    &&& internal_legal(now as nat, a@, b@)
}

/// An occurrence of a schedule, as the kernel asks for it.
pub open spec fn occurrence_ok(c: ASchedule, o: Occurrence, now: u64) -> bool {
    c.next_run_at <= o.at as nat && o.at <= now
}

// ---------------------------------------------------------------------------
// The three sweeper steps as functions of the state: what a node that fires
// deadlines is proved to compute, object by object.
// ---------------------------------------------------------------------------

/// `processPromiseTimeout`: the object projected at `now`, if there is one.
pub open spec fn promise_timeout_objects(a: AState, id: Seq<char>, now: nat) -> Map<Seq<char>, APromise> {
    if a.objects.contains_key(id) { a.objects.insert(id, a.objects[id].project(now)) } else { a.objects }
}

/// A lease is due: the task is acquired and its lease has passed, on a
/// promise still pending and not yet past its own deadline.
pub open spec fn lease_due(p: APromise, now: nat) -> bool {
    &&& p.task is Some
    &&& p.task.unwrap().state == TaskState::Acquired
    &&& p.task.unwrap().lease_timeout_at is Some
    &&& p.task.unwrap().lease_timeout_at.unwrap() <= now
    &&& p.state == PromiseState::Pending
    &&& p.timeout_at > now
}

/// `processLeaseTimeout`: a due lease returns the task to pending.
pub open spec fn lease_timeout_objects(a: AState, id: Seq<char>, now: nat) -> Map<Seq<char>, APromise> {
    if a.objects.contains_key(id) && lease_due(a.objects[id], now) {
        a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().release(now)))
    } else {
        a.objects
    }
}

/// A retry is due: the task is pending and its retry time has passed, on a
/// promise still pending and not yet past its own deadline.
pub open spec fn retry_due(p: APromise, now: nat) -> bool {
    &&& p.task is Some
    &&& p.task.unwrap().state == TaskState::Pending
    &&& p.task.unwrap().retry_timeout_at is Some
    &&& p.task.unwrap().retry_timeout_at.unwrap() <= now
    &&& p.state == PromiseState::Pending
    &&& p.timeout_at > now
}

/// `processRetryTimeout`: a due retry is re-armed `retry_timeout` ahead.
pub open spec fn retry_timeout_objects(a: AState, id: Seq<char>, now: nat, retry_timeout: nat) -> Map<Seq<char>, APromise> {
    if a.objects.contains_key(id) && retry_due(a.objects[id], now) {
        a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().rearm(now, retry_timeout)))
    } else {
        a.objects
    }
}

impl State {
    /// `processPromiseTimeout`: touch the object.
    pub fn process_promise_timeout(&mut self, req: &PromiseTimeoutReq, now: u64, cfg: &Config)
        requires
            pre(*old(self), now, *cfg),
        ensures
            ipost(*old(self), *final(self), now),
            final(self)@.objects == promise_timeout_objects(old(self)@, req.id@, now as nat),
            final(self)@.schedules == old(self)@.schedules,
            final(self)@.outbox == old(self)@.outbox,
    {
        let ghost a = self@;
        match self.read_object(&req.id, now) {
            None => {
                proof {
                    crate::frame::lemma_noop(now as nat, a);
                    lemma_internal_noop(now as nat, a);
                }
            }
            Some(_) => {
                proof {
                    lemma_project_legal(now as nat, a, self@, req.id@);
                    lemma_project_internal(now as nat, a, self@, |x: Seq<char>| x == req.id@);
                }
            }
        }
    }

    /// `processLeaseTimeout`: an expired lease returns the task to pending.
    pub fn process_lease_timeout(&mut self, req: &TaskLeaseTimeoutReq, now: u64, cfg: &Config)
        requires
            pre(*old(self), now, *cfg),
        ensures
            ipost(*old(self), *final(self), now),
            final(self)@.objects == lease_timeout_objects(old(self)@, req.id@, now as nat),
            final(self)@.schedules == old(self)@.schedules,
            final(self)@.outbox == old(self)@.outbox,
    {
        let ghost a = self@;
        proof {
            crate::frame::lemma_noop(now as nat, a);
            lemma_internal_noop(now as nat, a);
        }
        let i = match self.find_object(&req.id) {
            None => { return; }
            Some(i) => i,
        };
        proof { self.lemma_object_at(i as int); }
        let due = match &self.objects[i].task {
            None => { return; }
            Some(t) => match t.lease_timeout_at {
                None => { return; }
                Some(d) => t.state == TaskState::Acquired && d <= now,
            },
        };
        if !due || self.objects[i].state != PromiseState::Pending || self.objects[i].timeout_at <= now {
            return;
        }
        let ghost before = self.objects@;
        self.objects[i].task_release(now);
        proof {
            let x = req.id@;
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().release(now as nat))));
            lemma_release_legal(now as nat, a, self@, x);
            lemma_internal_one(now as nat, a, self@, x);
        }
    }

    /// `processRetryTimeout`: a due pending task is re-offered and re-armed.
    pub fn process_retry_timeout(&mut self, req: &TaskRetryTimeoutReq, now: u64, cfg: &Config)
        requires
            pre(*old(self), now, *cfg),
        ensures
            ipost(*old(self), *final(self), now),
            final(self)@.objects == retry_timeout_objects(old(self)@, req.id@, now as nat, cfg.retry_timeout as nat),
            final(self)@.schedules == old(self)@.schedules,
            !(old(self)@.objects.contains_key(req.id@) && retry_due(old(self)@.objects[req.id@], now as nat)) ==> final(self)@.outbox == old(self)@.outbox,
    {
        let ghost a = self@;
        proof {
            crate::frame::lemma_noop(now as nat, a);
            lemma_internal_noop(now as nat, a);
        }
        let i = match self.find_object(&req.id) {
            None => { return; }
            Some(i) => i,
        };
        proof { self.lemma_object_at(i as int); }
        let (due, version) = match &self.objects[i].task {
            None => { return; }
            Some(t) => match t.retry_timeout_at {
                None => { return; }
                Some(d) => (t.state == TaskState::Pending && d <= now, t.version),
            },
        };
        if !due || self.objects[i].state != PromiseState::Pending || self.objects[i].timeout_at <= now {
            return;
        }
        let address = crate::tags::exec_target_of(&self.objects[i].tags);
        let ghost before = self.objects@;
        self.objects[i].task_rearm(now, cfg.retry_timeout);
        proof {
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
        }
        let ghost a1 = self@;
        let e = OutboxEntry { address, message: Message::Execute { task_id: req.id.clone(), version } };
        self.upsert_outbox(e);
        proof {
            let x = req.id@;
            assert(a1.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().rearm(now as nat, cfg.retry_timeout as nat))));
            lemma_retry_legal(now as nat, a, self@, x, cfg.retry_timeout as nat);
            lemma_internal_one(now as nat, a, self@, x);
        }
    }

    /// `processListener`: a settled promise's listener is told, once.
    pub fn process_listener(&mut self, req: &PromiseRegisterListenerReq, now: u64, cfg: &Config)
        requires
            pre(*old(self), now, *cfg),
        ensures
            ipost(*old(self), *final(self), now),
            final(self)@.schedules == old(self)@.schedules,
    {
        let ghost a = self@;
        let i = match self.read_object(&req.awaited, now) {
            None => {
                proof {
                    crate::frame::lemma_noop(now as nat, a);
                    lemma_internal_noop(now as nat, a);
                }
                return;
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.awaited@);
            lemma_project_internal(now as nat, a, self@, |x: Seq<char>| x == req.awaited@);
        }
        if self.objects[i].state == PromiseState::Pending {
            return;
        }
        if !seq_contains(&self.objects[i].listeners, &req.address) {
            return;
        }
        let ghost a1 = self@;
        let ghost before = self.objects@;
        self.objects[i].remove_listener(&req.address);
        proof {
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
        }
        let rec = self.objects[i].to_record();
        let e = OutboxEntry { address: req.address.clone(), message: Message::Unblock(rec) };
        self.upsert_outbox(e);
        proof {
            let x = req.awaited@;
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].project(now as nat).remove_listener(req.address@)));
            assert(self@.outbox =~= a.outbox.insert(OutboxKey::Notify(x, req.address@), AOutboxEntry {
                address: req.address@,
                message: AMessage::Unblock(a.objects[x].project(now as nat).remove_listener(req.address@).to_record()),
            }));
            lemma_listener_legal(now as nat, a, self@, x, req.address@);
            lemma_internal_one(now as nat, a, self@, x);
        }
    }

    /// `processCallback`: a settled promise's callback resumes its awaiter.
    pub fn process_callback(&mut self, req: &PromiseRegisterCallbackReq, now: u64, cfg: &Config)
        requires
            pre(*old(self), now, *cfg),
        ensures
            ipost(*old(self), *final(self), now),
            final(self)@.schedules == old(self)@.schedules,
    {
        let ghost a = self@;
        let i = match self.read_object(&req.awaited, now) {
            None => {
                proof {
                    crate::frame::lemma_noop(now as nat, a);
                    lemma_internal_noop(now as nat, a);
                }
                return;
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.awaited@);
            lemma_project_internal(now as nat, a, self@, |x: Seq<char>| x == req.awaited@);
        }
        if self.objects[i].state == PromiseState::Pending {
            return;
        }
        if !seq_contains(&self.objects[i].callbacks, &req.awaiter) {
            return;
        }
        let ghost x = req.awaited@;
        let ghost y = req.awaiter@;
        proof {
            lemma_inv_pointwise(now as nat, a);
            assert(inv_obj(now as nat, a, x));
            assert(x != y);
        }
        let ghost before = self.objects@;
        self.objects[i].remove_callback(&req.awaiter);
        proof {
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
        }
        let ghost a1 = self@;
        // resumeOne
        let j = match self.read_task_object(&req.awaiter, now) {
            None => {
                proof { lemma_callback_legal(now as nat, a, self@, x, y, false); }
                return;
            }
            Some(j) => j,
        };
        proof {
            assert(j != i);
            self.lemma_object_at(j as int);
        }
        let state = match &self.objects[j].task {
            None => {
                proof { lemma_callback_legal(now as nat, a, self@, x, y, true); }
                return;
            }
            Some(t) => t.state,
        };
        let ghost before2 = self.objects@;
        if state == TaskState::Suspended {
            self.objects[j].task_wake(&req.awaited, now);
        } else if state != TaskState::Fulfilled {
            self.objects[j].task_buffer(&req.awaited);
        }
        proof {
            crate::store::lemma_fold_update(before2, crate::store::obj_key(), crate::store::obj_val(), j as int, self.objects@[j as int]);
            lemma_callback_legal(now as nat, a, self@, x, y, true);
        }
    }

    /// `processSchedule`: fire the due occurrences and advance the schedule.
    ///
    /// The caller's cron engine supplies the occurrences, in increasing order,
    /// each at or after the schedule's `next_run_at` and at or before `now`,
    /// and the next run strictly after the last of them.
    pub fn process_schedule(&mut self, req: &ScheduleTimeoutReq, now: u64, cfg: &Config)
        requires
            pre(*old(self), now, *cfg),
            forall|j: int| 0 <= j < req.occurrences@.len() ==> #[trigger] req.occurrences@[j].at <= now,
            forall|j: int, k: int| 0 <= j < k < req.occurrences@.len() ==> #[trigger] req.occurrences@[j].at < #[trigger] req.occurrences@[k].at,
            req.occurrences@.len() > 0 ==> req.next_run_at > req.occurrences@[req.occurrences@.len() - 1].at,
            old(self)@.schedules.contains_key(req.schedule@) && req.occurrences@.len() > 0 ==>
                old(self)@.schedules[req.schedule@].next_run_at <= req.occurrences@[0].at as nat,
        ensures
            ipost(*old(self), *final(self), now),
    {
        let ghost a = self@;
        let si = match self.find_schedule(&req.schedule) {
            None => {
                proof {
                    crate::frame::lemma_noop(now as nat, a);
                    lemma_internal_noop(now as nat, a);
                }
                return;
            }
            Some(si) => si,
        };
        proof { self.lemma_schedule_at(si as int); }
        if req.occurrences.len() == 0 {
            proof {
                crate::frame::lemma_noop(now as nat, a);
                lemma_internal_noop(now as nat, a);
            }
            return;
        }
        let ghost occs = req.occurrences@;
        let ghost sched = a.schedules[req.schedule@];
        proof {
            lemma_inv_pointwise(now as nat, a);
            assert(inv_sched(now as nat, a, req.schedule@));
        }
        let n = req.occurrences.len();
        let mut k: usize = 0;
        while k < n
            invariant
                a == old(self)@,
                k <= n,
                n == occs.len(),
                occs == req.occurrences@,
                now <= MAX_TIME,
                inv(now as nat, a),
                a.schedules.contains_key(req.schedule@),
                sched == a.schedules[req.schedule@],
                sched.promise_timeout <= MAX_TIME as nat,
                !crate::tags::timer_targeted(sched.promise_tags),
                forall|j: int| 0 <= j < n ==> #[trigger] occs[j].at <= now,
                si < self.schedules@.len(),
                self.schedules@[si as int]@ == sched,
                self.wf(),
                inv(now as nat, self@),
                self@.schedules == a.schedules,
                self@.outbox == a.outbox,
                forall|x: Seq<char>| !occ_touched(occs, k as int, x) ==> #[trigger] crate::external::unchanged_at(a, self@, x),
                forall|x: Seq<char>| #[trigger] occ_touched(occs, k as int, x) ==> fire_shape(now as nat, a, self@, sched, occs, x),
            decreases n - k,
        {
            let ghost s0 = self@;
            let o = &req.occurrences[k];
            let ghost x = o.promise_id@;
            let creq = PromiseCreateReq {
                id: o.promise_id.clone(),
                timeout_at: o.at + self.schedules[si].promise_timeout,
                param: self.schedules[si].promise_param.dup(),
                tags: clone_tags(&self.schedules[si].promise_tags),
            };
            match self.read_object(&o.promise_id, now) {
                Some(_) => {
                    proof {
                        lemma_project_legal(now as nat, s0, self@, x);
                        if occ_touched(occs, k as int, x) {
                            assert(fire_shape(now as nat, a, s0, sched, occs, x));
                            lemma_fire_project_idem(now as nat, a, s0, self@, sched, occs, x);
                        } else {
                            assert(crate::external::unchanged_at(a, s0, x));
                            crate::external_proof::lemma_project_idem(a.objects[x], now as nat);
                        }
                    }
                }
                None => {
                    let birth = if creq.timeout_at > now { o.at } else { now };
                    let p = create_promise(&creq, birth);
                    self.push_object(p);
                    proof {
                        assert(!s0.objects.contains_key(x));
                        if occ_touched(occs, k as int, x) {
                            assert(fire_shape(now as nat, a, s0, sched, occs, x));
                            assert(false);
                        }
                        assert(crate::external::unchanged_at(a, s0, x));
                        assert(!a.objects.contains_key(x));
                        assert(creq@ == occ_req(sched, occs[k as int]));
                        assert(self@.objects[x] == spec_create(occ_req(sched, occs[k as int]), birth_of(occs[k as int], sched, now as nat)));
                        lemma_fire_birth_legal(now as nat, s0, self@, sched, occs[k as int]);
                    }
                }
            }
            proof {
                let ghost b = self@;
                assert forall|y: Seq<char>| #[trigger] occ_touched(occs, k as int + 1, y) implies fire_shape(now as nat, a, b, sched, occs, y) by {
                    if y == x {
                        assert(fire_shape(now as nat, a, b, sched, occs, y));
                    } else {
                        let jj = choose|jj: int| 0 <= jj < k as int + 1 && #[trigger] occs[jj].promise_id@ == y;
                        assert(jj < k as int);
                        assert(occ_touched(occs, k as int, y));
                        assert(fire_shape(now as nat, a, s0, sched, occs, y));
                        assert(crate::external::unchanged_at(s0, b, y));
                    }
                }
                assert forall|y: Seq<char>| !occ_touched(occs, k as int + 1, y) implies #[trigger] crate::external::unchanged_at(a, b, y) by {
                    assert(!occ_touched(occs, k as int, y));
                    assert(occs[k as int].promise_id@ != y);
                    assert(crate::external::unchanged_at(a, s0, y));
                    assert(crate::external::unchanged_at(s0, b, y));
                }
            }
            k += 1;
        }
        // advance the schedule
        let last = req.occurrences[n - 1].at;
        let mut c = self.schedules[si].dup();
        c.last_run_at = Some(last);
        c.next_run_at = req.next_run_at;
        let ghost a2 = self@;
        self.set_schedule(si, c);
        proof {
            lemma_fire_legal(now as nat, a, a2, self@, req.schedule@, occs, req.next_run_at as nat);
        }
    }
}

// ---------------------------------------------------------------------------
// Shapes
// ---------------------------------------------------------------------------

/// Some occurrence among the first `k` expands to `x`.
pub open spec fn occ_touched(occs: Seq<Occurrence>, k: int, x: Seq<char>) -> bool {
    exists|j: int| 0 <= j < k && #[trigger] occs[j].promise_id@ == x
}

pub open spec fn occ_of(occs: Seq<Occurrence>, x: Seq<char>) -> bool {
    occ_touched(occs, occs.len() as int, x)
}

/// The create request an occurrence stands for.
pub open spec fn occ_req(c: ASchedule, o: Occurrence) -> APromiseCreateReq {
    APromiseCreateReq {
        id: o.promise_id@,
        timeout_at: o.at as nat + c.promise_timeout,
        param: c.promise_param,
        tags: c.promise_tags,
    }
}

/// When the occurrence's promise is born: at the occurrence if it is still
/// live at `now`, else at `now`, dead.
pub open spec fn birth_of(o: Occurrence, c: ASchedule, now: nat) -> nat {
    if o.at as nat + c.promise_timeout > now { o.at as nat } else { now }
}

/// What firing leaves at `x`: an existing object projected, or a promise born
/// of one of the occurrences that expand to `x`.
pub open spec fn fire_shape(now: nat, a: AState, b: AState, c: ASchedule, occs: Seq<Occurrence>, x: Seq<char>) -> bool {
    &&& b.objects.contains_key(x)
    &&& a.objects.contains_key(x) ==> b.objects[x] == a.objects[x].project(now)
    &&& !a.objects.contains_key(x) ==> exists|j: int| 0 <= j < occs.len() && #[trigger] occs[j].promise_id@ == x
        && b.objects[x] == spec_create(occ_req(c, occs[j]), birth_of(occs[j], c, now))
}

// ---------------------------------------------------------------------------
// Proofs
// ---------------------------------------------------------------------------

/// Nothing changed: the sweeper entries hold.
pub proof fn lemma_internal_noop(now: nat, a: AState)
    ensures
        internal_legal(now, a, a),
{
    assert forall|x: Seq<char>| #[trigger] internal_obj(now, a, a, x) by {}
    lemma_internal_pointwise(now, a, a);
}

/// Projecting objects is a sweeper step.
pub proof fn lemma_project_internal(now: nat, a: AState, b: AState, ids: spec_fn(Seq<char>) -> bool)
    requires
        forall|x: Seq<char>| #[trigger] ids(x) ==>
            a.objects.contains_key(x) && b.objects.contains_key(x) && b.objects[x] == a.objects[x].project(now),
        forall|x: Seq<char>| !ids(x) ==> #[trigger] crate::external::unchanged_at(a, b, x),
    ensures
        internal_legal(now, a, b),
{
    assert forall|x: Seq<char>| #[trigger] internal_obj(now, a, b, x) by {
        if ids(x) {
        } else {
            assert(crate::external::unchanged_at(a, b, x));
        }
    }
    lemma_internal_pointwise(now, a, b);
}

/// One object changed by an admissible sweeper edge, the rest untouched.
pub proof fn lemma_internal_one(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        forall|x: Seq<char>| x != id ==> #[trigger] crate::external::unchanged_at(a, b, x),
        consistent_task_state_edge_internal_admissible_at(now, b, id, a.objects[id]),
        consistent_promise_state_edge_internal_admissible_at(now, b, id, a.objects[id]),
    ensures
        internal_legal(now, a, b),
{
    assert forall|x: Seq<char>| #[trigger] internal_obj(now, a, b, x) by {
        if x != id {
            assert(crate::external::unchanged_at(a, b, x));
        }
    }
    lemma_internal_pointwise(now, a, b);
}

/// The retry dispatch: the task re-armed, an `execute` enqueued.
pub proof fn lemma_retry_legal(now: nat, a: AState, b: AState, id: Seq<char>, rt: nat)
    requires
        inv(now, a),
        0 < rt <= MAX_TIME as nat,
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Pending,
        a.objects[id].task.unwrap().retry_timeout_at is Some,
        a.objects[id].task.unwrap().retry_timeout_at.unwrap() <= now,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().rearm(now, rt))),
        b.schedules == a.schedules,
        b.outbox == a.outbox.insert(OutboxKey::Execute(id), AOutboxEntry {
            address: target_or_empty(a.objects[id]),
            message: AMessage::Execute { task_id: id, version: a.objects[id].task.unwrap().version },
        }),
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.rearm(now, rt);
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w != id {
            assert(b.objects.contains_key(w));
        }
    }
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    // the outbox entry
    let k = OutboxKey::Execute(id);
    let e = b.outbox[k];
    assert(e.key() == k);
    assert(b.has_task(id));
    assert(b.task_of(id) == Some(u));
    assert(inv_out(now, b, k));
    assert(trans_out(now, a, b, k));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    assert forall|kk: OutboxKey| kk != k implies
        (a.outbox.contains_key(kk) <==> #[trigger] b.outbox.contains_key(kk))
        && (a.outbox.contains_key(kk) ==> a.outbox[kk] == b.outbox[kk]) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |kk: OutboxKey| kk == k, |x: Seq<char>| false);
}

/// The listener drain: the promise was read, lost one listener, and the
/// listener's `unblock` was enqueued.
pub proof fn lemma_listener_legal(now: nat, a: AState, b: AState, id: Seq<char>, address: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].project(now).state != PromiseState::Pending,
        a.objects[id].project(now).listeners.contains(address),
        b.objects == a.objects.insert(id, a.objects[id].project(now).remove_listener(address)),
        b.schedules == a.schedules,
        b.outbox == a.outbox.insert(OutboxKey::Notify(id, address), AOutboxEntry {
            address: address,
            message: AMessage::Unblock(a.objects[id].project(now).remove_listener(address).to_record()),
        }),
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let m = p.project(now);
    let q = m.remove_listener(address);
    assert(b.objects[id] == q);
    assert(q.callbacks == p.callbacks && q.tags == p.tags);
    assert(q.listeners == without(p.listeners, address));
    lemma_without_no_dups(p.listeners, address);
    assert forall|y: Seq<char>| #[trigger] q.listeners.contains(y) implies p.listeners.contains(y) && y != address by {
        lemma_without_contains(p.listeners, address, y);
    }
    assert(!q.listeners.contains(address)) by {
        lemma_without_contains(p.listeners, address, address);
    }
    assert forall|i: int| 0 <= i < q.listeners.len() implies p.listeners.contains(#[trigger] q.listeners[i]) by {
        assert(q.listeners.contains(q.listeners[i]));
    }
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
    }
    // the settled promise's task is fulfilled, so no rung is owed
    assert(inv_obj(now, b, id));
    // the trans entries at id: the projection's, plus the listener consumed
    let k = OutboxKey::Notify(id, address);
    assert(b.outbox.contains_key(k));
    assert(b.outbox[k].key() == k);
    assert(one_unblock(b, id, address)) by {
        assert forall|kk: OutboxKey| #[trigger] b.outbox.contains_key(kk) && b.outbox[kk].address == address
            && (match b.outbox[kk].message { AMessage::Unblock(r) => r.id == id, AMessage::Execute { .. } => false })
            implies kk == k by {
            if kk != k {
                assert(a.outbox.contains_key(kk) && a.outbox[kk] == b.outbox[kk]);
                assert(inv_out(now, a, kk));
                assert(a.outbox[kk].key() == kk);
            }
        }
    }
    assert forall|i: int| 0 <= i < p.listeners.len() implies
        q.listeners.contains(#[trigger] p.listeners[i]) || one_unblock(b, id, p.listeners[i]) by {
        if p.listeners[i] != address {
            lemma_without_contains(p.listeners, address, p.listeners[i]);
        }
    }
    assert(trans_obj(now, a, b, id));
    // the outbox entry
    assert(inv_out(now, b, k));
    assert(trans_out(now, a, b, k));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    assert forall|kk: OutboxKey| kk != k implies
        (a.outbox.contains_key(kk) <==> #[trigger] b.outbox.contains_key(kk))
        && (a.outbox.contains_key(kk) ==> a.outbox[kk] == b.outbox[kk]) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |kk: OutboxKey| kk == k, |x: Seq<char>| false);
}

/// What the callback drain leaves at the awaiter.
pub open spec fn resumed_shape(now: nat, a: AState, b: AState, x: Seq<char>, y: Seq<char>) -> bool {
    &&& !a.objects.contains_key(y) ==> !b.objects.contains_key(y)
    &&& a.objects.contains_key(y) ==> b.objects.contains_key(y) && {
        let p = a.objects[y];
        let m = p.project(now);
        ||| b.objects[y] == p && p.task is None
        ||| b.objects[y] == m && (m.task is None || m.task.unwrap().state == TaskState::Fulfilled)
        ||| (m.task is Some && m.task.unwrap().state == TaskState::Suspended
                && b.objects[y] == m.with_task(m.task.unwrap().wake(x, now)))
        ||| (m.task is Some && m.task.unwrap().state != TaskState::Suspended && m.task.unwrap().state != TaskState::Fulfilled
                && b.objects[y] == m.with_task(m.task.unwrap().buffer(x)))
    }
}

/// The callback drain: the awaited promise, read and settled, lost the
/// awaiter's callback; the awaiter was read and resumed.
#[verifier::rlimit(120)]
pub proof fn lemma_callback_legal(now: nat, a: AState, b: AState, x: Seq<char>, y: Seq<char>, touched: bool)
    requires
        inv(now, a),
        x != y,
        a.objects.contains_key(x),
        a.objects[x].project(now).state != PromiseState::Pending,
        a.objects[x].project(now).callbacks.contains(y),
        b.objects.contains_key(x),
        b.objects[x] == a.objects[x].project(now).remove_callback(y),
        resumed_shape(now, a, b, x, y),
        forall|z: Seq<char>| z != x && z != y ==> #[trigger] crate::external::unchanged_at(a, b, z),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
        internal_legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, x));
    let p = a.objects[x];
    let m = p.project(now);
    let q = m.remove_callback(y);
    assert(q.callbacks == without(p.callbacks, y));
    assert(q.listeners == p.listeners && q.tags == p.tags);
    lemma_without_no_dups(p.callbacks, y);
    assert forall|z: Seq<char>| #[trigger] q.callbacks.contains(z) implies p.callbacks.contains(z) && z != y by {
        lemma_without_contains(p.callbacks, y, z);
    }
    assert(!q.callbacks.contains(y)) by {
        lemma_without_contains(p.callbacks, y, y);
    }
    assert forall|z: Seq<char>| p.callbacks.contains(z) && z != y implies #[trigger] q.callbacks.contains(z) by {
        lemma_without_contains(p.callbacks, y, z);
    }
    // every object keeps its tags; callbacks other than `y`'s survive
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) && z != y ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w == x {
        } else if w == y {
            assert(resumed_shape(now, a, b, x, y));
        } else {
            assert(crate::external::unchanged_at(a, b, w));
        }
    }
    // --- the awaited object ---
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable
        && crate::ident::same_origin_spec(q.callbacks[i], x) by {
        assert(q.callbacks.contains(q.callbacks[i]));
        let z = q.callbacks[i];
        assert(p.callbacks.contains(z));
        let ii = choose|ii: int| 0 <= ii < p.callbacks.len() && p.callbacks[ii] == z;
        assert(a.objects.contains_key(z) && a.objects[z].otype() == OType::Runnable);
    }
    assert forall|i: int| 0 <= i < q.callbacks.len() implies p.callbacks.contains(#[trigger] q.callbacks[i]) by {
        assert(q.callbacks.contains(q.callbacks[i]));
    }
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert(inv_obj(now, b, x));
    // callback consumption resumes the awaiter
    assert forall|i: int| 0 <= i < p.callbacks.len() implies {
        let z = #[trigger] p.callbacks[i];
        q.callbacks.contains(z)
        || match b.task_of(z) {
            None => true,
            Some(u) => u.state == TaskState::Fulfilled || u.resumes.contains(x),
        }
    } by {
        let z = p.callbacks[i];
        if z == y {
            assert(resumed_shape(now, a, b, x, y));
            if a.objects.contains_key(y) {
                let py = a.objects[y];
                let my = py.project(now);
                if b.objects[y] == py && py.task is None {
                } else if b.objects[y] == my && (my.task is None || my.task.unwrap().state == TaskState::Fulfilled) {
                } else if my.task is Some && my.task.unwrap().state == TaskState::Suspended
                    && b.objects[y] == my.with_task(my.task.unwrap().wake(x, now)) {
                    assert(b.objects[y].task.unwrap().resumes == seq![x]);
                    assert(b.objects[y].task.unwrap().resumes[0] == x);
                } else {
                    let u = my.task.unwrap().buffer(x);
                    if my.task.unwrap().resumes.contains(x) {
                    } else {
                        assert(u.resumes[u.resumes.len() - 1] == x);
                    }
                }
            }
        } else {
            assert(p.callbacks.contains(z));
        }
    }
    assert(trans_obj(now, a, b, x));
    assert(internal_obj(now, a, b, x));
    // --- the awaiter ---
    if a.objects.contains_key(y) {
        assert(inv_obj(now, a, y));
        let py = a.objects[y];
        let my = py.project(now);
        assert(b.objects.contains_key(y));
        if b.objects[y] == py && py.task is None {
            assert(crate::external::unchanged_at(a, b, y));
            lemma_trans_obj_unchanged(now, a, b, y);
            lemma_callback_frame_obj(now, a, b, x, y, y);
        } else if b.objects[y] == my && (my.task is None || my.task.unwrap().state == TaskState::Fulfilled) {
            lemma_project_trans_obj(now, a, b, y);
            lemma_project_inv_obj_lost(now, a, b, y, y);
        } else if my.task is Some && my.task.unwrap().state == TaskState::Suspended
            && b.objects[y] == my.with_task(my.task.unwrap().wake(x, now)) {
            lemma_projected_task_identity(now, a, y);
            assert(my == py);
            let t = py.task.unwrap();
            let u = t.wake(x, now);
            let qy = py.with_task(u);
            assert(b.objects[y] == qy);
            assert(u.resumes == seq![x]);
            assert(u.resumes.len() == 1);
            assert(u.resumes[0] == x);
            assert(no_dups(u.resumes));
            assert(u.resumes.contains(x));
            lemma_callback_edit_frame(now, a, b, x, y);
            assert(qy.project_promise(now) == qy);
            assert(t.resumes.len() == 0);
            assert(inv_obj(now, b, y));
            // wake follows callback consumption: `x` is the witness
            assert(a.objects[x].callbacks.contains(y));
            assert(!b.objects[x].callbacks.contains(y));
            assert(trans_obj(now, a, b, y));
            assert(internal_obj(now, a, b, y));
        } else {
            lemma_projected_task_identity(now, a, y);
            assert(my == py);
            let t = py.task.unwrap();
            let u = t.buffer(x);
            let qy = py.with_task(u);
            assert(b.objects[y] == qy);
            if t.resumes.contains(x) {
                assert(u == t);
            } else {
                assert(u.resumes == t.resumes.push(x));
                assert(no_dups(u.resumes)) by {
                    assert forall|i: int, j: int| 0 <= i < u.resumes.len() && 0 <= j < u.resumes.len()
                        && u.resumes[i] == u.resumes[j] implies i == j by {
                        if i < t.resumes.len() && j < t.resumes.len() {
                        } else if i < t.resumes.len() {
                            assert(t.resumes[i] == x);
                        } else if j < t.resumes.len() {
                            assert(t.resumes[j] == x);
                        }
                    }
                }
            }
            assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {
                if !t.resumes.contains(x) {
                    assert(u.resumes[i] == t.resumes[i]);
                }
            }
            lemma_callback_edit_frame(now, a, b, x, y);
            assert(qy.project_promise(now) == qy);
            // a suspended task is not buffered, so no rung moves
            assert(t.state != TaskState::Suspended);
            assert(inv_obj(now, b, y));
            assert(trans_obj(now, a, b, y));
            assert(internal_obj(now, a, b, y));
        }
    } else {
        assert(!b.objects.contains_key(y));
        assert(trans_obj(now, a, b, y));
        assert(internal_obj(now, a, b, y));
    }
    // --- the rest ---
    let changed = |z: Seq<char>| z == x || z == y;
    assert forall|z: Seq<char>| !changed(z) implies
        (a.objects.contains_key(z) <==> #[trigger] b.objects.contains_key(z))
        && (a.objects.contains_key(z) ==> a.objects[z] == b.objects[z]) by {
        assert(crate::external::unchanged_at(a, b, z));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z) && z != y
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    assert forall|z: Seq<char>| #[trigger] changed(z) && b.objects.contains_key(z) implies inv_obj(now, b, z) by {}
    assert forall|z: Seq<char>| #[trigger] changed(z) implies trans_obj(now, a, b, z) by {}
    crate::frame::lemma_step(now, a, b, changed, |z: Seq<char>| z == y, |k: OutboxKey| false, |z: Seq<char>| false);
    assert forall|z: Seq<char>| #[trigger] internal_obj(now, a, b, z) by {
        if !changed(z) {
            assert(crate::external::unchanged_at(a, b, z));
        }
    }
    lemma_internal_pointwise(now, a, b);
}

/// The awaiter's own pointers under the callback drain: it keeps its tags,
/// callbacks and listeners, and nothing it points at changed kind.
proof fn lemma_callback_edit_frame(now: nat, a: AState, b: AState, x: Seq<char>, y: Seq<char>)
    requires
        inv(now, a),
        x != y,
        a.objects.contains_key(y),
        b.objects.contains_key(y),
        b.objects[y].callbacks == a.objects[y].callbacks,
        b.objects[y].listeners == a.objects[y].listeners,
        b.objects[y].tags == a.objects[y].tags,
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags,
    ensures
        forall|i: int| 0 <= i < a.objects[y].callbacks.len() ==>
            b.objects[y].callbacks.contains(#[trigger] a.objects[y].callbacks[i]),
        forall|i: int| 0 <= i < a.objects[y].listeners.len() ==>
            b.objects[y].listeners.contains(#[trigger] a.objects[y].listeners[i]),
        consistent_callback_awaiter_is_targeted_at(now, b, b.objects[y]),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, y));
    let p = a.objects[y];
    let q = b.objects[y];
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        assert(b.objects[p.callbacks[i]].tags == a.objects[p.callbacks[i]].tags);
    }
}

/// An unchanged object whose task is not suspended, or whose rung is not
/// `lost`, still obeys the `.state` entries when only `lost`'s callbacks went.
proof fn lemma_callback_frame_obj(now: nat, a: AState, b: AState, x: Seq<char>, y: Seq<char>, z: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(z),
        b.objects.contains_key(z),
        a.objects[z] == b.objects[z],
        a.objects[z].task is None,
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags,
    ensures
        inv_obj(now, b, z),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, z));
    let p = a.objects[z];
    assert forall|i: int| 0 <= i < p.callbacks.len() implies
        b.objects.contains_key(#[trigger] p.callbacks[i]) && b.objects[p.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        assert(b.objects[p.callbacks[i]].tags == a.objects[p.callbacks[i]].tags);
    }
}

/// A projected object whose task ends fulfilled or absent obeys the `.state`
/// entries, whatever happened to callbacks elsewhere.
proof fn lemma_project_inv_obj_lost(now: nat, a: AState, b: AState, id: Seq<char>, lost: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].project(now),
        b.objects[id].task is None || b.objects[id].task.unwrap().state == TaskState::Fulfilled,
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags,
    ensures
        inv_obj(now, b, id),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let q = b.objects[id];
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        assert(b.objects[p.callbacks[i]].tags == a.objects[p.callbacks[i]].tags);
    }
}

/// Firing one occurrence on a fresh id is a legal step.
pub proof fn lemma_fire_birth_legal(now: nat, a: AState, b: AState, c: ASchedule, o: Occurrence)
    requires
        inv(now, a),
        !a.objects.contains_key(o.promise_id@),
        !crate::tags::timer_targeted(c.promise_tags),
        c.promise_timeout <= MAX_TIME as nat,
        o.at <= now,
        now <= MAX_TIME,
        b.objects == a.objects.insert(o.promise_id@, spec_create(occ_req(c, o), birth_of(o, c, now))),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
        fire_shape(now, a, b, c, seq![o], o.promise_id@),
{
    lemma_inv_pointwise(now, a);
    let req = occ_req(c, o);
    let t = birth_of(o, c, now);
    assert(req.timeout_at <= 2 * (MAX_TIME as nat));
    assert(t <= now);
    assert(req.timeout_at <= t || req.timeout_at > now);
    lemma_born_obj(now, t, a, b, req);
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == o.promise_id@, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
    assert(seq![o][0] == o);
}

/// Projecting again an object the firing already touched leaves the shape.
pub proof fn lemma_fire_project_idem(now: nat, a: AState, s0: AState, b: AState, c: ASchedule, occs: Seq<Occurrence>, x: Seq<char>)
    requires
        fire_shape(now, a, s0, c, occs, x),
        b.objects.contains_key(x),
        b.objects[x] == s0.objects[x].project(now),
    ensures
        fire_shape(now, a, b, c, occs, x),
{
    if a.objects.contains_key(x) {
        crate::external_proof::lemma_project_idem(a.objects[x], now);
    } else {
        let j = choose|j: int| 0 <= j < occs.len() && #[trigger] occs[j].promise_id@ == x
            && s0.objects[x] == spec_create(occ_req(c, occs[j]), birth_of(occs[j], c, now));
        let q = spec_create(occ_req(c, occs[j]), birth_of(occs[j], c, now));
        // a promise born live is ahead of `now`; one born dead is settled: both fixed by projection
        assert(q.project(now) == q);
    }
}

/// `processSchedule` as one step: the objects fired, the schedule advanced.
pub proof fn lemma_fire_legal(now: nat, a: AState, a2: AState, b: AState, sid: Seq<char>, occs: Seq<Occurrence>, next: nat)
    requires
        inv(now, a),
        inv(now, a2),
        a.schedules.contains_key(sid),
        occs.len() > 0,
        forall|j: int| 0 <= j < occs.len() ==> #[trigger] occs[j].at <= now,
        a.schedules[sid].next_run_at <= occs[0].at as nat,
        forall|j: int, k: int| 0 <= j < k < occs.len() ==> #[trigger] occs[j].at < #[trigger] occs[k].at,
        next > occs[occs.len() - 1].at as nat,
        forall|x: Seq<char>| !occ_of(occs, x) ==> #[trigger] crate::external::unchanged_at(a, a2, x),
        forall|x: Seq<char>| #[trigger] occ_of(occs, x) ==> fire_shape(now, a, a2, a.schedules[sid], occs, x),
        a2.schedules == a.schedules,
        a2.outbox == a.outbox,
        b.objects == a2.objects,
        b.outbox == a2.outbox,
        b.schedules == a2.schedules.insert(sid, ASchedule {
            last_run_at: Some(occs[occs.len() - 1].at as nat),
            next_run_at: next,
            ..a.schedules[sid]
        }),
    ensures
        inv(now, b),
        legal(now, a, b),
        internal_legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    lemma_inv_pointwise(now, a2);
    let c = a.schedules[sid];
    assert(inv_sched(now, a, sid));
    assert(c.created_at <= c.next_run_at);
    let last = occs[occs.len() - 1].at as nat;
    assert(occs[0].at <= occs[occs.len() - 1].at) by {
        if occs.len() > 1 {
            assert(occs[0].at < occs[occs.len() - 1].at);
        }
    }
    // the objects: a2 relative to a, pointwise
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].callbacks == a.objects[w].callbacks
        && b.objects[w].tags == a.objects[w].tags by {
        if occ_of(occs, w) {
            assert(fire_shape(now, a, a2, c, occs, w));
        } else {
            assert(crate::external::unchanged_at(a, a2, w));
        }
    }
    assert forall|x: Seq<char>| #[trigger] occ_of(occs, x) implies inv_obj(now, b, x) && trans_obj(now, a, b, x) by {
        assert(fire_shape(now, a, a2, c, occs, x));
        if a.objects.contains_key(x) {
            lemma_project_inv_obj(now, a, b, x);
            lemma_project_trans_obj(now, a, b, x);
        } else {
            let j = choose|j: int| 0 <= j < occs.len() && #[trigger] occs[j].promise_id@ == x
                && a2.objects[x] == spec_create(occ_req(c, occs[j]), birth_of(occs[j], c, now));
            let req = occ_req(c, occs[j]);
            let t = birth_of(occs[j], c, now);
            assert(inv_sched(now, a, sid));
            assert(c.promise_timeout <= MAX_TIME as nat);
            assert(req.timeout_at <= 2 * (MAX_TIME as nat));
            lemma_born_obj(now, t, a, b, req);
        }
    }
    assert forall|x: Seq<char>| !occ_of(occs, x) implies
        (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]) by {
        assert(crate::external::unchanged_at(a, a2, x));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    // the schedule
    assert(inv_sched(now, b, sid));
    assert(trans_sched(now, a, b, sid));
    assert forall|x: Seq<char>| x != sid implies
        (a.schedules.contains_key(x) <==> #[trigger] b.schedules.contains_key(x))
        && (a.schedules.contains_key(x) ==> a.schedules[x] == b.schedules[x]) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| occ_of(occs, x), |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| x == sid);
    // sweeper entries: births are vacuous, projections admissible
    assert forall|x: Seq<char>| #[trigger] internal_obj(now, a, b, x) by {
        if occ_of(occs, x) {
            assert(fire_shape(now, a, a2, c, occs, x));
        } else {
            assert(crate::external::unchanged_at(a, a2, x));
        }
    }
    lemma_internal_pointwise(now, a, b);
}

} // verus!
