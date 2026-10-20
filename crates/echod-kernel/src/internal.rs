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
//!
//! The spec functions the contracts name are here; the lemmas the bodies
//! invoke are in `internal_proof`.

use vstd::prelude::*;

use crate::external::*;
use crate::external_proof::*;
use crate::internal_proof::*;
use crate::object::*;
use crate::properties::*;
use crate::properties_proof::*;
use crate::store::*;
use crate::store_proof::*;
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
                    crate::properties_proof::lemma_noop(now as nat, a);
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
            crate::properties_proof::lemma_noop(now as nat, a);
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
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
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
            crate::properties_proof::lemma_noop(now as nat, a);
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
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
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
                    crate::properties_proof::lemma_noop(now as nat, a);
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
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
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
                    crate::properties_proof::lemma_noop(now as nat, a);
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
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
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
            crate::store_proof::lemma_fold_update(before2, crate::store::obj_key(), crate::store::obj_val(), j as int, self.objects@[j as int]);
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
                    crate::properties_proof::lemma_noop(now as nat, a);
                    lemma_internal_noop(now as nat, a);
                }
                return;
            }
            Some(si) => si,
        };
        proof { self.lemma_schedule_at(si as int); }
        if req.occurrences.len() == 0 {
            proof {
                crate::properties_proof::lemma_noop(now as nat, a);
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
            lemma_fire_legal(now as nat, a, a2, self@, req.schedule@, occs, req.next_run_at);
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
        timeout_at: (o.at + c.promise_timeout) as u64,
        param: c.promise_param,
        tags: c.promise_tags,
    }
}

/// When the occurrence's promise is born: at the occurrence if it is still
/// live at `now`, else at `now`, dead.
pub open spec fn birth_of(o: Occurrence, c: ASchedule, now: nat) -> nat {
    if occ_req(c, o).timeout_at > now { o.at as nat } else { now }
}

/// What firing leaves at `x`: an existing object projected, or a promise born
/// of one of the occurrences that expand to `x`.
pub open spec fn fire_shape(now: nat, a: AState, b: AState, c: ASchedule, occs: Seq<Occurrence>, x: Seq<char>) -> bool {
    &&& b.objects.contains_key(x)
    &&& a.objects.contains_key(x) ==> b.objects[x] == a.objects[x].project(now)
    &&& !a.objects.contains_key(x) ==> exists|j: int| 0 <= j < occs.len() && #[trigger] occs[j].promise_id@ == x
        && b.objects[x] == spec_create(occ_req(c, occs[j]), birth_of(occs[j], c, now))
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

} // verus!
