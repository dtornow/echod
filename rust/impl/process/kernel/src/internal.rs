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
//! The spec functions the contracts name are `echod_concrete::internal_spec`.
//! The lemmas the bodies invoke are in `internal_proof`.

use vstd::prelude::*;

use crate::external::*;
use crate::internal_proof::*;
use crate::object::*;
use crate::store::*;
use crate::store_proof::*;
use crate::tags::OType;
use crate::types::*;

#[cfg(verus_keep_ghost)]
use crate::external_proof::*;
#[cfg(verus_keep_ghost)]
use crate::internal_spec::*;
#[cfg(verus_keep_ghost)]
use crate::properties::*;
#[cfg(verus_keep_ghost)]
use crate::properties_proof::*;

verus! {

/// What every internal step ensures: the catalogue, and the sweeper entries.
pub open spec fn ipost(a: State, b: State, now: u64) -> bool {
    &&& post(a, b, now)
    &&& internal_legal(now as nat, a@, b@)
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
        let (due, end) = match &self.objects[i].task {
            None => { return; }
            Some(t) => match t.lease_timeout_at {
                None => { return; }
                Some(d) => (t.state == TaskState::Acquired && d <= now, d),
            },
        };
        if !due || self.objects[i].state != PromiseState::Pending || self.objects[i].timeout_at <= now {
            return;
        }
        let ghost before = self.objects@;
        self.objects[i].task_release(end);
        proof {
            let x = req.id@;
            crate::store_proof::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            assert(self@.objects =~= a.objects.insert(x, a.objects[x].with_task(a.objects[x].task.unwrap().release(end as nat))));
            lemma_release_legal(now as nat, a, self@, x, end as nat);
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
            final(self)@.objects.dom() == old(self)@.objects.dom(),
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
            final(self)@.objects.dom() == old(self)@.objects.dom(),
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
            // the resumed task's first offer: when the awaited settled
            let since = match self.objects[i].settled_at { Some(t) => t, None => 0 };
            self.objects[j].task_wake(&req.awaited, since);
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
            forall|j: int| 0 <= j < req.occurrences.deep_view().len() ==> #[trigger] req.occurrences.deep_view()[j].at <= now,
            forall|j: int, k: int| 0 <= j < k < req.occurrences.deep_view().len() ==> #[trigger] req.occurrences.deep_view()[j].at < #[trigger] req.occurrences.deep_view()[k].at,
            req.occurrences.deep_view().len() > 0 ==> req.next_run_at > req.occurrences.deep_view()[req.occurrences.deep_view().len() - 1].at,
            old(self)@.schedules.contains_key(req.schedule@) && req.occurrences.deep_view().len() > 0 ==>
                old(self)@.schedules[req.schedule@].next_run_at <= req.occurrences.deep_view()[0].at as nat,
        ensures
            ipost(*old(self), *final(self), now),
            final(self)@ == spec_fire(old(self)@, req.schedule@, req.occurrences.deep_view(), req.next_run_at, now as nat),
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
        let ghost occs = req.occurrences.deep_view();
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
                occs == req.occurrences.deep_view(),
                now <= MAX_TIME,
                inv(now as nat, a),
                a.schedules.contains_key(req.schedule@),
                sched == a.schedules[req.schedule@],
                sched.id == req.schedule@,
                sched.promise_timeout <= MAX_TIME as nat,
                !crate::tags::timer_targeted(sched.promise_tags),
                forall|j: int| 0 <= j < n ==> #[trigger] occs[j].at <= now,
                si < self.schedules@.len(),
                self.schedules@[si as int]@ == sched,
                self.wf(),
                self@ == fire_fold(now as nat, a, sched, occs, k as int),
            decreases n - k,
        {
            let ghost s0 = self@;
            proof { lemma_fire_fold(now as nat, a, sched, occs, k as int); }
            let o = &req.occurrences[k];
            let ghost x = o.promise_id@;
            let creq = PromiseCreateReq {
                id: o.promise_id.clone(),
                timeout_at: o.at + self.schedules[si].promise_timeout,
                param: self.schedules[si].promise_param.dup(),
                tags: crate::tags::stamp_tags(&self.schedules[si].promise_tags, &req.schedule, &o.promise_id),
            };
            assert(occs[k as int] == o@);
            assert(creq@ == occ_req(sched, occs[k as int]));
            match self.find_object(&o.promise_id) {
                Some(i) => {
                    proof { self.lemma_object_at(i as int); }
                    assert(self@ == fire_step(now as nat, s0, sched, occs[k as int]));
                }
                None => {
                    let p = create_promise(&creq, o.at);
                    self.push_object(p);
                    assert(p@ == born_occurrence(sched, occs[k as int]));
                    assert(self@ == fire_step(now as nat, s0, sched, occs[k as int]));
                }
            }
            k += 1;
        }
        proof { lemma_fire_fold(now as nat, a, sched, occs, n as int); }
        // advance the schedule
        let last = req.occurrences[n - 1].at;
        let mut c = self.schedules[si].dup();
        c.last_run_at = Some(last);
        c.next_run_at = req.next_run_at;
        let ghost a2 = self@;
        self.set_schedule(si, c);
        proof {
            lemma_fire_legal(now as nat, a, a2, self@, req.schedule@, occs, req.next_run_at);
            assert(self@.schedules =~= a2.schedules.insert(req.schedule@, ASchedule { last_run_at: Some(last), next_run_at: req.next_run_at, ..sched }));
            assert(self@ == spec_fire(a, req.schedule@, occs, req.next_run_at, now as nat));
        }
    }
}

} // verus!
