//! External steps: the task handlers that touch several objects.
//!
//! `task.fence` runs a promise handler on behalf of a task; `task.heartbeat`
//! refreshes many leases; `task.suspend` registers a task on many promises.

use vstd::prelude::*;

use crate::external::*;
use crate::external_task::*;
use crate::object::*;
use crate::properties::*;
use crate::store::{AState, State};
use crate::tags::OType;
use crate::types::*;

verus! {

// ---------------------------------------------------------------------------
// Shapes a loop leaves behind
// ---------------------------------------------------------------------------

/// Some ref among the first `k` names `x`.
pub open spec fn ref_touched(refs: Seq<TaskRef>, k: int, x: Seq<char>) -> bool {
    exists|j: int| 0 <= j < k && #[trigger] refs[j].id@ == x
}

/// Some ref names `x`.
pub open spec fn ref_of(refs: Seq<TaskRef>, x: Seq<char>) -> bool {
    ref_touched(refs, refs.len() as int, x)
}

/// What a heartbeat leaves at `x`: the object untouched, projected, or its
/// acquired lease refreshed.
pub open spec fn heartbeat_shape(now: nat, a: AState, b: AState, x: Seq<char>) -> bool {
    &&& !a.objects.contains_key(x) ==> !b.objects.contains_key(x)
    &&& a.objects.contains_key(x) ==> b.objects.contains_key(x) && {
        let p = a.objects[x];
        ||| b.objects[x] == p
        ||| b.objects[x] == p.project(now)
        ||| (p.task is Some && p.task.unwrap().state == TaskState::Acquired
                && p.state == PromiseState::Pending && p.timeout_at > now
                && b.objects[x] == p.with_task(p.task.unwrap().heartbeat(now)))
    }
}

/// Some action among the first `k` awaits `x`.
pub open spec fn awaited_touched(actions: Seq<PromiseRegisterCallbackReq>, k: int, x: Seq<char>) -> bool {
    exists|j: int| 0 <= j < k && #[trigger] actions[j].awaited@ == x
}

/// Some action awaits `x`.
pub open spec fn awaited_of(actions: Seq<PromiseRegisterCallbackReq>, x: Seq<char>) -> bool {
    awaited_touched(actions, actions.len() as int, x)
}

pub open spec fn awaited_distinct(actions: Seq<PromiseRegisterCallbackReq>) -> bool {
    forall|i: int, j: int| 0 <= i < actions.len() && 0 <= j < actions.len()
        && #[trigger] actions[i].awaited@ == #[trigger] actions[j].awaited@ ==> i == j
}

/// The door checks of `task.suspend`, as the loops carry them.
pub open spec fn suspend_doors(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>) -> bool {
    &&& actions.len() > 0
    &&& awaited_distinct(actions)
    &&& forall|j: int| 0 <= j < actions.len() ==>
        #[trigger] actions[j].awaited@ != id && crate::ident::same_origin_spec(actions[j].awaited@, id)
}

/// The task `task.suspend` found: acquired, on a pending promise ahead of its
/// deadline — so its projection was the identity.
pub open spec fn suspend_base(now: nat, a: AState, id: Seq<char>) -> bool {
    &&& inv(now, a)
    &&& a.objects.contains_key(id)
    &&& a.objects[id].task is Some
    &&& a.objects[id].task.unwrap().state == TaskState::Acquired
    &&& a.objects[id].state == PromiseState::Pending
    &&& a.objects[id].timeout_at > now
}

pub open spec fn unchanged_at(a: AState, b: AState, x: Seq<char>) -> bool {
    (a.objects.contains_key(x) <==> b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x])
}

impl State {
    /// `task.fence`.
    pub fn task_fence(&mut self, req: &TaskFenceReq, now: u64, cfg: &Config) -> (r: TaskFenceRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 409,
    {
        let ghost a = self@;
        let target: &String = match &req.action {
            TaskFenceAction::Create(c) => &c.id,
            TaskFenceAction::Settle(c) => &c.id,
        };
        if *target == req.id || !crate::ident::same_origin(target, &req.id) {
            proof { crate::frame::lemma_noop(now as nat, a); }
            return TaskFenceRes { status: 400, action: None };
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                return TaskFenceRes { status: 404, action: None };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, req.id@);
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
            TaskFenceAction::Create(c) => TaskFenceInnerRes::Create(self.promise_create(c, now, cfg)),
            TaskFenceAction::Settle(c) => TaskFenceInnerRes::Settle(self.promise_settle(c, now, cfg)),
        };
        proof { lemma_fence_legal(now as nat, a, a1, self@, req.id@, target@); }
        TaskFenceRes { status: 200, action: Some(inner) }
    }

    /// `task.heartbeat`.
    pub fn task_heartbeat(&mut self, req: &TaskHeartbeatReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200,
    {
        let ghost a = self@;
        let ghost refs = req.tasks@;
        let mut k: usize = 0;
        while k < req.tasks.len()
            invariant
                a == old(self)@,
                k <= refs.len(),
                refs == req.tasks@,
                now <= MAX_TIME,
                inv(now as nat, a),
                self.wf(),
                inv(now as nat, self@),
                self@.schedules == a.schedules,
                self@.outbox == a.outbox,
                forall|x: Seq<char>| !ref_touched(refs, k as int, x) ==> #[trigger] unchanged_at(a, self@, x),
                forall|x: Seq<char>| #[trigger] ref_touched(refs, k as int, x) ==> heartbeat_shape(now as nat, a, self@, x),
            decreases refs.len() - k,
        {
            let ghost s0 = self@;
            let x = &req.tasks[k].id;
            match self.read_task_object(x, now) {
                None => {
                    proof { assert(unchanged_at(s0, self@, x@)); }
                }
                Some(i) => {
                    proof {
                        self.lemma_object_at(i as int);
                        lemma_project_legal(now as nat, s0, self@, x@);
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
                            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                            assert(self@.objects =~= s0.objects.insert(x@, s0.objects[x@].with_task(s0.objects[x@].task.unwrap().heartbeat(now as nat))));
                            assert(heartbeat_shape(now as nat, s0, self@, x@));
                            assert forall|y: Seq<char>| !(y == x@) implies #[trigger] unchanged_at(s0, self@, y) by {}
                            lemma_heartbeat_legal(now as nat, s0, self@, |y: Seq<char>| y == x@);
                        }
                    } else {
                        proof { assert(heartbeat_shape(now as nat, s0, self@, x@)); }
                    }
                }
            }
            proof {
                let ghost b = self@;
                assert(heartbeat_shape(now as nat, s0, b, x@) || unchanged_at(s0, b, x@));
                assert forall|y: Seq<char>| y != x@ implies unchanged_at(s0, b, y) by {}
                assert forall|y: Seq<char>| #[trigger] ref_touched(refs, k as int + 1, y) implies heartbeat_shape(now as nat, a, b, y) by {
                    if y == x@ {
                        if ref_touched(refs, k as int, y) {
                            assert(heartbeat_shape(now as nat, a, s0, y));
                        } else {
                            assert(unchanged_at(a, s0, y));
                        }
                        lemma_heartbeat_compose(now as nat, a, s0, b, y);
                    } else {
                        let j = choose|j: int| 0 <= j < k as int + 1 && #[trigger] refs[j].id@ == y;
                        assert(j < k as int);
                        assert(ref_touched(refs, k as int, y));
                        assert(heartbeat_shape(now as nat, a, s0, y));
                        assert(unchanged_at(s0, b, y));
                        lemma_heartbeat_compose(now as nat, a, s0, b, y);
                    }
                }
                assert forall|y: Seq<char>| !ref_touched(refs, k as int + 1, y) implies #[trigger] unchanged_at(a, b, y) by {
                    assert(!ref_touched(refs, k as int, y));
                    assert(refs[k as int].id@ != y);
                    assert(unchanged_at(a, s0, y));
                    assert(unchanged_at(s0, b, y));
                }
            }
            k += 1;
        }
        proof {
            assert forall|y: Seq<char>| #[trigger] ref_of(refs, y) implies heartbeat_shape(now as nat, a, self@, y) by {}
            assert forall|y: Seq<char>| !ref_of(refs, y) implies #[trigger] unchanged_at(a, self@, y) by {}
            lemma_heartbeat_legal(now as nat, a, self@, |y: Seq<char>| ref_of(refs, y));
        }
        StatusRes { status: 200 }
    }

    /// `task.suspend`.
    pub fn task_suspend(&mut self, req: &TaskSuspendReq, now: u64, cfg: &Config) -> (r: StatusRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 300 || r.status == 400 || r.status == 404 || r.status == 409 || r.status == 422,
    {
        let ghost a = self@;
        let ghost acts = req.actions@;
        let ghost id = req.id@;
        let n = req.actions.len();
        if n == 0 || awaits_self_or_crosses(&req.actions, &req.id) || awaits_twice(&req.actions) {
            proof { crate::frame::lemma_noop(now as nat, a); }
            return StatusRes { status: 400 };
        }
        proof {
            assert forall|j: int| 0 <= j < acts.len() implies
                #[trigger] acts[j].awaited@ != id && crate::ident::same_origin_spec(acts[j].awaited@, id) by {}
            assert(suspend_doors(acts, id));
        }
        let i = match self.read_task_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                return StatusRes { status: 404 };
            }
            Some(i) => i,
        };
        proof {
            self.lemma_object_at(i as int);
            lemma_project_legal(now as nat, a, self@, id);
        }
        let (state, version) = match &self.objects[i].task {
            None => { return StatusRes { status: 404 }; }
            Some(t) => (t.state, t.version),
        };
        if state != TaskState::Acquired || self.objects[i].state != PromiseState::Pending || version != req.version {
            return StatusRes { status: 409 };
        }
        proof {
            lemma_projected_task_identity(now as nat, a, id);
            assert(suspend_base(now as nat, a, id));
            assert(self.objects@[i as int]@ == a.objects[id]);
            assert forall|x: Seq<char>| !awaited_touched(acts, 0, x) implies #[trigger] unchanged_at(a, self@, x) by {
                if x == id {
                    assert(self@.objects[id] == a.objects[id]);
                } else {
                    assert(self@.objects.contains_key(x) == a.objects.contains_key(x));
                }
            }
        }
        // checkAwaited
        let mut settled = false;
        let mut k: usize = 0;
        while k < n
            invariant
                a == old(self)@,
                k <= n,
                n == acts.len(),
                acts == req.actions@,
                id == req.id@,
                now <= MAX_TIME,
                suspend_base(now as nat, a, id),
                suspend_doors(acts, id),
                self.wf(),
                inv(now as nat, self@),
                self@.schedules == a.schedules,
                self@.outbox == a.outbox,
                i < self.objects@.len(),
                self.objects@[i as int].id@ == id,
                self.objects@[i as int]@ == a.objects[id],
                forall|x: Seq<char>| !awaited_touched(acts, k as int, x) ==> #[trigger] unchanged_at(a, self@, x),
                forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int, x) ==>
                    a.objects.contains_key(x)
                    && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x].project(now as nat),
                forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int, x) ==> a.objects[x].otype().awaitable(),
                settled == exists|j: int| 0 <= j < k && a.objects[#[trigger] acts[j].awaited@].project(now as nat).state != PromiseState::Pending,
            decreases n - k,
        {
            let ghost s0 = self@;
            let w = &req.actions[k].awaited;
            proof {
                assert(acts[k as int].awaited@ == w@);
                assert(w@ != id);
            }
            let j = match self.read_object(w, now) {
                None => {
                    proof {
                        assert forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int, x) implies
                            a.objects.contains_key(x) && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x].project(now as nat) by {}
                        assert forall|x: Seq<char>| !awaited_touched(acts, k as int, x) implies
                            (a.objects.contains_key(x) <==> #[trigger] self@.objects.contains_key(x))
                            && (a.objects.contains_key(x) ==> a.objects[x] == self@.objects[x]) by {
                            assert(unchanged_at(a, self@, x));
                        }
                        lemma_project_many(now as nat, a, self@, |x: Seq<char>| awaited_touched(acts, k as int, x));
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
                assert forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int + 1, x) implies
                    a.objects.contains_key(x)
                    && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x].project(now as nat) by {
                    if x == w@ {
                    } else {
                        let jj = choose|jj: int| 0 <= jj < k as int + 1 && #[trigger] acts[jj].awaited@ == x;
                        assert(jj < k as int);
                        assert(awaited_touched(acts, k as int, x));
                    }
                }
                assert forall|x: Seq<char>| !awaited_touched(acts, k as int + 1, x) implies #[trigger] unchanged_at(a, self@, x) by {
                    assert(!awaited_touched(acts, k as int, x));
                    assert(acts[k as int].awaited@ != x);
                    assert(unchanged_at(a, s0, x));
                }
            }
            if !self.objects[j].otype().is_awaitable() {
                proof {
                    assert forall|x: Seq<char>| !awaited_touched(acts, k as int + 1, x) implies
                        (a.objects.contains_key(x) <==> #[trigger] self@.objects.contains_key(x))
                        && (a.objects.contains_key(x) ==> a.objects[x] == self@.objects[x]) by {
                        assert(unchanged_at(a, self@, x));
                    }
                    lemma_project_many(now as nat, a, self@, |x: Seq<char>| awaited_touched(acts, k as int + 1, x));
                }
                return StatusRes { status: 422 };
            }
            proof {
                assert(a.objects[w@].otype() == self@.objects[w@].otype());
                assert forall|x: Seq<char>| #[trigger] awaited_touched(acts, k as int + 1, x) implies a.objects[x].otype().awaitable() by {
                    if x != w@ {
                        let jj = choose|jj: int| 0 <= jj < k as int + 1 && #[trigger] acts[jj].awaited@ == x;
                        assert(jj < k as int);
                        assert(awaited_touched(acts, k as int, x));
                    }
                }
            }
            if self.objects[j].state != PromiseState::Pending {
                settled = true;
            }
            proof {
                assert(a.objects[acts[k as int].awaited@].project(now as nat).state == self@.objects[w@].state);
            }
            k += 1;
        }
        if settled {
            let ghost s_prev = self@;
            let ghost before = self.objects@;
            self.objects[i].task_clear_resumes();
            proof {
                crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                let ghost b = self@;
                assert(b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().clear_resumes()));
                assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
                    a.objects.contains_key(x) && x != id
                    && b.objects.contains_key(x) && b.objects[x] == a.objects[x].project(now as nat) by {
                    assert(awaited_touched(acts, n as int, x));
                    let jj = choose|jj: int| 0 <= jj < n && #[trigger] acts[jj].awaited@ == x;
                    assert(s_prev.objects.contains_key(x) && s_prev.objects[x] == a.objects[x].project(now as nat));
                }
                assert forall|x: Seq<char>| !awaited_of(acts, x) && x != id implies #[trigger] unchanged_at(a, b, x) by {
                    assert(!awaited_touched(acts, n as int, x));
                    assert(unchanged_at(a, s_prev, x));
                    assert(b.objects.contains_key(x) == s_prev.objects.contains_key(x));
                }
                lemma_suspend_300_legal(now as nat, a, b, id, acts);
            }
            return StatusRes { status: 300 };
        }
        // registerAwaited: every awaited promise is pending, so its projection was the identity
        proof {
            assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
                a.objects.contains_key(x) && a.objects[x].otype().awaitable()
                && a.objects[x].state == PromiseState::Pending && a.objects[x].timeout_at > now
                && x != id && crate::ident::same_origin_spec(x, id)
                && self@.objects.contains_key(x) && self@.objects[x] == a.objects[x] by {
                assert(awaited_touched(acts, n as int, x));
                let jj = choose|jj: int| 0 <= jj < n && #[trigger] acts[jj].awaited@ == x;
                assert(a.objects[acts[jj].awaited@].project(now as nat).state == PromiseState::Pending);
            }
            assert forall|j: int| 0 <= j < n implies self@.objects.contains_key(#[trigger] acts[j].awaited@)
                && self@.objects[acts[j].awaited@] == a.objects[acts[j].awaited@] by {
                assert(awaited_touched(acts, n as int, acts[j].awaited@));
                assert(awaited_of(acts, acts[j].awaited@));
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
                acts == req.actions@,
                id == req.id@,
                now <= MAX_TIME,
                suspend_base(now as nat, a, id),
                suspend_doors(acts, id),
                self.wf(),
                inv(now as nat, self@),
                self@.schedules == a.schedules,
                self@.outbox == a.outbox,
                i < self.objects@.len(),
                self.objects@[i as int].id@ == id,
                self.objects@[i as int]@ == a.objects[id],
                forall|x: Seq<char>| !awaited_of(acts, x) ==> #[trigger] unchanged_at(a, self@, x),
                forall|x: Seq<char>| #[trigger] awaited_of(acts, x) ==>
                    a.objects.contains_key(x) && a.objects[x].otype().awaitable()
                    && a.objects[x].state == PromiseState::Pending && a.objects[x].timeout_at > now
                    && x != id && crate::ident::same_origin_spec(x, id),
                forall|j: int| 0 <= j < k ==> self@.objects.contains_key(#[trigger] acts[j].awaited@)
                    && self@.objects[acts[j].awaited@] == a.objects[acts[j].awaited@].add_callback(id),
                forall|j: int| k <= j < n ==> self@.objects.contains_key(#[trigger] acts[j].awaited@)
                    && self@.objects[acts[j].awaited@] == a.objects[acts[j].awaited@],
            decreases n - k,
        {
            let ghost s0 = self@;
            let w = &req.actions[k].awaited;
            proof {
                assert(acts[k as int].awaited@ == w@);
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
                crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), j as int, self.objects@[j as int]);
                assert(self@.objects =~= s0.objects.insert(w@, s0.objects[w@].add_callback(id)));
                assert(a.objects[w@].project(now as nat) == a.objects[w@]);
                assert(a.objects[id].project(now as nat) == a.objects[id]);
                lemma_inv_pointwise(now as nat, s0);
                assert(inv_obj(now as nat, s0, id));
                assert(s0.objects[id].otype() == OType::Runnable);
                lemma_add_callback_legal(now as nat, s0, self@, w@, id);
                let ghost b = self@;
                assert forall|jj: int| 0 <= jj < k as int + 1 implies b.objects.contains_key(#[trigger] acts[jj].awaited@)
                    && b.objects[acts[jj].awaited@] == a.objects[acts[jj].awaited@].add_callback(id) by {
                    if jj < k as int {
                        assert(acts[jj].awaited@ != w@);
                    }
                }
                assert forall|jj: int| k as int + 1 <= jj < n implies b.objects.contains_key(#[trigger] acts[jj].awaited@)
                    && b.objects[acts[jj].awaited@] == a.objects[acts[jj].awaited@] by {
                    assert(acts[jj].awaited@ != w@);
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
        self.objects[i].task_suspend();
        proof {
            crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
            let ghost b = self@;
            assert(b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().suspend()));
            assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
                b.objects.contains_key(x) && b.objects[x] == a.objects[x].add_callback(id) by {
                assert(awaited_touched(acts, n as int, x));
                let jj = choose|jj: int| 0 <= jj < n && #[trigger] acts[jj].awaited@ == x;
                assert(s_prev.objects.contains_key(x) && s_prev.objects[x] == a.objects[x].add_callback(id));
            }
            assert forall|x: Seq<char>| !awaited_of(acts, x) && x != id implies #[trigger] unchanged_at(a, b, x) by {
                assert(unchanged_at(a, s_prev, x));
                assert(b.objects.contains_key(x) == s_prev.objects.contains_key(x));
            }
            lemma_suspend_legal(now as nat, a, b, id, acts);
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
        r == exists|j: int| 0 <= j < actions@.len()
            && (#[trigger] actions@[j].awaited@ == id@ || !crate::ident::same_origin_spec(actions@[j].awaited@, id@)),
{
    let mut k: usize = 0;
    while k < actions.len()
        invariant
            k <= actions@.len(),
            forall|j: int| 0 <= j < k ==>
                #[trigger] actions@[j].awaited@ != id@ && crate::ident::same_origin_spec(actions@[j].awaited@, id@),
        decreases actions@.len() - k,
    {
        if actions[k].awaited == *id || !crate::ident::same_origin(&actions[k].awaited, id) {
            return true;
        }
        k += 1;
    }
    false
}

/// Does any promise appear twice?
pub fn awaits_twice(actions: &Vec<PromiseRegisterCallbackReq>) -> (r: bool)
    ensures r == !awaited_distinct(actions@),
{
    let mut k: usize = 0;
    while k < actions.len()
        invariant
            k <= actions@.len(),
            forall|i: int, j: int| 0 <= i < k && 0 <= j < actions@.len()
                && #[trigger] actions@[i].awaited@ == #[trigger] actions@[j].awaited@ ==> i == j,
        decreases actions@.len() - k,
    {
        let mut m: usize = 0;
        while m < actions.len()
            invariant
                k < actions@.len(),
                m <= actions@.len(),
                forall|i: int, j: int| 0 <= i < k && 0 <= j < actions@.len()
                    && #[trigger] actions@[i].awaited@ == #[trigger] actions@[j].awaited@ ==> i == j,
                forall|j: int| 0 <= j < m && j != k ==> #[trigger] actions@[j].awaited@ != actions@[k as int].awaited@,
            decreases actions@.len() - m,
        {
            if m != k && actions[m].awaited == actions[k].awaited {
                return true;
            }
            m += 1;
        }
        k += 1;
    }
    false
}

// ---------------------------------------------------------------------------
// Proofs
// ---------------------------------------------------------------------------

/// Projection is idempotent.
pub proof fn lemma_project_idem(p: APromise, now: nat)
    ensures p.project(now).project(now) == p.project(now),
{
}

/// A heartbeat step from a state in heartbeat shape relative to `a` leaves a
/// state in heartbeat shape relative to `a`.
pub proof fn lemma_heartbeat_compose(now: nat, a: AState, s0: AState, b: AState, x: Seq<char>)
    requires
        heartbeat_shape(now, a, s0, x) || unchanged_at(a, s0, x),
        heartbeat_shape(now, s0, b, x) || unchanged_at(s0, b, x),
    ensures
        heartbeat_shape(now, a, b, x),
{
    if a.objects.contains_key(x) {
        let p = a.objects[x];
        assert(s0.objects.contains_key(x));
        let m = s0.objects[x];
        assert(b.objects.contains_key(x));
        if b.objects[x] == m {
        } else if b.objects[x] == m.project(now) {
            if m == p {
            } else if m == p.project(now) {
                lemma_project_idem(p, now);
            } else {
                let h = p.with_task(p.task.unwrap().heartbeat(now));
                assert(m == h);
                assert(h.project(now) == h);
            }
        } else {
            // m had an acquired task on a pending promise, and b[x] is m with its lease refreshed
            assert(m.task is Some && m.task.unwrap().state == TaskState::Acquired && m.state == PromiseState::Pending && m.timeout_at > now);
            if m == p {
            } else if m == p.project(now) {
                assert(p.project(now) == p);
            } else {
                let h = p.with_task(p.task.unwrap().heartbeat(now));
                assert(m == h);
                assert(h.with_task(h.task.unwrap().heartbeat(now)) == h);
            }
        }
    } else {
        assert(!s0.objects.contains_key(x));
        assert(!b.objects.contains_key(x));
    }
}

/// Any set of objects each untouched, projected or lease-refreshed is a legal step.
pub proof fn lemma_heartbeat_legal(now: nat, a: AState, b: AState, ids: spec_fn(Seq<char>) -> bool)
    requires
        inv(now, a),
        forall|x: Seq<char>| #[trigger] ids(x) ==> heartbeat_shape(now, a, b, x),
        forall|x: Seq<char>| !ids(x) ==> #[trigger] unchanged_at(a, b, x),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].callbacks == a.objects[w].callbacks
        && b.objects[w].tags == a.objects[w].tags by {
        if ids(w) {
            assert(heartbeat_shape(now, a, b, w));
            let p = a.objects[w];
            if b.objects[w] == p {
            } else if b.objects[w] == p.project(now) {
            } else {
                assert(b.objects[w] == p.with_task(p.task.unwrap().heartbeat(now)));
            }
        } else {
            assert(unchanged_at(a, b, w));
        }
    }
    assert(pointer_frame(a, b));
    // the changed ids
    assert forall|x: Seq<char>| #[trigger] ids(x) && b.objects.contains_key(x) implies inv_obj(now, b, x) && trans_obj(now, a, b, x) by {
        assert(heartbeat_shape(now, a, b, x));
        assert(a.objects.contains_key(x));
        assert(inv_obj(now, a, x));
        let p = a.objects[x];
        if b.objects[x] == p {
            assert(unchanged_at(a, b, x));
            lemma_trans_obj_unchanged(now, a, b, x);
            crate::frame::lemma_inv_obj_frame_simple(now, a, b, x);
        } else if b.objects[x] == p.project(now) {
            lemma_project_inv_obj(now, a, b, x);
            lemma_project_trans_obj(now, a, b, x);
        } else {
            let t = p.task.unwrap();
            let u = t.heartbeat(now);
            let q = p.with_task(u);
            assert(b.objects[x] == q);
            lemma_task_edit_frame(now, a, b, x);
            assert(q.project_promise(now) == q);
            assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
            assert(inv_obj(now, b, x));
            assert(trans_obj(now, a, b, x));
        }
    }
    assert forall|x: Seq<char>| #[trigger] ids(x) implies trans_obj(now, a, b, x) by {
        if !b.objects.contains_key(x) {
            assert(heartbeat_shape(now, a, b, x));
            assert(!a.objects.contains_key(x));
        }
    }
    assert forall|x: Seq<char>| !ids(x) implies
        (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]) by {
        assert(unchanged_at(a, b, x));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, ids, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `task.suspend`'s 300: the task keeps running with its ledger cleared, and
/// every awaited promise was read.
pub proof fn lemma_suspend_300_legal(now: nat, a: AState, b: AState, id: Seq<char>, acts: Seq<PromiseRegisterCallbackReq>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Acquired,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().clear_resumes()),
        forall|x: Seq<char>| #[trigger] awaited_of(acts, x) ==>
            a.objects.contains_key(x) && x != id
            && b.objects.contains_key(x) && b.objects[x] == a.objects[x].project(now),
        forall|x: Seq<char>| !awaited_of(acts, x) && x != id ==> #[trigger] unchanged_at(a, b, x),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    let changed = |x: Seq<char>| x == id || awaited_of(acts, x);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].callbacks == a.objects[w].callbacks
        && b.objects[w].tags == a.objects[w].tags by {
        if w == id {
        } else if awaited_of(acts, w) {
        } else {
            assert(unchanged_at(a, b, w));
        }
    }
    assert forall|x: Seq<char>| #[trigger] changed(x) && b.objects.contains_key(x) implies inv_obj(now, b, x) by {
        if x == id {
            assert(inv_obj(now, a, x));
            let p = a.objects[x];
            let t = p.task.unwrap();
            let u = t.clear_resumes();
            let q = p.with_task(u);
            assert(pointer_frame(a, b));
            lemma_task_edit_frame(now, a, b, x);
            assert(q.project_promise(now) == q);
            assert(inv_obj(now, b, x));
        } else {
            lemma_project_inv_obj(now, a, b, x);
        }
    }
    assert forall|x: Seq<char>| #[trigger] changed(x) implies trans_obj(now, a, b, x) by {
        if x == id {
            assert(inv_obj(now, a, x));
            let p = a.objects[x];
            let t = p.task.unwrap();
            let u = t.clear_resumes();
            let q = p.with_task(u);
            assert(pointer_frame(a, b));
            lemma_task_edit_frame(now, a, b, x);
            assert(q.project_promise(now) == q);
            assert(trans_obj(now, a, b, x));
        } else {
            lemma_project_trans_obj(now, a, b, x);
        }
    }
    assert forall|x: Seq<char>| !changed(x) implies
        (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]) by {
        assert(unchanged_at(a, b, x));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, changed, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `add_callback` registers `y`, and keeps what was registered.
pub proof fn lemma_add_callback_contains(p: APromise, y: Seq<char>)
    ensures
        p.add_callback(y).callbacks.contains(y),
        forall|z: Seq<char>| p.callbacks.contains(z) ==> #[trigger] p.add_callback(y).callbacks.contains(z),
        p.add_callback(y).tags == p.tags,
        p.add_callback(y).state == p.state,
{
    let q = p.add_callback(y);
    if p.callbacks.contains(y) {
    } else {
        assert(q.callbacks[q.callbacks.len() - 1] == y);
        assert forall|z: Seq<char>| p.callbacks.contains(z) implies #[trigger] q.callbacks.contains(z) by {
            let i = choose|i: int| 0 <= i < p.callbacks.len() && p.callbacks[i] == z;
            assert(q.callbacks[i] == z);
        }
    }
}

/// The parked task itself obeys the catalogue at its id, given a rung.
proof fn lemma_suspended_task_obj(now: nat, a: AState, b: AState, id: Seq<char>, w0: Seq<char>)
    requires
        suspend_base(now, a, id),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().suspend()),
        b.objects.contains_key(w0),
        b.objects[w0].callbacks.contains(id),
        b.objects[w0].state == PromiseState::Pending,
        pointer_frame(a, b),
    ensures
        inv_obj(now, b, id),
        trans_obj(now, a, b, id),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.suspend();
    let q = p.with_task(u);
    assert(some_callbacks_contain(b, id));
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert(u.resumes.len() == 0);
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
}

/// `task.suspend`'s 200: the task parked, registered on every awaited promise.
#[verifier::rlimit(400)]
pub proof fn lemma_suspend_legal(now: nat, a: AState, b: AState, id: Seq<char>, acts: Seq<PromiseRegisterCallbackReq>)
    requires
        suspend_base(now, a, id),
        acts.len() > 0,
        awaited_distinct(acts),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].with_task(a.objects[id].task.unwrap().suspend()),
        forall|x: Seq<char>| #[trigger] awaited_of(acts, x) ==>
            a.objects.contains_key(x) && a.objects[x].otype().awaitable()
            && a.objects[x].state == PromiseState::Pending && a.objects[x].timeout_at > now
            && x != id && crate::ident::same_origin_spec(x, id)
            && b.objects.contains_key(x) && b.objects[x] == a.objects[x].add_callback(id),
        forall|x: Seq<char>| !awaited_of(acts, x) && x != id ==> #[trigger] unchanged_at(a, b, x),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let changed = |x: Seq<char>| x == id || awaited_of(acts, x);
    assert(a.objects[id].otype() == OType::Runnable);
    // pointers survive
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w == id {
        } else if awaited_of(acts, w) {
            lemma_add_callback_contains(a.objects[w], id);
        } else {
            assert(unchanged_at(a, b, w));
        }
    }
    assert(pointer_frame(a, b));
    // the rung: the first awaited promise holds `id`
    let w0 = acts[0].awaited@;
    assert(awaited_touched(acts, acts.len() as int, w0));
    assert(awaited_of(acts, w0));
    lemma_add_callback_contains(a.objects[w0], id);
    assert(b.objects[w0].callbacks.contains(id));
    assert(b.objects[w0].state == PromiseState::Pending);
    assert(b.objects[id].otype() == OType::Runnable);
    // the task object
    lemma_suspended_task_obj(now, a, b, id, w0);
    // the awaited objects
    assert forall|x: Seq<char>| #[trigger] awaited_of(acts, x) implies
        inv_obj(now, b, x) && trans_obj(now, a, b, x) by {
        lemma_added_callback_obj(now, a, b, x, id);
    }
    assert forall|x: Seq<char>| #[trigger] changed(x) && b.objects.contains_key(x) implies inv_obj(now, b, x) by {}
    assert forall|x: Seq<char>| #[trigger] changed(x) implies trans_obj(now, a, b, x) by {}
    assert forall|x: Seq<char>| !changed(x) implies
        (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]) by {
        assert(unchanged_at(a, b, x));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, changed, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// A pending, awaitable promise that gained a callback on a runnable, pending
/// awaiter of its origin obeys the catalogue at its id.
pub proof fn lemma_added_callback_obj(now: nat, a: AState, b: AState, w: Seq<char>, awaiter: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(w),
        w != awaiter,
        crate::ident::same_origin_spec(awaiter, w),
        a.objects[w].state == PromiseState::Pending,
        a.objects[w].otype().awaitable(),
        b.objects.contains_key(w),
        b.objects[w] == a.objects[w].add_callback(awaiter),
        b.objects.contains_key(awaiter),
        b.objects[awaiter].otype() == OType::Runnable,
        pointer_frame(a, b),
    ensures
        inv_obj(now, b, w),
        trans_obj(now, a, b, w),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, w));
    let p = a.objects[w];
    let q = p.add_callback(awaiter);
    lemma_add_callback_contains(p, awaiter);
    if p.callbacks.contains(awaiter) {
        assert(q == p);
    } else {
        assert(q.callbacks == p.callbacks.push(awaiter));
        assert(no_dups(q.callbacks)) by {
            assert forall|i: int, j: int| 0 <= i < q.callbacks.len() && 0 <= j < q.callbacks.len()
                && q.callbacks[i] == q.callbacks[j] implies i == j by {
                if i < p.callbacks.len() && j < p.callbacks.len() {
                } else if i < p.callbacks.len() {
                    assert(p.callbacks[i] == awaiter);
                } else if j < p.callbacks.len() {
                    assert(p.callbacks[j] == awaiter);
                }
            }
        }
    }
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable
        && crate::ident::same_origin_spec(q.callbacks[i], w) && q.callbacks[i] != w by {
        if i < p.callbacks.len() {
            assert(q.callbacks[i] == p.callbacks[i]);
            assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
            assert(b.objects[p.callbacks[i]].tags == a.objects[p.callbacks[i]].tags);
        } else {
            assert(q.callbacks[i] == awaiter);
        }
    }
    assert(!q.callbacks.contains(w));
    match q.task {
        Some(t) => {
            if t.state == TaskState::Suspended && q.project_promise(now).state == PromiseState::Pending {
                assert(some_callbacks_contain(a, w));
                let w2 = choose|w2: Seq<char>| #[trigger] a.objects.contains_key(w2) && a.objects[w2].callbacks.contains(w);
                assert(b.objects[w2].callbacks.contains(w));
                assert(some_callbacks_contain(b, w));
            }
        }
        None => {}
    }
    assert(inv_obj(now, b, w));
    assert(trans_obj(now, a, b, w));
}

/// One projected object makes every other id's `.trans` entries carry from
/// the intermediate state back to the start.
pub proof fn lemma_trans_obj_transfer(now: nat, a: AState, a1: AState, c: AState, y: Seq<char>)
    requires
        trans_obj(now, a1, c, y),
        a.objects.contains_key(y) <==> a1.objects.contains_key(y),
        a.objects.contains_key(y) ==> a.objects[y] == a1.objects[y],
        forall|w: Seq<char>| #[trigger] a1.objects.contains_key(w) ==>
            a.objects.contains_key(w) && a1.objects[w].callbacks == a.objects[w].callbacks,
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==> a1.objects.contains_key(w),
    ensures
        trans_obj(now, a, c, y),
{
    if c.objects.contains_key(y) {
        let q = c.objects[y];
        assert(a.task_of(y) == a1.task_of(y));
        assert(a.promise_of(y) == a1.promise_of(y));
        assert(a.has_task(y) == a1.has_task(y));
        match q.task {
            Some(u) => {
                match a1.task_of(y) {
                    Some(t) => {
                        if t.state == TaskState::Suspended && u.state == TaskState::Pending {
                            assert(consistent_wake_follows_callback_consumption_at(now, a1, c, y, q));
                            assert(exists|pid: Seq<char>| #[trigger] a1.objects.contains_key(pid)
                                && a1.objects[pid].callbacks.contains(y)
                                && (match c.promise_of(pid) { None => false, Some(w) => !w.callbacks.contains(y) })
                                && u.resumes.contains(pid));
                            let pid = choose|pid: Seq<char>| #[trigger] a1.objects.contains_key(pid)
                                && a1.objects[pid].callbacks.contains(y)
                                && (match c.promise_of(pid) { None => false, Some(w) => !w.callbacks.contains(y) })
                                && u.resumes.contains(pid);
                            assert(a1.objects.contains_key(pid));
                            assert(a.objects.contains_key(pid));
                            assert(a1.objects[pid].callbacks == a.objects[pid].callbacks);
                            assert(a.objects[pid].callbacks.contains(y));
                            assert(consistent_wake_follows_callback_consumption_at(now, a, c, y, q));
                        }
                    }
                    None => {}
                }
            }
            None => {}
        }
    }
}

/// `task.fence`: a projection of the fencing task's object, then a legal
/// promise step on another id, is one legal step.
pub proof fn lemma_fence_legal(now: nat, a: AState, a1: AState, c: AState, x: Seq<char>, y: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(x),
        a1.objects == a.objects.insert(x, a.objects[x].project(now)),
        a1.schedules == a.schedules,
        a1.outbox == a.outbox,
        legal(now, a1, c),
        touches_only(a1, c, |z: Seq<char>| z == y),
        x != y,
    ensures
        legal(now, a, c),
{
    lemma_inv_pointwise(now, a);
    lemma_legal_pointwise(now, a1, c);
    assert forall|w: Seq<char>| #[trigger] a1.objects.contains_key(w) implies
        a.objects.contains_key(w) && a1.objects[w].callbacks == a.objects[w].callbacks by {}
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies a1.objects.contains_key(w) by {}
    assert forall|id: Seq<char>| #[trigger] trans_obj(now, a, c, id) by {
        if id == x {
            assert(a1.objects.contains_key(x));
            assert(a1.objects[x] == a.objects[x].project(now));
            assert(c.objects.contains_key(x));
            assert(c.objects[x] == a1.objects[x]);
            lemma_project_trans_obj(now, a, c, x);
        } else if id == y {
            assert(trans_obj(now, a1, c, y));
            assert(a.objects.contains_key(y) <==> a1.objects.contains_key(y));
            lemma_trans_obj_transfer(now, a, a1, c, y);
        } else {
            assert(a1.objects.contains_key(id) <==> c.objects.contains_key(id));
            assert(a.objects.contains_key(id) <==> c.objects.contains_key(id));
            lemma_trans_obj_unchanged(now, a, c, id);
        }
    }
    assert forall|k: OutboxKey| #[trigger] trans_out(now, a, c, k) by {
        lemma_trans_out_unchanged(now, a, c, k);
    }
    assert forall|id: Seq<char>| #[trigger] trans_sched(now, a, c, id) by {
        lemma_trans_sched_unchanged(now, a, c, id);
    }
    lemma_legal_pointwise(now, a, c);
}

} // verus!
