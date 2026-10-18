//! External steps: the request handlers.
//!
//! Each handler is `spec/02-abstract/external.lean`'s, under the
//! materialising reading (`mat = true`): a read projects the object at `now`
//! and persists what the projection moved. Every handler takes `now` and
//! the configuration, and ensures the whole catalogue: `inv` on the state it
//! leaves and `legal` on the pair.

use vstd::prelude::*;

use crate::object::*;
use crate::properties::*;
use crate::store::{AState, State};
use crate::tags::OType;
use crate::types::*;

verus! {

/// What every handler requires of its inputs.
pub open spec fn pre(s: State, now: u64, cfg: Config) -> bool {
    &&& s.wf()
    &&& inv(now as nat, s@)
    &&& now <= MAX_TIME
    &&& cfg.wf()
}

/// What every handler ensures of its outputs.
pub open spec fn post(a: State, b: State, now: u64) -> bool {
    &&& b.wf()
    &&& inv(now as nat, b@)
    &&& legal(now as nat, a@, b@)
}

/// The step wrote no object outside `ids`, and no schedule or outbox entry.
pub open spec fn touches_only(a: AState, b: AState, ids: spec_fn(Seq<char>) -> bool) -> bool {
    &&& forall|z: Seq<char>| !ids(z) ==>
        (a.objects.contains_key(z) <==> #[trigger] b.objects.contains_key(z))
        && (a.objects.contains_key(z) ==> a.objects[z] == b.objects[z])
    &&& b.schedules == a.schedules
    &&& b.outbox == a.outbox
}

impl State {
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
                    crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                }
                Some(i)
            }
        }
    }

    /// `promise.get`.
    pub fn promise_get(&mut self, req: &PromiseGetReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            match r.promise {
                None => r.status == 404 && !old(self)@.objects.contains_key(req.id@),
                Some(p) => r.status == 200 && old(self)@.objects.contains_key(req.id@)
                    && p@ == old(self)@.objects[req.id@].project(now as nat).to_record(),
            },
    {
        let ghost a = self@;
        match self.read_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
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
    pub fn promise_create(&mut self, req: &PromiseCreateReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            touches_only(old(self)@, final(self)@, |z: Seq<char>| z == req.id@),
            r.status == 200 || r.status == 400,
    {
        let ghost a = self@;
        if crate::tags::exec_timer_targeted(&req.tags) || req.timeout_at > MAX_TIME {
            proof { crate::frame::lemma_noop(now as nat, a); }
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
    pub fn promise_settle(&mut self, req: &PromiseSettleReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            touches_only(old(self)@, final(self)@, |z: Seq<char>| z == req.id@),
            r.status == 200 || r.status == 400 || r.status == 404,
    {
        let ghost a = self@;
        if !req.state.settable() {
            proof { crate::frame::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        match self.read_object(&req.id, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
                PromiseRes { status: 404, promise: None }
            }
            Some(i) => {
                if self.objects[i].state == PromiseState::Pending {
                    let ghost before = self.objects@;
                    self.objects[i].settle(req.state, req.value.dup(), now);
                    proof {
                        crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
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
    pub fn promise_register_callback(&mut self, req: &PromiseRegisterCallbackReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 400 || r.status == 404 || r.status == 422,
    {
        let ghost a = self@;
        if req.awaited == req.awaiter || !crate::ident::same_origin(&req.awaited, &req.awaiter) {
            proof { crate::frame::lemma_noop(now as nat, a); }
            return PromiseRes { status: 400, promise: None };
        }
        let i = match self.read_object(&req.awaited, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
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
                crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                assert(self@.objects =~= a.objects.insert(x, a.objects[x].add_callback(y)));
                lemma_add_callback_legal(now as nat, a, self@, x, y);
            }
        }
        let rec = self.objects[i].to_record();
        PromiseRes { status: 200, promise: Some(rec) }
    }

    /// `promise.listener`: register `address` to be told when `awaited` settles.
    pub fn promise_register_listener(&mut self, req: &PromiseRegisterListenerReq, now: u64, cfg: &Config) -> (r: PromiseRes)
        requires
            pre(*old(self), now, *cfg),
        ensures
            post(*old(self), *final(self), now),
            r.status == 200 || r.status == 404 || r.status == 422,
    {
        let ghost a = self@;
        let i = match self.read_object(&req.awaited, now) {
            None => {
                proof { crate::frame::lemma_noop(now as nat, a); }
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
                crate::store::lemma_fold_update(before, crate::store::obj_key(), crate::store::obj_val(), i as int, self.objects@[i as int]);
                assert(self@.objects =~= a.objects.insert(x, a.objects[x].add_listener(req.address@)));
                lemma_add_listener_legal(now as nat, a, self@, x, req.address@);
            }
        }
        let rec = self.objects[i].to_record();
        PromiseRes { status: 200, promise: Some(rec) }
    }
}

// ---------------------------------------------------------------------------
// Proofs
// ---------------------------------------------------------------------------

/// Projecting any set of objects at `now` is a legal step that keeps the invariant.
pub proof fn lemma_project_many(now: nat, a: AState, b: AState, ids: spec_fn(Seq<char>) -> bool)
    requires
        inv(now, a),
        forall|x: Seq<char>| #[trigger] ids(x) ==>
            a.objects.contains_key(x) && b.objects.contains_key(x) && b.objects[x] == a.objects[x].project(now),
        forall|x: Seq<char>| !ids(x) ==>
            (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
            && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]),
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
        } else {
            assert(b.objects.contains_key(w));
        }
    }
    assert forall|x: Seq<char>| #[trigger] ids(x) && b.objects.contains_key(x) implies inv_obj(now, b, x) by {
        lemma_project_inv_obj(now, a, b, x);
    }
    assert forall|x: Seq<char>| #[trigger] ids(x) implies trans_obj(now, a, b, x) by {
        lemma_project_trans_obj(now, a, b, x);
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, ids, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `promise.create` on a fresh id.
pub proof fn lemma_create_legal(now: nat, a: AState, b: AState, req: APromiseCreateReq)
    requires
        inv(now, a),
        !a.objects.contains_key(req.id),
        !crate::tags::timer_targeted(req.tags),
        req.timeout_at <= MAX_TIME as nat,
        b.objects == a.objects.insert(req.id, spec_create(req, now)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    let id = req.id;
    let q = spec_create(req, now);
    assert(b.objects[id] == q);
    assert(q.callbacks.len() == 0);
    assert(!q.callbacks.contains(id));
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `promise.settle` on a pending promise.
pub proof fn lemma_settle_legal(now: nat, a: AState, b: AState, id: Seq<char>, state: PromiseState, value: AValue)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].project(now).state == PromiseState::Pending,
        state.spec_settable(),
        b.objects == a.objects.insert(id, a.objects[id].project(now).settle(state, value, now)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    assert(p.state == PromiseState::Pending && p.timeout_at > now);
    assert(p.project(now) == p);
    let q = p.settle(state, value, now);
    assert(b.objects[id] == q);
    assert(q.callbacks == p.callbacks && q.listeners == p.listeners && q.tags == p.tags);
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
    }
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// A rung in `a` is a rung in `b` when no registered callback was lost.
pub proof fn lemma_rung_transfer(a: AState, b: AState, id: Seq<char>)
    requires
        some_callbacks_contain(a, id),
        forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
            && #[trigger] a.objects[w].callbacks.contains(z)
            ==> b.objects.contains_key(w) && b.objects[w].callbacks.contains(z),
    ensures
        some_callbacks_contain(b, id),
{
    let w = choose|w: Seq<char>| #[trigger] a.objects.contains_key(w) && a.objects[w].callbacks.contains(id);
    assert(b.objects.contains_key(w) && b.objects[w].callbacks.contains(id));
}

/// `promise.callback`: `awaited` and `awaiter` both pending, both read at `now`.
pub proof fn lemma_add_callback_legal(now: nat, a: AState, b: AState, awaited: Seq<char>, awaiter: Seq<char>)
    requires
        inv(now, a),
        awaited != awaiter,
        crate::ident::same_origin_spec(awaited, awaiter),
        a.objects.contains_key(awaited),
        a.objects.contains_key(awaiter),
        a.objects[awaited].project(now).state == PromiseState::Pending,
        a.objects[awaiter].project(now).state == PromiseState::Pending,
        a.objects[awaiter].otype() == OType::Runnable,
        a.objects[awaited].otype().awaitable(),
        b.objects == a.objects.insert(awaited, a.objects[awaited].add_callback(awaiter)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, awaited));
    assert(inv_obj(now, a, awaiter));
    let p = a.objects[awaited];
    let q = p.add_callback(awaiter);
    assert(b.objects[awaited] == q);
    assert(p.state == PromiseState::Pending);
    assert(b.objects[awaiter] == a.objects[awaiter]);
    // the new callback list
    if p.callbacks.contains(awaiter) {
        assert(q == p);
    } else {
        assert(q.callbacks == p.callbacks.push(awaiter));
        assert(q.callbacks[q.callbacks.len() - 1] == awaiter);
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
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {
        if !p.callbacks.contains(awaiter) {
            assert(q.callbacks[i] == p.callbacks[i]);
        }
    }
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable
        && crate::ident::same_origin_spec(q.callbacks[i], awaited) && q.callbacks[i] != awaited by {
        if i < p.callbacks.len() {
            assert(q.callbacks[i] == p.callbacks[i]);
            assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        } else {
            assert(q.callbacks[i] == awaiter);
        }
    }
    assert(!q.callbacks.contains(awaited));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {
        if w == awaited {
            let i = choose|i: int| 0 <= i < p.callbacks.len() && p.callbacks[i] == z;
            assert(q.callbacks.contains(p.callbacks[i]));
        }
    }
    match q.task {
        Some(t) => {
            if t.state == TaskState::Suspended && q.project_promise(now).state == PromiseState::Pending {
                assert(some_callbacks_contain(a, awaited));
                lemma_rung_transfer(a, b, awaited);
            }
        }
        None => {}
    }
    assert(inv_obj(now, b, awaited));
    assert(trans_obj(now, a, b, awaited));
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == awaited, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// `promise.listener`: `awaited` pending, read at `now`.
pub proof fn lemma_add_listener_legal(now: nat, a: AState, b: AState, awaited: Seq<char>, address: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(awaited),
        a.objects[awaited].project(now).state == PromiseState::Pending,
        a.objects[awaited].otype().awaitable(),
        b.objects == a.objects.insert(awaited, a.objects[awaited].add_listener(address)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, awaited));
    let p = a.objects[awaited];
    let q = p.add_listener(address);
    assert(b.objects[awaited] == q);
    assert(p.state == PromiseState::Pending);
    if p.listeners.contains(address) {
        assert(q == p);
    } else {
        assert(q.listeners == p.listeners.push(address));
        assert(no_dups(q.listeners)) by {
            assert forall|i: int, j: int| 0 <= i < q.listeners.len() && 0 <= j < q.listeners.len()
                && q.listeners[i] == q.listeners[j] implies i == j by {
                if i < p.listeners.len() && j < p.listeners.len() {
                } else if i < p.listeners.len() {
                    assert(p.listeners[i] == address);
                } else if j < p.listeners.len() {
                    assert(p.listeners[j] == address);
                }
            }
        }
    }
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {
        if !p.listeners.contains(address) {
            assert(q.listeners[i] == p.listeners[i]);
        }
    }
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    match q.task {
        Some(t) => {
            if t.state == TaskState::Suspended && q.project_promise(now).state == PromiseState::Pending {
                assert(some_callbacks_contain(a, awaited));
                lemma_rung_transfer(a, b, awaited);
            }
        }
        None => {}
    }
    assert(inv_obj(now, b, awaited));
    assert(trans_obj(now, a, b, awaited));
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == awaited, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// Projecting one object at `now` is a legal step that keeps the invariant.
pub proof fn lemma_project_legal(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects == a.objects.insert(id, a.objects[id].project(now)),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    let p = a.objects[id];
    let q = p.project(now);
    assert(b.objects[id] == q);
    assert(inv_obj(now, b, id)) by {
        lemma_project_inv_obj(now, a, b, id);
    }
    assert(trans_obj(now, a, b, id)) by {
        lemma_project_trans_obj(now, a, b, id);
    }
    crate::frame::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
}

/// The projected object obeys every `.state` entry.
pub proof fn lemma_project_inv_obj(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].project(now),
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].callbacks == a.objects[w].callbacks
            && b.objects[w].tags == a.objects[w].tags,
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
    }
    match q.task {
        Some(u) => {
            if u.state == TaskState::Suspended && q.project_promise(now).state == PromiseState::Pending {
                assert(p.project_promise(now).state == PromiseState::Pending);
                assert(some_callbacks_contain(a, id));
                let w = choose|w: Seq<char>| #[trigger] a.objects.contains_key(w) && a.objects[w].callbacks.contains(id);
                assert(b.objects[w].callbacks.contains(id));
                assert(some_callbacks_contain(b, id));
            }
        }
        None => {}
    }
}

/// Projection is a legal transition at its own id.
pub proof fn lemma_project_trans_obj(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].project(now),
    ensures
        trans_obj(now, a, b, id),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let q = b.objects[id];
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    match p.task {
        Some(t) => {
            assert forall|i: int| 0 <= i < t.resumes.len() implies t.resumes.contains(#[trigger] t.resumes[i]) by {}
        }
        None => {}
    }
}

} // verus!
