//! A request takes effect: the store machine sweeps, runs the kernel's
//! handler and sweeps again; the model runs its twin and drains. The handler
//! against its twin is one lemma per handler (`handlers.rs`); here is what
//! every one of them establishes (`h_ok`) and how that carries the relation
//! across the step.

use vstd::prelude::*;

use accordant::refinement::{end, lemma_end_add, lemma_legal_add, lemma_project_add, matches, shows};
use accordant::semantics::{before, effect, legal, project, req_of, schedule, start_all, step, Cfg, Config, Execution, ExternalOp, Lab, Label};
use accordant::{CallId, Event, Model, Sched};
use echod_kernel::external::spec_handle;
use echod_kernel::internal::{lease_due, retry_due};
use echod_kernel::properties::inv;
use echod_kernel::steps::{deadline_at, has_deadline, is_next, objects_deadline, strip};
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::collections::{spec_address_valid, spec_settable};
use resonate::spec::*;
use resonate::{Dispatch, Internal, Request, Resonate, Response};

use crate::drain::*;
use crate::frame::*;
use crate::handlers::*;
use crate::machine::*;
use crate::sweep::*;
use crate::sweep_proof::*;
use crate::theorem::*;
use crate::trans::leases_from_ttl;
use crate::translate::*;

verus! {

// ------------------------------------------------------ what a handler leaves

/// Ready to run once the model schedules it at `now`.
pub open spec fn work_ready(w: Sched<InternalV>, now: u64) -> bool {
    match w {
        Sched::Later(_) => true,
        Sched::Timer(t, _) => t <= now,
    }
}

pub open spec fn work_ids(w: Sched<InternalV>) -> Seq<Chars> {
    match req_of(w) {
        InternalV::On(ids) => ids,
        _ => Seq::empty(),
    }
}

pub open spec fn work_is_on(w: Sched<InternalV>) -> bool {
    req_of(w) matches InternalV::On(_)
}

/// The shape the drain wants of new work: `On` steps without duplicate ids,
/// timers on one id, laters on one or two whose first is settled in `b`.
pub open spec fn work_shape(b: AState, work: Seq<Sched<InternalV>>) -> bool {
    forall|i: int| 0 <= i < work.len() ==> {
        let ids = work_ids(#[trigger] work[i]);
        &&& work_is_on(work[i])
        &&& ids.no_duplicates()
        &&& (work[i] is Timer ==> ids.len() == 1)
        &&& (work[i] is Later ==> 1 <= ids.len() <= 2 && b.objects.contains_key(ids[0]) && b.objects[ids[0]].state != PromiseState::Pending)
    }
}

pub open spec fn work_covers(work: Seq<Sched<InternalV>>, now: u64, id: Chars) -> bool {
    exists|i: int| 0 <= i < work.len() && work_ready(#[trigger] work[i], now) && work_ids(work[i]).contains(id)
}

pub open spec fn work_covers2(work: Seq<Sched<InternalV>>, now: u64, x: Chars, w: Chars) -> bool {
    exists|i: int| 0 <= i < work.len() && work_ready(#[trigger] work[i], now) && work_ids(work[i]).contains(x) && work_ids(work[i]).contains(w)
}

pub open spec fn work_timer(work: Seq<Sched<InternalV>>, id: Chars, t: nat) -> bool {
    exists|i: int| 0 <= i < work.len() && #[trigger] work[i] == at_v(t as u64, id)
}

/// Everything due in `b` at `now` is covered by ready new work, and every
/// deadline ahead that `a` did not already owe has its timer among the new
/// work. (The relation keeps a timer for every deadline `a` owes.)
pub open spec fn covers(a: AState, b: AState, work: Seq<Sched<InternalV>>, now: u64) -> bool {
    let n = now as nat;
    &&& forall|id: Chars| pending_due(b, id, now) ==> work_covers(work, now, id)
    &&& forall|id: Chars| #[trigger] b.objects.contains_key(id) && lease_due(b.objects[id], n) ==> work_covers(work, now, id)
    &&& forall|id: Chars| #[trigger] b.objects.contains_key(id) && retry_due(b.objects[id], n) ==> work_covers(work, now, id)
    &&& forall|x: Chars, w: Chars| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && #[trigger] b.objects[x].callbacks.contains(w)
        ==> work_covers2(work, now, x, w)
    &&& forall|x: Chars| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && b.objects[x].listeners.len() > 0 ==> work_covers(work, now, x)
    &&& forall|id: Chars, t: nat| #[trigger] b.objects.contains_key(id) && #[trigger] mdeadline_at(b.objects[id], t) && t > now
        ==> (a.objects.contains_key(id) && mdeadline_at(a.objects[id], t)) || work_timer(work, id, t)
}

/// The state a handler runs on: the bucket swept at the clock, inside the
/// kernel's doors, as the relation keeps it.
pub open spec fn ready_state(a: AState, now: u64) -> bool {
    &&& now <= MAX_TIME
    &&& inv(now as nat, a)
    &&& swept(a, now as nat)
    &&& leases_from_ttl(a)
    &&& no_scope(a)
    &&& versions_bounded(a)
    &&& a.objects.dom().finite()
    &&& a.schedules == Map::<Seq<char>, ASchedule>::empty()
}

/// The handler commutes with the twin: the kernel's state `b` and answer
/// `resp` against the model's one outcome `o`, and `b` is a state the model
/// drains to the sweep of.
pub open spec fn h_ok(a: AState, b: AState, resp: ResponseV, o: OutV, now: u64) -> bool {
    &&& translate(b) == o.next
    &&& resp == o.resp
    &&& o.send == Seq::<DispatchV>::empty()
    &&& inv(now as nat, b)
    &&& leases_from_ttl(b)
    &&& no_scope(b)
    &&& versions_bounded(b)
    &&& b.objects.dom().finite()
    &&& b.schedules == a.schedules
    &&& work_shape(b, o.work)
    &&& covers(a, b, o.work, now)
}

/// One kernel request against the model's one outcome for `req`.
pub open spec fn h_one(cfg: Resonate, a: AState, req: RequestV, kreq: ARequest, now: u64) -> bool {
    let outs = ext(cfg, req, translate(a), now);
    let (b, r) = spec_handle(a, kreq, now as nat);
    &&& outs.len() == 1
    &&& h_ok(a, b, response_out(r), outs[0], now)
}

/// The two kernel requests of a detached create against the model's one
/// outcome: the create, then the fence's check on the swept result, which
/// changes nothing; the check's status decides the answer.
pub open spec fn h_two(cfg: Resonate, a: AState, req: RequestV, create: APromiseCreateReq, check: ATaskFenceCheckReq, now: u64, t: nat) -> bool {
    let n = now as nat;
    let outs = ext(cfg, req, translate(a), now);
    let (b, r1) = spec_handle(a, ARequest::PromiseCreate(create), n);
    let (c, r2) = spec_handle(sweep_fn(b, n, t), ARequest::TaskFenceCheck(check), n);
    let resp = match r2 {
        AResponse::Status(st) => if st.status != 200 { ResponseV::Status(st.status) } else { response_out(r1) },
        _ => response_out(r1),
    };
    &&& outs.len() == 1
    &&& c == sweep_fn(b, n, t)
    &&& h_ok(a, b, resp, outs[0], now)
}

// ------------------------------------------------------------ the handlers

/// A request the wire refuses, the model refuses with the same status and no
/// change: the doors the plan mirrors are the model's own first checks.
#[verifier::rlimit(30)]
pub proof fn lemma_refused(cfg: Resonate, a: AState, req: RequestV, now: u64, code: u16)
    requires
        request_bounded(req),
        plan(req) == Plan::Refuse(code),
    ensures
        ext(cfg, req, translate(a), now) == status_v(code, translate(a)),
{
    let s = translate(a);
    axiom_worker_valid();
    match req {
        RequestV::CreatePromise(c) => {
            assert(!delay_ok(c));
            assert(ext(cfg, req, s, now) == promise_create_v(c, s, now));
            assert(promise_create_v(c, s, now) == status_v(400, s));
        },
        RequestV::SettlePromise(st) => {
            assert(spec_settable(st.state) is None);
            assert(ext(cfg, req, s, now) == status_v(400, s));
        },
        RequestV::RegisterListener { awaited, address } => {
            assert(!spec_address_valid(address));
            assert(ext(cfg, req, s, now) == status_v(400, s));
        },
        RequestV::CreateTask { pid, ttl, action } => {
            assert(!action.tags.target || action.tags.delay is Some);
            assert(ext(cfg, req, s, now) == task_create_v(pid, ttl, action, s, now));
            assert(task_create_v(pid, ttl, action, s, now) == status_v(400, s));
        },
        RequestV::FulfillTask { id, version, state, data } => {
            assert(spec_settable(state) is None);
            assert(ext(cfg, req, s, now) == status_v(400, s));
        },
        RequestV::HeartbeatTask { pid, tasks } => {
            assert(!one_origin(tasks));
            assert(ext(cfg, req, s, now) == status_v(400, s));
        },
        RequestV::FenceTask { id, version, action } => {
            assert(ext(cfg, req, s, now) == fence_task_v(id, version, action, s, now));
            match action {
                FencedV::Create(c) => {
                    assert(!delay_ok(c));
                    assert(fence_task_v(id, version, action, s, now) == status_v(400, s));
                },
                FencedV::Settle(st) => {
                    assert(spec_settable(st.state) is Some);
                    assert(crate::translate::origin(st.id) != crate::translate::origin(id));
                    assert(fence_task_v(id, version, action, s, now) == status_v(400, s));
                },
            }
        },
        _ => {
            assert(false);
        },
    }
}

/// What the kernel does for a request, against the model: the plan's refusal
/// is the model's, and the plan's kernel request commutes with the twin.
#[verifier::rlimit(30)]
pub proof fn lemma_handled(cfg: Concrete, a: AState, req: RequestV, now: u64)
    requires
        dial_ok(cfg),
        ready_state(a, now),
        request_bounded(req),
    ensures
        ({
            let m = abstract_of(cfg);
            match plan(req) {
                Plan::Refuse(code) => ext(m, req, translate(a), now) == status_v(code, translate(a)),
                Plan::One(kreq) => h_one(m, a, req, kreq, now),
                Plan::Detached(create, check) => h_two(m, a, req, create, check, now, cfg.retry_timeout as nat),
            }
        }),
{
    let m = abstract_of(cfg);
    axiom_worker_valid();
    match req {
        RequestV::CreatePromise(c) => {
            if !delay_ok(c) {
                lemma_refused(m, a, req, now, 400);
            } else {
                h_promise_create(m, a, c, now);
            }
        },
        RequestV::GetPromise(id) => {
            h_promise_get(m, a, id, now);
        },
        RequestV::SettlePromise(st) => {
            match settle_in(st) {
                Some(q) => {
                    h_promise_settle(m, a, st, now);
                },
                None => {
                    lemma_refused(m, a, req, now, 400);
                },
            }
        },
        RequestV::RegisterCallback { awaited, awaiter } => {
            h_register_callback(m, a, awaited, awaiter, now);
        },
        RequestV::RegisterListener { awaited, address } => {
            if !spec_address_valid(address) {
                lemma_refused(m, a, req, now, 400);
            } else {
                h_register_listener(m, a, awaited, address, now);
            }
        },
        RequestV::GetTask(id) => {
            h_task_get(m, a, id, now);
        },
        RequestV::CreateTask { pid, ttl, action } => {
            if !action.tags.target || action.tags.delay is Some {
                lemma_refused(m, a, req, now, 400);
            } else {
                h_task_create(m, a, pid, ttl, action, now);
            }
        },
        RequestV::AcquireTask { id, version, pid, ttl } => {
            h_task_acquire(m, a, id, version, pid, ttl, now);
        },
        RequestV::ReleaseTask { id, version } => {
            h_task_release(m, a, id, version, now);
        },
        RequestV::FulfillTask { id, version, state, data } => {
            match settle_in(SettleV { id, state, data }) {
                Some(q) => {
                    h_task_fulfill(m, a, id, version, state, data, now);
                },
                None => {
                    lemma_refused(m, a, req, now, 400);
                },
            }
        },
        RequestV::HeartbeatTask { pid, tasks } => {
            if !one_origin(tasks) {
                lemma_refused(m, a, req, now, 400);
            } else {
                h_task_heartbeat(m, a, pid, tasks, now);
            }
        },
        RequestV::SuspendTask { id, version, awaited } => {
            h_task_suspend(m, a, id, version, awaited, now);
        },
        RequestV::FenceTask { id, version, action } => {
            match action {
                FencedV::Create(c) => {
                    if !delay_ok(c) {
                        lemma_refused(m, a, req, now, 400);
                    } else if crate::translate::origin(c.id) != crate::translate::origin(id) {
                        h_detached(m, a, id, version, c, now, cfg.retry_timeout as nat);
                    } else {
                        h_fence_create(m, a, id, version, c, now);
                    }
                },
                FencedV::Settle(st) => {
                    match settle_in(st) {
                        None => {
                            assert(false);
                        },
                        Some(q) => {
                            if crate::translate::origin(st.id) != crate::translate::origin(id) {
                                lemma_refused(m, a, req, now, 400);
                            } else {
                                h_fence_settle(m, a, id, version, st, now);
                            }
                        },
                    }
                },
            }
        },
        RequestV::HaltTask(id) => {
            h_task_halt(m, a, id, now);
        },
        RequestV::ContinueTask(id) => {
            h_task_continue(m, a, id, now);
        },
        RequestV::CreateSchedule(_) | RequestV::GetSchedule(_) | RequestV::DeleteSchedule(_) => {
            assert(false);
        },
    }
}

// ------------------------------------------------------------------ the step

/// The concrete effect step, unpacked: the one outcome of the call's request.
#[verifier::rlimit(30)]
pub proof fn lemma_effect_shape(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>)
    requires
        effect(cfg, x, l, y),
    ensures
        l is Silent,
        exists|call: CallId| #[trigger] x.externals.contains_key(call) && x.externals[call].res is None && {
            let o = cfg.request(x.externals[call].req@, x.state@, x.now);
            y == Config {
                state: o.next,
                externals: x.externals.insert(call, ExternalOp { req: x.externals[call].req, res: Some(o.resp) }),
                internals: start_all(x.internals, o.work, x.now),
                sent: x.sent + o.send,
                ..x
            }
        },
{
    let (call, j) = choose|call: CallId, j: int|
        #![trigger x.externals[call], cfg.spec_external(x.externals[call].req, x.state, x.now)[j]]
        x.externals.contains_key(call) && x.externals[call].res is None && {
            let outs = cfg.spec_external(x.externals[call].req, x.state, x.now);
            0 <= j < outs.len() && y == Config {
                state: outs[j].next,
                externals: x.externals.insert(call, ExternalOp { req: x.externals[call].req, res: Some(outs[j].resp) }),
                internals: start_all(x.internals, outs[j].work, x.now),
                sent: x.sent + outs[j].send,
                ..x
            }
        };
    let outs = cfg.spec_external(x.externals[call].req, x.state, x.now);
    assert(outs == seq![cfg.request(x.externals[call].req@, x.state@, x.now)]);
    assert(j == 0);
    assert(outs[0] == cfg.request(x.externals[call].req@, x.state@, x.now));
}

/// A model item, lifted and scheduled at `now`: what the drain reads of it.
#[verifier::rlimit(30)]
pub proof fn lemma_lifted_item(w: Sched<InternalV>, now: u64)
    requires
        work_is_on(w),
    ensures
        ({
            let it = schedule(now, lift_sched(w));
            &&& is_on(req_of(it))
            &&& item_ids(it) == work_ids(w)
            &&& (it is Timer) == (w is Timer)
            &&& ready_item(it, now) == work_ready(w, now)
            &&& (w is Timer && accordant::semantics::due(w).unwrap() > now ==> it == Sched::Timer(accordant::semantics::due(w).unwrap(), lift_internal(InternalV::On(work_ids(w)))))
        }),
{
    let ids = work_ids(w);
    axiom_realised(empty_server_v(), ResponseV::Status(0), InternalV::On(ids), DispatchV::Execute { id: Seq::empty(), version: 0 });
    match w {
        Sched::Later(r) => {
            assert(r == InternalV::On(ids));
        },
        Sched::Timer(t, r) => {
            assert(r == InternalV::On(ids));
        },
    }
}

/// The relation a drain keeps holds after the model's effect step, from the
/// kernel's post-handler state.
#[verifier::rlimit(30)]
pub proof fn lemma_drain_inv_after(cfg: Concrete, a: AState, b: AState, o: OutV, s: Cfg<Resonate>, s1: Cfg<Resonate>, resp: ResponseV)
    requires
        dial_ok(cfg),
        s.now <= MAX_TIME,
        a.schedules == Map::<Seq<char>, ASchedule>::empty(),
        timers_cover(s.internals, a, s.now),
        h_ok(a, b, resp, o, s.now),
        s1.now == s.now,
        s1.state@ == o.next,
        s1.internals == start_all(s.internals, o.work.map_values(|w: Sched<InternalV>| lift_sched(w)), s.now),
    ensures
        drain_inv(cfg, b, s1),
{
    let now = s.now;
    let n = now as nat;
    let k0 = s.internals.len() as int;
    let lifted = o.work.map_values(|w: Sched<InternalV>| lift_sched(w));
    let added = lifted.map_values(|w: Sched<Internal>| schedule(now, w));
    assert(s1.internals == s.internals + added);
    assert(s1.internals.len() == k0 + o.work.len());
    assert forall|i: int| 0 <= i < k0 implies s1.internals[i] == s.internals[i] by {}
    assert forall|k: int| 0 <= k < o.work.len() implies s1.internals[k0 + k] == schedule(now, lift_sched(#[trigger] o.work[k])) by {
        assert(added[k] == schedule(now, lifted[k]));
        assert(lifted[k] == lift_sched(o.work[k]));
    }
    // the shape
    assert(work_wf(b, s1.internals)) by {
        assert forall|i: int| 0 <= i < s1.internals.len() implies {
            let ids = item_ids(#[trigger] s1.internals[i]);
            &&& is_on(req_of(s1.internals[i]))
            &&& ids.no_duplicates()
            &&& (s1.internals[i] is Timer ==> ids.len() == 1)
            &&& (s1.internals[i] is Later ==> 1 <= ids.len() <= 2 && b.objects.contains_key(ids[0]) && b.objects[ids[0]].state != PromiseState::Pending)
        } by {
            if i < k0 {
                match s.internals[i] {
                    Sched::Timer(t, stp) => {
                        assert(item_ids(s.internals[i]) == on_ids(stp));
                    },
                    Sched::Later(_) => {
                        assert(false);
                    },
                }
            } else {
                let k = i - k0;
                let w = o.work[k];
                lemma_lifted_item(w, now);
            }
        }
    }
    // what is due is covered
    assert forall|id: Chars| pending_due(b, id, now) implies covered(s1.internals, now, id) by {
        let k = choose|k: int| 0 <= k < o.work.len() && work_ready(#[trigger] o.work[k], now) && work_ids(o.work[k]).contains(id);
        lemma_lifted_item(o.work[k], now);
        assert(ready_item(s1.internals[k0 + k], now) && item_ids(s1.internals[k0 + k]).contains(id));
    }
    assert forall|id: Chars| #[trigger] b.objects.contains_key(id) && lease_due(b.objects[id], n) implies covered(s1.internals, now, id) by {
        let k = choose|k: int| 0 <= k < o.work.len() && work_ready(#[trigger] o.work[k], now) && work_ids(o.work[k]).contains(id);
        lemma_lifted_item(o.work[k], now);
        assert(ready_item(s1.internals[k0 + k], now) && item_ids(s1.internals[k0 + k]).contains(id));
    }
    assert forall|id: Chars| #[trigger] b.objects.contains_key(id) && retry_due(b.objects[id], n) implies covered(s1.internals, now, id) by {
        let k = choose|k: int| 0 <= k < o.work.len() && work_ready(#[trigger] o.work[k], now) && work_ids(o.work[k]).contains(id);
        lemma_lifted_item(o.work[k], now);
        assert(ready_item(s1.internals[k0 + k], now) && item_ids(s1.internals[k0 + k]).contains(id));
    }
    assert forall|x: Chars, w: Chars| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && #[trigger] b.objects[x].callbacks.contains(w)
        implies covered2(s1.internals, now, x, w) by {
        let k = choose|k: int| 0 <= k < o.work.len() && work_ready(#[trigger] o.work[k], now) && work_ids(o.work[k]).contains(x) && work_ids(o.work[k]).contains(w);
        lemma_lifted_item(o.work[k], now);
        assert(ready_item(s1.internals[k0 + k], now) && item_ids(s1.internals[k0 + k]).contains(x) && item_ids(s1.internals[k0 + k]).contains(w));
    }
    assert forall|x: Chars| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && b.objects[x].listeners.len() > 0 implies covered(s1.internals, now, x) by {
        let k = choose|k: int| 0 <= k < o.work.len() && work_ready(#[trigger] o.work[k], now) && work_ids(o.work[k]).contains(x);
        lemma_lifted_item(o.work[k], now);
        assert(ready_item(s1.internals[k0 + k], now) && item_ids(s1.internals[k0 + k]).contains(x));
    }
    // every deadline ahead has its timer
    assert forall|id: Chars, t: nat| #[trigger] b.objects.contains_key(id) && #[trigger] mdeadline_at(b.objects[id], t) && t > now implies mdeadline_at_timer(s1.internals, id, t) by {
        if a.objects.contains_key(id) && mdeadline_at(a.objects[id], t) {
            let i = choose|i: int| 0 <= i < s.internals.len() && #[trigger] s.internals[i] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id])));
            assert(s1.internals[i] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id]))));
        } else {
            let k = choose|k: int| 0 <= k < o.work.len() && #[trigger] o.work[k] == at_v(t as u64, id);
            let w = o.work[k];
            assert(w == Sched::Timer(t as u64, InternalV::On(seq![id])));
            assert(work_is_on(w));
            lemma_lifted_item(w, now);
            assert(accordant::semantics::due(w) == Some(t as u64));
            assert(work_ids(w) == seq![id]);
            assert(s1.internals[k0 + k] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id]))));
        }
    }
}

/// The relation holds again at the end of the drain.
#[verifier::rlimit(30)]
pub proof fn lemma_rel_after(cfg: Concrete, x: Cfg<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>, s1: Cfg<Resonate>, t: Cfg<Resonate>, call: CallId, b: AState, o: OutV, resp: ResponseV, mid2: Execution<Resonate>, bn: AState)
    requires
        dial_ok(cfg),
        rel(cfg, x, s),
        x.externals.contains_key(call),
        ({
            let n = x.now as nat;
            let rt = cfg.retry_timeout as nat;
            let raw = raw_of(x);
            let a = sweep_fn(raw, n, rt);
            &&& h_ok(a, b, resp, o, x.now)
            &&& y.state == lift_store(fresh(sweep_fn(b, n, rt)))
            &&& y.externals == x.externals.insert(call, ExternalOp { req: x.externals[call].req, res: Some(lift_response(resp)) })
            &&& y.internals == start_all(x.internals, arm(sweep_fn(b, n, rt)), x.now)
            &&& y.sent.to_multiset() == (x.sent + lift_dispatches(sweep_sends(raw, n, rt)) + lift_dispatches(sweep_sends(b, n, rt))).to_multiset()
            &&& y.now == x.now
            &&& s1.now == s.now
            &&& s1.externals == s.externals.insert(call, ExternalOp { req: x.externals[call].req, res: Some(lift_response(o.resp)) })
            &&& s1.sent == s.sent + o.send.map_values(|d: DispatchV| lift_dispatch(d))
            &&& drained(cfg, b, s1, mid2, t, bn)
        }),
    ensures
        rel(cfg, y, t),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    let now = x.now;
    let n = now as nat;
    let rt = cfg.retry_timeout as nat;
    let raw = raw_of(x);
    let a = sweep_fn(raw, n, rt);
    let sb = sweep_fn(b, n, rt);
    axiom_store_realised(fresh(sb));
    let raw2 = raw_of(y);
    assert(raw2 == fresh(sb));
    assert(raw2.objects == sb.objects);
    // the state the sweep leaves is swept: sweeping it again is the identity
    lemma_sweep_swept(b, n, rt);
    assert(swept(sb, n));
    assert(swept(raw2, n));
    lemma_sweep_idem(raw2, n, rt);
    lemma_sends_idem(raw2, n, rt);
    let sw2 = sweep_fn(raw2, n, rt);
    assert(sw2 == raw2);
    assert(lift_dispatches(sweep_sends(raw2, n, rt)) =~= Seq::<Dispatch>::empty());
    assert(y.sent + lift_dispatches(sweep_sends(raw2, n, rt)) =~= y.sent);
    // the concrete side's invariants
    lemma_sweep_inv(b, n, rt);
    lemma_inv_fresh(n, sb);
    assert(inv(n, raw2));
    crate::tick::lemma_sweep_leases(b, n, rt);
    assert(leases_from_ttl(sb));
    assert(leases_from_ttl(raw2));
    lemma_sweep_shell(b, n, rt);
    lemma_shell_keeps(b, sb);
    assert(no_scope(raw2) && versions_bounded(raw2));
    assert(raw2.objects.dom() =~= b.objects.dom());
    assert(raw2.schedules == b.schedules);
    assert(a.schedules == raw.schedules) by {
        lemma_sweep_swept(raw, n, rt);
    }
    assert(sweep_armed(y)) by {
        match next_deadline(raw2) {
            Some(d) => {
                assert(strip(raw2) == strip(sb));
                assert(is_next(strip(sb), d));
                assert(has_deadline(strip(sb), d));
                assert(objects_deadline(sb.objects, d));
                let id = choose|id: Seq<char>| #[trigger] sb.objects.contains_key(id) && deadline_at(sb.objects[id], d);
                lemma_swept_ahead(sb, n);
                assert(d > now);
                assert(d <= u64::MAX);
                assert(arm(sb) == seq![Sched::Timer(d as u64, CStep::Sweep)]);
                let k = x.internals.len();
                assert(y.internals.len() == k + 1);
                assert(y.internals[k as int] == Sched::Timer(d as u64, CStep::Sweep));
                assert(timer_by(y.internals, d));
            },
            None => {},
        }
    }
    assert(calls_bounded(y.externals)) by {
        assert forall|k: CallId| #[trigger] y.externals.contains_key(k) implies request_bounded(y.externals[k].req@) by {
            if k != call {
                assert(x.externals.contains_key(k));
            }
        }
    }
    // the correspondence
    assert(t.now == y.now);
    assert(t.state@ == translate(bn));
    assert(bn.objects == sw2.objects);
    assert(translate(bn) == translate(sw2));
    assert(t.externals == y.externals);
    // the messages: one of each the drain sends more, on both sides
    assert(o.send.map_values(|d: DispatchV| lift_dispatch(d)) =~= Seq::<Dispatch>::empty());
    assert(s1.sent =~= s.sent);
    let extra = lift_dispatches(sweep_sends(b, n, rt)).to_multiset();
    assert(t.sent.to_multiset() == s.sent.to_multiset().add(extra));
    let before = (x.sent + lift_dispatches(sweep_sends(raw, n, rt))).to_multiset();
    assert(y.sent.to_multiset() == before.add(extra));
    assert(before.subset_of(s.sent.to_multiset()));
    assert((y.sent + lift_dispatches(sweep_sends(raw2, n, rt))).to_multiset().subset_of(t.sent.to_multiset())) by {
        assert forall|d: Dispatch| before.add(extra).count(d) <= s.sent.to_multiset().add(extra).count(d) by {}
    }
    assert(timers_cover(t.internals, sw2, y.now)) by {
        assert forall|id: Seq<char>, tt: nat| #[trigger] sw2.objects.contains_key(id) && #[trigger] mdeadline_at(sw2.objects[id], tt) implies mdeadline_at_timer(t.internals, id, tt) by {
            assert(bn.objects.contains_key(id) && mdeadline_at(bn.objects[id], tt));
        }
    }
    assert(rel(cfg, y, t));
}

/// A handled request: the model's effect step, then its drain, match the
/// concrete step.
#[verifier::rlimit(30)]
pub proof fn lemma_effect_handled(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>, call: CallId, b: AState, resp: ResponseV)
    requires
        dial_ok(cfg),
        rel(cfg, x, s),
        l is Silent,
        x.externals.contains_key(call),
        x.externals[call].res is None,
        ({
            let n = x.now as nat;
            let rt = cfg.retry_timeout as nat;
            let raw = raw_of(x);
            let a = sweep_fn(raw, n, rt);
            let outs = ext(abstract_of(cfg), x.externals[call].req@, translate(a), x.now);
            &&& outs.len() == 1
            &&& h_ok(a, b, resp, outs[0], x.now)
            &&& y.state == lift_store(fresh(sweep_fn(b, n, rt)))
            &&& y.externals == x.externals.insert(call, ExternalOp { req: x.externals[call].req, res: Some(lift_response(resp)) })
            &&& y.internals == start_all(x.internals, arm(sweep_fn(b, n, rt)), x.now)
            &&& y.sent.to_multiset() == (x.sent + lift_dispatches(sweep_sends(raw, n, rt)) + lift_dispatches(sweep_sends(b, n, rt))).to_multiset()
            &&& y.now == x.now
        }),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    let m = abstract_of(cfg);
    let now = x.now;
    let n = now as nat;
    let rt = cfg.retry_timeout as nat;
    let raw = raw_of(x);
    let a = sweep_fn(raw, n, rt);
    let req = x.externals[call].req;
    let outs = ext(m, req@, translate(a), now);
    let o = outs[0];
    // the model's effect step
    let s1 = Config {
        state: lift_server(o.next),
        externals: s.externals.insert(call, ExternalOp { req, res: Some(lift_response(o.resp)) }),
        internals: start_all(s.internals, o.work.map_values(|w: Sched<InternalV>| lift_sched(w)), now),
        sent: s.sent + o.send.map_values(|d: DispatchV| lift_dispatch(d)),
        ..s
    };
    no_overdue(cfg, x, s);
    let mouts = m.spec_external(req, s.state, now);
    assert(mouts == outs.map_values(|oo: OutV| lift_out(oo)));
    assert(mouts.len() == 1);
    assert(mouts[0] == lift_out(o));
    assert(effect(m, s, l, s1)) by {
        assert(s.externals.contains_key(call) && s.externals[call].res is None && {
            let outs2 = m.spec_external(s.externals[call].req, s.state, s.now);
            0 <= 0 < outs2.len() && s1 == Config {
                state: outs2[0].next,
                externals: s.externals.insert(call, ExternalOp { req: s.externals[call].req, res: Some(outs2[0].resp) }),
                internals: start_all(s.internals, outs2[0].work, s.now),
                sent: s.sent + outs2[0].send,
                ..s
            }
        });
    }
    axiom_realised(o.next, ResponseV::Status(0), InternalV::On(Seq::empty()), DispatchV::Execute { id: Seq::empty(), version: 0 });
    assert(s1.state@ == o.next);
    // the model drains
    lemma_sweep_swept(raw, n, rt);
    assert(a.schedules == raw.schedules);
    lemma_drain_inv_after(cfg, a, b, o, s, s1, resp);
    lemma_drain(cfg, b, s1);
    let (mid2, t, bn) = choose|mid2: Execution<Resonate>, t: Cfg<Resonate>, bn: AState| #[trigger] drained(cfg, b, s1, mid2, t, bn);
    // the step, then the drain, shows nothing
    let first: Execution<Resonate> = seq![(l, s1)];
    assert(legal(m, s, first)) by {
        assert forall|k: int| 0 <= k < first.len() implies #[trigger] step(m, before::<Resonate>(s, first, k), first[k].0, first[k].1) by {
            assert(k == 0);
            assert(before::<Resonate>(s, first, 0) == s);
        }
    }
    assert(end::<Resonate>(s, first) == s1);
    assert(project::<Resonate>(first) =~= shows(l)) by {
        assert(first.len() == 1);
        assert(first.last() == (l, s1));
        assert(first.drop_last() =~= Seq::<(Lab<Resonate>, Cfg<Resonate>)>::empty());
        assert(project::<Resonate>(first.drop_last()) =~= Seq::<Event<Request, Response, Dispatch>>::empty());
    }
    let mid = first + mid2;
    lemma_legal_add(m, s, first, mid2);
    lemma_project_add::<Resonate>(first, mid2);
    lemma_end_add::<Resonate>(s, first, mid2);
    assert(project::<Resonate>(mid) =~= shows(l));
    assert(matches(m, s, l, t));
    lemma_rel_after(cfg, x, y, s, s1, t, call, b, o, resp, mid2, bn);
}

/// A refused request: the model's effect step alone matches the concrete
/// step, and nothing moves.
#[verifier::rlimit(30)]
pub proof fn lemma_effect_refused(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>, call: CallId, code: u16)
    requires
        dial_ok(cfg),
        rel(cfg, x, s),
        l is Silent,
        x.externals.contains_key(call),
        x.externals[call].res is None,
        ({
            let n = x.now as nat;
            let rt = cfg.retry_timeout as nat;
            let raw = raw_of(x);
            let a = sweep_fn(raw, n, rt);
            &&& ext(abstract_of(cfg), x.externals[call].req@, translate(a), x.now) == status_v(code, translate(a))
            &&& y == Config {
                state: lift_store(raw),
                externals: x.externals.insert(call, ExternalOp { req: x.externals[call].req, res: Some(lift_response(ResponseV::Status(code))) }),
                internals: start_all(x.internals, arm(raw), x.now),
                sent: x.sent + lift_dispatches(Seq::empty()),
                ..x
            }
        }),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    let m = abstract_of(cfg);
    let now = x.now;
    let n = now as nat;
    let rt = cfg.retry_timeout as nat;
    let raw = raw_of(x);
    let a = sweep_fn(raw, n, rt);
    let req = x.externals[call].req;
    let o = OutV { resp: ResponseV::Status(code), next: translate(a), work: Seq::empty(), send: Seq::empty() };
    assert(ext(m, req@, translate(a), now) == seq![o]);
    let s1 = Config {
        state: lift_server(o.next),
        externals: s.externals.insert(call, ExternalOp { req, res: Some(lift_response(o.resp)) }),
        internals: start_all(s.internals, o.work.map_values(|w: Sched<InternalV>| lift_sched(w)), now),
        sent: s.sent + o.send.map_values(|d: DispatchV| lift_dispatch(d)),
        ..s
    };
    no_overdue(cfg, x, s);
    let mouts = m.spec_external(req, s.state, now);
    assert(mouts == seq![o].map_values(|oo: OutV| lift_out(oo)));
    assert(mouts.len() == 1);
    assert(mouts[0] == lift_out(o));
    assert(effect(m, s, l, s1)) by {
        assert(s.externals.contains_key(call) && s.externals[call].res is None && {
            let outs2 = m.spec_external(s.externals[call].req, s.state, s.now);
            0 <= 0 < outs2.len() && s1 == Config {
                state: outs2[0].next,
                externals: s.externals.insert(call, ExternalOp { req: s.externals[call].req, res: Some(outs2[0].resp) }),
                internals: start_all(s.internals, outs2[0].work, s.now),
                sent: s.sent + outs2[0].send,
                ..s
            }
        });
    }
    one_step(m, s, l, s1);
    // nothing moved on either side
    axiom_realised(o.next, ResponseV::Status(0), InternalV::On(Seq::empty()), DispatchV::Execute { id: Seq::empty(), version: 0 });
    assert(s1.state@ == translate(a));
    axiom_store_realised(raw);
    assert(y.state@ == raw);
    assert(raw_of(y) == raw);
    assert(s1.internals =~= s.internals);
    assert(s1.sent =~= s.sent);
    assert(y.sent =~= x.sent);
    assert(sweep_armed(y)) by {
        match next_deadline(raw) {
            Some(d) => {
                let i = choose|i: int| 0 <= i < x.internals.len() && match #[trigger] x.internals[i] {
                    Sched::Timer(u, _) => u as nat <= d,
                    Sched::Later(_) => false,
                };
                assert(y.internals[i] == x.internals[i]);
                assert(timer_by(y.internals, d));
            },
            None => {},
        }
    }
    assert(calls_bounded(y.externals)) by {
        assert forall|k: CallId| #[trigger] y.externals.contains_key(k) implies request_bounded(y.externals[k].req@) by {
            if k != call {
                assert(x.externals.contains_key(k));
            }
        }
    }
    assert(rel(cfg, y, s1));
}

/// The concrete step for a call, as `effect` leaves it.
pub open spec fn effect_step(cfg: Concrete, x: Cfg<Concrete>, y: Cfg<Concrete>, call: CallId) -> bool {
    let o = cfg.request(x.externals[call].req@, x.state@, x.now);
    y == Config {
        state: o.next,
        externals: x.externals.insert(call, ExternalOp { req: x.externals[call].req, res: Some(o.resp) }),
        internals: start_all(x.internals, o.work, x.now),
        sent: x.sent + o.send,
        ..x
    }
}

/// The plan passes one kernel request on: the handler's lemma, then the step.
#[verifier::rlimit(30)]
pub proof fn lemma_effect_one(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>, call: CallId, kreq: ARequest)
    requires
        dial_ok(cfg),
        rel(cfg, x, s),
        l is Silent,
        x.externals.contains_key(call),
        x.externals[call].res is None,
        effect_step(cfg, x, y, call),
        plan(x.externals[call].req@) == Plan::One(kreq),
        h_one(abstract_of(cfg), sweep_fn(raw_of(x), x.now as nat, cfg.retry_timeout as nat), x.externals[call].req@, kreq, x.now),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    let now = x.now;
    let n = now as nat;
    let rt = cfg.retry_timeout as nat;
    let raw = raw_of(x);
    let a = sweep_fn(raw, n, rt);
    let req = x.externals[call].req@;
    let o = cfg.request(req, x.state@, now);
    assert(fresh(x.state@) == raw);
    let (b, r) = spec_handle(a, kreq, n);
    assert(o == outcome(sweep_fn(b, n, rt), response_out(r), sweep_sends(raw, n, rt) + sweep_sends(b, n, rt)));
    assert(y.sent == x.sent + lift_dispatches(sweep_sends(raw, n, rt) + sweep_sends(b, n, rt)));
    assert(lift_dispatches(sweep_sends(raw, n, rt) + sweep_sends(b, n, rt)) =~= lift_dispatches(sweep_sends(raw, n, rt)) + lift_dispatches(sweep_sends(b, n, rt)));
    assert(y.sent =~= x.sent + lift_dispatches(sweep_sends(raw, n, rt)) + lift_dispatches(sweep_sends(b, n, rt)));
    lemma_effect_handled(cfg, x, l, y, s, call, b, response_out(r));
}

/// The plan passes a create and then the fence's check on: the check moves
/// nothing and decides the answer; the create's lemma, then the step.
#[verifier::rlimit(30)]
pub proof fn lemma_effect_detached(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>, call: CallId, create: APromiseCreateReq, check: ATaskFenceCheckReq)
    requires
        dial_ok(cfg),
        rel(cfg, x, s),
        l is Silent,
        x.externals.contains_key(call),
        x.externals[call].res is None,
        effect_step(cfg, x, y, call),
        plan(x.externals[call].req@) == Plan::Detached(create, check),
        h_two(abstract_of(cfg), sweep_fn(raw_of(x), x.now as nat, cfg.retry_timeout as nat), x.externals[call].req@, create, check, x.now, cfg.retry_timeout as nat),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    let now = x.now;
    let n = now as nat;
    let rt = cfg.retry_timeout as nat;
    let raw = raw_of(x);
    let a = sweep_fn(raw, n, rt);
    let req = x.externals[call].req@;
    let o = cfg.request(req, x.state@, now);
    assert(fresh(x.state@) == raw);
    let (b, r1) = spec_handle(a, ARequest::PromiseCreate(create), n);
    let sb = sweep_fn(b, n, rt);
    let (c, r2) = spec_handle(sb, ARequest::TaskFenceCheck(check), n);
    let resp = match r2 {
        AResponse::Status(st) => if st.status != 200 { ResponseV::Status(st.status) } else { response_out(r1) },
        _ => response_out(r1),
    };
    assert(c == sb);
    assert(o == outcome(sweep_fn(c, n, rt), resp, sweep_sends(raw, n, rt) + sweep_sends(b, n, rt) + sweep_sends(c, n, rt)));
    lemma_sweep_swept(b, n, rt);
    lemma_sweep_idem(sb, n, rt);
    lemma_sends_idem(sb, n, rt);
    assert(sweep_fn(c, n, rt) == sb);
    assert(sweep_sends(c, n, rt) == Seq::<DispatchV>::empty());
    assert(sweep_sends(raw, n, rt) + sweep_sends(b, n, rt) + sweep_sends(c, n, rt) =~= sweep_sends(raw, n, rt) + sweep_sends(b, n, rt));
    assert(y.sent == x.sent + lift_dispatches(sweep_sends(raw, n, rt) + sweep_sends(b, n, rt)));
    assert(lift_dispatches(sweep_sends(raw, n, rt) + sweep_sends(b, n, rt)) =~= lift_dispatches(sweep_sends(raw, n, rt)) + lift_dispatches(sweep_sends(b, n, rt)));
    assert(y.sent =~= x.sent + lift_dispatches(sweep_sends(raw, n, rt)) + lift_dispatches(sweep_sends(b, n, rt)));
    lemma_effect_handled(cfg, x, l, y, s, call, b, resp);
}

/// The plan refuses: the step moves nothing.
#[verifier::rlimit(30)]
pub proof fn lemma_effect_refuse(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>, call: CallId, code: u16)
    requires
        dial_ok(cfg),
        rel(cfg, x, s),
        l is Silent,
        x.externals.contains_key(call),
        x.externals[call].res is None,
        effect_step(cfg, x, y, call),
        plan(x.externals[call].req@) == Plan::Refuse(code),
        ext(abstract_of(cfg), x.externals[call].req@, translate(sweep_fn(raw_of(x), x.now as nat, cfg.retry_timeout as nat)), x.now)
            == status_v(code, translate(sweep_fn(raw_of(x), x.now as nat, cfg.retry_timeout as nat))),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    let now = x.now;
    let raw = raw_of(x);
    let req = x.externals[call].req@;
    let o = cfg.request(req, x.state@, now);
    assert(fresh(x.state@) == raw);
    assert(o == outcome(raw, ResponseV::Status(code), Seq::empty()));
    assert(fresh(raw) == raw);
    lemma_effect_refused(cfg, x, l, y, s, call, code);
}

/// A request takes effect: refused, handled, or handled twice (a detached
/// create), the model's step and drain match.
#[verifier::rlimit(30)]
pub proof fn effect_matched(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        dial_ok(cfg),
        rel(cfg, x, s),
        effect(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    lemma_effect_shape(cfg, x, l, y);
    let call = choose|call: CallId| #[trigger] x.externals.contains_key(call) && x.externals[call].res is None && {
        let o = cfg.request(x.externals[call].req@, x.state@, x.now);
        y == Config {
            state: o.next,
            externals: x.externals.insert(call, ExternalOp { req: x.externals[call].req, res: Some(o.resp) }),
            internals: start_all(x.internals, o.work, x.now),
            sent: x.sent + o.send,
            ..x
        }
    };
    assert(effect_step(cfg, x, y, call));
    let now = x.now;
    let n = now as nat;
    let rt = cfg.retry_timeout as nat;
    let raw = raw_of(x);
    let a = sweep_fn(raw, n, rt);
    let req = x.externals[call].req@;
    assert(request_bounded(req));
    // the swept bucket is a state a handler runs on
    assert(ready_state(a, now)) by {
        lemma_sweep_inv(raw, n, rt);
        lemma_sweep_swept(raw, n, rt);
        crate::tick::lemma_sweep_leases(raw, n, rt);
        lemma_sweep_shell(raw, n, rt);
        lemma_shell_keeps(raw, a);
    }
    lemma_handled(cfg, a, req, now);
    match plan(req) {
        Plan::Refuse(code) => {
            lemma_effect_refuse(cfg, x, l, y, s, call, code);
        },
        Plan::One(kreq) => {
            lemma_effect_one(cfg, x, l, y, s, call, kreq);
        },
        Plan::Detached(create, check) => {
            lemma_effect_detached(cfg, x, l, y, s, call, create, check);
        },
    }
}

} // verus!
