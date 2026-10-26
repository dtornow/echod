//! One lemma per handler: the kernel's `spec_*` on a swept bucket, against
//! the model's twin on the translated state (`h_one`, `h_two`).

use vstd::prelude::*;

use echod_kernel::external::*;
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::collections::{spec_address_valid, spec_settable};
use resonate::twins::*;
use resonate::{PState, Resonate, TState};

use echod_kernel::external_proof::*;
use accordant::Sched;
use echod_kernel::internal::{lease_due, retry_due};
use echod_kernel::tags::OType;
use echod_kernel::properties::inv;
use echod_kernel::steps::{lease_deadline, retry_deadline};

use crate::effect::*;
use crate::hcommon::*;
use crate::tagsv::*;
use crate::sweep::mdeadline_at;
use crate::theorem::*;
use crate::trans::{lemma_prec, lemma_translate_insert, lemma_translate_reads};
use crate::translate::*;

verus! {

pub proof fn h_promise_get(cfg: Resonate, a: AState, id: Chars, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::GetPromise(id)),
    ensures
        h_one(cfg, a, RequestV::GetPromise(id), ARequest::PromiseGet(APromiseGetReq { id }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::GetPromise(id);
    let kreq = ARequest::PromiseGet(APromiseGetReq { id });
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    if a.objects.contains_key(id) {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let r = AResponse::Promise(APromiseRes { status: 200, promise: Some(p.to_record()) });
        assert(spec_handle(a, kreq, n) == (a, r));
        lemma_prec(p);
        assert(response_out(r) == ResponseV::Promise(prec_v(id, promise_v(p))));
        assert(ext(cfg, req, s, now) == echo_v(ResponseV::Promise(prec_v(id, s.promises[id])), s));
        lemma_h_noop(a, ResponseV::Promise(prec_v(id, promise_v(p))), now);
    } else {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 404, promise: None })));
        assert(ext(cfg, req, s, now) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    }
}

pub proof fn h_promise_create(cfg: Resonate, a: AState, c: CreateV, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::CreatePromise(c)),
        delay_ok(c),
    ensures
        h_one(cfg, a, RequestV::CreatePromise(c), ARequest::PromiseCreate(create_in(c)), now),
{
    let n = now as nat;
    let s = translate(a);
    let id = c.id;
    let req = RequestV::CreatePromise(c);
    let q0 = create_in(c);
    let kreq = ARequest::PromiseCreate(q0);
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    lemma_tags_in_kind(c.tags, n);
    lemma_tags_roundtrip(c.tags);
    lemma_empty_to_set();
    assert(ext(cfg, req, s, now) == promise_create_v(c, s, now));
    assert(!echod_kernel::tags::timer_targeted(q0.tags) && q0.timeout_at <= MAX_TIME);
    if a.objects.contains_key(id) {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        lemma_prec(p);
        let res = ResponseV::Promise(prec_v(id, promise_v(p)));
        assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 200, promise: Some(p.to_record()) })));
        assert(promise_create_v(c, s, now) == echo_v(res, s));
        lemma_h_noop(a, res, now);
    } else {
        let p = echod_kernel::object::spec_create(q0, n);
        let b = with_objects(a, a.objects.insert(id, p));
        assert(spec_handle(a, kreq, n) == (b, AResponse::Promise(APromiseRes { status: 200, promise: Some(p.to_record()) })));
        lemma_spec_promise_create(n, a, q0);
        assert(inv(n, b));
        let live = c.timeout_at > now;
        let born = if live { PState::Pending } else if c.tags.timer { PState::Resolved } else { PState::TimedOut };
        let pv = PromiseV {
            state: born,
            value: None,
            param: c.data,
            timeout_at: c.timeout_at,
            created_at: if live { now } else { c.timeout_at },
            settled_at: if live { None } else { Some(c.timeout_at) },
            tags: c.tags,
            callbacks: Set::empty(),
            listeners: Set::empty(),
        };
        assert(promise_v(p) == pv);
        lemma_prec(p);
        let res = ResponseV::Promise(prec_v(id, pv));
        assert(response_out(AResponse::Promise(APromiseRes { status: 200, promise: Some(p.to_record()) })) == res);
        lemma_translate_insert(a, id, p);
        let promises = s.promises.insert(id, pv);
        let work0: Seq<Sched<InternalV>> = if live { seq![at_v(c.timeout_at, id)] } else { Seq::empty() };
        let runnable = echod_kernel::tags::otype(q0.tags) == OType::Runnable;
        assert(runnable == c.tags.target);
        if c.tags.target {
            let due = match c.tags.delay {
                Some(d) => if d > now { d } else { now },
                None => now,
            };
            let task = TaskV {
                state: if live { TState::Pending } else { TState::Fulfilled },
                version: 0,
                pid: None,
                ttl: None,
                acquired_at: 0,
                retry_at: if live { Some(due) } else { None },
                resumes: Seq::empty(),
            };
            assert(p.task is Some);
            assert(task_v(p.task.unwrap()) == task);
            let next = ServerV { promises, tasks: s.tasks.insert(id, task), ..s };
            assert(translate(b) == next);
            let work = if live { work0.push(at_v(due, id)) } else { work0 };
            assert(promise_create_v(c, s, now) == one_v(res, next, work, Seq::empty()));
            let o = OutV { resp: res, next, work, send: Seq::empty() };
            if live {
                assert(work[0] == at_v(c.timeout_at, id));
                assert(work[1] == at_v(due, id));
                assert(work_shape(b, work)) by {
                    assert forall|k: int| 0 <= k < work.len() implies work_ids(#[trigger] work[k]) == seq![id] && work[k] is Timer && work_is_on(work[k]) by {}
                    assert(seq![id].no_duplicates());
                }
                assert(retry_due(p, n) ==> work_covers(work, now, id)) by {
                    if retry_due(p, n) {
                        assert(due <= now);
                        assert(work_ready(work[1], now));
                        assert(work_ids(work[1]) == seq![id]);
                        assert(seq![id][0] == id);
                    }
                }
                assert forall|tt: nat| #[trigger] mdeadline_at(p, tt) && tt > now implies work_timer(work, id, tt) by {
                    assert(lease_deadline(p) is None);
                    if p.timeout_at as nat == tt {
                        assert(work[0] == at_v(tt as u64, id));
                    } else {
                        assert(retry_deadline(p) == Some(tt));
                        assert(tt == due as nat);
                        assert(work[1] == at_v(tt as u64, id));
                    }
                }
                lemma_h_new_object(a, b, id, p, res, o, now);
            } else {
                assert(work == Seq::<Sched<InternalV>>::empty());
                assert forall|tt: nat| #[trigger] mdeadline_at(p, tt) && tt > now implies false by {
                    assert(lease_deadline(p) is None);
                    assert(retry_deadline(p) is None);
                }
                lemma_h_new_object(a, b, id, p, res, o, now);
            }
        } else {
            assert(p.task is None);
            assert(s.tasks.remove(id) =~= s.tasks);
            let next = ServerV { promises, ..s };
            assert(translate(b) == next);
            assert(promise_create_v(c, s, now) == one_v(res, next, work0, Seq::empty()));
            let o = OutV { resp: res, next, work: work0, send: Seq::empty() };
            if live {
                assert(work0[0] == at_v(c.timeout_at, id));
                assert(work_shape(b, work0)) by {
                    assert(work_ids(work0[0]) == seq![id]);
                    assert(seq![id].no_duplicates());
                }
            }
            assert forall|tt: nat| #[trigger] mdeadline_at(p, tt) && tt > now implies work_timer(work0, id, tt) by {
                assert(lease_deadline(p) is None);
                assert(retry_deadline(p) is None);
                assert(p.timeout_at as nat == tt && live);
                assert(work0[0] == at_v(tt as u64, id));
            }
            lemma_h_new_object(a, b, id, p, res, o, now);
        }
    }
}

pub proof fn h_promise_settle(cfg: Resonate, a: AState, st: SettleV, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::SettlePromise(st)),
        settle_in(st) is Some,
    ensures
        h_one(cfg, a, RequestV::SettlePromise(st), ARequest::PromiseSettle(settle_in(st).unwrap()), now),
{
    let n = now as nat;
    let s = translate(a);
    let id = st.id;
    let req = RequestV::SettlePromise(st);
    let state = spec_settable(st.state).unwrap();
    let q0 = settle_in(st).unwrap();
    assert(q0 == APromiseSettleReq { id, state: pstate_in(state), value: value_in(st.data) });
    let kreq = ARequest::PromiseSettle(q0);
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    lemma_pstate_roundtrip(state);
    assert(ext(cfg, req, s, now) == promise_settle_v(st, s, now));
    if !a.objects.contains_key(id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 404, promise: None })));
        assert(promise_settle_v(st, s, now) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        lemma_live(p);
        lemma_prec(p);
        if p.state == PromiseState::Pending {
            let q = p.settle(pstate_in(state), value_in(st.data), n);
            let b = with_objects(a, a.objects.insert(id, q));
            assert(spec_handle(a, kreq, n) == (b, AResponse::Promise(APromiseRes { status: 200, promise: Some(q.to_record()) })));
            lemma_spec_promise_settle(n, a, q0);
            assert(inv(n, b));
            lemma_settle_one(a, id, state, st.data, now);
            let sv = settle_v(s, id, state, st.data, now);
            assert(promise_settle_v(st, s, now) == one_v(ResponseV::Promise(prec_v(id, sv.promises[id])), sv, settled_work_v(promise_v(p), id), Seq::empty()));
        } else {
            let res = ResponseV::Promise(prec_v(id, promise_v(p)));
            assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 200, promise: Some(p.to_record()) })));
            assert(promise_settle_v(st, s, now) == echo_v(res, s));
            lemma_h_noop(a, res, now);
        }
    }
}

pub proof fn h_register_callback(cfg: Resonate, a: AState, awaited: Chars, awaiter: Chars, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::RegisterCallback { awaited, awaiter }),
    ensures
        h_one(cfg, a, RequestV::RegisterCallback { awaited, awaiter }, ARequest::PromiseRegisterCallback(APromiseRegisterCallbackReq { awaited, awaiter }), now),
{
    let n = now as nat;
    let s = translate(a);
    let x = awaited;
    let y = awaiter;
    let req = RequestV::RegisterCallback { awaited, awaiter };
    let q0 = APromiseRegisterCallbackReq { awaited, awaiter };
    let kreq = ARequest::PromiseRegisterCallback(q0);
    lemma_swept_read(a, x, now);
    lemma_swept_read(a, y, now);
    lemma_translate_reads(a, x);
    lemma_translate_reads(a, y);
    axiom_origin(x);
    axiom_origin(y);
    assert(ext(cfg, req, s, now) == register_callback_v(x, y, s));
    if x == y || !echod_kernel::types::same_origin_spec(x, y) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 400, promise: None })));
        assert(register_callback_v(x, y, s) == status_v(400, s));
        lemma_h_noop(a, ResponseV::Status(400), now);
    } else if !a.objects.contains_key(x) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 404, promise: None })));
        assert(register_callback_v(x, y, s) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else if !a.objects.contains_key(y) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 422, promise: None })));
        assert(register_callback_v(x, y, s) == status_v(422, s));
        lemma_h_noop(a, ResponseV::Status(422), now);
    } else {
        lemma_object_facts(a, x, now);
        lemma_object_facts(a, y, now);
        let p = a.objects[x];
        let w = a.objects[y];
        lemma_external(p);
        lemma_live(p);
        lemma_live(w);
        lemma_prec(p);
        assert((w.task is Some) == (w.otype() == OType::Runnable));
        let res = ResponseV::Promise(prec_v(x, promise_v(p)));
        if w.otype() != OType::Runnable || !p.otype().awaitable() {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 422, promise: None })));
            assert(register_callback_v(x, y, s) == status_v(422, s));
            lemma_h_noop(a, ResponseV::Status(422), now);
        } else if p.state == PromiseState::Pending && w.state == PromiseState::Pending {
            let q = p.add_callback(y);
            let b = with_objects(a, a.objects.insert(x, q));
            assert(spec_handle(a, kreq, n) == (b, AResponse::Promise(APromiseRes { status: 200, promise: Some(q.to_record()) })));
            assert(q.to_record() == p.to_record());
            lemma_spec_promise_register_callback(n, a, q0);
            assert(inv(n, b));
            lemma_add_callback_v(p, y);
            lemma_translate_insert(a, x, q);
            let qv = PromiseV { callbacks: promise_v(p).callbacks.insert(y), ..promise_v(p) };
            let next = ServerV { promises: s.promises.insert(x, qv), ..s };
            assert(translate(b).tasks == s.tasks) by {
                match q.task {
                    Some(t) => { assert(s.tasks.insert(x, task_v(t)) =~= s.tasks); },
                    None => { assert(s.tasks.remove(x) =~= s.tasks); },
                }
            }
            assert(translate(b) == next);
            assert(register_callback_v(x, y, s) == one_v(res, next, Seq::empty(), Seq::empty()));
            let o = OutV { resp: res, next, work: Seq::empty(), send: Seq::empty() };
            assert forall|tt: nat| #[trigger] mdeadline_at(q, tt) && tt > now implies mdeadline_at(p, tt) by {}
            lemma_h_one_object(a, b, x, q, res, o, now);
        } else {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 200, promise: Some(p.to_record()) })));
            assert(register_callback_v(x, y, s) == echo_v(res, s));
            lemma_h_noop(a, res, now);
        }
    }
}

pub proof fn h_register_listener(cfg: Resonate, a: AState, awaited: Chars, address: Chars, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::RegisterListener { awaited, address }),
        spec_address_valid(address),
    ensures
        h_one(cfg, a, RequestV::RegisterListener { awaited, address }, ARequest::PromiseRegisterListener(APromiseRegisterListenerReq { awaited, address }), now),
{
    let n = now as nat;
    let s = translate(a);
    let x = awaited;
    let req = RequestV::RegisterListener { awaited, address };
    let q0 = APromiseRegisterListenerReq { awaited, address };
    let kreq = ARequest::PromiseRegisterListener(q0);
    lemma_swept_read(a, x, now);
    lemma_translate_reads(a, x);
    assert(ext(cfg, req, s, now) == register_listener_v(x, address, s));
    if !a.objects.contains_key(x) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 404, promise: None })));
        assert(register_listener_v(x, address, s) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, x, now);
        let p = a.objects[x];
        lemma_external(p);
        lemma_live(p);
        lemma_prec(p);
        let res = ResponseV::Promise(prec_v(x, promise_v(p)));
        if !p.otype().awaitable() {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 422, promise: None })));
            assert(register_listener_v(x, address, s) == status_v(422, s));
            lemma_h_noop(a, ResponseV::Status(422), now);
        } else if p.state == PromiseState::Pending {
            let q = p.add_listener(address);
            let b = with_objects(a, a.objects.insert(x, q));
            assert(spec_handle(a, kreq, n) == (b, AResponse::Promise(APromiseRes { status: 200, promise: Some(q.to_record()) })));
            assert(q.to_record() == p.to_record());
            lemma_spec_promise_register_listener(n, a, q0);
            assert(inv(n, b));
            lemma_add_listener_v(p, address);
            lemma_translate_insert(a, x, q);
            let qv = PromiseV { listeners: promise_v(p).listeners.insert(address), ..promise_v(p) };
            let next = ServerV { promises: s.promises.insert(x, qv), ..s };
            assert(translate(b).tasks == s.tasks) by {
                match q.task {
                    Some(t) => { assert(s.tasks.insert(x, task_v(t)) =~= s.tasks); },
                    None => { assert(s.tasks.remove(x) =~= s.tasks); },
                }
            }
            assert(translate(b) == next);
            assert(register_listener_v(x, address, s) == one_v(res, next, Seq::empty(), Seq::empty()));
            let o = OutV { resp: res, next, work: Seq::empty(), send: Seq::empty() };
            assert forall|tt: nat| #[trigger] mdeadline_at(q, tt) && tt > now implies mdeadline_at(p, tt) by {}
            lemma_h_one_object(a, b, x, q, res, o, now);
        } else {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 200, promise: Some(p.to_record()) })));
            assert(register_listener_v(x, address, s) == echo_v(res, s));
            lemma_h_noop(a, res, now);
        }
    }
}

pub proof fn h_task_get(cfg: Resonate, a: AState, id: Chars, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::GetTask(id)),
    ensures
        h_one(cfg, a, RequestV::GetTask(id), ARequest::TaskGet(ATaskGetReq { id }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::GetTask(id);
    let kreq = ARequest::TaskGet(ATaskGetReq { id });
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    if a.has_task(id) {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let t = p.task.unwrap();
        let r = AResponse::TaskGet(ATaskGetRes { status: 200, task: Some(t.to_record(id)) });
        assert(spec_handle(a, kreq, n) == (a, r));
        lemma_trec(t, id);
        assert(response_out(r) == ResponseV::Task(trec_v(id, task_v(t))));
        assert(s.tasks.contains_key(id));
        assert(ext(cfg, req, s, now) == echo_v(ResponseV::Task(trec_v(id, s.tasks[id])), s));
        lemma_h_noop(a, ResponseV::Task(trec_v(id, task_v(t))), now);
    } else {
        assert(spec_handle(a, kreq, n) == (a, AResponse::TaskGet(ATaskGetRes { status: 404, task: None })));
        assert(!s.tasks.contains_key(id));
        assert(ext(cfg, req, s, now) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    }
}

pub proof fn h_task_create(cfg: Resonate, a: AState, pid: Chars, ttl: u64, action: CreateV, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::CreateTask { pid, ttl, action }),
        action.tags.target,
        action.tags.delay is None,
    ensures
        h_one(cfg, a, RequestV::CreateTask { pid, ttl, action }, ARequest::TaskCreate(ATaskCreateReq { pid, ttl, action: create_in(action) }), now),
{
    let n = now as nat;
    let s = translate(a);
    let c = action;
    let id = c.id;
    let req = RequestV::CreateTask { pid, ttl, action };
    let act = create_in(c);
    let q0 = ATaskCreateReq { pid, ttl, action: act };
    let kreq = ARequest::TaskCreate(q0);
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    lemma_tags_in_kind(c.tags, n);
    lemma_tags_roundtrip(c.tags);
    lemma_empty_to_set();
    assert(!c.tags.timer);
    assert(echod_kernel::tags::otype(act.tags) == OType::Runnable);
    assert(ttl >= 1 && ttl <= MAX_TIME && c.timeout_at <= MAX_TIME);
    assert(ext(cfg, req, s, now) == task_create_v(pid, ttl, c, s, now));
    if a.objects.contains_key(id) {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        lemma_external(p);
        lemma_live(p);
        lemma_prec(p);
        assert(s.promises[id] == promise_v(p));
        if p.otype() != OType::Runnable {
            assert(spec_handle(a, kreq, n) == (a, AResponse::TaskClaim(claim_err(422))));
            assert(task_create_v(pid, ttl, c, s, now) == status_v(422, s));
            lemma_h_noop(a, ResponseV::Status(422), now);
        } else {
            assert(p.task is Some);
            let t = p.task.unwrap();
            assert(s.tasks.contains_key(id) && s.tasks[id] == task_v(t));
            assert((t.version >= echod_kernel::types::MAX_VERSION) == (task_v(t).version >= resonate::twins::MAX_VERSION));
            if t.state == TaskState::Fulfilled {
                lemma_trec(t, id);
                let res = ResponseV::Both(prec_v(id, promise_v(p)), trec_v(id, task_v(t)));
                assert(spec_handle(a, kreq, n) == (a, AResponse::TaskClaim(claim_of(p))));
                assert(response_out(AResponse::TaskClaim(claim_of(p))) == res);
                assert(task_create_v(pid, ttl, c, s, now) == echo_v(res, s));
                lemma_h_noop(a, res, now);
            } else if t.state != TaskState::Pending || t.version >= echod_kernel::types::MAX_VERSION {
                assert(spec_handle(a, kreq, n) == (a, AResponse::TaskClaim(claim_err(409))));
                assert(task_create_v(pid, ttl, c, s, now) == status_v(409, s));
                lemma_h_noop(a, ResponseV::Status(409), now);
            } else {
                let t2 = t.acquire(pid, ttl as nat, n);
                let q = p.with_task(t2);
                let b = with_objects(a, a.objects.insert(id, q));
                assert(spec_handle(a, kreq, n) == (b, AResponse::TaskClaim(claim_of(q))));
                lemma_spec_task_create(n, a, q0);
                assert(inv(n, b));
                let u = acquired_v(task_v(t), (task_v(t).version + 1) as u32, pid, ttl, now);
                assert(task_v(t2) == u);
                lemma_promise_v_task(p, t2);
                assert(q.to_record() == p.to_record());
                lemma_trec(t2, id);
                let res = ResponseV::Both(prec_v(id, promise_v(p)), trec_v(id, u));
                assert(response_out(AResponse::TaskClaim(claim_of(q))) == res);
                lemma_translate_insert(a, id, q);
                assert(s.promises.insert(id, promise_v(p)) =~= s.promises);
                let next = ServerV { tasks: s.tasks.insert(id, u), ..s };
                assert(translate(b) == next);
                assert(sat_add(now, ttl) == now + ttl);
                let work = seq![at_v((now + ttl) as u64, id)];
                assert(task_create_v(pid, ttl, c, s, now) == one_v(res, next, work, Seq::empty()));
                let o = OutV { resp: res, next, work, send: Seq::empty() };
                assert(work_shape(b, work)) by {
                    assert(work_ids(work[0]) == seq![id]);
                    assert(seq![id].no_duplicates());
                }
                assert(!lease_due(q, n));
                assert forall|tt: nat| #[trigger] mdeadline_at(q, tt) && tt > now implies mdeadline_at(p, tt) || work_timer(work, id, tt) by {
                    assert(retry_deadline(q) is None);
                    if lease_deadline(q) == Some(tt) {
                        assert(tt == n + ttl);
                        assert(work[0] == at_v(tt as u64, id));
                    }
                }
                lemma_h_one_object(a, b, id, q, res, o, now);
            }
        }
    } else {
        let live = c.timeout_at > now;
        let p = if live { echod_kernel::object::spec_create_acquired(act, pid, ttl as nat, n) } else { echod_kernel::object::spec_create(act, n) };
        let b = with_objects(a, a.objects.insert(id, p));
        assert(spec_handle(a, kreq, n) == (b, AResponse::TaskClaim(claim_of(p))));
        lemma_spec_task_create(n, a, q0);
        assert(inv(n, b));
        let pv = PromiseV {
            state: if live { PState::Pending } else { PState::TimedOut },
            value: None,
            param: c.data,
            timeout_at: c.timeout_at,
            created_at: if live { now } else { c.timeout_at },
            settled_at: if live { None } else { Some(c.timeout_at) },
            tags: c.tags,
            callbacks: Set::empty(),
            listeners: Set::empty(),
        };
        assert(promise_v(p) == pv);
        let t0 = TaskV { state: TState::Fulfilled, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Seq::empty() };
        let tv = if live { acquired_v(t0, 1, pid, ttl, now) } else { t0 };
        assert(p.task is Some);
        let t = p.task.unwrap();
        assert(task_v(t) == tv);
        lemma_prec(p);
        lemma_trec(t, id);
        let res = ResponseV::Both(prec_v(id, pv), trec_v(id, tv));
        assert(response_out(AResponse::TaskClaim(claim_of(p))) == res);
        lemma_translate_insert(a, id, p);
        let next = ServerV { promises: s.promises.insert(id, pv), tasks: s.tasks.insert(id, tv), ..s };
        assert(translate(b) == next);
        assert(sat_add(now, ttl) == now + ttl);
        let work: Seq<Sched<InternalV>> = if live { seq![at_v(c.timeout_at, id), at_v((now + ttl) as u64, id)] } else { Seq::empty() };
        assert(task_create_v(pid, ttl, c, s, now) == one_v(res, next, work, Seq::empty()));
        let o = OutV { resp: res, next, work, send: Seq::empty() };
        if live {
            assert(work[0] == at_v(c.timeout_at, id));
            assert(work[1] == at_v((now + ttl) as u64, id));
            assert(work_shape(b, work)) by {
                assert forall|k: int| 0 <= k < work.len() implies work_ids(#[trigger] work[k]) == seq![id] && work[k] is Timer && work_is_on(work[k]) by {}
                assert(seq![id].no_duplicates());
            }
            assert(!lease_due(p, n));
            assert(!retry_due(p, n));
            assert forall|tt: nat| #[trigger] mdeadline_at(p, tt) && tt > now implies work_timer(work, id, tt) by {
                assert(retry_deadline(p) is None);
                if p.timeout_at as nat == tt {
                    assert(work[0] == at_v(tt as u64, id));
                } else {
                    assert(lease_deadline(p) == Some(tt));
                    assert(tt == n + ttl);
                    assert(work[1] == at_v(tt as u64, id));
                }
            }
        } else {
            assert forall|tt: nat| #[trigger] mdeadline_at(p, tt) && tt > now implies false by {
                assert(lease_deadline(p) is None);
                assert(retry_deadline(p) is None);
            }
        }
        lemma_h_new_object(a, b, id, p, res, o, now);
    }
}

pub proof fn h_task_acquire(cfg: Resonate, a: AState, id: Chars, version: u32, pid: Chars, ttl: u64, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::AcquireTask { id, version, pid, ttl }),
    ensures
        h_one(cfg, a, RequestV::AcquireTask { id, version, pid, ttl }, ARequest::TaskAcquire(ATaskAcquireReq { id, version: version as u64, pid, ttl }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::AcquireTask { id, version, pid, ttl };
    let q0 = ATaskAcquireReq { id, version: version as u64, pid, ttl };
    let kreq = ARequest::TaskAcquire(q0);
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    assert(ext(cfg, req, s, now) == acquire_task_v(id, version, pid, ttl, s, now));
    assert(ttl <= MAX_TIME && ttl >= 1);
    if !a.has_task(id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::TaskClaim(claim_err(404))));
        assert(!s.tasks.contains_key(id));
        assert(acquire_task_v(id, version, pid, ttl, s, now) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let t = p.task.unwrap();
        assert(s.tasks[id] == task_v(t));
        assert(s.promises.contains_key(id));
        lemma_live(p);
        lemma_version(t, version);
        assert((t.version >= echod_kernel::types::MAX_VERSION) == (task_v(t).version >= resonate::twins::MAX_VERSION));
        if t.state != TaskState::Pending || p.state != PromiseState::Pending || t.version != version as u64 || t.version >= echod_kernel::types::MAX_VERSION {
            assert(spec_handle(a, kreq, n) == (a, AResponse::TaskClaim(claim_err(409))));
            assert(acquire_task_v(id, version, pid, ttl, s, now) == status_v(409, s));
            lemma_h_noop(a, ResponseV::Status(409), now);
        } else {
            let t2 = t.acquire(pid, ttl as nat, n);
            let q = p.with_task(t2);
            let b = with_objects(a, a.objects.insert(id, q));
            assert(spec_handle(a, kreq, n) == (b, AResponse::TaskClaim(claim_of(q))));
            lemma_spec_task_acquire(n, a, q0);
            assert(inv(n, b));
            let u = acquired_v(task_v(t), (task_v(t).version + 1) as u32, pid, ttl, now);
            assert(task_v(t2) == u);
            lemma_promise_v_task(p, t2);
            lemma_prec(p);
            assert(q.to_record() == p.to_record());
            lemma_trec(t2, id);
            let res = ResponseV::Both(prec_v(id, promise_v(p)), trec_v(id, u));
            assert(response_out(AResponse::TaskClaim(claim_of(q))) == res);
            lemma_translate_insert(a, id, q);
            assert(s.promises.insert(id, promise_v(p)) =~= s.promises);
            let next = ServerV { tasks: s.tasks.insert(id, u), ..s };
            assert(translate(b) == next);
            assert(sat_add(now, ttl) == now + ttl);
            let work = seq![at_v((now + ttl) as u64, id)];
            assert(acquire_task_v(id, version, pid, ttl, s, now) == one_v(res, next, work, Seq::empty()));
            let o = OutV { resp: res, next, work, send: Seq::empty() };
            assert(work_shape(b, work)) by {
                assert(work_ids(work[0]) == seq![id]);
                assert(seq![id].no_duplicates());
            }
            assert(!lease_due(q, n));
            assert forall|tt: nat| #[trigger] mdeadline_at(q, tt) && tt > now implies mdeadline_at(p, tt) || work_timer(work, id, tt) by {
                assert(retry_deadline(q) is None);
                if lease_deadline(q) == Some(tt) {
                    assert(tt == n + ttl);
                    assert(work[0] == at_v(tt as u64, id));
                }
            }
            lemma_h_one_object(a, b, id, q, res, o, now);
        }
    }
}

pub proof fn h_task_release(cfg: Resonate, a: AState, id: Chars, version: u32, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::ReleaseTask { id, version }),
    ensures
        h_one(cfg, a, RequestV::ReleaseTask { id, version }, ARequest::TaskRelease(ATaskReleaseReq { id, version: version as u64 }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::ReleaseTask { id, version };
    let q0 = ATaskReleaseReq { id, version: version as u64 };
    let kreq = ARequest::TaskRelease(q0);
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    assert(ext(cfg, req, s, now) == release_task_v(id, version, s, now));
    if !a.has_task(id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 404 })));
        assert(!s.tasks.contains_key(id));
        assert(held_v(s, id, version) == Err::<TaskV, u16>(404));
        assert(release_task_v(id, version, s, now) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let t = p.task.unwrap();
        assert(s.tasks[id] == task_v(t));
        lemma_live(p);
        lemma_version(t, version);
        if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != version as u64 {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 409 })));
            assert(held_v(s, id, version) == Err::<TaskV, u16>(409));
            assert(release_task_v(id, version, s, now) == status_v(409, s));
            lemma_h_noop(a, ResponseV::Status(409), now);
        } else {
            assert(held_v(s, id, version) == Ok::<TaskV, u16>(task_v(t)));
            let q = p.with_task(t.release(now as nat));
            let b = with_objects(a, a.objects.insert(id, q));
            assert(spec_handle(a, kreq, n) == (b, AResponse::Status(AStatusRes { status: 200 })));
            lemma_spec_task_release(n, a, q0);
            assert(inv(n, b));
            let u = released_v(task_v(t), now);
            assert(task_v(t.release(now as nat)) == u);
            let next = ServerV { tasks: s.tasks.insert(id, u), ..s };
            lemma_translate_insert(a, id, q);
            lemma_promise_v_task(p, t.release(now as nat));
            assert(s.promises.insert(id, promise_v(p)) =~= s.promises);
            assert(translate(b) == next);
            let work = seq![at_v(now, id)];
            assert(release_task_v(id, version, s, now) == one_v(ResponseV::Status(200), next, work, Seq::empty()));
            let o = OutV { resp: ResponseV::Status(200), next, work, send: Seq::empty() };
            assert(work_covers(work, now, id)) by {
                assert(work_ids(work[0]) == seq![id]);
                assert(seq![id][0] == id);
                assert(work_ready(work[0], now));
            }
            assert(work_shape(b, work)) by {
                assert(work_ids(work[0]) == seq![id]);
                assert(seq![id].no_duplicates());
            }
            assert forall|tt: nat| #[trigger] mdeadline_at(q, tt) && tt > now implies mdeadline_at(p, tt) by {
                assert(lease_deadline(q) is None);
                assert(retry_deadline(q) == Some(now as nat));
            }
            lemma_h_one_object(a, b, id, q, ResponseV::Status(200), o, now);
        }
    }
}

pub proof fn h_task_fulfill(cfg: Resonate, a: AState, id: Chars, version: u32, state: Chars, data: Option<Chars>, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::FulfillTask { id, version, state, data }),
        settle_in(SettleV { id, state, data }) is Some,
    ensures
        h_one(cfg, a, RequestV::FulfillTask { id, version, state, data }, ARequest::TaskFulfill(ATaskFulfillReq { id, version: version as u64, action: settle_in(SettleV { id, state, data }).unwrap() }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::FulfillTask { id, version, state, data };
    let pst = spec_settable(state).unwrap();
    let act = settle_in(SettleV { id, state, data }).unwrap();
    assert(act == APromiseSettleReq { id, state: pstate_in(pst), value: value_in(data) });
    let q0 = ATaskFulfillReq { id, version: version as u64, action: act };
    let kreq = ARequest::TaskFulfill(q0);
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    lemma_pstate_roundtrip(pst);
    assert(ext(cfg, req, s, now) == fulfill_task_v(id, version, state, data, s, now));
    if !a.has_task(id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 404, promise: None })));
        assert(!s.tasks.contains_key(id));
        assert(held_v(s, id, version) == Err::<TaskV, u16>(404));
        assert(fulfill_task_v(id, version, state, data, s, now) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let t = p.task.unwrap();
        assert(s.tasks[id] == task_v(t));
        lemma_live(p);
        lemma_version(t, version);
        if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != version as u64 {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Promise(APromiseRes { status: 409, promise: None })));
            assert(held_v(s, id, version) == Err::<TaskV, u16>(409));
            assert(fulfill_task_v(id, version, state, data, s, now) == status_v(409, s));
            lemma_h_noop(a, ResponseV::Status(409), now);
        } else {
            assert(held_v(s, id, version) == Ok::<TaskV, u16>(task_v(t)));
            let q = p.settle(pstate_in(pst), value_in(data), n);
            let b = with_objects(a, a.objects.insert(id, q));
            assert(spec_handle(a, kreq, n) == (b, AResponse::Promise(APromiseRes { status: 200, promise: Some(q.to_record()) })));
            lemma_spec_task_fulfill(n, a, q0);
            assert(inv(n, b));
            lemma_settle_one(a, id, pst, data, now);
            let sv = settle_v(s, id, pst, data, now);
            assert(s.promises.contains_key(id));
            assert(sv.promises.contains_key(id));
            assert(fulfill_task_v(id, version, state, data, s, now) == one_v(ResponseV::Promise(prec_v(id, sv.promises[id])), sv, settled_work_v(s.promises[id], id), Seq::empty()));
        }
    }
}

pub proof fn h_task_heartbeat(cfg: Resonate, a: AState, pid: Chars, tasks: Seq<TaskRefV>, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::HeartbeatTask { pid, tasks }),
        one_origin(tasks),
    ensures
        h_one(cfg, a, RequestV::HeartbeatTask { pid, tasks }, ARequest::TaskHeartbeat(ATaskHeartbeatReq {
            pid,
            tasks: tasks.map_values(|r: TaskRefV| ATaskRef { id: r.id, version: r.version as u64 }),
        }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::HeartbeatTask { pid, tasks };
    let refs = tasks.map_values(|r: TaskRefV| ATaskRef { id: r.id, version: r.version as u64 });
    let kreq = ARequest::TaskHeartbeat(ATaskHeartbeatReq { pid, tasks: refs });
    assert(ext(cfg, req, s, now) == heartbeat_v(pid, tasks, s, now));
    let k = tasks.len() as int;
    assert(refs.len() == k);
    crate::hmany::lemma_hb_k(a, pid, tasks, k, now);
    assert(tasks.take(k) =~= tasks);
    let acc = spec_heartbeat_fold(a, pid, refs, k, n);
    assert(spec_handle(a, kreq, n) == (acc, AResponse::Status(AStatusRes { status: 200 })));
    let (ns, work, e) = heartbeat_fold(pid, tasks, s, s, Seq::empty(), false, now);
    assert(heartbeat_v(pid, tasks, s, now) == one_v(ResponseV::Status(200), ns, work, Seq::empty()));
    crate::hmany::lemma_hb_hok(a, acc, work, pid, now);
}

pub proof fn h_task_suspend(cfg: Resonate, a: AState, id: Chars, version: u32, awaited: Seq<Chars>, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::SuspendTask { id, version, awaited }),
    ensures
        h_one(cfg, a, RequestV::SuspendTask { id, version, awaited }, ARequest::TaskSuspend(ATaskSuspendReq {
            id,
            version: version as u64,
            actions: awaited.map_values(|w: Chars| APromiseRegisterCallbackReq { awaited: w, awaiter: id }),
        }), now),
{
    let n = now as nat;
    let s = translate(a);
    let ids = awaited;
    let req = RequestV::SuspendTask { id, version, awaited };
    let acts = crate::hmany::susp_acts(ids, id);
    let q0 = ATaskSuspendReq { id, version: version as u64, actions: acts };
    let kreq = ARequest::TaskSuspend(q0);
    let na = acts.len() as int;
    assert(na == ids.len());
    assert forall|j: int| 0 <= j < ids.len() implies #[trigger] acts[j].awaited == ids[j] by {}
    crate::hmany::lemma_susp_doors(ids, id);
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    assert(ext(cfg, req, s, now) == suspend_task_v(id, version, ids, s));
    if !suspend_doors(acts, id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 400 })));
        assert(suspend_task_v(id, version, ids, s) == status_v(400, s));
        lemma_h_noop(a, ResponseV::Status(400), now);
    } else if !a.has_task(id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 404 })));
        assert(!s.tasks.contains_key(id));
        assert(held_v(s, id, version) == Err::<TaskV, u16>(404));
        assert(suspend_task_v(id, version, ids, s) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let t = p.task.unwrap();
        assert(s.tasks[id] == task_v(t));
        lemma_live(p);
        lemma_version(t, version);
        if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != version as u64 {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 409 })));
            assert(held_v(s, id, version) == Err::<TaskV, u16>(409));
            assert(suspend_task_v(id, version, ids, s) == status_v(409, s));
            lemma_h_noop(a, ResponseV::Status(409), now);
        } else {
            assert(held_v(s, id, version) == Ok::<TaskV, u16>(task_v(t)));
            // what each awaited promise is, on both sides
            assert forall|j: int| 0 <= j < ids.len() implies {
                let x = #[trigger] ids[j];
                &&& (s.promises.contains_key(x) == a.objects.contains_key(x))
                &&& (a.objects.contains_key(x) ==> external_v(s.promises[x]) == a.objects[x].otype().awaitable())
                &&& (a.objects.contains_key(x) ==> live_v(s.promises[x]) == (a.objects[x].state == PromiseState::Pending))
                &&& (a.objects.contains_key(x) ==> a.objects[x].project(n) == a.objects[x])
            } by {
                let x = ids[j];
                lemma_translate_reads(a, x);
                if a.objects.contains_key(x) {
                    lemma_object_facts(a, x, now);
                    lemma_external(a.objects[x]);
                    lemma_live(a.objects[x]);
                }
            }
            let ok = all_present(ids, s) && all_external(ids, s);
            if !ok {
                // some awaited promise fails the check: 422, and the reads are the identity
                assert(exists|j: int| 0 <= j < na && awaited_fails(a, #[trigger] acts[j])) by {
                    if !all_present(ids, s) {
                        let j = choose|j: int| 0 <= j < ids.len() && !s.promises.contains_key(#[trigger] ids[j]);
                        assert(awaited_fails(a, acts[j]));
                    } else {
                        let j = choose|j: int| 0 <= j < ids.len() && !external_v(s.promises[#[trigger] ids[j]]);
                        assert(awaited_fails(a, acts[j]));
                    }
                }
                assert(first_failing(a, acts, na) is Some) by {
                    if first_failing(a, acts, na) is None {
                        lemma_first_failing_none(a, acts, na);
                    }
                }
                lemma_first_failing_some(a, acts, na);
                let j = first_failing(a, acts, na).unwrap();
                let m = if a.objects.contains_key(acts[j].awaited) { j + 1 } else { j };
                lemma_spec_awaited_read(n, a, acts, m);
                let rd = spec_awaited_read(a, acts, m, n);
                assert(rd.objects =~= a.objects) by {
                    assert forall|x: Chars| a.objects.contains_key(x) == rd.objects.contains_key(x) && (a.objects.contains_key(x) ==> rd.objects[x] == a.objects[x]) by {
                        if awaited_touched(acts, m, x) && a.objects.contains_key(x) {
                            let jj = choose|jj: int| 0 <= jj < m && #[trigger] acts[jj].awaited == x;
                            lemma_object_facts(a, x, now);
                        } else if !awaited_touched(acts, m, x) {
                            assert(unchanged_at(a, rd, x));
                        }
                    }
                }
                assert(rd == a);
                assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 422 })));
                assert(suspend_task_v(id, version, ids, s) == status_v(422, s));
                lemma_h_noop(a, ResponseV::Status(422), now);
            } else {
                assert(first_failing(a, acts, na) is None) by {
                    if first_failing(a, acts, na) is Some {
                        lemma_first_failing_some(a, acts, na);
                        let j = first_failing(a, acts, na).unwrap();
                        assert(!awaited_fails(a, acts[j]));
                    }
                }
                lemma_spec_awaited_read(n, a, acts, na);
                let cread = spec_awaited_read(a, acts, na, n);
                assert(cread.objects =~= a.objects) by {
                    assert forall|x: Chars| a.objects.contains_key(x) == cread.objects.contains_key(x) && (a.objects.contains_key(x) ==> cread.objects[x] == a.objects[x]) by {
                        if awaited_touched(acts, na, x) && a.objects.contains_key(x) {
                            lemma_object_facts(a, x, now);
                        } else if !awaited_touched(acts, na, x) {
                            assert(unchanged_at(a, cread, x));
                        }
                    }
                }
                assert(cread == a);
                lemma_spec_task_suspend(n, a, q0);
                if echod_kernel::external::any_settled(a, acts, n) {
                    assert(resonate::twins::any_settled(ids, s));
                    let q = p.with_task(t.clear_resumes());
                    let b = with_objects(a, a.objects.insert(id, q));
                    assert(spec_handle(a, kreq, n) == (b, AResponse::Status(AStatusRes { status: 300 })));
                    assert(inv(n, b));
                    let u = TaskV { resumes: Seq::empty(), ..task_v(t) };
                    assert(task_v(t.clear_resumes()) == u);
                    lemma_translate_insert(a, id, q);
                    lemma_promise_v_task(p, t.clear_resumes());
                    assert(s.promises.insert(id, promise_v(p)) =~= s.promises);
                    let next = ServerV { tasks: s.tasks.insert(id, u), ..s };
                    assert(translate(b) == next);
                    assert(suspend_task_v(id, version, ids, s) == one_v(ResponseV::Status(300), next, Seq::empty(), Seq::empty()));
                    let o = OutV { resp: ResponseV::Status(300), next, work: Seq::empty(), send: Seq::empty() };
                    assert forall|tt: nat| #[trigger] mdeadline_at(q, tt) && tt > now implies mdeadline_at(p, tt) by {}
                    lemma_h_one_object(a, b, id, q, ResponseV::Status(300), o, now);
                } else {
                    assert(!resonate::twins::any_settled(ids, s)) by {
                        if resonate::twins::any_settled(ids, s) {
                            let j = choose|j: int| 0 <= j < ids.len() && !live_v(s.promises[#[trigger] ids[j]]);
                            assert(a.objects[acts[j].awaited].project(n).state != PromiseState::Pending);
                        }
                    }
                    assert(crate::hmany::susp_ready(a, ids, id, now));
                    crate::hmany::lemma_susp_register_k(a, ids, id, na, now);
                    let d = spec_awaited_register(a, acts, na, id);
                    assert(ids.take(na) =~= ids);
                    assert(d.objects[id] == p);
                    let q = p.with_task(t.suspend());
                    let b = with_objects(d, d.objects.insert(id, q));
                    assert(spec_handle(a, kreq, n) == (b, AResponse::Status(AStatusRes { status: 200 })));
                    assert(inv(n, b));
                    let u = TaskV { state: TState::Suspended, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Seq::empty(), ..task_v(t) };
                    assert(task_v(t.suspend()) == u);
                    lemma_translate_insert(d, id, q);
                    lemma_translate_reads(d, id);
                    lemma_promise_v_task(p, t.suspend());
                    assert(translate(d).promises.insert(id, promise_v(p)) =~= translate(d).promises);
                    let next = ServerV { promises: with_callbacks(s.promises, ids, id), tasks: s.tasks.insert(id, u), ..s };
                    assert(translate(b) == next);
                    assert(suspend_task_v(id, version, ids, s) == one_v(ResponseV::Status(200), next, Seq::empty(), Seq::empty()));
                    let o = OutV { resp: ResponseV::Status(200), next, work: Seq::empty(), send: Seq::empty() };
                    crate::hmany::lemma_susp_hok(a, d, b, ids, id, q, o, now);
                }
            }
        }
    }
}

pub proof fn h_fence_create(cfg: Resonate, a: AState, id: Chars, version: u32, c: CreateV, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::FenceTask { id, version, action: FencedV::Create(c) }),
        delay_ok(c),
        crate::translate::origin(c.id) == crate::translate::origin(id),
    ensures
        h_one(cfg, a, RequestV::FenceTask { id, version, action: FencedV::Create(c) },
            ARequest::TaskFence(ATaskFenceReq { id, version: version as u64, action: ATaskFenceAction::Create(create_in(c)) }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::FenceTask { id, version, action: FencedV::Create(c) };
    let fq = ATaskFenceReq { id, version: version as u64, action: ATaskFenceAction::Create(create_in(c)) };
    let kreq = ARequest::TaskFence(fq);
    axiom_origin(c.id);
    axiom_origin(id);
    assert(echod_kernel::types::same_origin_spec(c.id, id));
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    assert(ext(cfg, req, s, now) == fence_task_v(id, version, FencedV::Create(c), s, now));
    assert(fence_target(fq.action) == c.id);
    if c.id == id {
        assert(spec_handle(a, kreq, n) == (a, AResponse::TaskFence(ATaskFenceRes { status: 400, action: None })));
        assert(fence_task_v(id, version, FencedV::Create(c), s, now) == status_v(400, s));
        lemma_h_noop(a, ResponseV::Status(400), now);
    } else if !a.has_task(id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::TaskFence(ATaskFenceRes { status: 404, action: None })));
        assert(!s.tasks.contains_key(id));
        assert(held_v(s, id, version) == Err::<TaskV, u16>(404));
        assert(fence_task_v(id, version, FencedV::Create(c), s, now) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let t = p.task.unwrap();
        assert(s.tasks[id] == task_v(t));
        lemma_live(p);
        lemma_version(t, version);
        if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != version as u64 {
            assert(spec_handle(a, kreq, n) == (a, AResponse::TaskFence(ATaskFenceRes { status: 409, action: None })));
            assert(held_v(s, id, version) == Err::<TaskV, u16>(409));
            assert(fence_task_v(id, version, FencedV::Create(c), s, now) == status_v(409, s));
            lemma_h_noop(a, ResponseV::Status(409), now);
        } else {
            assert(held_v(s, id, version) == Ok::<TaskV, u16>(task_v(t)));
            assert(fence_task_v(id, version, FencedV::Create(c), s, now) == promise_create_v(c, s, now));
            assert(request_bounded(RequestV::CreatePromise(c)));
            h_promise_create(cfg, a, c, now);
            let (d, r) = spec_promise_create(a, create_in(c), n);
            assert(spec_handle(a, ARequest::PromiseCreate(create_in(c)), n) == (d, AResponse::Promise(r)));
            assert(spec_handle(a, kreq, n) == (d, AResponse::TaskFence(ATaskFenceRes { status: 200, action: Some(ATaskFenceInnerRes::Create(r)) })));
            assert(response_out(AResponse::TaskFence(ATaskFenceRes { status: 200, action: Some(ATaskFenceInnerRes::Create(r)) })) == response_out(AResponse::Promise(r)));
        }
    }
}

pub proof fn h_fence_settle(cfg: Resonate, a: AState, id: Chars, version: u32, st: SettleV, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::FenceTask { id, version, action: FencedV::Settle(st) }),
        settle_in(st) is Some,
        crate::translate::origin(st.id) == crate::translate::origin(id),
    ensures
        h_one(cfg, a, RequestV::FenceTask { id, version, action: FencedV::Settle(st) },
            ARequest::TaskFence(ATaskFenceReq { id, version: version as u64, action: ATaskFenceAction::Settle(settle_in(st).unwrap()) }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::FenceTask { id, version, action: FencedV::Settle(st) };
    let sq = settle_in(st).unwrap();
    let fq = ATaskFenceReq { id, version: version as u64, action: ATaskFenceAction::Settle(sq) };
    let kreq = ARequest::TaskFence(fq);
    axiom_origin(st.id);
    axiom_origin(id);
    assert(echod_kernel::types::same_origin_spec(st.id, id));
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    assert(ext(cfg, req, s, now) == fence_task_v(id, version, FencedV::Settle(st), s, now));
    assert(fence_target(fq.action) == st.id);
    if st.id == id {
        assert(spec_handle(a, kreq, n) == (a, AResponse::TaskFence(ATaskFenceRes { status: 400, action: None })));
        assert(fence_task_v(id, version, FencedV::Settle(st), s, now) == status_v(400, s));
        lemma_h_noop(a, ResponseV::Status(400), now);
    } else if !a.has_task(id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::TaskFence(ATaskFenceRes { status: 404, action: None })));
        assert(!s.tasks.contains_key(id));
        assert(held_v(s, id, version) == Err::<TaskV, u16>(404));
        assert(fence_task_v(id, version, FencedV::Settle(st), s, now) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let t = p.task.unwrap();
        assert(s.tasks[id] == task_v(t));
        lemma_live(p);
        lemma_version(t, version);
        if t.state != TaskState::Acquired || p.state != PromiseState::Pending || t.version != version as u64 {
            assert(spec_handle(a, kreq, n) == (a, AResponse::TaskFence(ATaskFenceRes { status: 409, action: None })));
            assert(held_v(s, id, version) == Err::<TaskV, u16>(409));
            assert(fence_task_v(id, version, FencedV::Settle(st), s, now) == status_v(409, s));
            lemma_h_noop(a, ResponseV::Status(409), now);
        } else {
            assert(held_v(s, id, version) == Ok::<TaskV, u16>(task_v(t)));
            assert(fence_task_v(id, version, FencedV::Settle(st), s, now) == promise_settle_v(st, s, now));
            assert(request_bounded(RequestV::SettlePromise(st)));
            h_promise_settle(cfg, a, st, now);
            let (d, r) = spec_promise_settle(a, sq, n);
            assert(spec_handle(a, ARequest::PromiseSettle(sq), n) == (d, AResponse::Promise(r)));
            assert(spec_handle(a, kreq, n) == (d, AResponse::TaskFence(ATaskFenceRes { status: 200, action: Some(ATaskFenceInnerRes::Settle(r)) })));
            assert(response_out(AResponse::TaskFence(ATaskFenceRes { status: 200, action: Some(ATaskFenceInnerRes::Settle(r)) })) == response_out(AResponse::Promise(r)));
        }
    }
}

pub proof fn h_detached(cfg: Resonate, a: AState, id: Chars, version: u32, c: CreateV, now: u64, t: nat)
    requires
        ready_state(a, now),
        request_bounded(RequestV::FenceTask { id, version, action: FencedV::Create(c) }),
        delay_ok(c),
        crate::translate::origin(c.id) != crate::translate::origin(id),
        0 < t <= MAX_TIME,
    ensures
        h_two(cfg, a, RequestV::FenceTask { id, version, action: FencedV::Create(c) }, create_in(c), ATaskFenceCheckReq { id, version: version as u64 }, now, t),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::FenceTask { id, version, action: FencedV::Create(c) };
    let create = create_in(c);
    let check = ATaskFenceCheckReq { id, version: version as u64 };
    assert(c.id != id);
    assert(ext(cfg, req, s, now) == detached_create_v(id, version, c, s, now));
    assert(request_bounded(RequestV::CreatePromise(c)));
    h_promise_create(cfg, a, c, now);
    let outs0 = promise_create_v(c, s, now);
    let o = outs0[0];
    let (b, r1) = spec_handle(a, ARequest::PromiseCreate(create), n);
    assert(h_ok(a, b, response_out(r1), o, now));
    assert(o.next == translate(b));
    // the create wrote `c.id` at most, a new object without callbacks
    lemma_swept_read(a, c.id, now);
    assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies (a.objects.contains_key(z) && b.objects[z] == a.objects[z]) || (z == c.id && b.objects[z].callbacks.len() == 0) by {
        if a.objects.contains_key(c.id) {
            assert(b == a);
        } else {
            assert(b.objects == a.objects.insert(c.id, echod_kernel::object::spec_create(create, n)));
        }
    }
    let sb = crate::sweep::sweep_fn(b, n, t);
    crate::sweep_proof::lemma_sweep_swept(b, n, t);
    assert(crate::sweep_proof::swept(sb, n));
    crate::hmany::lemma_sweep_untouched(a, b, c.id, now, t);
    assert(sb.objects.dom() == b.objects.dom());
    // the check reads the task's object, unmoved
    lemma_swept_read(sb, id, now);
    lemma_translate_reads(a, id);
    lemma_translate_reads(b, id);
    let (c2, r2) = spec_handle(sb, ARequest::TaskFenceCheck(check), n);
    assert(c2 == sb);
    if !a.has_task(id) {
        assert(!sb.has_task(id));
        assert(r2 == AResponse::Status(AStatusRes { status: 404 }));
        assert(!o.next.tasks.contains_key(id));
        assert(held_v(o.next, id, version) == Err::<TaskV, u16>(404));
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        assert(b.objects[id] == p);
        assert(sb.objects[id] == p);
        let tk = p.task.unwrap();
        assert(o.next.tasks.contains_key(id) && o.next.tasks[id] == task_v(tk));
        assert(o.next.promises.contains_key(id) && o.next.promises[id] == promise_v(p));
        lemma_live(p);
        lemma_version(tk, version);
        if tk.state != TaskState::Acquired || p.state != PromiseState::Pending || tk.version != version as u64 {
            assert(r2 == AResponse::Status(AStatusRes { status: 409 }));
            assert(held_v(o.next, id, version) == Err::<TaskV, u16>(409));
        } else {
            assert(r2 == AResponse::Status(AStatusRes { status: 200 }));
            assert(held_v(o.next, id, version) == Ok::<TaskV, u16>(task_v(tk)));
        }
    }
}

pub proof fn h_task_halt(cfg: Resonate, a: AState, id: Chars, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::HaltTask(id)),
    ensures
        h_one(cfg, a, RequestV::HaltTask(id), ARequest::TaskHalt(ATaskHaltReq { id }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::HaltTask(id);
    let q0 = ATaskHaltReq { id };
    let kreq = ARequest::TaskHalt(q0);
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    assert(ext(cfg, req, s, now) == halt_task_v(id, s));
    if !a.has_task(id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 404 })));
        assert(!s.tasks.contains_key(id));
        assert(halt_task_v(id, s) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let t = p.task.unwrap();
        assert(s.tasks[id] == task_v(t));
        if t.state == TaskState::Fulfilled {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 409 })));
            assert(halt_task_v(id, s) == status_v(409, s));
            lemma_h_noop(a, ResponseV::Status(409), now);
        } else if t.state == TaskState::Halted {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 200 })));
            assert(halt_task_v(id, s) == status_v(200, s));
            lemma_h_noop(a, ResponseV::Status(200), now);
        } else {
            let q = p.with_task(t.halt());
            let b = with_objects(a, a.objects.insert(id, q));
            assert(spec_handle(a, kreq, n) == (b, AResponse::Status(AStatusRes { status: 200 })));
            lemma_spec_task_halt(n, a, q0);
            assert(inv(n, b));
            let u = TaskV { state: TState::Halted, pid: None, ttl: None, acquired_at: 0, retry_at: None, ..task_v(t) };
            assert(task_v(t.halt()) == u);
            let next = ServerV { tasks: s.tasks.insert(id, u), ..s };
            lemma_translate_insert(a, id, q);
            lemma_promise_v_task(p, t.halt());
            assert(s.promises.insert(id, promise_v(p)) =~= s.promises);
            assert(translate(b) == next);
            assert(halt_task_v(id, s) == one_v(ResponseV::Status(200), next, Seq::empty(), Seq::empty()));
            let o = OutV { resp: ResponseV::Status(200), next, work: Seq::empty(), send: Seq::empty() };
            assert forall|tt: nat| #[trigger] mdeadline_at(q, tt) && tt > now implies mdeadline_at(p, tt) by {
                assert(lease_deadline(q) is None);
                assert(retry_deadline(q) is None);
            }
            lemma_h_one_object(a, b, id, q, ResponseV::Status(200), o, now);
        }
    }
}

pub proof fn h_task_continue(cfg: Resonate, a: AState, id: Chars, now: u64)
    requires
        ready_state(a, now),
        request_bounded(RequestV::ContinueTask(id)),
    ensures
        h_one(cfg, a, RequestV::ContinueTask(id), ARequest::TaskContinue(ATaskContinueReq { id }), now),
{
    let n = now as nat;
    let s = translate(a);
    let req = RequestV::ContinueTask(id);
    let q0 = ATaskContinueReq { id };
    let kreq = ARequest::TaskContinue(q0);
    lemma_swept_read(a, id, now);
    lemma_translate_reads(a, id);
    assert(ext(cfg, req, s, now) == continue_task_v(id, s, now));
    if !a.has_task(id) {
        assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 404 })));
        assert(!s.tasks.contains_key(id));
        assert(continue_task_v(id, s, now) == status_v(404, s));
        lemma_h_noop(a, ResponseV::Status(404), now);
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let t = p.task.unwrap();
        assert(s.tasks[id] == task_v(t));
        lemma_live(p);
        if t.state != TaskState::Halted || p.state != PromiseState::Pending {
            assert(spec_handle(a, kreq, n) == (a, AResponse::Status(AStatusRes { status: 409 })));
            assert(continue_task_v(id, s, now) == status_v(409, s));
            lemma_h_noop(a, ResponseV::Status(409), now);
        } else {
            let q = p.with_task(t.continue_(now as nat));
            let b = with_objects(a, a.objects.insert(id, q));
            assert(spec_handle(a, kreq, n) == (b, AResponse::Status(AStatusRes { status: 200 })));
            lemma_spec_task_continue(n, a, q0);
            assert(inv(n, b));
            let u = TaskV { state: TState::Pending, retry_at: Some(now), ..task_v(t) };
            assert(task_v(t.continue_(now as nat)) == u);
            let next = ServerV { tasks: s.tasks.insert(id, u), ..s };
            lemma_translate_insert(a, id, q);
            lemma_promise_v_task(p, t.continue_(now as nat));
            assert(s.promises.insert(id, promise_v(p)) =~= s.promises);
            assert(translate(b) == next);
            let work = seq![at_v(now, id)];
            assert(continue_task_v(id, s, now) == one_v(ResponseV::Status(200), next, work, Seq::empty()));
            let o = OutV { resp: ResponseV::Status(200), next, work, send: Seq::empty() };
            // the task is halted, so cleared: no lease to carry
            assert(echod_kernel::properties::task_cleared(t));
            assert(work_covers(work, now, id)) by {
                assert(work_ids(work[0]) == seq![id]);
                assert(seq![id][0] == id);
                assert(work_ready(work[0], now));
            }
            assert(work_shape(b, work)) by {
                assert(work_ids(work[0]) == seq![id]);
                assert(seq![id].no_duplicates());
            }
            assert forall|tt: nat| #[trigger] mdeadline_at(q, tt) && tt > now implies mdeadline_at(p, tt) by {
                assert(lease_deadline(q) is None);
                assert(retry_deadline(q) == Some(now as nat));
            }
            lemma_h_one_object(a, b, id, q, ResponseV::Status(200), o, now);
        }
    }
}

} // verus!
