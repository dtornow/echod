//! What the handler lemmas share: a swept bucket reads as itself, a handler
//! that changes nothing leaves the relation where it was, a handler that
//! writes one object is judged on that object alone, and the records agree.

use vstd::prelude::*;

use accordant::Sched;
use echod_kernel::external::*;
use echod_kernel::internal::{lease_due, retry_due};
use echod_kernel::properties::{inv, inv_obj};
use echod_kernel::properties_proof::lemma_inv_pointwise;
use echod_kernel::steps::{lease_deadline, retry_deadline};
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::twins::*;
use resonate::PState;

use crate::drain::pending_due;
use crate::effect::*;
use crate::frame::*;
use crate::sweep::mdeadline_at;
use crate::sweep_proof::{lemma_projected_obj, swept, swept_obj};
use crate::theorem::*;
use crate::trans::{lemma_prec, lemma_translate_insert, lemma_translate_reads, leases_from_ttl};
use crate::translate::*;

verus! {

/// On a swept bucket a read changes nothing: every object is its projection.
pub proof fn lemma_swept_read(a: AState, id: Chars, now: u64)
    requires
        swept(a, now as nat),
    ensures
        spec_read(a, id, now as nat) == a,
        spec_read_task(a, id, now as nat) == a,
{
    if a.objects.contains_key(id) {
        assert(swept_obj(a.objects[id], now as nat));
        assert(a.objects.insert(id, a.objects[id].project(now as nat)) =~= a.objects);
    }
}

/// The kernel's record of a task is the model's, within the wire's version.
pub proof fn lemma_trec(t: ATask, id: Chars)
    requires
        t.version <= echod_kernel::types::MAX_VERSION,
    ensures
        trec_out(t.to_record(id)) == trec_v(id, task_v(t)),
{
}

/// Alive in the model is pending in the kernel.
pub proof fn lemma_live(p: APromise)
    ensures
        live_v(promise_v(p)) == (p.state == PromiseState::Pending),
{
}

/// The promise the model sees does not read the task.
pub proof fn lemma_promise_v_task(p: APromise, t: ATask)
    ensures
        promise_v(p.with_task(t)) == promise_v(p),
{
}

/// A swept bucket owes nothing at the clock: the empty work covers it.
pub proof fn lemma_covers_swept(a: AState, now: u64)
    requires
        inv(now as nat, a),
        swept(a, now as nat),
    ensures
        covers(a, a, Seq::empty(), now),
{
    let n = now as nat;
    assert forall|id: Chars| pending_due(a, id, now) implies false by {
        assert(swept_obj(a.objects[id], n));
        lemma_projected_obj(a.objects[id], n);
    }
    assert forall|x: Chars, w: Chars| #[trigger] a.objects.contains_key(x) && a.objects[x].state != PromiseState::Pending && #[trigger] a.objects[x].callbacks.contains(w) implies false by {
        assert(swept_obj(a.objects[x], n));
    }
}

/// A handler that changes nothing: the model answers alike and arms nothing.
pub proof fn lemma_h_noop(a: AState, resp: ResponseV, now: u64)
    requires
        ready_state(a, now),
    ensures
        h_ok(a, a, resp, OutV { resp, next: translate(a), work: Seq::empty(), send: Seq::empty() }, now),
{
    lemma_covers_swept(a, now);
}

/// `b` is `a` with one object written: what the new work must cover is what
/// that object owes.
pub proof fn lemma_covers_one(a: AState, b: AState, id: Chars, q: APromise, work: Seq<Sched<InternalV>>, now: u64)
    requires
        inv(now as nat, a),
        swept(a, now as nat),
        b.objects == a.objects.insert(id, q),
        pending_due(b, id, now) ==> work_covers(work, now, id),
        lease_due(q, now as nat) ==> work_covers(work, now, id),
        retry_due(q, now as nat) ==> work_covers(work, now, id),
        forall|w: Chars| q.state != PromiseState::Pending && #[trigger] q.callbacks.contains(w) ==> work_covers2(work, now, id, w),
        q.state != PromiseState::Pending && q.listeners.len() > 0 ==> work_covers(work, now, id),
        forall|t: nat| #[trigger] mdeadline_at(q, t) && t > now ==> (a.objects.contains_key(id) && mdeadline_at(a.objects[id], t)) || work_timer(work, id, t),
    ensures
        covers(a, b, work, now),
{
    let n = now as nat;
    assert forall|z: Chars| pending_due(b, z, now) implies work_covers(work, now, z) by {
        if z != id {
            assert(swept_obj(a.objects[z], n));
            lemma_projected_obj(a.objects[z], n);
        }
    }
    assert forall|z: Chars| #[trigger] b.objects.contains_key(z) && lease_due(b.objects[z], n) implies work_covers(work, now, z) by {
        if z != id {
            assert(swept_obj(a.objects[z], n));
        }
    }
    assert forall|z: Chars| #[trigger] b.objects.contains_key(z) && retry_due(b.objects[z], n) implies work_covers(work, now, z) by {
        if z != id {
            assert(swept_obj(a.objects[z], n));
        }
    }
    assert forall|x: Chars, w: Chars| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && #[trigger] b.objects[x].callbacks.contains(w)
        implies work_covers2(work, now, x, w) by {
        if x != id {
            assert(swept_obj(a.objects[x], n));
        }
    }
    assert forall|x: Chars| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && b.objects[x].listeners.len() > 0 implies work_covers(work, now, x) by {
        if x != id {
            assert(swept_obj(a.objects[x], n));
        }
    }
    assert forall|z: Chars, t: nat| #[trigger] b.objects.contains_key(z) && #[trigger] mdeadline_at(b.objects[z], t) && t > now
        implies (a.objects.contains_key(z) && mdeadline_at(a.objects[z], t)) || work_timer(work, z, t) by {
        if z != id {
            assert(b.objects[z] == a.objects[z]);
        }
    }
}

/// A handler that writes one object, judged on that object: its shell kept,
/// its lease by the rule, the kernel's invariant on the result, and what it
/// owes covered.
pub proof fn lemma_h_one_object(a: AState, b: AState, id: Chars, q: APromise, resp: ResponseV, o: OutV, now: u64)
    requires
        ready_state(a, now),
        a.objects.contains_key(id),
        b.objects == a.objects.insert(id, q),
        b.schedules == a.schedules,
        inv(now as nat, b),
        translate(b) == o.next,
        resp == o.resp,
        o.send == Seq::<DispatchV>::empty(),
        q.tags == a.objects[id].tags,
        match q.task {
            Some(t) => t.version <= echod_kernel::types::MAX_VERSION && ((t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap()),
            None => true,
        },
        work_shape(b, o.work),
        pending_due(b, id, now) ==> work_covers(o.work, now, id),
        lease_due(q, now as nat) ==> work_covers(o.work, now, id),
        retry_due(q, now as nat) ==> work_covers(o.work, now, id),
        forall|w: Chars| q.state != PromiseState::Pending && #[trigger] q.callbacks.contains(w) ==> work_covers2(o.work, now, id, w),
        q.state != PromiseState::Pending && q.listeners.len() > 0 ==> work_covers(o.work, now, id),
        forall|t: nat| #[trigger] mdeadline_at(q, t) && t > now ==> mdeadline_at(a.objects[id], t) || work_timer(o.work, id, t),
    ensures
        h_ok(a, b, resp, o, now),
{
    let n = now as nat;
    assert(b.objects.dom() =~= a.objects.dom());
    assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies match b.objects[z].task {
        Some(t) => (t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap(),
        None => true,
    } by {
        if z != id {
            assert(b.objects[z] == a.objects[z]);
        }
    }
    assert(no_scope(b)) by {
        assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies echod_kernel::tags::tags_get(b.objects[z].tags, "resonate:scope"@) != Some("global"@) by {
            if z != id {
                assert(b.objects[z] == a.objects[z]);
            }
        }
    }
    assert(versions_bounded(b)) by {
        assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies match b.objects[z].task {
            Some(t) => t.version <= echod_kernel::types::MAX_VERSION,
            None => true,
        } by {
            if z != id {
                assert(b.objects[z] == a.objects[z]);
            }
        }
    }
    lemma_covers_one(a, b, id, q, o.work, now);
}

/// The object at `id`, read on a swept bucket under the invariant: what every
/// task handler knows of it.
pub proof fn lemma_object_facts(a: AState, id: Chars, now: u64)
    requires
        ready_state(a, now),
        a.objects.contains_key(id),
    ensures
        ({
            let p = a.objects[id];
            &&& p.id == id
            &&& inv_obj(now as nat, a, id)
            &&& p.project(now as nat) == p
            &&& (p.state == PromiseState::Pending ==> p.timeout_at > now)
            &&& !lease_due(p, now as nat)
            &&& !retry_due(p, now as nat)
            &&& (p.state != PromiseState::Pending ==> p.callbacks.len() == 0 && p.listeners.len() == 0)
            &&& (p.task is Some ==> p.task.unwrap().version <= echod_kernel::types::MAX_VERSION)
            &&& (p.task is Some) == translate(a).tasks.contains_key(id)
            &&& translate(a).promises.contains_key(id)
            &&& translate(a).promises[id] == promise_v(p)
            &&& (p.task is Some ==> translate(a).tasks[id] == task_v(p.task.unwrap()))
        }),
{
    let n = now as nat;
    lemma_inv_pointwise(n, a);
    assert(inv_obj(n, a, id));
    assert(swept_obj(a.objects[id], n));
    lemma_projected_obj(a.objects[id], n);
    lemma_translate_reads(a, id);
}

/// The version the wire carries is the kernel's: a `u32` and a `u64` that
/// agree once the kernel's is within the wire's.
pub proof fn lemma_version(t: ATask, version: u32)
    requires
        t.version <= echod_kernel::types::MAX_VERSION,
    ensures
        (task_v(t).version == version) == (t.version == version as u64),
{
}

// ------------------------------------------------------------ edits of one
// object, as the model sees them

/// A listener added is a listener inserted.
pub proof fn lemma_add_listener_v(p: APromise, address: Chars)
    ensures
        promise_v(p.add_listener(address)) == (PromiseV { listeners: promise_v(p).listeners.insert(address), ..promise_v(p) }),
{
    broadcast use Seq::to_set_ensures;
    if p.listeners.contains(address) {
        assert(p.listeners.to_set().insert(address) =~= p.listeners.to_set());
    } else {
        p.listeners.lemma_push_to_set_commute(address);
    }
}

/// A callback added is a callback inserted.
pub proof fn lemma_add_callback_v(p: APromise, awaiter: Chars)
    ensures
        promise_v(p.add_callback(awaiter)) == (PromiseV { callbacks: promise_v(p).callbacks.insert(awaiter), ..promise_v(p) }),
{
    broadcast use Seq::to_set_ensures;
    if p.callbacks.contains(awaiter) {
        assert(p.callbacks.to_set().insert(awaiter) =~= p.callbacks.to_set());
    } else {
        p.callbacks.lemma_push_to_set_commute(awaiter);
    }
}

/// The model's settled state names, through the kernel and back.
pub proof fn lemma_pstate_roundtrip(s: PState)
    ensures
        pstate_out(pstate_in(s)) == s,
        (pstate_in(s).spec_settable()) == (s != PState::Pending && s != PState::TimedOut),
{
}

/// The work a settled promise starts, item by item: a resume for each
/// callback, an unblock note if it had listeners, nothing else.
pub proof fn lemma_settled_work(p: APromise, id: Chars)
    ensures
        ({
            let work = settled_work_v(promise_v(p), id);
            &&& forall|w: Chars| p.callbacks.contains(w) ==> exists|k: int| 0 <= k < work.len() && #[trigger] work[k] == later2_v(id, w)
            &&& p.listeners.len() > 0 ==> exists|k: int| 0 <= k < work.len() && #[trigger] work[k] == Sched::Later(InternalV::On(seq![id]))
            &&& forall|k: int| 0 <= k < work.len() ==> (#[trigger] work[k] == Sched::Later(InternalV::On(seq![id])) || exists|w: Chars| p.callbacks.contains(w) && work[k] == later2_v(id, w))
        }),
{
    broadcast use Seq::to_set_ensures;
    let pv = promise_v(p);
    let cs = pv.callbacks.to_seq();
    pv.callbacks.lemma_to_seq_to_set_id();
    assert(cs.to_set() == p.callbacks.to_set());
    let f = |w: Chars| later2_v(id, w);
    let resumes = cs.map_values(f);
    let work = settled_work_v(pv, id);
    crate::trans::lemma_to_set_nonempty(p.listeners);
    assert((pv.listeners.len() > 0) == (p.listeners.len() > 0));
    assert forall|w: Chars| p.callbacks.contains(w) implies exists|k: int| 0 <= k < work.len() && #[trigger] work[k] == later2_v(id, w) by {
        assert(cs.to_set().contains(w));
        assert(cs.contains(w));
        let k = choose|k: int| 0 <= k < cs.len() && cs[k] == w;
        assert(resumes[k] == later2_v(id, w));
        assert(work[k] == later2_v(id, w));
    }
    if p.listeners.len() > 0 {
        assert(work == resumes.push(Sched::Later(InternalV::On(seq![id]))));
        assert(work[resumes.len() as int] == Sched::Later(InternalV::On(seq![id])));
    }
    assert forall|k: int| 0 <= k < work.len() implies (#[trigger] work[k] == Sched::Later(InternalV::On(seq![id])) || exists|w: Chars| p.callbacks.contains(w) && work[k] == later2_v(id, w)) by {
        if k < resumes.len() {
            let w = cs[k];
            assert(cs.contains(w));
            assert(cs.to_set().contains(w));
            assert(p.callbacks.contains(w));
            assert(work[k] == later2_v(id, w));
        }
    }
}

/// A pending promise settled by a client at `now`: the kernel's object and
/// the model's state agree, and so do the answers.
#[verifier::rlimit(60)]
pub proof fn lemma_settle_translate(a: AState, id: Chars, state: PState, data: Option<Chars>, now: u64)
    requires
        ready_state(a, now),
        a.objects.contains_key(id),
        a.objects[id].state == PromiseState::Pending,
        pstate_in(state).spec_settable(),
    ensures
        ({
            let n = now as nat;
            let s = translate(a);
            let p = a.objects[id];
            let q = p.settle(pstate_in(state), value_in(data), n);
            let b = with_objects(a, a.objects.insert(id, q));
            let sv = settle_v(s, id, state, data, now);
            &&& promise_v(q) == (PromiseV { state, value: data, settled_at: Some(now), ..promise_v(p) })
            &&& sv.promises[id] == promise_v(q)
            &&& translate(b) == sv
            &&& response_out(AResponse::Promise(APromiseRes { status: 200, promise: Some(q.to_record()) })) == ResponseV::Promise(prec_v(id, sv.promises[id]))
            &&& (q.task is Some ==> q.task.unwrap().state == TaskState::Fulfilled && q.task.unwrap().lease_timeout_at is None && q.task.unwrap().retry_timeout_at is None && q.task.unwrap().version == p.task.unwrap().version)
            &&& (q.task is Some) == (p.task is Some)
        }),
{
    let n = now as nat;
    let s = translate(a);
    lemma_object_facts(a, id, now);
    let p = a.objects[id];
    let st = pstate_in(state);
    let v = value_in(data);
    let q = p.settle(st, v, n);
    let b = with_objects(a, a.objects.insert(id, q));
    let pv = promise_v(p);
    let qv = PromiseV { state, value: data, settled_at: Some(now), ..pv };
    lemma_pstate_roundtrip(state);
    assert(promise_v(q) == qv);
    lemma_translate_insert(a, id, q);
    let sv = settle_v(s, id, state, data, now);
    assert(translate(b).promises == sv.promises);
    match p.task {
        None => {
            assert(!s.tasks.contains_key(id));
            assert(s.tasks.remove(id) =~= s.tasks);
        },
        Some(t) => {
            assert(s.tasks[id] == task_v(t));
            if t.state != TaskState::Fulfilled {
                assert(q.task == Some(t.fulfill()));
                assert(task_v(t.fulfill()) == fulfilled_v(task_v(t)));
            } else {
                assert(q.task == Some(t));
                assert(s.tasks.insert(id, task_v(t)) =~= s.tasks);
                assert(echod_kernel::properties::task_cleared(t));
            }
        },
    }
    assert(translate(b) == sv);
    lemma_prec(q);
}

/// One item of the work a settled promise starts: a later on the promise and
/// one awaiter, or on the promise alone.
pub proof fn lemma_settle_item(b: AState, id: Chars, w: Option<Chars>, it: Sched<InternalV>)
    requires
        b.objects.contains_key(id),
        b.objects[id].state != PromiseState::Pending,
        it == (match w { Some(w) => later2_v(id, w), None => Sched::Later(InternalV::On(seq![id])) }),
        w is Some ==> w.unwrap() != id,
    ensures
        ({
            let ids = work_ids(it);
            &&& work_is_on(it)
            &&& ids.no_duplicates()
            &&& (it is Timer ==> ids.len() == 1)
            &&& (it is Later ==> 1 <= ids.len() <= 2 && b.objects.contains_key(ids[0]) && b.objects[ids[0]].state != PromiseState::Pending)
        }),
{
    match w {
        Some(w) => {
            assert(work_ids(it) == seq![id, w]);
            assert(seq![id, w].no_duplicates());
        },
        None => {
            assert(work_ids(it) == seq![id]);
            assert(seq![id].no_duplicates());
        },
    }
}

/// The work a settled promise starts has the drain's shape: laters on the
/// promise and one awaiter, or on the promise alone.
#[verifier::rlimit(100)]
pub proof fn lemma_settle_shape(a: AState, id: Chars, state: PState, data: Option<Chars>, now: u64)
    requires
        ready_state(a, now),
        a.objects.contains_key(id),
        a.objects[id].state == PromiseState::Pending,
        pstate_in(state).spec_settable(),
    ensures
        ({
            let n = now as nat;
            let p = a.objects[id];
            let q = p.settle(pstate_in(state), value_in(data), n);
            let b = with_objects(a, a.objects.insert(id, q));
            work_shape(b, settled_work_v(promise_v(p), id))
        }),
{
    let n = now as nat;
    lemma_object_facts(a, id, now);
    let p = a.objects[id];
    let q = p.settle(pstate_in(state), value_in(data), n);
    let b = with_objects(a, a.objects.insert(id, q));
    let pv = promise_v(p);
    let work = settled_work_v(pv, id);
    lemma_settled_work(p, id);
    assert(!p.callbacks.contains(id));
    assert(b.objects[id] == q);
    assert(q.state != PromiseState::Pending);
    assert forall|k: int| 0 <= k < work.len() implies {
        let ids = work_ids(#[trigger] work[k]);
        &&& work_is_on(work[k])
        &&& ids.no_duplicates()
        &&& (work[k] is Timer ==> ids.len() == 1)
        &&& (work[k] is Later ==> 1 <= ids.len() <= 2 && b.objects.contains_key(ids[0]) && b.objects[ids[0]].state != PromiseState::Pending)
    } by {
        if work[k] == Sched::Later(InternalV::On(seq![id])) {
            lemma_settle_item(b, id, None, work[k]);
        } else {
            let w = choose|w: Chars| p.callbacks.contains(w) && work[k] == later2_v(id, w);
            lemma_settle_item(b, id, Some(w), work[k]);
        }
    }
}

/// The work a settled promise starts covers what it owes: a resume per
/// callback, a note if it had listeners; its deadlines are gone.
#[verifier::rlimit(60)]
pub proof fn lemma_settle_covers(a: AState, id: Chars, state: PState, data: Option<Chars>, now: u64)
    requires
        ready_state(a, now),
        a.objects.contains_key(id),
        a.objects[id].state == PromiseState::Pending,
        pstate_in(state).spec_settable(),
    ensures
        ({
            let n = now as nat;
            let p = a.objects[id];
            let q = p.settle(pstate_in(state), value_in(data), n);
            let b = with_objects(a, a.objects.insert(id, q));
            let work = settled_work_v(promise_v(p), id);
            &&& work_shape(b, work)
            &&& forall|w: Chars| #[trigger] q.callbacks.contains(w) ==> work_covers2(work, now, id, w)
            &&& (q.listeners.len() > 0 ==> work_covers(work, now, id))
            &&& forall|tt: nat| #[trigger] mdeadline_at(q, tt) ==> false
        }),
{
    let n = now as nat;
    lemma_object_facts(a, id, now);
    lemma_settle_shape(a, id, state, data, now);
    let p = a.objects[id];
    let q = p.settle(pstate_in(state), value_in(data), n);
    let pv = promise_v(p);
    let work = settled_work_v(pv, id);
    lemma_settled_work(p, id);
    assert(q.callbacks == p.callbacks && q.listeners == p.listeners);
    assert(q.state != PromiseState::Pending);
    match p.task {
        None => {},
        Some(t) => {
            if t.state == TaskState::Fulfilled {
                assert(echod_kernel::properties::task_cleared(t));
            }
            assert(q.task.unwrap().lease_timeout_at is None);
            assert(q.task.unwrap().retry_timeout_at is None);
        },
    }
    assert forall|w: Chars| #[trigger] q.callbacks.contains(w) implies work_covers2(work, now, id, w) by {
        let k = choose|k: int| 0 <= k < work.len() && #[trigger] work[k] == later2_v(id, w);
        assert(work_ids(work[k]) == seq![id, w]);
        assert(seq![id, w][0] == id && seq![id, w][1] == w);
    }
    if q.listeners.len() > 0 {
        let k = choose|k: int| 0 <= k < work.len() && #[trigger] work[k] == Sched::Later(InternalV::On(seq![id]));
        assert(work_ids(work[k]) == seq![id]);
        assert(seq![id][0] == id);
    }
    assert forall|tt: nat| #[trigger] mdeadline_at(q, tt) implies false by {
        assert(lease_deadline(q) is None);
        assert(retry_deadline(q) is None);
    }
}

/// A pending promise settled by a client at `now`, in the kernel and in the
/// model: the same promise, the same task, the same answer, and the work the
/// model starts covers what the settled promise owes.
#[verifier::rlimit(60)]
pub proof fn lemma_settle_one(a: AState, id: Chars, state: PState, data: Option<Chars>, now: u64)
    requires
        ready_state(a, now),
        a.objects.contains_key(id),
        a.objects[id].state == PromiseState::Pending,
        pstate_in(state).spec_settable(),
        inv(now as nat, with_objects(a, a.objects.insert(id, a.objects[id].settle(pstate_in(state), value_in(data), now as nat)))),
    ensures
        ({
            let n = now as nat;
            let s = translate(a);
            let p = a.objects[id];
            let q = p.settle(pstate_in(state), value_in(data), n);
            let b = with_objects(a, a.objects.insert(id, q));
            let sv = settle_v(s, id, state, data, now);
            let resp = ResponseV::Promise(prec_v(id, sv.promises[id]));
            &&& translate(b) == sv
            &&& response_out(AResponse::Promise(APromiseRes { status: 200, promise: Some(q.to_record()) })) == resp
            &&& h_ok(a, b, resp, OutV { resp, next: sv, work: settled_work_v(promise_v(p), id), send: Seq::empty() }, now)
        }),
{
    let n = now as nat;
    let s = translate(a);
    lemma_object_facts(a, id, now);
    let p = a.objects[id];
    let q = p.settle(pstate_in(state), value_in(data), n);
    let b = with_objects(a, a.objects.insert(id, q));
    lemma_settle_translate(a, id, state, data, now);
    lemma_settle_covers(a, id, state, data, now);
    let sv = settle_v(s, id, state, data, now);
    let resp = ResponseV::Promise(prec_v(id, sv.promises[id]));
    let work = settled_work_v(promise_v(p), id);
    let o = OutV { resp, next: sv, work, send: Seq::empty() };
    assert(q.tags == p.tags);
    assert(!lease_due(q, n));
    assert(!retry_due(q, n));
    assert(!pending_due(b, id, now));
    lemma_h_one_object(a, b, id, q, resp, o, now);
}

/// No callbacks, no listeners: the empty set.
pub proof fn lemma_empty_to_set()
    ensures
        Seq::<Chars>::empty().to_set() == Set::<Chars>::empty(),
{
    broadcast use Seq::to_set_ensures;
    assert(Seq::<Chars>::empty().to_set() =~= Set::<Chars>::empty());
}

/// A handler that writes one new object, judged on that object: every
/// deadline it owes has its timer among the new work.
pub proof fn lemma_h_new_object(a: AState, b: AState, id: Chars, q: APromise, resp: ResponseV, o: OutV, now: u64)
    requires
        ready_state(a, now),
        !a.objects.contains_key(id),
        b.objects == a.objects.insert(id, q),
        b.schedules == a.schedules,
        inv(now as nat, b),
        translate(b) == o.next,
        resp == o.resp,
        o.send == Seq::<DispatchV>::empty(),
        echod_kernel::tags::tags_get(q.tags, "resonate:scope"@) != Some("global"@),
        match q.task {
            Some(t) => t.version <= echod_kernel::types::MAX_VERSION && ((t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap()),
            None => true,
        },
        work_shape(b, o.work),
        pending_due(b, id, now) ==> work_covers(o.work, now, id),
        lease_due(q, now as nat) ==> work_covers(o.work, now, id),
        retry_due(q, now as nat) ==> work_covers(o.work, now, id),
        forall|w: Chars| q.state != PromiseState::Pending && #[trigger] q.callbacks.contains(w) ==> work_covers2(o.work, now, id, w),
        q.state != PromiseState::Pending && q.listeners.len() > 0 ==> work_covers(o.work, now, id),
        forall|t: nat| #[trigger] mdeadline_at(q, t) && t > now ==> work_timer(o.work, id, t),
    ensures
        h_ok(a, b, resp, o, now),
{
    let n = now as nat;
    assert(b.objects.dom() =~= a.objects.dom().insert(id));
    assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies match b.objects[z].task {
        Some(t) => (t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap(),
        None => true,
    } by {
        if z != id {
            assert(b.objects[z] == a.objects[z]);
        }
    }
    assert(no_scope(b)) by {
        assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies echod_kernel::tags::tags_get(b.objects[z].tags, "resonate:scope"@) != Some("global"@) by {
            if z != id {
                assert(b.objects[z] == a.objects[z]);
            }
        }
    }
    assert(versions_bounded(b)) by {
        assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies match b.objects[z].task {
            Some(t) => t.version <= echod_kernel::types::MAX_VERSION,
            None => true,
        } by {
            if z != id {
                assert(b.objects[z] == a.objects[z]);
            }
        }
    }
    lemma_covers_one(a, b, id, q, o.work, now);
}

} // verus!
