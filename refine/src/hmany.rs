//! The handlers that write many objects: a heartbeat refreshes every lease it
//! names, a suspend registers a task on every promise it awaits. Each is a
//! fold on both sides, matched step by step.

use vstd::prelude::*;

use accordant::Sched;
use echod_kernel::external::*;
use echod_kernel::external_proof::*;
use echod_kernel::internal::{lease_due, retry_due};
use echod_kernel::properties::{inv, inv_obj, opt_or_zero};
use echod_kernel::steps::{lease_deadline, retry_deadline};
use echod_kernel::store::AState;
use echod_kernel::tags::OType;
use echod_kernel::types::*;
use resonate::spec::*;
use resonate::{Resonate, TState};

use crate::drain::pending_due;
use crate::effect::*;
use crate::frame::*;
use crate::hcommon::*;
use crate::sweep::mdeadline_at;
use crate::sweep_proof::swept_obj;
use crate::theorem::*;
use crate::trans::{lemma_translate_insert, lemma_translate_reads, leases_from_ttl};
use crate::translate::*;

verus! {

// --------------------------------------------------------------- heartbeat

/// A lease `pid` holds on `id`, live: what a heartbeat refreshes.
pub open spec fn hb_ok(a: AState, id: Chars, pid: Chars) -> bool {
    &&& a.objects.contains_key(id)
    &&& a.objects[id].task is Some
    &&& a.objects[id].task.unwrap().state == TaskState::Acquired
    &&& a.objects[id].task.unwrap().pid == Some(pid)
    &&& a.objects[id].state == PromiseState::Pending
}

/// The object with its lease refreshed from `now`.
pub open spec fn hb_obj(a: AState, id: Chars, now: u64) -> APromise {
    a.objects[id].with_task(a.objects[id].task.unwrap().heartbeat(now as nat))
}

/// The lease's new end.
pub open spec fn hb_end(a: AState, id: Chars, now: u64) -> nat {
    now as nat + opt_or_zero(a.objects[id].task.unwrap().ttl)
}

/// Along the fold: every object is as it was or refreshed, with its timer
/// among the work; every item of work is such a timer.
pub open spec fn hb_inv(a: AState, acc: AState, work: Seq<Sched<InternalV>>, pid: Chars, now: u64) -> bool {
    &&& acc.objects.dom() == a.objects.dom()
    &&& acc.schedules == a.schedules
    &&& forall|id: Chars| #[trigger] acc.objects.contains_key(id) ==>
        acc.objects[id] == a.objects[id] || (hb_ok(a, id, pid) && acc.objects[id] == hb_obj(a, id, now) && work_timer(work, id, hb_end(a, id, now)))
    &&& forall|j: int| 0 <= j < work.len() ==> exists|id: Chars| hb_ok(a, id, pid) && #[trigger] work[j] == at_v(hb_end(a, id, now) as u64, id)
}

/// The model's one step of its fold, as a function of what the fold holds.
pub open spec fn hb_model_step(s: ServerV, ns: ServerV, work: Seq<Sched<InternalV>>, pid: Chars, r: TaskRefV, now: u64) -> (ServerV, Seq<Sched<InternalV>>) {
    match held_v(s, r.id, r.version) {
        Ok(t) => {
            if t.pid is Some && t.pid.unwrap() == pid {
                let u = TaskV { acquired_at: now, ..t };
                (ServerV { tasks: ns.tasks.insert(r.id, u), ..ns }, work.push(at_v(lease_expires_v(u), r.id)))
            } else {
                (ns, work)
            }
        },
        Err(_) => (ns, work),
    }
}

/// The model's fold is `hb_model_step`, step by step.
pub proof fn lemma_hb_fold_step(pid: Chars, refs: Seq<TaskRefV>, s: ServerV, now: u64)
    requires
        refs.len() > 0,
    ensures
        ({
            let (n1, w1, e1) = task_heartbeat_fold(pid, refs.drop_last(), s, s, Seq::empty(), false, now);
            let (n2, w2, e2) = task_heartbeat_fold(pid, refs, s, s, Seq::empty(), false, now);
            (n2, w2) == hb_model_step(s, n1, w1, pid, refs.last(), now)
        }),
{
}

/// A refreshed object reads as itself, and its lease is the one the model
/// computes.
pub proof fn lemma_hb_obj(a: AState, id: Chars, pid: Chars, now: u64)
    requires
        ready_state(a, now),
        hb_ok(a, id, pid),
    ensures
        ({
            let q = hb_obj(a, id, now);
            let t = a.objects[id].task.unwrap();
            &&& q.project(now as nat) == q
            &&& q.task is Some
            &&& q.task.unwrap().lease_timeout_at == Some(hb_end(a, id, now) as u64)
            &&& task_v(q.task.unwrap()) == TaskV { acquired_at: now, ..task_v(t) }
            &&& lease_expires_v(TaskV { acquired_at: now, ..task_v(t) }) == hb_end(a, id, now) as u64
            &&& promise_v(q) == promise_v(a.objects[id])
            &&& t.ttl is Some
            &&& hb_end(a, id, now) <= 2 * (MAX_TIME as nat)
        }),
{
    let n = now as nat;
    lemma_object_facts(a, id, now);
    let p = a.objects[id];
    let t = p.task.unwrap();
    assert(t.ttl is Some);
    let ttl = t.ttl.unwrap();
    assert(ttl <= MAX_TIME);
    let q = hb_obj(a, id, now);
    assert(q.project(n) == q);
    assert(sat_add(now, ttl) == now + ttl);
}

/// One ref of a heartbeat, on both sides.
#[verifier::rlimit(60)]
pub proof fn lemma_hb_step(a: AState, acc: AState, work: Seq<Sched<InternalV>>, pid: Chars, r: TaskRefV, now: u64)
    requires
        ready_state(a, now),
        inv(now as nat, acc),
        hb_inv(a, acc, work, pid, now),
        translate(acc) == hb_ns(a, acc),
    ensures
        ({
            let n = now as nat;
            let acc2 = spec_heartbeat_one(acc, pid, ATaskRef { id: r.id, version: r.version as u64 }, n);
            let (ns2, work2) = hb_model_step(translate(a), translate(acc), work, pid, r, now);
            &&& translate(acc2) == ns2
            &&& hb_inv(a, acc2, work2, pid, now)
        }),
{
    let n = now as nat;
    let s = translate(a);
    let id = r.id;
    let kr = ATaskRef { id, version: r.version as u64 };
    let acc2 = spec_heartbeat_one(acc, pid, kr, n);
    lemma_translate_reads(a, id);
    lemma_translate_reads(acc, id);
    if !a.objects.contains_key(id) {
        assert(!acc.objects.contains_key(id));
        assert(!acc.has_task(id));
        assert(acc2 == acc);
        assert(held_v(s, id, r.version) == Err::<TaskV, u16>(404));
    } else {
        lemma_object_facts(a, id, now);
        let p = a.objects[id];
        let pa = acc.objects[id];
        lemma_live(p);
        match p.task {
            None => {
                assert(pa == p);
                assert(!acc.has_task(id));
                assert(acc2 == acc);
                assert(!s.tasks.contains_key(id));
                assert(held_v(s, id, r.version) == Err::<TaskV, u16>(404));
            },
            Some(t) => {
                lemma_version(t, r.version);
                assert(s.tasks[id] == task_v(t));
                // the object as the fold holds it reads as itself, with t's state, version, pid
                let ta = pa.task.unwrap();
                assert(pa.project(n) == pa) by {
                    if pa != p {
                        lemma_hb_obj(a, id, pid, now);
                    }
                }
                assert(ta.state == t.state && ta.version == t.version && ta.pid == t.pid && ta.ttl == t.ttl);
                assert(pa.state == p.state);
                assert(spec_read_task(acc, id, n) == acc) by {
                    assert(acc.objects.insert(id, pa.project(n)) =~= acc.objects);
                }
                let held = t.state == TaskState::Acquired && t.version == r.version as u64 && p.state == PromiseState::Pending;
                if !held {
                    assert(acc2 == acc);
                    assert(held_v(s, id, r.version) == Err::<TaskV, u16>(409));
                } else {
                    assert(held_v(s, id, r.version) == Ok::<TaskV, u16>(task_v(t)));
                    if t.pid != Some(pid) {
                        assert(acc2 == acc);
                    } else {
                        assert(hb_ok(a, id, pid));
                        lemma_hb_obj(a, id, pid, now);
                        let q = hb_obj(a, id, now);
                        assert(ta.heartbeat(n) == t.heartbeat(n));
                        assert(pa.with_task(ta.heartbeat(n)) == q);
                        assert(acc2.objects == acc.objects.insert(id, q));
                        let u = TaskV { acquired_at: now, ..task_v(t) };
                        lemma_translate_insert(acc, id, q);
                        assert(translate(acc).promises.insert(id, promise_v(q)) =~= translate(acc).promises);
                        let (ns2, work2) = hb_model_step(s, translate(acc), work, pid, r, now);
                        assert(ns2 == ServerV { tasks: translate(acc).tasks.insert(id, u), ..translate(acc) });
                        assert(translate(acc2) == ns2);
                        assert(work2 == work.push(at_v(hb_end(a, id, now) as u64, id)));
                        assert(work2[work.len() as int] == at_v(hb_end(a, id, now) as u64, id));
                        assert(acc2.objects.dom() =~= a.objects.dom());
                        assert forall|z: Chars| #[trigger] acc2.objects.contains_key(z) implies
                            acc2.objects[z] == a.objects[z] || (hb_ok(a, z, pid) && acc2.objects[z] == hb_obj(a, z, now) && work_timer(work2, z, hb_end(a, z, now))) by {
                            if z == id {
                            } else {
                                assert(acc2.objects[z] == acc.objects[z]);
                                if acc.objects[z] != a.objects[z] {
                                    let j = choose|j: int| 0 <= j < work.len() && #[trigger] work[j] == at_v(hb_end(a, z, now) as u64, z);
                                    assert(work2[j] == work[j]);
                                }
                            }
                        }
                        assert forall|j: int| 0 <= j < work2.len() implies exists|z: Chars| hb_ok(a, z, pid) && #[trigger] work2[j] == at_v(hb_end(a, z, now) as u64, z) by {
                            if j < work.len() {
                                assert(work2[j] == work[j]);
                            }
                        }
                    }
                }
            },
        }
    }
}

/// What the fold's state translates to: a name for `translate(acc)`.
pub open spec fn hb_ns(a: AState, acc: AState) -> ServerV {
    translate(acc)
}

/// The first `k` refs, on both sides.
pub proof fn lemma_hb_k(a: AState, pid: Chars, tasks: Seq<TaskRefV>, k: int, now: u64)
    requires
        ready_state(a, now),
        0 <= k <= tasks.len(),
    ensures
        ({
            let n = now as nat;
            let refs = tasks.map_values(|r: TaskRefV| ATaskRef { id: r.id, version: r.version as u64 });
            let acc = spec_heartbeat_fold(a, pid, refs, k, n);
            let (ns, work, e) = task_heartbeat_fold(pid, tasks.take(k), translate(a), translate(a), Seq::empty(), false, now);
            &&& inv(n, acc)
            &&& translate(acc) == ns
            &&& hb_inv(a, acc, work, pid, now)
        }),
    decreases k,
{
    let n = now as nat;
    let s = translate(a);
    let refs = tasks.map_values(|r: TaskRefV| ATaskRef { id: r.id, version: r.version as u64 });
    lemma_spec_heartbeat_fold_inv(n, a, pid, refs, k);
    if k == 0 {
        assert(tasks.take(0).len() == 0);
        assert(spec_heartbeat_fold(a, pid, refs, 0, n) == a);
    } else {
        lemma_hb_k(a, pid, tasks, k - 1, now);
        let acc1 = spec_heartbeat_fold(a, pid, refs, k - 1, n);
        let prefix = tasks.take(k);
        assert(prefix.drop_last() =~= tasks.take(k - 1));
        assert(prefix.last() == tasks[k - 1]);
        assert(refs[k - 1] == ATaskRef { id: tasks[k - 1].id, version: tasks[k - 1].version as u64 });
        lemma_hb_fold_step(pid, prefix, s, now);
        let (ns1, work1, e1) = task_heartbeat_fold(pid, tasks.take(k - 1), s, s, Seq::empty(), false, now);
        lemma_hb_step(a, acc1, work1, pid, tasks[k - 1], now);
        assert(spec_heartbeat_fold(a, pid, refs, k, n) == spec_heartbeat_one(acc1, pid, refs[k - 1], n));
    }
}

/// The heartbeat's result keeps the relation: every refreshed lease has its
/// timer, nothing else moved.
#[verifier::rlimit(60)]
pub proof fn lemma_hb_hok(a: AState, acc: AState, work: Seq<Sched<InternalV>>, pid: Chars, now: u64)
    requires
        ready_state(a, now),
        inv(now as nat, acc),
        hb_inv(a, acc, work, pid, now),
    ensures
        h_ok(a, acc, ResponseV::Status(200), OutV { resp: ResponseV::Status(200), next: translate(acc), work, send: Seq::empty() }, now),
{
    let n = now as nat;
    assert(leases_from_ttl(acc)) by {
        assert forall|z: Chars| #[trigger] acc.objects.contains_key(z) implies match acc.objects[z].task {
            Some(t) => (t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap(),
            None => true,
        } by {
            if acc.objects[z] != a.objects[z] {
                lemma_hb_obj(a, z, pid, now);
            }
        }
    }
    assert(no_scope(acc)) by {
        assert forall|z: Chars| #[trigger] acc.objects.contains_key(z) implies echod_kernel::tags::tags_get(acc.objects[z].tags, "resonate:scope"@) != Some("global"@) by {
            assert(acc.objects[z].tags == a.objects[z].tags);
        }
    }
    assert(versions_bounded(acc)) by {
        assert forall|z: Chars| #[trigger] acc.objects.contains_key(z) implies match acc.objects[z].task {
            Some(t) => t.version <= echod_kernel::types::MAX_VERSION,
            None => true,
        } by {
            if acc.objects[z] != a.objects[z] {
                lemma_object_facts(a, z, now);
            }
        }
    }
    assert(work_shape(acc, work)) by {
        assert forall|j: int| 0 <= j < work.len() implies {
            let ids = work_ids(#[trigger] work[j]);
            &&& work_is_on(work[j])
            &&& ids.no_duplicates()
            &&& (work[j] is Timer ==> ids.len() == 1)
            &&& (work[j] is Later ==> 1 <= ids.len() <= 2 && acc.objects.contains_key(ids[0]) && acc.objects[ids[0]].state != PromiseState::Pending)
        } by {
            let z = choose|z: Chars| hb_ok(a, z, pid) && #[trigger] work[j] == at_v(hb_end(a, z, now) as u64, z);
            assert(work_ids(work[j]) == seq![z]);
            assert(seq![z].no_duplicates());
        }
    }
    // what is due: a refreshed lease whose ttl is zero, covered by its timer, now ready
    assert forall|z: Chars| pending_due(acc, z, now) implies work_covers(work, now, z) by {
        lemma_object_facts(a, z, now);
        assert(acc.objects[z].state == a.objects[z].state && acc.objects[z].timeout_at == a.objects[z].timeout_at);
    }
    assert forall|z: Chars| #[trigger] acc.objects.contains_key(z) && lease_due(acc.objects[z], n) implies work_covers(work, now, z) by {
        lemma_object_facts(a, z, now);
        if acc.objects[z] != a.objects[z] {
            lemma_hb_obj(a, z, pid, now);
            let e = hb_end(a, z, now);
            assert(e <= n);
            let j = choose|j: int| 0 <= j < work.len() && #[trigger] work[j] == at_v(e as u64, z);
            assert(work_ready(work[j], now));
            assert(work_ids(work[j]) == seq![z]);
            assert(seq![z][0] == z);
        }
    }
    assert forall|z: Chars| #[trigger] acc.objects.contains_key(z) && retry_due(acc.objects[z], n) implies work_covers(work, now, z) by {
        lemma_object_facts(a, z, now);
        if acc.objects[z] != a.objects[z] {
            lemma_hb_obj(a, z, pid, now);
        }
    }
    assert forall|x: Chars, w: Chars| #[trigger] acc.objects.contains_key(x) && acc.objects[x].state != PromiseState::Pending && #[trigger] acc.objects[x].callbacks.contains(w)
        implies work_covers2(work, now, x, w) by {
        lemma_object_facts(a, x, now);
        assert(acc.objects[x].state == a.objects[x].state && acc.objects[x].callbacks == a.objects[x].callbacks);
    }
    assert forall|x: Chars| #[trigger] acc.objects.contains_key(x) && acc.objects[x].state != PromiseState::Pending && acc.objects[x].listeners.len() > 0 implies work_covers(work, now, x) by {
        lemma_object_facts(a, x, now);
        assert(acc.objects[x].state == a.objects[x].state && acc.objects[x].listeners == a.objects[x].listeners);
    }
    assert forall|z: Chars, t: nat| #[trigger] acc.objects.contains_key(z) && #[trigger] mdeadline_at(acc.objects[z], t) && t > now
        implies (a.objects.contains_key(z) && mdeadline_at(a.objects[z], t)) || work_timer(work, z, t) by {
        if acc.objects[z] != a.objects[z] {
            lemma_object_facts(a, z, now);
            lemma_hb_obj(a, z, pid, now);
            let q = acc.objects[z];
            let p = a.objects[z];
            assert(retry_deadline(q) == retry_deadline(p));
            if lease_deadline(q) == Some(t) {
                assert(t == hb_end(a, z, now));
            }
        }
    }
}

} // verus!

verus! {

// ----------------------------------------------------------------- suspend

/// The kernel's actions for a suspend: one callback registration per awaited.
pub open spec fn susp_acts(ids: Seq<Chars>, id: Chars) -> Seq<APromiseRegisterCallbackReq> {
    ids.map_values(|w: Chars| APromiseRegisterCallbackReq { awaited: w, awaiter: id })
}

/// The kernel's doors are the model's three.
pub proof fn lemma_susp_doors(ids: Seq<Chars>, id: Chars)
    ensures
        suspend_doors(susp_acts(ids, id), id) == (!(ids.len() == 0 || ids.contains(id)) && distinct(ids) && all_in_origin(ids, id)),
{
    let acts = susp_acts(ids, id);
    assert(acts.len() == ids.len());
    assert forall|j: int| 0 <= j < ids.len() implies #[trigger] acts[j].awaited == ids[j] by {}
    assert forall|j: int| 0 <= j < ids.len() implies (echod_kernel::types::same_origin_spec(#[trigger] ids[j], id) == (crate::translate::origin(ids[j]) == crate::translate::origin(id))) by {
        axiom_origin(ids[j]);
        axiom_origin(id);
    }
    if suspend_doors(acts, id) {
        assert(ids.len() > 0);
        assert(!ids.contains(id)) by {
            if ids.contains(id) {
                let j = choose|j: int| 0 <= j < ids.len() && ids[j] == id;
                assert(acts[j].awaited == id);
            }
        }
        assert(distinct(ids)) by {
            assert forall|i: int, j: int| 0 <= i < j < ids.len() implies ids[i] != ids[j] by {
                if ids[i] == ids[j] {
                    assert(acts[i].awaited == acts[j].awaited);
                }
            }
        }
        assert forall|i: int| 0 <= i < ids.len() implies crate::translate::origin(#[trigger] ids[i]) == crate::translate::origin(id) by {
            assert(acts[i].awaited == ids[i]);
            assert(echod_kernel::types::same_origin_spec(acts[i].awaited, id));
        }
        assert(all_in_origin(ids, id));
    } else {
        if ids.len() > 0 && !ids.contains(id) && distinct(ids) && all_in_origin(ids, id) {
            assert(awaited_distinct(acts)) by {
                assert forall|i: int, j: int| 0 <= i < acts.len() && 0 <= j < acts.len() && #[trigger] acts[i].awaited == #[trigger] acts[j].awaited implies i == j by {
                    if i < j {
                        assert(ids[i] != ids[j]);
                    } else if j < i {
                        assert(ids[j] != ids[i]);
                    }
                }
            }
            assert forall|j: int| 0 <= j < acts.len() implies #[trigger] acts[j].awaited != id && echod_kernel::types::same_origin_spec(acts[j].awaited, id) by {
                assert(ids[j] != id) by {
                    if ids[j] == id {
                        assert(ids.contains(id));
                    }
                }
            }
            assert(suspend_doors(acts, id));
        }
    }
}

/// Every awaited promise is there, awaitable, live and ahead of its deadline;
/// the task's own promise is live too. What a suspend that succeeds knows.
pub open spec fn susp_ready(a: AState, ids: Seq<Chars>, id: Chars, now: u64) -> bool {
    &&& ids.len() > 0
    &&& !ids.contains(id)
    &&& distinct(ids)
    &&& all_in_origin(ids, id)
    &&& forall|j: int| 0 <= j < ids.len() ==> {
        let x = #[trigger] ids[j];
        &&& a.objects.contains_key(x)
        &&& a.objects[x].otype().awaitable()
        &&& a.objects[x].state == PromiseState::Pending
    }
    &&& a.objects.contains_key(id)
    &&& a.objects[id].otype() == OType::Runnable
    &&& a.objects[id].state == PromiseState::Pending
}

/// The model's `with_callbacks` on a prefix is the kernel's registration of
/// that prefix, translated.
pub proof fn lemma_susp_register_k(a: AState, ids: Seq<Chars>, id: Chars, k: int, now: u64)
    requires
        ready_state(a, now),
        susp_ready(a, ids, id, now),
        0 <= k <= ids.len(),
    ensures
        ({
            let d = spec_awaited_register(a, susp_acts(ids, id), k, id);
            &&& inv(now as nat, d)
            &&& d.objects.dom() == a.objects.dom()
            &&& d.schedules == a.schedules
            &&& translate(d) == ServerV { promises: with_callbacks(translate(a).promises, ids.take(k), id), ..translate(a) }
            &&& forall|j: int| 0 <= j < k ==> d.objects[#[trigger] ids[j]] == a.objects[ids[j]].add_callback(id)
            &&& forall|x: Chars| #[trigger] d.objects.contains_key(x) && !ids.take(k).contains(x) ==> d.objects[x] == a.objects[x]
        }),
    decreases k,
{
    let n = now as nat;
    let s = translate(a);
    let acts = susp_acts(ids, id);
    lemma_susp_doors(ids, id);
    assert forall|j: int| 0 <= j < ids.len() implies #[trigger] acts[j].awaited == ids[j] by {}
    assert forall|j: int| 0 <= j < ids.len() implies a.objects[#[trigger] ids[j]].timeout_at > now by {
        lemma_object_facts(a, ids[j], now);
    }
    lemma_object_facts(a, id, now);
    lemma_spec_awaited_register(n, a, acts, k, id);
    let d = spec_awaited_register(a, acts, k, id);
    assert(d.objects.dom() =~= a.objects.dom()) by {
        assert forall|x: Chars| a.objects.contains_key(x) == d.objects.contains_key(x) by {
            if awaited_touched(acts, k, x) {
                let j = choose|j: int| 0 <= j < k && #[trigger] acts[j].awaited == x;
                assert(acts[j].awaited == ids[j]);
            } else {
                assert(unchanged_at(a, d, x));
            }
        }
    }
    assert forall|x: Chars| #[trigger] d.objects.contains_key(x) && !ids.take(k).contains(x) implies d.objects[x] == a.objects[x] by {
        assert(!awaited_touched(acts, k, x)) by {
            if awaited_touched(acts, k, x) {
                let j = choose|j: int| 0 <= j < k && #[trigger] acts[j].awaited == x;
                assert(ids.take(k)[j] == x);
            }
        }
        assert(unchanged_at(a, d, x));
    }
    if k == 0 {
        assert(ids.take(0).len() == 0);
        assert(d == a);
    } else {
        lemma_susp_register_k(a, ids, id, k - 1, now);
        let d1 = spec_awaited_register(a, acts, k - 1, id);
        let w = ids[k - 1];
        assert(acts[k - 1].awaited == w);
        let m = with_callbacks(s.promises, ids.take(k - 1), id);
        assert(ids.take(k).drop_last() =~= ids.take(k - 1));
        assert(ids.take(k).last() == w);
        assert(translate(d1).promises == m);
        assert(d1.objects.contains_key(w));
        lemma_translate_reads(d1, w);
        assert(m.contains_key(w));
        assert(m[w] == promise_v(d1.objects[w]));
        let q = d1.objects[w].add_callback(id);
        assert(d.objects == d1.objects.insert(w, q));
        lemma_add_callback_v(d1.objects[w], id);
        lemma_translate_insert(d1, w, q);
        assert(translate(d).tasks == translate(d1).tasks) by {
            match q.task {
                Some(t) => { assert(translate(d1).tasks.insert(w, task_v(t)) =~= translate(d1).tasks); },
                None => { assert(translate(d1).tasks.remove(w) =~= translate(d1).tasks); },
            }
        }
        assert(with_callbacks(s.promises, ids.take(k), id) == m.insert(w, PromiseV { callbacks: m[w].callbacks.insert(id), ..m[w] }));
    }
}

// ------------------------------------------------- the sweep after a create

/// Sweeping a swept bucket with one object written that holds no callback
/// leaves every other object as it was.
pub proof fn lemma_sweep_untouched(a: AState, b: AState, x: Chars, now: u64, t: nat)
    requires
        ready_state(a, now),
        inv(now as nat, b),
        0 < t <= MAX_TIME,
        b.objects.dom().finite(),
        forall|z: Chars| #[trigger] b.objects.contains_key(z) ==> (a.objects.contains_key(z) && b.objects[z] == a.objects[z]) || (z == x && b.objects[z].callbacks.len() == 0),
    ensures
        forall|z: Chars| #[trigger] b.objects.contains_key(z) && z != x ==> crate::sweep::sweep_fn(b, now as nat, t).objects[z] == b.objects[z],
{
    let n = now as nat;
    let ids = crate::sweep::ids_of(b);
    crate::canon::lemma_sweep_canon(b, n, t);
    assert forall|z: Chars| #[trigger] b.objects.contains_key(z) && z != x implies crate::sweep::sweep_fn(b, n, t).objects[z] == b.objects[z] by {
        let p = b.objects[z];
        lemma_object_facts(a, z, now);
        assert(p == a.objects[z]);
        assert(crate::canon::c12(p, n) == p);
        assert forall|k: int| 0 <= k < ids.len() implies !crate::canon::awaits(b, #[trigger] ids[k], z, n) by {
            let y = ids[k];
            if b.objects.contains_key(y) {
                if a.objects.contains_key(y) && b.objects[y] == a.objects[y] {
                    lemma_object_facts(a, y, now);
                    assert(b.objects[y].project(n) == b.objects[y]);
                } else {
                    assert(b.objects[y].callbacks.len() == 0);
                }
            }
        }
        match p.task {
            None => {},
            Some(t0) => {
                crate::absorb::lemma_resumed_none(b, z, ids, t0, n);
            },
        }
        if p.state != PromiseState::Pending {
            assert(p.callbacks =~= Seq::<Chars>::empty());
            assert(p.listeners =~= Seq::<Chars>::empty());
        }
        assert(crate::canon::c4(b, z, ids, n) == p);
        assert(crate::canon::c5(b, z, ids, n, t) == p);
    }
}

} // verus!

verus! {

/// The suspend's result keeps the relation: the awaited promises gained a
/// callback, the task went to sleep, nothing is owed.
#[verifier::rlimit(60)]
pub proof fn lemma_susp_hok(a: AState, d: AState, b: AState, ids: Seq<Chars>, id: Chars, q: APromise, o: OutV, now: u64)
    requires
        ready_state(a, now),
        susp_ready(a, ids, id, now),
        d.objects.dom() == a.objects.dom(),
        d.schedules == a.schedules,
        forall|j: int| 0 <= j < ids.len() ==> d.objects[#[trigger] ids[j]] == a.objects[ids[j]].add_callback(id),
        forall|x: Chars| #[trigger] d.objects.contains_key(x) && !ids.contains(x) ==> d.objects[x] == a.objects[x],
        q == a.objects[id].with_task(a.objects[id].task.unwrap().suspend()),
        b.objects == d.objects.insert(id, q),
        b.schedules == d.schedules,
        inv(now as nat, b),
        translate(b) == o.next,
        o.resp == ResponseV::Status(200),
        o.work == Seq::<Sched<InternalV>>::empty(),
        o.send == Seq::<DispatchV>::empty(),
    ensures
        h_ok(a, b, ResponseV::Status(200), o, now),
{
    let n = now as nat;
    lemma_object_facts(a, id, now);
    assert(b.objects.dom() =~= a.objects.dom());
    // every object: as it was, with a callback more, or the task asleep
    assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies {
        let r = b.objects[z];
        let p = a.objects[z];
        &&& r.tags == p.tags
        &&& r.state == p.state
        &&& r.timeout_at == p.timeout_at
        &&& r.listeners == p.listeners
        &&& (z != id ==> r.task == p.task && (r.state != PromiseState::Pending ==> r.callbacks == p.callbacks))
        &&& (z == id ==> r.callbacks == p.callbacks && r.task == Some(p.task.unwrap().suspend()))
    } by {
        if z == id {
        } else if ids.contains(z) {
            let j = choose|j: int| 0 <= j < ids.len() && ids[j] == z;
            assert(b.objects[z] == a.objects[z].add_callback(id));
            lemma_object_facts(a, z, now);
        } else {
            assert(b.objects[z] == a.objects[z]);
        }
    }
    assert(leases_from_ttl(b)) by {
        assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies match b.objects[z].task {
            Some(t) => (t.lease_timeout_at is Some && t.ttl is Some) ==> t.lease_timeout_at.unwrap() >= t.ttl.unwrap(),
            None => true,
        } by {
            if z != id {
                assert(b.objects[z].task == a.objects[z].task);
            }
        }
    }
    assert(no_scope(b)) by {
        assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies echod_kernel::tags::tags_get(b.objects[z].tags, "resonate:scope"@) != Some("global"@) by {
            assert(b.objects[z].tags == a.objects[z].tags);
        }
    }
    assert(versions_bounded(b)) by {
        assert forall|z: Chars| #[trigger] b.objects.contains_key(z) implies match b.objects[z].task {
            Some(t) => t.version <= echod_kernel::types::MAX_VERSION,
            None => true,
        } by {
            lemma_object_facts(a, z, now);
            if z != id {
                assert(b.objects[z].task == a.objects[z].task);
            }
        }
    }
    assert forall|z: Chars| pending_due(b, z, now) implies false by {
        lemma_object_facts(a, z, now);
    }
    assert forall|z: Chars| #[trigger] b.objects.contains_key(z) && lease_due(b.objects[z], n) implies false by {
        lemma_object_facts(a, z, now);
        if z != id {
            assert(b.objects[z].task == a.objects[z].task);
        }
    }
    assert forall|z: Chars| #[trigger] b.objects.contains_key(z) && retry_due(b.objects[z], n) implies false by {
        lemma_object_facts(a, z, now);
        if z != id {
            assert(b.objects[z].task == a.objects[z].task);
        }
    }
    assert forall|x: Chars, w: Chars| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && #[trigger] b.objects[x].callbacks.contains(w) implies false by {
        lemma_object_facts(a, x, now);
    }
    assert forall|x: Chars| #[trigger] b.objects.contains_key(x) && b.objects[x].state != PromiseState::Pending && b.objects[x].listeners.len() > 0 implies false by {
        lemma_object_facts(a, x, now);
    }
    assert forall|z: Chars, tt: nat| #[trigger] b.objects.contains_key(z) && #[trigger] mdeadline_at(b.objects[z], tt) && tt > now implies mdeadline_at(a.objects[z], tt) by {
        if z == id {
            assert(lease_deadline(b.objects[z]) is None);
            assert(retry_deadline(b.objects[z]) is None);
        } else {
            assert(b.objects[z].task == a.objects[z].task);
        }
    }
}

} // verus!
