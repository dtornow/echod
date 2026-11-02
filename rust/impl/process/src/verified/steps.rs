//! The steps a node runs around a request, verified: the instant a step is
//! decided at, the sweep that fires what is due, the drain that discharges
//! what a step left owed, and the nearest deadline a document owes a timer
//! for.
//!
//! The specification of that composition is `echod_concrete::steps_spec`:
//! after a sweep at `now` nothing in the document is due (`no_due`), a sweep
//! that fired nothing left the document as it was, and `next_deadline` is
//! the least deadline (`is_next`). The functions here ensure they compute it.

use vstd::prelude::*;

use super::external::*;
use super::internal::*;
use super::store::*;
use super::store_proof::*;
use super::tags::OType;
use super::types::*;

#[cfg(verus_keep_ghost)]
use super::internal_spec::*;
#[cfg(verus_keep_ghost)]
use super::properties::*;
#[cfg(verus_keep_ghost)]
use super::steps_spec::*;

verus! {

// ---------------------------------------------------------------------------
// The instant a step is decided at
// ---------------------------------------------------------------------------

/// The instant a step on a document is decided at: the node's clock, or the
/// document's stamp — the instant of the step that wrote it — whichever is
/// later. The kernel is proved for `now` at or after the instant it last
/// ran at (`lemma_inv_at`), and a node behind the previous writer's clock
/// would otherwise step outside that.
pub fn clamp_now(stamp: u64, now: u64) -> (r: u64)
    ensures r >= stamp, r >= now, r == stamp || r == now,
{
    if stamp > now { stamp } else { now }
}

// ---------------------------------------------------------------------------
// The nearest deadline
// ---------------------------------------------------------------------------

fn note(min: Option<u64>, d: u64) -> (r: Option<u64>)
    ensures r == Some(match min { Some(m) => if d < m { d } else { m }, None => d }),
{
    match min {
        Some(m) => if d < m { Some(d) } else { Some(m) },
        None => Some(d),
    }
}

/// The least deadline of the object rows, which fold to the objects.
fn objects_next(rows: &Vec<Promise>) -> (r: Option<u64>)
    requires distinct_by(rows@, obj_key()),
    ensures
        match r {
            Some(d) => objects_deadline(fold_by(rows@, obj_key(), obj_val()), d as nat)
                && forall |u: nat| objects_deadline(fold_by(rows@, obj_key(), obj_val()), u) ==> d as nat <= u,
            None => forall |t: nat| !objects_deadline(fold_by(rows@, obj_key(), obj_val()), t),
        },
{
    let mut min: Option<u64> = None;
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows@.len(),
            match min {
                Some(m) => (exists |j: int| 0 <= j < i && #[trigger] deadline_at(rows@[j]@, m as nat))
                    && forall |j: int, t: nat| 0 <= j < i && #[trigger] deadline_at(rows@[j]@, t) ==> m as nat <= t,
                None => forall |j: int, t: nat| 0 <= j < i ==> !#[trigger] deadline_at(rows@[j]@, t),
            },
        decreases rows@.len() - i,
    {
        let p = &rows[i];
        let ghost before = min;
        let ghost ap = p@;
        let pending = match p.state { PromiseState::Pending => true, _ => false };
        let internal = match super::tags::exec_otype(&p.tags) { OType::Internal => true, _ => false };
        if pending && !internal {
            min = note(min, p.timeout_at);
        }
        let ghost after_p = min;
        match &p.task {
            Some(t) => {
                match t.lease_timeout_at {
                    Some(d) => { min = note(min, d); }
                    None => {}
                }
                match t.retry_timeout_at {
                    Some(d) => { min = note(min, d); }
                    None => {}
                }
            }
            None => {}
        }
        proof {
            assert(promise_deadline(ap) == (if pending && !internal { Some(ap.timeout_at as nat) } else { None }));
            assert forall |t: nat| deadline_at(ap, t) implies min is Some && min.unwrap() as nat <= t by {}
            assert forall |j: int, t: nat| 0 <= j < i + 1 && #[trigger] deadline_at(rows@[j]@, t) implies min is Some && min.unwrap() as nat <= t by {
                if j < i {
                    assert(deadline_at(rows@[j]@, t));
                }
            }
            if min is Some {
                let m = min.unwrap() as nat;
                if before is Some && m == before.unwrap() as nat {
                    let j = choose |j: int| 0 <= j < i && deadline_at(#[trigger] rows@[j]@, m);
                    assert(deadline_at(rows@[j]@, m));
                } else {
                    assert(deadline_at(rows@[i as int]@, m));
                }
            }
        }
        i += 1;
    }
    proof {
        let d = fold_by(rows@, obj_key(), obj_val());
        lemma_fold_dom(rows@, obj_key(), obj_val());
        lemma_fold_distinct(rows@, obj_key(), obj_val());
        assert forall |t: nat| objects_deadline(d, t) implies exists |j: int| 0 <= j < rows@.len() && #[trigger] deadline_at(rows@[j]@, t) by {
            let id = choose |id: Seq<char>| #[trigger] d.contains_key(id) && deadline_at(d[id], t);
            assert(mentions(rows@, obj_key(), id));
            let j = choose |j: int| 0 <= j < rows@.len() && #[trigger] obj_key()(rows@[j]) == id;
            assert(d[obj_key()(rows@[j])] == obj_val()(rows@[j]));
            assert(deadline_at(rows@[j]@, t));
        }
        assert forall |j: int, t: nat| 0 <= j < rows@.len() && #[trigger] deadline_at(rows@[j]@, t) implies objects_deadline(d, t) by {
            assert(d.contains_key(obj_key()(rows@[j])));
            assert(d[obj_key()(rows@[j])] == obj_val()(rows@[j]));
        }
    }
    min
}

/// The least next run of the schedule rows, which fold to the schedules.
fn schedules_next(rows: &Vec<Schedule>) -> (r: Option<u64>)
    requires distinct_by(rows@, sched_key()),
    ensures
        match r {
            Some(d) => schedules_deadline(fold_by(rows@, sched_key(), sched_val()), d as nat)
                && forall |u: nat| schedules_deadline(fold_by(rows@, sched_key(), sched_val()), u) ==> d as nat <= u,
            None => forall |t: nat| !schedules_deadline(fold_by(rows@, sched_key(), sched_val()), t),
        },
{
    let mut min: Option<u64> = None;
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows@.len(),
            match min {
                Some(m) => (exists |j: int| 0 <= j < i && #[trigger] rows@[j].next_run_at == m)
                    && forall |j: int| 0 <= j < i ==> m <= #[trigger] rows@[j].next_run_at,
                None => i == 0,
            },
        decreases rows@.len() - i,
    {
        let ghost before = min;
        min = note(min, rows[i].next_run_at);
        proof {
            if before is Some && min == before {
                let j = choose |j: int| 0 <= j < i && #[trigger] rows@[j].next_run_at == before.unwrap();
                assert(rows@[j].next_run_at == min.unwrap());
            } else {
                assert(rows@[i as int].next_run_at == min.unwrap());
            }
        }
        i += 1;
    }
    proof {
        let c = fold_by(rows@, sched_key(), sched_val());
        lemma_fold_dom(rows@, sched_key(), sched_val());
        lemma_fold_distinct(rows@, sched_key(), sched_val());
        assert forall |t: nat| schedules_deadline(c, t) implies exists |j: int| 0 <= j < rows@.len() && #[trigger] rows@[j].next_run_at as nat == t by {
            let id = choose |id: Seq<char>| #[trigger] c.contains_key(id) && c[id].next_run_at as nat == t;
            assert(mentions(rows@, sched_key(), id));
            let j = choose |j: int| 0 <= j < rows@.len() && #[trigger] sched_key()(rows@[j]) == id;
            assert(c[sched_key()(rows@[j])] == sched_val()(rows@[j]));
            assert(rows@[j].next_run_at as nat == t);
        }
        assert forall |j: int| 0 <= j < rows@.len() implies schedules_deadline(c, #[trigger] rows@[j].next_run_at as nat) by {
            assert(c.contains_key(sched_key()(rows@[j])));
            assert(c[sched_key()(rows@[j])] == sched_val()(rows@[j]));
        }
    }
    min
}

/// A schedule due at `now`, if any: the first row whose next run has come.
/// A fire's decision: `None` is a schedule's document with nothing due,
/// which is swept unchanged so its key can be collected.
pub fn schedule_due(s: &State, now: u64) -> (r: Option<usize>)
    requires s.wf(),
    ensures
        match r {
            Some(i) => i < s.schedules@.len() && s.schedules@[i as int].next_run_at <= now
                && s@.schedules.contains_key(s.schedules@[i as int].id@) && s@.schedules[s.schedules@[i as int].id@] == s.schedules@[i as int]@,
            None => schedules_idle(now as nat, s@.schedules),
        },
{
    let mut i: usize = 0;
    while i < s.schedules.len()
        invariant
            s.wf(),
            i <= s.schedules@.len(),
            forall |j: int| 0 <= j < i ==> #[trigger] s.schedules@[j].next_run_at > now,
        decreases s.schedules@.len() - i,
    {
        if s.schedules[i].next_run_at <= now {
            proof { s.lemma_schedule_at(i as int); }
            return Some(i);
        }
        i += 1;
    }
    proof {
        let c = fold_by(s.schedules@, sched_key(), sched_val());
        lemma_fold_dom(s.schedules@, sched_key(), sched_val());
        lemma_fold_distinct(s.schedules@, sched_key(), sched_val());
        assert forall |id: Seq<char>| #[trigger] c.contains_key(id) implies c[id].next_run_at > now by {
            assert(mentions(s.schedules@, sched_key(), id));
            let j = choose |j: int| 0 <= j < s.schedules@.len() && #[trigger] sched_key()(s.schedules@[j]) == id;
            assert(c[sched_key()(s.schedules@[j])] == sched_val()(s.schedules@[j]));
        }
    }
    None
}

/// The least deadline of a state: of its objects and of its schedules.
pub fn next_deadline(s: &State) -> (r: Option<u64>)
    requires s.wf(),
    ensures
        match r {
            Some(d) => is_next(strip(s@), d as nat),
            None => forall |t: nat| !has_deadline(strip(s@), t),
        },
{
    let a = objects_next(&s.objects);
    let b = schedules_next(&s.schedules);
    let r = match (a, b) {
        (None, None) => None,
        (Some(x), None) => Some(x),
        (None, Some(y)) => Some(y),
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    };
    proof {
        let d = strip(s@);
        assert(d.objects == fold_by(s.objects@, obj_key(), obj_val()));
        assert(d.schedules == fold_by(s.schedules@, sched_key(), sched_val()));
    }
    r
}

// ---------------------------------------------------------------------------
// The sweep
// ---------------------------------------------------------------------------

/// Fire what is due in a document at `now`: deadlines, leases, retries, one
/// object at a time. Returns whether anything fired. After it, nothing in
/// the document is due at `now`; if nothing fired, the document is as it was.
pub fn sweep(s: &mut State, now: u64, retry_timeout: u64) -> (did: bool)
    requires pre(*old(s), now, retry_timeout),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        swept_by(now as nat, old(s)@, final(s)@, did),
{
    let ghost a = s@;
    proof { lemma_reach_refl(now as nat, a); }
    let mut ids: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < s.objects.len()
        invariant
            i <= s.objects@.len(),
            ids@.len() == i,
            forall |j: int| 0 <= j < i ==> #[trigger] ids@[j]@ == s.objects@[j].id@,
        decreases s.objects@.len() - i,
    {
        ids.push(clone_string(&s.objects[i].id));
        i += 1;
    }
    proof {
        lemma_fold_dom(s.objects@, obj_key(), obj_val());
        assert forall |id: Seq<char>| #[trigger] a.objects.contains_key(id) implies exists |j: int| 0 <= j < ids@.len() && #[trigger] ids@[j]@ == id by {
            assert(mentions(s.objects@, obj_key(), id));
            let j = choose |j: int| 0 <= j < s.objects@.len() && #[trigger] obj_key()(s.objects@[j]) == id;
            assert(ids@[j]@ == id);
        }
    }
    let mut did = false;
    let mut k: usize = 0;
    while k < ids.len()
        invariant
            k <= ids@.len(),
            s.wf(),
            inv(now as nat, s@),
            reach(now as nat, a, s@),
            s@.schedules == a.schedules,
            s@.objects.dom() == a.objects.dom(),
            now <= MAX_TIME,
            0 < retry_timeout <= MAX_TIME,
            forall |j: int| 0 <= j < k && s@.objects.contains_key(#[trigger] ids@[j]@) ==> cleared(s@.objects[ids@[j]@], now as nat),
            !did ==> s@ == a,
            forall |id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> exists |j: int| 0 <= j < ids@.len() && #[trigger] ids@[j]@ == id,
        decreases ids@.len() - k,
    {
        let id = &ids[k];
        let ghost s0 = s@;
        let due_p = match s.find_object(id) {
            Some(i) => {
                proof { s.lemma_object_at(i as int); }
                let pending = match s.objects[i].state { PromiseState::Pending => true, _ => false };
                pending && s.objects[i].timeout_at <= now
            }
            None => false,
        };
        s.process_promise_timeout(&PromiseTimeoutReq { id: clone_string(id) }, now, retry_timeout);
        let ghost s1 = s@;
        proof { lemma_reach_step(now as nat, a, s0, s1); }
        let due_l = match s.find_object(id) {
            Some(i) => {
                proof { s.lemma_object_at(i as int); }
                let p = &s.objects[i];
                let pending = match p.state { PromiseState::Pending => true, _ => false };
                match &p.task {
                    Some(t) => match t.lease_timeout_at {
                        Some(d) => {
                            let acquired = match t.state { TaskState::Acquired => true, _ => false };
                            acquired && d <= now && pending && p.timeout_at > now
                        }
                        None => false,
                    },
                    None => false,
                }
            }
            None => false,
        };
        s.process_lease_timeout(&TaskLeaseTimeoutReq { id: clone_string(id) }, now, retry_timeout);
        let ghost s2 = s@;
        proof { lemma_reach_step(now as nat, a, s1, s2); }
        let due_r = match s.find_object(id) {
            Some(i) => {
                proof { s.lemma_object_at(i as int); }
                let p = &s.objects[i];
                let pending = match p.state { PromiseState::Pending => true, _ => false };
                match &p.task {
                    Some(t) => match t.retry_timeout_at {
                        Some(d) => {
                            let tpending = match t.state { TaskState::Pending => true, _ => false };
                            tpending && d <= now && pending && p.timeout_at > now
                        }
                        None => false,
                    },
                    None => false,
                }
            }
            None => false,
        };
        s.process_retry_timeout(&TaskRetryTimeoutReq { id: clone_string(id) }, now, retry_timeout);
        let ghost s3 = s@;
        proof { lemma_reach_step(now as nat, a, s2, s3); }
        if due_p || due_l || due_r {
            did = true;
        }
        proof {
            let x = id@;
            lemma_swept_object(now as nat, s0, s1, s2, s3, x, retry_timeout as nat);
            assert(s3.objects.dom() =~= a.objects.dom());
            if !(due_p || due_l || due_r) {
                // nothing fired: each step left the object as it was
                reveal(inv);
                if s0.objects.contains_key(x) {
                    let p0 = s0.objects[x];
                    assert(p0.project(now as nat) == p0);
                    assert(s1.objects =~= s0.objects);
                    assert(!lease_due(p0, now as nat));
                    assert(s2.objects =~= s0.objects);
                    assert(!retry_due(p0, now as nat));
                    assert(s3.objects =~= s0.objects);
                } else {
                    assert(s3.objects =~= s0.objects);
                }
                assert(s3 == s0);
            }
        }
        k += 1;
    }
    proof {
        assert forall |id: Seq<char>| #[trigger] s@.objects.contains_key(id) implies cleared(s@.objects[id], now as nat) by {
            let j = choose |j: int| 0 <= j < ids@.len() && #[trigger] ids@[j]@ == id;
        }
    }
    did
}

// ---------------------------------------------------------------------------
// The drain
// ---------------------------------------------------------------------------

/// What a settled promise still owes: its callbacks and listeners.
struct Owed {
    awaited: String,
    callbacks: Vec<String>,
    listeners: Vec<String>,
}

fn clone_strings(v: &Vec<String>) -> (r: Vec<String>)
    ensures r.deep_view() == v.deep_view(),
{
    let mut r: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@.len() == i, forall |j: int| 0 <= j < i ==> #[trigger] r@[j]@ == v@[j]@,
        decreases v@.len() - i,
    {
        r.push(clone_string(&v[i]));
        i += 1;
    }
    assert(r.deep_view() =~= v.deep_view());
    r
}

/// Discharge every settled promise's callbacks and listeners, then fire
/// every retry that is due, until nothing is owed or the round limit is
/// reached. Every step is a kernel step at `now`.
pub fn drain(s: &mut State, now: u64, retry_timeout: u64)
    requires pre(*old(s), now, retry_timeout),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        drained(now as nat, old(s)@, final(s)@),
{
    proof { lemma_reach_refl(now as nat, old(s)@); }
    let mut rounds: u64 = 0;
    while rounds <= 64
        invariant
            s.wf(),
            inv(now as nat, s@),
            reach(now as nat, old(s)@, s@),
            s@.schedules == old(s)@.schedules,
            s@.objects.dom() == old(s)@.objects.dom(),
            now <= MAX_TIME,
            0 < retry_timeout <= MAX_TIME,
        decreases 65 - rounds,
    {
        rounds += 1;
        let mut did = false;
        let mut owed: Vec<Owed> = Vec::new();
        let mut i: usize = 0;
        while i < s.objects.len()
            invariant i <= s.objects@.len(),
            decreases s.objects@.len() - i,
        {
            let p = &s.objects[i];
            let pending = match p.state { PromiseState::Pending => true, _ => false };
            if !pending && (p.callbacks.len() > 0 || p.listeners.len() > 0) {
                owed.push(Owed { awaited: clone_string(&p.id), callbacks: clone_strings(&p.callbacks), listeners: clone_strings(&p.listeners) });
            }
            i += 1;
        }
        let mut o: usize = 0;
        while o < owed.len()
            invariant
                o <= owed@.len(),
                s.wf(), inv(now as nat, s@), reach(now as nat, old(s)@, s@), s@.schedules == old(s)@.schedules, s@.objects.dom() == old(s)@.objects.dom(), now <= MAX_TIME, 0 < retry_timeout <= MAX_TIME,
            decreases owed@.len() - o,
        {
            let mut c: usize = 0;
            while c < owed[o].callbacks.len()
                invariant
                    o < owed@.len(),
                    c <= owed@[o as int].callbacks@.len(),
                    s.wf(), inv(now as nat, s@), reach(now as nat, old(s)@, s@), s@.schedules == old(s)@.schedules, s@.objects.dom() == old(s)@.objects.dom(), now <= MAX_TIME, 0 < retry_timeout <= MAX_TIME,
                decreases owed@[o as int].callbacks@.len() - c,
            {
                let ghost b = s@;
                let req = PromiseRegisterCallbackReq { awaited: clone_string(&owed[o].awaited), awaiter: clone_string(&owed[o].callbacks[c]) };
                s.process_callback(&req, now, retry_timeout);
                proof {
                    assert(inv(now as nat, s@));
                    assert(legal(now as nat, b, s@));
                    assert(kstep(now as nat, b, s@));
                    lemma_reach_step(now as nat, old(s)@, b, s@);
                }
                did = true;
                c += 1;
            }
            let mut l: usize = 0;
            while l < owed[o].listeners.len()
                invariant
                    o < owed@.len(),
                    l <= owed@[o as int].listeners@.len(),
                    s.wf(), inv(now as nat, s@), reach(now as nat, old(s)@, s@), s@.schedules == old(s)@.schedules, s@.objects.dom() == old(s)@.objects.dom(), now <= MAX_TIME, 0 < retry_timeout <= MAX_TIME,
                decreases owed@[o as int].listeners@.len() - l,
            {
                let ghost b = s@;
                let req = PromiseRegisterListenerReq { awaited: clone_string(&owed[o].awaited), address: clone_string(&owed[o].listeners[l]) };
                s.process_listener(&req, now, retry_timeout);
                proof { lemma_reach_step(now as nat, old(s)@, b, s@); }
                did = true;
                l += 1;
            }
            o += 1;
        }
        let mut due: Vec<String> = Vec::new();
        let mut i: usize = 0;
        while i < s.objects.len()
            invariant i <= s.objects@.len(),
            decreases s.objects@.len() - i,
        {
            let p = &s.objects[i];
            let pending = match p.state { PromiseState::Pending => true, _ => false };
            let task_due = match &p.task {
                Some(t) => match t.retry_timeout_at {
                    Some(d) => { let tp = match t.state { TaskState::Pending => true, _ => false }; tp && d <= now }
                    None => false,
                },
                None => false,
            };
            if pending && task_due {
                due.push(clone_string(&p.id));
            }
            i += 1;
        }
        let mut d: usize = 0;
        while d < due.len()
            invariant
                d <= due@.len(),
                s.wf(), inv(now as nat, s@), reach(now as nat, old(s)@, s@), s@.schedules == old(s)@.schedules, s@.objects.dom() == old(s)@.objects.dom(), now <= MAX_TIME, 0 < retry_timeout <= MAX_TIME,
            decreases due@.len() - d,
        {
            let ghost b = s@;
            s.process_retry_timeout(&TaskRetryTimeoutReq { id: clone_string(&due[d]) }, now, retry_timeout);
            proof {
                lemma_reach_step(now as nat, old(s)@, b, s@);
                assert(s@.objects.dom() =~= b.objects.dom());
            }
            did = true;
            d += 1;
        }
        if !did {
            return;
        }
    }
}

} // verus!
