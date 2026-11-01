//! Internal-step specifications: what a sweep computes, as a function of the document.

use vstd::prelude::*;

use crate::object::*;
use crate::properties::*;
use crate::spec::*;
use crate::state::*;
use crate::tags::*;
use crate::types::*;

verus! {

/// An occurrence of a schedule, as the kernel asks for it.
pub open spec fn occurrence_ok(c: ASchedule, o: AOccurrence, now: u64) -> bool {
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

/// `processLeaseTimeout`: a due lease returns the task to pending, its first
/// offer due at the lease's end (what a read already projects, `lapse`).
pub open spec fn lease_timeout_objects(a: AState, id: Seq<char>, now: nat) -> Map<Seq<char>, APromise> {
    if a.objects.contains_key(id) && lease_due(a.objects[id], now) {
        a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().release(a.objects[id].task.unwrap().lease_timeout_at.unwrap() as nat)))
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


// ---------------------------------------------------------------------------
// Shapes
// ---------------------------------------------------------------------------

/// Some occurrence among the first `k` expands to `x`.
pub open spec fn occ_touched(occs: Seq<AOccurrence>, k: int, x: Seq<char>) -> bool {
    exists|j: int| 0 <= j < k && #[trigger] occs[j].promise_id == x
}

pub open spec fn occ_of(occs: Seq<AOccurrence>, x: Seq<char>) -> bool {
    occ_touched(occs, occs.len() as int, x)
}

/// The create request an occurrence stands for: the template's tags,
/// stamped with the schedule and the promise's own lineage.
pub open spec fn occ_req(c: ASchedule, o: AOccurrence) -> APromiseCreateReq {
    APromiseCreateReq {
        id: o.promise_id,
        timeout_at: (o.at + c.promise_timeout) as u64,
        param: c.promise_param,
        tags: crate::tags::spec_stamp(c.promise_tags, c.id, o.promise_id),
    }
}

/// One occurrence fired: the object projected if it exists, else born of
/// the occurrence.
pub open spec fn fire_step(_now: nat, a: AState, c: ASchedule, o: AOccurrence) -> AState {
    let x = o.promise_id;
    if a.objects.contains_key(x) {
        a
    } else {
        with_objects(a, a.objects.insert(x, born_occurrence(c, o)))
    }
}

/// The first `k` occurrences fired, in order.
pub open spec fn fire_fold(now: nat, a: AState, c: ASchedule, occs: Seq<AOccurrence>, k: int) -> AState
    decreases k,
{
    if k <= 0 { a } else { fire_step(now, fire_fold(now, a, c, occs, k - 1), c, occs[k - 1]) }
}

/// `processSchedule` as a function: every occurrence fired, then the
/// schedule advanced; nothing when the schedule is absent or nothing is due.
pub open spec fn spec_fire(a: AState, sid: Seq<char>, occs: Seq<AOccurrence>, next: u64, now: nat) -> AState {
    if !a.schedules.contains_key(sid) || occs.len() == 0 {
        a
    } else {
        let c = a.schedules[sid];
        let a2 = fire_fold(now, a, c, occs, occs.len() as int);
        AState { schedules: a2.schedules.insert(sid, ASchedule { last_run_at: Some(occs[occs.len() - 1].at), next_run_at: next, ..c }), ..a2 }
    }
}

/// The occurrence's promise as the firing leaves it: created as of the
/// occurrence's own instant, as Lean's `fireOccurrence` creates it at `t`,
/// whenever the server gets to it. One whose deadline has passed by then is
/// stored pending, as Lean stores it; every read projects it, settled at that
/// deadline and created at the occurrence.
pub open spec fn born_occurrence(c: ASchedule, o: AOccurrence) -> APromise {
    spec_create(occ_req(c, o), o.at as nat)
}

/// What firing leaves at `x`: an existing object as it was, or a promise born
/// of one of the occurrences that expand to `x`.
pub open spec fn fire_shape(_now: nat, a: AState, b: AState, c: ASchedule, occs: Seq<AOccurrence>, x: Seq<char>) -> bool {
    &&& b.objects.contains_key(x)
    &&& a.objects.contains_key(x) ==> b.objects[x] == a.objects[x]
    &&& !a.objects.contains_key(x) ==> exists|j: int| 0 <= j < occs.len() && #[trigger] occs[j].promise_id == x
        && b.objects[x] == born_occurrence(c, occs[j])
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
                && b.objects[y] == m.with_task(m.task.unwrap().wake(x, crate::properties::opt_or_zero(a.objects[x].project(now).settled_at))))
        ||| (m.task is Some && m.task.unwrap().state != TaskState::Suspended && m.task.unwrap().state != TaskState::Fulfilled
                && b.objects[y] == m.with_task(m.task.unwrap().buffer(x)))
    }
}


} // verus!
