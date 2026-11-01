//! The sweep and the drain, as functions of the document.
//!
//! `sweep` and `drain` in the kernel ensure they compute these. The lemmas
//! are what the specifications themselves guarantee: nothing is due after a
//! sweep, and the catalogue survives a chain of steps and a later clock.

use vstd::prelude::*;

use crate::internal_spec::*;
use crate::object::*;
use crate::properties::*;
use crate::state::*;
use crate::tags::OType;
use crate::types::*;

verus! {

/// A document, as the kernel sees it: an origin's objects, or a schedule's
/// row. The bucket holds either kind under one protocol; which a document
/// is, its name says (`is_sched`), and the shape invariant keeps the other
/// map empty.
#[cfg(verus_keep_ghost)]
pub struct Doc {
    pub objects: Map<Seq<char>, APromise>,
    pub schedules: Map<Seq<char>, ASchedule>,
}

pub open spec fn empty_doc() -> Doc {
    Doc { objects: Map::empty(), schedules: Map::empty() }
}

/// A document as a kernel state: nothing in the outbox.
pub open spec fn full(d: Doc) -> AState {
    AState { objects: d.objects, schedules: d.schedules, outbox: Map::empty() }
}

/// A kernel state as a document: the outbox dropped.
pub open spec fn strip(s: AState) -> Doc {
    Doc { objects: s.objects, schedules: s.schedules }
}

/// A kernel state's objects alone, and its schedules alone: what a fire
/// writes to the origin's document and to the schedule's.
pub open spec fn objects_only(s: AState) -> Doc {
    Doc { objects: s.objects, schedules: Map::empty() }
}

pub open spec fn schedules_only(s: AState) -> Doc {
    Doc { objects: Map::empty(), schedules: s.schedules }
}

/// An origin's document and a schedule's, loaded together for a fire.
pub open spec fn joint(o: Doc, c: Doc) -> AState {
    AState { objects: o.objects, schedules: c.schedules, outbox: Map::empty() }
}

// ---------------------------------------------------------------------------
// Deadlines
// ---------------------------------------------------------------------------

/// A pending promise that is not internal owes a timer at its deadline.
pub open spec fn promise_deadline(p: APromise) -> Option<nat> {
    if p.state == PromiseState::Pending && p.otype() != OType::Internal { Some(p.timeout_at as nat) } else { None }
}

pub open spec fn lease_deadline(p: APromise) -> Option<nat> {
    match p.task { Some(t) => crate::commit_spec::opt_nat(t.lease_timeout_at), None => None }
}

pub open spec fn retry_deadline(p: APromise) -> Option<nat> {
    match p.task { Some(t) => crate::commit_spec::opt_nat(t.retry_timeout_at), None => None }
}

pub open spec fn deadline_at(p: APromise, t: nat) -> bool {
    promise_deadline(p) == Some(t) || lease_deadline(p) == Some(t) || retry_deadline(p) == Some(t)
}

pub open spec fn objects_deadline(d: Map<Seq<char>, APromise>, t: nat) -> bool {
    exists |id: Seq<char>| #[trigger] d.contains_key(id) && deadline_at(d[id], t)
}

/// A schedule owes a timer at its next run.
pub open spec fn schedules_deadline(c: Map<Seq<char>, ASchedule>, t: nat) -> bool {
    exists |id: Seq<char>| #[trigger] c.contains_key(id) && c[id].next_run_at as nat == t
}

pub open spec fn has_deadline(d: Doc, t: nat) -> bool {
    objects_deadline(d.objects, t) || schedules_deadline(d.schedules, t)
}

/// `t` is the least deadline of the document.
pub open spec fn is_next(d: Doc, t: nat) -> bool {
    has_deadline(d, t) && forall |u: nat| has_deadline(d, u) ==> t <= u
}

/// Nothing in the object is due at `now`.
pub open spec fn cleared(p: APromise, now: nat) -> bool {
    forall |t: nat| deadline_at(p, t) ==> t > now
}

pub open spec fn objects_cleared(now: nat, d: Map<Seq<char>, APromise>) -> bool {
    forall |id: Seq<char>| #[trigger] d.contains_key(id) ==> cleared(d[id], now)
}

/// Nothing in the document is due at `now`: no object, and no schedule.
pub open spec fn no_due(now: nat, d: Doc) -> bool {
    &&& objects_cleared(now, d.objects)
    &&& forall |id: Seq<char>| #[trigger] d.schedules.contains_key(id) ==> d.schedules[id].next_run_at > now
}

pub proof fn lemma_no_due(now: nat, d: Doc)
    requires no_due(now, d),
    ensures forall |t: nat| has_deadline(d, t) ==> t > now,
{
    assert forall |t: nat| has_deadline(d, t) implies t > now by {
        if objects_deadline(d.objects, t) {
            let id = choose |id: Seq<char>| #[trigger] d.objects.contains_key(id) && deadline_at(d.objects[id], t);
            assert(cleared(d.objects[id], now));
        } else {
            let id = choose |id: Seq<char>| #[trigger] d.schedules.contains_key(id) && d.schedules[id].next_run_at as nat == t;
        }
    }
}

// ---------------------------------------------------------------------------
// Kernel steps, chained
// ---------------------------------------------------------------------------

/// What `drain` ensures: kernel steps at `now` that leave the schedules and
/// every object's key as they were. The system model's relation for the
/// steps after a handler or a fire.
pub open spec fn drained(now: nat, a: AState, b: AState) -> bool {
    &&& reach(now, a, b)
    &&& b.schedules == a.schedules
    &&& b.objects.dom() == a.objects.dom()
}

/// What `sweep` ensures: as `drained`, and nothing in the objects is due;
/// if nothing fired, the state is as it was.
pub open spec fn swept_by(now: nat, a: AState, b: AState, did: bool) -> bool {
    &&& drained(now, a, b)
    &&& objects_cleared(now, b.objects)
    &&& !did ==> b == a
}

/// No schedule is due at `now`: what `schedule_due` answers `None` with.
pub open spec fn schedules_idle(now: nat, c: Map<Seq<char>, ASchedule>) -> bool {
    forall |id: Seq<char>| #[trigger] c.contains_key(id) ==> c[id].next_run_at > now
}

/// One kernel step at `now`: what every handler and internal step ensures.
pub open spec fn kstep(now: nat, a: AState, b: AState) -> bool {
    inv(now, b) && legal(now, a, b)
}

/// A chain of kernel steps at `now`.
pub open spec fn chain(now: nat, s: Seq<AState>) -> bool {
    s.len() >= 1 && forall |i: int| 0 <= i < s.len() - 1 ==> #[trigger] kstep(now, s[i], s[i + 1])
}

/// `b` is what some sequence of kernel steps at `now` makes of `a`.
pub open spec fn reach(now: nat, a: AState, b: AState) -> bool {
    exists |s: Seq<AState>| #[trigger] chain(now, s) && s[0] == a && s.last() == b
}

pub proof fn lemma_reach_refl(now: nat, a: AState)
    ensures reach(now, a, a),
{
    let w: Seq<AState> = seq![a];
    assert(chain(now, w) && w[0] == a && w.last() == a);
}

pub proof fn lemma_reach_step(now: nat, a: AState, b: AState, c: AState)
    requires reach(now, a, b), kstep(now, b, c),
    ensures reach(now, a, c),
{
    let s = choose |s: Seq<AState>| #[trigger] chain(now, s) && s[0] == a && s.last() == b;
    let w = s.push(c);
    assert forall |i: int| 0 <= i < w.len() - 1 implies #[trigger] kstep(now, w[i], w[i + 1]) by {
        if i < s.len() - 1 {
            assert(kstep(now, s[i], s[i + 1]));
        } else {
            assert(w[i] == s.last());
        }
    }
    assert(chain(now, w) && w[0] == a && w.last() == c);
}

pub proof fn lemma_reach_inv(now: nat, a: AState, b: AState)
    requires reach(now, a, b), inv(now, a),
    ensures inv(now, b),
{
    let s = choose |s: Seq<AState>| #[trigger] chain(now, s) && s[0] == a && s.last() == b;
    if s.len() == 1 {
        assert(b == a);
    } else {
        let i: int = s.len() - 2;
        assert(kstep(now, s[i], s[i + 1]));
        assert(s[i + 1] == b);
    }
}

/// The catalogue at a later instant. Three entries mention `now`: two say
/// the stamps are not in the future, one that a suspended task holds a
/// rung unless its promise is dead; none is lost as time passes.
pub proof fn lemma_inv_at(t0: nat, t: nat, s: AState)
    requires
        inv(t0, s),
        t0 <= t,
    ensures inv(t, s),
{
    reveal(inv);
    assert(well_formed_promise_created_at_lte_timeout_at(t, s)) by { assert(well_formed_promise_created_at_lte_timeout_at(t0, s)); }
    assert(well_formed_promise_pending_created_before_deadline(t, s)) by { assert(well_formed_promise_pending_created_before_deadline(t0, s)); }
    assert(well_formed_promise_settled_at_lte_timeout_at(t, s)) by { assert(well_formed_promise_settled_at_lte_timeout_at(t0, s)); }
    assert(well_formed_promise_created_at_lte_settled_at(t, s)) by { assert(well_formed_promise_created_at_lte_settled_at(t0, s)); }
    assert(well_formed_promise_settled_at_iff_not_pending(t, s)) by { assert(well_formed_promise_settled_at_iff_not_pending(t0, s)); }
    assert(well_formed_promise_pending_has_no_value(t, s)) by { assert(well_formed_promise_pending_has_no_value(t0, s)); }
    assert(well_formed_promise_deadline_verdict_matches_timer_tag(t, s)) by { assert(well_formed_promise_deadline_verdict_matches_timer_tag(t0, s)); }
    assert(well_formed_promise_deadline_settlement_has_no_value(t, s)) by { assert(well_formed_promise_deadline_settlement_has_no_value(t0, s)); }
    assert(well_formed_promise_timer_not_targeted(t, s)) by { assert(well_formed_promise_timer_not_targeted(t0, s)); }
    assert(well_formed_promise_timedout_is_server_owned(t, s)) by { assert(well_formed_promise_timedout_is_server_owned(t0, s)); }
    assert(well_formed_promise_callbacks_unique(t, s)) by { assert(well_formed_promise_callbacks_unique(t0, s)); }
    assert(well_formed_promise_listeners_unique(t, s)) by { assert(well_formed_promise_listeners_unique(t0, s)); }
    assert(well_formed_promise_obligations_require_external(t, s)) by { assert(well_formed_promise_obligations_require_external(t0, s)); }
    assert(well_formed_promise_awaiter_is_not_self(t, s)) by { assert(well_formed_promise_awaiter_is_not_self(t0, s)); }
    assert(well_formed_promise_callbacks_same_origin(t, s)) by { assert(well_formed_promise_callbacks_same_origin(t0, s)); }
    assert(well_formed_promise_created_at_lte_now(t, s)) by { assert(well_formed_promise_created_at_lte_now(t0, s)); }
    assert(well_formed_promise_settled_at_lte_now(t, s)) by { assert(well_formed_promise_settled_at_lte_now(t0, s)); }
    assert(well_formed_task_acquired_iff_has_pid(t, s)) by { assert(well_formed_task_acquired_iff_has_pid(t0, s)); }
    assert(well_formed_task_acquired_iff_has_ttl(t, s)) by { assert(well_formed_task_acquired_iff_has_ttl(t0, s)); }
    assert(well_formed_task_acquired_iff_has_lease_timeout_at(t, s)) by { assert(well_formed_task_acquired_iff_has_lease_timeout_at(t0, s)); }
    assert(well_formed_task_pending_iff_has_retry_timeout_at(t, s)) by { assert(well_formed_task_pending_iff_has_retry_timeout_at(t0, s)); }
    assert(well_formed_task_fulfilled_is_cleared(t, s)) by { assert(well_formed_task_fulfilled_is_cleared(t0, s)); }
    assert(well_formed_task_suspended_is_cleared(t, s)) by { assert(well_formed_task_suspended_is_cleared(t0, s)); }
    assert(well_formed_task_halted_is_cleared(t, s)) by { assert(well_formed_task_halted_is_cleared(t0, s)); }
    assert(well_formed_task_suspended_has_no_resumes(t, s)) by { assert(well_formed_task_suspended_has_no_resumes(t0, s)); }
    assert(well_formed_task_resumes_unique(t, s)) by { assert(well_formed_task_resumes_unique(t0, s)); }
    assert(well_formed_task_acquired_version_positive(t, s)) by { assert(well_formed_task_acquired_version_positive(t0, s)); }
    assert(well_formed_schedule_promise_tags_not_timer_targeted(t, s)) by { assert(well_formed_schedule_promise_tags_not_timer_targeted(t0, s)); }
    assert(well_formed_schedule_created_at_lte_next_run_at(t, s)) by { assert(well_formed_schedule_created_at_lte_next_run_at(t0, s)); }
    assert(well_formed_schedule_created_at_lte_last_run_at(t, s)) by { assert(well_formed_schedule_created_at_lte_last_run_at(t0, s)); }
    assert(well_formed_schedule_last_run_at_lt_next_run_at(t, s)) by { assert(well_formed_schedule_last_run_at_lt_next_run_at(t0, s)); }
    assert(consistent_task_iff_kind_task(t, s)) by { assert(consistent_task_iff_kind_task(t0, s)); }
    assert(consistent_settled_promise_has_fulfilled_task(t, s)) by { assert(consistent_settled_promise_has_fulfilled_task(t0, s)); }
    assert(consistent_callback_awaiter_is_targeted(t, s)) by { assert(consistent_callback_awaiter_is_targeted(t0, s)); }
    assert(consistent_outbox_execute_names_existing_task(t, s)) by { assert(consistent_outbox_execute_names_existing_task(t0, s)); }
    assert(consistent_outbox_never_ahead(t, s)) by { assert(consistent_outbox_never_ahead(t0, s)); }
    assert(consistent_outbox_execute_address_is_target_tag(t, s)) by { assert(consistent_outbox_execute_address_is_target_tag(t0, s)); }
    assert(consistent_outbox_unblock_names_settled_promise(t, s)) by { assert(consistent_outbox_unblock_names_settled_promise(t0, s)); }
    assert(consistent_settled_task_promise_settled(t, s)) by { assert(consistent_settled_task_promise_settled(t0, s)); }
    assert(consistent_suspended_task_holds_rung(t, s)) by {
        assert forall |id: Seq<char>| #[trigger] s.objects.contains_key(id) implies consistent_suspended_task_holds_rung_at(t, s, id) by {
            assert(consistent_suspended_task_holds_rung_at(t0, s, id));
            let p = s.objects[id];
            if p.project_promise(t0).state != PromiseState::Pending {
                assert(p.project_promise(t).state != PromiseState::Pending);
            }
        }
    }
}

/// The catalogue on the objects alone.
pub proof fn lemma_inv_full(now: nat, s: AState)
    requires inv(now, s),
    ensures inv(now, full(strip(s))),
{
    reveal(inv);
}

/// The catalogue holds of a state's objects alone, and of its schedules
/// alone: no entry crosses from one to the other.
pub proof fn lemma_inv_objects_only(now: nat, s: AState)
    requires inv(now, s),
    ensures inv(now, full(objects_only(s))),
{
    reveal(inv);
}

pub proof fn lemma_inv_schedules_only(now: nat, s: AState)
    requires inv(now, s),
    ensures inv(now, full(schedules_only(s))),
{
    reveal(inv);
}

/// And of an origin's objects beside a schedule's row.
pub proof fn lemma_inv_joint(now: nat, o: Doc, c: Doc)
    requires inv(now, full(o)), inv(now, full(c)), o.schedules == Map::<Seq<char>, ASchedule>::empty(), c.objects == Map::<Seq<char>, APromise>::empty(),
    ensures inv(now, joint(o, c)),
{
    reveal(inv);
}

/// What one object looks like after the three sweeper steps at `now`,
/// given the catalogue: nothing in it is due.
pub proof fn lemma_swept_object(now: nat, s0: AState, s1: AState, s2: AState, s3: AState, id: Seq<char>, rt: nat)
    requires
        inv(now, s0), inv(now, s1), inv(now, s2), inv(now, s3),
        s1.objects == promise_timeout_objects(s0, id, now),
        s2.objects == lease_timeout_objects(s1, id, now),
        s3.objects == retry_timeout_objects(s2, id, now, rt),
        0 < rt <= MAX_TIME, now <= MAX_TIME,
    ensures
        s3.objects.contains_key(id) ==> cleared(s3.objects[id], now),
        forall |x: Seq<char>| x != id ==> (s3.objects.contains_key(x) <==> s0.objects.contains_key(x)) && (s0.objects.contains_key(x) ==> s3.objects[x] == s0.objects[x]),
        s3.objects.dom() == s0.objects.dom(),
{
    reveal(inv);
    if s0.objects.contains_key(id) {
        let p0 = s0.objects[id];
        let p1 = s1.objects[id];
        let p2 = s2.objects[id];
        let p3 = s3.objects[id];
        assert(p1 == p0.project(now));
        // after projection: pending means the deadline is ahead; settled means the task is fulfilled and cleared
        assert(p1.state == PromiseState::Pending ==> p1.timeout_at > now);
        assert(p2.state == p1.state && p2.timeout_at == p1.timeout_at);
        assert(p3.state == p1.state && p3.timeout_at == p1.timeout_at);
        assert forall |t: nat| deadline_at(p3, t) implies t > now by {
            if promise_deadline(p3) == Some(t) {
                assert(t == p3.timeout_at as nat);
                assert(t > now);
            } else if lease_deadline(p3) == Some(t) {
                let t3 = p3.task.unwrap();
                assert(t3.lease_timeout_at is Some && t == t3.lease_timeout_at.unwrap() as nat);
                assert(t3.state == TaskState::Acquired);
                if p1.state != PromiseState::Pending {
                    assert(false);
                } else {
                    assert(!lease_due(p1, now));
                    assert(p2 == p1);
                    assert(!retry_due(p2, now) || p3.task.unwrap().lease_timeout_at == p2.task.unwrap().lease_timeout_at);
                    assert(t > now);
                }
            } else {
                let t3 = p3.task.unwrap();
                assert(t3.retry_timeout_at is Some && t == t3.retry_timeout_at.unwrap() as nat);
                assert(t3.state == TaskState::Pending);
                if p1.state != PromiseState::Pending {
                    assert(false);
                } else {
                    if retry_due(p2, now) {
                        // re-offered: the next offer on the task's grid, after `now`
                        // and at most `rt` ahead, and the sum fits
                        let t2 = p2.task.unwrap();
                        assert(t3 == t2.rearm(now, rt));
                        let due = crate::properties::opt_or_zero(t2.retry_timeout_at);
                        crate::object::lemma_next_offer(due, now, rt);
                        assert(now + rt <= 2 * (MAX_TIME as nat));
                        assert(t3.retry_timeout_at == Some(crate::object::next_offer(due, now, rt) as u64));
                        assert(t == crate::object::next_offer(due, now, rt));
                    } else {
                        if lease_due(p1, now) {
                            // reclaimed: its first offer is due at the lease's end, already passed
                            let end = p1.task.unwrap().lease_timeout_at.unwrap();
                            assert(p2.task.unwrap().retry_timeout_at == Some(end));
                            assert(retry_due(p2, now));
                            assert(false);
                        }
                    }
                    assert(t > now);
                }
            }
        }
    }
    assert(s3.objects.dom() =~= s0.objects.dom());
}


} // verus!
