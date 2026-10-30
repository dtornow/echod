//! The schedule's firing, simulated.
//!
//! The kernel's `processSchedule` fires every due occurrence and then moves
//! the schedule, in one step (`spec_fire`). The Abstract claims no atomicity
//! across objects: it has `ScheduleFire`, one occurrence's promise created if
//! absent, and `ScheduleAdvance`, the schedule moved past an occurrence whose
//! promise exists. The kernel step is a run of those: a fire for each
//! occurrence whose promise is absent when the kernel reaches it, nothing for
//! one already present (the kernel leaves it as it is, and so does an
//! Abstract run with no action on it), then one advance past the last.

use vstd::prelude::*;

use echod_abstract::internal as aint;
use echod_abstract::state as abs_state;
use echod_abstract::state::{AEffect, AObject, AState, spec_apply_all, spec_apply_effect, spec_find_object, spec_find_schedule};
use echod_abstract::types as abs;
use echod_kernel::external as kext;
use echod_kernel::internal as kint;
use echod_kernel::object as kobject;
use echod_kernel::store::AState as KState;
use echod_kernel::tags as ktags;
use echod_kernel::types as kernel;
use echod_kernel::types::{AOccurrence, APromise, ASchedule};

use crate::actions::*;
use crate::bridge::*;
use crate::promise_sim::{lemma_create_absent, promise_create_req};
use crate::read_sim::*;
use crate::relation::*;
use crate::*;

verus! {

pub open spec fn occurrence(o: AOccurrence) -> abs::AOccurrence {
    abs::AOccurrence { at: o.at, promise_id: ident(o.promise_id) }
}

pub open spec fn fire_req(sid: Chars, o: AOccurrence) -> abs::AScheduleFireReq {
    abs::AScheduleFireReq { schedule: ident(sid), occurrence: occurrence(o) }
}

pub open spec fn advance_req(sid: Chars, o: AOccurrence, next: u64) -> abs::AScheduleAdvanceReq {
    abs::AScheduleAdvanceReq { schedule: ident(sid), occurrence: occurrence(o), next_run_at: next }
}

pub open spec fn canonical_occurrences(occs: Seq<AOccurrence>) -> bool {
    forall|j: int| 0 <= j < occs.len() ==> canonical(#[trigger] occs[j].promise_id)
}

/// Every occurrence is one the schedule owes, and none is in the future.
pub open spec fn occurrences_due(c: ASchedule, occs: Seq<AOccurrence>, now: u64) -> bool {
    forall|j: int| 0 <= j < occs.len() ==> c.next_run_at <= #[trigger] occs[j].at && occs[j].at <= now
}

/// The Abstract fires the kernel's first `j` occurrences owe: one for each
/// whose promise the kernel finds absent.
pub open spec fn fire_actions(k: KState, sid: Chars, c: ASchedule, occs: Seq<AOccurrence>, now: u64, j: int) -> Seq<AbsInternal>
    decreases j,
{
    if j <= 0 {
        Seq::empty()
    } else {
        let before = kint::fire_fold(now as nat, k, c, occs, j - 1);
        let acts = fire_actions(k, sid, c, occs, now, j - 1);
        if before.objects.contains_key(occs[j - 1].promise_id) {
            acts
        } else {
            acts.push(AbsInternal::ScheduleFire(fire_req(sid, occs[j - 1])))
        }
    }
}

/// The create an occurrence stands for, on both sides.
pub proof fn lemma_occ_req(c: ASchedule, o: AOccurrence, now: u64)
    requires
        canonical(c.id),
        canonical(o.promise_id),
        o.at <= now,
        now <= kernel::MAX_TIME,
        c.promise_timeout <= kernel::MAX_TIME,
    ensures promise_create_req(kint::occ_req(c, o)) == aint::occurrence_create_req(schedule(c), occurrence(o)),
{
    lemma_stamp(c.promise_tags, c.id, o.promise_id);
    assert(o.at + c.promise_timeout <= u64::MAX);
}

/// One occurrence fired on related states: the kernel's `fire_step` is the
/// Abstract `ScheduleFire` when the promise is absent, and nothing otherwise.
pub proof fn lemma_fire_step_sim(k: KState, a: AState, sid: Chars, c: ASchedule, o: AOccurrence, now: u64, rt: u64)
    requires
        doc_related(k, a),
        canonical(sid),
        canonical(o.promise_id),
        k.schedules.contains_key(sid),
        k.schedules[sid] == c,
        c.next_run_at <= o.at,
        o.at <= now,
        now <= kernel::MAX_TIME,
        c.promise_timeout <= kernel::MAX_TIME,
    ensures
        !k.objects.contains_key(o.promise_id) ==> doc_related(
            kint::fire_step(now as nat, k, c, o),
            internal_step(a, AbsInternal::ScheduleFire(fire_req(sid, o)), now, rt)),
        k.objects.contains_key(o.promise_id) ==> kint::fire_step(now as nat, k, c, o) == k,
{
    if !k.objects.contains_key(o.promise_id) {
        let pid = o.promise_id;
        assert(spec_find_schedule(a.schedules, ident(sid)) == Some(schedule(c)));
        assert(c.id == sid);
        assert(aint::occurrence_due(schedule(c), occurrence(o), now));
        lemma_read_absent(k, a, pid, o.at);
        lemma_occ_req(c, o, now);
        let req = kint::occ_req(c, o);
        let made = abs_state::spec_create_promise_effects(promise_create_req(req), o.at);
        assert(aint::schedule_fire_semantics(a, fire_req(sid, o), now) == Seq::<AEffect>::empty() + made);
        assert(Seq::<AEffect>::empty() + made =~= made);
        lemma_create_absent(k, a, req, o.at);
        assert(kint::fire_step(now as nat, k, c, o)
            == KState { objects: k.objects.insert(pid, kobject::spec_create(req, o.at as nat)), ..k });
    }
}

/// The first `j` occurrences fired: related to the Abstract run of their
/// fires; the schedules untouched; every fired occurrence's promise present.
pub proof fn lemma_fire_fold_sim(k: KState, a: AState, sid: Chars, c: ASchedule, occs: Seq<AOccurrence>, now: u64, rt: u64, j: int)
    requires
        doc_related(k, a),
        canonical(sid),
        canonical_occurrences(occs),
        occurrences_due(c, occs, now),
        k.schedules.contains_key(sid),
        k.schedules[sid] == c,
        now <= kernel::MAX_TIME,
        c.promise_timeout <= kernel::MAX_TIME,
        0 <= j <= occs.len(),
    ensures ({
        let kj = kint::fire_fold(now as nat, k, c, occs, j);
        &&& doc_related(kj, internal_run(a, fire_actions(k, sid, c, occs, now, j), now, rt))
        &&& kj.schedules == k.schedules
        &&& forall|i: int| 0 <= i < j ==> kj.objects.contains_key(#[trigger] occs[i].promise_id)
        &&& forall|x: Chars| k.objects.contains_key(x) ==> kj.objects.contains_key(x)
    }),
    decreases j,
{
    if j == 0 {
    } else {
        lemma_fire_fold_sim(k, a, sid, c, occs, now, rt, j - 1);
        let before = kint::fire_fold(now as nat, k, c, occs, j - 1);
        let acts = fire_actions(k, sid, c, occs, now, j - 1);
        let abefore = internal_run(a, acts, now, rt);
        let o = occs[j - 1];
        lemma_fire_step_sim(before, abefore, sid, c, o, now, rt);
        if !before.objects.contains_key(o.promise_id) {
            lemma_internal_run_push(a, acts, AbsInternal::ScheduleFire(fire_req(sid, o)), now, rt);
        }
    }
}

/// `processSchedule` as a run: the fires, then the advance past the last
/// occurrence.
pub proof fn lemma_spec_fire_sim(k: KState, a: AState, sid: Chars, occs: Seq<AOccurrence>, next: u64, now: u64, rt: u64)
    requires
        doc_related(k, a),
        canonical(sid),
        canonical_occurrences(occs),
        k.schedules.contains_key(sid),
        occs.len() > 0,
        occurrences_due(k.schedules[sid], occs, now),
        occs[occs.len() - 1].at < next,
        now <= kernel::MAX_TIME,
        k.schedules[sid].promise_timeout <= kernel::MAX_TIME,
    ensures ({
        let c = k.schedules[sid];
        let n = occs.len() as int;
        let acts = fire_actions(k, sid, c, occs, now, n).push(AbsInternal::ScheduleAdvance(advance_req(sid, occs[n - 1], next)));
        doc_related(kint::spec_fire(k, sid, occs, next, now as nat), internal_run(a, acts, now, rt))
    }),
{
    let c = k.schedules[sid];
    let n = occs.len() as int;
    let last = occs[n - 1];
    lemma_fire_fold_sim(k, a, sid, c, occs, now, rt, n);
    let k2 = kint::fire_fold(now as nat, k, c, occs, n);
    let acts = fire_actions(k, sid, c, occs, now, n);
    let a2 = internal_run(a, acts, now, rt);
    let adv = AbsInternal::ScheduleAdvance(advance_req(sid, last, next));
    lemma_internal_run_push(a, acts, adv, now, rt);
    // The advance is enabled: the last occurrence is due, ahead of `next`,
    // and its promise exists.
    assert(k2.schedules.contains_key(sid) && k2.schedules[sid] == c);
    assert(spec_find_schedule(a2.schedules, ident(sid)) == Some(schedule(c)));
    assert(k2.objects.contains_key(last.promise_id));
    lemma_related_contains(k2.objects, a2.objects, last.promise_id);
    let req = advance_req(sid, last, next);
    assert(aint::advance_enabled(a2, schedule(c), req, now));
    let c2 = ASchedule { last_run_at: Some(last.at), next_run_at: next, ..c };
    assert(canonical_schedule(c2));
    assert(schedule(c2) == aint::advanced_schedule(schedule(c), req));
    lemma_set_schedule(k2.schedules, a2.schedules, c2);
    lemma_apply_all_one(a2, AEffect::SetSchedule(schedule(c2)));
    assert(c2.id == sid);
    let kf = kint::spec_fire(k, sid, occs, next, now as nat);
    assert(kf.objects == k2.objects);
    assert(kf.schedules == k2.schedules.insert(sid, c2));
}

} // verus!
