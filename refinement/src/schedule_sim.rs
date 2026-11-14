//! The three Schedule handlers, simulated.
//!
//! The Abstract create takes Lean's opaque `nextCron cron now` as a
//! witness; the kernel takes it as the request's `next_run_at`, computed by
//! the caller's cron engine. The simulation passes the one as the other.

use vstd::prelude::*;

use echod_abstract::schedule_spec as sspec;
use echod_abstract::state as abs_state;
use echod_abstract::state::{AEffect, AState, spec_apply_all, spec_apply_effect, spec_find_schedule};
use echod_abstract::types as abs;
use echod_kernel::external as kext;
use echod_kernel::store::AState as KState;
use echod_kernel::tags as ktags;
use echod_kernel::types as kernel;
use echod_kernel::types::ASchedule;

use crate::bridge::*;
use crate::read_sim::*;
use crate::relation::*;
use crate::*;

verus! {

pub open spec fn schedule_get_req(r: kernel::AScheduleGetReq) -> abs::AScheduleGetReq {
    abs::AScheduleGetReq { id: ident(r.id) }
}

pub open spec fn schedule_create_req(r: kernel::AScheduleCreateReq) -> abs::AScheduleCreateReq {
    abs::AScheduleCreateReq {
        id: ident(r.id),
        cron: text(r.cron),
        promise_id: ident(r.promise_id),
        promise_timeout: r.promise_timeout,
        promise_param: value(r.promise_param),
        promise_tags: tags(r.promise_tags),
        next_run_at: r.next_run_at,
    }
}

pub open spec fn schedule_delete_req(r: kernel::AScheduleDeleteReq) -> abs::AScheduleDeleteReq {
    abs::AScheduleDeleteReq { id: ident(r.id) }
}

/// What the kernel accepts of a schedule create.
pub open spec fn schedule_create_in_domain(r: kernel::AScheduleCreateReq, now: u64) -> bool {
    &&& canonical(r.id)
    &&& canonical(r.promise_id)
    &&& !ktags::timer_targeted(r.promise_tags)
    &&& r.promise_timeout <= kernel::MAX_TIME
    &&& r.next_run_at >= now
}

pub proof fn lemma_schedule_get_sim(k: KState, a: AState, req: kernel::AScheduleGetReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_schedule_get(k, req, now as nat);
        let r = sspec::spec_schedule_get_action(a, schedule_get_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& schedule_res(res) == r.response
    }),
{
    lemma_sched_related_contains(k.schedules, a.schedules, req.id);
}

pub proof fn lemma_schedule_create_sim(k: KState, a: AState, req: kernel::AScheduleCreateReq, now: u64)
    requires
        doc_related(k, a),
        schedule_create_in_domain(req, now),
    ensures ({
        let (k2, res) = kext::spec_schedule_create(k, req, now as nat);
        let r = sspec::spec_schedule_create_action(a, schedule_create_req(req), req.next_run_at, now, true);
        &&& doc_related(k2, r.next_state)
        &&& schedule_res(res) == r.response
    }),
{
    let areq = schedule_create_req(req);
    lemma_strip_identity(req.promise_tags);
    assert(abs::AScheduleCreateReq { promise_tags: abs::spec_strip_timer_target(areq.promise_tags), ..areq } == areq);
    lemma_timer_targeted(req.promise_tags);
    lemma_sched_related_contains(k.schedules, a.schedules, req.id);
    if k.schedules.contains_key(req.id) {
    } else {
        let c = kext::spec_new_schedule(req, now as nat);
        assert(schedule(c) == sspec::spec_new_schedule(areq, req.next_run_at, now));
        assert(canonical_schedule(c));
        lemma_set_schedule(k.schedules, a.schedules, c);
        lemma_apply_all_one(a, AEffect::SetSchedule(schedule(c)));
    }
}

pub proof fn lemma_schedule_delete_sim(k: KState, a: AState, req: kernel::AScheduleDeleteReq, now: u64)
    requires
        doc_related(k, a),
        canonical(req.id),
    ensures ({
        let (k2, res) = kext::spec_schedule_delete(k, req, now as nat);
        let r = sspec::spec_schedule_delete_action(a, schedule_delete_req(req), now, true);
        &&& doc_related(k2, r.next_state)
        &&& schedule_delete_res(res) == r.response
    }),
{
    lemma_sched_related_contains(k.schedules, a.schedules, req.id);
    if k.schedules.contains_key(req.id) {
        assert(spec_find_schedule(a.schedules, ident(req.id)) == Some(schedule(k.schedules[req.id])));
        lemma_delete_schedule(k.schedules, a.schedules, req.id);
        lemma_apply_all_one(a, AEffect::DeleteSchedule(ident(req.id)));
    }
}

} // verus!
