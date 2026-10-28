//! Pure ghost semantics for the four Abstract Schedule external actions.
//!
//! These definitions use only the Abstract state and writer effects. Reads
//! observe the immutable pre-state, and `spec_apply_all` commits the ordered
//! effects afterward. Lean's opaque `nextCron cron now` remains an explicit
//! witness supplied by the executable boundary.

use vstd::prelude::*;
use crate::state::*;
use crate::types::*;

verus! {

#[cfg(verus_keep_ghost)]
pub struct AScheduleActionResult {
    pub response: AScheduleRes,
    pub effects: Seq<AEffect>,
    pub next_state: AState,
}

#[cfg(verus_keep_ghost)]
pub struct AScheduleDeleteActionResult {
    pub response: AScheduleDeleteRes,
    pub effects: Seq<AEffect>,
    pub next_state: AState,
}

#[cfg(verus_keep_ghost)]
pub struct AScheduleSearchActionResult {
    pub response: AScheduleSearchRes,
    pub effects: Seq<AEffect>,
    pub next_state: AState,
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_schedule_finish(
    state: AState,
    response: AScheduleRes,
    effects: Seq<AEffect>,
) -> AScheduleActionResult {
    AScheduleActionResult {
        response,
        effects,
        next_state: spec_apply_all(state, effects),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_schedule_delete_finish(
    state: AState,
    response: AScheduleDeleteRes,
    effects: Seq<AEffect>,
) -> AScheduleDeleteActionResult {
    AScheduleDeleteActionResult {
        response,
        effects,
        next_state: spec_apply_all(state, effects),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_schedule_search_finish(
    state: AState,
    response: AScheduleSearchRes,
    effects: Seq<AEffect>,
) -> AScheduleSearchActionResult {
    AScheduleSearchActionResult {
        response,
        effects,
        next_state: spec_apply_all(state, effects),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_schedule_get_action(
    state: AState,
    req: AScheduleGetReq,
    _now: u64,
    _materialize: bool,
) -> AScheduleActionResult {
    match spec_find_schedule(state.schedules, req.id) {
        None => spec_schedule_finish(
            state,
            AScheduleRes { status: 404, schedule: None },
            Seq::empty(),
        ),
        Some(schedule) => spec_schedule_finish(
            state,
            AScheduleRes { status: 200, schedule: Some(schedule) },
            Seq::empty(),
        ),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_new_schedule(
    req: AScheduleCreateReq,
    next_cron_witness: u64,
    now: u64,
) -> ASchedule {
    ASchedule {
        id: req.id,
        cron: req.cron,
        promise_id: req.promise_id,
        promise_timeout: req.promise_timeout,
        promise_param: req.promise_param,
        promise_tags: req.promise_tags,
        next_run_at: next_cron_witness,
        last_run_at: None,
        created_at: now,
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_schedule_create_action(
    state: AState,
    req: AScheduleCreateReq,
    next_cron_witness: u64,
    now: u64,
    _materialize: bool,
) -> AScheduleActionResult {
    if spec_is_timer(req.promise_tags) && spec_has_target(req.promise_tags) {
        spec_schedule_finish(
            state,
            AScheduleRes { status: 400, schedule: None },
            Seq::empty(),
        )
    } else {
        match spec_find_schedule(state.schedules, req.id) {
            Some(schedule) => spec_schedule_finish(
                state,
                AScheduleRes { status: 200, schedule: Some(schedule) },
                Seq::empty(),
            ),
            None => {
                let schedule = spec_new_schedule(req, next_cron_witness, now);
                spec_schedule_finish(
                    state,
                    AScheduleRes { status: 200, schedule: Some(schedule) },
                    seq![AEffect::SetSchedule(schedule)],
                )
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_schedule_delete_action(
    state: AState,
    req: AScheduleDeleteReq,
    _now: u64,
    _materialize: bool,
) -> AScheduleDeleteActionResult {
    match spec_find_schedule(state.schedules, req.id) {
        None => spec_schedule_delete_finish(
            state,
            AScheduleDeleteRes { status: 404 },
            Seq::empty(),
        ),
        Some(schedule) => spec_schedule_delete_finish(
            state,
            AScheduleDeleteRes { status: 200 },
            seq![AEffect::DeleteSchedule(schedule.id)],
        ),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_schedule_search_action(
    state: AState,
    _req: AScheduleSearchReq,
    _now: u64,
    _materialize: bool,
) -> AScheduleSearchActionResult {
    spec_schedule_search_finish(
        state,
        AScheduleSearchRes {
            status: 501,
            schedules: Seq::empty(),
            cursor: None,
        },
        Seq::empty(),
    )
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_schedule_create_next_state(
    state: AState,
    req: AScheduleCreateReq,
    next_cron_witness: u64,
    now: u64,
    materialize: bool,
)
    ensures spec_schedule_create_action(
        state, req, next_cron_witness, now, materialize,
    ).next_state == spec_apply_all(
        state,
        spec_schedule_create_action(
            state, req, next_cron_witness, now, materialize,
        ).effects,
    ),
{
}

} // verus!
