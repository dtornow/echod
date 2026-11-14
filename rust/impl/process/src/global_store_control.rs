//! Small structural preservation lemmas for active Store bookkeeping.
//!
//! This module is deliberately separate from the physical Store proof so
//! Verus does not load the document/history algebra when proving control-flow
//! facts.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::global_store_invariants::{
    active_flight_ids_match_keys,
    active_flight_owners_match_phase,
    active_flights_precede_allocator,
    exact_request_certificates,
    exact_store_certificate_maps,
    commit_issued_operation_provenance,
    noncommit_certificates_are_other,
    old_active_store_certificates_preserved,
    pending_store_effects_are_exact,
    production_core_control_body,
    store_certificates_extend,
};
#[cfg(verus_keep_ghost)]
use crate::state::{Owner, S};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

proof fn lemma_store_certificate_extension_transitive(
    first: S,
    second: S,
    third: S,
)
    requires
        store_certificates_extend(first, second),
        store_certificates_extend(second, third),
    ensures
        store_certificates_extend(first, third),
{
    crate::global_store_invariants::
        lemma_store_certificates_extend_transitive(
            first, second, third,
        );
}

pub open spec fn detached_flight_control(state: S, fid: u64) -> bool {
    &&& production_core_control_body(state)
    &&& !state.flights.inflight.contains_key(fid)
    &&& forall|op: u64| state.ops.contains_key(op) ==>
        state.ops[op] != Owner::Flight(fid)
    &&& fid <= state.next_flight
    &&& !state.flights_exhausted ==> fid < state.next_flight
}

pub open spec fn commit_issuance_control_ready(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
) -> bool {
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        answer,
    );
    advanced.2 is Issued ==> commit_issued_operation_provenance(
        advanced.0,
        fid,
        advanced.1,
    )
}

pub open spec fn decision_issuance_control_ready(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
) -> bool {
    let decided = crate::handler_docs::spec_decide(
        state,
        flight.work,
        working,
    );
    commit_issuance_control_ready(
        decided.0,
        flight.id,
        decided.1,
        None,
    )
}

pub open spec fn fire_idle_issuance_control_ready(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    at: u64,
    fired: Option<crate::verified::flight_spec::AFired>,
) -> bool {
    let idle = crate::handler_docs::FlightSpec {
        idle: true,
        ..flight
    };
    let body = crate::document::spec_loaded_body(working.loaded);
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::SweepBegin {
            flight: idle.id,
            target: working.target,
            now: at,
        },
    );
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        body,
        echod_concrete::node::spec_body_deadline(body),
        at,
        fired,
    );
    commit_issuance_control_ready(
        committed.0,
        idle.id,
        committed.1,
        None,
    )
}

pub open spec fn fire_advance_issuance_control_ready(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
) -> bool {
    match flight.work {
        crate::handler_docs::WorkSpec::Fire {
            schedule,
            fired,
            ..
        } => {
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::AdvanceBegin {
                    flight: flight.id,
                    schedule,
                    now: at,
                    at: context.pending.at,
                    next: context.next,
                },
            );
            let committed = crate::handler_docs::spec_commit_new(
                noted,
                context.ws,
                context.advanced,
                echod_concrete::node::spec_body_deadline(
                    context.advanced,
                ),
                at,
                fired,
            );
            commit_issuance_control_ready(
                committed.0,
                flight.id,
                committed.1,
                None,
            )
        },
        _ => true,
    }
}

pub open spec fn fire_run_issuance_control_ready(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    working: crate::handler_docs::WorkingSpec,
) -> bool {
    let at = crate::document::spec_clamp_now(
        crate::document::spec_loaded_committed_at(working.loaded),
        context.t1,
    );
    let transition = echod_concrete::node::spec_occurrence_transition(
        crate::document::spec_loaded_body(working.loaded),
        context.pending,
        at,
        crate::handler_docs::spec_effective_retry_timeout(
            state.cfg.retry_timeout,
        ),
    );
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::FireBegin {
            flight: flight.id,
            origin: context.origin,
            now: at,
            row: context.row,
            at: context.pending.at,
            promise_id: context.pending.promise,
            next: context.next,
        },
    );
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        transition.0,
        echod_concrete::node::spec_body_deadline(transition.0),
        at,
        None,
    );
    commit_issuance_control_ready(
        committed.0,
        flight.id,
        committed.1,
        None,
    )
}

pub open spec fn fire_run_followup_control_ready(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    working: crate::handler_docs::WorkingSpec,
) -> bool {
    let at = crate::document::spec_clamp_now(
        crate::document::spec_loaded_committed_at(working.loaded),
        context.t1,
    );
    let transition = echod_concrete::node::spec_occurrence_transition(
        crate::document::spec_loaded_body(working.loaded),
        context.pending,
        at,
        crate::handler_docs::spec_effective_retry_timeout(
            state.cfg.retry_timeout,
        ),
    );
    let outbox = crate::handler_docs::spec_dispatches(
        transition.0,
        transition.1,
    );
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::FireBegin {
            flight: flight.id,
            origin: context.origin,
            now: at,
            row: context.row,
            at: context.pending.at,
            promise_id: context.pending.promise,
            next: context.next,
        },
    );
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        transition.0,
        echod_concrete::node::spec_body_deadline(transition.0),
        at,
        None,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Done(_) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::FireEnd {
                        flight: flight.id,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            let sent = crate::handler_docs::spec_send_all(ended, outbox);
            let released = crate::handler_docs::spec_release(
                sent,
                crate::target::spec_name(
                    crate::target::TargetSpec::Origin(context.origin),
                ),
            );
            fire_advance_issuance_control_ready(
                released,
                flight,
                context,
                at,
            )
        },
        _ => true,
    }
}

pub open spec fn answered_fire_origin_followup_control_ready(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
    outbox: Seq<(Seq<char>, crate::types::MessageSpec)>,
    response: echod_concrete::store::StoreRes,
) -> bool {
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Done(_) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::FireEnd {
                        flight: fid,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            let sent = crate::handler_docs::spec_send_all(ended, outbox);
            let released = crate::handler_docs::spec_release(
                sent,
                crate::target::spec_name(
                    crate::target::TargetSpec::Origin(context.origin),
                ),
            );
            fire_advance_issuance_control_ready(
                released,
                flight,
                context,
                at,
            )
        },
        _ => true,
    }
}

pub open spec fn answered_loading_issuance_control_ready(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    revalidating: Option<crate::cache::CachedSpec>,
    response: echod_concrete::store::StoreRes,
) -> bool {
    match flight.target {
        crate::target::TargetSpec::Origin(origin) => {
            let loaded = crate::handler_docs::spec_loaded_origin(
                state,
                origin,
                revalidating,
                response,
            );
            match loaded.1 {
                Ok(working) =>
                    decision_issuance_control_ready(
                        loaded.0,
                        flight,
                        working,
                    ),
                Err(_) => true,
            }
        },
        crate::target::TargetSpec::Schedule(id) => {
            let loaded = crate::handler_sched::spec_loaded_schedule(
                state,
                id,
                response,
            );
            match loaded.1 {
                Ok(working) =>
                    decision_issuance_control_ready(
                        loaded.0,
                        flight,
                        working,
                    ),
                Err(_) => true,
            }
        },
    }
}

pub open spec fn fire_decide_issuance_control_ready(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
) -> bool {
    match flight.work {
        crate::handler_docs::WorkSpec::Fire { fired, now, .. } => {
            let at = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(
                    working.loaded,
                ),
                now,
            );
            let body = crate::document::spec_loaded_body(working.loaded);
            let transition = crate::verified::flight_spec::spec_step(
                crate::verified::flight_spec::AJob::Fire,
                body,
                at,
                state.cfg.retry_timeout,
            );
            let due = match (
                crate::handler_sched::spec_schedule_row(body),
                transition.2.len() > 0,
            ) {
                (Some(row), true) => Some((row, transition.2.last())),
                _ => None,
            };
            match due {
                None =>
                    fire_idle_issuance_control_ready(
                        state,
                        flight,
                        working,
                        at,
                        fired,
                    ),
                Some(_) => true,
            }
        },
        _ => true,
    }
}

pub open spec fn answered_fire_loading_origin_issuance_control_ready(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    revalidating: Option<crate::cache::CachedSpec>,
    context: crate::handler_docs::FireCtxSpec,
    response: echod_concrete::store::StoreRes,
) -> bool {
    let loaded = crate::handler_docs::spec_loaded_origin(
        state,
        context.origin,
        revalidating,
        response,
    );
    match loaded.1 {
        Ok(working) =>
            fire_run_issuance_control_ready(
                loaded.0,
                flight,
                context,
                working,
            ) && fire_run_followup_control_ready(
                loaded.0,
                flight,
                context,
                working,
            ),
        Err(_) => true,
    }
}

pub open spec fn answered_fire_loading_schedule_issuance_control_ready(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    response: echod_concrete::store::StoreRes,
) -> bool {
    match flight.work {
        crate::handler_docs::WorkSpec::Fire { schedule, .. } => {
            let loaded = crate::handler_sched::spec_loaded_schedule(
                state,
                schedule,
                response,
            );
            match loaded.1 {
                Ok(working) =>
                    fire_decide_issuance_control_ready(
                        loaded.0,
                        flight,
                        working,
                    ),
                Err(_) => true,
            }
        },
        _ => true,
    }
}

pub open spec fn answered_phase_issuance_control_ready(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    phase: crate::handler_docs::PhaseSpec,
    response: echod_concrete::store::StoreRes,
) -> bool {
    match phase {
        crate::handler_docs::PhaseSpec::Loading {
            revalidating,
            ..
        } =>
            answered_loading_issuance_control_ready(
                state,
                flight,
                revalidating,
                response,
            ),
        crate::handler_docs::PhaseSpec::Origin { commit, .. }
        | crate::handler_docs::PhaseSpec::Schedule { commit, .. }
        | crate::handler_docs::PhaseSpec::FireIdle { commit }
        | crate::handler_docs::PhaseSpec::FireSchedule { commit } =>
            commit_issuance_control_ready(
                state,
                fid,
                commit,
                Some(response),
            ),
        crate::handler_docs::PhaseSpec::FireOrigin {
            commit,
            ctx,
            t,
            outbox,
            ..
        } =>
            commit_issuance_control_ready(
                state,
                fid,
                commit,
                Some(response),
            ) && answered_fire_origin_followup_control_ready(
                state,
                fid,
                flight,
                commit,
                ctx,
                t,
                outbox,
                response,
            ),
        crate::handler_docs::PhaseSpec::FireLoadingSchedule { .. } =>
            answered_fire_loading_schedule_issuance_control_ready(
                state,
                flight,
                response,
            ),
        crate::handler_docs::PhaseSpec::FireLoadingOrigin {
            revalidating,
            ctx,
            ..
        } =>
            answered_fire_loading_origin_issuance_control_ready(
                state,
                flight,
                revalidating,
                ctx,
                response,
            ),
        _ => true,
    }
}

pub open spec fn matching_flight_completion_control_ready(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
) -> bool {
    let flight = state.flights.inflight[fid];
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let detached = crate::handler_docs::spec_take_flight(consumed, fid);
    answered_phase_issuance_control_ready(
        detached,
        fid,
        crate::handler_docs::FlightSpec {
            phase: crate::handler_docs::PhaseSpec::Idle,
            ..flight
        },
        flight.phase,
        response,
    )
}

proof fn lemma_store_raw_preserves_exact_maps_and_pending(
    state: S,
    request: echod_concrete::store::StoreReqSpec,
    owner: Owner,
    certificate:
        crate::global_store_invariants::StoreEffectCertificateV,
)
    requires
        production_core_control_body(state),
        crate::global_store_invariants::
            invariant1_certificate_matches_request(
                state.keys.prefix,
                state.keys.bucket_ms,
                request,
                certificate,
            ),
    ensures
        ({
            let next = crate::state::spec_store_raw(
                state,
                request,
                owner,
                certificate,
            ).0;
            &&& exact_store_certificate_maps(
                next.keys.prefix,
                next.keys.bucket_ms,
                next.store_requests,
                next.ops,
                next.store_certificates,
            )
            &&& pending_store_effects_are_exact(next)
        }),
{
    reveal(crate::state::spec_store_raw);
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(exact_request_certificates);
    reveal(pending_store_effects_are_exact);
}

pub proof fn lemma_consume_and_detach_flight_preserves_core_control(
    state: S,
    op: u64,
    fid: u64,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates:
                    state.store_certificates.remove(op),
                ..state
            };
            detached_flight_control(
                crate::handler_docs::spec_take_flight(consumed, fid),
                fid,
            )
        }),
{
    reveal(crate::handler_docs::spec_take_flight);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(exact_request_certificates);
    reveal(pending_store_effects_are_exact);
    reveal(active_flights_precede_allocator);
    reveal(active_flight_ids_match_keys);
    reveal(active_flight_owners_match_phase);
    assert(state.flights.inflight.contains_key(fid));
    assert(state.flights.inflight[fid].id == fid);
    assert(state.flights.inflight[fid].phase.expects() == Some(op));
    assert forall|current: u64|
        state.ops.contains_key(current) && current != op implies
            state.ops[current] != Owner::Flight(fid) by {
        if state.ops[current] == Owner::Flight(fid) {
            assert(state.flights.inflight[fid].phase.expects()
                == Some(current));
            assert(current == op);
        }
    };
}

pub proof fn lemma_loaded_origin_preserves_detached_flight_control(
    state: S,
    fid: u64,
    origin: Seq<char>,
    revalidating: Option<crate::cache::CachedSpec>,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
    ensures
        detached_flight_control(
            crate::handler_docs::spec_loaded_origin(
                state,
                origin,
                revalidating,
                response,
            ).0,
            fid,
        ),
{
    reveal(crate::handler_docs::spec_loaded_origin);
    reveal(crate::state::spec_remember);
    reveal(crate::state::spec_forget_origin);
    reveal(crate::cache::spec_put);
    reveal(crate::cache::spec_remove);
    reveal(crate::state::spec_note);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
}

pub proof fn lemma_loaded_schedule_preserves_detached_flight_control(
    state: S,
    fid: u64,
    id: Seq<char>,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
    ensures
        detached_flight_control(
            crate::handler_sched::spec_loaded_schedule(
                state,
                id,
                response,
            ).0,
            fid,
        ),
{
    reveal(crate::handler_sched::spec_loaded_schedule);
    reveal(detached_flight_control);
}

pub proof fn lemma_decide_preserves_detached_flight_control(
    state: S,
    fid: u64,
    work: crate::handler_docs::WorkSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        detached_flight_control(state, fid),
    ensures
        detached_flight_control(
            crate::handler_docs::spec_decide(
                state,
                work,
                working,
            ).0,
            fid,
        ),
{
    reveal(crate::handler_docs::spec_decide);
    reveal(crate::handler_docs::spec_commit_new);
    reveal(crate::state::spec_note);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_issued_shape(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        production_core_control_body(state),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            &&& advanced.1.expects() is Some
            &&& {
                let op = advanced.1.expects().unwrap();
                &&& advanced.0.ops.contains_key(op)
                &&& advanced.0.ops[op] == Owner::Flight(fid)
                &&& advanced.0.store_requests.contains_key(op)
                &&& crate::state::spec_store_request_representable(
                    advanced.0.store_requests[op],
                )
                &&& advanced.0.store_certificates.contains_key(op)
                &&& forall|old: u64|
                    state.ops.contains_key(old) ==> {
                        &&& advanced.0.ops.contains_key(old)
                        &&& advanced.0.ops[old] == state.ops[old]
                        &&& advanced.0.store_requests
                            .contains_key(old)
                        &&& advanced.0.store_requests[old]
                            == state.store_requests[old]
                        &&& advanced.0.store_certificates
                            .contains_key(old)
                        &&& advanced.0.store_certificates[old]
                            == state.store_certificates[old]
                    }
                &&& forall|current: u64|
                    advanced.0.ops.contains_key(current)
                        && !state.ops.contains_key(current) ==>
                            current == op
                &&& forall|current: u64|
                    advanced.0.store_certificates.contains_key(current)
                        && !state.store_certificates
                            .contains_key(current) ==>
                            current == op
            }
        }),
{
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(pending_store_effects_are_exact);
    reveal(active_flights_precede_allocator);
    reveal(active_flight_owners_match_phase);
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_issued_request_frame(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            let issued = advanced.1.expects().unwrap();
            &&& advanced.0.keys == state.keys
            &&& forall|op: u64|
                advanced.0.store_requests.contains_key(op)
                    && !state.store_requests.contains_key(op) ==>
                        op == issued
        }),
{
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_remember);
    reveal(crate::cache::spec_put);
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_issued_output_shape(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            let issued = advanced.1.expects().unwrap();
            &&& advanced.0.out.len() > state.out.len()
            &&& advanced.0.out.take(state.out.len() as int) == state.out
            &&& advanced.0.out.last()
                == crate::types::EffectSpec::Store {
                    op: issued,
                    request: advanced.0.store_requests[issued],
                }
            &&& forall|i: int|
                state.out.len() <= i
                    && i < advanced.0.out.len() - 1 ==>
                        advanced.0.out[i] !is Store
        }),
{
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_remember);
    reveal(crate::cache::spec_put);
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_issued_exact_maps(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        production_core_control_body(state),
        commit_issuance_control_ready(
            state,
            fid,
            commit,
            answer,
        ),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0;
            exact_store_certificate_maps(
                advanced.keys.prefix,
                advanced.keys.bucket_ms,
                advanced.store_requests,
                advanced.ops,
                advanced.store_certificates,
            )
        }),
{
    lemma_commit_advance_issued_shape(
        state,
        fid,
        commit,
        answer,
    );
    lemma_commit_advance_issued_request_frame(
        state,
        fid,
        commit,
        answer,
    );
    reveal(commit_issuance_control_ready);
    reveal(commit_issued_operation_provenance);
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        answer,
    );
    let issued = advanced.1.expects().unwrap();
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    assert forall|op: u64|
        advanced.0.store_requests.contains_key(op) implies {
            &&& advanced.0.store_certificates.contains_key(op)
            &&& crate::global_store_invariants::
                invariant1_certificate_matches_request(
                    advanced.0.keys.prefix,
                    advanced.0.keys.bucket_ms,
                    advanced.0.store_requests[op],
                    advanced.0.store_certificates[op],
                )
        } by {
        if op == issued {
            assert(commit_issued_operation_provenance(
                advanced.0,
                fid,
                advanced.1,
            ));
        } else {
            assert(state.store_requests.contains_key(op));
        }
    };
    assert forall|op: u64|
        advanced.0.store_requests.contains_key(op) implies
            advanced.0.ops.contains_key(op) by {
        if op == issued {
            assert(advanced.0.ops.contains_key(issued));
        } else {
            assert(state.store_requests.contains_key(op));
        }
    };
    assert forall|op: u64|
        advanced.0.ops.contains_key(op) implies
            advanced.0.store_requests.contains_key(op) by {
        if op == issued {
            assert(advanced.0.store_requests.contains_key(issued));
        } else {
            assert(state.ops.contains_key(op));
            assert(advanced.0.store_requests.contains_key(op));
        }
    };
    assert forall|op: u64|
        advanced.0.store_certificates.contains_key(op) implies
            advanced.0.store_requests.contains_key(op) by {
        if op == issued {
            assert(advanced.0.store_requests.contains_key(issued));
        } else {
            assert(state.store_certificates.contains_key(op));
            assert(state.store_requests.contains_key(op));
            assert(state.ops.contains_key(op));
            assert(advanced.0.store_requests.contains_key(op));
        }
    };
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_issued_pending_effects(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        production_core_control_body(state),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 is Issued
        }),
    ensures
        pending_store_effects_are_exact(
            crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0,
        ),
{
    lemma_commit_advance_issued_shape(state, fid, commit, answer);
    lemma_commit_advance_issued_output_shape(
        state,
        fid,
        commit,
        answer,
    );
    reveal(production_core_control_body);
    reveal(pending_store_effects_are_exact);
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        answer,
    );
    let issued = advanced.1.expects().unwrap();
    assert forall|i: int, op: u64,
        request: echod_concrete::store::StoreReqSpec|
        0 <= i < advanced.0.out.len()
            && advanced.0.out[i]
                == (crate::types::EffectSpec::Store {
                    op,
                    request,
                }) implies {
                &&& advanced.0.ops.contains_key(op)
                &&& advanced.0.store_requests.contains_key(op)
                &&& advanced.0.store_requests[op] == request
                &&& advanced.0.store_certificates.contains_key(op)
                &&& crate::state::spec_store_request_representable(request)
            } by {
        if i < state.out.len() {
            assert(advanced.0.out.take(state.out.len() as int)[i]
                == advanced.0.out[i]);
            assert(advanced.0.out.take(state.out.len() as int)[i]
                == state.out[i]);
            assert(advanced.0.out[i] == state.out[i]);
            assert(state.out[i]
                == (crate::types::EffectSpec::Store {
                    op,
                    request,
                }));
            assert(state.ops.contains_key(op));
            assert(state.store_requests.contains_key(op));
            assert(state.store_requests[op] == request);
            assert(state.store_certificates.contains_key(op));
            assert(advanced.0.ops.contains_key(op));
            assert(advanced.0.store_requests.contains_key(op));
            assert(advanced.0.store_requests[op] == request);
            assert(advanced.0.store_certificates.contains_key(op));
        } else {
            assert(i == advanced.0.out.len() - 1);
            assert(op == issued);
            assert(request == advanced.0.store_requests[issued]);
            assert(advanced.0.ops.contains_key(issued));
            assert(advanced.0.store_certificates.contains_key(issued));
        }
    };
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_issued_exact_bookkeeping(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        production_core_control_body(state),
        commit_issuance_control_ready(
            state,
            fid,
            commit,
            answer,
        ),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0;
            &&& exact_store_certificate_maps(
                advanced.keys.prefix,
                advanced.keys.bucket_ms,
                advanced.store_requests,
                advanced.ops,
                advanced.store_certificates,
            )
            &&& pending_store_effects_are_exact(advanced)
        }),
{
    reveal(production_core_control_body);
    lemma_commit_advance_issued_exact_maps(
        state,
        fid,
        commit,
        answer,
    );
    lemma_commit_advance_issued_pending_effects(
        state,
        fid,
        commit,
        answer,
    );
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_issued_structural_frame(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        production_core_control_body(state),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0;
            &&& crate::production_relation::
                operation_allocator_consistent(advanced)
            &&& advanced.flights == state.flights
            &&& advanced.next_flight == state.next_flight
            &&& advanced.flights_exhausted
                == state.flights_exhausted
            &&& advanced.debug == state.debug
            &&& old_active_store_certificates_preserved(
                state,
                advanced,
            )
            &&& store_certificates_extend(state, advanced)
            &&& forall|current: u64|
                advanced.ops.contains_key(current) ==>
                    advanced.store_requests.contains_key(current)
            &&& forall|current: u64|
                advanced.store_requests.contains_key(current) ==>
                    advanced.ops.contains_key(current)
            &&& forall|current: u64|
                advanced.ops.contains_key(current) ==>
                    advanced.ops[current] != Owner::Debug
        }),
{
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(old_active_store_certificates_preserved);
    reveal(store_certificates_extend);
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_issued_control(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        production_core_control_body(state),
        commit_issuance_control_ready(
            state,
            fid,
            commit,
            answer,
        ),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0;
            &&& crate::production_relation::
                operation_allocator_consistent(advanced)
            &&& exact_store_certificate_maps(
                advanced.keys.prefix,
                advanced.keys.bucket_ms,
                advanced.store_requests,
                advanced.ops,
                advanced.store_certificates,
            )
            &&& pending_store_effects_are_exact(advanced)
            &&& old_active_store_certificates_preserved(
                state,
                advanced,
            )
            &&& store_certificates_extend(state, advanced)
            &&& advanced.flights == state.flights
            &&& advanced.next_flight == state.next_flight
            &&& advanced.flights_exhausted
                == state.flights_exhausted
            &&& advanced.debug == state.debug
            &&& forall|current: u64|
                advanced.ops.contains_key(current) ==>
                    advanced.store_requests.contains_key(current)
            &&& forall|current: u64|
                advanced.store_requests.contains_key(current) ==>
                    advanced.ops.contains_key(current)
            &&& forall|current: u64|
                advanced.ops.contains_key(current) ==>
                    advanced.ops[current] != Owner::Debug
        }),
{
    lemma_commit_advance_issued_exact_bookkeeping(
        state,
        fid,
        commit,
        answer,
    );
    lemma_commit_advance_issued_structural_frame(
        state,
        fid,
        commit,
        answer,
    );
}

pub proof fn lemma_commit_advance_preserves_old_active_certificates(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        production_core_control_body(state),
    ensures
        old_active_store_certificates_preserved(
            state,
            crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0,
        ),
        store_certificates_extend(
            state,
            crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0,
        ),
{
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        answer,
    );
    if advanced.2 is Issued {
        lemma_commit_advance_issued_structural_frame(
            state,
            fid,
            commit,
            answer,
        );
    } else {
        lemma_commit_advance_nonissued_frame(
            state,
            fid,
            commit,
            answer,
        );
        reveal(old_active_store_certificates_preserved);
        reveal(store_certificates_extend);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_nonissued_frame(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 !is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0;
            &&& advanced.ops == state.ops
            &&& advanced.store_requests == state.store_requests
            &&& advanced.store_certificates == state.store_certificates
            &&& advanced.flights == state.flights
            &&& advanced.next_flight == state.next_flight
            &&& advanced.flights_exhausted == state.flights_exhausted
            &&& advanced.keys == state.keys
        }),
{
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_remember);
    reveal(crate::cache::spec_put);
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_nonissued_output_frame(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 !is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0;
            &&& advanced.out.len() >= state.out.len()
            &&& advanced.out.take(state.out.len() as int) == state.out
            &&& forall|i: int|
                state.out.len() <= i && i < advanced.out.len() ==>
                    advanced.out[i] !is Store
        }),
{
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_remember);
    reveal(crate::cache::spec_put);
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_nonissued_pending_effects(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        pending_store_effects_are_exact(state),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 !is Issued
        }),
    ensures
        pending_store_effects_are_exact(
            crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0,
        ),
{
    lemma_commit_advance_nonissued_frame(
        state,
        fid,
        commit,
        answer,
    );
    lemma_commit_advance_nonissued_output_frame(
        state,
        fid,
        commit,
        answer,
    );
    reveal(pending_store_effects_are_exact);
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        answer,
    ).0;
    assert forall|i: int, op: u64,
        request: echod_concrete::store::StoreReqSpec|
        0 <= i < advanced.out.len()
            && advanced.out[i]
                == (crate::types::EffectSpec::Store {
                    op,
                    request,
                }) implies {
                &&& advanced.ops.contains_key(op)
                &&& advanced.store_requests.contains_key(op)
                &&& advanced.store_requests[op] == request
                &&& advanced.store_certificates.contains_key(op)
                &&& crate::state::spec_store_request_representable(request)
            } by {
        assert(i < state.out.len());
        assert(advanced.out.take(state.out.len() as int)[i]
            == advanced.out[i]);
        assert(advanced.out.take(state.out.len() as int)[i]
            == state.out[i]);
        assert(advanced.out[i] == state.out[i]);
        assert(state.out[i]
            == (crate::types::EffectSpec::Store {
                op,
                request,
            }));
    };
}

#[verifier::spinoff_prover]
proof fn lemma_commit_advance_nonissued_bookkeeping(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        production_core_control_body(state),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 !is Issued
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0;
            &&& exact_store_certificate_maps(
                advanced.keys.prefix,
                advanced.keys.bucket_ms,
                advanced.store_requests,
                advanced.ops,
                advanced.store_certificates,
            )
            &&& pending_store_effects_are_exact(advanced)
            &&& advanced.ops == state.ops
            &&& advanced.store_requests == state.store_requests
            &&& advanced.store_certificates == state.store_certificates
            &&& advanced.flights == state.flights
            &&& advanced.next_flight == state.next_flight
            &&& advanced.flights_exhausted == state.flights_exhausted
        }),
{
    lemma_commit_advance_nonissued_frame(
        state,
        fid,
        commit,
        answer,
    );
    lemma_commit_advance_nonissued_pending_effects(
        state,
        fid,
        commit,
        answer,
    );
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(pending_store_effects_are_exact);
}

#[verifier::spinoff_prover]
pub proof fn lemma_commit_advance_nonissued_preserves_detached_flight_control(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
)
    requires
        detached_flight_control(state, fid),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            advanced.2 !is Issued
        }),
    ensures
        detached_flight_control(
            crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            ).0,
            fid,
        ),
{
    lemma_commit_advance_nonissued_bookkeeping(
        state,
        fid,
        commit,
        answer,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        answer,
    ).0;
    assert(advanced.ops == state.ops);
    assert(advanced.flights == state.flights);
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_remember);
    reveal(crate::cache::spec_put);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    reveal(active_flights_precede_allocator);
    reveal(active_flight_owners_match_phase);
    reveal(active_flight_ids_match_keys);
}

#[verifier::spinoff_prover]
pub proof fn lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
    replacement: crate::handler_docs::FlightSpec,
)
    requires
        production_core_control_body(state),
        commit_issuance_control_ready(
            state,
            fid,
            commit,
            answer,
        ),
        !state.flights.inflight.contains_key(fid),
        forall|op: u64| state.ops.contains_key(op) ==>
            state.ops[op] != Owner::Flight(fid),
        fid <= state.next_flight,
        !state.flights_exhausted ==> fid < state.next_flight,
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            &&& advanced.2 is Issued
            &&& replacement.id == fid
            &&& replacement.phase.expects() == advanced.1.expects()
            &&& match replacement.phase {
                crate::handler_docs::PhaseSpec::Origin { .. }
                | crate::handler_docs::PhaseSpec::Schedule { .. }
                | crate::handler_docs::PhaseSpec::FireIdle { .. }
                | crate::handler_docs::PhaseSpec::FireOrigin { .. }
                | crate::handler_docs::PhaseSpec::FireSchedule {
                    ..
                } => true,
                _ => false,
            }
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                answer,
            );
            let issued = advanced.1.expects().unwrap();
            let next = crate::handler_docs::spec_inflight(
                advanced.0,
                replacement,
            );
            &&& production_core_control_body(next)
            &&& advanced.0.ops.contains_key(issued)
            &&& advanced.0.ops[issued] == Owner::Flight(fid)
            &&& advanced.0.store_requests.contains_key(issued)
            &&& advanced.0.store_certificates.contains_key(issued)
            &&& next.flights.inflight.contains_key(fid)
            &&& next.flights.inflight[fid] == replacement
            &&& replacement.phase.expects() == Some(issued)
            &&& forall|op: u64| state.ops.contains_key(op) ==> {
                &&& advanced.0.ops.contains_key(op)
                &&& advanced.0.ops[op] == state.ops[op]
                &&& advanced.0.store_requests[op]
                    == state.store_requests[op]
                &&& advanced.0.store_certificates[op]
                    == state.store_certificates[op]
            }
        }),
{
    lemma_commit_advance_issued_shape(state, fid, commit, answer);
    lemma_commit_advance_issued_control(state, fid, commit, answer);
    reveal(crate::handler_docs::spec_inflight);
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(pending_store_effects_are_exact);
    reveal(active_flights_precede_allocator);
    reveal(active_flight_owners_match_phase);
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        answer,
    );
    assert(advanced.1.expects() is Some);
    let issued = advanced.1.expects().unwrap();
    assert(advanced.0.ops.contains_key(issued));
    assert(advanced.0.ops[issued] == Owner::Flight(fid));
    assert(advanced.0.store_requests.contains_key(issued));
    assert forall|op: u64|
        advanced.0.ops.contains_key(op)
            && advanced.0.ops[op] == Owner::Flight(fid) implies
                op == issued by {
        if state.ops.contains_key(op) {
            assert(state.ops[op] != Owner::Flight(fid));
        }
    };
    let next = crate::handler_docs::spec_inflight(
        advanced.0,
        replacement,
    );
    assert(advanced.0.next_flight == state.next_flight);
    assert(advanced.0.flights_exhausted == state.flights_exhausted);
    assert(next.next_flight == state.next_flight);
    assert(next.flights_exhausted == state.flights_exhausted);
    assert(crate::production_relation::operation_allocator_consistent(next));
    assert(active_flights_precede_allocator(next)) by {
        assert forall|current: u64|
            next.flights.inflight.contains_key(current) implies {
                &&& current <= next.next_flight
                &&& !next.flights_exhausted ==>
                    current < next.next_flight
            } by {
            if current == fid {
            } else {
                assert(advanced.0.flights.inflight.contains_key(current));
                assert(state.flights.inflight.contains_key(current));
                assert(current <= state.next_flight);
                assert(!state.flights_exhausted ==>
                    current < state.next_flight);
            }
        };
    };
    assert forall|op: u64|
        next.ops.contains_key(op) implies
            next.store_requests.contains_key(op) by {};
    assert forall|op: u64|
        next.store_requests.contains_key(op) implies
            next.ops.contains_key(op) by {};
    assert(active_flight_owners_match_phase(next)) by {
        assert forall|op: u64, owner: u64|
            next.ops.contains_key(op)
                && next.ops[op] == Owner::Flight(owner) implies {
                    &&& next.flights.inflight.contains_key(owner)
                    &&& next.flights.inflight[owner].phase.expects()
                        == Some(op)
                } by {
            if owner == fid {
                assert(op == issued);
                assert(next.flights.inflight[fid] == replacement);
            } else {
                assert(state.ops.contains_key(op));
                assert(state.ops[op] == Owner::Flight(owner));
                assert(state.flights.inflight.contains_key(owner));
                assert(next.flights.inflight[owner]
                    == state.flights.inflight[owner]);
            }
        };
    };
    assert(active_flight_ids_match_keys(next)) by {
        assert forall|current: u64|
            next.flights.inflight.contains_key(current) implies
                next.flights.inflight[current].id == current by {
            if current == fid {
                assert(next.flights.inflight[fid] == replacement);
            } else {
                assert(state.flights.inflight.contains_key(current));
                assert(next.flights.inflight[current]
                    == state.flights.inflight[current]);
                assert(active_flight_ids_match_keys(state));
            }
        };
    };
    assert forall|op: u64|
        next.ops.contains_key(op) implies
            next.ops[op] != Owner::Debug by {};
    assert(crate::production_relation::operation_allocator_consistent(
        next,
    ));
    assert(active_flights_precede_allocator(next));
    assert(exact_store_certificate_maps(
        next.keys.prefix,
        next.keys.bucket_ms,
        next.store_requests,
        next.ops,
        next.store_certificates,
    ));
    assert(active_flight_owners_match_phase(next));
    assert(active_flight_ids_match_keys(next));
    assert(pending_store_effects_are_exact(next));
    assert(noncommit_certificates_are_other(next)) by {
        reveal(noncommit_certificates_are_other);
        assert forall|op: u64|
            next.ops.contains_key(op) implies {
                &&& next.store_certificates.contains_key(op)
                &&& match next.ops[op] {
                    Owner::Flight(owner) => {
                        &&& next.flights.inflight.contains_key(owner)
                        &&& match next.flights.inflight[owner].phase {
                            crate::handler_docs::PhaseSpec::Origin {
                                ..
                            }
                            | crate::handler_docs::PhaseSpec::Schedule {
                                ..
                            }
                            | crate::handler_docs::PhaseSpec::FireIdle {
                                ..
                            }
                            | crate::handler_docs::PhaseSpec::FireOrigin {
                                ..
                            }
                            | crate::handler_docs::PhaseSpec::FireSchedule {
                                ..
                            } => true,
                            _ =>
                                next.store_certificates[op]
                                    == crate::global_store_invariants::
                                        StoreEffectCertificateV::Other,
                        }
                    },
                    _ =>
                        next.store_certificates[op]
                            == crate::global_store_invariants::
                                StoreEffectCertificateV::Other,
                }
            } by {
            if op == issued {
                assert(next.ops[op] == Owner::Flight(fid));
                assert(next.flights.inflight[fid] == replacement);
            } else {
                assert(state.ops.contains_key(op));
                match state.ops[op] {
                    Owner::Flight(owner) => {
                        assert(state.flights.inflight.contains_key(owner));
                        if owner == fid {
                            assert(false);
                        } else {
                            assert(next.flights.inflight[owner]
                                == state.flights.inflight[owner]);
                        }
                    },
                    _ => {},
                }
            }
        };
    };
    assert(next.debug == state.debug);
    assert(state.debug.current is None);
    assert(state.debug.queue.len() == 0);
    assert(next.debug.current is None);
    assert(next.debug.queue.len() == 0);
    assert(production_core_control_body(next));
}

pub proof fn lemma_resume_preserves_core_control_body(
    state: S,
    fid: u64,
)
    requires
        production_core_control_body(state),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_resume(state, fid),
        ),
{
    reveal(crate::handler_docs::spec_resume);
    if state.flights.inflight.contains_key(fid) {
        let flight = state.flights.inflight[fid];
        let detached = crate::handler_docs::spec_take_flight(state, fid);
        match flight.phase {
            crate::handler_docs::PhaseSpec::FireWaitingOrigin(ctx) => {
                assert(detached_flight_control(detached, fid)) by {
                    reveal(crate::handler_docs::spec_take_flight);
                    reveal(detached_flight_control);
                    reveal(production_core_control_body);
                    reveal(active_flights_precede_allocator);
                    reveal(active_flight_owners_match_phase);
                };
                assert forall|op: u64|
                    state.ops.contains_key(op) implies
                        state.ops[op] != Owner::Flight(fid) by {
                    if state.ops[op] == Owner::Flight(fid) {
                        assert(state.flights.inflight[fid]
                            .phase.expects() == Some(op));
                        assert(false);
                    }
                };
                lemma_fire_load_origin_preserves_core_control_body(
                    detached,
                    crate::handler_docs::FlightSpec {
                        phase: crate::handler_docs::PhaseSpec::Idle,
                        ..flight
                    },
                    ctx,
                );
            },
            _ => {
                reveal(crate::handler_docs::spec_inflight);
                reveal(crate::handler_docs::spec_take_flight);
                reveal(production_core_control_body);
                reveal(active_flight_owners_match_phase);
            },
        }
    }
}

pub proof fn lemma_fire_load_origin_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        production_core_control_body(
            crate::handler_sched::spec_fire_load_origin(
                state,
                flight,
                context,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_load_origin);
    reveal(crate::handler_docs::spec_load_origin);
    let key = crate::keys::spec_doc_key(
        state.keys.prefix,
        context.origin,
    );
    let cached = crate::cache::spec_get(
        state.cache,
        context.origin,
    );
    match cached.1 {
        Some(entry) => {
            lemma_store_raw_preserves_exact_maps_and_pending(
                S { cache: cached.0, ..state },
                echod_concrete::store::StoreReqSpec::GetIfNoneMatch {
                    key,
                    etag: entry.etag,
                },
                Owner::Flight(flight.id),
                crate::global_store_invariants::
                    StoreEffectCertificateV::Other,
            );
        },
        None => {
            lemma_store_raw_preserves_exact_maps_and_pending(
                S { cache: cached.0, ..state },
                echod_concrete::store::StoreReqSpec::Get { key },
                Owner::Flight(flight.id),
                crate::global_store_invariants::
                    StoreEffectCertificateV::Other,
            );
        },
    }
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_raw);
    reveal(crate::handler_docs::spec_inflight);
    let loaded = crate::handler_docs::spec_load_origin(
        state,
        flight.id,
        context.origin,
    );
    match loaded.1 {
        Some(op) => {
            let replacement = crate::handler_docs::FlightSpec {
                phase:
                    crate::handler_docs::PhaseSpec::FireLoadingOrigin {
                        op,
                        revalidating: cached.1,
                        ctx: context,
                    },
                ..flight
            };
            match cached.1 {
                Some(entry) => {
                    let base = S { cache: cached.0, ..state };
                    assert(detached_flight_control(
                        base,
                        flight.id,
                    )) by {
                        reveal(detached_flight_control);
                        reveal(production_core_control_body);
                    };
                    lemma_store_issuance_then_flight_attachment_preserves_core_control(
                        base,
                        echod_concrete::store::StoreReqSpec::
                            GetIfNoneMatch {
                                key,
                                etag: entry.etag,
                            },
                        flight.id,
                        crate::global_store_invariants::
                            StoreEffectCertificateV::Other,
                        replacement,
                    );
                },
                None => {
                    let base = crate::state::spec_note(
                        S { cache: cached.0, ..state },
                        crate::types::NoteSpec::Cache(
                            crate::types::CacheResult::Miss,
                        ),
                    );
                    assert(detached_flight_control(
                        base,
                        flight.id,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(detached_flight_control);
                        reveal(production_core_control_body);
                    };
                    lemma_store_issuance_then_flight_attachment_preserves_core_control(
                        base,
                        echod_concrete::store::StoreReqSpec::Get {
                            key,
                        },
                        flight.id,
                        crate::global_store_invariants::
                            StoreEffectCertificateV::Other,
                        replacement,
                    );
                },
            }
            assert(crate::handler_sched::spec_fire_load_origin(
                state,
                flight,
                context,
            ) == crate::handler_docs::spec_inflight(
                loaded.0,
                replacement,
            ));
            assert(production_core_control_body(
                crate::handler_docs::spec_inflight(
                    loaded.0,
                    replacement,
                ),
            ));
        },
        None => {
            let origin = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            let abandoned = crate::handler_docs::spec_abandon_slot(
                loaded.0,
                origin,
            );
            assert(detached_flight_control(abandoned, flight.id)) by {
                reveal(crate::handler_docs::spec_abandon_slot);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_op_exhausted_preserves_core_control_body(
                abandoned,
                flight,
            );
            assert(crate::handler_sched::spec_fire_load_origin(
                state,
                flight,
                context,
            ) == crate::handler_docs::spec_op_exhausted(
                abandoned,
                flight,
            ));
        },
    }
}

pub proof fn lemma_release_preserves_core_control_body(
    state: S,
    name: Seq<char>,
)
    requires
        production_core_control_body(state),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_release(state, name),
        ),
{
    reveal(crate::handler_docs::spec_release);
    if state.flights.slots.contains_key(name) {
        let slot = state.flights.slots[name];
        if slot.queue.len() == 0 {
            reveal(crate::handler_docs::spec_without_slot);
            reveal(production_core_control_body);
        } else {
            let rest = slot.queue.drop_first();
            match slot.queue[0] {
                crate::handler_docs::QueuedSpec::Work {
                    target,
                    work,
                    firing,
                    debug,
                } => {
                    let slotted = crate::handler_docs::spec_with_slot(
                        state,
                        name,
                        crate::handler_docs::SlotSpec {
                            busy: None,
                            queue: rest,
                        },
                    );
                    assert(production_core_control_body(slotted)) by {
                        reveal(crate::handler_docs::spec_with_slot);
                        reveal(production_core_control_body);
                    };
                    crate::global_store_invariants::
                        lemma_start_preserves_core_control_body(
                            slotted,
                            target,
                            work,
                            firing,
                            debug,
                        );
                },
                crate::handler_docs::QueuedSpec::Waiter(waiter) => {
                    let slotted = crate::handler_docs::spec_with_slot(
                        state,
                        name,
                        crate::handler_docs::SlotSpec {
                            busy: Some(waiter),
                            queue: rest,
                        },
                    );
                    assert(production_core_control_body(slotted)) by {
                        reveal(crate::handler_docs::spec_with_slot);
                        reveal(production_core_control_body);
                    };
                    lemma_resume_preserves_core_control_body(
                        slotted,
                        waiter,
                    );
                },
            }
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_release_work_preserves_detached_flight_control(
    state: S,
    name: Seq<char>,
    fid: u64,
)
    requires
        detached_flight_control(state, fid),
        state.flights.slots.contains_key(name),
        state.flights.slots[name].queue.len() > 0,
        state.flights.slots[name].queue[0] is Work,
    ensures
        detached_flight_control(
            crate::handler_docs::spec_release(state, name),
            fid,
        ),
{
    lemma_release_preserves_core_control_body(state, name);
    reveal(crate::handler_docs::spec_release);
    reveal(crate::handler_docs::spec_start);
    reveal(crate::state::spec_flight);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    reveal(active_flights_precede_allocator);
    reveal(active_flight_owners_match_phase);
    reveal(active_flight_ids_match_keys);
    assert(fid != state.next_flight || state.flights_exhausted);
}

#[verifier::spinoff_prover]
proof fn lemma_release_waiter_preserves_detached_flight_control(
    state: S,
    name: Seq<char>,
    fid: u64,
)
    requires
        detached_flight_control(state, fid),
        state.flights.slots.contains_key(name),
        state.flights.slots[name].queue.len() > 0,
        state.flights.slots[name].queue[0] is Waiter,
    ensures
        detached_flight_control(
            crate::handler_docs::spec_release(state, name),
            fid,
        ),
{
    lemma_release_preserves_core_control_body(state, name);
    reveal(crate::handler_docs::spec_release);
    reveal(crate::handler_docs::spec_resume);
    reveal(crate::handler_docs::spec_take_flight);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    reveal(active_flights_precede_allocator);
    reveal(active_flight_owners_match_phase);
    reveal(active_flight_ids_match_keys);
    match state.flights.slots[name].queue[0] {
        crate::handler_docs::QueuedSpec::Waiter(waiter) => {
            if waiter == fid {
                assert(!state.flights.inflight.contains_key(waiter));
            } else if state.flights.inflight.contains_key(waiter) {
                let resumed = state.flights.inflight[waiter];
                match resumed.phase {
                    crate::handler_docs::PhaseSpec::FireWaitingOrigin(_) => {
                        reveal(crate::handler_sched::spec_fire_load_origin);
                        reveal(crate::handler_docs::spec_load_origin);
                        reveal(crate::handler_docs::spec_inflight);
                        reveal(crate::handler_docs::spec_op_exhausted);
                        reveal(crate::handler_docs::spec_abandon_slot);
                        reveal(crate::state::spec_store);
                        reveal(crate::state::spec_store_certified);
                        reveal(crate::state::spec_store_raw);
                    },
                    _ => {
                        reveal(crate::handler_docs::spec_inflight);
                    },
                }
            }
        }
        _ => assert(false),
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_release_preserves_detached_flight_control(
    state: S,
    name: Seq<char>,
    fid: u64,
)
    requires
        detached_flight_control(state, fid),
    ensures
        detached_flight_control(
            crate::handler_docs::spec_release(state, name),
            fid,
        ),
{
    lemma_release_preserves_core_control_body(state, name);
    reveal(crate::handler_docs::spec_release);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    if state.flights.slots.contains_key(name) {
        let slot = state.flights.slots[name];
        if slot.queue.len() > 0 {
            match slot.queue[0] {
                crate::handler_docs::QueuedSpec::Work { .. } => {
                    lemma_release_work_preserves_detached_flight_control(
                        state,
                        name,
                        fid,
                    );
                },
                crate::handler_docs::QueuedSpec::Waiter(_) => {
                    lemma_release_waiter_preserves_detached_flight_control(
                        state,
                        name,
                        fid,
                    );
                },
            }
        }
    }
}

pub proof fn lemma_op_exhausted_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_op_exhausted(state, flight),
        ),
{
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
}

pub proof fn lemma_finish_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    result: Result<crate::types::Fired, Seq<char>>,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_finish(state, flight, result),
        ),
{
    reveal(crate::handler_docs::spec_finish);
    let released = crate::handler_docs::spec_release(
        state,
        crate::target::spec_name(flight.target),
    );
    lemma_release_preserves_core_control_body(
        state,
        crate::target::spec_name(flight.target),
    );
    let fired = match flight.firing {
        Some(firing) => {
            crate::global_store_invariants::
                lemma_timer_fired_preserves_core_control_body(
                    released,
                    firing,
                    crate::state::spec_now(released),
                    result,
                );
            crate::handler_timers::spec_timer_fired(
                released,
                firing,
                crate::state::spec_now(released),
                result,
            )
        },
        None => released,
    };
    if flight.debug {
        reveal(crate::debug::spec_debug_flight_done);
        reveal(crate::debug::spec_debug_tick_advance);
        reveal(production_core_control_body);
        assert(fired.debug.current is None);
    }
}

pub proof fn lemma_send_all_preserves_detached_flight_control(
    state: S,
    fid: u64,
    outbox: Seq<(Seq<char>, crate::types::MessageSpec)>,
)
    requires
        detached_flight_control(state, fid),
    ensures
        detached_flight_control(
            crate::handler_docs::spec_send_all(state, outbox),
            fid,
        ),
        store_certificates_extend(
            state,
            crate::handler_docs::spec_send_all(state, outbox),
        ),
    decreases outbox.len(),
{
    reveal(crate::handler_docs::spec_send_all);
    if outbox.len() > 0 {
        let emitted = crate::state::spec_emit(
            state,
            crate::types::EffectSpec::Send {
                address: outbox[0].0,
                message: outbox[0].1,
            },
        );
        assert(detached_flight_control(emitted, fid)) by {
            reveal(crate::state::spec_emit);
            reveal(detached_flight_control);
            reveal(production_core_control_body);
        };
        assert(store_certificates_extend(state, emitted)) by {
            reveal(crate::state::spec_emit);
            reveal(store_certificates_extend);
        };
        lemma_send_all_preserves_detached_flight_control(
            emitted,
            fid,
            outbox.drop_first(),
        );
        lemma_store_certificate_extension_transitive(
            state,
            emitted,
            crate::handler_docs::spec_send_all(
                emitted,
                outbox.drop_first(),
            ),
        );
    } else {
        reveal(store_certificates_extend);
    }
}

pub proof fn lemma_fail_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    error: Seq<char>,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_fail(state, flight, error),
        ),
{
    reveal(crate::handler_docs::spec_fail);
    let emitted = match flight.work {
        crate::handler_docs::WorkSpec::Request { id, .. } =>
            crate::state::spec_emit(
                state,
                crate::types::EffectSpec::Reply {
                    id,
                    response: Err(error),
                },
            ),
        crate::handler_docs::WorkSpec::Sweep { .. } =>
            crate::state::spec_note(
                crate::state::spec_note(
                    state,
                    crate::types::NoteSpec::Sweep(
                        crate::types::SweepOutcome::Failed,
                    ),
                ),
                crate::types::NoteSpec::SweepEnd {
                    flight: flight.id,
                    committed: false,
                },
            ),
        crate::handler_docs::WorkSpec::Fire { .. } => state,
    };
    assert(detached_flight_control(emitted, flight.id)) by {
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(detached_flight_control);
        reveal(production_core_control_body);
    };
    lemma_finish_preserves_core_control_body(
        emitted,
        flight,
        Err(error),
    );
}

pub proof fn lemma_committed_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    done: crate::handler_docs::DoneSpec,
    fired: crate::types::Fired,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_committed(
                state,
                flight,
                done,
                fired,
            ),
        ),
{
    reveal(crate::handler_docs::spec_committed);
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    assert(detached_flight_control(noted, flight.id)) by {
        reveal(crate::state::spec_note);
        reveal(detached_flight_control);
        reveal(production_core_control_body);
    };
    lemma_send_all_preserves_detached_flight_control(
        noted,
        flight.id,
        done.outbox,
    );
    let sent = crate::handler_docs::spec_send_all(noted, done.outbox);
    let answered = match flight.work {
        crate::handler_docs::WorkSpec::Request {
            id,
            kind,
            corr,
            action_kind,
            ..
        } => {
            let response = match done.response {
                Some(response) => Ok(crate::types::AnswerSpec::Step {
                    kind,
                    corr,
                    action_kind,
                    response,
                    why: done.why,
                }),
                None => Err("no answer"@),
            };
            crate::state::spec_emit(
                sent,
                crate::types::EffectSpec::Reply { id, response },
            )
        },
        crate::handler_docs::WorkSpec::Sweep { .. } =>
            crate::state::spec_note(
                crate::state::spec_note(
                    sent,
                    crate::types::NoteSpec::Sweep(
                        if done.did {
                            crate::types::SweepOutcome::Fired
                        } else {
                            crate::types::SweepOutcome::Idle
                        },
                    ),
                ),
                crate::types::NoteSpec::SweepEnd {
                    flight: flight.id,
                    committed: true,
                },
            ),
        crate::handler_docs::WorkSpec::Fire { .. } => sent,
    };
    assert(detached_flight_control(answered, flight.id)) by {
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(detached_flight_control);
        reveal(production_core_control_body);
    };
    lemma_finish_preserves_core_control_body(
        answered,
        crate::handler_docs::FlightSpec {
            idle: !done.did,
            ..flight
        },
        Ok(fired),
    );
}

#[verifier::spinoff_prover]
pub proof fn lemma_store_issuance_then_flight_attachment_preserves_core_control(
    state: S,
    request: echod_concrete::store::StoreReqSpec,
    fid: u64,
    certificate:
        crate::global_store_invariants::StoreEffectCertificateV,
    replacement: crate::handler_docs::FlightSpec,
)
    requires
        detached_flight_control(state, fid),
        certificate
            == crate::global_store_invariants::
                StoreEffectCertificateV::Other,
        crate::global_store_invariants::
            invariant1_certificate_matches_request(
                state.keys.prefix,
                state.keys.bucket_ms,
                request,
                certificate,
            ),
        ({
            let stored = crate::state::spec_store_raw(
                state,
                request,
                Owner::Flight(fid),
                certificate,
            );
            &&& stored.1 is Some
            &&& replacement.id == fid
            &&& replacement.phase.expects() == stored.1
        }),
    ensures
        ({
            let stored = crate::state::spec_store_raw(
                state,
                request,
                Owner::Flight(fid),
                certificate,
            );
            let issued = stored.1.unwrap();
            let next = crate::handler_docs::spec_inflight(
                stored.0,
                replacement,
            );
            production_core_control_body(next)
        }),
        ({
            let stored = crate::state::spec_store_raw(
                state,
                request,
                Owner::Flight(fid),
                certificate,
            );
            let issued = stored.1.unwrap();
            &&& stored.0.ops.contains_key(issued)
            &&& stored.0.ops[issued] == Owner::Flight(fid)
        }),
        ({
            let stored = crate::state::spec_store_raw(
                state,
                request,
                Owner::Flight(fid),
                certificate,
            );
            let issued = stored.1.unwrap();
            &&& stored.0.store_requests.contains_key(issued)
            &&& stored.0.store_requests[issued] == request
        }),
        ({
            let stored = crate::state::spec_store_raw(
                state,
                request,
                Owner::Flight(fid),
                certificate,
            );
            let issued = stored.1.unwrap();
            &&& stored.0.store_certificates.contains_key(issued)
            &&& stored.0.store_certificates[issued] == certificate
        }),
        ({
            let stored = crate::state::spec_store_raw(
                state,
                request,
                Owner::Flight(fid),
                certificate,
            );
            let issued = stored.1.unwrap();
            let next = crate::handler_docs::spec_inflight(
                stored.0,
                replacement,
            );
            &&& next.flights.inflight.contains_key(fid)
            &&& next.flights.inflight[fid] == replacement
            &&& replacement.phase.expects() == Some(issued)
        }),
{
    lemma_store_raw_preserves_exact_maps_and_pending(
        state,
        request,
        Owner::Flight(fid),
        certificate,
    );
    reveal(crate::state::spec_store_raw);
    reveal(crate::handler_docs::spec_inflight);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(pending_store_effects_are_exact);
    reveal(active_flights_precede_allocator);
    reveal(active_flight_owners_match_phase);
    reveal(active_flight_ids_match_keys);
    let stored = crate::state::spec_store_raw(
        state,
        request,
        Owner::Flight(fid),
        certificate,
    );
    let issued = stored.1.unwrap();
    let next = crate::handler_docs::spec_inflight(
        stored.0,
        replacement,
    );
    assert(stored.1 == Some(issued));
    assert(replacement.id == fid);
    assert forall|op: u64|
        stored.0.ops.contains_key(op)
            && stored.0.ops[op] == Owner::Flight(fid)
        implies op == issued by {
        if state.ops.contains_key(op) {
            assert(state.ops[op] != Owner::Flight(fid));
        }
    };
    assert(active_flights_precede_allocator(next)) by {
        assert forall|current: u64|
            next.flights.inflight.contains_key(current) implies {
                &&& current <= next.next_flight
                &&& !next.flights_exhausted ==>
                    current < next.next_flight
            } by {
            if current != fid {
                assert(state.flights.inflight.contains_key(current));
            }
        };
    };
    assert(active_flight_owners_match_phase(next)) by {
        assert forall|op: u64, owner: u64|
            next.ops.contains_key(op)
                && next.ops[op] == Owner::Flight(owner) implies {
                    &&& next.flights.inflight.contains_key(owner)
                    &&& next.flights.inflight[owner].phase.expects()
                        == Some(op)
                } by {
            if owner == fid {
                assert(op == issued);
            } else {
                assert(state.ops.contains_key(op));
                assert(state.ops[op] == Owner::Flight(owner));
                assert(state.flights.inflight.contains_key(owner));
            }
        };
    };
    assert(active_flight_ids_match_keys(next)) by {
        assert forall|current: u64|
            next.flights.inflight.contains_key(current) implies
                next.flights.inflight[current].id == current by {
            if current != fid {
                assert(state.flights.inflight.contains_key(current));
            }
        };
    };
    assert(stored.0.ops.contains_key(issued));
    assert(stored.0.ops[issued] == Owner::Flight(fid));
    assert(stored.0.store_requests.contains_key(issued));
    assert(stored.0.store_requests[issued] == request);
    assert(stored.0.store_certificates.contains_key(issued));
    assert(stored.0.store_certificates[issued] == certificate);
    assert(next.flights.inflight.contains_key(fid));
    assert(next.flights.inflight[fid] == replacement);
    assert(replacement.phase.expects() == Some(issued));
    assert forall|op: u64| state.ops.contains_key(op) implies {
        &&& stored.0.ops.contains_key(op)
        &&& stored.0.ops[op] == state.ops[op]
        &&& stored.0.store_requests[op] == state.store_requests[op]
        &&& stored.0.store_certificates[op]
            == state.store_certificates[op]
    } by {
        assert(op != issued);
    };
    assert forall|other: u64|
        state.flights.inflight.contains_key(other)
            && other != fid implies
            next.flights.inflight[other]
                == state.flights.inflight[other] by {};
    assert(crate::production_relation::operation_allocator_consistent(next));
    assert(exact_store_certificate_maps(
        next.keys.prefix,
        next.keys.bucket_ms,
        next.store_requests,
        next.ops,
        next.store_certificates,
    ));
    assert(pending_store_effects_are_exact(next));
    assert(noncommit_certificates_are_other(next)) by {
        reveal(noncommit_certificates_are_other);
        assert forall|op: u64|
            next.ops.contains_key(op)
                && !(next.ops[op] is Flight) implies
                next.store_certificates[op]
                    == crate::global_store_invariants::
                        StoreEffectCertificateV::Other by {
            if op == issued {
                assert(next.ops[op] == Owner::Flight(fid));
                assert(next.store_certificates[op]
                    == crate::global_store_invariants::
                        StoreEffectCertificateV::Other);
                assert(next.flights.inflight[fid] == replacement);
                match replacement.phase {
                    crate::handler_docs::PhaseSpec::Origin { .. }
                    | crate::handler_docs::PhaseSpec::Schedule { .. }
                    | crate::handler_docs::PhaseSpec::FireIdle { .. }
                    | crate::handler_docs::PhaseSpec::FireOrigin { .. }
                    | crate::handler_docs::PhaseSpec::FireSchedule {
                        ..
                    } => {},
                    _ => {},
                }
            } else {
                assert(state.ops.contains_key(op));
            }
        };
    };
    assert forall|op: u64|
        next.ops.contains_key(op) implies
            next.ops[op] != Owner::Debug by {
        if op == issued {
            assert(next.ops[op] == Owner::Flight(fid));
        } else {
            assert(state.ops.contains_key(op));
        }
    };
    assert(next.debug == state.debug);
    assert(production_core_control_body(next));
}

#[verifier::spinoff_prover]
pub proof fn lemma_begin_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_begin(state, flight),
        ),
{
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_raw);
    reveal(crate::handler_docs::spec_inflight);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire { schedule, .. } => {
            let request = echod_concrete::store::StoreReqSpec::Get {
                key: crate::keys::spec_sched_key(
                    state.keys.prefix,
                    schedule,
                ),
            };
            lemma_store_raw_preserves_exact_maps_and_pending(
                state,
                request,
                Owner::Flight(flight.id),
                crate::global_store_invariants::
                    StoreEffectCertificateV::Other,
            );
            let stored = crate::state::spec_store_raw(
                state,
                request,
                Owner::Flight(flight.id),
                crate::global_store_invariants::
                    StoreEffectCertificateV::Other,
            );
            if stored.1 is Some {
                lemma_store_issuance_then_flight_attachment_preserves_core_control(
                    state,
                    request,
                    flight.id,
                    crate::global_store_invariants::
                        StoreEffectCertificateV::Other,
                    crate::handler_docs::FlightSpec {
                        phase:
                            crate::handler_docs::PhaseSpec::
                                FireLoadingSchedule {
                                    op: stored.1.unwrap(),
                                },
                        ..flight
                    },
                );
            } else {
                lemma_op_exhausted_preserves_core_control_body(
                    state,
                    flight,
                );
            }
        },
        _ => match flight.target {
            crate::target::TargetSpec::Origin(origin) => {
                reveal(crate::cache::spec_get);
                let cache_result =
                    crate::cache::spec_get(state.cache, origin);
                let looked = S {
                    cache: cache_result.0,
                    ..state
                };
                assert(production_core_control_body(looked)) by {
                    reveal(production_core_control_body);
                };
                match cache_result.1 {
                    Some(cached) => {
                        let request =
                            echod_concrete::store::StoreReqSpec::
                                GetIfNoneMatch {
                                    key: crate::keys::spec_doc_key(
                                        state.keys.prefix,
                                        origin,
                                    ),
                                    etag: cached.etag,
                                };
                        lemma_store_raw_preserves_exact_maps_and_pending(
                            looked,
                            request,
                            Owner::Flight(flight.id),
                            crate::global_store_invariants::
                                StoreEffectCertificateV::Other,
                        );
                        let stored = crate::state::spec_store_raw(
                            looked,
                            request,
                            Owner::Flight(flight.id),
                            crate::global_store_invariants::
                                StoreEffectCertificateV::Other,
                        );
                        if stored.1 is Some {
                            lemma_store_issuance_then_flight_attachment_preserves_core_control(
                                looked,
                                request,
                                flight.id,
                                crate::global_store_invariants::
                                    StoreEffectCertificateV::Other,
                                crate::handler_docs::FlightSpec {
                                    phase:
                                        crate::handler_docs::PhaseSpec::
                                            Loading {
                                                op: stored.1.unwrap(),
                                                revalidating: Some(cached),
                                            },
                                    ..flight
                                },
                            );
                        } else {
                            lemma_op_exhausted_preserves_core_control_body(
                                looked,
                                flight,
                            );
                        }
                    },
                    None => {
                        let noted = crate::state::spec_note(
                            looked,
                            crate::types::NoteSpec::Cache(
                                crate::types::CacheResult::Miss,
                            ),
                        );
                        assert(production_core_control_body(noted)) by {
                            reveal(crate::state::spec_note);
                            reveal(production_core_control_body);
                        };
                        let request =
                            echod_concrete::store::StoreReqSpec::Get {
                                key: crate::keys::spec_doc_key(
                                    state.keys.prefix,
                                    origin,
                                ),
                            };
                        lemma_store_raw_preserves_exact_maps_and_pending(
                            noted,
                            request,
                            Owner::Flight(flight.id),
                            crate::global_store_invariants::
                                StoreEffectCertificateV::Other,
                        );
                        let stored = crate::state::spec_store_raw(
                            noted,
                            request,
                            Owner::Flight(flight.id),
                            crate::global_store_invariants::
                                StoreEffectCertificateV::Other,
                        );
                        if stored.1 is Some {
                            lemma_store_issuance_then_flight_attachment_preserves_core_control(
                                noted,
                                request,
                                flight.id,
                                crate::global_store_invariants::
                                    StoreEffectCertificateV::Other,
                                crate::handler_docs::FlightSpec {
                                    phase:
                                        crate::handler_docs::PhaseSpec::
                                            Loading {
                                                op: stored.1.unwrap(),
                                                revalidating: None,
                                            },
                                    ..flight
                                },
                            );
                        } else {
                            lemma_op_exhausted_preserves_core_control_body(
                                noted,
                                flight,
                            );
                        }
                    },
                }
            },
            crate::target::TargetSpec::Schedule(id) => {
                let request = echod_concrete::store::StoreReqSpec::Get {
                    key: crate::keys::spec_sched_key(
                        state.keys.prefix,
                        id,
                    ),
                };
                lemma_store_raw_preserves_exact_maps_and_pending(
                    state,
                    request,
                    Owner::Flight(flight.id),
                    crate::global_store_invariants::
                        StoreEffectCertificateV::Other,
                );
                let stored = crate::state::spec_store_raw(
                    state,
                    request,
                    Owner::Flight(flight.id),
                    crate::global_store_invariants::
                        StoreEffectCertificateV::Other,
                );
                if stored.1 is Some {
                    lemma_store_issuance_then_flight_attachment_preserves_core_control(
                        state,
                        request,
                        flight.id,
                        crate::global_store_invariants::
                            StoreEffectCertificateV::Other,
                        crate::handler_docs::FlightSpec {
                            phase:
                                crate::handler_docs::PhaseSpec::Loading {
                                    op: stored.1.unwrap(),
                                    revalidating: None,
                                },
                            ..flight
                        },
                    );
                } else {
                    lemma_op_exhausted_preserves_core_control_body(
                        state,
                        flight,
                    );
                }
            },
        },
    }
}

pub proof fn lemma_retry_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_retry(state, flight),
        ),
{
    reveal(crate::handler_docs::spec_retry);
    let retried = crate::handler_docs::FlightSpec {
        attempt: flight.attempt.wrapping_add(1),
        ..flight
    };
    if retried.attempt > state.flights.max_retries {
        let noted = crate::state::spec_note(
            state,
            crate::types::NoteSpec::Commit(
                crate::types::CommitOutcome::Exhausted,
            ),
        );
        assert(detached_flight_control(noted, flight.id)) by {
            reveal(crate::state::spec_note);
            reveal(detached_flight_control);
            reveal(production_core_control_body);
        };
        lemma_fail_preserves_core_control_body(
            noted,
            retried,
            "too many races on the "@ + match retried.target {
                crate::target::TargetSpec::Origin(_) => "document"@,
                crate::target::TargetSpec::Schedule(_) => "schedule"@,
            },
        );
    } else {
        lemma_begin_preserves_core_control_body(state, retried);
    }
}

pub proof fn lemma_commit_failed_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    error: echod_concrete::store::StoreErrorSpec,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_commit_failed(
                state,
                flight,
                error,
            ),
        ),
{
    reveal(crate::handler_docs::spec_commit_failed);
    let forgotten = match flight.target {
        crate::target::TargetSpec::Origin(origin) =>
            crate::state::spec_forget_origin(state, origin),
        _ => state,
    };
    assert(detached_flight_control(forgotten, flight.id)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(detached_flight_control);
        reveal(production_core_control_body);
    };
    match error {
        echod_concrete::store::StoreErrorSpec::PreconditionFailed => {
            let noted = crate::state::spec_note(
                crate::state::spec_note(
                    forgotten,
                    crate::types::NoteSpec::Commit(
                        crate::types::CommitOutcome::Raced,
                    ),
                ),
                crate::types::NoteSpec::Raced {
                    target: crate::target::spec_name(flight.target),
                    attempt: flight.attempt,
                },
            );
            assert(detached_flight_control(noted, flight.id)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_retry_preserves_core_control_body(noted, flight);
        },
        _ => {
            let noted = crate::state::spec_note(
                forgotten,
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Failed,
                ),
            );
            assert(detached_flight_control(noted, flight.id)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_fail_preserves_core_control_body(
                noted,
                flight,
                crate::types::spec_error_text(error),
            );
        },
    }
}

pub proof fn lemma_run_origin_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        detached_flight_control(state, flight.id),
        decision_issuance_control_ready(state, flight, working),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_run_origin(
                state,
                flight,
                working,
            ),
        ),
{
    reveal(crate::handler_docs::spec_run_origin);
    lemma_decide_preserves_detached_flight_control(
        state,
        flight.id,
        flight.work,
        working,
    );
    let decided = crate::handler_docs::spec_decide(
        state,
        flight.work,
        working,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        decided.0,
        flight.id,
        decided.1,
        None,
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            decided.0,
            flight.id,
            decided.1,
            None,
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            let replacement = crate::handler_docs::FlightSpec {
                phase: crate::handler_docs::PhaseSpec::Origin {
                    commit: advanced.1,
                    done: decided.2,
                },
                ..flight
            };
            lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                decided.0,
                flight.id,
                decided.1,
                None,
                replacement,
            );
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            lemma_committed_preserves_core_control_body(
                advanced.0,
                flight,
                decided.2,
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            lemma_commit_failed_preserves_core_control_body(
                advanced.0,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_core_control_body(
                advanced.0,
                flight,
            );
        },
    }
}

pub proof fn lemma_run_schedule_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        detached_flight_control(state, flight.id),
        decision_issuance_control_ready(state, flight, working),
    ensures
        production_core_control_body(
            crate::handler_sched::spec_run_schedule(
                state,
                flight,
                working,
            ),
        ),
{
    reveal(crate::handler_sched::spec_run_schedule);
    lemma_decide_preserves_detached_flight_control(
        state,
        flight.id,
        flight.work,
        working,
    );
    let decided = crate::handler_docs::spec_decide(
        state,
        flight.work,
        working,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        decided.0,
        flight.id,
        decided.1,
        None,
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            decided.0,
            flight.id,
            decided.1,
            None,
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            let replacement = crate::handler_docs::FlightSpec {
                phase: crate::handler_docs::PhaseSpec::Schedule {
                    commit: advanced.1,
                    done: decided.2,
                },
                ..flight
            };
            lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                decided.0,
                flight.id,
                decided.1,
                None,
                replacement,
            );
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            lemma_committed_preserves_core_control_body(
                advanced.0,
                flight,
                decided.2,
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            lemma_commit_failed_preserves_core_control_body(
                advanced.0,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_core_control_body(
                advanced.0,
                flight,
            );
        },
    }
}

pub proof fn lemma_answered_loading_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    revalidating: Option<crate::cache::CachedSpec>,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, flight.id),
        answered_loading_issuance_control_ready(
            state,
            flight,
            revalidating,
            response,
        ),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_answered_loading(
                state,
                flight,
                revalidating,
                response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_loading);
    reveal(answered_loading_issuance_control_ready);
    match flight.target {
        crate::target::TargetSpec::Origin(origin) => {
            lemma_loaded_origin_preserves_detached_flight_control(
                state,
                flight.id,
                origin,
                revalidating,
                response,
            );
            let loaded = crate::handler_docs::spec_loaded_origin(
                state,
                origin,
                revalidating,
                response,
            );
            match loaded.1 {
                Ok(working) => {
                    lemma_run_origin_preserves_core_control_body(
                        loaded.0,
                        flight,
                        working,
                    );
                },
                Err(error) => {
                    lemma_fail_preserves_core_control_body(
                        loaded.0,
                        flight,
                        error,
                    );
                },
            }
        },
        crate::target::TargetSpec::Schedule(id) => {
            lemma_loaded_schedule_preserves_detached_flight_control(
                state,
                flight.id,
                id,
                response,
            );
            let loaded = crate::handler_sched::spec_loaded_schedule(
                state,
                id,
                response,
            );
            match loaded.1 {
                Ok(working) => {
                    lemma_run_schedule_preserves_core_control_body(
                        loaded.0,
                        flight,
                        working,
                    );
                },
                Err(error) => {
                    lemma_fail_preserves_core_control_body(
                        loaded.0,
                        flight,
                        error,
                    );
                },
            }
        },
    }
}

pub proof fn lemma_answered_origin_preserves_core_control_body(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
        commit_issuance_control_ready(
            state,
            fid,
            commit,
            Some(response),
        ),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_answered_origin(
                state,
                fid,
                flight,
                commit,
                done,
                response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_origin);
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state,
            fid,
            commit,
            Some(response),
        );
    }
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state,
            fid,
            commit,
            Some(response),
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                state,
                fid,
                commit,
                Some(response),
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::Origin {
                        commit: advanced.1,
                        done,
                    },
                    ..flight
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            lemma_committed_preserves_core_control_body(
                advanced.0,
                flight,
                done,
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            lemma_commit_failed_preserves_core_control_body(
                advanced.0,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_core_control_body(
                advanced.0,
                flight,
            );
        },
    }
}

pub proof fn lemma_answered_schedule_preserves_core_control_body(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
        commit_issuance_control_ready(
            state,
            fid,
            commit,
            Some(response),
        ),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_answered_schedule(
                state,
                fid,
                flight,
                commit,
                done,
                response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_schedule);
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state,
            fid,
            commit,
            Some(response),
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                state,
                fid,
                commit,
                Some(response),
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::Schedule {
                        commit: advanced.1,
                        done,
                    },
                    ..flight
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            lemma_committed_preserves_core_control_body(
                advanced.0,
                flight,
                done,
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            lemma_commit_failed_preserves_core_control_body(
                advanced.0,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_core_control_body(
                advanced.0,
                flight,
            );
        },
    }
}

pub proof fn lemma_fire_claim_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        production_core_control_body(
            crate::handler_sched::spec_fire_claim(
                state,
                flight,
                context,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_claim);
    let origin = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    let slot = crate::handler_docs::spec_slot_of(state, origin);
    if slot.busy is Some {
        let queued = crate::handler_docs::spec_with_slot(
            state,
            origin,
            crate::handler_docs::SlotSpec {
                queue: slot.queue.push(
                    crate::handler_docs::QueuedSpec::Waiter(flight.id),
                ),
                ..slot
            },
        );
        assert(detached_flight_control(queued, flight.id)) by {
            reveal(crate::handler_docs::spec_with_slot);
            reveal(detached_flight_control);
            reveal(production_core_control_body);
        };
        reveal(crate::handler_docs::spec_inflight);
        reveal(detached_flight_control);
        reveal(production_core_control_body);
        reveal(active_flights_precede_allocator);
        reveal(active_flight_owners_match_phase);
    } else {
        let claimed = crate::handler_docs::spec_with_slot(
            state,
            origin,
            crate::handler_docs::SlotSpec {
                busy: Some(flight.id),
                ..slot
            },
        );
        assert(detached_flight_control(claimed, flight.id)) by {
            reveal(crate::handler_docs::spec_with_slot);
            reveal(detached_flight_control);
            reveal(production_core_control_body);
        };
        lemma_fire_load_origin_preserves_core_control_body(
            claimed,
            flight,
            context,
        );
    }
}

pub proof fn lemma_fire_idle_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    at: u64,
    fired: Option<crate::verified::flight_spec::AFired>,
)
    requires
        detached_flight_control(state, flight.id),
        fire_idle_issuance_control_ready(
            state,
            flight,
            working,
            at,
            fired,
        ),
    ensures
        production_core_control_body(
            crate::handler_sched::spec_fire_idle(
                state,
                flight,
                working,
                at,
                fired,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_idle);
    reveal(fire_idle_issuance_control_ready);
    let idle = crate::handler_docs::FlightSpec {
        idle: true,
        ..flight
    };
    assert(idle.id == flight.id);
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::SweepBegin {
            flight: idle.id,
            target: working.target,
            now: at,
        },
    );
    assert(detached_flight_control(noted, idle.id)) by {
        reveal(crate::state::spec_note);
        reveal(detached_flight_control);
        reveal(production_core_control_body);
    };
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        crate::document::spec_loaded_body(working.loaded),
        echod_concrete::node::spec_body_deadline(
            crate::document::spec_loaded_body(working.loaded),
        ),
        at,
        fired,
    );
    assert(detached_flight_control(committed.0, idle.id)) by {
        reveal(crate::handler_docs::spec_commit_new);
        reveal(detached_flight_control);
        reveal(production_core_control_body);
    };
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        idle.id,
        committed.1,
        None,
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            committed.0,
            idle.id,
            committed.1,
            None,
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                committed.0,
                idle.id,
                committed.1,
                None,
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::FireIdle {
                        commit: advanced.1,
                    },
                    ..idle
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(result) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::SweepEnd {
                        flight: idle.id,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            assert(detached_flight_control(ended, idle.id)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_finish_preserves_core_control_body(
                ended,
                idle,
                Ok(result),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::SweepEnd {
                    flight: idle.id,
                    committed: false,
                },
            );
            assert(detached_flight_control(ended, idle.id)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_commit_failed_preserves_core_control_body(
                ended,
                idle,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_core_control_body(
                advanced.0,
                idle,
            );
        },
    }
}

pub proof fn lemma_fire_decide_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        detached_flight_control(state, flight.id),
        fire_decide_issuance_control_ready(
            state,
            flight,
            working,
        ),
    ensures
        production_core_control_body(
            crate::handler_sched::spec_fire_decide(
                state,
                flight,
                working,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_decide);
    reveal(fire_decide_issuance_control_ready);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire {
            fired,
            now,
            ..
        } => {
            let at = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(working.loaded),
                now,
            );
            let body = crate::document::spec_loaded_body(working.loaded);
            let transition = crate::verified::flight_spec::spec_step(
                crate::verified::flight_spec::AJob::Fire,
                body,
                at,
                state.cfg.retry_timeout,
            );
            let due = match (
                crate::handler_sched::spec_schedule_row(body),
                transition.2.len() > 0,
            ) {
                (Some(row), true) => Some((row, transition.2.last())),
                _ => None,
            };
            match due {
                None => {
                    lemma_fire_idle_preserves_core_control_body(
                        state,
                        flight,
                        working,
                        at,
                        fired,
                    );
                },
                Some((row, pending)) => {
                    let next = match
                        crate::handler_sched::spec_schedule_row(
                            transition.0,
                        )
                    {
                        Some(schedule) => schedule.next_run_at,
                        None => pending.at,
                    };
                    lemma_fire_claim_preserves_core_control_body(
                        state,
                        flight,
                        crate::handler_docs::FireCtxSpec {
                            ws: working,
                            row,
                            advanced: transition.0,
                            pending,
                            t1: at,
                            origin: echod_types::origin(pending.promise),
                            next,
                        },
                    );
                },
            }
        },
        _ => {
            lemma_fail_preserves_core_control_body(
                state,
                flight,
                "not a fire"@,
            );
        },
    }
}

pub proof fn lemma_answered_fire_loading_schedule_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, flight.id),
        answered_fire_loading_schedule_issuance_control_ready(
            state,
            flight,
            response,
        ),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_answered_fire_loading_schedule(
                state,
                flight,
                response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_loading_schedule);
    reveal(answered_fire_loading_schedule_issuance_control_ready);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire { schedule, .. } => {
            lemma_loaded_schedule_preserves_detached_flight_control(
                state,
                flight.id,
                schedule,
                response,
            );
            let loaded = crate::handler_sched::spec_loaded_schedule(
                state,
                schedule,
                response,
            );
            match loaded.1 {
                Ok(working) => {
                    lemma_fire_decide_preserves_core_control_body(
                        loaded.0,
                        flight,
                        working,
                    );
                },
                Err(error) => {
                    lemma_fail_preserves_core_control_body(
                        loaded.0,
                        flight,
                        error,
                    );
                },
            }
        },
        _ => {
            lemma_fail_preserves_core_control_body(
                state,
                flight,
                "not a fire"@,
            );
        },
    }
}

pub proof fn lemma_fire_advance_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
)
    requires
        detached_flight_control(state, flight.id),
        fire_advance_issuance_control_ready(
            state,
            flight,
            context,
            at,
        ),
    ensures
        production_core_control_body(
            crate::handler_sched::spec_fire_advance(
                state,
                flight,
                context,
                at,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_advance);
    reveal(fire_advance_issuance_control_ready);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire {
            schedule,
            fired,
            ..
        } => {
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::AdvanceBegin {
                    flight: flight.id,
                    schedule,
                    now: at,
                    at: context.pending.at,
                    next: context.next,
                },
            );
            assert(detached_flight_control(noted, flight.id)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            let committed = crate::handler_docs::spec_commit_new(
                noted,
                context.ws,
                context.advanced,
                echod_concrete::node::spec_body_deadline(
                    context.advanced,
                ),
                at,
                fired,
            );
            assert(detached_flight_control(
                committed.0,
                flight.id,
            )) by {
                reveal(crate::handler_docs::spec_commit_new);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            let advanced = crate::handler_docs::spec_commit_advance(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            if advanced.2 !is Issued {
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    committed.0,
                    flight.id,
                    committed.1,
                    None,
                );
            }
            match advanced.2 {
                crate::handler_docs::ProgressSpec::Issued => {
                    lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                        committed.0,
                        flight.id,
                        committed.1,
                        None,
                        crate::handler_docs::FlightSpec {
                            phase:
                                crate::handler_docs::PhaseSpec::FireSchedule {
                                    commit: advanced.1,
                                },
                            ..flight
                        },
                    );
                },
                crate::handler_docs::ProgressSpec::Done(result) => {
                    let ended = crate::state::spec_note(
                        crate::state::spec_note(
                            advanced.0,
                            crate::types::NoteSpec::AdvanceEnd {
                                flight: flight.id,
                                committed: true,
                            },
                        ),
                        crate::types::NoteSpec::Commit(
                            crate::types::CommitOutcome::Committed,
                        ),
                    );
                    assert(detached_flight_control(
                        ended,
                        flight.id,
                    )) by {
                        assert(detached_flight_control(
                            advanced.0,
                            flight.id,
                        ));
                        reveal(crate::state::spec_note);
                        reveal(detached_flight_control);
                        reveal(production_core_control_body);
                    };
                    lemma_finish_preserves_core_control_body(
                        ended,
                        flight,
                        Ok(result),
                    );
                },
                crate::handler_docs::ProgressSpec::Failed(error) => {
                    let ended = crate::state::spec_note(
                        advanced.0,
                        crate::types::NoteSpec::AdvanceEnd {
                            flight: flight.id,
                            committed: false,
                        },
                    );
                    assert(detached_flight_control(
                        ended,
                        flight.id,
                    )) by {
                        assert(detached_flight_control(
                            advanced.0,
                            flight.id,
                        ));
                        reveal(crate::state::spec_note);
                        reveal(detached_flight_control);
                        reveal(production_core_control_body);
                    };
                    lemma_commit_failed_preserves_core_control_body(
                        ended,
                        flight,
                        error,
                    );
                },
                crate::handler_docs::ProgressSpec::Exhausted => {
                    lemma_op_exhausted_preserves_core_control_body(
                        advanced.0,
                        flight,
                    );
                },
            }
        },
        _ => {
            lemma_fail_preserves_core_control_body(
                state,
                flight,
                "not a fire"@,
            );
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_fire_run_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        detached_flight_control(state, flight.id),
        fire_run_issuance_control_ready(
            state,
            flight,
            context,
            working,
        ),
        fire_run_followup_control_ready(
            state,
            flight,
            context,
            working,
        ),
    ensures
        production_core_control_body(
            crate::handler_sched::spec_fire_run(
                state,
                flight,
                context,
                working,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_run);
    reveal(fire_run_issuance_control_ready);
    reveal(fire_run_followup_control_ready);
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    let at = crate::document::spec_clamp_now(
        crate::document::spec_loaded_committed_at(working.loaded),
        context.t1,
    );
    let transition =
        echod_concrete::node::spec_occurrence_transition(
            crate::document::spec_loaded_body(working.loaded),
            context.pending,
            at,
            crate::handler_docs::spec_effective_retry_timeout(
                state.cfg.retry_timeout,
            ),
        );
    let outbox = crate::handler_docs::spec_dispatches(
        transition.0,
        transition.1,
    );
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::FireBegin {
            flight: flight.id,
            origin: context.origin,
            now: at,
            row: context.row,
            at: context.pending.at,
            promise_id: context.pending.promise,
            next: context.next,
        },
    );
    assert(detached_flight_control(noted, flight.id)) by {
        reveal(crate::state::spec_note);
        reveal(detached_flight_control);
        reveal(production_core_control_body);
    };
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        transition.0,
        echod_concrete::node::spec_body_deadline(transition.0),
        at,
        None,
    );
    assert(detached_flight_control(committed.0, flight.id)) by {
        reveal(crate::handler_docs::spec_commit_new);
        reveal(detached_flight_control);
        reveal(production_core_control_body);
    };
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            committed.0,
            flight.id,
            committed.1,
            None,
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                committed.0,
                flight.id,
                committed.1,
                None,
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::FireOrigin {
                        commit: advanced.1,
                        ctx: context,
                        t: at,
                        outbox,
                    },
                    ..flight
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(_) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::FireEnd {
                        flight: flight.id,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            assert(detached_flight_control(ended, flight.id)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_send_all_preserves_detached_flight_control(
                ended,
                flight.id,
                outbox,
            );
            let sent = crate::handler_docs::spec_send_all(ended, outbox);
            lemma_release_preserves_detached_flight_control(
                sent,
                secondary,
                flight.id,
            );
            let released = crate::handler_docs::spec_release(
                sent,
                secondary,
            );
            lemma_fire_advance_preserves_core_control_body(
                released,
                flight,
                context,
                at,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::FireEnd {
                    flight: flight.id,
                    committed: false,
                },
            );
            let forgotten = crate::state::spec_forget_origin(
                ended,
                context.origin,
            );
            assert(detached_flight_control(
                forgotten,
                flight.id,
            )) by {
                reveal(crate::state::spec_note);
                reveal(crate::state::spec_forget_origin);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_release_preserves_detached_flight_control(
                forgotten,
                secondary,
                flight.id,
            );
            let released = crate::handler_docs::spec_release(
                forgotten,
                secondary,
            );
            lemma_commit_failed_preserves_core_control_body(
                released,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            let forgotten = crate::state::spec_forget_origin(
                advanced.0,
                context.origin,
            );
            let abandoned = crate::handler_docs::spec_abandon_slot(
                forgotten,
                secondary,
            );
            assert(detached_flight_control(
                abandoned,
                flight.id,
            )) by {
                reveal(crate::state::spec_forget_origin);
                reveal(crate::handler_docs::spec_abandon_slot);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_op_exhausted_preserves_core_control_body(
                abandoned,
                flight,
            );
        },
    }
}

pub proof fn lemma_answered_fire_loading_origin_preserves_core_control_body(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    revalidating: Option<crate::cache::CachedSpec>,
    context: crate::handler_docs::FireCtxSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, flight.id),
        answered_fire_loading_origin_issuance_control_ready(
            state,
            flight,
            revalidating,
            context,
            response,
        ),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_answered_fire_loading_origin(
                state,
                flight,
                revalidating,
                context,
                response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_loading_origin);
    reveal(answered_fire_loading_origin_issuance_control_ready);
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    lemma_loaded_origin_preserves_detached_flight_control(
        state,
        flight.id,
        context.origin,
        revalidating,
        response,
    );
    let loaded = crate::handler_docs::spec_loaded_origin(
        state,
        context.origin,
        revalidating,
        response,
    );
    match loaded.1 {
        Ok(working) => {
            lemma_fire_run_preserves_core_control_body(
                loaded.0,
                flight,
                context,
                working,
            );
        },
        Err(error) => {
            lemma_release_preserves_detached_flight_control(
                loaded.0,
                secondary,
                flight.id,
            );
            let released = crate::handler_docs::spec_release(
                loaded.0,
                secondary,
            );
            lemma_fail_preserves_core_control_body(
                released,
                flight,
                error,
            );
        },
    }
}

pub proof fn lemma_answered_fire_idle_preserves_core_control_body(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
        commit_issuance_control_ready(
            state,
            fid,
            commit,
            Some(response),
        ),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_answered_fire_idle(
                state,
                fid,
                flight,
                commit,
                response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_idle);
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state,
            fid,
            commit,
            Some(response),
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                state,
                fid,
                commit,
                Some(response),
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::FireIdle {
                        commit: advanced.1,
                    },
                    ..flight
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(result) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::SweepEnd {
                        flight: fid,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            assert(detached_flight_control(ended, fid)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_finish_preserves_core_control_body(
                ended,
                flight,
                Ok(result),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::SweepEnd {
                    flight: fid,
                    committed: false,
                },
            );
            assert(detached_flight_control(ended, fid)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_commit_failed_preserves_core_control_body(
                ended,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_core_control_body(
                advanced.0,
                flight,
            );
        },
    }
}

pub proof fn lemma_answered_fire_origin_preserves_core_control_body(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
    outbox: Seq<(Seq<char>, crate::types::MessageSpec)>,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
        commit_issuance_control_ready(
            state,
            fid,
            commit,
            Some(response),
        ),
        answered_fire_origin_followup_control_ready(
            state,
            fid,
            flight,
            commit,
            context,
            at,
            outbox,
            response,
        ),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_answered_fire_origin(
                state,
                fid,
                flight,
                commit,
                context,
                at,
                outbox,
                response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_origin);
    reveal(answered_fire_origin_followup_control_ready);
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state,
            fid,
            commit,
            Some(response),
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                state,
                fid,
                commit,
                Some(response),
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::FireOrigin {
                        commit: advanced.1,
                        ctx: context,
                        t: at,
                        outbox,
                    },
                    ..flight
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(_) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::FireEnd {
                        flight: fid,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            assert(detached_flight_control(ended, fid)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_send_all_preserves_detached_flight_control(
                ended,
                fid,
                outbox,
            );
            let sent = crate::handler_docs::spec_send_all(ended, outbox);
            lemma_release_preserves_detached_flight_control(
                sent,
                secondary,
                fid,
            );
            let released = crate::handler_docs::spec_release(
                sent,
                secondary,
            );
            lemma_fire_advance_preserves_core_control_body(
                released,
                flight,
                context,
                at,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::FireEnd {
                    flight: fid,
                    committed: false,
                },
            );
            let forgotten = crate::state::spec_forget_origin(
                ended,
                context.origin,
            );
            assert(detached_flight_control(forgotten, fid)) by {
                reveal(crate::state::spec_note);
                reveal(crate::state::spec_forget_origin);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_release_preserves_detached_flight_control(
                forgotten,
                secondary,
                fid,
            );
            let released = crate::handler_docs::spec_release(
                forgotten,
                secondary,
            );
            lemma_commit_failed_preserves_core_control_body(
                released,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            let forgotten = crate::state::spec_forget_origin(
                advanced.0,
                context.origin,
            );
            let abandoned = crate::handler_docs::spec_abandon_slot(
                forgotten,
                secondary,
            );
            assert(detached_flight_control(abandoned, fid)) by {
                reveal(crate::state::spec_forget_origin);
                reveal(crate::handler_docs::spec_abandon_slot);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_op_exhausted_preserves_core_control_body(
                abandoned,
                flight,
            );
        },
    }
}

pub proof fn lemma_answered_fire_schedule_preserves_core_control_body(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
        commit_issuance_control_ready(
            state,
            fid,
            commit,
            Some(response),
        ),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_answered_fire_schedule(
                state,
                fid,
                flight,
                commit,
                response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_schedule);
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state,
            fid,
            commit,
            Some(response),
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            lemma_commit_advance_issued_then_inflight_preserves_core_control_body(
                state,
                fid,
                commit,
                Some(response),
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::FireSchedule {
                        commit: advanced.1,
                    },
                    ..flight
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(result) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::AdvanceEnd {
                        flight: fid,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            assert(detached_flight_control(ended, fid)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_finish_preserves_core_control_body(
                ended,
                flight,
                Ok(result),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::AdvanceEnd {
                    flight: fid,
                    committed: false,
                },
            );
            assert(detached_flight_control(ended, fid)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_commit_failed_preserves_core_control_body(
                ended,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_core_control_body(
                advanced.0,
                flight,
            );
        },
    }
}

proof fn lemma_answered_fire_schedule_extends_store_certificates(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
    ensures
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_fire_schedule(
                state,
                fid,
                flight,
                commit,
                response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_schedule);
    lemma_commit_advance_preserves_old_active_certificates(
        state,
        fid,
        commit,
        Some(response),
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state,
            fid,
            commit,
            Some(response),
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            assert(store_certificates_extend(
                advanced.0,
                crate::handler_docs::spec_inflight(
                    advanced.0,
                    crate::handler_docs::FlightSpec {
                        phase:
                            crate::handler_docs::PhaseSpec::FireSchedule {
                                commit: advanced.1,
                            },
                        ..flight
                    },
                ),
            )) by {
                reveal(crate::handler_docs::spec_inflight);
                reveal(store_certificates_extend);
            };
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_inflight(
                    advanced.0,
                    crate::handler_docs::FlightSpec {
                        phase:
                            crate::handler_docs::PhaseSpec::FireSchedule {
                                commit: advanced.1,
                            },
                        ..flight
                    },
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Done(result) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::AdvanceEnd {
                        flight: fid,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            assert(store_certificates_extend(advanced.0, ended)) by {
                reveal(crate::state::spec_note);
                reveal(store_certificates_extend);
            };
            assert(detached_flight_control(ended, fid)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            crate::global_store_invariants::
                lemma_finish_only_adds_nonappend(
                    ended,
                    flight,
                    Ok(result),
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                ended,
            );
            lemma_store_certificate_extension_transitive(
                state,
                ended,
                crate::handler_docs::spec_finish(
                    ended,
                    flight,
                    Ok(result),
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::AdvanceEnd {
                    flight: fid,
                    committed: false,
                },
            );
            assert(store_certificates_extend(advanced.0, ended)) by {
                reveal(crate::state::spec_note);
                reveal(store_certificates_extend);
            };
            assert(detached_flight_control(ended, fid)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            crate::global_store_invariants::
                lemma_commit_failed_only_adds_nonappend(
                    ended,
                    flight,
                    error,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                ended,
            );
            lemma_store_certificate_extension_transitive(
                state,
                ended,
                crate::handler_docs::spec_commit_failed(
                    ended,
                    flight,
                    error,
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            crate::global_store_invariants::
                lemma_op_exhausted_only_adds_nonappend(
                    advanced.0,
                    flight,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_op_exhausted(
                    advanced.0,
                    flight,
                ),
            );
        },
    }
}

#[verifier::spinoff_prover]
proof fn lemma_fire_idle_preserves_old_active_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    at: u64,
    fired: Option<crate::verified::flight_spec::AFired>,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        old_active_store_certificates_preserved(
            state,
            crate::handler_sched::spec_fire_idle(
                state, flight, working, at, fired,
            ),
        ),
        store_certificates_extend(
            state,
            crate::handler_sched::spec_fire_idle(
                state, flight, working, at, fired,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_idle);
    reveal(crate::handler_docs::spec_commit_new);
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_finish);
    reveal(crate::handler_docs::spec_release);
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_resume);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_without_slot);
    reveal(crate::handler_sched::spec_fire_load_origin);
    reveal(crate::handler_docs::spec_commit_failed);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_flight);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(crate::production_relation::operation_allocator_consistent);
    reveal(crate::production_relation::operation_id_fresh);
    reveal(old_active_store_certificates_preserved);
    let idle = crate::handler_docs::FlightSpec {
        idle: true,
        ..flight
    };
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::SweepBegin {
            flight: idle.id,
            target: working.target,
            now: at,
        },
    );
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        crate::document::spec_loaded_body(working.loaded),
        echod_concrete::node::spec_body_deadline(
            crate::document::spec_loaded_body(working.loaded),
        ),
        at,
        fired,
    );
    lemma_commit_advance_preserves_old_active_certificates(
        committed.0,
        idle.id,
        committed.1,
        None,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        idle.id,
        committed.1,
        None,
    );
    assert(store_certificates_extend(state, committed.0)) by {
        reveal(store_certificates_extend);
    };
    lemma_store_certificate_extension_transitive(
        state, committed.0, advanced.0,
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            assert(store_certificates_extend(
                advanced.0,
                crate::handler_docs::spec_inflight(
                    advanced.0,
                    crate::handler_docs::FlightSpec {
                        phase: crate::handler_docs::PhaseSpec::FireIdle {
                            commit: advanced.1,
                        },
                        ..idle
                    },
                ),
            )) by {
                reveal(store_certificates_extend);
            };
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_inflight(
                    advanced.0,
                    crate::handler_docs::FlightSpec {
                        phase: crate::handler_docs::PhaseSpec::FireIdle {
                            commit: advanced.1,
                        },
                        ..idle
                    },
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Done(result) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::SweepEnd {
                        flight: idle.id,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            assert(store_certificates_extend(advanced.0, ended)) by {
                reveal(store_certificates_extend);
            };
            crate::global_store_invariants::
                lemma_finish_only_adds_nonappend(
                    ended, idle, Ok(result),
                );
            lemma_store_certificate_extension_transitive(
                state, advanced.0, ended,
            );
            lemma_store_certificate_extension_transitive(
                state,
                ended,
                crate::handler_docs::spec_finish(
                    ended, idle, Ok(result),
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::SweepEnd {
                    flight: idle.id,
                    committed: false,
                },
            );
            assert(store_certificates_extend(advanced.0, ended)) by {
                reveal(store_certificates_extend);
            };
            crate::global_store_invariants::
                lemma_commit_failed_only_adds_nonappend(
                    ended, idle, error,
                );
            lemma_store_certificate_extension_transitive(
                state, advanced.0, ended,
            );
            lemma_store_certificate_extension_transitive(
                state,
                ended,
                crate::handler_docs::spec_commit_failed(
                    ended, idle, error,
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            crate::global_store_invariants::
                lemma_op_exhausted_only_adds_nonappend(
                    advanced.0, idle,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_op_exhausted(
                    advanced.0, idle,
                ),
            );
        },
    }
    reveal(store_certificates_extend);
}

#[verifier::spinoff_prover]
proof fn lemma_fire_claim_preserves_old_active_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        old_active_store_certificates_preserved(
            state,
            crate::handler_sched::spec_fire_claim(
                state, flight, context,
            ),
        ),
        store_certificates_extend(
            state,
            crate::handler_sched::spec_fire_claim(
                state, flight, context,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_claim);
    reveal(crate::handler_sched::spec_fire_load_origin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_flight);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(detached_flight_control);
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(crate::production_relation::operation_allocator_consistent);
    reveal(crate::production_relation::operation_id_fresh);
    reveal(old_active_store_certificates_preserved);
}

#[verifier::spinoff_prover]
proof fn lemma_fire_decide_preserves_old_active_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        detached_flight_control(state, flight.id),
        flight.work is Fire,
    ensures
        old_active_store_certificates_preserved(
            state,
            crate::handler_sched::spec_fire_decide(
                state, flight, working,
            ),
        ),
        store_certificates_extend(
            state,
            crate::handler_sched::spec_fire_decide(
                state, flight, working,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_decide);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire { fired, now, .. } => {
            let at = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(working.loaded),
                now,
            );
            let body = crate::document::spec_loaded_body(working.loaded);
            let transition = crate::verified::flight_spec::spec_step(
                crate::verified::flight_spec::AJob::Fire,
                body,
                at,
                state.cfg.retry_timeout,
            );
            match (
                crate::handler_sched::spec_schedule_row(body),
                transition.2.len() > 0,
            ) {
                (Some(row), true) => {
                    let pending = transition.2.last();
                    let next = match
                        crate::handler_sched::spec_schedule_row(
                            transition.0,
                        )
                    {
                        Some(schedule) => schedule.next_run_at,
                        None => pending.at,
                    };
                    lemma_fire_claim_preserves_old_active_certificates(
                        state,
                        flight,
                        crate::handler_docs::FireCtxSpec {
                            ws: working,
                            row,
                            advanced: transition.0,
                            pending,
                            t1: at,
                            origin: echod_types::origin(pending.promise),
                            next,
                        },
                    );
                },
                _ => {
                    lemma_fire_idle_preserves_old_active_certificates(
                        state, flight, working, at, fired,
                    );
                },
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_answered_fire_loading_schedule_fire_preserves_old_active_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, flight.id),
        flight.work is Fire,
    ensures
        old_active_store_certificates_preserved(
            state,
            crate::handler_docs::spec_answered_fire_loading_schedule(
                state, flight, response,
            ),
        ),
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_fire_loading_schedule(
                state, flight, response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_loading_schedule);
    reveal(crate::handler_sched::spec_loaded_schedule);
    reveal(crate::handler_docs::spec_fail);
    reveal(old_active_store_certificates_preserved);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire {
            fired,
            now,
            schedule,
        } => {
            let loaded = crate::handler_sched::spec_loaded_schedule(
                state, schedule, response,
            );
            match loaded.1 {
                Ok(working) => {
                    lemma_loaded_schedule_preserves_detached_flight_control(
                        state,
                        flight.id,
                        schedule,
                        response,
                    );
                    lemma_fire_decide_preserves_old_active_certificates(
                        loaded.0,
                        flight,
                        working,
                    );
                },
                Err(error) => {
                    crate::global_store_invariants::
                        lemma_fail_only_adds_nonappend(
                            loaded.0,
                            flight,
                            error,
                        );
                    reveal(store_certificates_extend);
                    assert(old_active_store_certificates_preserved(
                        state,
                        crate::handler_docs::
                            spec_answered_fire_loading_schedule(
                                state, flight, response,
                            ),
                    ));
                },
            }
        },
        _ => {
            crate::global_store_invariants::
                lemma_fail_only_adds_nonappend(
                    state,
                    flight,
                    "not a fire"@,
                );
            reveal(store_certificates_extend);
            assert(old_active_store_certificates_preserved(
                state,
                crate::handler_docs::
                    spec_answered_fire_loading_schedule(
                        state, flight, response,
                    ),
            ));
        },
    }
}

#[verifier::spinoff_prover]
proof fn lemma_answered_fire_loading_schedule_preserves_old_active_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        old_active_store_certificates_preserved(
            state,
            crate::handler_docs::spec_answered_fire_loading_schedule(
                state, flight, response,
            ),
        ),
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_fire_loading_schedule(
                state, flight, response,
            ),
        ),
{
    match flight.work {
        crate::handler_docs::WorkSpec::Fire { .. } => {
            lemma_answered_fire_loading_schedule_fire_preserves_old_active_certificates(
                state, flight, response,
            );
        },
        _ => {
            crate::global_store_invariants::
                lemma_fail_only_adds_nonappend(
                    state,
                    flight,
                    "not a fire"@,
                );
            reveal(
                crate::handler_docs::
                    spec_answered_fire_loading_schedule,
            );
            reveal(crate::handler_docs::spec_fail);
            reveal(store_certificates_extend);
            reveal(old_active_store_certificates_preserved);
        },
    }
}

#[verifier::spinoff_prover]
proof fn lemma_fire_advance_preserves_old_active_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        old_active_store_certificates_preserved(
            state,
            crate::handler_sched::spec_fire_advance(
                state, flight, context, at,
            ),
        ),
        store_certificates_extend(
            state,
            crate::handler_sched::spec_fire_advance(
                state, flight, context, at,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_advance);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire {
            schedule,
            fired,
            ..
        } => {
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::AdvanceBegin {
                    flight: flight.id,
                    schedule,
                    now: at,
                    at: context.pending.at,
                    next: context.next,
                },
            );
            let committed = crate::handler_docs::spec_commit_new(
                noted,
                context.ws,
                context.advanced,
                echod_concrete::node::spec_body_deadline(
                    context.advanced,
                ),
                at,
                fired,
            );
            assert(detached_flight_control(
                noted, flight.id,
            )) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            assert(detached_flight_control(
                committed.0, flight.id,
            )) by {
                reveal(crate::handler_docs::spec_commit_new);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_commit_advance_preserves_old_active_certificates(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            let advanced = crate::handler_docs::spec_commit_advance(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            if advanced.2 !is Issued {
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    committed.0,
                    flight.id,
                    committed.1,
                    None,
                );
            }
            assert(store_certificates_extend(
                state, committed.0,
            )) by {
                reveal(crate::state::spec_note);
                reveal(crate::handler_docs::spec_commit_new);
                reveal(store_certificates_extend);
            };
            lemma_store_certificate_extension_transitive(
                state, committed.0, advanced.0,
            );
            match advanced.2 {
                crate::handler_docs::ProgressSpec::Issued => {
                    let next = crate::handler_docs::spec_inflight(
                        advanced.0,
                        crate::handler_docs::FlightSpec {
                            phase:
                                crate::handler_docs::PhaseSpec::
                                    FireSchedule {
                                        commit: advanced.1,
                                    },
                            ..flight
                        },
                    );
                    assert(store_certificates_extend(
                        advanced.0, next,
                    )) by {
                        reveal(crate::handler_docs::spec_inflight);
                        reveal(store_certificates_extend);
                    };
                    lemma_store_certificate_extension_transitive(
                        state, advanced.0, next,
                    );
                },
                crate::handler_docs::ProgressSpec::Done(result) => {
                    let ended = crate::state::spec_note(
                        crate::state::spec_note(
                            advanced.0,
                            crate::types::NoteSpec::AdvanceEnd {
                                flight: flight.id,
                                committed: true,
                            },
                        ),
                        crate::types::NoteSpec::Commit(
                            crate::types::CommitOutcome::Committed,
                        ),
                    );
                    assert(store_certificates_extend(
                        advanced.0, ended,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(store_certificates_extend);
                    };
                    assert(detached_flight_control(
                        ended, flight.id,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(detached_flight_control);
                        reveal(production_core_control_body);
                    };
                    crate::global_store_invariants::
                        lemma_finish_only_adds_nonappend(
                            ended, flight, Ok(result),
                        );
                    lemma_store_certificate_extension_transitive(
                        state, advanced.0, ended,
                    );
                    lemma_store_certificate_extension_transitive(
                        state,
                        ended,
                        crate::handler_docs::spec_finish(
                            ended, flight, Ok(result),
                        ),
                    );
                },
                crate::handler_docs::ProgressSpec::Failed(error) => {
                    let ended = crate::state::spec_note(
                        advanced.0,
                        crate::types::NoteSpec::AdvanceEnd {
                            flight: flight.id,
                            committed: false,
                        },
                    );
                    assert(store_certificates_extend(
                        advanced.0, ended,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(store_certificates_extend);
                    };
                    assert(detached_flight_control(
                        ended, flight.id,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(detached_flight_control);
                        reveal(production_core_control_body);
                    };
                    crate::global_store_invariants::
                        lemma_commit_failed_only_adds_nonappend(
                            ended, flight, error,
                        );
                    lemma_store_certificate_extension_transitive(
                        state, advanced.0, ended,
                    );
                    lemma_store_certificate_extension_transitive(
                        state,
                        ended,
                        crate::handler_docs::spec_commit_failed(
                            ended, flight, error,
                        ),
                    );
                },
                crate::handler_docs::ProgressSpec::Exhausted => {
                    crate::global_store_invariants::
                        lemma_op_exhausted_only_adds_nonappend(
                            advanced.0, flight,
                        );
                    lemma_store_certificate_extension_transitive(
                        state,
                        advanced.0,
                        crate::handler_docs::spec_op_exhausted(
                            advanced.0, flight,
                        ),
                    );
                },
            }
            reveal(old_active_store_certificates_preserved);
            reveal(store_certificates_extend);
        },
        _ => {
            crate::global_store_invariants::
                lemma_fail_only_adds_nonappend(
                    state, flight, "not a fire"@,
                );
            reveal(crate::handler_docs::spec_fail);
            reveal(old_active_store_certificates_preserved);
            reveal(store_certificates_extend);
        },
    }
}

#[verifier::spinoff_prover]
proof fn lemma_answered_fire_origin_preserves_old_active_certificates(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
    outbox: Seq<(Seq<char>, crate::types::MessageSpec)>,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
    ensures
        old_active_store_certificates_preserved(
            state,
            crate::handler_docs::spec_answered_fire_origin(
                state, fid, flight, commit, context, at, outbox, response,
            ),
        ),
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_fire_origin(
                state, fid, flight, commit, context, at, outbox, response,
            ),
        ),
{
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    lemma_commit_advance_preserves_old_active_certificates(
        state, fid, commit, Some(response),
    );
    reveal(crate::handler_docs::spec_answered_fire_origin);
    let advanced = crate::handler_docs::spec_commit_advance(
        state, fid, commit, Some(response),
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state, fid, commit, Some(response),
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            let next = crate::handler_docs::spec_inflight(
                advanced.0,
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::FireOrigin {
                        commit: advanced.1,
                        ctx: context,
                        t: at,
                        outbox,
                    },
                    ..flight
                },
            );
            assert(store_certificates_extend(
                advanced.0, next,
            )) by {
                reveal(crate::handler_docs::spec_inflight);
                reveal(store_certificates_extend);
            };
            lemma_store_certificate_extension_transitive(
                state, advanced.0, next,
            );
        },
        crate::handler_docs::ProgressSpec::Done(_) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::FireEnd {
                        flight: fid,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            assert(detached_flight_control(
                ended, fid,
            )) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_send_all_preserves_detached_flight_control(
                ended, fid, outbox,
            );
            let sent = crate::handler_docs::spec_send_all(
                ended, outbox,
            );
            lemma_release_preserves_detached_flight_control(
                sent, secondary, fid,
            );
            let released = crate::handler_docs::spec_release(
                sent, secondary,
            );
            crate::global_store_invariants::
                lemma_release_only_adds_nonappend(
                    sent, secondary,
                );
            lemma_fire_advance_preserves_old_active_certificates(
                released, flight, context, at,
            );
            assert(store_certificates_extend(
                advanced.0, ended,
            )) by {
                reveal(crate::state::spec_note);
                reveal(store_certificates_extend);
            };
            lemma_store_certificate_extension_transitive(
                state, advanced.0, ended,
            );
            lemma_store_certificate_extension_transitive(
                state, ended, sent,
            );
            lemma_store_certificate_extension_transitive(
                state, sent, released,
            );
            lemma_store_certificate_extension_transitive(
                state,
                released,
                crate::handler_sched::spec_fire_advance(
                    released, flight, context, at,
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::FireEnd {
                    flight: fid,
                    committed: false,
                },
            );
            let forgotten = crate::state::spec_forget_origin(
                ended, context.origin,
            );
            assert(detached_flight_control(
                forgotten, fid,
            )) by {
                reveal(crate::state::spec_note);
                reveal(crate::state::spec_forget_origin);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            lemma_release_preserves_detached_flight_control(
                forgotten, secondary, fid,
            );
            let released = crate::handler_docs::spec_release(
                forgotten, secondary,
            );
            crate::global_store_invariants::
                lemma_release_only_adds_nonappend(
                    forgotten, secondary,
                );
            crate::global_store_invariants::
                lemma_commit_failed_only_adds_nonappend(
                    released, flight, error,
                );
            assert(store_certificates_extend(
                advanced.0, forgotten,
            )) by {
                reveal(crate::state::spec_note);
                reveal(crate::state::spec_forget_origin);
                reveal(store_certificates_extend);
            };
            lemma_store_certificate_extension_transitive(
                state, advanced.0, forgotten,
            );
            lemma_store_certificate_extension_transitive(
                state, forgotten, released,
            );
            lemma_store_certificate_extension_transitive(
                state,
                released,
                crate::handler_docs::spec_commit_failed(
                    released, flight, error,
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            let forgotten = crate::state::spec_forget_origin(
                advanced.0, context.origin,
            );
            let abandoned = crate::handler_docs::spec_abandon_slot(
                forgotten, secondary,
            );
            assert(detached_flight_control(
                abandoned, fid,
            )) by {
                reveal(crate::state::spec_forget_origin);
                reveal(crate::handler_docs::spec_abandon_slot);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            crate::global_store_invariants::
                lemma_op_exhausted_only_adds_nonappend(
                    abandoned, flight,
                );
            assert(store_certificates_extend(
                advanced.0, abandoned,
            )) by {
                reveal(crate::state::spec_forget_origin);
                reveal(crate::handler_docs::spec_abandon_slot);
                reveal(store_certificates_extend);
            };
            lemma_store_certificate_extension_transitive(
                state, advanced.0, abandoned,
            );
            lemma_store_certificate_extension_transitive(
                state,
                abandoned,
                crate::handler_docs::spec_op_exhausted(
                    abandoned, flight,
                ),
            );
        },
    }
    reveal(old_active_store_certificates_preserved);
    reveal(store_certificates_extend);
}

#[verifier::spinoff_prover]
proof fn lemma_answered_fire_loading_origin_extends_store_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    revalidating: Option<crate::cache::CachedSpec>,
    context: crate::handler_docs::FireCtxSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_fire_loading_origin(
                state,
                flight,
                revalidating,
                context,
                response,
            ),
        ),
{
    reveal(
        crate::handler_docs::spec_answered_fire_loading_origin,
    );
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    lemma_loaded_origin_preserves_detached_flight_control(
        state,
        flight.id,
        context.origin,
        revalidating,
        response,
    );
    let loaded = crate::handler_docs::spec_loaded_origin(
        state,
        context.origin,
        revalidating,
        response,
    );
    assert(store_certificates_extend(state, loaded.0)) by {
        reveal(crate::handler_docs::spec_loaded_origin);
        reveal(crate::state::spec_note);
        reveal(crate::state::spec_remember);
        reveal(crate::state::spec_forget_origin);
        reveal(store_certificates_extend);
    };
    match loaded.1 {
        Err(error) => {
            lemma_release_preserves_detached_flight_control(
                loaded.0, secondary, flight.id,
            );
            crate::global_store_invariants::
                lemma_release_only_adds_nonappend(
                    loaded.0, secondary,
                );
            let released = crate::handler_docs::spec_release(
                loaded.0, secondary,
            );
            crate::global_store_invariants::
                lemma_fail_only_adds_nonappend(
                    released, flight, error,
                );
            lemma_store_certificate_extension_transitive(
                state, loaded.0, released,
            );
            lemma_store_certificate_extension_transitive(
                state,
                released,
                crate::handler_docs::spec_fail(
                    released, flight, error,
                ),
            );
        },
        Ok(working) => {
            reveal(crate::handler_sched::spec_fire_run);
            let at = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(
                    working.loaded,
                ),
                context.t1,
            );
            let transition =
                echod_concrete::node::spec_occurrence_transition(
                    crate::document::spec_loaded_body(working.loaded),
                    context.pending,
                    at,
                    crate::handler_docs::spec_effective_retry_timeout(
                        loaded.0.cfg.retry_timeout,
                    ),
                );
            let outbox = crate::handler_docs::spec_dispatches(
                transition.0,
                transition.1,
            );
            let noted = crate::state::spec_note(
                loaded.0,
                crate::types::NoteSpec::FireBegin {
                    flight: flight.id,
                    origin: context.origin,
                    now: at,
                    row: context.row,
                    at: context.pending.at,
                    promise_id: context.pending.promise,
                    next: context.next,
                },
            );
            let committed = crate::handler_docs::spec_commit_new(
                noted,
                working,
                transition.0,
                echod_concrete::node::spec_body_deadline(
                    transition.0,
                ),
                at,
                None,
            );
            assert(detached_flight_control(
                committed.0, flight.id,
            )) by {
                reveal(crate::state::spec_note);
                reveal(crate::handler_docs::spec_commit_new);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            assert(store_certificates_extend(
                loaded.0, committed.0,
            )) by {
                reveal(crate::state::spec_note);
                reveal(crate::handler_docs::spec_commit_new);
                reveal(store_certificates_extend);
            };
            lemma_commit_advance_preserves_old_active_certificates(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            let advanced = crate::handler_docs::spec_commit_advance(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            lemma_store_certificate_extension_transitive(
                loaded.0, committed.0, advanced.0,
            );
            match advanced.2 {
                crate::handler_docs::ProgressSpec::Issued => {
                    let next = crate::handler_docs::spec_inflight(
                        advanced.0,
                        crate::handler_docs::FlightSpec {
                            phase:
                                crate::handler_docs::PhaseSpec::FireOrigin {
                                    commit: advanced.1,
                                    ctx: context,
                                    t: at,
                                    outbox,
                                },
                            ..flight
                        },
                    );
                    assert(store_certificates_extend(
                        advanced.0, next,
                    )) by {
                        reveal(crate::handler_docs::spec_inflight);
                        reveal(store_certificates_extend);
                    };
                    lemma_store_certificate_extension_transitive(
                        loaded.0, advanced.0, next,
                    );
                    lemma_store_certificate_extension_transitive(
                        state, loaded.0, next,
                    );
                },
                crate::handler_docs::ProgressSpec::Done(_) => {
                    lemma_commit_advance_nonissued_preserves_detached_flight_control(
                        committed.0,
                        flight.id,
                        committed.1,
                        None,
                    );
                    let ended = crate::state::spec_note(
                        crate::state::spec_note(
                            advanced.0,
                            crate::types::NoteSpec::FireEnd {
                                flight: flight.id,
                                committed: true,
                            },
                        ),
                        crate::types::NoteSpec::Commit(
                            crate::types::CommitOutcome::Committed,
                        ),
                    );
                    assert(detached_flight_control(
                        ended, flight.id,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(detached_flight_control);
                        reveal(production_core_control_body);
                    };
                    crate::global_store_invariants::
                        lemma_send_all_only_adds_nonappend(
                            ended, outbox,
                        );
                    lemma_send_all_preserves_detached_flight_control(
                        ended, flight.id, outbox,
                    );
                    let sent =
                        crate::handler_docs::spec_send_all(
                            ended, outbox,
                        );
                    lemma_release_preserves_detached_flight_control(
                        sent, secondary, flight.id,
                    );
                    crate::global_store_invariants::
                        lemma_release_only_adds_nonappend(
                            sent, secondary,
                        );
                    let released =
                        crate::handler_docs::spec_release(
                            sent, secondary,
                        );
                    lemma_fire_advance_preserves_old_active_certificates(
                        released, flight, context, at,
                    );
                    assert(store_certificates_extend(
                        advanced.0, ended,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(store_certificates_extend);
                    };
                    lemma_store_certificate_extension_transitive(
                        loaded.0, advanced.0, ended,
                    );
                    lemma_store_certificate_extension_transitive(
                        loaded.0, ended, sent,
                    );
                    lemma_store_certificate_extension_transitive(
                        loaded.0, sent, released,
                    );
                    lemma_store_certificate_extension_transitive(
                        loaded.0,
                        released,
                        crate::handler_sched::spec_fire_advance(
                            released, flight, context, at,
                        ),
                    );
                    lemma_store_certificate_extension_transitive(
                        state,
                        loaded.0,
                        crate::handler_sched::spec_fire_advance(
                            released, flight, context, at,
                        ),
                    );
                },
                crate::handler_docs::ProgressSpec::Failed(error) => {
                    lemma_commit_advance_nonissued_preserves_detached_flight_control(
                        committed.0,
                        flight.id,
                        committed.1,
                        None,
                    );
                    let forgotten =
                        crate::state::spec_forget_origin(
                            crate::state::spec_note(
                                advanced.0,
                                crate::types::NoteSpec::FireEnd {
                                    flight: flight.id,
                                    committed: false,
                                },
                            ),
                            context.origin,
                        );
                    assert(detached_flight_control(
                        forgotten, flight.id,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(crate::state::spec_forget_origin);
                        reveal(detached_flight_control);
                        reveal(production_core_control_body);
                    };
                    lemma_release_preserves_detached_flight_control(
                        forgotten, secondary, flight.id,
                    );
                    crate::global_store_invariants::
                        lemma_release_only_adds_nonappend(
                            forgotten, secondary,
                        );
                    let released =
                        crate::handler_docs::spec_release(
                            forgotten, secondary,
                        );
                    crate::global_store_invariants::
                        lemma_commit_failed_only_adds_nonappend(
                            released, flight, error,
                        );
                    assert(store_certificates_extend(
                        advanced.0, forgotten,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(crate::state::spec_forget_origin);
                        reveal(store_certificates_extend);
                    };
                    lemma_store_certificate_extension_transitive(
                        loaded.0, advanced.0, forgotten,
                    );
                    lemma_store_certificate_extension_transitive(
                        loaded.0, forgotten, released,
                    );
                    lemma_store_certificate_extension_transitive(
                        loaded.0,
                        released,
                        crate::handler_docs::spec_commit_failed(
                            released, flight, error,
                        ),
                    );
                    lemma_store_certificate_extension_transitive(
                        state,
                        loaded.0,
                        crate::handler_docs::spec_commit_failed(
                            released, flight, error,
                        ),
                    );
                },
                crate::handler_docs::ProgressSpec::Exhausted => {
                    lemma_commit_advance_nonissued_preserves_detached_flight_control(
                        committed.0,
                        flight.id,
                        committed.1,
                        None,
                    );
                    let abandoned =
                        crate::handler_docs::spec_abandon_slot(
                            crate::state::spec_forget_origin(
                                advanced.0, context.origin,
                            ),
                            secondary,
                        );
                    assert(detached_flight_control(
                        abandoned, flight.id,
                    )) by {
                        reveal(crate::state::spec_forget_origin);
                        reveal(crate::handler_docs::spec_abandon_slot);
                        reveal(detached_flight_control);
                        reveal(production_core_control_body);
                    };
                    crate::global_store_invariants::
                        lemma_op_exhausted_only_adds_nonappend(
                            abandoned, flight,
                        );
                    assert(store_certificates_extend(
                        advanced.0, abandoned,
                    )) by {
                        reveal(crate::state::spec_forget_origin);
                        reveal(crate::handler_docs::spec_abandon_slot);
                        reveal(store_certificates_extend);
                    };
                    lemma_store_certificate_extension_transitive(
                        loaded.0, advanced.0, abandoned,
                    );
                    lemma_store_certificate_extension_transitive(
                        loaded.0,
                        abandoned,
                        crate::handler_docs::spec_op_exhausted(
                            abandoned, flight,
                        ),
                    );
                    lemma_store_certificate_extension_transitive(
                        state,
                        loaded.0,
                        crate::handler_docs::spec_op_exhausted(
                            abandoned, flight,
                        ),
                    );
                },
            }
        },
    }
}

#[verifier::spinoff_prover]
proof fn lemma_answered_loading_extends_store_certificates(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    phase: crate::handler_docs::PhaseSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
        phase is Loading,
    ensures
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_phase(
                state, fid, flight, phase, response,
            ),
        ),
        old_active_store_certificates_preserved(
            state,
            crate::handler_docs::spec_answered_phase(
                state, fid, flight, phase, response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_phase);
    reveal(crate::handler_docs::spec_answered_loading);
    match flight.target {
        crate::target::TargetSpec::Origin(origin) => {
            lemma_loaded_origin_preserves_detached_flight_control(
                state,
                fid,
                origin,
                phase->Loading_revalidating,
                response,
            );
            let loaded = crate::handler_docs::spec_loaded_origin(
                state,
                origin,
                phase->Loading_revalidating,
                response,
            );
            assert(store_certificates_extend(state, loaded.0)) by {
                reveal(crate::handler_docs::spec_loaded_origin);
                reveal(crate::state::spec_note);
                reveal(crate::state::spec_remember);
                reveal(crate::state::spec_forget_origin);
                reveal(store_certificates_extend);
            };
            match loaded.1 {
                Ok(working) => {
                    lemma_regular_run_extends_store_certificates(
                        loaded.0, flight, working, false,
                    );
                    lemma_store_certificate_extension_transitive(
                        state,
                        loaded.0,
                        crate::handler_docs::spec_run_origin(
                            loaded.0, flight, working,
                        ),
                    );
                },
                Err(error) => {
                    crate::global_store_invariants::
                        lemma_fail_only_adds_nonappend(
                            loaded.0, flight, error,
                        );
                    lemma_store_certificate_extension_transitive(
                        state,
                        loaded.0,
                        crate::handler_docs::spec_fail(
                            loaded.0, flight, error,
                        ),
                    );
                },
            }
        },
        crate::target::TargetSpec::Schedule(id) => {
            lemma_loaded_schedule_preserves_detached_flight_control(
                state, fid, id, response,
            );
            let loaded = crate::handler_sched::spec_loaded_schedule(
                state, id, response,
            );
            assert(store_certificates_extend(state, loaded.0)) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(crate::state::spec_note);
                reveal(store_certificates_extend);
            };
            match loaded.1 {
                Ok(working) => {
                    lemma_regular_run_extends_store_certificates(
                        loaded.0, flight, working, true,
                    );
                    lemma_store_certificate_extension_transitive(
                        state,
                        loaded.0,
                        crate::handler_sched::spec_run_schedule(
                            loaded.0, flight, working,
                        ),
                    );
                },
                Err(error) => {
                    crate::global_store_invariants::
                        lemma_fail_only_adds_nonappend(
                            loaded.0, flight, error,
                        );
                    lemma_store_certificate_extension_transitive(
                        state,
                        loaded.0,
                        crate::handler_docs::spec_fail(
                            loaded.0, flight, error,
                        ),
                    );
                },
            }
        },
    }
    reveal(old_active_store_certificates_preserved);
    reveal(store_certificates_extend);
}

#[verifier::spinoff_prover]
proof fn lemma_regular_run_extends_store_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    schedule: bool,
)
    requires
        detached_flight_control(state, flight.id),
    ensures
        store_certificates_extend(
            state,
            if schedule {
                crate::handler_sched::spec_run_schedule(
                    state, flight, working,
                )
            } else {
                crate::handler_docs::spec_run_origin(
                    state, flight, working,
                )
            },
        ),
{
    reveal(crate::handler_docs::spec_run_origin);
    reveal(crate::handler_sched::spec_run_schedule);
    lemma_decide_preserves_detached_flight_control(
        state, flight.id, flight.work, working,
    );
    let decided = crate::handler_docs::spec_decide(
        state, flight.work, working,
    );
    assert(store_certificates_extend(state, decided.0)) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
        reveal(crate::state::spec_note);
        reveal(crate::state::spec_emit);
        reveal(store_certificates_extend);
    };
    lemma_commit_advance_preserves_old_active_certificates(
        decided.0,
        flight.id,
        decided.1,
        None,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        decided.0,
        flight.id,
        decided.1,
        None,
    );
    lemma_store_certificate_extension_transitive(
        state, decided.0, advanced.0,
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            reveal(crate::handler_docs::spec_inflight);
            reveal(store_certificates_extend);
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            lemma_commit_advance_nonissued_preserves_detached_flight_control(
                decided.0,
                flight.id,
                decided.1,
                None,
            );
            crate::global_store_invariants::
                lemma_committed_only_adds_nonappend(
                    advanced.0,
                    flight,
                    decided.2,
                    fired,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_committed(
                    advanced.0,
                    flight,
                    decided.2,
                    fired,
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            lemma_commit_advance_nonissued_preserves_detached_flight_control(
                decided.0,
                flight.id,
                decided.1,
                None,
            );
            crate::global_store_invariants::
                lemma_commit_failed_only_adds_nonappend(
                    advanced.0, flight, error,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_commit_failed(
                    advanced.0, flight, error,
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_commit_advance_nonissued_preserves_detached_flight_control(
                decided.0,
                flight.id,
                decided.1,
                None,
            );
            crate::global_store_invariants::
                lemma_op_exhausted_only_adds_nonappend(
                    advanced.0, flight,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_op_exhausted(
                    advanced.0, flight,
                ),
            );
        },
    }
}

proof fn lemma_answered_regular_extends_store_certificates(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    response: echod_concrete::store::StoreRes,
    schedule: bool,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
    ensures
        store_certificates_extend(
            state,
            if schedule {
                crate::handler_docs::spec_answered_schedule(
                    state, fid, flight, commit, done, response,
                )
            } else {
                crate::handler_docs::spec_answered_origin(
                    state, fid, flight, commit, done, response,
                )
            },
        ),
{
    lemma_commit_advance_preserves_old_active_certificates(
        state, fid, commit, Some(response),
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state, fid, commit, Some(response),
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state, fid, commit, Some(response),
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            let next = crate::handler_docs::spec_inflight(
                advanced.0,
                crate::handler_docs::FlightSpec {
                    phase: if schedule {
                        crate::handler_docs::PhaseSpec::Schedule {
                            commit: advanced.1,
                            done,
                        }
                    } else {
                        crate::handler_docs::PhaseSpec::Origin {
                            commit: advanced.1,
                            done,
                        }
                    },
                    ..flight
                },
            );
            assert(store_certificates_extend(
                advanced.0, next,
            )) by {
                reveal(crate::handler_docs::spec_inflight);
                reveal(store_certificates_extend);
            };
            lemma_store_certificate_extension_transitive(
                state, advanced.0, next,
            );
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            crate::global_store_invariants::
                lemma_committed_only_adds_nonappend(
                    advanced.0, flight, done, fired,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_committed(
                    advanced.0, flight, done, fired,
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_invariants::
                lemma_commit_failed_only_adds_nonappend(
                    advanced.0, flight, error,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_commit_failed(
                    advanced.0, flight, error,
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            crate::global_store_invariants::
                lemma_op_exhausted_only_adds_nonappend(
                    advanced.0, flight,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_op_exhausted(
                    advanced.0, flight,
                ),
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_origin);
    reveal(crate::handler_docs::spec_answered_schedule);
}

proof fn lemma_answered_origin_extends_store_certificates(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
    ensures
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_origin(
                state, fid, flight, commit, done, response,
            ),
        ),
{
    lemma_answered_regular_extends_store_certificates(
        state, fid, flight, commit, done, response, false,
    );
}

proof fn lemma_answered_schedule_extends_store_certificates(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
    ensures
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_schedule(
                state, fid, flight, commit, done, response,
            ),
        ),
{
    lemma_answered_regular_extends_store_certificates(
        state, fid, flight, commit, done, response, true,
    );
}

proof fn lemma_answered_fire_idle_extends_store_certificates(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
    ensures
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_fire_idle(
                state, fid, flight, commit, response,
            ),
        ),
{
    lemma_commit_advance_preserves_old_active_certificates(
        state, fid, commit, Some(response),
    );
    reveal(crate::handler_docs::spec_answered_fire_idle);
    let advanced = crate::handler_docs::spec_commit_advance(
        state, fid, commit, Some(response),
    );
    if advanced.2 !is Issued {
        lemma_commit_advance_nonissued_preserves_detached_flight_control(
            state, fid, commit, Some(response),
        );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            let next = crate::handler_docs::spec_inflight(
                advanced.0,
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::FireIdle {
                        commit: advanced.1,
                    },
                    ..flight
                },
            );
            assert(store_certificates_extend(
                advanced.0, next,
            )) by {
                reveal(crate::handler_docs::spec_inflight);
                reveal(store_certificates_extend);
            };
            lemma_store_certificate_extension_transitive(
                state, advanced.0, next,
            );
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::SweepEnd {
                        flight: fid,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            assert(production_core_control_body(ended)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            assert(store_certificates_extend(
                advanced.0, ended,
            )) by {
                reveal(crate::state::spec_note);
                reveal(store_certificates_extend);
            };
            crate::global_store_invariants::
                lemma_finish_only_adds_nonappend(
                    ended, flight, Ok(fired),
                );
            lemma_store_certificate_extension_transitive(
                advanced.0,
                ended,
                crate::handler_docs::spec_finish(
                    ended, flight, Ok(fired),
                ),
            );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_finish(
                    ended, flight, Ok(fired),
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::SweepEnd {
                    flight: fid,
                    committed: false,
                },
            );
            assert(production_core_control_body(ended)) by {
                reveal(crate::state::spec_note);
                reveal(detached_flight_control);
                reveal(production_core_control_body);
            };
            assert(store_certificates_extend(
                advanced.0, ended,
            )) by {
                reveal(crate::state::spec_note);
                reveal(store_certificates_extend);
            };
            crate::global_store_invariants::
                lemma_commit_failed_only_adds_nonappend(
                    ended, flight, error,
                );
            lemma_store_certificate_extension_transitive(
                advanced.0,
                ended,
                crate::handler_docs::spec_commit_failed(
                    ended, flight, error,
                ),
            );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_commit_failed(
                    ended, flight, error,
                ),
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            crate::global_store_invariants::
                lemma_op_exhausted_only_adds_nonappend(
                    advanced.0, flight,
                );
            lemma_store_certificate_extension_transitive(
                state,
                advanced.0,
                crate::handler_docs::spec_op_exhausted(
                    advanced.0, flight,
                ),
            );
        },
    }
}

#[verifier::spinoff_prover]
proof fn lemma_answered_commit_phase_extends_store_certificates(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    phase: crate::handler_docs::PhaseSpec,
    commit: crate::handler_docs::CommittingSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
        phase is Origin
            && phase->Origin_commit == commit
            || phase is Schedule
                && phase->Schedule_commit == commit
            || phase is FireIdle
                && phase->FireIdle_commit == commit,
    ensures
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_phase(
                state, fid, flight, phase, response,
            ),
        ),
        old_active_store_certificates_preserved(
            state,
            crate::handler_docs::spec_answered_phase(
                state, fid, flight, phase, response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_phase);
    match phase {
        crate::handler_docs::PhaseSpec::Origin {
            commit: phase_commit,
            done,
        } => {
            assert(phase_commit == commit);
            lemma_answered_origin_extends_store_certificates(
                state,
                fid,
                flight,
                commit,
                done,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::Schedule {
            commit: phase_commit,
            done,
        } => {
            assert(phase_commit == commit);
            lemma_answered_schedule_extends_store_certificates(
                state,
                fid,
                flight,
                commit,
                done,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::FireIdle {
            commit: phase_commit,
        } => {
            assert(phase_commit == commit);
            lemma_answered_fire_idle_extends_store_certificates(
                state, fid, flight, commit, response,
            );
        },
        _ => {
            assert(false);
        },
    }
    reveal(old_active_store_certificates_preserved);
    reveal(store_certificates_extend);
}

#[verifier::spinoff_prover]
proof fn lemma_answered_phase_preserves_old_active_certificates(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    phase: crate::handler_docs::PhaseSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
    ensures
        old_active_store_certificates_preserved(
            state,
            crate::handler_docs::spec_answered_phase(
                state, fid, flight, phase, response,
            ),
        ),
        store_certificates_extend(
            state,
            crate::handler_docs::spec_answered_phase(
                state, fid, flight, phase, response,
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_phase);
    match phase {
        crate::handler_docs::PhaseSpec::Loading {
            ..
        } => {
            lemma_answered_loading_extends_store_certificates(
                state, fid, flight, phase, response,
            );
        },
        crate::handler_docs::PhaseSpec::Origin { commit, .. }
        | crate::handler_docs::PhaseSpec::Schedule { commit, .. }
        | crate::handler_docs::PhaseSpec::FireIdle { commit } => {
            lemma_answered_commit_phase_extends_store_certificates(
                state, fid, flight, phase, commit, response,
            );
        },
        crate::handler_docs::PhaseSpec::FireLoadingSchedule { .. } => {
            lemma_answered_fire_loading_schedule_preserves_old_active_certificates(
                state, flight, response,
            );
        },
        crate::handler_docs::PhaseSpec::FireLoadingOrigin {
            revalidating,
            ctx,
            ..
        } => {
            lemma_answered_fire_loading_origin_extends_store_certificates(
                state,
                flight,
                revalidating,
                ctx,
                response,
            );
            reveal(old_active_store_certificates_preserved);
            assert(old_active_store_certificates_preserved(
                state,
                crate::handler_docs::spec_answered_phase(
                    state, fid, flight, phase, response,
                ),
            ));
        },
        crate::handler_docs::PhaseSpec::FireOrigin {
            commit,
            ctx,
            t,
            outbox,
        } => {
            lemma_answered_fire_origin_preserves_old_active_certificates(
                state, fid, flight, commit, ctx, t, outbox, response,
            );
        },
        crate::handler_docs::PhaseSpec::FireSchedule { commit } => {
            lemma_answered_fire_schedule_extends_store_certificates(
                state, fid, flight, commit, response,
            );
            reveal(store_certificates_extend);
            reveal(old_active_store_certificates_preserved);
            assert(old_active_store_certificates_preserved(
                state,
                crate::handler_docs::spec_answered_phase(
                    state, fid, flight, phase, response,
                ),
            ));
        },
        _ => {
            crate::global_store_invariants::
                lemma_fail_only_adds_nonappend(
                    state,
                    flight,
                    "an answer the flight did not wait for"@,
                );
            reveal(store_certificates_extend);
            reveal(old_active_store_certificates_preserved);
            assert(old_active_store_certificates_preserved(
                state,
                crate::handler_docs::spec_answered_phase(
                    state, fid, flight, phase, response,
                ),
            ));
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_answered_phase_preserves_core_control_body(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    phase: crate::handler_docs::PhaseSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        detached_flight_control(state, fid),
        flight.id == fid,
        answered_phase_issuance_control_ready(
            state,
            fid,
            flight,
            phase,
            response,
        ),
    ensures
        production_core_control_body(
            crate::handler_docs::spec_answered_phase(
                state,
                fid,
                flight,
                phase,
                response,
            ),
        ),
        old_active_store_certificates_preserved(
            state,
            crate::handler_docs::spec_answered_phase(
                state,
                fid,
                flight,
                phase,
                response,
            ),
        ),
{
    reveal(answered_phase_issuance_control_ready);
    lemma_answered_phase_preserves_old_active_certificates(
        state, fid, flight, phase, response,
    );
    reveal(crate::handler_docs::spec_answered_phase);
    match phase {
        crate::handler_docs::PhaseSpec::Loading {
            revalidating,
            ..
        } => {
            lemma_answered_loading_preserves_core_control_body(
                state,
                flight,
                revalidating,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::Origin { commit, done } => {
            lemma_answered_origin_preserves_core_control_body(
                state,
                fid,
                flight,
                commit,
                done,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::Schedule { commit, done } => {
            lemma_answered_schedule_preserves_core_control_body(
                state,
                fid,
                flight,
                commit,
                done,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::FireLoadingSchedule { .. } => {
            lemma_answered_fire_loading_schedule_preserves_core_control_body(
                state,
                flight,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::FireLoadingOrigin {
            revalidating,
            ctx,
            ..
        } => {
            lemma_answered_fire_loading_origin_preserves_core_control_body(
                state,
                flight,
                revalidating,
                ctx,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::FireIdle { commit } => {
            lemma_answered_fire_idle_preserves_core_control_body(
                state,
                fid,
                flight,
                commit,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::FireOrigin {
            commit,
            ctx,
            t,
            outbox,
        } => {
            lemma_answered_fire_origin_preserves_core_control_body(
                state,
                fid,
                flight,
                commit,
                ctx,
                t,
                outbox,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::FireSchedule { commit } => {
            lemma_answered_fire_schedule_preserves_core_control_body(
                state,
                fid,
                flight,
                commit,
                response,
            );
        },
        _ => {
            lemma_fail_preserves_core_control_body(
                state,
                flight,
                "an answer the flight did not wait for"@,
            );
        },
    }
}

/// A matching Flight response consumes its operation before running the
/// phase machine. The consumed id was the flight's unique expected id, so
/// the detached machine may either finish or atomically issue and install
/// one replacement operation.
#[verifier::spinoff_prover]
pub proof fn lemma_matching_flight_completion_preserves_old_active_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates:
                    state.store_certificates.remove(op),
                ..state
            };
            old_active_store_certificates_preserved(
                consumed,
                crate::handler_docs::spec_flight_completed(
                    consumed, fid, op, response,
                ),
            )
            && store_certificates_extend(
                consumed,
                crate::handler_docs::spec_flight_completed(
                    consumed, fid, op, response,
                ),
            )
        }),
{
    lemma_consume_and_detach_flight_preserves_core_control(
        state, op, fid,
    );
    let flight = state.flights.inflight[fid];
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates:
            state.store_certificates.remove(op),
        ..state
    };
    let detached = crate::handler_docs::spec_take_flight(consumed, fid);
    reveal(crate::handler_docs::spec_flight_completed);
    assert(consumed.flights.inflight.contains_key(fid));
    assert(consumed.flights.inflight[fid] == flight);
    assert(flight.phase.expects() == Some(op)) by {
        reveal(production_core_control_body);
        reveal(active_flight_owners_match_phase);
    };
    assert(flight.id == fid) by {
        reveal(production_core_control_body);
        reveal(active_flight_ids_match_keys);
    };
    lemma_answered_phase_preserves_old_active_certificates(
        detached,
        fid,
        crate::handler_docs::FlightSpec {
            phase: crate::handler_docs::PhaseSpec::Idle,
            ..flight
        },
        flight.phase,
        response,
    );
    reveal(old_active_store_certificates_preserved);
    reveal(store_certificates_extend);
    reveal(crate::handler_docs::spec_take_flight);
    assert forall|current: u64|
        consumed.store_certificates.contains_key(current)
            && crate::handler_docs::spec_flight_completed(
                consumed, fid, op, response,
            ).ops.contains_key(current)
    implies
        crate::handler_docs::spec_flight_completed(
            consumed, fid, op, response,
        ).store_certificates.contains_key(current)
            && crate::handler_docs::spec_flight_completed(
                consumed, fid, op, response,
            ).store_certificates[current]
                == consumed.store_certificates[current] by
    {
        assert(detached.store_certificates.contains_key(current));
        assert(detached.store_certificates[current]
            == consumed.store_certificates[current]);
    };
}

pub proof fn lemma_matching_flight_completion_preserves_core_control_body(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        matching_flight_completion_control_ready(
            state,
            op,
            fid,
            response,
        ),
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates:
                    state.store_certificates.remove(op),
                ..state
            };
            production_core_control_body(
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
            && old_active_store_certificates_preserved(
                consumed,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
            && store_certificates_extend(
                consumed,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    reveal(matching_flight_completion_control_ready);
    lemma_consume_and_detach_flight_preserves_core_control(
        state,
        op,
        fid,
    );
    let flight = state.flights.inflight[fid];
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates:
            state.store_certificates.remove(op),
        ..state
    };
    let detached = crate::handler_docs::spec_take_flight(consumed, fid);
    reveal(crate::handler_docs::spec_flight_completed);
    assert(consumed.flights.inflight.contains_key(fid));
    assert(consumed.flights.inflight[fid] == flight);
    assert(flight.phase.expects() == Some(op)) by {
        reveal(production_core_control_body);
        reveal(active_flight_owners_match_phase);
    };
    assert(flight.id == fid) by {
        reveal(production_core_control_body);
        reveal(active_flight_ids_match_keys);
    };
    lemma_answered_phase_preserves_core_control_body(
        detached,
        fid,
        crate::handler_docs::FlightSpec {
            phase: crate::handler_docs::PhaseSpec::Idle,
            ..flight
        },
        flight.phase,
        response,
    );
    lemma_matching_flight_completion_preserves_old_active_certificates(
        state, op, fid, response,
    );
}

} // verus!
