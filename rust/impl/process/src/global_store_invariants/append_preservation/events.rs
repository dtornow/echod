//! Events append-certification preservation lemmas.

#![cfg(verus_keep_ghost)]

use vstd::prelude::*;

use super::super::*;

verus! {

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_exact_emitted_store_effects_are_safe(
    store: StoreV,
    effects: Seq<crate::types::EffectSpec>,
    next: S,
)
    requires
        production_core_control_body(next),
        emitted_append_effects_have_store_provenance(
            store,
            next.keys.prefix,
            effects,
            next,
        ),
        forall|i: int, op: u64, request: StoreReqSpec|
            0 <= i < effects.len()
                && effects[i] == (crate::types::EffectSpec::Store {
                    op,
                    request,
                }) ==> {
                    &&& next.ops.contains_key(op)
                    &&& next.store_requests.contains_key(op)
                    &&& next.store_requests[op] == request
                    &&& next.store_certificates.contains_key(op)
                },
    ensures
        forall|i: int, op: u64, request: StoreReqSpec|
            #![trigger store_effect_matches(
                effects,
                i,
                op,
                request,
            )]
            store_effect_matches(effects, i, op, request)
                ==> invariant1_store_request_safe(
                    store,
                    next.keys.prefix,
                    next.keys.bucket_ms,
                    request,
                    next.store_certificates[op],
                ),
{
    reveal(invariant1_certificate_matches_request);
    reveal(certificate_exact_request);
    reveal(invariant1_store_request_safe);
    reveal(production_core_control_body);
    reveal(pending_store_effects_are_exact);
    assert forall|i: int, op: u64, request: StoreReqSpec|
        0 <= i < effects.len()
            && effects[i] == crate::types::EffectSpec::Store {
                op,
                request,
            } implies invariant1_certificate_matches_request(
                next.keys.prefix,
                next.keys.bucket_ms,
                request,
                next.store_certificates[op],
            ) by {
        reveal(store_effect_matches);
        assert({
            &&& next.ops.contains_key(op)
            &&& next.store_requests.contains_key(op)
            &&& next.store_requests[op] == request
            &&& next.store_certificates.contains_key(op)
        }) by {
        };
        assert(invariant1_certificate_matches_request(
            next.keys.prefix,
            next.keys.bucket_ms,
            request,
            next.store_certificates[op],
        )) by {
            reveal(production_core_control_body);
            reveal(exact_store_certificate_maps);
            reveal(exact_request_certificates);
        };
        if next.store_certificates[op] is DocumentAppend {
            reveal(emitted_append_effects_have_store_provenance);
        }
    };
    reveal(store_effect_matches);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_wake_event_preserves_active_write_cache_exclusion(
    node: crate::rover::NodeV,
    now: u64,
    clock: u64,
    armed: crate::types::Armed,
)
    requires
        production_core_control_invariants(node.core),
        rover_realizable_event(
            node,
            now,
            crate::types::EventSpec::Wake { clock, armed },
        ),
        active_document_writes_exclude_certified_cache(node.core),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler::spec_on_event(
                node.core,
                crate::types::EventSpec::Wake { clock, armed },
            ).0,
        ),
{
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler::spec_on_known_event);
    let prepared = spec_event_prepared(node.core, clock);
    lemma_event_prepared_preserves_core_control_body(node.core, clock);
    lemma_event_prepared_preserves_active_write_cache_exclusion(
        node.core,
        clock,
    );
    let woke = S { last_wake: None, ..prepared };
    assert(production_core_control_body(woke)) by {
        reveal(production_core_control_body);
    };
    assert(active_document_writes_exclude_certified_cache(woke)) by {
        reveal(active_document_writes_exclude_certified_cache);
    };
    let handled = if woke.loops {
        let current = crate::state::spec_now(woke);
        match armed {
            crate::types::Armed::Heartbeat => {
                lemma_members_tick_preserves_core_control_body(
                    woke,
                    current,
                );
                lemma_members_tick_preserves_active_write_cache_exclusion(
                    woke,
                    current,
                );
                let members =
                    crate::handler_node::spec_members_tick(woke, current);
                lemma_timers_run_preserves_core_control_body(
                    members,
                    current,
                );
                lemma_timers_run_preserves_active_write_cache_exclusion(
                    members,
                    current,
                );
                crate::handler_timers::spec_timers_run(members, current)
            },
            crate::types::Armed::Wheel => {
                lemma_timers_run_preserves_core_control_body(
                    woke,
                    current,
                );
                lemma_timers_run_preserves_active_write_cache_exclusion(
                    woke,
                    current,
                );
                let timers =
                    crate::handler_timers::spec_timers_run(woke, current);
                lemma_members_tick_preserves_core_control_body(
                    timers,
                    current,
                );
                lemma_members_tick_preserves_active_write_cache_exclusion(
                    timers,
                    current,
                );
                crate::handler_node::spec_members_tick(timers, current)
            },
        }
    } else {
        woke
    };
    let scheduled = crate::handler::spec_schedule_wake(handled);
    assert(active_document_writes_exclude_certified_cache(scheduled)) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(active_document_writes_exclude_certified_cache);
    };
    reveal(crate::handler::spec_schedule_wake);
    reveal(crate::state::spec_emit);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_store_completion_tail_preserves_retained_provenance(
    completed: S,
)
    requires
        production_core_control_body(completed),
        retained_commit_provenance(completed),
        cache_identity_provenance(completed),
    ensures
        ({
            let scheduled = crate::handler::spec_schedule_wake(completed);
            let next = S { out: Seq::empty(), ..scheduled };
            &&& retained_commit_provenance(next)
            &&& cache_identity_provenance(next)
        }),
{
    lemma_schedule_wake_preserves_retained_provenance(completed);
    lemma_schedule_wake_preserves_core_control_body(completed);
    let scheduled = crate::handler::spec_schedule_wake(completed);
    lemma_clear_out_preserves_retained_provenance(scheduled);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_flight_store_completion_tail_preserves_retained_provenance(
    consumed: S,
    completed: S,
)
    requires
        production_core_control_body(consumed),
        production_core_control_body(completed),
        retained_commit_provenance(completed),
        cache_identity_provenance(completed),
        old_active_store_certificates_preserved(consumed, completed),
    ensures
        ({
            let scheduled = crate::handler::spec_schedule_wake(completed);
            let frozen =
                crate::handler::spec_freeze_active_store_certificates(
                    consumed,
                    scheduled,
                );
            let next = S { out: Seq::empty(), ..frozen };
            &&& retained_commit_provenance(next)
            &&& cache_identity_provenance(next)
        }),
{
    lemma_schedule_wake_preserves_retained_provenance(completed);
    lemma_schedule_wake_preserves_core_control_body(completed);
    let scheduled = crate::handler::spec_schedule_wake(completed);
    assert(old_active_store_certificates_preserved(
        consumed,
        scheduled,
    )) by {
        reveal(old_active_store_certificates_preserved);
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    lemma_freeze_preserves_core_control_body(consumed, scheduled);
    let frozen = crate::handler::spec_freeze_active_store_certificates(
        consumed,
        scheduled,
    );
    assert(retained_commit_provenance(frozen)) by {
        reveal(crate::handler::spec_freeze_active_store_certificates);
        reveal(retained_commit_provenance);
        reveal(phase_commit_provenance);
        reveal(commit_provenance);
        reveal(commit_attachable_provenance);
        reveal(commit_candidate_provenance);
        reveal(commit_static_provenance);
        reveal(commit_issued_operation_provenance);
    };
    assert(cache_identity_provenance(frozen)) by {
        reveal(crate::handler::spec_freeze_active_store_certificates);
        reveal(cache_identity_provenance);
    };
    lemma_clear_out_preserves_retained_provenance(frozen);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_flight_store_completion_tail_preserves_active_write_cache_exclusion(
    consumed: S,
    completed: S,
)
    requires
        production_core_control_body(consumed),
        production_core_control_body(completed),
        active_document_writes_exclude_certified_cache(consumed),
        active_document_writes_exclude_certified_cache(completed),
        old_active_store_certificates_preserved(consumed, completed),
    ensures
        active_document_writes_exclude_certified_cache(
            S {
                out: Seq::empty(),
                ..crate::handler::spec_freeze_active_store_certificates(
                    consumed,
                    crate::handler::spec_schedule_wake(completed),
                )
            },
        ),
{
    lemma_schedule_wake_preserves_core_control_body(completed);
    let scheduled = crate::handler::spec_schedule_wake(completed);
    assert(active_document_writes_exclude_certified_cache(
        scheduled,
    )) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
        reveal(active_document_writes_exclude_certified_cache);
    };
    assert(scheduled.ops == completed.ops) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    assert(scheduled.store_certificates
        == completed.store_certificates) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    assert(old_active_store_certificates_preserved(
        consumed,
        scheduled,
    )) by {
        reveal(old_active_store_certificates_preserved);
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    lemma_freeze_preserves_core_control_body(consumed, scheduled);
    let frozen = crate::handler::spec_freeze_active_store_certificates(
        consumed,
        scheduled,
    );
    assert(frozen == scheduled);
    assert(active_document_writes_exclude_certified_cache(
        S { out: Seq::empty(), ..frozen },
    )) by {
        reveal(active_document_writes_exclude_certified_cache);
    };
}

pub(crate) proof fn lemma_flight_store_event_shape(
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
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            let completed = crate::handler_docs::spec_flight_completed(
                consumed,
                fid,
                op,
                response,
            );
            let scheduled = crate::handler::spec_schedule_wake(completed);
            crate::handler::spec_on_event(
                state,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: state.clock,
                },
            ).0 == S {
                out: Seq::empty(),
                ..crate::handler::spec_freeze_active_store_certificates(
                    consumed,
                    scheduled,
                )
            }
        }),
{
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let flight = state.flights.inflight[fid];
    assert(state.flights.inflight.contains_key(fid)) by {
        reveal(production_core_control_body);
        reveal(active_flight_owners_match_phase);
    };
    assert(flight.phase.expects() == Some(op)) by {
        reveal(production_core_control_body);
        reveal(active_flight_owners_match_phase);
    };
    let detached = crate::handler_docs::spec_take_flight(
        consumed,
        fid,
    );
    let idle = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Idle,
        ..flight
    };
    lemma_answered_phase_extends_store_allocator(
        detached,
        fid,
        idle,
        flight.phase,
        response,
    );
    let completed = crate::handler_docs::spec_flight_completed(
        consumed,
        fid,
        op,
        response,
    );
    assert(completed
        == crate::handler_docs::spec_answered_phase(
            detached,
            fid,
            idle,
            flight.phase,
            response,
        )) by {
        reveal(crate::handler_docs::spec_flight_completed);
    };
    assert(store_allocator_extension(consumed, detached)) by {
        reveal(store_allocator_extension);
        reveal(crate::handler_docs::spec_take_flight);
    };
    lemma_store_allocator_extension_transitive(
        consumed,
        detached,
        completed,
    );
    lemma_flight_completed_preserves_keys(
        consumed,
        fid,
        op,
        response,
    );
    let scheduled = crate::handler::spec_schedule_wake(completed);
    assert(scheduled.keys == state.keys) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    assert(scheduled.next_op >= state.next_op) by {
        reveal(store_allocator_extension);
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler::spec_on_known_event);
    reveal(crate::handler::spec_dispatch_known_event);
    reveal(crate::handler::spec_freeze_active_store_certificates);
}

pub(crate) proof fn lemma_members_store_event_shape(
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        state.ops.contains_key(op),
        state.ops[op] == Owner::Members,
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            let completed = crate::handler_node::spec_members_completed(
                consumed,
                op,
                response,
            );
            crate::handler::spec_on_event(
                state,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: state.clock,
                },
            ).0 == S {
                out: Seq::empty(),
                ..crate::handler::spec_schedule_wake(completed)
            }
        }),
{
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    lemma_consume_active_store_operation_preserves_core_control_body(
        state,
        op,
    );
    let completed = crate::handler_node::spec_members_completed(
        consumed,
        op,
        response,
    );
    lemma_members_completed_extends_store_allocator(
        consumed,
        op,
        response,
    );
    lemma_members_completed_preserves_keys(
        consumed,
        op,
        response,
    );
    let scheduled = crate::handler::spec_schedule_wake(completed);
    assert(scheduled.keys == state.keys) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    assert(scheduled.next_op >= state.next_op) by {
        reveal(store_allocator_extension);
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler::spec_on_known_event);
    reveal(crate::handler::spec_dispatch_known_event);
}

pub(crate) proof fn lemma_timers_store_event_shape(
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        state.out.len() == 0,
        state.ops.contains_key(op),
        state.ops[op] == Owner::Timers,
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            let completed = crate::handler_timers::spec_timers_completed(
                consumed,
                op,
                response,
            );
            crate::handler::spec_on_event(
                state,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: state.clock,
                },
            ).0 == S {
                out: Seq::empty(),
                ..crate::handler::spec_schedule_wake(completed)
            }
        }),
{
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let completed = crate::handler_timers::spec_timers_completed(
        consumed,
        op,
        response,
    );
    lemma_timers_completed_extends_store_allocator(
        consumed,
        op,
        response,
    );
    lemma_timers_completed_preserves_keys(
        consumed,
        op,
        response,
    );
    let scheduled = crate::handler::spec_schedule_wake(completed);
    assert(scheduled.keys == state.keys) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    assert(scheduled.next_op >= state.next_op) by {
        reveal(store_allocator_extension);
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler::spec_on_known_event);
    reveal(crate::handler::spec_dispatch_known_event);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_flight_store_completion_preserves_active_write_cache_exclusion(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler::spec_on_event(
                state,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: state.clock,
                },
            ).0,
        ),
{
    lemma_matching_flight_completion_preserves_retained_provenance(
        state,
        op,
        fid,
        response,
    );
    lemma_matching_flight_completion_preserves_active_write_cache_exclusion(
        state,
        op,
        fid,
        response,
    );
    crate::global_store_control::
        lemma_matching_flight_completion_preserves_core_control_body(
            state,
            op,
            fid,
            response,
        );
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let completed = crate::handler_docs::spec_flight_completed(
        consumed,
        fid,
        op,
        response,
    );
    assert(active_document_writes_exclude_certified_cache(
        consumed,
    )) by {
        reveal(active_document_writes_exclude_certified_cache);
    };
    assert(old_active_store_certificates_preserved(
        consumed,
        completed,
    )) by {
        reveal(old_active_store_certificates_preserved);
    };
    lemma_flight_store_completion_tail_preserves_active_write_cache_exclusion(
        consumed,
        completed,
    );
    lemma_flight_store_event_shape(state, op, fid, response);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ignored_store_completion_preserves_active_write_cache_exclusion(
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        active_document_writes_exclude_certified_cache(state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Ignored,
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler::spec_on_event(
                state,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: state.clock,
                },
            ).0,
        ),
{
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    assert(active_document_writes_exclude_certified_cache(
        consumed,
    )) by {
        reveal(active_document_writes_exclude_certified_cache);
    };
    let scheduled = crate::handler::spec_schedule_wake(consumed);
    assert(active_document_writes_exclude_certified_cache(
        scheduled,
    )) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
        reveal(active_document_writes_exclude_certified_cache);
    };
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler::spec_on_known_event);
    reveal(crate::handler::spec_schedule_wake);
    reveal(crate::state::spec_emit);
    reveal(active_document_writes_exclude_certified_cache);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_members_store_completion_preserves_active_write_cache_exclusion(
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        state.out.len() == 0,
        state.ops.contains_key(op),
        state.ops[op] == Owner::Members,
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler::spec_on_event(
                state,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: state.clock,
                },
            ).0,
        ),
{
    lemma_consume_nonflight_operation_preserves_retained_provenance(
        state,
        op,
    );
    lemma_consume_active_store_operation_preserves_core_control_body(
        state,
        op,
    );
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    assert(active_document_writes_exclude_certified_cache(
        consumed,
    )) by {
        reveal(active_document_writes_exclude_certified_cache);
    };
    lemma_members_completed_preserves_core_control_body(
        consumed,
        op,
        response,
    );
    lemma_members_completed_preserves_retained_provenance(
        consumed,
        op,
        response,
    );
    let completed = crate::handler_node::spec_members_completed(
        consumed,
        op,
        response,
    );
    lemma_members_completed_preserves_active_write_cache_exclusion(
        consumed,
        op,
        response,
    );
    let scheduled = crate::handler::spec_schedule_wake(completed);
    assert(active_document_writes_exclude_certified_cache(
        scheduled,
    )) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
        reveal(active_document_writes_exclude_certified_cache);
    };
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler::spec_on_known_event);
    reveal(crate::handler::spec_schedule_wake);
    reveal(crate::state::spec_emit);
    reveal(active_document_writes_exclude_certified_cache);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_timers_store_completion_preserves_active_write_cache_exclusion(
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        state.out.len() == 0,
        state.ops.contains_key(op),
        state.ops[op] == Owner::Timers,
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler::spec_on_event(
                state,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: state.clock,
                },
            ).0,
        ),
{
    lemma_consume_nonflight_operation_preserves_retained_provenance(
        state,
        op,
    );
    lemma_consume_active_store_operation_preserves_core_control_body(
        state,
        op,
    );
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    assert(active_document_writes_exclude_certified_cache(
        consumed,
    )) by {
        reveal(active_document_writes_exclude_certified_cache);
    };
    lemma_timers_completed_preserves_core_control_body(
        consumed,
        op,
        response,
    );
    lemma_timers_completed_preserves_retained_provenance(
        consumed,
        op,
        response,
    );
    let completed = crate::handler_timers::spec_timers_completed(
        consumed,
        op,
        response,
    );
    lemma_timers_completed_preserves_active_write_cache_exclusion(
        consumed,
        op,
        response,
    );
    let scheduled = crate::handler::spec_schedule_wake(completed);
    assert(active_document_writes_exclude_certified_cache(
        scheduled,
    )) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
        reveal(active_document_writes_exclude_certified_cache);
    };
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler::spec_on_known_event);
    reveal(crate::handler::spec_schedule_wake);
    reveal(crate::state::spec_emit);
    reveal(active_document_writes_exclude_certified_cache);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_store_event_preserves_active_write_cache_exclusion(
    node: crate::rover::NodeV,
    now: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    clock: u64,
)
    requires
        production_core_control_invariants(node.core),
        rover_realizable_event(
            node,
            now,
            crate::types::EventSpec::Store {
                op,
                response,
                clock,
            },
        ),
        retained_commit_provenance(node.core),
        cache_identity_provenance(node.core),
        active_document_writes_exclude_certified_cache(node.core),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler::spec_on_event(
                node.core,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock,
                },
            ).0,
        ),
{
    if !node.core.ops.contains_key(op) {
        reveal(crate::handler::spec_on_event);
        reveal(active_document_writes_exclude_certified_cache);
    } else {
        let prepared = S { clock, ..node.core };
        assert(production_core_control_body(prepared)) by {
            reveal(production_core_control_invariants);
            reveal(production_core_control_body);
        };
        assert(prepared.out.len() == 0) by {
            reveal(production_core_control_invariants);
        };
        assert(retained_commit_provenance(prepared)) by {
            reveal(retained_commit_provenance);
        };
        assert(cache_identity_provenance(prepared)) by {
            reveal(cache_identity_provenance);
        };
        assert(active_document_writes_exclude_certified_cache(
            prepared,
        )) by {
            reveal(active_document_writes_exclude_certified_cache);
        };
        match node.core.ops[op] {
            Owner::Flight(fid) => {
                lemma_flight_store_completion_preserves_active_write_cache_exclusion(
                    prepared,
                    op,
                    fid,
                    response,
                );
            },
            Owner::Ignored => {
                lemma_ignored_store_completion_preserves_active_write_cache_exclusion(
                    prepared,
                    op,
                    response,
                );
            },
            Owner::Members => {
                lemma_members_store_completion_preserves_active_write_cache_exclusion(
                    prepared,
                    op,
                    response,
                );
            },
            Owner::Timers => {
                lemma_timers_store_completion_preserves_active_write_cache_exclusion(
                    prepared,
                    op,
                    response,
                );
            },
            Owner::Debug => {
                assert(false) by {
                    reveal(production_core_control_invariants);
                    reveal(production_core_control_body);
                };
            },
        }
        reveal(crate::handler::spec_on_event);
        reveal(crate::handler::spec_on_known_event);
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_global_inductive_store_invariants_ignore_world_time(
    world: World<ProductionModel>,
    now: u64,
)
    requires
        global_inductive_store_invariants(world),
    ensures
        global_inductive_store_invariants(
            World::<ProductionModel> { now, ..world },
        ),
{
    reveal(global_inductive_store_invariants);
    reveal(global_persisted_document_invariant);
    reveal(global_store_invariants);
    reveal(pending_store_requests_invariant1_safe);
    reveal(actionable_store_responses_ready);
    reveal(production_node_control_invariants);
    reveal(retained_append_certificates);
}

}
