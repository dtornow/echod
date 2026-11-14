//! Control append-certification preservation lemmas.

#![cfg(verus_keep_ghost)]

use vstd::prelude::*;

use super::super::*;

verus! {

pub(crate) proof fn lemma_nonflight_store_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    request: StoreReqSpec,
    owner: Owner,
)
    requires
        core_retained_append_certificates(store, state),
        !(owner is Flight),
    ensures
        core_retained_append_certificates(
            store,
            crate::state::spec_store(state, request, owner).0,
        ),
{
    let next = crate::state::spec_store(state, request, owner).0;
    assert(next.keys.prefix == state.keys.prefix) by {
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(crate::state::spec_emit);
    };
    assert(next.cache.entries == state.cache.entries) by {
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(crate::state::spec_emit);
    };
    assert(next.flights.inflight == state.flights.inflight) by {
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(crate::state::spec_emit);
    };
    lemma_core_retained_append_certificates_frame(store, state, next);
}

pub(crate) proof fn lemma_read_nodes_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    keys: Seq<Seq<char>>,
    pending: Map<u64, bool>,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_read_nodes(state, keys, pending).0,
        ),
    decreases keys.len(),
{
    reveal(crate::handler_node::spec_read_nodes);
    if keys.len() > 0 {
        if crate::keys::spec_node_of_key(state.keys.prefix, keys[0])
            != Some(state.node.members.me.id)
        {
            let request = StoreReqSpec::Get { key: keys[0] };
            lemma_nonflight_store_preserves_core_retained_append_certificates(
                store,
                state,
                request,
                Owner::Members,
            );
            lemma_nonflight_store_issue_preserves_core_control_body(
                state,
                request,
                Owner::Members,
            );
            let issued = crate::state::spec_store(
                state,
                request,
                Owner::Members,
            );
            match issued.1 {
                Some(op) => {
                    lemma_read_nodes_preserves_core_retained_append_certificates(
                        store,
                        issued.0,
                        keys.drop_first(),
                        pending.insert(op, true),
                    );
                },
                None => {
                    lemma_read_nodes_preserves_core_retained_append_certificates(
                        store,
                        issued.0,
                        keys.drop_first(),
                        pending,
                    );
                },
            }
        } else {
            lemma_read_nodes_preserves_core_retained_append_certificates(
                store,
                state,
                keys.drop_first(),
                pending,
            );
        }
    }
}

pub(crate) proof fn lemma_list_buckets_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    prefixes: Seq<Seq<char>>,
    horizon: u64,
    pending: Map<u64, u64>,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_timers::spec_list_buckets(
                state,
                prefixes,
                horizon,
                pending,
            ).0,
        ),
    decreases prefixes.len(),
{
    reveal(crate::handler_timers::spec_list_buckets);
    if prefixes.len() > 0 {
        match crate::keys::spec_parse_bucket_prefix(
            state.keys.prefix,
            prefixes[0],
        ) {
            Some(bucket) if bucket <= horizon => {
                let request = StoreReqSpec::List {
                    prefix: crate::keys::spec_bucket_prefix(
                        state.keys.prefix,
                        bucket,
                    ),
                    max_keys: usize::MAX,
                };
                lemma_nonflight_store_preserves_core_retained_append_certificates(
                    store,
                    state,
                    request,
                    Owner::Timers,
                );
                lemma_nonflight_store_issue_preserves_core_control_body(
                    state,
                    request,
                    Owner::Timers,
                );
                let issued = crate::state::spec_store(
                    state,
                    request,
                    Owner::Timers,
                );
                match issued.1 {
                    Some(op) => {
                        lemma_list_buckets_preserves_core_retained_append_certificates(
                            store,
                            issued.0,
                            prefixes.drop_first(),
                            horizon,
                            pending.insert(op, bucket),
                        );
                    },
                    None => {
                        lemma_list_buckets_preserves_core_retained_append_certificates(
                            store,
                            issued.0,
                            prefixes.drop_first(),
                            horizon,
                            pending,
                        );
                    },
                }
            },
            _ => {
                lemma_list_buckets_preserves_core_retained_append_certificates(
                    store,
                    state,
                    prefixes.drop_first(),
                    horizon,
                    pending,
                );
            },
        }
    }
}

pub(crate) proof fn lemma_take_bucket_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_timers::spec_take_bucket(state, keys, count).0,
        ),
    decreases keys.len(),
{
    reveal(crate::handler_timers::spec_take_bucket);
    if keys.len() > 0 {
        match crate::keys::spec_parse_timer_key(keys[0]) {
            Some(entry)
                if crate::handler_timers::spec_owns_entry(state, entry) => {
                    let next = crate::handler_timers::spec_with_timers(
                        state,
                        crate::state_timers::TimersSpec {
                            wheel: crate::state_timers::TimerWheelSpec {
                                armed: crate::state_timers::spec_arm(
                                    state.timers.wheel.armed,
                                    entry.deadline(),
                                    keys[0],
                                ),
                            },
                            ..state.timers
                        },
                    );
                    lemma_core_retained_append_certificates_frame(
                        store,
                        state,
                        next,
                    );
                    lemma_timers_field_update_preserves_core_control_body(
                        state,
                        next.timers,
                    );
                    lemma_take_bucket_preserves_core_retained_append_certificates(
                        store,
                        next,
                        keys.drop_first(),
                        count + 1,
                    );
                },
            _ => {
                lemma_take_bucket_preserves_core_retained_append_certificates(
                    store,
                    state,
                    keys.drop_first(),
                    count,
                );
            },
        }
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_store_delivery_preserves_new_actionable_response(
    before: World<ProductionModel>,
    after: World<ProductionModel>,
    request_index: int,
    delivered_op: u64,
    delivered_request: StoreReq,
)
    requires
        global_inductive_store_invariants(before),
        production_store_delivery_witness(
            before,
            after,
            request_index,
            delivered_op,
            delivered_request,
        ),
        crate::production_world_refinement::production_node(after)
            == crate::production_world_refinement::production_node(before),
        crate::production_world_refinement::production_node(before)
            .core.ops.contains_key(delivered_op),
    ensures
        ({
            let node =
                crate::production_world_refinement::production_node(after);
            let response = echod_concrete::store::spec_apply(
                production_store(before),
                delivered_request,
            ).1;
            &&& node.store_certificates.contains_key(delivered_op)
            &&& response_certificate_ready(
                production_store(after),
                node.core.keys.prefix,
                response,
                node.store_certificates[delivered_op],
            )
        }),
{
    reveal(production_store_delivery_witness);
    let node =
        crate::production_world_refinement::production_node(before);
    let certificate = node.store_certificates[delivered_op];
    let applied = echod_concrete::store::spec_apply(
        production_store(before),
        delivered_request,
    );
    assert(invariant1_store_request_safe(
        production_store(before),
        node.core.keys.prefix,
        node.core.keys.bucket_ms,
        delivered_request.deep_view(),
        certificate,
    ));
    lemma_store_apply_response_ready(
        production_store(before),
        node.core.keys.prefix,
        node.core.keys.bucket_ms,
        delivered_request,
        certificate,
    );
    assert(production_store(after).entries == applied.0.entries);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_store_delivery_preserves_old_actionable_response(
    before: World<ProductionModel>,
    after: World<ProductionModel>,
    request_index: int,
    delivered_op: u64,
    delivered_request: StoreReq,
    i: int,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        global_inductive_store_invariants(before),
        production_store_delivery_witness(
            before,
            after,
            request_index,
            delivered_op,
            delivered_request,
        ),
        crate::production_world_refinement::production_node(after)
            == crate::production_world_refinement::production_node(before),
        0 <= i < before.network.len(),
        store_response_envelope_matches(
            after.network[i],
            op,
            response,
        ),
        crate::production_world_refinement::production_node(before)
            .core.ops.contains_key(op),
    ensures
        ({
            let node =
                crate::production_world_refinement::production_node(after);
            &&& node.store_certificates.contains_key(op)
            &&& response_certificate_ready(
                production_store(after),
                node.core.keys.prefix,
                response,
                node.store_certificates[op],
            )
        }),
{
    reveal(production_store_delivery_witness);
    let node =
        crate::production_world_refinement::production_node(before);
    let certificate = node.store_certificates[delivered_op];
    let applied = echod_concrete::store::spec_apply(
        production_store(before),
        delivered_request,
    );
    assert(after.network[i] == before.network[i]);
    assert(op != delivered_op) by {
        if op == delivered_op {
            assert(production_store(before).seen.contains((
                Pid::Node(0),
                delivered_op,
            )));
            assert(false);
        }
    };
    assert(response_certificate_ready(
        production_store(before),
        node.core.keys.prefix,
        response,
        node.store_certificates[op],
    ));
    assert(store_certificates_compatible(
        certificate,
        node.store_certificates[op],
    ));
    assert(invariant1_store_request_safe(
        production_store(before),
        node.core.keys.prefix,
        node.core.keys.bucket_ms,
        delivered_request.deep_view(),
        certificate,
    ));
    lemma_compatible_store_apply_preserves_response_ready(
        production_store(before),
        node.core.keys.prefix,
        node.core.keys.bucket_ms,
        delivered_request,
        certificate,
        response,
        node.store_certificates[op],
    );
    assert(production_store(after).entries == applied.0.entries);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_store_delivery_preserves_one_actionable_response(
    before: World<ProductionModel>,
    after: World<ProductionModel>,
    request_index: int,
    delivered_op: u64,
    delivered_request: StoreReq,
    i: int,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        global_inductive_store_invariants(before),
        production_store_delivery_witness(
            before,
            after,
            request_index,
            delivered_op,
            delivered_request,
        ),
        crate::production_world_refinement::production_node(after)
            == crate::production_world_refinement::production_node(before),
        0 <= i < after.network.len(),
        store_response_envelope_matches(
            after.network[i],
            op,
            response,
        ),
        crate::production_world_refinement::production_node(before)
            .core.ops.contains_key(op),
    ensures
        ({
            let node =
                crate::production_world_refinement::production_node(after);
            &&& node.store_certificates.contains_key(op)
            &&& response_certificate_ready(
                production_store(after),
                node.core.keys.prefix,
                response,
                node.store_certificates[op],
            )
        }),
{
    reveal(production_store_delivery_witness);
    if i == before.network.len() {
        assert(op == delivered_op);
        assert(response == echod_concrete::store::spec_apply(
            production_store(before),
            delivered_request,
        ).1);
        lemma_store_delivery_preserves_new_actionable_response(
            before,
            after,
            request_index,
            delivered_op,
            delivered_request,
        );
    } else {
        assert(i < before.network.len());
        lemma_store_delivery_preserves_old_actionable_response(
            before,
            after,
            request_index,
            delivered_op,
            delivered_request,
            i,
            op,
            response,
        );
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_begin_origin_cached_preserves_retained_commit(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    origin: Seq<char>,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        flight_submission_provenance(flight),
        flight.work !is Fire,
        flight.target == crate::target::TargetSpec::Origin(origin),
        crate::cache::spec_get(state.cache, origin).1 is Some,
    ensures
        ({
            let next =
                crate::handler_docs::spec_begin(state, flight);
            retained_commit_provenance(next)
        }),
{
    lemma_cache_get_preserves_identity(state.cache, origin);
    lemma_cache_get_preserves_unique_origins(state.cache, origin);
    let cache_framed = S {
        cache: crate::cache::spec_get(state.cache, origin).0,
        ..state
    };
    assert(retained_commit_provenance(cache_framed)) by {
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(cache_framed)) by {
        reveal(cache_identity_provenance);
    };
    let cached = crate::cache::spec_get(state.cache, origin).1.unwrap();
    let key = crate::keys::spec_doc_key(state.keys.prefix, origin);
    let request = StoreReqSpec::GetIfNoneMatch {
        key,
        etag: cached.etag,
    };
    let certificate = StoreEffectCertificateV::WorkflowRead {
        key,
        origin,
        etag: Some(cached.etag),
        fid: flight.id,
    };
    let issued = crate::state::spec_store_certified(
        cache_framed,
        request,
        Owner::Flight(flight.id),
        certificate,
    );
    assert forall|op: u64, owner: u64|
        cache_framed.ops.contains_key(op)
            && cache_framed.ops[op] == Owner::Flight(owner) implies {
                &&& cache_framed.store_requests.contains_key(op)
                &&& cache_framed.store_certificates.contains_key(op)
                &&& issued.0.ops.contains_key(op)
                &&& issued.0.ops[op] == Owner::Flight(owner)
                &&& issued.0.store_requests.contains_key(op)
                &&& issued.0.store_requests[op]
                    == cache_framed.store_requests[op]
                &&& issued.0.store_certificates.contains_key(op)
                &&& issued.0.store_certificates[op]
                    == cache_framed.store_certificates[op]
            } by {
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(production_core_control_body);
        reveal(crate::production_relation::operation_allocator_consistent);
    };
    lemma_nonflight_frame_preserves_retained_provenance(
        cache_framed,
        issued.0,
    );
    match issued.1 {
        Some(op) => {
            let attached = crate::handler_docs::spec_inflight(
                issued.0,
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::Loading {
                        op,
                        revalidating: Some(cached),
                    },
                    ..flight
                },
            );
            assert(retained_commit_provenance(attached)) by {
                reveal(crate::handler_docs::spec_inflight);
                reveal(retained_commit_provenance);
                reveal(phase_commit_provenance);
            };
        },
        None => {
            assert(crate::global_store_control::detached_flight_control(
                issued.0,
                flight.id,
            )) by {
                reveal(crate::global_store_control::detached_flight_control);
                reveal(crate::state::spec_store_certified);
                reveal(crate::state::spec_store_raw);
            };
            assert(crate::global_store_lane::detached_flight_owns_primary(
                issued.0,
                flight,
            )) by {
                reveal(
                    crate::global_store_lane::detached_flight_owns_primary,
                );
                reveal(crate::state::spec_store_certified);
                reveal(crate::state::spec_store_raw);
            };
            lemma_op_exhausted_preserves_retained_provenance(
                issued.0,
                flight,
            );
        },
    }
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::state::spec_store_certified);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_begin_origin_uncached_preserves_retained_commit(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    origin: Seq<char>,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        flight_submission_provenance(flight),
        flight.work !is Fire,
        flight.target == crate::target::TargetSpec::Origin(origin),
        crate::cache::spec_get(state.cache, origin).1 is None,
    ensures
        retained_commit_provenance(
            crate::handler_docs::spec_begin(state, flight),
        ),
{
    crate::global_store_control::lemma_begin_preserves_core_control_body(
        state,
        flight,
    );
    crate::global_store_lane::lemma_begin_preserves_lane_ownership(
        state,
        flight,
    );
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(retained_commit_provenance);
    reveal(phase_commit_provenance);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_begin_schedule_preserves_retained_commit(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    schedule: Seq<char>,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        flight_submission_provenance(flight),
        flight.work !is Fire,
        flight.target == crate::target::TargetSpec::Schedule(schedule),
    ensures
        ({
            let next =
                crate::handler_docs::spec_begin(state, flight);
            retained_commit_provenance(next)
        }),
{
    crate::global_store_control::lemma_begin_preserves_core_control_body(
        state,
        flight,
    );
    crate::global_store_lane::lemma_begin_preserves_lane_ownership(
        state,
        flight,
    );
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(retained_commit_provenance);
    reveal(phase_commit_provenance);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_begin_schedule_preserves_cache_identity(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    schedule: Seq<char>,
)
    requires
        cache_identity_provenance(state),
        flight.work !is Fire,
        flight.target == crate::target::TargetSpec::Schedule(schedule),
    ensures
        cache_identity_provenance(
            crate::handler_docs::spec_begin(state, flight),
        ),
{
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(cache_identity_provenance);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_start_preserves_exact_store_certificate_maps(
    state: S,
    target: crate::target::TargetSpec,
    work: crate::handler_docs::WorkSpec,
    firing: Option<crate::handler_docs::FiringSpec>,
    debug: bool,
)
    requires
        production_core_control_body(state),
    ensures
        ({
            let next = crate::handler_docs::spec_start(
                state, target, work, firing, debug,
            );
            exact_store_certificate_maps(
                next.keys.prefix,
                next.keys.bucket_ms,
                next.store_requests,
                next.ops,
                next.store_certificates,
            )
        }),
{
    let next = crate::handler_docs::spec_start(
        state, target, work, firing, debug,
    );
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_flight);
    reveal(production_core_control_body);
    reveal(exact_store_certificate_maps);
    reveal(exact_request_certificates);
    reveal(store_effect_certificate);
    assert forall|op: u64|
        next.store_requests.contains_key(op) implies
            invariant1_certificate_matches_request(
                next.keys.prefix,
                next.keys.bucket_ms,
                next.store_requests[op],
                next.store_certificates[op],
            ) by {
        if state.store_requests.contains_key(op) {
            assert(state.store_certificates.contains_key(op));
        }
    };
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_start_preserves_pending_store_effects_exact(
    state: S,
    target: crate::target::TargetSpec,
    work: crate::handler_docs::WorkSpec,
    firing: Option<crate::handler_docs::FiringSpec>,
    debug: bool,
)
    requires
        production_core_control_body(state),
    ensures
        pending_store_effects_are_exact(
            crate::handler_docs::spec_start(
                state, target, work, firing, debug,
            ),
        ),
{
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_flight);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(production_core_control_body);
    reveal(pending_store_effects_are_exact);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_start_preserves_noncommit_and_debug_control(
    state: S,
    target: crate::target::TargetSpec,
    work: crate::handler_docs::WorkSpec,
    firing: Option<crate::handler_docs::FiringSpec>,
    debug: bool,
)
    requires
        production_core_control_body(state),
    ensures
        ({
            let next = crate::handler_docs::spec_start(
                state, target, work, firing, debug,
            );
            &&& noncommit_certificates_are_other(next)
            &&& forall|op: u64|
                next.ops.contains_key(op) ==>
                    next.ops[op] != Owner::Debug
            &&& next.debug.current is None
            &&& next.debug.queue.len() == 0
        }),
{
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_flight);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(production_core_control_body);
    reveal(noncommit_certificates_are_other);
    reveal(flight_read_certificate);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_start_preserves_exact_certificate_control(
    state: S,
    target: crate::target::TargetSpec,
    work: crate::handler_docs::WorkSpec,
    firing: Option<crate::handler_docs::FiringSpec>,
    debug: bool,
)
    requires
        production_core_control_body(state),
    ensures
        ({
            let next = crate::handler_docs::spec_start(
                state, target, work, firing, debug,
            );
            &&& exact_store_certificate_maps(
                next.keys.prefix,
                next.keys.bucket_ms,
                next.store_requests,
                next.ops,
                next.store_certificates,
            )
            &&& pending_store_effects_are_exact(next)
            &&& noncommit_certificates_are_other(next)
            &&& forall|op: u64|
                next.ops.contains_key(op) ==>
                    next.ops[op] != Owner::Debug
            &&& next.debug.current is None
            &&& next.debug.queue.len() == 0
        }),
{
    lemma_start_preserves_exact_store_certificate_maps(
        state, target, work, firing, debug,
    );
    lemma_start_preserves_pending_store_effects_exact(
        state, target, work, firing, debug,
    );
    lemma_start_preserves_noncommit_and_debug_control(
        state, target, work, firing, debug,
    );
}

pub(crate) proof fn lemma_timer_reload_issue_preserves_retained_provenance(
    state: S,
    now: u64,
)
    requires
        production_core_control_body(state),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
    ensures
        ({
            let next = crate::handler_timers::spec_reload(state, now);
            &&& retained_commit_provenance(next)
            &&& cache_identity_provenance(next)
        }),
{
    reveal(crate::handler_timers::spec_reload);
    let filtered = crate::handler_timers::spec_with_timers(
        state,
        crate::state_timers::TimersSpec {
            wheel: crate::state_timers::TimerWheelSpec {
                armed: state.timers.wheel.armed.filter(
                    |k: crate::state_timers::SlotSpec|
                        crate::handler_timers::spec_owns_key(state, k.1),
                ),
            },
            ..state.timers
        },
    );
    lemma_with_timers_preserves_retained_provenance(
        state,
        crate::state_timers::TimersSpec {
            wheel: crate::state_timers::TimerWheelSpec {
                armed: state.timers.wheel.armed.filter(
                    |k: crate::state_timers::SlotSpec|
                        crate::handler_timers::spec_owns_key(state, k.1),
                ),
            },
            ..state.timers
        },
    );
    assert(production_core_control_body(filtered)) by {
        reveal(production_core_control_body);
    };
    let request = StoreReqSpec::ListPrefixes {
        prefix: crate::keys::spec_timer_prefix(filtered.keys.prefix),
    };
    lemma_nonflight_store_issue_preserves_core_control_body(
        filtered,
        request,
        Owner::Timers,
    );
    lemma_nonflight_store_issue_preserves_retained_provenance(
        filtered,
        request,
        Owner::Timers,
    );
    let stored =
        crate::state::spec_store(filtered, request, Owner::Timers);
    if stored.1 is Some {
        lemma_with_timers_preserves_retained_provenance(
            stored.0,
            crate::state_timers::TimersSpec {
                listing: Some(
                    crate::state_timers::ListingSpec::Prefixes {
                        op: stored.1.unwrap(),
                        horizon: crate::handler_timers::spec_horizon(
                            filtered,
                            now,
                        ),
                    },
                ),
                ..stored.0.timers
            },
        );
    }
}

pub(crate) proof fn lemma_timer_extend_issue_preserves_retained_provenance(
    state: S,
    bucket: u64,
)
    requires
        production_core_control_body(state),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
    ensures
        ({
            let request = StoreReqSpec::List {
                prefix: crate::keys::spec_bucket_prefix(
                    state.keys.prefix,
                    bucket,
                ),
                max_keys: usize::MAX,
            };
            let stored =
                crate::state::spec_store(state, request, Owner::Timers);
            let next = match stored.1 {
                Some(op) => crate::handler_timers::spec_with_timers(
                    stored.0,
                    crate::state_timers::TimersSpec {
                        listing: Some(
                            crate::state_timers::ListingSpec::Extend {
                                op,
                                bucket,
                            },
                        ),
                        ..stored.0.timers
                    },
                ),
                None => stored.0,
            };
            &&& retained_commit_provenance(next)
            &&& cache_identity_provenance(next)
        }),
{
    let request = StoreReqSpec::List {
        prefix: crate::keys::spec_bucket_prefix(
            state.keys.prefix,
            bucket,
        ),
        max_keys: usize::MAX,
    };
    lemma_nonflight_store_issue_preserves_core_control_body(
        state,
        request,
        Owner::Timers,
    );
    lemma_nonflight_store_issue_preserves_retained_provenance(
        state,
        request,
        Owner::Timers,
    );
    let stored =
        crate::state::spec_store(state, request, Owner::Timers);
    if stored.1 is Some {
        lemma_with_timers_preserves_retained_provenance(
            stored.0,
            crate::state_timers::TimersSpec {
                listing: Some(
                    crate::state_timers::ListingSpec::Extend {
                        op: stored.1.unwrap(),
                        bucket,
                    },
                ),
                ..stored.0.timers
            },
        );
    }
}

pub(crate) proof fn lemma_timer_relist_issue_preserves_retained_provenance(
    state: S,
    bucket: u64,
)
    requires
        production_core_control_body(state),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
    ensures
        ({
            let request = StoreReqSpec::List {
                prefix: crate::keys::spec_bucket_prefix(
                    state.keys.prefix,
                    bucket,
                ),
                max_keys: usize::MAX,
            };
            let stored =
                crate::state::spec_store(state, request, Owner::Timers);
            let next = match stored.1 {
                Some(op) => crate::handler_timers::spec_with_timers(
                    stored.0,
                    crate::state_timers::TimersSpec {
                        listing: Some(
                            crate::state_timers::ListingSpec::Relist {
                                op,
                                bucket,
                            },
                        ),
                        ..stored.0.timers
                    },
                ),
                None => stored.0,
            };
            &&& retained_commit_provenance(next)
            &&& cache_identity_provenance(next)
        }),
{
    let request = StoreReqSpec::List {
        prefix: crate::keys::spec_bucket_prefix(
            state.keys.prefix,
            bucket,
        ),
        max_keys: usize::MAX,
    };
    lemma_nonflight_store_issue_preserves_core_control_body(
        state,
        request,
        Owner::Timers,
    );
    lemma_nonflight_store_issue_preserves_retained_provenance(
        state,
        request,
        Owner::Timers,
    );
    let stored =
        crate::state::spec_store(state, request, Owner::Timers);
    if stored.1 is Some {
        lemma_with_timers_preserves_retained_provenance(
            stored.0,
            crate::state_timers::TimersSpec {
                listing: Some(
                    crate::state_timers::ListingSpec::Relist {
                        op: stored.1.unwrap(),
                        bucket,
                    },
                ),
                ..stored.0.timers
            },
        );
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_origin_preserves_active_write_cache_exclusion(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            fid,
        ),
        flight.id == fid,
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        commit_candidate_provenance(
            state,
            fid,
            flight.target,
            commit,
        ),
        commit.issued is Some,
    ensures
        active_document_writes_exclude_certified_cache(
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
    reveal(crate::global_store_control::detached_flight_control);
    assert(production_core_control_body(state));
    reveal(
        crate::global_store_lane::detached_flight_owns_primary,
    );
    lemma_detached_commit_advance_preserves_active_write_cache_exclusion(
        state,
        fid,
        flight.target,
        commit,
        response,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            reveal(crate::handler_docs::spec_inflight);
            reveal(active_document_writes_exclude_certified_cache);
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
            reveal(
                crate::global_store_control::detached_flight_control,
            );
            lemma_committed_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
                done,
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
            reveal(
                crate::global_store_control::detached_flight_control,
            );
            lemma_commit_failed_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_origin);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_schedule_preserves_active_write_cache_exclusion(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            fid,
        ),
        flight.id == fid,
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        commit_candidate_provenance(
            state,
            fid,
            flight.target,
            commit,
        ),
        commit.issued is Some,
    ensures
        active_document_writes_exclude_certified_cache(
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
    reveal(crate::global_store_control::detached_flight_control);
    assert(production_core_control_body(state));
    reveal(
        crate::global_store_lane::detached_flight_owns_primary,
    );
    lemma_detached_commit_advance_preserves_active_write_cache_exclusion(
        state,
        fid,
        flight.target,
        commit,
        response,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            reveal(crate::handler_docs::spec_inflight);
            reveal(active_document_writes_exclude_certified_cache);
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
            reveal(
                crate::global_store_control::detached_flight_control,
            );
            lemma_committed_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
                done,
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
            reveal(
                crate::global_store_control::detached_flight_control,
            );
            lemma_commit_failed_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_schedule);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_run_origin_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        cache_identity_provenance(state),
        working_document_provenance(state.keys.prefix, working),
        working_matches_target(working, flight.target),
        flight_submission_provenance(flight),
        flight_submission_provenance(flight),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_run_origin(
                state,
                flight,
                working,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    assert(production_core_control_body(state));
    reveal(retained_commit_provenance);
    lemma_decide_establishes_commit_provenance(
        state,
        flight,
        working,
    );
    let decided = crate::handler_docs::spec_decide(
        state,
        flight.work,
        working,
    );
    assert(decided.0 == state) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
    };
    assert(decided.1.issued is None) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
    };
    lemma_initial_commit_advance_preserves_active_write_cache_exclusion(
        decided.0,
        flight.id,
        flight.target,
        decided.1,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        decided.0,
        flight.id,
        decided.1,
        None,
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            reveal(crate::handler_docs::spec_inflight);
            reveal(active_document_writes_exclude_certified_cache);
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    decided.0,
                    flight.id,
                    decided.1,
                    None,
                );
            reveal(crate::global_store_control::detached_flight_control);
            lemma_committed_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
                decided.2,
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    decided.0,
                    flight.id,
                    decided.1,
                    None,
                );
            reveal(crate::global_store_control::detached_flight_control);
            lemma_commit_failed_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
            );
        },
    }
    reveal(crate::handler_docs::spec_run_origin);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_run_schedule_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        cache_identity_provenance(state),
        working_document_provenance(state.keys.prefix, working),
        working_matches_target(working, flight.target),
        flight_submission_provenance(flight),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_sched::spec_run_schedule(
                state,
                flight,
                working,
            ),
        ),
{
    lemma_run_origin_preserves_active_write_cache_exclusion(
        state,
        flight,
        working,
    );
    let origin = crate::handler_docs::spec_run_origin(
        state,
        flight,
        working,
    );
    let schedule = crate::handler_sched::spec_run_schedule(
        state,
        flight,
        working,
    );
    assert(schedule.cache == origin.cache) by {
        reveal(crate::handler_docs::spec_run_origin);
        reveal(crate::handler_sched::spec_run_schedule);
        reveal(crate::handler_docs::spec_inflight);
    };
    assert(schedule.ops == origin.ops) by {
        reveal(crate::handler_docs::spec_run_origin);
        reveal(crate::handler_sched::spec_run_schedule);
        reveal(crate::handler_docs::spec_inflight);
    };
    assert(schedule.store_certificates
        == origin.store_certificates) by {
        reveal(crate::handler_docs::spec_run_origin);
        reveal(crate::handler_sched::spec_run_schedule);
        reveal(crate::handler_docs::spec_inflight);
    };
    reveal(active_document_writes_exclude_certified_cache);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_loading_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    revalidating: Option<crate::cache::CachedSpec>,
    response: echod_concrete::store::StoreRes,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_control_provenance(
            state.keys.prefix,
            crate::handler_docs::FlightSpec {
                phase: crate::handler_docs::PhaseSpec::Loading {
                    op: 0,
                    revalidating,
                },
                ..flight
            },
        ),
        flight_submission_provenance(flight),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_answered_loading(
                state,
                flight,
                revalidating,
                response,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    assert(production_core_control_body(state));
    reveal(
        crate::global_store_lane::detached_flight_owns_primary,
    );
    match flight.target {
        crate::target::TargetSpec::Origin(origin) => {
            assert(revalidating is Some ==>
                forall|op: u64|
                    state.ops.contains_key(op)
                        && state.store_certificates.contains_key(op)
                        && certificate_written_document(
                            state.store_certificates[op],
                        ) is Some
                        && revalidating.unwrap()
                            .loaded.append_certified ==>
                    document_lane(
                        revalidating.unwrap().loaded.document,
                    ) != document_lane(
                        certificate_written_document(
                            state.store_certificates[op],
                        ).unwrap(),
                    )) by {
                if revalidating is Some {
                    reveal(flight_control_provenance);
                    reveal(cached_origin_provenance);
                    assert forall|op: u64|
                        state.ops.contains_key(op)
                            && state.store_certificates.contains_key(op)
                            && certificate_written_document(
                                state.store_certificates[op],
                            ) is Some
                        implies document_lane(
                            revalidating.unwrap().loaded.document,
                        ) != document_lane(
                            certificate_written_document(
                                state.store_certificates[op],
                            ).unwrap(),
                        ) by {
                        lemma_active_document_write_differs_from_detached_owned_lane(
                            state,
                            op,
                            flight.id,
                            crate::target::spec_name(flight.target),
                        );
                        assert(document_lane(
                            revalidating.unwrap().loaded.document,
                        ) == crate::target::spec_name(flight.target)) by {
                            reveal(
                                crate::document::loaded_workflow_has_identity,
                            );
                            reveal(document_lane);
                            reveal(crate::target::spec_name);
                        };
                    };
                }
            };
            lemma_loaded_origin_success_has_provenance(
                state,
                origin,
                revalidating,
                response,
            );
            lemma_loaded_origin_preserves_active_write_cache_exclusion(
                state,
                origin,
                revalidating,
                response,
            );
            crate::global_store_control::
                lemma_loaded_origin_preserves_detached_flight_control(
                    state,
                    flight.id,
                    origin,
                    revalidating,
                    response,
                );
            lemma_loaded_origin_preserves_remembered_timer_lanes(
                state,
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
            assert(loaded.0.flights == state.flights) by {
                reveal(crate::handler_docs::spec_loaded_origin);
                reveal(crate::document::spec_validate_workflow_identity);
                reveal(crate::state::spec_note);
                reveal(crate::state::spec_remember);
                reveal(crate::state::spec_forget_origin);
            };
            assert(loaded.0.keys == state.keys) by {
                reveal(crate::handler_docs::spec_loaded_origin);
                reveal(crate::document::spec_validate_workflow_identity);
                reveal(crate::state::spec_note);
                reveal(crate::state::spec_remember);
                reveal(crate::state::spec_forget_origin);
            };
            assert(retained_commit_provenance(loaded.0)) by {
                reveal(crate::handler_docs::spec_loaded_origin);
                reveal(crate::document::spec_validate_workflow_identity);
                reveal(crate::state::spec_note);
                reveal(crate::state::spec_remember);
                reveal(crate::state::spec_forget_origin);
                reveal(retained_commit_provenance);
            };
            assert(crate::global_store_lane::detached_flight_owns_primary(
                loaded.0,
                flight,
            )) by {
                reveal(
                    crate::global_store_lane::detached_flight_owns_primary,
                );
            };
            match loaded.1 {
                Ok(working) => {
                    lemma_run_origin_preserves_active_write_cache_exclusion(
                        loaded.0,
                        flight,
                        working,
                    );
                },
                Err(error) => {
                    reveal(crate::global_store_control::detached_flight_control);
                    lemma_fail_preserves_active_write_cache_exclusion(
                        loaded.0,
                        flight,
                        error,
                    );
                },
            }
        },
        crate::target::TargetSpec::Schedule(schedule) => {
            lemma_loaded_schedule_success_has_provenance(
                state,
                schedule,
                response,
            );
            crate::global_store_control::
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
            assert(active_document_writes_exclude_certified_cache(
                loaded.0,
            )) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(active_document_writes_exclude_certified_cache);
            };
            assert(retained_commit_provenance(loaded.0)) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(retained_commit_provenance);
            };
            assert(cache_identity_provenance(loaded.0)) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(cache_identity_provenance);
            };
            assert(crate::global_store_control::detached_flight_control(
                loaded.0,
                flight.id,
            )) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(crate::global_store_control::detached_flight_control);
            };
            assert(crate::global_store_lane::detached_flight_owns_primary(
                loaded.0,
                flight,
            )) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(
                    crate::global_store_lane::detached_flight_owns_primary,
                );
            };
            match loaded.1 {
                Ok(working) => {
                    lemma_run_schedule_preserves_active_write_cache_exclusion(
                        loaded.0,
                        flight,
                        working,
                    );
                },
                Err(error) => {
                    reveal(crate::global_store_control::detached_flight_control);
                    lemma_fail_preserves_active_write_cache_exclusion(
                        loaded.0,
                        flight,
                        error,
                    );
                },
            }
        },
    }
    reveal(crate::handler_docs::spec_answered_loading);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_idle_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    at: u64,
    fired: Option<crate::verified::flight_spec::AFired>,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        flight.work is Fire,
        match flight.work {
            crate::handler_docs::WorkSpec::Fire {
                fired: submitted,
                ..
            } => fired == submitted,
            _ => true,
        },
        working_document_provenance(state.keys.prefix, working),
        working_matches_target(working, flight.target),
        spec_stored_committed_at(working.loaded.document) <= at,
        at <= echod_types::MAX_TIME,
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_sched::spec_fire_idle(
                state,
                flight,
                working,
                at,
                fired,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    reveal(retained_commit_provenance);
    reveal(
        crate::global_store_lane::detached_flight_owns_primary,
    );
    reveal(
        crate::global_store_lane::detached_flight_owns_primary,
    );
    let body = crate::document::spec_loaded_body(working.loaded);
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::SweepBegin {
            flight: flight.id,
            target: working.target,
            now: at,
        },
    );
    assert(production_core_control_body(noted)) by {
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
    };
    assert(retained_commit_provenance(noted)) by {
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(noted)) by {
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    assert(active_document_writes_exclude_certified_cache(noted)) by {
        reveal(crate::state::spec_note);
        reveal(active_document_writes_exclude_certified_cache);
    };
    crate::global_store_bounds::lemma_stored_body_ids_bounded(
        working.loaded.document,
    );
    crate::global_store_bounds::lemma_advance_stored_ids_bounded(
        working.loaded.document,
        body,
        at,
    );
    assert(working.loaded.document is Schedule) by {
        reveal(flight_submission_provenance);
        reveal(submission_provenance);
        reveal(working_matches_target);
        match flight.work {
            crate::handler_docs::WorkSpec::Fire { schedule, .. } => {
                assert(flight.target
                    == crate::target::TargetSpec::Schedule(schedule));
            },
            _ => assert(false),
        }
    };
    assert(well_formed(
        echod_concrete::node::spec_advance_stored(
            working.loaded.document,
            body,
            at,
        ),
    )) by {
        reveal(crate::document::spec_loaded_body);
        reveal(working_document_provenance);
        reveal(working_matches_target);
        reveal(echod_concrete::document::well_formed);
        reveal(echod_concrete::document::schedule_well_formed);
        reveal(echod_concrete::node::spec_advance_stored);
        reveal(echod_concrete::node::spec_body_deadline);
    };
    lemma_commit_new_establishes_provenance(
        noted,
        flight.id,
        flight.target,
        working,
        body,
        echod_concrete::node::spec_body_deadline(body),
        at,
        fired,
    );
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        body,
        echod_concrete::node::spec_body_deadline(body),
        at,
        fired,
    );
    assert(committed.0 == noted) by {
        reveal(crate::handler_docs::spec_commit_new);
    };
    assert(committed.1.issued is None) by {
        reveal(crate::handler_docs::spec_commit_new);
    };
    lemma_initial_commit_advance_preserves_active_write_cache_exclusion(
        committed.0,
        flight.id,
        flight.target,
        committed.1,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            reveal(crate::handler_docs::spec_inflight);
            reveal(active_document_writes_exclude_certified_cache);
        },
        crate::handler_docs::ProgressSpec::Done(result) => {
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    advanced.0,
                    crate::types::NoteSpec::SweepEnd {
                        flight: flight.id,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    committed.0,
                    flight.id,
                    committed.1,
                    None,
                );
            assert(production_core_control_body(ended)) by {
                reveal(crate::global_store_control::detached_flight_control);
                reveal(crate::state::spec_note);
            };
            assert(active_document_writes_exclude_certified_cache(
                ended,
            )) by {
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_finish_preserves_active_write_cache_exclusion(
                ended,
                crate::handler_docs::FlightSpec {
                    idle: true,
                    ..flight
                },
                Ok(result),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::SweepEnd {
                    flight: flight.id,
                    committed: false,
                },
            );
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    committed.0,
                    flight.id,
                    committed.1,
                    None,
                );
            assert(production_core_control_body(ended)) by {
                reveal(crate::global_store_control::detached_flight_control);
                reveal(crate::state::spec_note);
            };
            assert(active_document_writes_exclude_certified_cache(
                ended,
            )) by {
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_commit_failed_preserves_active_write_cache_exclusion(
                ended,
                crate::handler_docs::FlightSpec {
                    idle: true,
                    ..flight
                },
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_active_write_cache_exclusion(
                advanced.0,
                crate::handler_docs::FlightSpec {
                    idle: true,
                    ..flight
                },
            );
        },
    }
    reveal(crate::handler_sched::spec_fire_idle);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_claim_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_sched::spec_fire_claim(
                state,
                flight,
                context,
            ),
        ),
{
    let origin_lane = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    let slot = crate::handler_docs::spec_slot_of(state, origin_lane);
    if slot.busy is Some {
        reveal(crate::handler_sched::spec_fire_claim);
        reveal(crate::handler_docs::spec_with_slot);
        reveal(crate::handler_docs::spec_inflight);
        reveal(active_document_writes_exclude_certified_cache);
    } else {
        let claimed = crate::handler_docs::spec_with_slot(
            state,
            origin_lane,
            crate::handler_docs::SlotSpec {
                busy: Some(flight.id),
                ..slot
            },
        );
        assert(production_core_control_body(claimed)) by {
            reveal(crate::handler_docs::spec_with_slot);
            reveal(production_core_control_body);
        };
        assert(active_document_writes_exclude_certified_cache(
            claimed,
        )) by {
            reveal(crate::handler_docs::spec_with_slot);
            reveal(active_document_writes_exclude_certified_cache);
        };
        lemma_fire_load_origin_preserves_active_write_cache_exclusion(
            claimed,
            flight,
            context,
        );
        reveal(crate::handler_sched::spec_fire_claim);
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_decide_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        working_document_provenance(state.keys.prefix, working),
        working_matches_target(working, flight.target),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_sched::spec_fire_decide(
                state,
                flight,
                working,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    assert(production_core_control_body(state));
    reveal(flight_submission_provenance);
    reveal(submission_provenance);
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
            let stepped = crate::verified::flight_spec::spec_step(
                crate::verified::flight_spec::AJob::Fire,
                body,
                at,
                state.cfg.retry_timeout,
            );
            let due = match (
                crate::handler_sched::spec_schedule_row(body),
                stepped.2.len() > 0,
            ) {
                (Some(row), true) => Some((row, stepped.2.last())),
                _ => None,
            };
            match due {
                None => {
                    assert(spec_stored_committed_at(
                        working.loaded.document,
                    ) <= at) by {
                        reveal(crate::document::spec_clamp_now);
                        reveal(crate::document::spec_loaded_committed_at);
                    };
                    assert(at <= echod_types::MAX_TIME) by {
                        reveal(crate::document::spec_clamp_now);
                    };
                    lemma_fire_idle_preserves_active_write_cache_exclusion(
                        state,
                        flight,
                        working,
                        at,
                        fired,
                    );
                },
                Some((row, pending)) => {
                    let advanced = stepped.0;
                    let next = match crate::handler_sched::
                        spec_schedule_row(advanced)
                    {
                        Some(candidate) => candidate.next_run_at,
                        None => pending.at,
                    };
                    lemma_fire_claim_preserves_active_write_cache_exclusion(
                        state,
                        flight,
                        crate::handler_docs::FireCtxSpec {
                            ws: working,
                            row,
                            advanced,
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
            lemma_fail_preserves_active_write_cache_exclusion(
                state,
                flight,
                "not a fire"@,
            );
        },
    }
    reveal(crate::handler_sched::spec_fire_decide);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_advance_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        match flight.work {
            crate::handler_docs::WorkSpec::Fire { schedule, .. } =>
                fire_context_provenance(
                    state.keys.prefix,
                    schedule,
                    context,
                ),
            _ => false,
        },
        context.t1 <= at,
        at <= echod_types::MAX_TIME,
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_sched::spec_fire_advance(
                state,
                flight,
                context,
                at,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    reveal(retained_commit_provenance);
    reveal(
        crate::global_store_lane::detached_flight_owns_primary,
    );
    reveal(flight_submission_provenance);
    reveal(submission_provenance);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire {
            schedule,
            fired,
            ..
        } => {
            reveal(fire_context_provenance);
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
            assert(production_core_control_body(noted)) by {
                reveal(crate::state::spec_note);
                reveal(production_core_control_body);
            };
            assert(cache_identity_provenance(noted)) by {
                reveal(crate::state::spec_note);
                reveal(cache_identity_provenance);
            };
            assert(active_document_writes_exclude_certified_cache(
                noted,
            )) by {
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            };
            crate::global_store_bounds::
                lemma_advance_stored_ids_bounded(
                    context.ws.loaded.document,
                    context.advanced,
                    at,
                );
            echod_concrete::quick_n_dirty::
                fire_candidate_preserves_well_formed(
                    context.ws.loaded.document,
                    context.t1,
                );
            assert(well_formed(
                echod_concrete::node::spec_advance_stored(
                    context.ws.loaded.document,
                    context.advanced,
                    at,
                ),
            )) by {
                reveal(echod_concrete::document::well_formed);
                reveal(echod_concrete::document::schedule_well_formed);
                reveal(echod_concrete::node::spec_advance_stored);
                reveal(echod_concrete::node::spec_body_deadline);
            };
            lemma_commit_new_establishes_provenance(
                noted,
                flight.id,
                flight.target,
                context.ws,
                context.advanced,
                echod_concrete::node::spec_body_deadline(
                    context.advanced,
                ),
                at,
                fired,
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
            assert(committed.1.w.loaded == context.ws.loaded) by {
                reveal(crate::handler_docs::spec_commit_new);
            };
            assert(committed.0 == noted) by {
                reveal(crate::handler_docs::spec_commit_new);
            };
            assert(committed.1.issued is None) by {
                reveal(crate::handler_docs::spec_commit_new);
            };
            lemma_initial_commit_advance_preserves_active_write_cache_exclusion(
                committed.0,
                flight.id,
                flight.target,
                committed.1,
            );
            let advanced = crate::handler_docs::spec_commit_advance(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            match advanced.2 {
                crate::handler_docs::ProgressSpec::Issued => {
                    reveal(crate::handler_docs::spec_inflight);
                    reveal(active_document_writes_exclude_certified_cache);
                },
                crate::handler_docs::ProgressSpec::Done(result) => {
                    crate::global_store_control::
                        lemma_commit_advance_nonissued_preserves_detached_flight_control(
                            committed.0,
                            flight.id,
                            committed.1,
                            None,
                        );
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
                    assert(production_core_control_body(ended)) by {
                        reveal(crate::global_store_control::detached_flight_control);
                        reveal(crate::state::spec_note);
                    };
                    assert(active_document_writes_exclude_certified_cache(
                        ended,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(active_document_writes_exclude_certified_cache);
                    };
                    lemma_finish_preserves_active_write_cache_exclusion(
                        ended,
                        flight,
                        Ok(result),
                    );
                },
                crate::handler_docs::ProgressSpec::Failed(error) => {
                    crate::global_store_control::
                        lemma_commit_advance_nonissued_preserves_detached_flight_control(
                            committed.0,
                            flight.id,
                            committed.1,
                            None,
                        );
                    let ended = crate::state::spec_note(
                        advanced.0,
                        crate::types::NoteSpec::AdvanceEnd {
                            flight: flight.id,
                            committed: false,
                        },
                    );
                    assert(production_core_control_body(ended)) by {
                        reveal(crate::global_store_control::detached_flight_control);
                        reveal(crate::state::spec_note);
                    };
                    assert(active_document_writes_exclude_certified_cache(
                        ended,
                    )) by {
                        reveal(crate::state::spec_note);
                        reveal(active_document_writes_exclude_certified_cache);
                    };
                    lemma_commit_failed_preserves_active_write_cache_exclusion(
                        ended,
                        flight,
                        error,
                    );
                },
                crate::handler_docs::ProgressSpec::Exhausted => {
                    lemma_op_exhausted_preserves_active_write_cache_exclusion(
                        advanced.0,
                        flight,
                    );
                },
            }
        },
        _ => {
            lemma_fail_preserves_active_write_cache_exclusion(
                state,
                flight,
                "not a fire"@,
            );
        },
    }
    reveal(crate::handler_sched::spec_fire_advance);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_loading_schedule_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_answered_fire_loading_schedule(
                state,
                flight,
                response,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    assert(production_core_control_body(state));
    match flight.work {
        crate::handler_docs::WorkSpec::Fire { schedule, .. } => {
            lemma_loaded_schedule_success_has_provenance(
                state,
                schedule,
                response,
            );
            let loaded = crate::handler_sched::spec_loaded_schedule(
                state,
                schedule,
                response,
            );
            assert(active_document_writes_exclude_certified_cache(
                loaded.0,
            )) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(active_document_writes_exclude_certified_cache);
            };
            assert(retained_commit_provenance(loaded.0)) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(retained_commit_provenance);
            };
            assert(cache_identity_provenance(loaded.0)) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(cache_identity_provenance);
            };
            assert(crate::global_store_control::detached_flight_control(
                loaded.0,
                flight.id,
            )) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(crate::global_store_control::detached_flight_control);
            };
            assert(crate::global_store_lane::detached_flight_owns_primary(
                loaded.0,
                flight,
            )) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(
                    crate::global_store_lane::detached_flight_owns_primary,
                );
            };
            match loaded.1 {
                Ok(working) => {
                    lemma_fire_decide_preserves_active_write_cache_exclusion(
                        loaded.0,
                        flight,
                        working,
                    );
                },
                Err(error) => {
                    lemma_fail_preserves_active_write_cache_exclusion(
                        loaded.0,
                        flight,
                        error,
                    );
                },
            }
        },
        _ => {
            lemma_fail_preserves_active_write_cache_exclusion(
                state,
                flight,
                "not a fire"@,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_fire_loading_schedule);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_run_initial_candidate_for_active(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(flight.id)
        }),
        working_document_provenance(state.keys.prefix, working),
        working_matches_target(
            working,
            crate::target::TargetSpec::Origin(context.origin),
        ),
        fire_context_provenance(
            state.keys.prefix,
            match flight.work {
                crate::handler_docs::WorkSpec::Fire { schedule, .. } =>
                    schedule,
                _ => Seq::empty(),
            },
            context,
        ),
    ensures
        ({
            let at = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(working.loaded),
                context.t1,
            );
            let retry_timeout =
                crate::handler_docs::spec_effective_retry_timeout(
                    state.cfg.retry_timeout,
                );
            let occurrence =
                echod_concrete::node::spec_occurrence_transition(
                    crate::document::spec_loaded_body(working.loaded),
                    context.pending,
                    at,
                    retry_timeout,
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
                occurrence.0,
                echod_concrete::node::spec_body_deadline(occurrence.0),
                at,
                None,
            );
            &&& context.t1 <= at
            &&& at <= echod_types::MAX_TIME
            &&& production_core_control_body(noted)
            &&& retained_commit_provenance(noted)
            &&& cache_identity_provenance(noted)
            &&& active_document_writes_exclude_certified_cache(noted)
            &&& committed.0 == noted
            &&& committed.1.issued is None
            &&& committed.1.seq.step is Start
            &&& commit_candidate_provenance(
                committed.0,
                flight.id,
                crate::target::TargetSpec::Origin(context.origin),
                committed.1,
            )
        }),
{
    reveal(fire_context_provenance);
    let at = crate::document::spec_clamp_now(
        crate::document::spec_loaded_committed_at(working.loaded),
        context.t1,
    );
    let retry_timeout =
        crate::handler_docs::spec_effective_retry_timeout(
            state.cfg.retry_timeout,
        );
    let occurrence = echod_concrete::node::spec_occurrence_transition(
        crate::document::spec_loaded_body(working.loaded),
        context.pending,
        at,
        retry_timeout,
    );
    let after = occurrence.0;
    assert(spec_stored_committed_at(working.loaded.document) <= at) by {
        reveal(crate::document::spec_clamp_now);
        reveal(crate::document::spec_loaded_committed_at);
    };
    assert(context.t1 <= at) by {
        reveal(crate::document::spec_clamp_now);
    };
    assert(at <= echod_types::MAX_TIME) by {
        reveal(crate::document::spec_clamp_now);
    };
    assert(0 < retry_timeout
        && retry_timeout <= echod_types::MAX_TIME) by {
        reveal(crate::handler_docs::spec_effective_retry_timeout);
    };
    assert(same_document_family(
        working.loaded.document,
        echod_concrete::node::spec_advance_stored(
            working.loaded.document,
            after,
            at,
        ),
    )) by {
        reveal(working_document_provenance);
        reveal(crate::document::loaded_workflow_has_identity);
        reveal(crate::document::spec_loaded_body);
        reveal(echod_concrete::node::spec_occurrence_transition);
        reveal(echod_concrete::node::spec_occurrence);
        reveal(echod_concrete::node::spec_advance_stored);
        reveal(same_document_family);
    };
    crate::global_store_bounds::lemma_stored_body_ids_bounded(
        working.loaded.document,
    );
    crate::global_store_bounds::
        lemma_occurrence_transition_preserves_body_ids_bounded(
            crate::document::spec_loaded_body(working.loaded),
            context.pending,
            at,
            retry_timeout,
        );
    crate::global_store_bounds::lemma_advance_stored_ids_bounded(
        working.loaded.document,
        after,
        at,
    );
    match working.loaded.document {
        StoredDocumentV::Workflow(workflow) => {
            crate::refinement::
                lemma_occurrence_transition_preserves_well_formed(
                    workflow,
                    context.pending,
                    at,
                    retry_timeout,
                );
        },
        _ => {
            reveal(working_matches_target);
            assert(false);
        },
    }
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
    assert(production_core_control_body(noted)) by {
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
    };
    assert(retained_commit_provenance(noted)) by {
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(noted)) by {
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    assert(active_document_writes_exclude_certified_cache(noted)) by {
        reveal(crate::state::spec_note);
        reveal(active_document_writes_exclude_certified_cache);
    };
    lemma_commit_new_establishes_provenance(
        noted,
        flight.id,
        crate::target::TargetSpec::Origin(context.origin),
        working,
        after,
        echod_concrete::node::spec_body_deadline(after),
        at,
        None,
    );
    reveal(crate::handler_docs::spec_commit_new);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_run_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy
                == Some(flight.id)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        match flight.work {
            crate::handler_docs::WorkSpec::Fire { schedule, .. } =>
                fire_context_provenance(
                    state.keys.prefix,
                    schedule,
                    context,
                ),
            _ => false,
        },
        working_document_provenance(state.keys.prefix, working),
        working_matches_target(
            working,
            crate::target::TargetSpec::Origin(context.origin),
        ),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_sched::spec_fire_run(
                state,
                flight,
                context,
                working,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    reveal(retained_commit_provenance);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire { schedule, .. } => {
            lemma_fire_run_initial_candidate_for_active(
                state,
                flight,
                context,
                working,
            );
        },
        _ => assert(false),
    }
    let at = crate::document::spec_clamp_now(
        crate::document::spec_loaded_committed_at(working.loaded),
        context.t1,
    );
    let retry_timeout =
        crate::handler_docs::spec_effective_retry_timeout(
            state.cfg.retry_timeout,
        );
    let occurrence = echod_concrete::node::spec_occurrence_transition(
        crate::document::spec_loaded_body(working.loaded),
        context.pending,
        at,
        retry_timeout,
    );
    let after = occurrence.0;
    let outbox = crate::handler_docs::spec_dispatches(
        after,
        occurrence.1,
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
        after,
        echod_concrete::node::spec_body_deadline(after),
        at,
        None,
    );
    lemma_detached_initial_commit_advance_preserves_retained_provenance(
        committed.0,
        flight.id,
        crate::target::TargetSpec::Origin(context.origin),
        committed.1,
    );
    lemma_commit_advance_frames_keys_and_flights(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    lemma_initial_commit_advance_preserves_active_write_cache_exclusion(
        committed.0,
        flight.id,
        crate::target::TargetSpec::Origin(context.origin),
        committed.1,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    if advanced.2 !is Issued {
        crate::global_store_control::
            lemma_commit_advance_nonissued_preserves_detached_flight_control(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
    }
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            reveal(crate::handler_docs::spec_inflight);
            reveal(active_document_writes_exclude_certified_cache);
        },
        crate::handler_docs::ProgressSpec::Done(_) => {
            lemma_fire_origin_done_tail_preserves_active_write_cache_exclusion(
                advanced.0,
                flight.id,
                flight,
                context,
                at,
                outbox,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            lemma_fire_origin_failed_tail_preserves_active_write_cache_exclusion(
                advanced.0,
                flight.id,
                flight,
                context,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_fire_origin_exhausted_tail_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
                context,
            );
        },
    }
    reveal(crate::handler_sched::spec_fire_run);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_loading_origin_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    revalidating: Option<crate::cache::CachedSpec>,
    context: crate::handler_docs::FireCtxSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy
                == Some(flight.id)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        match flight.work {
            crate::handler_docs::WorkSpec::Fire { schedule, .. } =>
                fire_context_provenance(
                    state.keys.prefix,
                    schedule,
                    context,
                ),
            _ => false,
        },
        cached_origin_provenance(context.origin, revalidating),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_answered_fire_loading_origin(
                state,
                flight,
                revalidating,
                context,
                response,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    assert(production_core_control_body(state));
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    assert(revalidating is Some ==>
        forall|op: u64|
            state.ops.contains_key(op)
                && state.store_certificates.contains_key(op)
                && certificate_written_document(
                    state.store_certificates[op],
                ) is Some
                && revalidating.unwrap().loaded.append_certified ==>
            document_lane(revalidating.unwrap().loaded.document)
                != document_lane(
                    certificate_written_document(
                        state.store_certificates[op],
                    ).unwrap(),
                )) by {
        if revalidating is Some {
            reveal(cached_origin_provenance);
            assert forall|op: u64|
                state.ops.contains_key(op)
                    && state.store_certificates.contains_key(op)
                    && certificate_written_document(
                        state.store_certificates[op],
                    ) is Some
                implies document_lane(
                    revalidating.unwrap().loaded.document,
                ) != document_lane(
                    certificate_written_document(
                        state.store_certificates[op],
                    ).unwrap(),
                ) by {
                lemma_active_document_write_differs_from_detached_owned_lane(
                    state,
                    op,
                    flight.id,
                    secondary,
                );
                assert(document_lane(
                    revalidating.unwrap().loaded.document,
                ) == secondary) by {
                    reveal(crate::document::loaded_workflow_has_identity);
                    reveal(document_lane);
                    reveal(crate::target::spec_name);
                };
            };
        }
    };
    lemma_loaded_origin_success_has_provenance(
        state,
        context.origin,
        revalidating,
        response,
    );
    lemma_loaded_origin_preserves_active_write_cache_exclusion(
        state,
        context.origin,
        revalidating,
        response,
    );
    crate::global_store_control::
        lemma_loaded_origin_preserves_detached_flight_control(
            state,
            flight.id,
            context.origin,
            revalidating,
            response,
        );
    lemma_loaded_origin_preserves_remembered_timer_lanes(
        state,
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
    assert(loaded.0.flights == state.flights) by {
        reveal(crate::handler_docs::spec_loaded_origin);
        reveal(crate::document::spec_validate_workflow_identity);
        reveal(crate::state::spec_note);
        reveal(crate::state::spec_remember);
        reveal(crate::state::spec_forget_origin);
    };
    assert(loaded.0.keys == state.keys) by {
        reveal(crate::handler_docs::spec_loaded_origin);
        reveal(crate::document::spec_validate_workflow_identity);
        reveal(crate::state::spec_note);
        reveal(crate::state::spec_remember);
        reveal(crate::state::spec_forget_origin);
    };
    assert(retained_commit_provenance(loaded.0)) by {
        reveal(crate::handler_docs::spec_loaded_origin);
        reveal(crate::document::spec_validate_workflow_identity);
        reveal(crate::state::spec_note);
        reveal(crate::state::spec_remember);
        reveal(crate::state::spec_forget_origin);
        reveal(retained_commit_provenance);
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        loaded.0,
        flight,
    )) by {
        reveal(crate::global_store_lane::detached_flight_owns_primary);
    };
    assert(loaded.0.flights.slots.contains_key(secondary)
        && loaded.0.flights.slots[secondary].busy
            == Some(flight.id));
    match loaded.1 {
        Ok(working) => {
            lemma_fire_run_preserves_active_write_cache_exclusion(
                loaded.0,
                flight,
                context,
                working,
            );
        },
        Err(error) => {
            lemma_fire_primary_differs_origin_lane(
                flight,
                context.origin,
            );
            crate::global_store_lane::
                lemma_detached_busy_owner_leaves_lane_unowned(
                    loaded.0.flights,
                    secondary,
                    flight.id,
                );
            crate::global_store_lane::
                lemma_detached_busy_owner_leaves_secondary_lane_unowned(
                    loaded.0,
                    secondary,
                    flight.id,
                );
            crate::global_store_lane::
                lemma_release_other_lane_preserves_detached_primary(
                    loaded.0,
                    secondary,
                    flight,
                );
            lemma_release_preserves_active_write_cache_exclusion(
                loaded.0,
                secondary,
            );
            lemma_release_preserves_retained_provenance(
                loaded.0,
                secondary,
            );
            crate::global_store_control::
                lemma_release_preserves_detached_flight_control(
                    loaded.0,
                    secondary,
                    flight.id,
                );
            let released = crate::handler_docs::spec_release(
                loaded.0,
                secondary,
            );
            reveal(crate::global_store_control::detached_flight_control);
            lemma_fail_preserves_active_write_cache_exclusion(
                released,
                flight,
                error,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_fire_loading_origin);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_idle_preserves_active_write_cache_exclusion(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        crate::global_store_control::detached_flight_control(state, fid),
        flight.id == fid,
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        commit_candidate_provenance(
            state,
            fid,
            flight.target,
            commit,
        ),
        commit.issued is Some,
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_answered_fire_idle(
                state,
                fid,
                flight,
                commit,
                response,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    assert(production_core_control_body(state));
    reveal(
        crate::global_store_lane::detached_flight_owns_primary,
    );
    lemma_detached_commit_advance_preserves_active_write_cache_exclusion(
        state,
        fid,
        flight.target,
        commit,
        response,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            reveal(crate::handler_docs::spec_inflight);
            reveal(active_document_writes_exclude_certified_cache);
        },
        crate::handler_docs::ProgressSpec::Done(result) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
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
                reveal(crate::global_store_control::detached_flight_control);
                reveal(crate::state::spec_note);
            };
            assert(active_document_writes_exclude_certified_cache(
                ended,
            )) by {
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_finish_preserves_active_write_cache_exclusion(
                ended,
                flight,
                Ok(result),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::SweepEnd {
                    flight: fid,
                    committed: false,
                },
            );
            assert(production_core_control_body(ended)) by {
                reveal(crate::global_store_control::detached_flight_control);
                reveal(crate::state::spec_note);
            };
            assert(active_document_writes_exclude_certified_cache(
                ended,
            )) by {
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_commit_failed_preserves_active_write_cache_exclusion(
                ended,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_fire_idle);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_schedule_preserves_active_write_cache_exclusion(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        crate::global_store_control::detached_flight_control(state, fid),
        flight.id == fid,
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        commit_candidate_provenance(
            state,
            fid,
            flight.target,
            commit,
        ),
        commit.issued is Some,
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_answered_fire_schedule(
                state,
                fid,
                flight,
                commit,
                response,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    assert(production_core_control_body(state));
    reveal(
        crate::global_store_lane::detached_flight_owns_primary,
    );
    lemma_detached_commit_advance_preserves_active_write_cache_exclusion(
        state,
        fid,
        flight.target,
        commit,
        response,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        fid,
        commit,
        Some(response),
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            reveal(crate::handler_docs::spec_inflight);
            reveal(active_document_writes_exclude_certified_cache);
        },
        crate::handler_docs::ProgressSpec::Done(result) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
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
            assert(production_core_control_body(ended)) by {
                reveal(crate::global_store_control::detached_flight_control);
                reveal(crate::state::spec_note);
            };
            assert(active_document_writes_exclude_certified_cache(
                ended,
            )) by {
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_finish_preserves_active_write_cache_exclusion(
                ended,
                flight,
                Ok(result),
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
            let ended = crate::state::spec_note(
                advanced.0,
                crate::types::NoteSpec::AdvanceEnd {
                    flight: fid,
                    committed: false,
                },
            );
            assert(production_core_control_body(ended)) by {
                reveal(crate::global_store_control::detached_flight_control);
                reveal(crate::state::spec_note);
            };
            assert(active_document_writes_exclude_certified_cache(
                ended,
            )) by {
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_commit_failed_preserves_active_write_cache_exclusion(
                ended,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_fire_schedule);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_origin_done_tail_preserves_active_write_cache_exclusion(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
    outbox: Seq<(Seq<char>, crate::types::MessageSpec)>,
)
    requires
        crate::global_store_control::detached_flight_control(state, fid),
        flight.id == fid,
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(fid)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        match flight.work {
            crate::handler_docs::WorkSpec::Fire { schedule, .. } =>
                fire_context_provenance(
                    state.keys.prefix,
                    schedule,
                    context,
                ),
            _ => false,
        },
        context.t1 <= at,
        at <= echod_types::MAX_TIME,
    ensures
        ({
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    state,
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
            active_document_writes_exclude_certified_cache(
                crate::handler_sched::spec_fire_advance(
                    released,
                    flight,
                    context,
                    at,
                ),
            )
        }),
{
    lemma_fire_origin_done_tail_preserves_retained_provenance(
        state,
        fid,
        flight,
        context,
        at,
        outbox,
    );
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    let ended = crate::state::spec_note(
        crate::state::spec_note(
            state,
            crate::types::NoteSpec::FireEnd {
                flight: fid,
                committed: true,
            },
        ),
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    assert(active_document_writes_exclude_certified_cache(ended)) by {
        reveal(crate::state::spec_note);
        reveal(active_document_writes_exclude_certified_cache);
    };
    assert(retained_commit_provenance(ended)) by {
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(ended)) by {
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    lemma_send_all_preserves_active_write_cache_exclusion(
        ended,
        outbox,
    );
    lemma_send_all_preserves_retained_provenance(ended, outbox);
    lemma_send_all_preserves_core_control_body(ended, outbox);
    lemma_send_all_preserves_flights(ended, outbox);
    lemma_send_all_preserves_keys(ended, outbox);
    crate::global_store_control::
        lemma_send_all_preserves_detached_flight_control(
            ended,
            flight.id,
            outbox,
        );
    let sent = crate::handler_docs::spec_send_all(ended, outbox);
    assert(sent.flights.slots.contains_key(secondary)
        && sent.flights.slots[secondary].busy == Some(fid)) by {
        reveal(crate::state::spec_note);
    };
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_lane_unowned(
            sent.flights,
            secondary,
            fid,
        );
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_secondary_lane_unowned(
            sent,
            secondary,
            fid,
        );
    crate::global_store_control::
        lemma_send_all_preserves_detached_flight_control(
            ended,
            fid,
            outbox,
        );
    lemma_fire_primary_differs_origin_lane(flight, context.origin);
    crate::global_store_lane::
        lemma_release_other_lane_preserves_detached_primary(
            sent,
            secondary,
            flight,
        );
    lemma_release_preserves_active_write_cache_exclusion(
        sent,
        secondary,
    );
    lemma_release_preserves_retained_provenance(sent, secondary);
    crate::global_store_control::
        lemma_release_preserves_detached_flight_control(
            sent,
            secondary,
            fid,
        );
    lemma_release_preserves_keys(sent, secondary);
    let released = crate::handler_docs::spec_release(sent, secondary);
    assert(crate::global_store_control::detached_flight_control(
        released,
        fid,
    ));
    assert(retained_commit_provenance(released));
    assert(cache_identity_provenance(released));
    assert(crate::global_store_lane::detached_flight_owns_primary(
        released,
        flight,
    ));
    assert(released.keys == state.keys) by {
        reveal(crate::state::spec_note);
    };
    lemma_fire_advance_preserves_active_write_cache_exclusion(
        released,
        flight,
        context,
        at,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_origin_failed_tail_preserves_active_write_cache_exclusion(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    error: echod_concrete::store::StoreErrorSpec,
)
    requires
        crate::global_store_control::detached_flight_control(state, fid),
        flight.id == fid,
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(fid)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight.work is Fire,
    ensures
        ({
            let ended = crate::state::spec_note(
                state,
                crate::types::NoteSpec::FireEnd {
                    flight: fid,
                    committed: false,
                },
            );
            let forgotten = crate::state::spec_forget_origin(
                ended,
                context.origin,
            );
            let released = crate::handler_docs::spec_release(
                forgotten,
                crate::target::spec_name(
                    crate::target::TargetSpec::Origin(context.origin),
                ),
            );
            active_document_writes_exclude_certified_cache(
                crate::handler_docs::spec_commit_failed(
                    released,
                    flight,
                    error,
                ),
            )
        }),
{
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    let ended = crate::state::spec_note(
        state,
        crate::types::NoteSpec::FireEnd {
            flight: fid,
            committed: false,
        },
    );
    assert(production_core_control_body(ended)) by {
        reveal(crate::global_store_control::detached_flight_control);
        reveal(crate::state::spec_note);
    };
    assert(active_document_writes_exclude_certified_cache(ended)) by {
        reveal(crate::state::spec_note);
        reveal(active_document_writes_exclude_certified_cache);
    };
    assert(retained_commit_provenance(ended)) by {
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(ended)) by {
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    lemma_cache_remove_preserves_active_write_cache_exclusion(
        ended,
        context.origin,
    );
    lemma_cache_remove_preserves_identity(
        ended.cache,
        context.origin,
    );
    lemma_cache_remove_preserves_unique_origins(
        ended.cache,
        context.origin,
    );
    let forgotten = crate::state::spec_forget_origin(
        ended,
        context.origin,
    );
    assert(production_core_control_body(forgotten)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
    };
    assert(retained_commit_provenance(forgotten)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(forgotten)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_lane_unowned(
            forgotten.flights,
            secondary,
            fid,
        );
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_secondary_lane_unowned(
            forgotten,
            secondary,
            fid,
        );
    lemma_release_preserves_active_write_cache_exclusion(
        forgotten,
        secondary,
    );
    lemma_release_preserves_retained_provenance(
        forgotten,
        secondary,
    );
    crate::global_store_control::
        lemma_release_preserves_detached_flight_control(
            forgotten,
            secondary,
            fid,
        );
    let released = crate::handler_docs::spec_release(
        forgotten,
        secondary,
    );
    reveal(crate::global_store_control::detached_flight_control);
    lemma_commit_failed_preserves_active_write_cache_exclusion(
        released,
        flight,
        error,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_origin_exhausted_tail_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
)
    requires
        active_document_writes_exclude_certified_cache(state),
    ensures
        ({
            let forgotten = crate::state::spec_forget_origin(
                state,
                context.origin,
            );
            let abandoned = crate::handler_docs::spec_abandon_slot(
                forgotten,
                crate::target::spec_name(
                    crate::target::TargetSpec::Origin(context.origin),
                ),
            );
            active_document_writes_exclude_certified_cache(
                crate::handler_docs::spec_op_exhausted(
                    abandoned,
                    flight,
                ),
            )
        }),
{
    lemma_cache_remove_preserves_active_write_cache_exclusion(
        state,
        context.origin,
    );
    let forgotten = crate::state::spec_forget_origin(
        state,
        context.origin,
    );
    let abandoned = crate::handler_docs::spec_abandon_slot(
        forgotten,
        crate::target::spec_name(
            crate::target::TargetSpec::Origin(context.origin),
        ),
    );
    assert(active_document_writes_exclude_certified_cache(
        abandoned,
    )) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(active_document_writes_exclude_certified_cache);
    };
    lemma_op_exhausted_preserves_active_write_cache_exclusion(
        abandoned,
        flight,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_origin_preserves_active_write_cache_exclusion(
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
        crate::global_store_control::detached_flight_control(state, fid),
        flight.id == fid,
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(fid)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        match flight.work {
            crate::handler_docs::WorkSpec::Fire { schedule, .. } =>
                fire_context_provenance(
                    state.keys.prefix,
                    schedule,
                    context,
                ),
            _ => false,
        },
        context.t1 <= at,
        at <= echod_types::MAX_TIME,
        commit_candidate_provenance(
            state,
            fid,
            crate::target::TargetSpec::Origin(context.origin),
            commit,
        ),
        commit.issued is Some,
    ensures
        active_document_writes_exclude_certified_cache(
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
    reveal(crate::global_store_control::detached_flight_control);
    reveal(
        crate::global_store_lane::detached_flight_owns_primary,
    );
    lemma_detached_commit_advance_preserves_active_write_cache_exclusion(
        state,
        fid,
        crate::target::TargetSpec::Origin(context.origin),
        commit,
        response,
    );
    lemma_detached_commit_advance_preserves_retained_provenance(
        state,
        fid,
        crate::target::TargetSpec::Origin(context.origin),
        commit,
        response,
    );
    lemma_commit_advance_frames_keys_and_flights(
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
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            reveal(crate::handler_docs::spec_inflight);
            reveal(active_document_writes_exclude_certified_cache);
        },
        crate::handler_docs::ProgressSpec::Done(_) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
            lemma_fire_origin_done_tail_preserves_active_write_cache_exclusion(
                advanced.0,
                fid,
                flight,
                context,
                at,
                outbox,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    fid,
                    commit,
                    Some(response),
                );
            lemma_fire_origin_failed_tail_preserves_active_write_cache_exclusion(
                advanced.0,
                fid,
                flight,
                context,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_fire_origin_exhausted_tail_preserves_active_write_cache_exclusion(
                advanced.0,
                flight,
                context,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_fire_origin);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_phase_preserves_active_write_cache_exclusion(
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    phase: crate::handler_docs::PhaseSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        crate::global_store_control::detached_flight_control(state, fid),
        flight.id == fid,
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        match phase {
            crate::handler_docs::PhaseSpec::FireLoadingOrigin {
                ctx,
                ..
            }
            | crate::handler_docs::PhaseSpec::FireOrigin {
                ctx,
                ..
            } => {
                let secondary = crate::target::spec_name(
                    crate::target::TargetSpec::Origin(ctx.origin),
                );
                &&& state.flights.slots.contains_key(secondary)
                &&& state.flights.slots[secondary].busy == Some(fid)
            },
            _ => true,
        },
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        active_document_writes_exclude_certified_cache(state),
        flight_submission_provenance(flight),
        flight_control_provenance(
            state.keys.prefix,
            crate::handler_docs::FlightSpec { phase, ..flight },
        ),
        phase_commit_candidate_provenance(
            state,
            fid,
            flight.target,
            phase,
        ),
        match phase {
            crate::handler_docs::PhaseSpec::Origin { commit, .. }
            | crate::handler_docs::PhaseSpec::Schedule { commit, .. }
            | crate::handler_docs::PhaseSpec::FireIdle { commit }
            | crate::handler_docs::PhaseSpec::FireOrigin { commit, .. }
            | crate::handler_docs::PhaseSpec::FireSchedule { commit } =>
                commit.issued is Some,
            _ => true,
        },
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_answered_phase(
                state,
                fid,
                flight,
                phase,
                response,
            ),
        ),
{
    reveal(phase_commit_candidate_provenance);
    match phase {
        crate::handler_docs::PhaseSpec::Loading {
            revalidating,
            ..
        } => {
            lemma_answered_loading_preserves_active_write_cache_exclusion(
                state,
                flight,
                revalidating,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::Origin { commit, done } => {
            lemma_answered_origin_preserves_active_write_cache_exclusion(
                state,
                fid,
                flight,
                commit,
                done,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::Schedule { commit, done } => {
            lemma_answered_schedule_preserves_active_write_cache_exclusion(
                state,
                fid,
                flight,
                commit,
                done,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::FireLoadingSchedule { .. } => {
            lemma_answered_fire_loading_schedule_preserves_active_write_cache_exclusion(
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
            lemma_answered_fire_loading_origin_preserves_active_write_cache_exclusion(
                state,
                flight,
                revalidating,
                ctx,
                response,
            );
        },
        crate::handler_docs::PhaseSpec::FireIdle { commit } => {
            lemma_answered_fire_idle_preserves_active_write_cache_exclusion(
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
            lemma_answered_fire_origin_preserves_active_write_cache_exclusion(
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
            lemma_answered_fire_schedule_preserves_active_write_cache_exclusion(
                state,
                fid,
                flight,
                commit,
                response,
            );
        },
        _ => {
            reveal(crate::global_store_control::detached_flight_control);
            lemma_fail_preserves_active_write_cache_exclusion(
                state,
                flight,
                "an answer the flight did not wait for"@,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_phase);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_matching_flight_completion_preserves_active_write_cache_exclusion(
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
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            active_document_writes_exclude_certified_cache(
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    let flight = state.flights.inflight[fid];
    assert(state.flights.inflight.contains_key(fid)) by {
        reveal(production_core_control_body);
        reveal(active_flight_owners_match_phase);
    };
    assert(flight.phase.expects() == Some(op)) by {
        reveal(production_core_control_body);
        reveal(active_flight_owners_match_phase);
    };
    assert(flight.id == fid) by {
        reveal(production_core_control_body);
        reveal(active_flight_ids_match_keys);
    };
    lemma_consume_and_detach_flight_preserves_retained_provenance(
        state,
        fid,
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
    let detached = crate::handler_docs::spec_take_flight(consumed, fid);
    assert(active_document_writes_exclude_certified_cache(
        detached,
    )) by {
        reveal(crate::handler_docs::spec_take_flight);
        reveal(active_document_writes_exclude_certified_cache);
    };
    let idle = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Idle,
        ..flight
    };
    assert(flight_submission_provenance(idle));
    assert(flight_control_provenance(
        detached.keys.prefix,
        crate::handler_docs::FlightSpec {
            phase: flight.phase,
            ..idle
        },
    ));
    lemma_answered_phase_preserves_active_write_cache_exclusion(
        detached,
        fid,
        idle,
        flight.phase,
        response,
    );
    reveal(crate::handler_docs::spec_flight_completed);
}

pub(crate) proof fn lemma_with_timers_preserves_retained_provenance(
    state: S,
    timers: crate::state_timers::TimersSpec,
)
    requires
        production_core_control_body(state),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
    ensures
        ({
            let next =
                crate::handler_timers::spec_with_timers(state, timers);
            &&& retained_commit_provenance(next)
            &&& cache_identity_provenance(next)
        }),
{
    let next = crate::handler_timers::spec_with_timers(state, timers);
    reveal(crate::handler_timers::spec_with_timers);
    assert(next.flights == state.flights);
    assert(next.cache == state.cache);
    assert(next.keys == state.keys);
    assert(remembered_timer_lanes_consistent_node(next.node.core)) by {
        reveal(retained_commit_provenance);
        reveal(remembered_timer_lanes_consistent);
    };
    assert forall|op: u64, fid: u64|
        state.ops.contains_key(op)
            && state.ops[op] == Owner::Flight(fid) implies {
            &&& state.store_requests.contains_key(op)
            &&& state.store_certificates.contains_key(op)
            &&& next.ops.contains_key(op)
            &&& next.ops[op] == Owner::Flight(fid)
            &&& next.store_requests.contains_key(op)
            &&& next.store_requests[op] == state.store_requests[op]
            &&& next.store_certificates.contains_key(op)
            &&& next.store_certificates[op]
                == state.store_certificates[op]
        } by {
        assert(state.store_requests.contains_key(op)) by {
            reveal(production_core_control_body);
        };
        assert(state.store_certificates.contains_key(op)) by {
            reveal(production_core_control_body);
        };
    };
    lemma_nonflight_frame_preserves_retained_provenance(state, next);
}

pub(crate) proof fn lemma_fresh_store_other_only_adds_nonappend(
    state: S,
    request: StoreReqSpec,
    owner: Owner,
)
    requires
        pending_store_effects_are_exact(state),
        state.ops_exhausted || {
            &&& !state.ops.contains_key(state.next_op)
            &&& !state.store_requests.contains_key(state.next_op)
            &&& !state.store_certificates.contains_key(state.next_op)
        },
    ensures
        only_other_store_effects_added(
            state,
            crate::state::spec_store(state, request, owner).0,
        ),
{
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(only_other_store_effects_added);
    reveal(pending_store_effects_are_exact);
    let next = crate::state::spec_store(state, request, owner).0;
    assert forall|i: int, op: u64, emitted: StoreReqSpec|
        state.out.len() <= i < next.out.len()
            && next.out[i]
                == (crate::types::EffectSpec::Store {
                    op,
                    request: emitted,
                })
            && next.store_certificates.contains_key(op) implies
                !(next.store_certificates[op] is DocumentAppend) by {
        assert(i == state.out.len());
        assert(op == state.next_op);
        assert(next.store_certificates[op]
            == StoreEffectCertificateV::Other);
    };
}

pub(crate) proof fn lemma_store_other_only_adds_nonappend(
    state: S,
    request: StoreReqSpec,
    owner: Owner,
)
    requires
        production_core_control_body(state),
    ensures
        only_other_store_effects_added(
            state,
            crate::state::spec_store(state, request, owner).0,
        ),
{
    assert(state.ops_exhausted || {
        &&& !state.ops.contains_key(state.next_op)
        &&& !state.store_requests.contains_key(state.next_op)
        &&& !state.store_certificates.contains_key(state.next_op)
    }) by {
        reveal(production_core_control_body);
        reveal(exact_store_certificate_maps);
        reveal(crate::production_relation::operation_allocator_consistent);
        reveal(crate::production_relation::operation_id_fresh);
    };
    lemma_fresh_store_other_only_adds_nonappend(
        state,
        request,
        owner,
    );
}

pub(crate) proof fn lemma_members_read_nodes_only_adds_nonappend(
    state: S,
    keys: Seq<Seq<char>>,
    pending: Map<u64, bool>,
)
    requires
        production_core_control_body(state),
    ensures
        only_other_store_effects_added(
            state,
            crate::handler_node::spec_read_nodes(
                state, keys, pending,
            ).0,
        ),
    decreases keys.len(),
{
    reveal_with_fuel(crate::handler_node::spec_read_nodes, 1);
    if keys.len() > 0 {
        let key = keys[0];
        let own = crate::keys::spec_node_of_key(
            state.keys.prefix,
            key,
        ) == Some(state.node.members.me.id);
        let request = StoreReqSpec::Get { key };
        let one = if own {
            state
        } else {
            lemma_store_other_only_adds_nonappend(
                state,
                request,
                Owner::Members,
            );
            crate::state::spec_store(state, request, Owner::Members).0
        };
        assert(only_other_store_effects_added(state, one)) by {
            if own {
                reveal(only_other_store_effects_added);
            }
        };
        assert(production_core_control_body(one)) by {
            if !own {
                lemma_nonflight_store_issue_preserves_core_control_body(
                    state,
                    request,
                    Owner::Members,
                );
            }
        };
        let next_pending = if own {
            pending
        } else {
            let stored = crate::state::spec_store(
                state,
                request,
                Owner::Members,
            );
            match stored.1 {
                Some(op) => pending.insert(op, true),
                None => pending,
            }
        };
        lemma_members_read_nodes_only_adds_nonappend(
            one,
            keys.drop_first(),
            next_pending,
        );
        lemma_only_other_store_effects_added_transitive(
            state,
            one,
            crate::handler_node::spec_read_nodes(
                state, keys, pending,
            ).0,
        );
    } else {
        reveal(only_other_store_effects_added);
    }
}

pub(crate) proof fn lemma_members_read_one_outcome_only_adds_nonappend(
    state: S,
    nodes: crate::state_node::RosterSpec,
    now: u64,
    failed: Option<echod_concrete::store::StoreErrorSpec>,
    outcome: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
    ensures
        only_other_store_effects_added(
            state,
            crate::handler_node::spec_read_one_outcome(
                state, nodes, now, failed, outcome,
            ).0,
        ),
{
    reveal(crate::handler_node::spec_read_one_outcome);
    match outcome {
        echod_concrete::store::StoreRes::Get {
            result: Ok(Some((bytes, _))),
        } => match crate::state_node::spec_parse_announcement(bytes@) {
            Some(announcement) => {
                let staged = S {
                    node: crate::state_node::NodeSpec {
                        fleet_at:
                            if state.node.fleet_at > announcement.at {
                                state.node.fleet_at
                            } else {
                                announcement.at
                            },
                        ..state.node
                    },
                    ..state
                };
                assert(only_other_store_effects_added(
                    state,
                    staged,
                )) by {
                    reveal(only_other_store_effects_added);
                };
                assert(staged.ops_exhausted || {
                    &&& !staged.ops.contains_key(staged.next_op)
                    &&& !staged.store_requests.contains_key(
                        staged.next_op,
                    )
                    &&& !staged.store_certificates.contains_key(
                        staged.next_op,
                    )
                }) by {
                    reveal(production_core_control_body);
                    reveal(exact_store_certificate_maps);
                    reveal(
                        crate::production_relation::
                            operation_allocator_consistent,
                    );
                    reveal(
                        crate::production_relation::operation_id_fresh,
                    );
                };
                if announcement.at.saturating_add(
                    (2 as u64).saturating_mul(
                        staged.node.members.ttl,
                    ),
                ) < now {
                    let request = StoreReqSpec::Del {
                        key: crate::keys::spec_node_key(
                            staged.keys.prefix,
                            announcement.id,
                        ),
                    };
                    assert(production_core_control_body(staged)) by {
                        reveal(production_core_control_body);
                    };
                    lemma_store_other_only_adds_nonappend(
                        staged,
                        request,
                        Owner::Ignored,
                    );
                    lemma_only_other_store_effects_added_transitive(
                        state,
                        staged,
                        crate::state::spec_store(
                            staged,
                            request,
                            Owner::Ignored,
                        ).0,
                    );
                }
            },
            None => {},
        },
        _ => {},
    }
    reveal(only_other_store_effects_added);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_initial_commit_advance_preserves_core_retained_append_certificates(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    store: StoreV,
)
    requires
        commit.issued is None,
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_commit_advance(
                state,
                fid,
                commit,
                None,
            ).0,
        ),
{
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_allocate_arm_token);
    let allocated = crate::handler_docs::spec_allocate_arm_token(
        state,
        commit,
    );
    if allocated.2 {
        let advanced_pair =
            crate::verified::flight_spec::spec_advance(
                allocated.1.seq,
                allocated.0.node.core,
                crate::verified::flight_spec::answer_v(
                    allocated.1.seq.step,
                    None,
                ),
            );
        let advanced_state = S {
            node: crate::state_node::NodeSpec {
                core: advanced_pair.1,
                ..allocated.0.node
            },
            ..allocated.0
        };
        let advanced_commit = crate::handler_docs::CommittingSpec {
            seq: advanced_pair.0,
            ..allocated.1
        };
        lemma_core_retained_append_certificates_frame(
            store,
            state,
            advanced_state,
        );
        match advanced_pair.2 {
            crate::verified::flight_spec::AOutcome::Act(
                crate::verified::flight_spec::AAct::Write {
                    cond,
                    idle,
                },
            ) => {
                lemma_issue_write_preserves_core_retained_append_certificates(
                    advanced_state,
                    fid,
                    advanced_commit,
                    cond,
                    idle,
                    store,
                );
            },
            _ => {},
        }
    }
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(core_retained_append_certificates);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_initial_origin_commit_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        commit_candidate_provenance(
            state,
            flight.id,
            flight.target,
            commit,
        ),
        commit.issued is None,
        commit.seq.step is Start,
        loaded_append_certificate(
            store,
            state.keys.prefix,
            commit.w.loaded,
        ),
        commit == crate::handler_docs::spec_decide(
            state,
            flight.work,
            commit.w,
        ).1,
        done == crate::handler_docs::spec_decide(
            state,
            flight.work,
            commit.w,
        ).2,
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_run_origin(
                state,
                flight,
                commit.w,
            ),
        ),
{
    reveal(crate::handler_docs::spec_run_origin);
    let decided = crate::handler_docs::spec_decide(
        state,
        flight.work,
        commit.w,
    );
    assert(decided.0 == state) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
    };
    assert(decided.1 == commit);
    assert(decided.2 == done);
    lemma_initial_commit_advance_preserves_core_retained_append_certificates(
        state,
        flight.id,
        commit,
        store,
    );
    lemma_detached_initial_commit_advance_preserves_retained_provenance(
        state,
        flight.id,
        flight.target,
        commit,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        flight.id,
        commit,
        None,
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            assert(phase_append_certificates(
                store,
                advanced.0.keys.prefix,
                crate::handler_docs::PhaseSpec::Origin {
                    commit: advanced.1,
                    done,
                },
            )) by {
                reveal(phase_append_certificates);
                reveal(commit_loaded_append_certificate);
                reveal(crate::handler_docs::spec_commit_advance);
                reveal(crate::handler_docs::spec_allocate_arm_token);
                reveal(crate::verified::flight_spec::spec_advance);
                reveal(crate::handler_docs::spec_issue_write);
                reveal(crate::state::spec_store_certified);
                reveal(crate::state::spec_store_raw);
            };
            lemma_inflight_preserves_core_retained_append_certificates(
                store,
                advanced.0,
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
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    flight.id,
                    commit,
                    None,
                );
            assert(crate::global_store_lane::
                detached_flight_owns_primary(
                    advanced.0,
                    flight,
                )) by {
                reveal(
                    crate::global_store_lane::
                        detached_flight_owns_primary,
                );
                lemma_commit_advance_frames_keys_and_flights(
                    state,
                    flight.id,
                    commit,
                    None,
                );
            };
            lemma_committed_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                flight,
                done,
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    state,
                    flight.id,
                    commit,
                    None,
                );
            assert(crate::global_store_lane::
                detached_flight_owns_primary(
                    advanced.0,
                    flight,
                )) by {
                reveal(
                    crate::global_store_lane::
                        detached_flight_owns_primary,
                );
                lemma_commit_advance_frames_keys_and_flights(
                    state,
                    flight.id,
                    commit,
                    None,
                );
            };
            lemma_commit_failed_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                flight,
            );
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_run_origin_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    store: StoreV,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        working_document_provenance(state.keys.prefix, working),
        working_matches_target(working, flight.target),
        flight_submission_provenance(flight),
        loaded_append_certificate(
            store,
            state.keys.prefix,
            working.loaded,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_run_origin(
                state,
                flight,
                working,
            ),
        ),
{
    lemma_run_origin_preserves_retained_provenance(
        state,
        flight,
        working,
    );
    lemma_decide_establishes_commit_provenance(
        state,
        flight,
        working,
    );
    let decided = crate::handler_docs::spec_decide(
        state,
        flight.work,
        working,
    );
    assert(decided.0 == state) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
    };
    assert(decided.1.issued is None) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
    };
    assert(decided.1.seq.step is Start) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
        reveal(crate::verified::flight_spec::spec_new);
    };
    assert(decided.1.w == working) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
    };
    assert(crate::handler_docs::spec_decide(
        state,
        flight.work,
        decided.1.w,
    ) == decided) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
    };
    lemma_initial_origin_commit_preserves_core_retained_append_certificates(
        state,
        flight,
        decided.1,
        decided.2,
        store,
    );
}

pub(crate) proof fn lemma_run_schedule_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    store: StoreV,
)
    requires
        crate::global_store_control::detached_flight_control(
            state,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        working_document_provenance(state.keys.prefix, working),
        working_matches_target(working, flight.target),
        flight_submission_provenance(flight),
        loaded_append_certificate(
            store,
            state.keys.prefix,
            working.loaded,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_sched::spec_run_schedule(
                state,
                flight,
                working,
            ),
        ),
{
    lemma_run_origin_preserves_core_retained_append_certificates(
        state,
        flight,
        working,
        store,
    );
    let decided = crate::handler_docs::spec_decide(
        state,
        flight.work,
        working,
    );
    assert(decided.0 == state) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
    };
    assert(decided.1.issued is None) by {
        reveal(crate::handler_docs::spec_decide);
        reveal(crate::handler_docs::spec_commit_new);
    };
    lemma_initial_commit_advance_preserves_core_retained_append_certificates(
        state,
        flight.id,
        decided.1,
        store,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        state,
        flight.id,
        decided.1,
        None,
    );
    reveal(crate::handler_docs::spec_run_origin);
    reveal(crate::handler_sched::spec_run_schedule);
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            assert(phase_append_certificates(
                store,
                advanced.0.keys.prefix,
                crate::handler_docs::PhaseSpec::Schedule {
                    commit: advanced.1,
                    done: decided.2,
                },
            )) by {
                reveal(phase_append_certificates);
                reveal(commit_loaded_append_certificate);
                reveal(crate::handler_docs::spec_commit_advance);
                reveal(crate::handler_docs::spec_allocate_arm_token);
                reveal(crate::verified::flight_spec::spec_advance);
                reveal(crate::handler_docs::spec_issue_write);
                reveal(crate::state::spec_store_certified);
                reveal(crate::state::spec_store_raw);
                reveal(crate::handler_docs::spec_decide);
                reveal(crate::handler_docs::spec_commit_new);
            };
            lemma_inflight_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::Schedule {
                        commit: advanced.1,
                        done: decided.2,
                    },
                    ..flight
                },
            );
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_commit_frames_emitted_append_provenance(
    state: S,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
    store: StoreV,
)
    requires
        emitted_append_effects_have_store_provenance(
            store,
            state.keys.prefix,
            state.out,
            state,
        ),
        commit.issued is Some,
    ensures
        ({
            let answered = crate::handler_docs::spec_answered(
                state,
                crate::handler_docs::CommittingSpec {
                    issued: None,
                    ..commit
                },
                commit.issued.unwrap(),
                answer,
            );
            &&& emitted_append_effects_have_store_provenance(
                store,
                state.keys.prefix,
                answered.0.out,
                answered.0,
            )
            &&& answered.0.keys == state.keys
            &&& answered.1.w.loaded == commit.w.loaded
            &&& answered.1.w.key == commit.w.key
        }),
{
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_remember);
    reveal(emitted_append_effects_have_store_provenance);
}

}
