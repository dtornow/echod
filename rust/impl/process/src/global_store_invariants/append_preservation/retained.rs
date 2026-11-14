//! Retained append-certification preservation lemmas.

#![cfg(verus_keep_ghost)]

use vstd::prelude::*;

use super::super::*;

verus! {

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_loaded_origin_preserves_append_gate(
    state: S,
    origin: Seq<char>,
    revalidating: Option<crate::cache::CachedSpec>,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        cache_identity_provenance(state),
        revalidating is Some ==> {
            &&& crate::document::loaded_workflow_has_identity(
                revalidating.unwrap().loaded,
                origin,
            )
            &&& well_formed(
                revalidating.unwrap().loaded.document,
            )
            &&& echod_concrete::document::document_ids_bounded(
                revalidating.unwrap().loaded.document,
            )
        },
    ensures
        ({
            let loaded = crate::handler_docs::spec_loaded_origin(
                state,
                origin,
                revalidating,
                response,
            );
            loaded.1 is Ok
                && loaded.1->Ok_0.loaded.append_certified ==> {
                    &&& revalidating is Some
                    &&& response
                        == echod_concrete::store::StoreRes::
                            GetIfNoneMatch {
                            result: Ok(
                                echod_concrete::store::Read::NotModified,
                            ),
                        }
                    &&& loaded.1->Ok_0.loaded
                        == revalidating.unwrap().loaded
                }
        }),
{
    reveal(crate::handler_docs::spec_loaded_origin);
    reveal(crate::document::spec_validate_workflow_identity);
    match revalidating {
        Some(_) => match response {
            echod_concrete::store::StoreRes::GetIfNoneMatch {
                result: Ok(echod_concrete::store::Read::NotModified),
            } => {},
            echod_concrete::store::StoreRes::GetIfNoneMatch {
                result: Ok(echod_concrete::store::Read::Body(bytes, _)),
            } => {
                match crate::document::spec_decode_workflow(bytes@) {
                    Ok(loaded) => {
                        crate::document::
                            lemma_workflow_decode_success_is_well_formed(
                                bytes@,
                                loaded,
                            );
                    },
                    Err(_) => {},
                }
            },
            _ => {},
        },
        None => match response {
            echod_concrete::store::StoreRes::Get {
                result: Ok(Some((bytes, _))),
            } => {
                match crate::document::spec_decode_workflow(bytes@) {
                    Ok(loaded) => {
                        crate::document::
                            lemma_workflow_decode_success_is_well_formed(
                                bytes@,
                                loaded,
                            );
                    },
                    Err(_) => {},
                }
            },
            _ => {},
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_loaded_schedule_is_uncertified(
    state: S,
    id: Seq<char>,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    ensures
        ({
            let loaded = crate::handler_sched::spec_loaded_schedule(
                state,
                id,
                response,
            );
            loaded.1 is Ok ==>
                !loaded.1->Ok_0.loaded.append_certified
        }),
{
    reveal(crate::handler_sched::spec_loaded_schedule);
    reveal(crate::document::spec_validate_schedule_identity);
    match response {
        echod_concrete::store::StoreRes::Get {
            result: Ok(Some((bytes, _))),
        } => {
            match crate::document::spec_decode_schedule(bytes@) {
                Ok(loaded) => {
                    crate::document::
                        lemma_schedule_decode_success_is_well_formed(
                            bytes@,
                            loaded,
                        );
                },
                Err(_) => {},
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_start_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    target: crate::target::TargetSpec,
    work: crate::handler_docs::WorkSpec,
    firing: Option<crate::handler_docs::FiringSpec>,
    debug: bool,
)
    requires
        core_retained_append_certificates(store, state),
        state.flights_exhausted
            || !state.flights.inflight.contains_key(state.next_flight),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_start(
                state,
                target,
                work,
                firing,
                debug,
            ),
        ),
{
    let next = crate::handler_docs::spec_start(
        state,
        target,
        work,
        firing,
        debug,
    );
    match target {
        crate::target::TargetSpec::Origin(origin) => {
            lemma_cache_get_preserves_append_certificates(
                store,
                state.keys.prefix,
                state.cache,
                origin,
            );
        },
        _ => {},
    }
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::handler_docs::spec_slot_of);
    reveal(crate::handler_docs::spec_empty_slot);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state::spec_flight);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_emit);
    reveal(crate::cache::spec_get);
    reveal(crate::cache::spec_find);
    reveal(core_retained_append_certificates);
    reveal(phase_append_certificates);
    assert(next.keys == state.keys);
    assert forall|i: int|
        0 <= i < next.cache.entries.len() implies
            loaded_append_certificate(
                store,
                next.keys.prefix,
                #[trigger] next.cache.entries[i].cached.loaded,
            ) by {
        if next.cache.entries == state.cache.entries {
            assert(next.cache.entries[i] == state.cache.entries[i]);
        } else {
            match target {
                crate::target::TargetSpec::Origin(origin) => {
                    let got = crate::cache::spec_get(
                        state.cache,
                        origin,
                    );
                    assert(next.cache.entries == got.0.entries);
                    assert(loaded_append_certificate(
                        store,
                        state.keys.prefix,
                        got.0.entries[i].cached.loaded,
                    ));
                },
                _ => {
                    assert(next.cache.entries == state.cache.entries);
                },
            }
        }
    };
    assert forall|fid: u64|
        next.flights.inflight.contains_key(fid) implies
            phase_append_certificates(
                store,
                next.keys.prefix,
                #[trigger] next.flights.inflight[fid].phase,
            ) by {};
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_send_all_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    outbox: Seq<(Seq<char>, crate::types::MessageSpec)>,
)
    requires
        core_retained_append_certificates(store, state),
    ensures
        ({
            let next =
                crate::handler_docs::spec_send_all(state, outbox);
            &&& core_retained_append_certificates(store, next)
            &&& next.keys == state.keys
            &&& next.cache == state.cache
            &&& next.flights == state.flights
        }),
    decreases outbox.len(),
{
    reveal_with_fuel(crate::handler_docs::spec_send_all, 1);
    if outbox.len() > 0 {
        let emitted = crate::state::spec_emit(
            state,
            crate::types::EffectSpec::Send {
                address: outbox[0].0,
                message: outbox[0].1,
            },
        );
        lemma_core_retained_append_certificates_frame(
            store,
            state,
            emitted,
        );
        lemma_send_all_preserves_core_retained_append_certificates(
            store,
            emitted,
            outbox.drop_first(),
        );
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_committed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    flight: crate::handler_docs::FlightSpec,
    done: crate::handler_docs::DoneSpec,
    fired: crate::types::Fired,
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
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_committed(
                state,
                flight,
                done,
                fired,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    let sent = crate::handler_docs::spec_send_all(
        noted,
        done.outbox,
    );
    lemma_core_retained_append_certificates_frame(
        store,
        state,
        noted,
    );
    lemma_send_all_preserves_core_retained_append_certificates(
        store,
        noted,
        done.outbox,
    );
    lemma_note_preserves_core_control_body(
        state,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    lemma_send_all_preserves_core_control_body(noted, done.outbox);
    lemma_note_preserves_retained_provenance(
        state,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    lemma_send_all_preserves_retained_provenance(
        noted,
        done.outbox,
    );
    lemma_send_all_preserves_flights(noted, done.outbox);
    lemma_send_all_preserves_keys(noted, done.outbox);
    let staged = match flight.work {
        crate::handler_docs::WorkSpec::Request {
            id,
            kind,
            corr,
            action_kind,
            ..
        } => crate::state::spec_emit(
            sent,
            crate::types::EffectSpec::Reply {
                id,
                response: match done.response {
                    Some(response) =>
                        Ok(crate::types::AnswerSpec::Step {
                            kind,
                            corr,
                            action_kind,
                            response,
                            why: done.why,
                        }),
                    None => Err("no answer"@),
                },
            },
        ),
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
    assert(staged.keys.prefix == sent.keys.prefix
        && staged.cache.entries == sent.cache.entries
        && staged.flights.inflight == sent.flights.inflight) by {
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
    };
    lemma_core_retained_append_certificates_frame(
        store,
        sent,
        staged,
    );
    match flight.work {
        crate::handler_docs::WorkSpec::Request {
            id,
            kind,
            corr,
            action_kind,
            ..
        } => {
            let response = match done.response {
                Some(response) =>
                    Ok(crate::types::AnswerSpec::Step {
                        kind,
                        corr,
                        action_kind,
                        response,
                        why: done.why,
                    }),
                None => Err("no answer"@),
            };
            lemma_emit_reply_preserves_core_control_body(
                sent,
                id,
                response,
            );
            assert(retained_commit_provenance(staged)) by {
                reveal(crate::state::spec_emit);
                reveal(retained_commit_provenance);
            };
        },
        crate::handler_docs::WorkSpec::Sweep { .. } => {
            let swept = crate::state::spec_note(
                sent,
                crate::types::NoteSpec::Sweep(
                    if done.did {
                        crate::types::SweepOutcome::Fired
                    } else {
                        crate::types::SweepOutcome::Idle
                    },
                ),
            );
            lemma_note_preserves_core_control_body(
                sent,
                crate::types::NoteSpec::Sweep(
                    if done.did {
                        crate::types::SweepOutcome::Fired
                    } else {
                        crate::types::SweepOutcome::Idle
                    },
                ),
            );
            lemma_note_preserves_core_control_body(
                swept,
                crate::types::NoteSpec::SweepEnd {
                    flight: flight.id,
                    committed: true,
                },
            );
            assert(retained_commit_provenance(staged)) by {
                reveal(crate::state::spec_note);
                reveal(retained_commit_provenance);
            };
        },
        crate::handler_docs::WorkSpec::Fire { .. } => {},
    }
    assert(staged.keys.prefix == state.keys.prefix
        && staged.cache.entries == state.cache.entries
        && staged.flights.inflight == state.flights.inflight) by {
        assert(noted.cache.entries == state.cache.entries) by {
            reveal(crate::state::spec_note);
        };
    };
    assert(production_core_control_body(staged)) by {
        reveal(crate::handler_docs::spec_send_all);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
        reveal(pending_store_effects_are_exact);
    };
    assert(retained_commit_provenance(staged)) by {
        reveal(crate::handler_docs::spec_send_all);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(staged)) by {
        reveal(crate::handler_docs::spec_send_all);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_lane_unowned(
            state.flights,
            crate::target::spec_name(flight.target),
            flight.id,
        );
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_secondary_lane_unowned(
            state,
            crate::target::spec_name(flight.target),
            flight.id,
        );
    assert(crate::global_store_lane::lane_has_no_active_flight(
        staged.flights,
        crate::target::spec_name(flight.target),
    ));
    assert(crate::global_store_lane::lane_has_no_secondary_flight_owner(
        staged.flights,
        crate::target::spec_name(flight.target),
    )) by {
        reveal(
            crate::global_store_lane::
                lane_has_no_secondary_flight_owner,
        );
    };
    lemma_finish_preserves_core_retained_append_certificates(
        store,
        staged,
        crate::handler_docs::FlightSpec {
            idle: !done.did,
            ..flight
        },
        Ok(fired),
    );
    reveal(crate::handler_docs::spec_committed);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fail_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    flight: crate::handler_docs::FlightSpec,
    error: Seq<char>,
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
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_fail(
                state,
                flight,
                error,
            ),
        ),
{
    reveal(crate::global_store_control::detached_flight_control);
    let staged = match flight.work {
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
    assert(staged.keys.prefix == state.keys.prefix
        && staged.cache.entries == state.cache.entries
        && staged.flights.inflight == state.flights.inflight) by {
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
    };
    lemma_core_retained_append_certificates_frame(
        store,
        state,
        staged,
    );
    assert(production_core_control_body(staged)) by {
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
        reveal(pending_store_effects_are_exact);
    };
    assert(retained_commit_provenance(staged)) by {
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(staged)) by {
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_lane_unowned(
            state.flights,
            crate::target::spec_name(flight.target),
            flight.id,
        );
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_secondary_lane_unowned(
            state,
            crate::target::spec_name(flight.target),
            flight.id,
        );
    assert(crate::global_store_lane::lane_has_no_active_flight(
        staged.flights,
        crate::target::spec_name(flight.target),
    ));
    assert(crate::global_store_lane::lane_has_no_secondary_flight_owner(
        staged.flights,
        crate::target::spec_name(flight.target),
    )) by {
        reveal(
            crate::global_store_lane::
                lane_has_no_secondary_flight_owner,
        );
    };
    lemma_finish_preserves_core_retained_append_certificates(
        store,
        staged,
        flight,
        Err(error),
    );
    reveal(crate::handler_docs::spec_fail);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_forget_failed_origin_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    flight: crate::handler_docs::FlightSpec,
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
    ensures
        ({
            let forgotten = match flight.target {
                crate::target::TargetSpec::Origin(origin) =>
                    crate::state::spec_forget_origin(state, origin),
                _ => state,
            };
            &&& crate::global_store_control::detached_flight_control(
                forgotten,
                flight.id,
            )
            &&& crate::global_store_lane::detached_flight_owns_primary(
                forgotten,
                flight,
            )
            &&& retained_commit_provenance(forgotten)
            &&& cache_identity_provenance(forgotten)
            &&& core_retained_append_certificates(store, forgotten)
        }),
{
    let forgotten = match flight.target {
        crate::target::TargetSpec::Origin(origin) =>
            crate::state::spec_forget_origin(state, origin),
        _ => state,
    };
    match flight.target {
        crate::target::TargetSpec::Origin(origin) => {
            reveal(core_retained_append_certificates);
            lemma_cache_remove_preserves_append_certificates(
                store,
                state.keys.prefix,
                state.cache,
                origin,
            );
            lemma_cache_remove_preserves_identity(state.cache, origin);
            lemma_cache_remove_preserves_unique_origins(
                state.cache,
                origin,
            );
        },
        _ => {},
    }
    assert(core_retained_append_certificates(store, forgotten)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(core_retained_append_certificates);
    };
    assert(crate::global_store_control::detached_flight_control(
        forgotten,
        flight.id,
    )) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::global_store_control::detached_flight_control);
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        forgotten,
        flight,
    )) by {
        reveal(crate::state::spec_forget_origin);
        reveal(
            crate::global_store_lane::detached_flight_owns_primary,
        );
    };
    assert(retained_commit_provenance(forgotten)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(forgotten)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(cache_identity_provenance);
    };
}

pub(crate) proof fn lemma_raced_commit_preserves_core_retained_append_certificates(
    store: StoreV,
    forgotten: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        crate::global_store_control::detached_flight_control(
            forgotten,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            forgotten,
            flight,
        ),
        retained_commit_provenance(forgotten),
        cache_identity_provenance(forgotten),
        core_retained_append_certificates(store, forgotten),
    ensures
        ({
            let raced = crate::state::spec_note(
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
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_retry(raced, flight),
            )
        }),
{
    let raced = crate::state::spec_note(
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
    assert(core_retained_append_certificates(store, raced)) by {
        reveal(crate::state::spec_note);
        reveal(core_retained_append_certificates);
    };
    assert(retained_commit_provenance(raced)) by {
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(raced)) by {
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    assert(crate::global_store_control::detached_flight_control(
        raced,
        flight.id,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_control::detached_flight_control);
    };
    let retried = crate::handler_docs::FlightSpec {
        attempt: flight.attempt.wrapping_add(1),
        ..flight
    };
    if retried.attempt > raced.flights.max_retries {
        let exhausted = crate::state::spec_note(
            raced,
            crate::types::NoteSpec::Commit(
                crate::types::CommitOutcome::Exhausted,
            ),
        );
        let what = match retried.target {
            crate::target::TargetSpec::Origin(_) => "document"@,
            crate::target::TargetSpec::Schedule(_) => "schedule"@,
        };
        assert(retained_commit_provenance(exhausted)) by {
            reveal(crate::state::spec_note);
            reveal(retained_commit_provenance);
        };
        assert(cache_identity_provenance(exhausted)) by {
            reveal(crate::state::spec_note);
            reveal(cache_identity_provenance);
        };
        assert(core_retained_append_certificates(store, exhausted)) by {
            reveal(crate::state::spec_note);
            reveal(core_retained_append_certificates);
        };
        assert(crate::global_store_control::detached_flight_control(
            exhausted,
            retried.id,
        )) by {
            reveal(crate::state::spec_note);
            reveal(crate::global_store_control::detached_flight_control);
        };
        assert(crate::global_store_lane::detached_flight_owns_primary(
            exhausted,
            retried,
        )) by {
            reveal(crate::state::spec_note);
            reveal(
                crate::global_store_lane::detached_flight_owns_primary,
            );
        };
        lemma_fail_preserves_core_retained_append_certificates(
            store,
            exhausted,
            retried,
            "too many races on the "@ + what,
        );
    } else {
        lemma_begin_preserves_core_retained_append_certificates(
            store,
            raced,
            retried,
        );
    }
    reveal(crate::handler_docs::spec_retry);
}

pub(crate) proof fn lemma_nonraced_commit_failure_preserves_core_retained_append_certificates(
    store: StoreV,
    forgotten: S,
    flight: crate::handler_docs::FlightSpec,
    error: echod_concrete::store::StoreErrorSpec,
)
    requires
        !(error is PreconditionFailed),
        crate::global_store_control::detached_flight_control(
            forgotten,
            flight.id,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            forgotten,
            flight,
        ),
        retained_commit_provenance(forgotten),
        cache_identity_provenance(forgotten),
        core_retained_append_certificates(store, forgotten),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_fail(
                crate::state::spec_note(
                    forgotten,
                    crate::types::NoteSpec::Commit(
                        crate::types::CommitOutcome::Failed,
                    ),
                ),
                flight,
                crate::types::spec_error_text(error),
            ),
        ),
{
    let failed = crate::state::spec_note(
        forgotten,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Failed,
        ),
    );
    assert(retained_commit_provenance(failed)) by {
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(failed)) by {
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    assert(core_retained_append_certificates(store, failed)) by {
        reveal(crate::state::spec_note);
        reveal(core_retained_append_certificates);
    };
    assert(crate::global_store_control::detached_flight_control(
        failed,
        flight.id,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_control::detached_flight_control);
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        failed,
        flight,
    )) by {
        reveal(crate::state::spec_note);
        reveal(
            crate::global_store_lane::detached_flight_owns_primary,
        );
    };
    lemma_fail_preserves_core_retained_append_certificates(
        store,
        failed,
        flight,
        crate::types::spec_error_text(error),
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_commit_failed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    flight: crate::handler_docs::FlightSpec,
    error: echod_concrete::store::StoreErrorSpec,
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
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_commit_failed(
                state,
                flight,
                error,
            ),
        ),
{
    let forgotten = match flight.target {
        crate::target::TargetSpec::Origin(origin) =>
            crate::state::spec_forget_origin(state, origin),
        _ => state,
    };
    lemma_forget_failed_origin_preserves_core_retained_append_certificates(
        store,
        state,
        flight,
    );
    match error {
        echod_concrete::store::StoreErrorSpec::PreconditionFailed => {
            lemma_raced_commit_preserves_core_retained_append_certificates(
                store,
                forgotten,
                flight,
            );
        },
        _ => {
            lemma_nonraced_commit_failure_preserves_core_retained_append_certificates(
                store,
                forgotten,
                flight,
                error,
            );
        },
    }
    reveal(crate::handler_docs::spec_commit_failed);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_op_exhausted_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_op_exhausted(state, flight),
        ),
{
    let next =
        crate::handler_docs::spec_op_exhausted(state, flight);
    assert(next.keys.prefix == state.keys.prefix) by {
        reveal(crate::handler_docs::spec_op_exhausted);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(crate::handler_timers::spec_timer_op_exhausted);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
    };
    assert(next.cache.entries == state.cache.entries) by {
        reveal(crate::handler_docs::spec_op_exhausted);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(crate::handler_timers::spec_timer_op_exhausted);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
    };
    assert(next.flights.inflight == state.flights.inflight) by {
        reveal(crate::handler_docs::spec_op_exhausted);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(crate::handler_timers::spec_timer_op_exhausted);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
    };
    lemma_core_retained_append_certificates_frame(
        store,
        state,
        next,
    );
}

pub(crate) proof fn lemma_listing_failed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    error: echod_concrete::store::StoreErrorSpec,
    now: u64,
)
    requires
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_timers::spec_listing_failed(
                state,
                error,
                now,
            ),
        ),
{
    let next = crate::handler_timers::spec_listing_failed(
        state,
        error,
        now,
    );
    assert(next.keys.prefix == state.keys.prefix) by {
        reveal(crate::handler_timers::spec_listing_failed);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_note);
    };
    assert(next.cache.entries == state.cache.entries) by {
        reveal(crate::handler_timers::spec_listing_failed);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_note);
    };
    assert(next.flights.inflight == state.flights.inflight) by {
        reveal(crate::handler_timers::spec_listing_failed);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_note);
    };
    lemma_core_retained_append_certificates_frame(store, state, next);
}

pub(crate) proof fn lemma_reloaded_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    horizon: u64,
    loaded: usize,
    now: u64,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_timers::spec_reloaded(
                state,
                horizon,
                loaded,
                now,
            ),
        ),
{
    reveal(crate::handler_timers::spec_reloaded);
    let updated = crate::handler_timers::spec_with_timers(
        state,
        crate::state_timers::TimersSpec {
            loaded_through: Some(horizon),
            closed_through: Some(
                crate::keys::spec_bucket_of(
                    now,
                    state.keys.bucket_ms,
                ).saturating_sub(state.keys.bucket_ms),
            ),
            reload_pending: false,
            ..state.timers
        },
    );
    lemma_core_retained_append_certificates_frame(store, state, updated);
    lemma_timers_field_update_preserves_core_control_body(
        state,
        updated.timers,
    );
    let listed = crate::state::spec_note(
        updated,
        crate::types::NoteSpec::TimerListing { ok: true },
    );
    lemma_core_retained_append_certificates_frame(store, updated, listed);
    lemma_note_preserves_core_control_body(
        updated,
        crate::types::NoteSpec::TimerListing { ok: true },
    );
    let noted = crate::state::spec_note(
        listed,
        crate::types::NoteSpec::TimersLoaded {
            deadlines: loaded,
            wheel: listed.timers.wheel.armed.len() as usize,
            epoch: listed.node.core.epoch as u64,
        },
    );
    lemma_core_retained_append_certificates_frame(store, listed, noted);
    lemma_note_preserves_core_control_body(
        listed,
        crate::types::NoteSpec::TimersLoaded {
            deadlines: loaded,
            wheel: listed.timers.wheel.armed.len() as usize,
            epoch: listed.node.core.epoch as u64,
        },
    );
    lemma_timers_run_preserves_core_retained_append_certificates(
        store,
        noted,
        now,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_prefixes_listed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    horizon: u64,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_timers::spec_prefixes_listed(
                state,
                horizon,
                now,
                response,
            ),
        ),
{
    reveal(crate::handler_timers::spec_prefixes_listed);
    match response {
        echod_concrete::store::StoreRes::ListPrefixes {
            result: Ok(prefixes),
        } => {
            lemma_list_buckets_preserves_core_retained_append_certificates(
                store,
                state,
                prefixes.deep_view(),
                horizon,
                Map::empty(),
            );
            lemma_list_buckets_preserves_core_control_body(
                state,
                prefixes.deep_view(),
                horizon,
                Map::empty(),
            );
            let listed = crate::handler_timers::spec_list_buckets(
                state,
                prefixes.deep_view(),
                horizon,
                Map::empty(),
            );
            if listed.1 =~= Map::<u64, u64>::empty() {
                lemma_reloaded_preserves_core_retained_append_certificates(
                    store,
                    listed.0,
                    horizon,
                    0,
                    now,
                );
            } else {
                let next = crate::handler_timers::spec_with_timers(
                    listed.0,
                    crate::state_timers::TimersSpec {
                        listing: Some(
                            crate::state_timers::ListingSpec::Buckets {
                                pending: listed.1,
                                horizon,
                                loaded: 0,
                                failed: None,
                            },
                        ),
                        ..listed.0.timers
                    },
                );
                lemma_core_retained_append_certificates_frame(
                    store,
                    listed.0,
                    next,
                );
            }
        },
        echod_concrete::store::StoreRes::ListPrefixes {
            result: Err(error),
        } => {
            lemma_listing_failed_preserves_core_retained_append_certificates(
                store,
                state,
                error.deep_view(),
                now,
            );
        },
        _ => {
            lemma_listing_failed_preserves_core_retained_append_certificates(
                store,
                state,
                crate::types::spec_unexpected(),
                now,
            );
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_bucket_listed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    pending: Map<u64, u64>,
    horizon: u64,
    loaded: usize,
    failed: Option<echod_concrete::store::StoreErrorSpec>,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_timers::spec_bucket_listed(
                state,
                pending,
                horizon,
                loaded,
                failed,
                now,
                response,
            ),
        ),
{
    reveal(crate::handler_timers::spec_bucket_listed);
    let staged = match response {
        echod_concrete::store::StoreRes::List {
            result: Ok(keys),
        } => {
            lemma_take_bucket_preserves_core_retained_append_certificates(
                store,
                state,
                keys.deep_view(),
                0,
            );
            lemma_take_bucket_preserves_core_control_body(
                state,
                keys.deep_view(),
                0,
            );
            crate::handler_timers::spec_take_bucket(
                state,
                keys.deep_view(),
                0,
            ).0
        },
        _ => state,
    };
    let result = match response {
        echod_concrete::store::StoreRes::List {
            result: Ok(keys),
        } => crate::handler_timers::spec_take_bucket(
            state,
            keys.deep_view(),
            0,
        ),
        _ => (state, 0),
    };
    let final_loaded = match response {
        echod_concrete::store::StoreRes::List { result: Ok(_) } =>
            loaded.saturating_add(result.1 as usize),
        _ => loaded,
    };
    let final_failed = match response {
        echod_concrete::store::StoreRes::List { result: Ok(_) } =>
            failed,
        echod_concrete::store::StoreRes::List {
            result: Err(error),
        } => Some(error.deep_view()),
        _ => Some(crate::types::spec_unexpected()),
    };
    if !(pending =~= Map::<u64, u64>::empty()) {
        let next = crate::handler_timers::spec_with_timers(
            staged,
            crate::state_timers::TimersSpec {
                listing: Some(
                    crate::state_timers::ListingSpec::Buckets {
                        pending,
                        horizon,
                        loaded: final_loaded,
                        failed: final_failed,
                    },
                ),
                ..staged.timers
            },
        );
        lemma_core_retained_append_certificates_frame(
            store,
            staged,
            next,
        );
    } else {
        match final_failed {
            Some(error) => {
                lemma_listing_failed_preserves_core_retained_append_certificates(
                    store,
                    staged,
                    error,
                    now,
                );
            },
            None => {
                lemma_reloaded_preserves_core_retained_append_certificates(
                    store,
                    staged,
                    horizon,
                    final_loaded,
                    now,
                );
            },
        }
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_extended_or_relisted_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    bucket: u64,
    now: u64,
    response: echod_concrete::store::StoreRes,
    relist: bool,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            if relist {
                crate::handler_timers::spec_relisted(
                    state,
                    bucket,
                    now,
                    response,
                )
            } else {
                crate::handler_timers::spec_extended(
                    state,
                    bucket,
                    now,
                    response,
                )
            },
        ),
{
    if relist {
        reveal(crate::handler_timers::spec_relisted);
    } else {
        reveal(crate::handler_timers::spec_extended);
    }
    match response {
        echod_concrete::store::StoreRes::List {
            result: Ok(keys),
        } => {
            lemma_take_bucket_preserves_core_retained_append_certificates(
                store,
                state,
                keys.deep_view(),
                0,
            );
            lemma_take_bucket_preserves_core_control_body(
                state,
                keys.deep_view(),
                0,
            );
            let taken = crate::handler_timers::spec_take_bucket(
                state,
                keys.deep_view(),
                0,
            );
            let loaded = crate::state::spec_note(
                taken.0,
                crate::types::NoteSpec::BucketLoaded {
                    bucket,
                    deadlines: taken.1 as usize,
                },
            );
            lemma_core_retained_append_certificates_frame(
                store,
                taken.0,
                loaded,
            );
            lemma_note_preserves_core_control_body(
                taken.0,
                crate::types::NoteSpec::BucketLoaded {
                    bucket,
                    deadlines: taken.1 as usize,
                },
            );
            let noted = crate::state::spec_note(
                loaded,
                crate::types::NoteSpec::TimerListing { ok: true },
            );
            lemma_core_retained_append_certificates_frame(
                store,
                loaded,
                noted,
            );
            lemma_note_preserves_core_control_body(
                loaded,
                crate::types::NoteSpec::TimerListing { ok: true },
            );
            let advanced = crate::handler_timers::spec_with_timers(
                noted,
                if relist {
                    crate::state_timers::TimersSpec {
                        closed_through: Some(bucket),
                        ..noted.timers
                    }
                } else {
                    crate::state_timers::TimersSpec {
                        loaded_through: Some(bucket),
                        ..noted.timers
                    }
                },
            );
            lemma_core_retained_append_certificates_frame(
                store,
                noted,
                advanced,
            );
            lemma_timers_field_update_preserves_core_control_body(
                noted,
                advanced.timers,
            );
            lemma_timers_run_preserves_core_retained_append_certificates(
                store,
                advanced,
                now,
            );
        },
        echod_concrete::store::StoreRes::List {
            result: Err(error),
        } => {
            lemma_listing_failed_preserves_core_retained_append_certificates(
                store,
                state,
                error.deep_view(),
                now,
            );
        },
        _ => {
            lemma_listing_failed_preserves_core_retained_append_certificates(
                store,
                state,
                crate::types::spec_unexpected(),
                now,
            );
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_timers_completed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_timers::spec_timers_completed(
                state,
                op,
                response,
            ),
        ),
{
    reveal(crate::handler_timers::spec_timers_completed);
    match state.timers.listing {
        Some(listing) if listing.expects(op) => {
            let cleared = crate::handler_timers::spec_with_timers(
                state,
                crate::state_timers::TimersSpec {
                    listing: None,
                    ..state.timers
                },
            );
            lemma_core_retained_append_certificates_frame(
                store,
                state,
                cleared,
            );
            lemma_timers_field_update_preserves_core_control_body(
                state,
                cleared.timers,
            );
            let now = crate::state::spec_now(cleared);
            match listing {
                crate::state_timers::ListingSpec::Prefixes {
                    horizon,
                    ..
                } => {
                    lemma_prefixes_listed_preserves_core_retained_append_certificates(
                        store,
                        cleared,
                        horizon,
                        now,
                        response,
                    );
                },
                crate::state_timers::ListingSpec::Buckets {
                    pending,
                    horizon,
                    loaded,
                    failed,
                } => {
                    lemma_bucket_listed_preserves_core_retained_append_certificates(
                        store,
                        cleared,
                        pending.remove(op),
                        horizon,
                        loaded,
                        failed,
                        now,
                        response,
                    );
                },
                crate::state_timers::ListingSpec::Extend {
                    bucket,
                    ..
                } => {
                    lemma_extended_or_relisted_preserves_core_retained_append_certificates(
                        store,
                        cleared,
                        bucket,
                        now,
                        response,
                        false,
                    );
                },
                crate::state_timers::ListingSpec::Relist {
                    bucket,
                    ..
                } => {
                    lemma_extended_or_relisted_preserves_core_retained_append_certificates(
                        store,
                        cleared,
                        bucket,
                        now,
                        response,
                        true,
                    );
                },
            }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_read_configuration_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    nodes: crate::state_node::RosterSpec,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_read_configuration(state, nodes),
        ),
{
    reveal(crate::handler_node::spec_read_configuration);
    let request = StoreReqSpec::Get {
        key: crate::keys::spec_members_key(state.keys.prefix),
    };
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
            let next = crate::handler_node::spec_with_members(
                issued.0,
                crate::state_node::MembersSpec {
                    refresh: Some(
                        crate::state_node::RefreshSpec::Config {
                            op,
                            nodes,
                        },
                    ),
                    ..issued.0.node.members
                },
            );
            lemma_core_retained_append_certificates_frame(
                store,
                issued.0,
                next,
            );
        },
        None => {
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                issued.0,
                Err(crate::types::spec_exhausted()),
            );
        },
    }
}

pub(crate) proof fn lemma_write_members_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    configuration: crate::state_node::ConfigurationSpec,
    etag: Option<echod_concrete::store::EtagSpec>,
    nodes: crate::state_node::RosterSpec,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_write_members(
                state,
                configuration,
                etag,
                nodes,
            ),
        ),
{
    reveal(crate::handler_node::spec_write_members);
    let live = crate::state_node::spec_roster_ids(nodes.entries);
    if live != configuration.members {
        let next_config = crate::state_node::ConfigurationSpec {
            epoch: configuration.epoch.saturating_add(1),
            members: live,
        };
        let request = match etag {
            Some(tag) => StoreReqSpec::PutIfMatch {
                key: crate::keys::spec_members_key(state.keys.prefix),
                body: crate::state_node::spec_configuration_bytes(next_config),
                etag: tag,
            },
            None => StoreReqSpec::PutIfNoneMatch {
                key: crate::keys::spec_members_key(state.keys.prefix),
                body: crate::state_node::spec_configuration_bytes(next_config),
            },
        };
        lemma_members_key_is_not_document_or_timer(state.keys.prefix);
        assert(certificate_matches_request(
            state.keys.prefix,
            state.keys.bucket_ms,
            request,
            StoreEffectCertificateV::Other,
        )) by {
            reveal(certificate_matches_request);
        };
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
                let next = crate::handler_node::spec_with_members(
                    issued.0,
                    crate::state_node::MembersSpec {
                        refresh: Some(
                            crate::state_node::RefreshSpec::Writing {
                                op,
                                next: next_config,
                            },
                        ),
                        ..issued.0.node.members
                    },
                );
                lemma_core_retained_append_certificates_frame(
                    store,
                    issued.0,
                    next,
                );
            },
            None => {
                lemma_refresh_ended_preserves_core_retained_append_certificates(
                    store,
                    issued.0,
                    Err(crate::types::spec_exhausted()),
                );
            },
        }
    } else {
        lemma_refresh_ended_preserves_core_retained_append_certificates(
            store,
            state,
            Ok(()),
        );
    }
}

pub(crate) proof fn lemma_take_on_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    configuration: crate::state_node::ConfigurationSpec,
    etag: Option<echod_concrete::store::EtagSpec>,
    nodes: crate::state_node::RosterSpec,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_take_on(
                state,
                configuration,
                etag,
                nodes,
            ),
        ),
{
    reveal(crate::handler_node::spec_take_on);
    let changed = !(state.node.core.read_any
        && state.node.core.epoch == configuration.epoch as nat);
    let noted = if changed {
        let next = crate::state::spec_note(
            state,
            crate::types::NoteSpec::ConfigurationRead {
                epoch: configuration.epoch,
                members: configuration.members,
            },
        );
        lemma_core_retained_append_certificates_frame(
            store,
            state,
            next,
        );
        lemma_note_preserves_core_control_body(
            state,
            crate::types::NoteSpec::ConfigurationRead {
                epoch: configuration.epoch,
                members: configuration.members,
            },
        );
        next
    } else {
        state
    };
    let configured = S {
        node: crate::state_node::NodeSpec {
            core: crate::verified::node_spec::spec_read_config(
                noted.node.core,
                crate::state::spec_now(noted) as nat,
                configuration.epoch as nat,
                configuration.members,
            ),
            members: crate::state_node::MembersSpec {
                nodes,
                etag,
                ..noted.node.members
            },
            ..noted.node
        },
        ..noted
    };
    lemma_core_retained_append_certificates_frame(
        store,
        noted,
        configured,
    );
    assert(production_core_control_body(configured)) by {
        reveal(production_core_control_body);
    };
    let reloading = if changed {
        let changed_note = crate::state::spec_note(
            configured,
            crate::types::NoteSpec::ConfigurationChange,
        );
        lemma_core_retained_append_certificates_frame(
            store,
            configured,
            changed_note,
        );
        lemma_note_preserves_core_control_body(
            configured,
            crate::types::NoteSpec::ConfigurationChange,
        );
        let next = crate::handler_timers::spec_timers_membership_changed(
            changed_note,
        );
        reveal(crate::handler_timers::spec_timers_membership_changed);
        lemma_core_retained_append_certificates_frame(
            store,
            changed_note,
            next,
        );
        lemma_timers_field_update_preserves_core_control_body(
            changed_note,
            next.timers,
        );
        next
    } else {
        configured
    };
    lemma_write_members_preserves_core_retained_append_certificates(
        store,
        reloading,
        configuration,
        etag,
        nodes,
    );
}

pub(crate) proof fn lemma_members_read_one_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    pending: Map<u64, bool>,
    nodes: crate::state_node::RosterSpec,
    now: u64,
    failed: Option<echod_concrete::store::StoreErrorSpec>,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_read_one(
                state,
                pending,
                nodes,
                now,
                failed,
                response,
            ),
        ),
{
    reveal(crate::handler_node::spec_read_one);
    reveal(crate::handler_node::spec_read_one_outcome);
    let staged = match response {
        echod_concrete::store::StoreRes::Get {
            result: Ok(Some((bytes, _))),
        } => match crate::state_node::spec_parse_announcement(bytes@) {
            Some(announcement) => {
                let fleet_at = if state.node.fleet_at > announcement.at {
                    state.node.fleet_at
                } else {
                    announcement.at
                };
                let observed = S {
                    node: crate::state_node::NodeSpec {
                        fleet_at,
                        ..state.node
                    },
                    ..state
                };
                lemma_core_retained_append_certificates_frame(
                    store,
                    state,
                    observed,
                );
                assert(production_core_control_body(observed)) by {
                    reveal(production_core_control_body);
                };
                if announcement.at.saturating_add(
                    observed.node.members.ttl,
                ) >= now {
                    observed
                } else if announcement.at.saturating_add(
                    (2 as u64).saturating_mul(
                        observed.node.members.ttl,
                    ),
                ) < now {
                    let request = StoreReqSpec::Del {
                        key: crate::keys::spec_node_key(
                            observed.keys.prefix,
                            announcement.id,
                        ),
                    };
                    lemma_node_key_is_not_document_or_timer(
                        observed.keys.prefix,
                        announcement.id,
                    );
                    assert(certificate_matches_request(
                        observed.keys.prefix,
                        observed.keys.bucket_ms,
                        request,
                        StoreEffectCertificateV::Other,
                    )) by {
                        reveal(certificate_matches_request);
                    };
                    lemma_nonflight_store_preserves_core_retained_append_certificates(
                        store,
                        observed,
                        request,
                        Owner::Ignored,
                    );
                    lemma_nonflight_store_issue_preserves_core_control_body(
                        observed,
                        request,
                        Owner::Ignored,
                    );
                    crate::state::spec_store(
                        observed,
                        request,
                        Owner::Ignored,
                    ).0
                } else {
                    observed
                }
            },
            None => state,
        },
        _ => state,
    };
    assert(core_retained_append_certificates(store, staged));
    assert(production_core_control_body(staged)) by {
        lemma_members_read_one_preserves_core_control_body(
            state,
            pending,
            nodes,
            now,
            failed,
            response,
        );
    };
    let result = crate::handler_node::spec_read_one_outcome(
        state,
        nodes,
        now,
        failed,
        response,
    );
    assert(result.0 == staged);
    if !(pending =~= Map::<u64, bool>::empty()) {
        let next = crate::handler_node::spec_with_members(
            result.0,
            crate::state_node::MembersSpec {
                refresh: Some(
                    crate::state_node::RefreshSpec::Reading {
                        pending,
                        nodes: result.1,
                        now,
                        failed: result.2,
                    },
                ),
                ..result.0.node.members
            },
        );
        lemma_core_retained_append_certificates_frame(
            store,
            result.0,
            next,
        );
    } else {
        match result.2 {
            Some(error) => {
                lemma_refresh_ended_preserves_core_retained_append_certificates(
                    store,
                    result.0,
                    Err(error),
                );
            },
            None => {
                lemma_read_configuration_preserves_core_retained_append_certificates(
                    store,
                    result.0,
                    result.1,
                );
            },
        }
    }
}

pub(crate) proof fn lemma_members_announced_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_announced(state, now, response),
        ),
{
    reveal(crate::handler_node::spec_announced);
    match response {
        echod_concrete::store::StoreRes::Put { result: Ok(()) } => {
            let request = StoreReqSpec::List {
                prefix: crate::keys::spec_node_prefix(state.keys.prefix),
                max_keys: 10_000,
            };
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
                    let next = crate::handler_node::spec_with_members(
                        issued.0,
                        crate::state_node::MembersSpec {
                            refresh: Some(
                                crate::state_node::RefreshSpec::Listing {
                                    op,
                                    now,
                                },
                            ),
                            ..issued.0.node.members
                        },
                    );
                    lemma_core_retained_append_certificates_frame(
                        store,
                        issued.0,
                        next,
                    );
                },
                None => {
                    lemma_refresh_ended_preserves_core_retained_append_certificates(
                        store,
                        issued.0,
                        Err(crate::types::spec_exhausted()),
                    );
                },
            }
        },
        echod_concrete::store::StoreRes::Put {
            result: Err(error),
        } => {
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                state,
                Err(error.deep_view()),
            );
        },
        _ => {
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                state,
                Err(crate::types::spec_unexpected()),
            );
        },
    }
}

pub(crate) proof fn lemma_members_listed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_listed(state, now, response),
        ),
{
    reveal(crate::handler_node::spec_listed);
    match response {
        echod_concrete::store::StoreRes::List {
            result: Ok(keys),
        } => {
            let nodes = crate::state_node::RosterSpec {
                entries: crate::state_node::spec_roster_insert(
                    Seq::empty(),
                    state.node.members.me.id,
                    state.node.members.me,
                ),
            };
            lemma_read_nodes_preserves_core_retained_append_certificates(
                store,
                state,
                keys.deep_view(),
                Map::empty(),
            );
            lemma_read_nodes_preserves_core_control_body(
                state,
                keys.deep_view(),
                Map::empty(),
            );
            let read = crate::handler_node::spec_read_nodes(
                state,
                keys.deep_view(),
                Map::empty(),
            );
            if read.1 =~= Map::<u64, bool>::empty() {
                lemma_read_configuration_preserves_core_retained_append_certificates(
                    store,
                    read.0,
                    nodes,
                );
            } else {
                let next = crate::handler_node::spec_with_members(
                    read.0,
                    crate::state_node::MembersSpec {
                        refresh: Some(
                            crate::state_node::RefreshSpec::Reading {
                                pending: read.1,
                                nodes,
                                now,
                                failed: None,
                            },
                        ),
                        ..read.0.node.members
                    },
                );
                lemma_core_retained_append_certificates_frame(
                    store,
                    read.0,
                    next,
                );
            }
        },
        echod_concrete::store::StoreRes::List {
            result: Err(error),
        } => {
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                state,
                Err(error.deep_view()),
            );
        },
        _ => {
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                state,
                Err(crate::types::spec_unexpected()),
            );
        },
    }
}

pub(crate) proof fn lemma_members_configured_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    nodes: crate::state_node::RosterSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_configured(state, nodes, response),
        ),
{
    reveal(crate::handler_node::spec_configured);
    match response {
        echod_concrete::store::StoreRes::Get {
            result: Ok(read),
        } => {
            let parsed = match read {
                Some((bytes, etag)) => (
                    crate::state_node::spec_parse_configuration(bytes@),
                    Some(etag.deep_view()),
                ),
                None => (
                    crate::state_node::ConfigurationSpec {
                        epoch: 0,
                        members: Seq::empty(),
                    },
                    None,
                ),
            };
            lemma_take_on_preserves_core_retained_append_certificates(
                store,
                state,
                parsed.0,
                parsed.1,
                nodes,
            );
        },
        echod_concrete::store::StoreRes::Get {
            result: Err(error),
        } => {
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                state,
                Err(error.deep_view()),
            );
        },
        _ => {
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                state,
                Err(crate::types::spec_unexpected()),
            );
        },
    }
}

pub(crate) proof fn lemma_members_written_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    next_config: crate::state_node::ConfigurationSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_written(
                state,
                next_config,
                response,
            ),
        ),
{
    reveal(crate::handler_node::spec_written);
    match response {
        echod_concrete::store::StoreRes::PutIfMatch {
            result: Ok(_),
        }
        | echod_concrete::store::StoreRes::PutIfNoneMatch {
            result: Ok(_),
        } => {
            let written = crate::state::spec_note(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Written,
                ),
            );
            lemma_core_retained_append_certificates_frame(
                store,
                state,
                written,
            );
            lemma_note_preserves_core_control_body(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Written,
                ),
            );
            let noted = crate::state::spec_note(
                written,
                crate::types::NoteSpec::ConfigurationWritten {
                    epoch: next_config.epoch,
                    members: next_config.members,
                },
            );
            lemma_core_retained_append_certificates_frame(
                store,
                written,
                noted,
            );
            lemma_note_preserves_core_control_body(
                written,
                crate::types::NoteSpec::ConfigurationWritten {
                    epoch: next_config.epoch,
                    members: next_config.members,
                },
            );
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                noted,
                Ok(()),
            );
        },
        echod_concrete::store::StoreRes::PutIfMatch {
            result: Err(echod_concrete::store::StoreError::PreconditionFailed),
        }
        | echod_concrete::store::StoreRes::PutIfNoneMatch {
            result: Err(echod_concrete::store::StoreError::PreconditionFailed),
        } => {
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Conflict,
                ),
            );
            lemma_core_retained_append_certificates_frame(
                store,
                state,
                noted,
            );
            lemma_note_preserves_core_control_body(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Conflict,
                ),
            );
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                noted,
                Ok(()),
            );
        },
        echod_concrete::store::StoreRes::PutIfMatch {
            result: Err(error),
        }
        | echod_concrete::store::StoreRes::PutIfNoneMatch {
            result: Err(error),
        } => {
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Failed,
                ),
            );
            lemma_core_retained_append_certificates_frame(
                store,
                state,
                noted,
            );
            lemma_note_preserves_core_control_body(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Failed,
                ),
            );
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                noted,
                Err(error.deep_view()),
            );
        },
        _ => {
            lemma_refresh_ended_preserves_core_retained_append_certificates(
                store,
                state,
                Err(crate::types::spec_unexpected()),
            );
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_members_completed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        core_retained_append_certificates(store, state),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_node::spec_members_completed(
                state,
                op,
                response,
            ),
        ),
{
    reveal(crate::handler_node::spec_members_completed);
    match state.node.members.refresh {
        Some(refresh) if refresh.expects(op) => {
            let cleared = crate::handler_node::spec_with_members(
                state,
                crate::state_node::MembersSpec {
                    refresh: None,
                    ..state.node.members
                },
            );
            lemma_core_retained_append_certificates_frame(
                store,
                state,
                cleared,
            );
            lemma_members_field_update_preserves_core_control_body(
                state,
                cleared.node.members,
            );
            match refresh {
                crate::state_node::RefreshSpec::Announcing {
                    now,
                    ..
                } => {
                    lemma_members_announced_preserves_core_retained_append_certificates(
                        store,
                        cleared,
                        now,
                        response,
                    );
                },
                crate::state_node::RefreshSpec::Listing {
                    now,
                    ..
                } => {
                    lemma_members_listed_preserves_core_retained_append_certificates(
                        store,
                        cleared,
                        now,
                        response,
                    );
                },
                crate::state_node::RefreshSpec::Reading {
                    pending,
                    nodes,
                    now,
                    failed,
                } => {
                    lemma_members_read_one_preserves_core_retained_append_certificates(
                        store,
                        cleared,
                        pending.remove(op),
                        nodes,
                        now,
                        failed,
                        response,
                    );
                },
                crate::state_node::RefreshSpec::Config {
                    nodes,
                    ..
                } => {
                    lemma_members_configured_preserves_core_retained_append_certificates(
                        store,
                        cleared,
                        nodes,
                        response,
                    );
                },
                crate::state_node::RefreshSpec::Writing {
                    next,
                    ..
                } => {
                    lemma_members_written_preserves_core_retained_append_certificates(
                        store,
                        cleared,
                        next,
                        response,
                    );
                },
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_origin_preserves_core_retained_append_certificates(
    detached: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
    certificate: StoreEffectCertificateV,
)
    requires
        production_core_control_body(detached),
        retained_commit_provenance(detached),
        cache_identity_provenance(detached),
        core_retained_append_certificates(store, detached),
        crate::global_store_control::detached_flight_control(
            detached,
            fid,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            detached,
            flight,
        ),
        commit_candidate_provenance(
            detached,
            fid,
            flight.target,
            commit,
        ),
        commit.issued is Some,
        certificate_belongs_to_commit(certificate, commit),
        response_certificate_ready(
            store,
            detached.keys.prefix,
            response,
            certificate,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_answered_origin(
                detached,
                fid,
                flight,
                commit,
                done,
                response,
            ),
        ),
{
    lemma_answered_commit_advance_preserves_core_retained_append_certificates(
        detached,
        fid,
        commit,
        response,
        store,
        certificate,
    );
    lemma_detached_commit_advance_preserves_retained_provenance(
        detached,
        fid,
        flight.target,
        commit,
        response,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        detached,
        fid,
        commit,
        Some(response),
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
                reveal(crate::handler_docs::spec_answered);
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
                    phase:
                        crate::handler_docs::PhaseSpec::Origin {
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
                    detached,
                    fid,
                    commit,
                    Some(response),
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
                    detached,
                    fid,
                    commit,
                    Some(response),
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
                    detached,
                    fid,
                    commit,
                    Some(response),
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
                    detached,
                    fid,
                    commit,
                    Some(response),
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
    reveal(crate::handler_docs::spec_answered_origin);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_schedule_preserves_core_retained_append_certificates(
    detached: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    done: crate::handler_docs::DoneSpec,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
    certificate: StoreEffectCertificateV,
)
    requires
        production_core_control_body(detached),
        retained_commit_provenance(detached),
        cache_identity_provenance(detached),
        core_retained_append_certificates(store, detached),
        crate::global_store_control::detached_flight_control(
            detached,
            fid,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            detached,
            flight,
        ),
        commit_candidate_provenance(
            detached,
            fid,
            flight.target,
            commit,
        ),
        commit.issued is Some,
        certificate_belongs_to_commit(certificate, commit),
        response_certificate_ready(
            store,
            detached.keys.prefix,
            response,
            certificate,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_answered_schedule(
                detached,
                fid,
                flight,
                commit,
                done,
                response,
            ),
        ),
{
    lemma_answered_origin_preserves_core_retained_append_certificates(
        detached,
        fid,
        flight,
        commit,
        done,
        response,
        store,
        certificate,
    );
    lemma_answered_commit_advance_preserves_core_retained_append_certificates(
        detached,
        fid,
        commit,
        response,
        store,
        certificate,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        detached,
        fid,
        commit,
        Some(response),
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            assert(phase_append_certificates(
                store,
                advanced.0.keys.prefix,
                crate::handler_docs::PhaseSpec::Schedule {
                    commit: advanced.1,
                    done,
                },
            )) by {
                reveal(phase_append_certificates);
                reveal(commit_loaded_append_certificate);
                reveal(crate::handler_docs::spec_commit_advance);
                reveal(crate::handler_docs::spec_answered);
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
                    phase:
                        crate::handler_docs::PhaseSpec::Schedule {
                            commit: advanced.1,
                            done,
                        },
                    ..flight
                },
            );
        },
        _ => {
            assert(crate::handler_docs::spec_answered_schedule(
                detached,
                fid,
                flight,
                commit,
                done,
                response,
            ) == crate::handler_docs::spec_answered_origin(
                detached,
                fid,
                flight,
                commit,
                done,
                response,
            )) by {
                reveal(crate::handler_docs::spec_answered_schedule);
                reveal(crate::handler_docs::spec_answered_origin);
            };
        },
    }
    reveal(crate::handler_docs::spec_answered_schedule);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_idle_done_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    fired: crate::types::Fired,
)
    requires
        crate::global_store_control::detached_flight_control(state, fid),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
    ensures
        ({
            let swept = crate::state::spec_note(
                state,
                crate::types::NoteSpec::SweepEnd {
                    flight: fid,
                    committed: true,
                },
            );
            let noted = crate::state::spec_note(
                swept,
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_finish(
                    noted,
                    flight,
                    Ok(fired),
                ),
            )
        }),
{
    let swept = crate::state::spec_note(
        state,
        crate::types::NoteSpec::SweepEnd {
            flight: fid,
            committed: true,
        },
    );
    let noted = crate::state::spec_note(
        swept,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    lemma_note_preserves_core_control_body(
        state,
        crate::types::NoteSpec::SweepEnd {
            flight: fid,
            committed: true,
        },
    );
    lemma_note_preserves_retained_provenance(
        state,
        crate::types::NoteSpec::SweepEnd {
            flight: fid,
            committed: true,
        },
    );
    lemma_note_preserves_core_control_body(
        swept,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    lemma_note_preserves_retained_provenance(
        swept,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    lemma_core_retained_append_certificates_frame(store, state, noted);
    assert(crate::global_store_control::detached_flight_control(
        noted,
        fid,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_control::detached_flight_control);
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        noted,
        flight,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_lane::detached_flight_owns_primary);
    };
    let primary = crate::target::spec_name(flight.target);
    assert(crate::production_relation::flight_lanes_consistent(
        noted.flights,
    )) by {
        reveal(production_core_control_body);
    };
    assert(crate::global_store_lane::secondary_flight_lanes_consistent(
        noted,
    )) by {
        reveal(production_core_control_body);
    };
    crate::global_store_lane::lemma_detached_busy_owner_leaves_lane_unowned(
        noted.flights,
        primary,
        flight.id,
    );
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_secondary_lane_unowned(
            noted,
            primary,
            flight.id,
        );
    lemma_finish_preserves_core_retained_append_certificates(
        store,
        noted,
        flight,
        Ok(fired),
    );
}

pub(crate) proof fn lemma_fire_idle_failed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    error: echod_concrete::store::StoreErrorSpec,
)
    requires
        flight.id == fid,
        crate::global_store_control::detached_flight_control(state, fid),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
    ensures
        ({
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::SweepEnd {
                    flight: fid,
                    committed: false,
                },
            );
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_commit_failed(
                    noted,
                    flight,
                    error,
                ),
            )
        }),
{
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::SweepEnd {
            flight: fid,
            committed: false,
        },
    );
    lemma_note_preserves_core_control_body(
        state,
        crate::types::NoteSpec::SweepEnd {
            flight: fid,
            committed: false,
        },
    );
    lemma_note_preserves_retained_provenance(
        state,
        crate::types::NoteSpec::SweepEnd {
            flight: fid,
            committed: false,
        },
    );
    lemma_core_retained_append_certificates_frame(store, state, noted);
    assert(crate::global_store_control::detached_flight_control(
        noted,
        fid,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_control::detached_flight_control);
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        noted,
        flight,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_lane::detached_flight_owns_primary);
    };
    lemma_commit_failed_preserves_core_retained_append_certificates(
        store,
        noted,
        flight,
        error,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_idle_preserves_core_retained_append_certificates(
    detached: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
    certificate: StoreEffectCertificateV,
)
    requires
        production_core_control_body(detached),
        retained_commit_provenance(detached),
        cache_identity_provenance(detached),
        core_retained_append_certificates(store, detached),
        crate::global_store_control::detached_flight_control(
            detached,
            fid,
        ),
        crate::global_store_lane::detached_flight_owns_primary(
            detached,
            flight,
        ),
        commit_candidate_provenance(
            detached,
            fid,
            flight.target,
            commit,
        ),
        commit.issued is Some,
        certificate_belongs_to_commit(certificate, commit),
        response_certificate_ready(
            store,
            detached.keys.prefix,
            response,
            certificate,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_answered_fire_idle(
                detached,
                fid,
                flight,
                commit,
                response,
            ),
        ),
{
    lemma_answered_commit_advance_preserves_core_retained_append_certificates(
        detached,
        fid,
        commit,
        response,
        store,
        certificate,
    );
    lemma_detached_commit_advance_preserves_retained_provenance(
        detached,
        fid,
        flight.target,
        commit,
        response,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        detached,
        fid,
        commit,
        Some(response),
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            assert(phase_append_certificates(
                store,
                advanced.0.keys.prefix,
                crate::handler_docs::PhaseSpec::FireIdle {
                    commit: advanced.1,
                },
            )) by {
                reveal(phase_append_certificates);
                reveal(commit_loaded_append_certificate);
                reveal(crate::handler_docs::spec_commit_advance);
                reveal(crate::handler_docs::spec_answered);
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
                    phase: crate::handler_docs::PhaseSpec::FireIdle {
                        commit: advanced.1,
                    },
                    ..flight
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    detached,
                    fid,
                    commit,
                    Some(response),
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
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            };
            lemma_fire_idle_done_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                fid,
                flight,
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    detached,
                    fid,
                    commit,
                    Some(response),
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
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            };
            lemma_fire_idle_failed_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                fid,
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
    reveal(crate::handler_docs::spec_answered_fire_idle);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_loading_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    revalidating: Option<crate::cache::CachedSpec>,
    response: echod_concrete::store::StoreRes,
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
        flight_submission_provenance(flight),
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
        revalidating is Some ==>
            cached_append_certificate(
                store,
                state.keys.prefix,
                revalidating.unwrap(),
            ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_answered_loading(
                state,
                flight,
                revalidating,
                response,
            ),
        ),
{
    lemma_answered_loading_preserves_retained_provenance(
        state,
        flight,
        revalidating,
        response,
    );
    reveal(crate::handler_docs::spec_answered_loading);
    match flight.target {
        crate::target::TargetSpec::Origin(origin) => {
            lemma_loaded_origin_preserves_core_retained_append_certificates(
                state,
                origin,
                revalidating,
                response,
                store,
            );
            lemma_loaded_origin_success_has_provenance(
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
            assert(crate::global_store_lane::
                detached_flight_owns_primary(
                    loaded.0,
                    flight,
                )) by {
                reveal(crate::handler_docs::spec_loaded_origin);
                reveal(crate::state::spec_remember);
                reveal(crate::state::spec_forget_origin);
                reveal(crate::state::spec_note);
                reveal(
                    crate::global_store_lane::
                        detached_flight_owns_primary,
                );
            };
            assert(loaded.0.flights == state.flights) by {
                reveal(crate::handler_docs::spec_loaded_origin);
                reveal(crate::state::spec_remember);
                reveal(crate::state::spec_forget_origin);
                reveal(crate::state::spec_note);
            };
            assert(loaded.0.keys == state.keys) by {
                reveal(crate::handler_docs::spec_loaded_origin);
                reveal(crate::state::spec_remember);
                reveal(crate::state::spec_forget_origin);
                reveal(crate::state::spec_note);
            };
            assert(retained_commit_provenance(loaded.0)) by {
                reveal(crate::handler_docs::spec_loaded_origin);
                reveal(crate::state::spec_remember);
                reveal(crate::state::spec_forget_origin);
                reveal(crate::state::spec_note);
                reveal(retained_commit_provenance);
            };
            assert(cache_identity_provenance(loaded.0)) by {
                reveal(crate::handler_docs::spec_loaded_origin);
                reveal(crate::state::spec_remember);
                reveal(crate::state::spec_forget_origin);
                reveal(crate::state::spec_note);
                reveal(cache_identity_provenance);
            };
            match loaded.1 {
                Ok(working) => {
                    lemma_run_origin_preserves_core_retained_append_certificates(
                        loaded.0,
                        flight,
                        working,
                        store,
                    );
                },
                Err(error) => {
                    lemma_fail_preserves_core_retained_append_certificates(
                        store,
                        loaded.0,
                        flight,
                        error,
                    );
                },
            }
        },
        crate::target::TargetSpec::Schedule(schedule) => {
            let loaded = crate::handler_sched::spec_loaded_schedule(
                state,
                schedule,
                response,
            );
            lemma_loaded_schedule_is_uncertified(
                state,
                schedule,
                response,
                store,
            );
            assert(loaded.1 is Ok ==>
                loaded_append_certificate(
                    store,
                    state.keys.prefix,
                    loaded.1->Ok_0.loaded,
                )) by {
                reveal(loaded_append_certificate);
            };
            assert(core_retained_append_certificates(
                store,
                loaded.0,
            )) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(core_retained_append_certificates);
            };
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
            assert(crate::global_store_lane::
                detached_flight_owns_primary(
                    loaded.0,
                    flight,
                )) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(
                    crate::global_store_lane::
                        detached_flight_owns_primary,
                );
            };
            assert(retained_commit_provenance(loaded.0)) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(crate::state::spec_note);
                reveal(retained_commit_provenance);
            };
            assert(cache_identity_provenance(loaded.0)) by {
                reveal(crate::handler_sched::spec_loaded_schedule);
                reveal(crate::state::spec_note);
                reveal(cache_identity_provenance);
            };
            match loaded.1 {
                Ok(working) => {
                    lemma_run_schedule_preserves_core_retained_append_certificates(
                        loaded.0,
                        flight,
                        working,
                        store,
                    );
                },
                Err(error) => {
                    lemma_fail_preserves_core_retained_append_certificates(
                        store,
                        loaded.0,
                        flight,
                        error,
                    );
                },
            }
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_prepare_detached_flight_response_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
    ensures
        ({
            let certificate = state.store_certificates[op];
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            let flight = state.flights.inflight[fid];
            let detached =
                crate::handler_docs::spec_take_flight(consumed, fid);
            &&& flight.id == fid
            &&& flight.phase.expects() == Some(op)
            &&& detached.keys == state.keys
            &&& production_core_control_body(detached)
            &&& retained_commit_provenance(detached)
            &&& cache_identity_provenance(detached)
            &&& core_retained_append_certificates(store, detached)
            &&& phase_append_certificates(
                store,
                state.keys.prefix,
                flight.phase,
            )
            &&& flight_submission_provenance(flight)
            &&& flight_control_provenance(
                state.keys.prefix,
                flight,
            )
            &&& crate::global_store_control::detached_flight_control(
                detached,
                fid,
            )
            &&& crate::global_store_lane::detached_flight_owns_primary(
                detached,
                flight,
            )
            &&& phase_commit_candidate_provenance(
                detached,
                fid,
                flight.target,
                flight.phase,
            )
            &&& match flight.phase {
                crate::handler_docs::PhaseSpec::FireLoadingOrigin {
                    ctx,
                    ..
                } => {
                    let secondary = crate::target::spec_name(
                        crate::target::TargetSpec::Origin(ctx.origin),
                    );
                    &&& detached.flights.slots.contains_key(secondary)
                    &&& detached.flights.slots[secondary].busy == Some(fid)
                },
                _ => true,
            }
            &&& match flight.phase {
                crate::handler_docs::PhaseSpec::Origin { commit, .. }
                | crate::handler_docs::PhaseSpec::Schedule { commit, .. }
                | crate::handler_docs::PhaseSpec::FireIdle { commit }
                | crate::handler_docs::PhaseSpec::FireSchedule { commit }
                | crate::handler_docs::PhaseSpec::FireOrigin {
                    commit,
                    ..
                } => {
                    &&& commit.issued is Some
                    &&& certificate_belongs_to_commit(
                        certificate,
                        commit,
                    )
                    &&& core_retained_append_certificates(
                        store,
                        crate::handler_docs::spec_commit_advance(
                            detached,
                            fid,
                            commit,
                            Some(response),
                        ).0,
                    )
                },
                _ => true,
            }
        }),
{
    let certificate = state.store_certificates[op];
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    assert(core_retained_append_certificates(store, consumed)) by {
        reveal(core_retained_append_certificates);
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
    assert(flight.id == fid) by {
        reveal(production_core_control_body);
        reveal(active_flight_ids_match_keys);
    };
    assert(flight_submission_provenance(flight)) by {
        reveal(retained_commit_provenance);
    };
    assert(flight_control_provenance(
        state.keys.prefix,
        flight,
    )) by {
        reveal(retained_commit_provenance);
    };
    assert(phase_append_certificates(
        store,
        state.keys.prefix,
        flight.phase,
    )) by {
        reveal(core_retained_append_certificates);
    };
    crate::global_store_control::
        lemma_consume_and_detach_flight_preserves_core_control(
            state,
            op,
            fid,
        );
    lemma_consume_and_detach_flight_preserves_retained_provenance(
        state,
        fid,
        op,
    );
    let detached =
        crate::handler_docs::spec_take_flight(consumed, fid);
    match flight.phase {
        crate::handler_docs::PhaseSpec::FireLoadingOrigin {
            ctx,
            ..
        } => {
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(ctx.origin),
            );
            assert(state.flights.slots.contains_key(secondary)
                && state.flights.slots[secondary].busy == Some(fid)) by {
                reveal(retained_commit_provenance);
                reveal(
                    crate::global_store_lane::
                        secondary_flight_lanes_consistent,
                );
            };
            assert(detached.flights.slots.contains_key(secondary)
                && detached.flights.slots[secondary].busy == Some(fid)) by {
                reveal(crate::handler_docs::spec_take_flight);
            };
        },
        _ => {},
    }
    assert(detached.keys == state.keys) by {
        reveal(crate::handler_docs::spec_take_flight);
    };
    lemma_take_flight_preserves_core_retained_append_certificates(
        store,
        consumed,
        fid,
    );
    assert(response_certificate_ready(
        store,
        detached.keys.prefix,
        response,
        certificate,
    )) by {
        reveal(crate::handler_docs::spec_take_flight);
    };
    match flight.phase {
        crate::handler_docs::PhaseSpec::Origin { commit, .. }
        | crate::handler_docs::PhaseSpec::Schedule { commit, .. }
        | crate::handler_docs::PhaseSpec::FireIdle { commit }
        | crate::handler_docs::PhaseSpec::FireSchedule { commit }
        | crate::handler_docs::PhaseSpec::FireOrigin {
            commit,
            ..
        } => {
            assert(commit.issued is Some);
            assert(certificate_belongs_to_commit(
                certificate,
                commit,
            )) by {
                reveal(retained_commit_provenance);
                reveal(phase_commit_provenance);
                reveal(commit_provenance);
                reveal(commit_attachable_provenance);
                reveal(commit_issued_operation_provenance);
            };
            lemma_answered_commit_advance_preserves_core_retained_append_certificates(
                detached,
                fid,
                commit,
                response,
                store,
                certificate,
            );
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_loading_flight_completion_preserves_core_retained_append_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
        state.flights.inflight[fid].phase is Loading,
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    lemma_prepare_detached_flight_response_certificates(
        state,
        op,
        fid,
        response,
        store,
    );
    let certificate = state.store_certificates[op];
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let flight = state.flights.inflight[fid];
    let detached =
        crate::handler_docs::spec_take_flight(consumed, fid);
    let idle = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Idle,
        ..flight
    };
    assert(detached.keys == state.keys);
    assert(phase_append_certificates(
        store,
        state.keys.prefix,
        flight.phase,
    ));
    reveal(crate::handler_docs::spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    match flight.phase {
        crate::handler_docs::PhaseSpec::Loading {
            revalidating,
            ..
        } => {
            assert(revalidating is Some ==>
                cached_append_certificate(
                    store,
                    detached.keys.prefix,
                    revalidating.unwrap(),
                )) by {
                reveal(phase_append_certificates);
            };
            lemma_answered_loading_preserves_core_retained_append_certificates(
                detached,
                idle,
                revalidating,
                response,
                store,
            );
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_origin_flight_completion_preserves_core_retained_append_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
        state.flights.inflight[fid].phase is Origin,
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    lemma_prepare_detached_flight_response_certificates(
        state,
        op,
        fid,
        response,
        store,
    );
    let certificate = state.store_certificates[op];
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let flight = state.flights.inflight[fid];
    let detached =
        crate::handler_docs::spec_take_flight(consumed, fid);
    let idle = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Idle,
        ..flight
    };
    reveal(crate::handler_docs::spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    match flight.phase {
        crate::handler_docs::PhaseSpec::Origin {
            commit,
            done,
        } => {
            lemma_answered_origin_preserves_core_retained_append_certificates(
                detached,
                fid,
                idle,
                commit,
                done,
                response,
                store,
                certificate,
            );
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_schedule_flight_completion_preserves_core_retained_append_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
        state.flights.inflight[fid].phase is Schedule,
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    lemma_prepare_detached_flight_response_certificates(
        state,
        op,
        fid,
        response,
        store,
    );
    let certificate = state.store_certificates[op];
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let flight = state.flights.inflight[fid];
    let detached =
        crate::handler_docs::spec_take_flight(consumed, fid);
    let idle = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Idle,
        ..flight
    };
    reveal(crate::handler_docs::spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    match flight.phase {
        crate::handler_docs::PhaseSpec::Schedule {
            commit,
            done,
        } => {
            lemma_answered_schedule_preserves_core_retained_append_certificates(
                detached,
                fid,
                idle,
                commit,
                done,
                response,
                store,
                certificate,
            );
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_uncertified_fire_load_origin_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    store: StoreV,
)
    requires
        core_retained_append_certificates(store, state),
        !context.ws.loaded.append_certified,
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_sched::spec_fire_load_origin(
                state,
                flight,
                context,
            ),
        ),
{
    reveal(core_retained_append_certificates);
    lemma_cache_get_preserves_append_certificates(
        store,
        state.keys.prefix,
        state.cache,
        context.origin,
    );
    reveal(crate::handler_sched::spec_fire_load_origin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::cache::spec_get);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(phase_append_certificates);
    reveal(loaded_append_certificate);
    reveal(cached_append_certificate);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_uncertified_fire_claim_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
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
        flight_submission_provenance(flight),
        flight.work is Fire,
        fire_context_provenance(
            state.keys.prefix,
            flight.work->Fire_schedule,
            context,
        ),
        !context.ws.loaded.append_certified,
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_sched::spec_fire_claim(
                state,
                flight,
                context,
            ),
        ),
{
    lemma_fire_claim_preserves_retained_provenance(
        state,
        flight,
        context,
    );
    let origin = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    let slot = crate::handler_docs::spec_slot_of(state, origin);
    if slot.busy is Some {
        let staged = crate::handler_docs::spec_with_slot(
            state,
            origin,
            crate::handler_docs::SlotSpec {
                queue: slot.queue.push(
                    crate::handler_docs::QueuedSpec::Waiter(flight.id),
                ),
                ..slot
            },
        );
        lemma_core_retained_append_certificates_frame(
            store,
            state,
            staged,
        );
        assert(phase_append_certificates(
            store,
            staged.keys.prefix,
            crate::handler_docs::PhaseSpec::FireWaitingOrigin(context),
        )) by {
            reveal(phase_append_certificates);
            reveal(loaded_append_certificate);
        };
        lemma_inflight_preserves_core_retained_append_certificates(
            store,
            staged,
            crate::handler_docs::FlightSpec {
                phase:
                    crate::handler_docs::PhaseSpec::FireWaitingOrigin(
                        context,
                    ),
                ..flight
            },
        );
    } else {
        let claimed = crate::handler_docs::spec_with_slot(
            state,
            origin,
            crate::handler_docs::SlotSpec {
                busy: Some(flight.id),
                ..slot
            },
        );
        lemma_core_retained_append_certificates_frame(
            store,
            state,
            claimed,
        );
        lemma_uncertified_fire_load_origin_preserves_core_retained_append_certificates(
            claimed,
            flight,
            context,
            store,
        );
    }
    reveal(crate::handler_sched::spec_fire_claim);
    reveal(crate::handler_sched::spec_fire_load_origin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(core_retained_append_certificates);
    reveal(phase_append_certificates);
    reveal(loaded_append_certificate);
    reveal(cached_append_certificate);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_prepare_uncertified_fire_idle_commit(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    at: u64,
    fired: Option<crate::verified::flight_spec::AFired>,
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
        !working.loaded.append_certified,
    ensures
        ({
            let body =
                crate::document::spec_loaded_body(working.loaded);
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::SweepBegin {
                    flight: flight.id,
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
            let advanced = crate::handler_docs::spec_commit_advance(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            &&& committed.0 == noted
            &&& committed.1.issued is None
            &&& committed.1.seq.step is Start
            &&& retained_commit_provenance(advanced.0)
            &&& cache_identity_provenance(advanced.0)
            &&& core_retained_append_certificates(
                store,
                advanced.0,
            )
        }),
{
    let body = crate::document::spec_loaded_body(working.loaded);
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::SweepBegin {
            flight: flight.id,
            target: working.target,
            now: at,
        },
    );
    lemma_note_preserves_core_control_body(
        state,
        crate::types::NoteSpec::SweepBegin {
            flight: flight.id,
            target: working.target,
            now: at,
        },
    );
    lemma_note_preserves_retained_provenance(
        state,
        crate::types::NoteSpec::SweepBegin {
            flight: flight.id,
            target: working.target,
            now: at,
        },
    );
    lemma_core_retained_append_certificates_frame(store, state, noted);
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
    assert(committed.1.seq.step is Start) by {
        reveal(crate::handler_docs::spec_commit_new);
        reveal(crate::verified::flight_spec::spec_new);
    };
    lemma_initial_commit_advance_preserves_core_retained_append_certificates(
        committed.0,
        flight.id,
        committed.1,
        store,
    );
    lemma_detached_initial_commit_advance_preserves_retained_provenance(
        committed.0,
        flight.id,
        flight.target,
        committed.1,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_uncertified_fire_idle_issued_phase_fact(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    at: u64,
    fired: Option<crate::verified::flight_spec::AFired>,
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
        !working.loaded.append_certified,
    ensures
        ({
            let body =
                crate::document::spec_loaded_body(working.loaded);
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::SweepBegin {
                    flight: flight.id,
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
            let advanced = crate::handler_docs::spec_commit_advance(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            advanced.2 is Issued ==>
                phase_append_certificates(
                    store,
                    advanced.0.keys.prefix,
                    crate::handler_docs::PhaseSpec::FireIdle {
                        commit: advanced.1,
                    },
                )
        }),
{
    lemma_prepare_uncertified_fire_idle_commit(
        state,
        flight,
        working,
        at,
        fired,
        store,
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
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        body,
        echod_concrete::node::spec_body_deadline(body),
        at,
        fired,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    if advanced.2 is Issued {
        assert(committed.1.w == working) by {
            reveal(crate::handler_docs::spec_commit_new);
        };
        assert(advanced.1.w == working) by {
            reveal(crate::handler_docs::spec_commit_advance);
            reveal(crate::handler_docs::spec_allocate_arm_token);
            reveal(crate::verified::flight_spec::spec_advance);
            reveal(crate::handler_docs::spec_issue_write);
            reveal(crate::state::spec_store_certified);
            reveal(crate::state::spec_store_raw);
        };
        assert(phase_append_certificates(
            store,
            advanced.0.keys.prefix,
            crate::handler_docs::PhaseSpec::FireIdle {
                commit: advanced.1,
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
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_uncertified_fire_idle_nonissued_control_facts(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    at: u64,
    fired: Option<crate::verified::flight_spec::AFired>,
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
        !working.loaded.append_certified,
    ensures
        ({
            let body =
                crate::document::spec_loaded_body(working.loaded);
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::SweepBegin {
                    flight: flight.id,
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
            let advanced = crate::handler_docs::spec_commit_advance(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            !(advanced.2 is Issued) ==> {
                &&& crate::global_store_control::
                    detached_flight_control(
                        advanced.0,
                        flight.id,
                    )
                &&& crate::global_store_lane::
                    detached_flight_owns_primary(
                        advanced.0,
                        crate::handler_docs::FlightSpec {
                            idle: true,
                            ..flight
                        },
                    )
            }
        }),
{
    lemma_prepare_uncertified_fire_idle_commit(
        state,
        flight,
        working,
        at,
        fired,
        store,
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
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        body,
        echod_concrete::node::spec_body_deadline(body),
        at,
        fired,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    if !(advanced.2 is Issued) {
        crate::global_store_control::
            lemma_commit_advance_nonissued_preserves_detached_flight_control(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
        assert(crate::global_store_lane::
            detached_flight_owns_primary(
                advanced.0,
                crate::handler_docs::FlightSpec {
                    idle: true,
                    ..flight
                },
            )) by {
            reveal(
                crate::global_store_lane::
                    detached_flight_owns_primary,
            );
            lemma_commit_advance_frames_keys_and_flights(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
        };
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_uncertified_fire_idle_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    at: u64,
    fired: Option<crate::verified::flight_spec::AFired>,
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
        !working.loaded.append_certified,
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_sched::spec_fire_idle(
                state,
                flight,
                working,
                at,
                fired,
            ),
        ),
{
    lemma_prepare_uncertified_fire_idle_commit(
        state,
        flight,
        working,
        at,
        fired,
        store,
    );
    lemma_uncertified_fire_idle_issued_phase_fact(
        state,
        flight,
        working,
        at,
        fired,
        store,
    );
    lemma_uncertified_fire_idle_nonissued_control_facts(
        state,
        flight,
        working,
        at,
        fired,
        store,
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
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        body,
        echod_concrete::node::spec_body_deadline(body),
        at,
        fired,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    let idle_flight = crate::handler_docs::FlightSpec {
        idle: true,
        ..flight
    };
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            lemma_inflight_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::FireIdle {
                        commit: advanced.1,
                    },
                    ..idle_flight
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(result) => {
            lemma_fire_idle_done_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                flight.id,
                idle_flight,
                result,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            lemma_fire_idle_failed_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                flight.id,
                idle_flight,
                error,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_op_exhausted_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                idle_flight,
            );
        },
    }
    reveal(crate::handler_sched::spec_fire_idle);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_uncertified_fire_decide_preserves_core_retained_append_certificates(
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
        flight_submission_provenance(flight),
        flight.work is Fire,
        working_document_provenance(state.keys.prefix, working),
        working_matches_target(working, flight.target),
        !working.loaded.append_certified,
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_sched::spec_fire_decide(
                state,
                flight,
                working,
            ),
        ),
{
    lemma_fire_decide_preserves_retained_provenance(
        state,
        flight,
        working,
    );
    reveal(crate::handler_sched::spec_fire_decide);
    reveal(crate::handler_sched::spec_fire_idle);
    reveal(crate::handler_sched::spec_fire_claim);
    reveal(crate::handler_sched::spec_fire_load_origin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_commit_new);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(core_retained_append_certificates);
    reveal(phase_append_certificates);
    reveal(commit_loaded_append_certificate);
    reveal(loaded_append_certificate);
    reveal(cached_append_certificate);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire {
            fired,
            now,
            ..
        } => {
            let at = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(
                    working.loaded,
                ),
                now,
            );
            let body = crate::document::spec_loaded_body(
                working.loaded,
            );
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
                        reveal(
                            crate::document::
                                spec_loaded_committed_at,
                        );
                    };
                    assert(at <= echod_types::MAX_TIME) by {
                        reveal(crate::document::spec_clamp_now);
                    };
                    lemma_uncertified_fire_idle_preserves_core_retained_append_certificates(
                        state,
                        flight,
                        working,
                        at,
                        fired,
                        store,
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
                    let context = crate::handler_docs::FireCtxSpec {
                        ws: working,
                        row,
                        advanced,
                        pending,
                        t1: at,
                        origin: echod_types::origin(pending.promise),
                        next,
                    };
                    assert(fire_context_provenance(
                        state.keys.prefix,
                        flight.work->Fire_schedule,
                        context,
                    )) by {
                        reveal(fire_context_provenance);
                        reveal(working_matches_target);
                        reveal(working_document_provenance);
                        reveal(crate::document::spec_loaded_body);
                        reveal(crate::verified::flight_spec::spec_step);
                        reveal(
                            echod_concrete::node::spec_fire_schedule,
                        );
                        reveal(
                            echod_concrete::document::well_formed,
                        );
                        reveal(
                            echod_concrete::document::
                                schedule_well_formed,
                        );
                        reveal(echod_types::spec_deadline_bounded);
                    };
                    lemma_uncertified_fire_claim_preserves_core_retained_append_certificates(
                        state,
                        flight,
                        context,
                        store,
                    );
                },
            }
        },
        _ => {
            assert(core_retained_append_certificates(
                store,
                crate::handler_docs::spec_fail(
                    state,
                    flight,
                    "not a fire"@,
                ),
            ));
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_loading_schedule_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    response: echod_concrete::store::StoreRes,
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
        flight_submission_provenance(flight),
        flight.work is Fire,
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_answered_fire_loading_schedule(
                state,
                flight,
                response,
            ),
        ),
{
    let schedule = flight.work->Fire_schedule;
    let loaded = crate::handler_sched::spec_loaded_schedule(
        state,
        schedule,
        response,
    );
    lemma_loaded_schedule_is_uncertified(
        state,
        schedule,
        response,
        store,
    );
    assert(core_retained_append_certificates(store, loaded.0)) by {
        reveal(crate::handler_sched::spec_loaded_schedule);
        reveal(core_retained_append_certificates);
    };
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
    assert(crate::global_store_lane::detached_flight_owns_primary(
        loaded.0,
        flight,
    )) by {
        reveal(crate::handler_sched::spec_loaded_schedule);
        reveal(crate::global_store_lane::detached_flight_owns_primary);
    };
    assert(retained_commit_provenance(loaded.0)) by {
        reveal(crate::handler_sched::spec_loaded_schedule);
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(loaded.0)) by {
        reveal(crate::handler_sched::spec_loaded_schedule);
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    match loaded.1 {
        Ok(working) => {
            lemma_uncertified_fire_decide_preserves_core_retained_append_certificates(
                loaded.0,
                flight,
                working,
                store,
            );
        },
        Err(error) => {
            lemma_fail_preserves_core_retained_append_certificates(
                store,
                loaded.0,
                flight,
                error,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_fire_loading_schedule);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_loading_schedule_completion_preserves_core_retained_append_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
        state.flights.inflight[fid].phase is FireLoadingSchedule,
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    lemma_prepare_detached_flight_response_certificates(
        state,
        op,
        fid,
        response,
        store,
    );
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let flight = state.flights.inflight[fid];
    let detached =
        crate::handler_docs::spec_take_flight(consumed, fid);
    let idle = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Idle,
        ..flight
    };
    reveal(crate::handler_docs::spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    match flight.phase {
        crate::handler_docs::PhaseSpec::FireLoadingSchedule { .. } => {
            lemma_answered_fire_loading_schedule_preserves_core_retained_append_certificates(
                detached,
                idle,
                response,
                store,
            );
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_run_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
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
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(flight.id)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
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
        loaded_append_certificate(
            store,
            state.keys.prefix,
            working.loaded,
        ),
        loaded_append_certificate(
            store,
            state.keys.prefix,
            context.ws.loaded,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_sched::spec_fire_run(
                state,
                flight,
                context,
                working,
            ),
        ),
{
    lemma_prepare_fire_run_append_certificates(
        state,
        flight,
        context,
        working,
        store,
    );
    let at = crate::document::spec_clamp_now(
        crate::document::spec_loaded_committed_at(working.loaded),
        context.t1,
    );
    let occurrence = echod_concrete::node::spec_occurrence_transition(
        crate::document::spec_loaded_body(working.loaded),
        context.pending,
        at,
        crate::handler_docs::spec_effective_retry_timeout(
            state.cfg.retry_timeout,
        ),
    );
    let outbox = crate::handler_docs::spec_dispatches(
        occurrence.0,
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
        occurrence.0,
        echod_concrete::node::spec_body_deadline(occurrence.0),
        at,
        None,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    lemma_commit_advance_frames_keys_and_flights(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    assert(advanced.0.keys == state.keys) by {
        reveal(crate::state::spec_note);
        reveal(crate::handler_docs::spec_commit_new);
    };
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            lemma_inflight_preserves_core_retained_append_certificates(
                store,
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
        },
        crate::handler_docs::ProgressSpec::Done(_) => {
            lemma_fire_origin_done_tail_preserves_core_retained_append_certificates(
                advanced.0,
                flight,
                context,
                at,
                outbox,
                store,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            lemma_fire_origin_failed_tail_preserves_core_retained_append_certificates(
                advanced.0,
                flight,
                context,
                error,
                store,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            lemma_fire_origin_exhausted_tail_preserves_core_retained_append_certificates(
                advanced.0,
                flight,
                context,
                store,
            );
        },
    }
    reveal(crate::handler_sched::spec_fire_run);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_origin_failed_tail_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    error: echod_concrete::store::StoreErrorSpec,
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
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(flight.id)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        flight_submission_provenance(flight),
        flight.work is Fire,
    ensures
        ({
            let ended = crate::state::spec_note(
                state,
                crate::types::NoteSpec::FireEnd {
                    flight: flight.id,
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
            core_retained_append_certificates(
                store,
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
    lemma_fire_primary_differs_origin_lane(flight, context.origin);
    let ended = crate::state::spec_note(
        state,
        crate::types::NoteSpec::FireEnd {
            flight: flight.id,
            committed: false,
        },
    );
    lemma_core_retained_append_certificates_frame(store, state, ended);
    lemma_cache_remove_preserves_append_certificates(
        store,
        state.keys.prefix,
        ended.cache,
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
    assert(core_retained_append_certificates(store, forgotten)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(core_retained_append_certificates);
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
    assert(crate::global_store_control::detached_flight_control(
        forgotten,
        flight.id,
    )) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(
            crate::global_store_control::detached_flight_control,
        );
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        forgotten,
        flight,
    )) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(
            crate::global_store_lane::detached_flight_owns_primary,
        );
    };
    assert(forgotten.flights.slots.contains_key(secondary)
        && forgotten.flights.slots[secondary].busy
            == Some(flight.id)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
    };
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_lane_unowned(
            forgotten.flights,
            secondary,
            flight.id,
        );
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_secondary_lane_unowned(
            forgotten,
            secondary,
            flight.id,
        );
    crate::global_store_lane::
        lemma_release_other_lane_preserves_detached_primary(
            forgotten,
            secondary,
            flight,
        );
    lemma_release_preserves_core_retained_append_certificates(
        store,
        forgotten,
        secondary,
    );
    lemma_release_preserves_retained_provenance(forgotten, secondary);
    crate::global_store_control::
        lemma_release_preserves_detached_flight_control(
            forgotten,
            secondary,
            flight.id,
        );
    let released =
        crate::handler_docs::spec_release(forgotten, secondary);
    lemma_commit_failed_preserves_core_retained_append_certificates(
        store,
        released,
        flight,
        error,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_origin_exhausted_tail_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
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
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_op_exhausted(
                    abandoned,
                    flight,
                ),
            )
        }),
{
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    lemma_cache_remove_preserves_append_certificates(
        store,
        state.keys.prefix,
        state.cache,
        context.origin,
    );
    let forgotten = crate::state::spec_forget_origin(
        state,
        context.origin,
    );
    let abandoned = crate::handler_docs::spec_abandon_slot(
        forgotten,
        secondary,
    );
    assert(core_retained_append_certificates(store, abandoned)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(core_retained_append_certificates);
    };
    lemma_op_exhausted_preserves_core_retained_append_certificates(
        store,
        abandoned,
        flight,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_origin_done_tail_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
    outbox: Seq<(Seq<char>, crate::types::MessageSpec)>,
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
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(flight.id)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
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
        loaded_append_certificate(
            store,
            state.keys.prefix,
            context.ws.loaded,
        ),
    ensures
        ({
            let ended = crate::state::spec_note(
                crate::state::spec_note(
                    state,
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
            core_retained_append_certificates(
                store,
                crate::handler_sched::spec_fire_advance(
                    released,
                    flight,
                    context,
                    at,
                ),
            )
        }),
{
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    lemma_fire_primary_differs_origin_lane(flight, context.origin);
    let ended = crate::state::spec_note(
        crate::state::spec_note(
            state,
            crate::types::NoteSpec::FireEnd {
                flight: flight.id,
                committed: true,
            },
        ),
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    lemma_core_retained_append_certificates_frame(store, state, ended);
    assert(retained_commit_provenance(ended)) by {
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(ended)) by {
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    assert(production_core_control_body(ended)) by {
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
    };
    lemma_send_all_preserves_core_retained_append_certificates(
        store,
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
    assert(crate::global_store_control::detached_flight_control(
        sent,
        flight.id,
    )) by {
        reveal(crate::global_store_control::detached_flight_control);
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        sent,
        flight,
    )) by {
        reveal(
            crate::global_store_lane::detached_flight_owns_primary,
        );
    };
    assert(sent.flights.slots.contains_key(secondary)
        && sent.flights.slots[secondary].busy == Some(flight.id));
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_lane_unowned(
            sent.flights,
            secondary,
            flight.id,
        );
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_secondary_lane_unowned(
            sent,
            secondary,
            flight.id,
        );
    crate::global_store_lane::
        lemma_release_other_lane_preserves_detached_primary(
            sent,
            secondary,
            flight,
        );
    lemma_release_preserves_core_retained_append_certificates(
        store,
        sent,
        secondary,
    );
    lemma_release_preserves_retained_provenance(sent, secondary);
    crate::global_store_control::
        lemma_release_preserves_detached_flight_control(
            sent,
            secondary,
            flight.id,
        );
    lemma_release_preserves_keys(sent, secondary);
    let released = crate::handler_docs::spec_release(sent, secondary);
    lemma_fire_advance_preserves_core_retained_append_certificates(
        released,
        flight,
        context,
        at,
        store,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_prepare_fire_run_commit_candidate(
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
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(flight.id)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
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
        ({
            let at = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(working.loaded),
                context.t1,
            );
            let occurrence =
                echod_concrete::node::spec_occurrence_transition(
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
        StoredDocumentV::Schedule(_) => {
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
    assert(noted.flights.slots.contains_key(
        crate::target::spec_name(
            crate::target::TargetSpec::Origin(context.origin),
        ),
    )) by {
        reveal(crate::state::spec_note);
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
    reveal(crate::verified::flight_spec::spec_new);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_prepare_fire_run_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
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
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(flight.id)
        }),
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
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
        loaded_append_certificate(
            store,
            state.keys.prefix,
            working.loaded,
        ),
        loaded_append_certificate(
            store,
            state.keys.prefix,
            context.ws.loaded,
        ),
    ensures
        ({
            let at = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(working.loaded),
                context.t1,
            );
            let occurrence =
                echod_concrete::node::spec_occurrence_transition(
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
                occurrence.0,
                echod_concrete::node::spec_body_deadline(occurrence.0),
                at,
                None,
            );
            let advanced = crate::handler_docs::spec_commit_advance(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& context.t1 <= at
            &&& at <= echod_types::MAX_TIME
            &&& core_retained_append_certificates(store, advanced.0)
            &&& retained_commit_provenance(advanced.0)
            &&& cache_identity_provenance(advanced.0)
            &&& advanced.2 is Issued ==>
                phase_append_certificates(
                    store,
                    advanced.0.keys.prefix,
                    crate::handler_docs::PhaseSpec::FireOrigin {
                        commit: advanced.1,
                        ctx: context,
                        t: at,
                        outbox: crate::handler_docs::spec_dispatches(
                            occurrence.0,
                            occurrence.1,
                        ),
                    },
                )
            &&& !(advanced.2 is Issued) ==> {
                &&& crate::global_store_control::
                    detached_flight_control(
                        advanced.0,
                        flight.id,
                    )
                &&& crate::global_store_lane::
                    detached_flight_owns_primary(
                        advanced.0,
                        flight,
                    )
                &&& advanced.0.flights.slots.contains_key(secondary)
                &&& advanced.0.flights.slots[secondary].busy
                    == Some(flight.id)
            }
        }),
{
    lemma_prepare_fire_run_commit_candidate(
        state,
        flight,
        context,
        working,
    );
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
    lemma_core_retained_append_certificates_frame(
        store,
        state,
        noted,
    );
    let committed = crate::handler_docs::spec_commit_new(
        noted,
        working,
        after,
        echod_concrete::node::spec_body_deadline(after),
        at,
        None,
    );
    assert(committed.1.w.loaded == working.loaded) by {
        reveal(crate::handler_docs::spec_commit_new);
    };
    lemma_initial_commit_advance_preserves_core_retained_append_certificates(
        committed.0,
        flight.id,
        committed.1,
        store,
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
    let advanced = crate::handler_docs::spec_commit_advance(
        committed.0,
        flight.id,
        committed.1,
        None,
    );
    if advanced.2 is Issued {
        assert(advanced.1.w.loaded == working.loaded) by {
            reveal(crate::handler_docs::spec_commit_advance);
            reveal(crate::handler_docs::spec_allocate_arm_token);
            reveal(crate::verified::flight_spec::spec_advance);
            reveal(crate::handler_docs::spec_issue_write);
            reveal(crate::state::spec_store_certified);
            reveal(crate::state::spec_store_raw);
        };
        assert(phase_append_certificates(
            store,
            advanced.0.keys.prefix,
            crate::handler_docs::PhaseSpec::FireOrigin {
                commit: advanced.1,
                ctx: context,
                t: at,
                outbox: crate::handler_docs::spec_dispatches(
                    occurrence.0,
                    occurrence.1,
                ),
            },
        )) by {
            reveal(phase_append_certificates);
            reveal(commit_loaded_append_certificate);
        };
    } else {
        crate::global_store_control::
            lemma_commit_advance_nonissued_preserves_detached_flight_control(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
        assert(crate::global_store_lane::detached_flight_owns_primary(
            advanced.0,
            flight,
        )) by {
            reveal(
                crate::global_store_lane::detached_flight_owns_primary,
            );
            reveal(crate::state::spec_note);
        };
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_prepare_fire_advance_commit_candidate(
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
                &&& production_core_control_body(noted)
                &&& retained_commit_provenance(noted)
                &&& cache_identity_provenance(noted)
                &&& committed.0 == noted
                &&& committed.1.issued is None
                &&& committed.1.seq.step is Start
                &&& commit_candidate_provenance(
                    committed.0,
                    flight.id,
                    flight.target,
                    committed.1,
                )
            },
            _ => true,
        },
{
    reveal(flight_submission_provenance);
    reveal(submission_provenance);
    match flight.work {
        crate::handler_docs::WorkSpec::Fire {
            schedule,
            fired,
            ..
        } => {
            reveal(fire_context_provenance);
            reveal(working_document_provenance);
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
            assert(retained_commit_provenance(noted)) by {
                reveal(crate::state::spec_note);
                reveal(retained_commit_provenance);
            };
            assert(cache_identity_provenance(noted)) by {
                reveal(crate::state::spec_note);
                reveal(cache_identity_provenance);
            };
            assert(noted.flights.slots.contains_key(
                crate::target::spec_name(flight.target),
            )) by {
                reveal(crate::state::spec_note);
                reveal(
                    crate::global_store_lane::
                        detached_flight_owns_primary,
                );
            };
            crate::global_store_bounds::lemma_stored_body_ids_bounded(
                context.ws.loaded.document,
            );
            crate::global_store_bounds::
                lemma_fire_schedule_preserves_bounded_ids(
                    crate::document::spec_loaded_body(
                        context.ws.loaded,
                    ),
                    context.t1,
                );
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
                reveal(
                    echod_concrete::document::schedule_well_formed,
                );
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
            reveal(crate::handler_docs::spec_commit_new);
            reveal(crate::verified::flight_spec::spec_new);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_prepare_fire_advance_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
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
        loaded_append_certificate(
            store,
            state.keys.prefix,
            context.ws.loaded,
        ),
    ensures
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
                let advanced = crate::handler_docs::spec_commit_advance(
                    committed.0,
                    flight.id,
                    committed.1,
                    None,
                );
                &&& core_retained_append_certificates(store, advanced.0)
                &&& retained_commit_provenance(advanced.0)
                &&& cache_identity_provenance(advanced.0)
                &&& advanced.2 is Issued ==>
                    phase_append_certificates(
                        store,
                        advanced.0.keys.prefix,
                        crate::handler_docs::PhaseSpec::FireSchedule {
                            commit: advanced.1,
                        },
                    )
                &&& !(advanced.2 is Issued) ==> {
                    &&& crate::global_store_control::
                        detached_flight_control(
                            advanced.0,
                            flight.id,
                        )
                    &&& crate::global_store_lane::
                        detached_flight_owns_primary(
                            advanced.0,
                            flight,
                        )
                }
            },
            _ => true,
        },
{
    lemma_prepare_fire_advance_commit_candidate(
        state,
        flight,
        context,
        at,
    );
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
            lemma_core_retained_append_certificates_frame(
                store,
                state,
                noted,
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
            assert(committed.0 == noted) by {
                reveal(crate::handler_docs::spec_commit_new);
            };
            assert(committed.1.issued is None) by {
                reveal(crate::handler_docs::spec_commit_new);
            };
            assert(committed.1.seq.step is Start) by {
                reveal(crate::handler_docs::spec_commit_new);
                reveal(crate::verified::flight_spec::spec_new);
            };
            assert(committed.1.w.loaded
                == context.ws.loaded) by {
                reveal(crate::handler_docs::spec_commit_new);
                reveal(crate::verified::flight_spec::spec_new);
            };
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
            lemma_initial_commit_advance_preserves_core_retained_append_certificates(
                committed.0,
                flight.id,
                committed.1,
                store,
            );
            lemma_detached_initial_commit_advance_preserves_retained_provenance(
                committed.0,
                flight.id,
                flight.target,
                committed.1,
            );
            lemma_commit_advance_frames_keys_and_flights(
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
            if advanced.2 is Issued {
                assert(advanced.1.w.loaded == context.ws.loaded) by {
                    reveal(crate::handler_docs::spec_commit_advance);
                    reveal(crate::handler_docs::spec_allocate_arm_token);
                    reveal(crate::verified::flight_spec::spec_advance);
                    reveal(crate::handler_docs::spec_issue_write);
                    reveal(crate::state::spec_store_certified);
                    reveal(crate::state::spec_store_raw);
                };
                assert(phase_append_certificates(
                    store,
                    advanced.0.keys.prefix,
                    crate::handler_docs::PhaseSpec::FireSchedule {
                        commit: advanced.1,
                    },
                )) by {
                    reveal(phase_append_certificates);
                    reveal(commit_loaded_append_certificate);
                };
            } else {
                crate::global_store_control::
                    lemma_commit_advance_nonissued_preserves_detached_flight_control(
                        committed.0,
                        flight.id,
                        committed.1,
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
                    reveal(crate::state::spec_note);
                };
            }
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_advance_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
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
        loaded_append_certificate(
            store,
            state.keys.prefix,
            context.ws.loaded,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_sched::spec_fire_advance(
                state,
                flight,
                context,
                at,
            ),
        ),
{
    lemma_prepare_fire_advance_append_certificates(
        state,
        flight,
        context,
        at,
        store,
    );
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
            let advanced = crate::handler_docs::spec_commit_advance(
                committed.0,
                flight.id,
                committed.1,
                None,
            );
            match advanced.2 {
                crate::handler_docs::ProgressSpec::Issued => {
                    lemma_inflight_preserves_core_retained_append_certificates(
                        store,
                        advanced.0,
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
                    lemma_core_retained_append_certificates_frame(
                        store,
                        advanced.0,
                        ended,
                    );
                    assert(retained_commit_provenance(ended)) by {
                        reveal(crate::state::spec_note);
                        reveal(retained_commit_provenance);
                    };
                    assert(cache_identity_provenance(ended)) by {
                        reveal(crate::state::spec_note);
                        reveal(cache_identity_provenance);
                    };
                    assert(crate::global_store_control::
                        detached_flight_control(
                            ended,
                            flight.id,
                        )) by {
                        reveal(crate::state::spec_note);
                        reveal(
                            crate::global_store_control::
                                detached_flight_control,
                        );
                    };
                    assert(crate::global_store_lane::
                        detached_flight_owns_primary(
                            ended,
                            flight,
                        )) by {
                        reveal(crate::state::spec_note);
                        reveal(
                            crate::global_store_lane::
                                detached_flight_owns_primary,
                        );
                    };
                    lemma_finish_preserves_core_retained_append_certificates(
                        store,
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
                    lemma_core_retained_append_certificates_frame(
                        store,
                        advanced.0,
                        ended,
                    );
                    assert(retained_commit_provenance(ended)) by {
                        reveal(crate::state::spec_note);
                        reveal(retained_commit_provenance);
                    };
                    assert(cache_identity_provenance(ended)) by {
                        reveal(crate::state::spec_note);
                        reveal(cache_identity_provenance);
                    };
                    assert(crate::global_store_control::
                        detached_flight_control(
                            ended,
                            flight.id,
                        )) by {
                        reveal(crate::state::spec_note);
                        reveal(
                            crate::global_store_control::
                                detached_flight_control,
                        );
                    };
                    assert(crate::global_store_lane::
                        detached_flight_owns_primary(
                            ended,
                            flight,
                        )) by {
                        reveal(crate::state::spec_note);
                        reveal(
                            crate::global_store_lane::
                                detached_flight_owns_primary,
                        );
                    };
                    lemma_commit_failed_preserves_core_retained_append_certificates(
                        store,
                        ended,
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
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_loading_origin_preserves_core_retained_append_certificates(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    revalidating: Option<crate::cache::CachedSpec>,
    context: crate::handler_docs::FireCtxSpec,
    response: echod_concrete::store::StoreRes,
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
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& state.flights.slots.contains_key(secondary)
            &&& state.flights.slots[secondary].busy == Some(flight.id)
        }),
        match revalidating {
            Some(cached) =>
                cached_append_certificate(
                    store,
                    state.keys.prefix,
                    cached,
                ),
            None => true,
        },
        loaded_append_certificate(
            store,
            state.keys.prefix,
            context.ws.loaded,
        ),
        context.ws.key == document_key(
            state.keys.prefix,
            context.ws.loaded.document,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_answered_fire_loading_origin(
                state,
                flight,
                revalidating,
                context,
                response,
            ),
        ),
{
    lemma_loaded_origin_preserves_core_retained_append_certificates(
        state,
        context.origin,
        revalidating,
        response,
        store,
    );
    lemma_loaded_origin_success_has_provenance(
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
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    assert(loaded.0.flights == state.flights) by {
        reveal(crate::handler_docs::spec_loaded_origin);
        reveal(crate::state::spec_remember);
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
    };
    assert(loaded.0.keys == state.keys) by {
        reveal(crate::handler_docs::spec_loaded_origin);
        reveal(crate::state::spec_remember);
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
    };
    assert(retained_commit_provenance(loaded.0)) by {
        reveal(crate::handler_docs::spec_loaded_origin);
        reveal(crate::state::spec_remember);
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(loaded.0)) by {
        reveal(crate::handler_docs::spec_loaded_origin);
        reveal(crate::state::spec_remember);
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        loaded.0,
        flight,
    )) by {
        reveal(crate::handler_docs::spec_loaded_origin);
        reveal(crate::state::spec_remember);
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(crate::global_store_lane::detached_flight_owns_primary);
    };
    match loaded.1 {
        Ok(working) => {
            lemma_fire_run_preserves_core_retained_append_certificates(
                loaded.0,
                flight,
                context,
                working,
                store,
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
            lemma_release_preserves_core_retained_append_certificates(
                store,
                loaded.0,
                secondary,
            );
            crate::global_store_control::
                lemma_release_preserves_detached_flight_control(
                    loaded.0,
                    secondary,
                    flight.id,
                );
            lemma_release_preserves_retained_provenance(
                loaded.0,
                secondary,
            );
            let released = crate::handler_docs::spec_release(
                loaded.0,
                secondary,
            );
            assert(crate::global_store_lane::detached_flight_owns_primary(
                released,
                flight,
            )) by {
                reveal(crate::handler_docs::spec_release);
                reveal(crate::global_store_lane::detached_flight_owns_primary);
            };
            lemma_fail_preserves_core_retained_append_certificates(
                store,
                released,
                flight,
                error,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_fire_loading_origin);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_loading_origin_completion_preserves_core_retained_append_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
        state.flights.inflight[fid].phase is FireLoadingOrigin,
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    lemma_prepare_detached_flight_response_certificates(
        state,
        op,
        fid,
        response,
        store,
    );
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let flight = state.flights.inflight[fid];
    let detached =
        crate::handler_docs::spec_take_flight(consumed, fid);
    let idle = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Idle,
        ..flight
    };
    reveal(crate::handler_docs::spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    match flight.phase {
        crate::handler_docs::PhaseSpec::FireLoadingOrigin {
            revalidating,
            ctx,
            ..
        } => {
            assert(match idle.work {
                crate::handler_docs::WorkSpec::Fire {
                    schedule,
                    ..
                } => fire_context_provenance(
                    detached.keys.prefix,
                    schedule,
                    ctx,
                ),
                _ => false,
            }) by {
                reveal(flight_control_provenance);
            };
            assert(cached_origin_provenance(
                ctx.origin,
                revalidating,
            )) by {
                reveal(flight_control_provenance);
            };
            lemma_answered_fire_loading_origin_preserves_core_retained_append_certificates(
                detached,
                idle,
                revalidating,
                ctx,
                response,
                store,
            );
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_idle_completion_preserves_core_retained_append_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
        state.flights.inflight[fid].phase is FireIdle,
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    lemma_prepare_detached_flight_response_certificates(
        state,
        op,
        fid,
        response,
        store,
    );
    let certificate = state.store_certificates[op];
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let flight = state.flights.inflight[fid];
    let detached =
        crate::handler_docs::spec_take_flight(consumed, fid);
    let idle = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Idle,
        ..flight
    };
    reveal(crate::handler_docs::spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    match flight.phase {
        crate::handler_docs::PhaseSpec::FireIdle { commit } => {
            lemma_answered_fire_idle_preserves_core_retained_append_certificates(
                detached,
                fid,
                idle,
                commit,
                response,
                store,
                certificate,
            );
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_noted_finish_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    note: crate::types::NoteSpec,
    fired: crate::types::Fired,
)
    requires
        production_core_control_body(state),
        flight.id == fid,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        crate::global_store_control::detached_flight_control(state, fid),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
    ensures
        ({
            let ended = crate::state::spec_note(state, note);
            let noted = crate::state::spec_note(
                ended,
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            );
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_finish(
                    noted,
                    flight,
                    Ok(fired),
                ),
            )
        }),
{
    let ended = crate::state::spec_note(state, note);
    let commit_note = crate::types::NoteSpec::Commit(
        crate::types::CommitOutcome::Committed,
    );
    let noted = crate::state::spec_note(ended, commit_note);
    lemma_note_preserves_core_control_body(state, note);
    lemma_note_preserves_retained_provenance(state, note);
    lemma_note_preserves_core_control_body(ended, commit_note);
    lemma_note_preserves_retained_provenance(ended, commit_note);
    lemma_core_retained_append_certificates_frame(store, state, noted);
    assert(cache_identity_provenance(noted)) by {
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    assert(crate::global_store_control::detached_flight_control(
        noted,
        fid,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_control::detached_flight_control);
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        noted,
        flight,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_lane::detached_flight_owns_primary);
    };
    let primary = crate::target::spec_name(flight.target);
    assert(crate::production_relation::flight_lanes_consistent(
        noted.flights,
    )) by {
        reveal(production_core_control_body);
    };
    assert(crate::global_store_lane::secondary_flight_lanes_consistent(
        noted,
    )) by {
        reveal(production_core_control_body);
    };
    crate::global_store_lane::lemma_detached_busy_owner_leaves_lane_unowned(
        noted.flights,
        primary,
        flight.id,
    );
    crate::global_store_lane::
        lemma_detached_busy_owner_leaves_secondary_lane_unowned(
            noted,
            primary,
            flight.id,
        );
    lemma_finish_preserves_core_retained_append_certificates(
        store,
        noted,
        flight,
        Ok(fired),
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_noted_commit_failed_preserves_core_retained_append_certificates(
    store: StoreV,
    state: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    note: crate::types::NoteSpec,
    error: echod_concrete::store::StoreErrorSpec,
)
    requires
        production_core_control_body(state),
        flight.id == fid,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        crate::global_store_control::detached_flight_control(state, fid),
        crate::global_store_lane::detached_flight_owns_primary(
            state,
            flight,
        ),
    ensures
        ({
            let noted = crate::state::spec_note(state, note);
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_commit_failed(
                    noted,
                    flight,
                    error,
                ),
            )
        }),
{
    let noted = crate::state::spec_note(state, note);
    lemma_note_preserves_core_control_body(state, note);
    lemma_note_preserves_retained_provenance(state, note);
    lemma_core_retained_append_certificates_frame(store, state, noted);
    assert(cache_identity_provenance(noted)) by {
        reveal(crate::state::spec_note);
        reveal(cache_identity_provenance);
    };
    assert(crate::global_store_control::detached_flight_control(
        noted,
        fid,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_control::detached_flight_control);
    };
    assert(crate::global_store_lane::detached_flight_owns_primary(
        noted,
        flight,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::global_store_lane::detached_flight_owns_primary);
    };
    lemma_commit_failed_preserves_core_retained_append_certificates(
        store,
        noted,
        flight,
        error,
    );
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_origin_preserves_core_retained_append_certificates(
    detached: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    context: crate::handler_docs::FireCtxSpec,
    at: u64,
    outbox: Seq<(Seq<char>, crate::types::MessageSpec)>,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
    certificate: StoreEffectCertificateV,
)
    requires
        production_core_control_body(detached),
        flight.id == fid,
        retained_commit_provenance(detached),
        cache_identity_provenance(detached),
        core_retained_append_certificates(store, detached),
        crate::global_store_control::detached_flight_control(detached, fid),
        crate::global_store_lane::detached_flight_owns_primary(
            detached,
            flight,
        ),
        ({
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            );
            &&& detached.flights.slots.contains_key(secondary)
            &&& detached.flights.slots[secondary].busy == Some(fid)
        }),
        flight_submission_provenance(flight),
        match flight.work {
            crate::handler_docs::WorkSpec::Fire { schedule, .. } =>
                fire_context_provenance(
                    detached.keys.prefix,
                    schedule,
                    context,
                ),
            _ => false,
        },
        context.t1 <= at,
        at <= echod_types::MAX_TIME,
        loaded_append_certificate(
            store,
            detached.keys.prefix,
            context.ws.loaded,
        ),
        commit_candidate_provenance(
            detached,
            fid,
            crate::target::TargetSpec::Origin(context.origin),
            commit,
        ),
        commit.issued is Some,
        certificate_belongs_to_commit(certificate, commit),
        response_certificate_ready(
            store,
            detached.keys.prefix,
            response,
            certificate,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_answered_fire_origin(
                detached,
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
    lemma_answered_commit_advance_preserves_core_retained_append_certificates(
        detached,
        fid,
        commit,
        response,
        store,
        certificate,
    );
    lemma_detached_commit_advance_preserves_retained_provenance(
        detached,
        fid,
        crate::target::TargetSpec::Origin(context.origin),
        commit,
        response,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        detached,
        fid,
        commit,
        Some(response),
    );
    lemma_commit_advance_frames_keys_and_flights(
        detached,
        fid,
        commit,
        Some(response),
    );
    let secondary = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    assert(advanced.0.flights == detached.flights);
    assert(advanced.0.flights.slots.contains_key(secondary));
    assert(advanced.0.flights.slots[secondary].busy == Some(flight.id));
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            assert(phase_append_certificates(
                store,
                advanced.0.keys.prefix,
                crate::handler_docs::PhaseSpec::FireOrigin {
                    commit: advanced.1,
                    ctx: context,
                    t: at,
                    outbox,
                },
            )) by {
                reveal(phase_append_certificates);
                reveal(commit_loaded_append_certificate);
                reveal(crate::handler_docs::spec_commit_advance);
                reveal(crate::handler_docs::spec_answered);
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
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            assert(crate::global_store_lane::detached_flight_owns_primary(
                advanced.0,
                flight,
            )) by {
                reveal(crate::global_store_lane::detached_flight_owns_primary);
                lemma_commit_advance_frames_keys_and_flights(
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            };
            lemma_fire_origin_done_tail_preserves_core_retained_append_certificates(
                advanced.0,
                flight,
                context,
                at,
                outbox,
                store,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            assert(crate::global_store_lane::detached_flight_owns_primary(
                advanced.0,
                flight,
            )) by {
                reveal(crate::global_store_lane::detached_flight_owns_primary);
                lemma_commit_advance_frames_keys_and_flights(
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            };
            lemma_fire_origin_failed_tail_preserves_core_retained_append_certificates(
                advanced.0,
                flight,
                context,
                error,
                store,
            );
        },
        crate::handler_docs::ProgressSpec::Exhausted => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            assert(crate::global_store_lane::detached_flight_owns_primary(
                advanced.0,
                flight,
            )) by {
                reveal(
                    crate::global_store_lane::
                        detached_flight_owns_primary,
                );
            };
            lemma_fire_origin_exhausted_tail_preserves_core_retained_append_certificates(
                advanced.0,
                flight,
                context,
                store,
            );
        },
    }
    reveal(crate::handler_docs::spec_answered_fire_origin);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_answered_fire_schedule_preserves_core_retained_append_certificates(
    detached: S,
    fid: u64,
    flight: crate::handler_docs::FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
    certificate: StoreEffectCertificateV,
)
    requires
        production_core_control_body(detached),
        flight.id == fid,
        retained_commit_provenance(detached),
        cache_identity_provenance(detached),
        core_retained_append_certificates(store, detached),
        crate::global_store_control::detached_flight_control(detached, fid),
        crate::global_store_lane::detached_flight_owns_primary(
            detached,
            flight,
        ),
        commit_candidate_provenance(
            detached,
            fid,
            flight.target,
            commit,
        ),
        commit.issued is Some,
        certificate_belongs_to_commit(certificate, commit),
        response_certificate_ready(
            store,
            detached.keys.prefix,
            response,
            certificate,
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler_docs::spec_answered_fire_schedule(
                detached,
                fid,
                flight,
                commit,
                response,
            ),
        ),
{
    lemma_answered_commit_advance_preserves_core_retained_append_certificates(
        detached,
        fid,
        commit,
        response,
        store,
        certificate,
    );
    lemma_detached_commit_advance_preserves_retained_provenance(
        detached,
        fid,
        flight.target,
        commit,
        response,
    );
    let advanced = crate::handler_docs::spec_commit_advance(
        detached,
        fid,
        commit,
        Some(response),
    );
    match advanced.2 {
        crate::handler_docs::ProgressSpec::Issued => {
            assert(phase_append_certificates(
                store,
                advanced.0.keys.prefix,
                crate::handler_docs::PhaseSpec::FireSchedule {
                    commit: advanced.1,
                },
            )) by {
                reveal(phase_append_certificates);
                reveal(commit_loaded_append_certificate);
                reveal(crate::handler_docs::spec_commit_advance);
                reveal(crate::handler_docs::spec_answered);
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
                    phase: crate::handler_docs::PhaseSpec::FireSchedule {
                        commit: advanced.1,
                    },
                    ..flight
                },
            );
        },
        crate::handler_docs::ProgressSpec::Done(fired) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            assert(crate::global_store_lane::detached_flight_owns_primary(
                advanced.0,
                flight,
            )) by {
                reveal(crate::global_store_lane::detached_flight_owns_primary);
                lemma_commit_advance_frames_keys_and_flights(
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            };
            lemma_noted_finish_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                fid,
                flight,
                crate::types::NoteSpec::AdvanceEnd {
                    flight: fid,
                    committed: true,
                },
                fired,
            );
        },
        crate::handler_docs::ProgressSpec::Failed(error) => {
            crate::global_store_control::
                lemma_commit_advance_nonissued_preserves_detached_flight_control(
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            assert(crate::global_store_lane::detached_flight_owns_primary(
                advanced.0,
                flight,
            )) by {
                reveal(crate::global_store_lane::detached_flight_owns_primary);
                lemma_commit_advance_frames_keys_and_flights(
                    detached,
                    fid,
                    commit,
                    Some(response),
                );
            };
            lemma_noted_commit_failed_preserves_core_retained_append_certificates(
                store,
                advanced.0,
                fid,
                flight,
                crate::types::NoteSpec::AdvanceEnd {
                    flight: fid,
                    committed: false,
                },
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
    reveal(crate::handler_docs::spec_answered_fire_schedule);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_continuation_completion_preserves_core_retained_append_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
        ({
            let phase = state.flights.inflight[fid].phase;
            phase is FireOrigin
                || phase is FireSchedule
        }),
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    lemma_prepare_detached_flight_response_certificates(
        state,
        op,
        fid,
        response,
        store,
    );
    let certificate = state.store_certificates[op];
    let consumed = S {
        ops: state.ops.remove(op),
        store_requests: state.store_requests.remove(op),
        store_certificates: state.store_certificates.remove(op),
        ..state
    };
    let flight = state.flights.inflight[fid];
    let detached =
        crate::handler_docs::spec_take_flight(consumed, fid);
    let idle = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Idle,
        ..flight
    };
    reveal(crate::handler_docs::spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    match flight.phase {
        crate::handler_docs::PhaseSpec::FireOrigin {
            commit,
            ctx,
            t,
            outbox,
        } => {
            lemma_answered_fire_origin_preserves_core_retained_append_certificates(
                detached,
                fid,
                idle,
                commit,
                ctx,
                t,
                outbox,
                response,
                store,
                certificate,
            );
        },
        crate::handler_docs::PhaseSpec::FireSchedule { commit } => {
            lemma_answered_fire_schedule_preserves_core_retained_append_certificates(
                detached,
                fid,
                idle,
                commit,
                response,
                store,
                certificate,
            );
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_flight_store_completion_preserves_core_retained_append_certificates(
    state: S,
    op: u64,
    fid: u64,
    response: echod_concrete::store::StoreRes,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.ops[op] == Owner::Flight(fid),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
    ensures
        ({
            let consumed = S {
                ops: state.ops.remove(op),
                store_requests: state.store_requests.remove(op),
                store_certificates: state.store_certificates.remove(op),
                ..state
            };
            core_retained_append_certificates(
                store,
                crate::handler_docs::spec_flight_completed(
                    consumed,
                    fid,
                    op,
                    response,
                ),
            )
        }),
{
    assert(state.flights.inflight.contains_key(fid)) by {
        reveal(production_core_control_body);
        reveal(active_flight_owners_match_phase);
    };
    let phase = state.flights.inflight[fid].phase;
    match phase {
        crate::handler_docs::PhaseSpec::Loading { .. } => {
            lemma_loading_flight_completion_preserves_core_retained_append_certificates(
                state,
                op,
                fid,
                response,
                store,
            );
        },
        crate::handler_docs::PhaseSpec::Origin { .. } => {
            lemma_origin_flight_completion_preserves_core_retained_append_certificates(
                state,
                op,
                fid,
                response,
                store,
            );
        },
        crate::handler_docs::PhaseSpec::Schedule { .. } => {
            lemma_schedule_flight_completion_preserves_core_retained_append_certificates(
                state,
                op,
                fid,
                response,
                store,
            );
        },
        crate::handler_docs::PhaseSpec::Idle => {
            assert(false) by {
                reveal(production_core_control_body);
                reveal(active_flight_owners_match_phase);
            };
        },
        crate::handler_docs::PhaseSpec::FireLoadingSchedule { .. } => {
            lemma_fire_loading_schedule_completion_preserves_core_retained_append_certificates(
                state,
                op,
                fid,
                response,
                store,
            );
        },
        crate::handler_docs::PhaseSpec::FireLoadingOrigin { .. } => {
            lemma_fire_loading_origin_completion_preserves_core_retained_append_certificates(
                state,
                op,
                fid,
                response,
                store,
            );
        },
        crate::handler_docs::PhaseSpec::FireIdle { .. } => {
            lemma_fire_idle_completion_preserves_core_retained_append_certificates(
                state,
                op,
                fid,
                response,
                store,
            );
        },
        crate::handler_docs::PhaseSpec::FireOrigin { .. }
        | crate::handler_docs::PhaseSpec::FireSchedule { .. } => {
            lemma_fire_continuation_completion_preserves_core_retained_append_certificates(
                state,
                op,
                fid,
                response,
                store,
            );
        },
        _ => {
            assert(false) by {
                reveal(production_core_control_body);
                reveal(active_flight_owners_match_phase);
            };
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_store_event_preserves_core_retained_append_certificates(
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
    clock: u64,
    store: StoreV,
)
    requires
        production_core_control_body(state),
        state.out.len() == 0,
        retained_commit_provenance(state),
        cache_identity_provenance(state),
        core_retained_append_certificates(store, state),
        state.ops.contains_key(op),
        state.store_certificates.contains_key(op),
        response_certificate_ready(
            store,
            state.keys.prefix,
            response,
            state.store_certificates[op],
        ),
    ensures
        core_retained_append_certificates(
            store,
            crate::handler::spec_on_known_event(
                state,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock,
                },
            ).0,
        ),
{
    let prepared = S { clock, ..state };
    assert(production_core_control_body(prepared)) by {
        reveal(production_core_control_body);
    };
    assert(retained_commit_provenance(prepared)) by {
        reveal(retained_commit_provenance);
    };
    assert(cache_identity_provenance(prepared)) by {
        reveal(cache_identity_provenance);
    };
    assert(core_retained_append_certificates(store, prepared)) by {
        reveal(core_retained_append_certificates);
    };
    let owner = prepared.ops[op];
    let certificate = prepared.store_certificates[op];
    let consumed = S {
        ops: prepared.ops.remove(op),
        store_requests: prepared.store_requests.remove(op),
        store_certificates: prepared.store_certificates.remove(op),
        ..prepared
    };
    lemma_consume_active_store_operation_preserves_core_control_body(
        prepared,
        op,
    );
    assert(core_retained_append_certificates(store, consumed)) by {
        reveal(core_retained_append_certificates);
    };
    let completed = match owner {
        Owner::Flight(fid) =>
            crate::handler_docs::spec_flight_completed(
                consumed,
                fid,
                op,
                response,
            ),
        Owner::Members =>
            crate::handler_node::spec_members_completed(
                consumed,
                op,
                response,
            ),
        Owner::Timers =>
            crate::handler_timers::spec_timers_completed(
                consumed,
                op,
                response,
            ),
        Owner::Debug =>
            crate::debug::spec_debug_completed(
                consumed,
                op,
                response,
            ),
        Owner::Ignored => consumed,
    };
    match owner {
        Owner::Flight(fid) => {
            lemma_flight_store_completion_preserves_core_retained_append_certificates(
                prepared,
                op,
                fid,
                response,
                store,
            );
            lemma_flight_completed_preserves_keys(
                consumed,
                fid,
                op,
                response,
            );
        },
        Owner::Members => {
            lemma_members_completed_extends_store_certificates(
                consumed,
                op,
                response,
            );
            lemma_members_completed_preserves_core_retained_append_certificates(
                store,
                consumed,
                op,
                response,
            );
        },
        Owner::Timers => {
            lemma_timers_completed_extends_store_certificates(
                consumed,
                op,
                response,
            );
            lemma_timers_completed_preserves_core_retained_append_certificates(
                store,
                consumed,
                op,
                response,
            );
        },
        Owner::Ignored => {
            assert(completed == consumed);
        },
        Owner::Debug => {
            assert(false) by {
                reveal(production_core_control_body);
            };
        },
    }
    assert(completed.keys.prefix == prepared.keys.prefix);
    let scheduled = crate::handler::spec_schedule_wake(completed);
    assert(scheduled.keys.prefix == completed.keys.prefix) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    assert(scheduled.cache.entries == completed.cache.entries) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    assert(scheduled.flights.inflight
        == completed.flights.inflight) by {
        reveal(crate::handler::spec_schedule_wake);
        reveal(crate::state::spec_emit);
    };
    lemma_core_retained_append_certificates_frame(
        store,
        completed,
        scheduled,
    );
    let handled = crate::handler::spec_on_known_event(
        state,
        crate::types::EventSpec::Store {
            op,
            response,
            clock,
        },
    );
    assert(handled.0.keys.prefix == scheduled.keys.prefix) by {
        reveal(crate::handler::spec_on_known_event);
        reveal(crate::handler::spec_dispatch_known_event);
    };
    assert(handled.0.cache.entries == scheduled.cache.entries) by {
        reveal(crate::handler::spec_on_known_event);
        reveal(crate::handler::spec_dispatch_known_event);
        reveal(crate::handler::spec_freeze_active_store_certificates);
    };
    assert(handled.0.flights.inflight
        == scheduled.flights.inflight) by {
        reveal(crate::handler::spec_on_known_event);
        reveal(crate::handler::spec_dispatch_known_event);
        reveal(crate::handler::spec_freeze_active_store_certificates);
    };
    lemma_core_retained_append_certificates_frame(
        store,
        scheduled,
        handled.0,
    );
    reveal(crate::handler::spec_on_known_event);
    reveal(crate::handler::spec_dispatch_known_event);
    reveal(crate::handler::spec_freeze_active_store_certificates);
}

}
