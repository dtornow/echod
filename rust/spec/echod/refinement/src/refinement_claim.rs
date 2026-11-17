//! Component claims and unfinished global Echod trace refinement.
//! See DOCUMENT_SEMANTICS.md for the merge hold and verification boundaries.

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]
#![allow(non_shorthand_field_patterns)]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_abstract_spec::{Config as AbstractConfig, Spec as AbstractSpec};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::{Config as ConcreteConfig, Spec as ConcreteSpec};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::RoverSpec::refinement::refines;

verus! {
pub open spec fn public_admission_agrees(
    target: echod_concrete_spec::state::ProductionTargetV, request: echod_types::Request,
) -> bool {
    let normalized = echod_concrete_spec::handler::production_normalize_admission(target, request);
    match echod_abstract_spec::handler::spec_detached_admission(request) {
        None => normalized == (target, request, None),
        Some((create, check)) => normalized == (
            echod_concrete_spec::state::ProductionTargetV::Origin(echod_types::origin(create.id@)),
            echod_types::Request::PromiseCreate(create),
            Some((echod_concrete_spec::state::ProductionTargetV::Origin(echod_types::origin(check.id@)),
                echod_types::Request::TaskFenceCheck(check))),
        ),
    }
}

pub open spec fn accepted_document_validator_body(
    store: echod_concrete_spec::state::StoreV, request: echod_concrete_spec::StoreReq,
) -> Option<Seq<u8>> {
    use echod_concrete_spec::StoreReq;
    use echod_concrete_spec::handler::{spec_find, spec_etag};
    match request {
        StoreReq::GetIfNoneMatch { key, etag } | StoreReq::PutIfMatch { key, etag, .. } =>
            match spec_find(store.entries, key@, 0) {
                Some(i) if spec_etag(store.entries[i].body) == etag => Some(store.entries[i].body),
                _ => None,
            },
        StoreReq::AppIfMatch { key, etag, offset, .. } =>
            if store.appendable {
                match spec_find(store.entries, key@, 0) {
                    Some(i) if spec_etag(store.entries[i].body) == etag && store.entries[i].body.len() == offset =>
                        Some(store.entries[i].body),
                    _ => None,
                }
            } else { None },
        _ => None,
    }
}

/// Conditional theorem premise for an issued document operation and its captured
/// snapshot, not a hash axiom or an established backend guarantee. Same-body ABA
/// is allowed; failed comparisons and unrelated operations impose no condition.
/// The caller must bind the snapshot to read provenance. This premise is unproved
/// for the FNV store and is not a guarantee supplied by the S3 adapter.
pub open spec fn document_validator_separation(
    store: echod_concrete_spec::state::StoreV, request: echod_concrete_spec::StoreReq, captured: Seq<u8>,
) -> bool {
    match accepted_document_validator_body(store, request) {
        None => true,
        Some(current) => current == captured,
    }
}

pub open spec fn network_permutation<M: rover_spec::rover::RoverSpec::Spec>(
    left: rover_spec::rover::RoverSpec::State<M>,
    right: rover_spec::rover::RoverSpec::State<M>,
) -> bool {
    &&& left.process == right.process
    &&& left.now == right.now
    &&& left.network.to_multiset() == right.network.to_multiset()
}

pub open spec fn admitted_operation_time(offered: u64, pinned: bool, fleet_at: u64) -> u64 {
    if pinned || offered > fleet_at { offered } else { fleet_at }
}

pub open spec fn effective_document_time(admitted: u64, committed: u64) -> u64 {
    if committed > admitted { committed } else { admitted }
}

pub open spec fn public_work_time_agrees(
    state: echod_concrete_spec::state::ProductionStateV,
    call: echod_concrete_spec::state::ProductionCallV,
) -> bool {
    let stage = match call.then {
        None => echod_concrete_spec::state::ProductionStageV::Whole,
        Some((then, check)) => echod_concrete_spec::state::ProductionStageV::Detached { then, check: Some(check) },
    };
    echod_concrete_spec::handler::production_handler_spec_request(state, call)
        == echod_concrete_spec::handler::production_handler_docs_spec_submit(state, call.target,
            echod_concrete_spec::state::ProductionWorkV::Request {
                id: call.id, kind: call.kind, corr: call.corr, req: call.request, action_kind: call.action_kind,
                now: admitted_operation_time(call.now, call.pinned, state.node.fleet_at), stage,
            }, None, false)
}

pub open spec fn timed_admission_matches(
    target: echod_concrete_spec::state::ProductionTargetV,
    call: echod_types::protocol::TimedCall, fleet_at: u64,
) -> bool {
    let work = echod_abstract_spec::handler::spec_admit_timed(call, fleet_at);
    &&& work.admitted_at == admitted_operation_time(call.offered_at, call.pinned, fleet_at)
    &&& echod_abstract_spec::handler::spec_timed_request(work)
        == echod_concrete_spec::handler::production_normalize_admission(target, call.call.request).1
}

pub open spec fn detached_submission_preserves_saved_time(
    state: echod_concrete_spec::state::ProductionStateV,
    flight: echod_concrete_spec::state::ProductionFlightV,
    done: echod_concrete_spec::state::ProductionDoneV,
    fired: echod_types::ProductionFired,
) -> bool {
    match (flight.work, done.response) {
        (echod_concrete_spec::state::ProductionWorkV::Request {
            id, kind, corr, action_kind, now,
            stage: echod_concrete_spec::state::ProductionStageV::Detached { then, check: Some(check) }, ..
        }, Some(echod_types::spec::AResponse::Promise(inner))) => {
            let notified = echod_concrete_spec::handler::production_handler_docs_spec_send_all(
                echod_concrete_spec::handler::production_state_spec_note(state,
                    echod_concrete_spec::state::ProductionNoteV::Commit(echod_types::ProductionCommitOutcome::Committed)),
                done.outbox);
            let submitted = echod_concrete_spec::handler::production_handler_docs_spec_submit(notified, then,
                echod_concrete_spec::state::ProductionWorkV::Request {
                    id, kind, corr, action_kind, now, req: check,
                    stage: echod_concrete_spec::state::ProductionStageV::Check { inner: Some(inner) },
                }, None, flight.debug);
            echod_concrete_spec::handler::production_handler_docs_spec_committed(state, flight, done, fired)
                == echod_concrete_spec::handler::production_handler_docs_spec_finish(submitted,
                    echod_concrete_spec::state::ProductionFlightV { idle: !done.did, ..flight }, Ok(fired))
        },
        _ => true,
    }
}


/// Every concrete boundary trace is an abstract boundary trace, with the
/// concrete retry timeout mapped directly into the abstract configuration.
pub open spec fn concrete_refines_abstract(concrete_config: ConcreteConfig) -> bool {
    refines(
        ConcreteSpec,
        concrete_config,
        AbstractSpec,
        AbstractConfig {
            retry_timeout: concrete_config.retry_timeout,
        },
    )
}

} // verus!

mod refinement_proof;

#[cfg(verus_keep_ghost)]
pub use refinement_proof::{refinement_proof, public_admission_proof, work_admission_proof, document_time_proof, timed_admission_proof, detached_submission_time_proof};
