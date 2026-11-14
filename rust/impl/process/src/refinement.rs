//! Formal boundary between the production process and the abstract Rover
//! service.
//!
//! This module does not replace either machine.  It gives the production
//! `StateSpec` a small Rover-style shell: an `EventSpec` is delivered, the
//! resulting `EffectSpec`s are interpreted, store calls remain pending until
//! their matching completion, and replies/sends become boundary observations.
//! The relation below names every production component which can affect a
//! simulation: membership, timers, cache, document flights, pending store
//! calls, and the abstract pending-work queue.
//!
//! The proved part is deliberately narrower than the relation:
//!
//! * the initial production/abstract states are related;
//! * effect interpretation records Store/Reply/Send/Wake effects exactly;
//! * a matching successful Store completion consumes exactly its pending call;
//! * a normal atomic request preserves the stored-document invariant and its
//!   Reply/Send effects are exactly the endpoint delta.
//!
//! The last theorem intentionally reuses the two document theorems on which a
//! full process simulation must rest:
//! `quick_n_dirty::request_preserves_well_formed` and
//! `effects::lemma_request_transition_effects`.
//!
//! Failure, racing-CAS, detached two-document requests, concurrent flights,
//! membership refresh, and timer/fire steps are represented by the state and
//! classified by [`open_case`], but no refinement theorem is claimed for them.
//! There are no admits or axioms in this module.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::cache::CacheSpec;
#[cfg(verus_keep_ghost)]
use crate::config::ConfigSpec;
#[cfg(verus_keep_ghost)]
use crate::document::spec_loaded_body;
#[cfg(verus_keep_ghost)]
use crate::handler::spec_on_event;
#[cfg(verus_keep_ghost)]
use crate::handler_docs::{
    CommittingSpec, DoneSpec, FlightSpec, FlightsSpec, IssuedSpec,
    PhaseSpec, ProgressSpec, WorkingSpec,
};
#[cfg(verus_keep_ghost)]
use crate::state::{spec_state_new, Owner, S};
#[cfg(verus_keep_ghost)]
use crate::state_timers::{spec_slot_before, TimersSpec};
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;
#[cfg(verus_keep_ghost)]
use crate::types::{AnswerSpec, Armed, EffectSpec, EventSpec, MessageSpec, OpId};

#[cfg(verus_keep_ghost)]
use echod_abstract::model::{empty_store, StateV as AbstractStateV};
#[cfg(verus_keep_ghost)]
use echod_abstract::view::StoreV as AbstractStoreV;
#[cfg(verus_keep_ghost)]
use echod_abstract::ServerConfig;
#[cfg(verus_keep_ghost)]
use echod_concrete::document::{well_formed, StoredDocumentV};
#[cfg(verus_keep_ghost)]
use echod_concrete::effects::{
    effects_match, lemma_request_transition_effects, safe_effect_config,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::handlers::lemma_request_agrees;
#[cfg(verus_keep_ghost)]
use echod_concrete::interpret::{
    doc_rel, finite_store, origin_prefix, request_agrees, schedule_prefix,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::node::{spec_stored_body, REQUEST_SWEEP_STEPS};
#[cfg(verus_keep_ghost)]
use echod_concrete::quick_n_dirty::{on_request, request_preserves_well_formed, routed};
#[cfg(verus_keep_ghost)]
use echod_concrete::store::{StoreReqSpec, StoreRes};
#[cfg(verus_keep_ghost)]
use echod_types::{Request, MAX_TIME};

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// A Rover-style shell around StateSpec/EventSpec/EffectSpec
// ---------------------------------------------------------------------------

/// A Store effect which has left the core and has not yet completed.
pub ghost struct PendingStoreV {
    pub request: StoreReqSpec,
    /// The owner recorded by `StateSpec::ops` when the effect was emitted.
    pub owner: Option<Owner>,
}

/// The production boundary. Store calls, wakes, and notes are hidden.
pub ghost enum BoundaryObservationV {
    Reply {
        id: u64,
        response: Result<AnswerSpec, Seq<char>>,
    },
    Send {
        address: Seq<char>,
        message: MessageSpec,
    },
}

/// State of the production core together with the runtime bookkeeping needed
/// to interpret its effects as a Rover process.
pub ghost struct ProcessV {
    pub core: S,
    pub pending_store: Map<OpId, PendingStoreV>,
    pub completed_store: Set<OpId>,
    pub boundary: Seq<BoundaryObservationV>,
    /// The currently requested physical wake. A later Wake effect replaces it.
    pub wake: Option<(u64, Armed)>,
}

pub open spec fn initial_process(cfg: ConfigSpec) -> ProcessV {
    ProcessV {
        core: spec_state_new(cfg),
        pending_store: Map::empty(),
        completed_store: Set::empty(),
        boundary: Seq::empty(),
        wake: None,
    }
}

/// Interpret one effect. This is the formal counterpart of the impure
/// runtime's effect match.
pub open spec fn apply_effect(p: ProcessV, effect: EffectSpec) -> ProcessV {
    match effect {
        EffectSpec::Store { op, request } => {
            let owner = if p.core.ops.contains_key(op) {
                Some(p.core.ops[op])
            } else {
                None
            };
            ProcessV {
                pending_store: p.pending_store.insert(
                    op,
                    PendingStoreV { request, owner },
                ),
                ..p
            }
        },
        EffectSpec::Reply { id, response } => ProcessV {
            boundary: p.boundary.push(BoundaryObservationV::Reply {
                id,
                response,
            }),
            ..p
        },
        EffectSpec::Send { address, message } => ProcessV {
            boundary: p.boundary.push(BoundaryObservationV::Send {
                address,
                message,
            }),
            ..p
        },
        EffectSpec::Wake { after_ms, armed } => ProcessV {
            wake: Some((after_ms, armed)),
            ..p
        },
        EffectSpec::Note(_) => p,
    }
}

pub open spec fn apply_effects(
    p: ProcessV,
    effects: Seq<EffectSpec>,
) -> ProcessV
    decreases effects.len(),
{
    if effects.len() == 0 {
        p
    } else {
        apply_effects(apply_effect(p, effects[0]), effects.drop_first())
    }
}

/// The visible projection of an effect sequence.
pub open spec fn observe_effects(
    effects: Seq<EffectSpec>,
) -> Seq<BoundaryObservationV>
    decreases effects.len(),
{
    if effects.len() == 0 {
        Seq::empty()
    } else {
        let tail = observe_effects(effects.drop_first());
        match effects[0] {
            EffectSpec::Reply { id, response } =>
                seq![BoundaryObservationV::Reply { id, response }] + tail,
            EffectSpec::Send { address, message } =>
                seq![BoundaryObservationV::Send { address, message }] + tail,
            _ => tail,
        }
    }
}

/// Account for the runtime side of a delivered event before the core sees it.
/// A Store completion consumes the pending call with the same op. A physical
/// wake consumes the wake it delivers. Requests change no runtime bookkeeping.
pub open spec fn accept_event(p: ProcessV, event: EventSpec) -> ProcessV {
    match event {
        EventSpec::Store { op, .. } => ProcessV {
            pending_store: p.pending_store.remove(op),
            completed_store: p.completed_store.insert(op),
            ..p
        },
        EventSpec::Wake { .. } => ProcessV { wake: None, ..p },
        EventSpec::Request { .. } => p,
    }
}

/// One production-process step. `spec_on_event` is the verified twin of
/// `State::on_event`; this shell only interprets its returned effects.
pub open spec fn process_step(p: ProcessV, event: EventSpec) -> ProcessV {
    let accepted = accept_event(p, event);
    let (next, effects) = spec_on_event(accepted.core, event);
    apply_effects(ProcessV { core: next, ..accepted }, effects)
}

// ---------------------------------------------------------------------------
// Exact effect/bookkeeping facts
// ---------------------------------------------------------------------------

pub proof fn lemma_store_effect_is_pending(
    p: ProcessV,
    op: OpId,
    request: StoreReqSpec,
)
    ensures
        ({
            let next = apply_effect(
                p,
                EffectSpec::Store { op, request },
            );
            &&& next.pending_store.contains_key(op)
            &&& next.pending_store[op].request == request
            &&& next.boundary == p.boundary
            &&& next.completed_store == p.completed_store
        }),
{
}

pub proof fn lemma_reply_effect_is_observed(
    p: ProcessV,
    id: u64,
    response: Result<AnswerSpec, Seq<char>>,
)
    ensures
        apply_effect(
            p,
            EffectSpec::Reply { id, response },
        ).boundary == p.boundary.push(
            BoundaryObservationV::Reply { id, response },
        ),
{
}

pub proof fn lemma_send_effect_is_observed(
    p: ProcessV,
    address: Seq<char>,
    message: MessageSpec,
)
    ensures
        apply_effect(
            p,
            EffectSpec::Send { address, message },
        ).boundary == p.boundary.push(
            BoundaryObservationV::Send { address, message },
        ),
{
}

pub proof fn lemma_effect_observations(
    p: ProcessV,
    effects: Seq<EffectSpec>,
)
    ensures
        apply_effects(p, effects).boundary
            == p.boundary + observe_effects(effects),
    decreases effects.len(),
{
    if effects.len() == 0 {
        assert(p.boundary + Seq::<BoundaryObservationV>::empty()
            =~= p.boundary);
    } else {
        let first = effects[0];
        let tail = effects.drop_first();
        lemma_effect_observations(apply_effect(p, first), tail);
        match first {
            EffectSpec::Reply { id, response } => {
                assert(apply_effect(p, first).boundary
                    == p.boundary.push(
                        BoundaryObservationV::Reply { id, response },
                    ));
                assert(p.boundary.push(
                    BoundaryObservationV::Reply { id, response },
                ) + observe_effects(tail)
                    =~= p.boundary + (
                        seq![BoundaryObservationV::Reply { id, response }]
                            + observe_effects(tail)
                    ));
            },
            EffectSpec::Send { address, message } => {
                assert(apply_effect(p, first).boundary
                    == p.boundary.push(
                        BoundaryObservationV::Send { address, message },
                    ));
                assert(p.boundary.push(
                    BoundaryObservationV::Send { address, message },
                ) + observe_effects(tail)
                    =~= p.boundary + (
                        seq![BoundaryObservationV::Send {
                            address,
                            message,
                        }] + observe_effects(tail)
                    ));
            },
            _ => {
                assert(apply_effect(p, first).boundary == p.boundary);
            },
        }
    }
}

/// Observation simulation for every production step: accepting an event is
/// hidden, and the step contributes exactly the Reply/Send projection of the
/// effects returned by the verified core transition.
pub proof fn lemma_process_step_observes(
    p: ProcessV,
    event: EventSpec,
)
    ensures
        ({
            let accepted = accept_event(p, event);
            let (_, effects) = spec_on_event(accepted.core, event);
            process_step(p, event).boundary
                == p.boundary + observe_effects(effects)
        }),
{
    let accepted = accept_event(p, event);
    let (next, effects) = spec_on_event(accepted.core, event);
    assert(accepted.boundary == p.boundary);
    lemma_effect_observations(
        ProcessV { core: next, ..accepted },
        effects,
    );
}

pub proof fn lemma_successful_store_completion_bookkeeping(
    p: ProcessV,
    op: OpId,
    response: StoreRes,
    clock: u64,
)
    requires
        p.pending_store.contains_key(op),
        successful_response(p.pending_store[op].request, response),
    ensures
        ({
            let next = accept_event(
                p,
                EventSpec::Store { op, response, clock },
            );
            &&& !next.pending_store.contains_key(op)
            &&& next.completed_store.contains(op)
            &&& next.boundary == p.boundary
            &&& next.core == p.core
        }),
{
}

/// Request/response shapes covered by the successful StoreReq/StoreRes path.
/// The store implementation determines the returned etag/body; this predicate
/// records only the shape and success needed by the process continuation.
pub open spec fn successful_response(
    request: StoreReqSpec,
    response: StoreRes,
) -> bool {
    match (request, response) {
        (StoreReqSpec::Get { .. }, StoreRes::Get { result: Ok(_) }) => true,
        (
            StoreReqSpec::GetIfNoneMatch { .. },
            StoreRes::GetIfNoneMatch { result: Ok(_) },
        ) => true,
        (
            StoreReqSpec::PutIfMatch { .. },
            StoreRes::PutIfMatch { result: Ok(_) },
        ) => true,
        (
            StoreReqSpec::PutIfNoneMatch { .. },
            StoreRes::PutIfNoneMatch { result: Ok(_) },
        ) => true,
        (
            StoreReqSpec::AppIfMatch { .. },
            StoreRes::AppIfMatch { result: Ok(_) },
        ) => true,
        (StoreReqSpec::Put { .. }, StoreRes::Put { result: Ok(()) }) => true,
        (StoreReqSpec::Del { .. }, StoreRes::Del { result: Ok(()) }) => true,
        (StoreReqSpec::List { .. }, StoreRes::List { result: Ok(_) }) => true,
        (
            StoreReqSpec::ListPrefixes { .. },
            StoreRes::ListPrefixes { result: Ok(_) },
        ) => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Production state to abstract StateV
// ---------------------------------------------------------------------------

pub open spec fn logical_key(target: TargetSpec) -> Seq<char> {
    match target {
        TargetSpec::Origin(origin) => origin_prefix() + origin,
        TargetSpec::Schedule(id) => schedule_prefix() + id,
    }
}

pub open spec fn phase_after(phase: PhaseSpec) -> Option<StoredDocumentV> {
    match phase {
        PhaseSpec::Origin { commit, .. }
        | PhaseSpec::Schedule { commit, .. }
        | PhaseSpec::FireIdle { commit }
        | PhaseSpec::FireOrigin { commit, .. }
        | PhaseSpec::FireSchedule { commit } => Some(commit.after),
        _ => None,
    }
}

pub open spec fn target_linearized(s: S, target: TargetSpec) -> bool {
    exists|fid: u64|
        s.flights.inflight.contains_key(fid)
            && s.flights.inflight[fid].target == target
            && phase_after(s.flights.inflight[fid].phase) is Some
}

/// Cached workflow documents represent the abstract store except while a
/// flight on that origin has already selected its post-state. At that point
/// the flight, not the stale cache entry, is the linearization witness.
pub open spec fn cache_related(
    cache: CacheSpec,
    flights: FlightsSpec,
    store: AbstractStoreV,
) -> bool {
    forall|i: int|
        0 <= i < cache.entries.len() ==> {
            let entry = #[trigger] cache.entries[i];
            let target = TargetSpec::Origin(entry.origin);
            &&& !(
                exists|fid: u64|
                    flights.inflight.contains_key(fid)
                        && flights.inflight[fid].target == target
                        && phase_after(flights.inflight[fid].phase) is Some
            ) ==> doc_rel(
                logical_key(target),
                spec_loaded_body(entry.cached.loaded),
                store,
            )
        }
}

/// Every decided document flight is interpreted as the abstract post-state.
pub open spec fn flights_related(
    flights: FlightsSpec,
    store: AbstractStoreV,
) -> bool {
    forall|fid: u64|
        flights.inflight.contains_key(fid) ==> {
            let flight = flights.inflight[fid];
            match phase_after(flight.phase) {
                Some(after) => doc_rel(
                    logical_key(flight.target),
                    spec_stored_body(after),
                    store,
                ),
                None => true,
            }
        }
}

/// Explicit frame for a decision on `key`: every other active document lane
/// denotes a different abstract key. The lane invariant is intentionally kept
/// separate from this semantic-key fact because origin and schedule names can
/// share their unprefixed text.
pub open spec fn concurrent_lanes_framed(
    flights: FlightsSpec,
    deciding_flight: u64,
    key: Seq<char>,
) -> bool {
    forall|fid: u64|
        flights.inflight.contains_key(fid)
            && fid != deciding_flight ==> {
                logical_key(
                    #[trigger] flights.inflight[fid].target,
                ) != key
            }
}

pub open spec fn active_flight_keys_distinct(
    flights: FlightsSpec,
) -> bool {
    forall|left: u64, right: u64|
        flights.inflight.contains_key(left)
            && flights.inflight.contains_key(right)
            && left != right ==> {
                logical_key(
                    #[trigger] flights.inflight[left].target,
                ) != logical_key(
                    #[trigger] flights.inflight[right].target,
                )
            }
}

pub proof fn lemma_active_flights_frame_lane(
    flights: FlightsSpec,
    deciding_flight: u64,
)
    requires
        active_flight_keys_distinct(flights),
        flights.inflight.contains_key(deciding_flight),
    ensures
        concurrent_lanes_framed(
            flights,
            deciding_flight,
            logical_key(
                flights.inflight[deciding_flight].target,
            ),
        ),
{
}

/// Updating one abstract key preserves the interpretation of every explicitly
/// framed concurrent production lane.
pub proof fn lemma_concurrent_lanes_preserved(
    flights: FlightsSpec,
    deciding_flight: u64,
    key: Seq<char>,
    before: AbstractStoreV,
    after: AbstractStoreV,
)
    requires
        flights_related(flights, before),
        concurrent_lanes_framed(
            flights,
            deciding_flight,
            key,
        ),
        echod_concrete::interpret::others_kept(
            key,
            before,
            after,
        ),
    ensures
        forall|fid: u64|
            flights.inflight.contains_key(fid)
                && fid != deciding_flight ==> {
                    let flight = flights.inflight[fid];
                    match phase_after(flight.phase) {
                        Some(document) => doc_rel(
                            logical_key(flight.target),
                            spec_stored_body(document),
                            after,
                        ),
                        None => true,
                    }
                },
{
    assert forall|fid: u64|
        flights.inflight.contains_key(fid)
            && fid != deciding_flight implies {
                let flight = flights.inflight[fid];
                match phase_after(flight.phase) {
                    Some(document) => doc_rel(
                        logical_key(flight.target),
                        spec_stored_body(document),
                        after,
                    ),
                    None => true,
                }
            } by {
        let flight = flights.inflight[fid];
        match phase_after(flight.phase) {
            Some(document) => {
                assert(doc_rel(
                    logical_key(flight.target),
                    spec_stored_body(document),
                    before,
                ));
            },
            None => {},
        }
    };
}

/// Each active flight owns its document lane.
pub open spec fn flight_lanes_consistent(flights: FlightsSpec) -> bool {
    forall|fid: u64|
        flights.inflight.contains_key(fid) ==> {
            let flight = flights.inflight[fid];
            let name = crate::target::spec_name(flight.target);
            &&& flights.slots.contains_key(name)
            &&& flights.slots[name].busy == Some(fid)
        }
}

/// The allocator's next operation id is not currently owned. The production
/// allocator wraps, so preservation across an issuing step additionally needs
/// freshness of that step's successor id; individual issuing-slice theorems
/// state that local side condition explicitly.
pub open spec fn operation_id_fresh(s: S) -> bool {
    !s.ops.contains_key(s.next_op)
}

pub open spec fn operation_successor_fresh(s: S) -> bool {
    &&& s.next_op < u64::MAX
    &&& !s.ops.contains_key((s.next_op + 1) as u64)
}

/// Issuing one Store call consumes `next_op` and leaves its successor fresh.
pub proof fn lemma_store_issue_preserves_operation_freshness(
    s: S,
    request: StoreReqSpec,
    owner: Owner,
)
    requires
        operation_id_fresh(s),
        operation_successor_fresh(s),
    ensures
        ({
            let (next, op) = crate::state::spec_store(
                s,
                request,
                owner,
            );
            &&& op == s.next_op
            &&& operation_id_fresh(next)
        }),
{
    let (next, op) = crate::state::spec_store(
        s,
        request,
        owner,
    );
    assert(next.next_op == (s.next_op + 1) as u64);
}

/// The allocator's next flight id does not name an active flight. As with
/// operation ids, an issuing slice must establish freshness of the successor
/// before it can re-establish this invariant after a wrapping increment.
pub open spec fn flight_id_fresh(s: S) -> bool {
    !s.flights.inflight.contains_key(s.next_flight)
}

pub open spec fn flight_successor_fresh(s: S) -> bool {
    &&& s.next_flight < u64::MAX
    &&& !s.flights.inflight.contains_key(
        (s.next_flight + 1) as u64,
    )
}

pub proof fn lemma_inflight_replacement_preserves_flight_freshness(
    s: S,
    flight: FlightSpec,
)
    requires
        flight_id_fresh(s),
        flight.id != s.next_flight,
    ensures
        flight_id_fresh(
            crate::handler_docs::spec_inflight(s, flight),
        ),
{
}

pub proof fn lemma_inflight_replacement_preserves_lane_keys(
    s: S,
    fid: u64,
    replacement: FlightSpec,
)
    requires
        active_flight_keys_distinct(s.flights),
        s.flights.inflight.contains_key(fid),
        replacement.id == fid,
        replacement.target == s.flights.inflight[fid].target,
    ensures
        active_flight_keys_distinct(
            crate::handler_docs::spec_inflight(
                crate::handler_docs::spec_take_flight(s, fid),
                replacement,
            ).flights,
        ),
{
    let without =
        crate::handler_docs::spec_take_flight(s, fid);
    let after =
        crate::handler_docs::spec_inflight(without, replacement);
    assert forall|left: u64, right: u64|
        after.flights.inflight.contains_key(left)
            && after.flights.inflight.contains_key(right)
            && left != right implies {
                logical_key(
                    #[trigger] after.flights.inflight[left].target,
                ) != logical_key(
                    #[trigger] after.flights.inflight[right].target,
                )
            } by {
        if left != fid && right != fid {
            assert(after.flights.inflight[left]
                == s.flights.inflight[left]);
            assert(after.flights.inflight[right]
                == s.flights.inflight[right]);
        } else if left == fid {
            assert(after.flights.inflight[left] == replacement);
            assert(after.flights.inflight[right]
                == s.flights.inflight[right]);
        } else {
            assert(right == fid);
            assert(after.flights.inflight[right] == replacement);
            assert(after.flights.inflight[left]
                == s.flights.inflight[left]);
        }
    };
}

pub proof fn lemma_inflight_replacement_preserves_lane_owner(
    s: S,
    fid: u64,
    replacement: FlightSpec,
)
    requires
        flight_lanes_consistent(s.flights),
        s.flights.inflight.contains_key(fid),
        replacement.id == fid,
        replacement.target == s.flights.inflight[fid].target,
    ensures
        flight_lanes_consistent(
            crate::handler_docs::spec_inflight(
                crate::handler_docs::spec_take_flight(s, fid),
                replacement,
            ).flights,
        ),
{
    let after = crate::handler_docs::spec_inflight(
        crate::handler_docs::spec_take_flight(s, fid),
        replacement,
    );
    assert forall|other: u64|
        after.flights.inflight.contains_key(other) implies {
            let flight =
                #[trigger] after.flights.inflight[other];
            let name = crate::target::spec_name(flight.target);
            &&& after.flights.slots.contains_key(name)
            &&& after.flights.slots[name].busy == Some(other)
        } by {
        if other == fid {
            assert(after.flights.inflight[other] == replacement);
        } else {
            assert(after.flights.inflight[other]
                == s.flights.inflight[other]);
        }
        assert(after.flights.slots == s.flights.slots);
    };
}

pub open spec fn loaded_document_well_formed(
    loaded: crate::document::LoadedSpec,
) -> bool {
    &&& well_formed(loaded.document)
    &&& document_ids_bounded(loaded.document)
}

pub open spec fn cached_document_well_formed(
    cached: crate::cache::CachedSpec,
) -> bool {
    loaded_document_well_formed(cached.loaded)
}

pub open spec fn cache_entries_carried_except(
    before: crate::cache::CacheSpec,
    after: crate::cache::CacheSpec,
    replaced_origin: Seq<char>,
) -> bool {
    forall|i: int|
        0 <= i < after.entries.len()
            && after.entries[i].origin != replaced_origin ==>
            exists|j: int|
                0 <= j < before.entries.len()
                    && before.entries[j] == #[trigger] after.entries[i]
}

proof fn lemma_cache_find_valid(
    entries: Seq<crate::cache::EntrySpec>,
    origin: Seq<char>,
)
    ensures
        match crate::cache::spec_find(entries, origin) {
            Some(i) => {
                &&& 0 <= i < entries.len()
                &&& entries[i].origin == origin
            },
            None => true,
        },
    decreases entries.len(),
{
    reveal_with_fuel(crate::cache::spec_find, 1);
    if entries.len() > 0 && entries[0].origin != origin {
        lemma_cache_find_valid(entries.drop_first(), origin);
    }
}

proof fn lemma_cache_remove_carries_other_entries(
    cache: crate::cache::CacheSpec,
    origin: Seq<char>,
)
    ensures
        cache_entries_carried_except(
            cache,
            crate::cache::spec_remove(cache, origin),
            origin,
        ),
{
    let after = crate::cache::spec_remove(cache, origin);
    lemma_cache_find_valid(cache.entries, origin);
    match crate::cache::spec_find(cache.entries, origin) {
        Some(removed) => {
            assert(after.entries == cache.entries.remove(removed));
            cache.entries.remove_ensures(removed);
            assert forall|i: int|
                0 <= i < after.entries.len()
                    && after.entries[i].origin != origin implies
                    exists|j: int|
                        0 <= j < cache.entries.len()
                            && cache.entries[j]
                                == #[trigger] after.entries[i] by {
                if i < removed {
                    assert(after.entries[i] == cache.entries[i]);
                } else {
                    assert(after.entries[i]
                        == cache.entries[i + 1]);
                }
            };
        },
        None => {},
    }
}

pub proof fn lemma_cache_get_carries_unrelated_entries(
    cache: crate::cache::CacheSpec,
    origin: Seq<char>,
)
    ensures
        ({
            let (after, _) = crate::cache::spec_get(cache, origin);
            cache_entries_carried_except(cache, after, origin)
        }),
{
    let (after, _) = crate::cache::spec_get(cache, origin);
    lemma_cache_find_valid(cache.entries, origin);
    match crate::cache::spec_find(cache.entries, origin) {
        Some(found) => {
            cache.entries.remove_ensures(found);
            assert(after.entries
                == cache.entries.remove(found)
                    .push(cache.entries[found]));
            assert forall|i: int|
                0 <= i < after.entries.len()
                    && after.entries[i].origin != origin implies
                    exists|j: int|
                        0 <= j < cache.entries.len()
                            && cache.entries[j]
                                == #[trigger] after.entries[i] by {
                if i == after.entries.len() - 1 {
                    assert(after.entries[i] == cache.entries[found]);
                    assert(after.entries[i].origin == origin);
                    assert(false);
                }
                assert(i < after.entries.len() - 1);
                if i < found {
                    assert(after.entries[i] == cache.entries[i]);
                } else {
                    assert(after.entries[i]
                        == cache.entries[i + 1]);
                }
            };
        },
        None => {},
    }
}

proof fn lemma_cache_trim_carries_entries(
    original: crate::cache::CacheSpec,
    cache: crate::cache::CacheSpec,
    keep: Seq<char>,
)
    requires
        cache_entries_carried_except(original, cache, keep),
    ensures
        ({
            let (_, after) = crate::cache::spec_trim(cache, keep);
            cache_entries_carried_except(
                original,
                after,
                keep,
            )
        }),
    decreases cache.entries.len(),
{
    reveal_with_fuel(crate::cache::spec_trim, 2);
    if (cache.entries.len() > cache.max_entries
            || cache.bytes > cache.max_bytes)
        && cache.entries.len() > 0
        && cache.entries[0].origin != keep
    {
        let next = crate::cache::CacheSpec {
            entries: cache.entries.drop_first(),
            bytes: cache.bytes.wrapping_sub(
                cache.entries[0].cached.weight(),
            ),
            evictions: cache.evictions.wrapping_add(1),
            ..cache
        };
        assert(cache_entries_carried_except(
            original,
            next,
            keep,
        )) by {
            assert forall|i: int|
                0 <= i < next.entries.len()
                    && next.entries[i].origin != keep implies
                    exists|j: int|
                        0 <= j < original.entries.len()
                            && original.entries[j]
                                == #[trigger] next.entries[i] by {
                assert(next.entries[i] == cache.entries[i + 1]);
            };
        };
        lemma_cache_trim_carries_entries(
            original,
            next,
            keep,
        );
    }
}

/// Replacing/remembering one origin may evict unrelated cache entries, but it
/// cannot invent or modify one: every unrelated entry that remains is exactly
/// an entry from the old cache.
pub proof fn lemma_cache_put_carries_unrelated_entries(
    cache: crate::cache::CacheSpec,
    origin: Seq<char>,
    cached: crate::cache::CachedSpec,
)
    ensures
        ({
            let (_, after) =
                crate::cache::spec_put(cache, origin, cached);
            cache_entries_carried_except(cache, after, origin)
        }),
{
    lemma_cache_remove_carries_other_entries(cache, origin);
    let removed = crate::cache::spec_remove(cache, origin);
    let inserted = crate::cache::CacheSpec {
        entries: removed.entries.push(crate::cache::EntrySpec {
            origin,
            cached,
        }),
        bytes: removed.bytes.wrapping_add(cached.weight()),
        ..removed
    };
    assert(cache_entries_carried_except(
        cache,
        inserted,
        origin,
    )) by {
        assert forall|i: int|
            0 <= i < inserted.entries.len()
                && inserted.entries[i].origin != origin implies
                exists|j: int|
                    0 <= j < cache.entries.len()
                        && cache.entries[j]
                            == #[trigger] inserted.entries[i] by {
            assert(i < removed.entries.len());
            assert(inserted.entries[i] == removed.entries[i]);
        };
    };
    lemma_cache_trim_carries_entries(
        cache,
        inserted,
        origin,
    );
}

pub proof fn lemma_forget_all_preserves_membership_fields(
    core: crate::verified::node_spec::ANode,
    evicted: Seq<Seq<char>>,
)
    ensures
        crate::state::spec_forget_all(core, evicted).id == core.id,
        crate::state::spec_forget_all(core, evicted).ttl == core.ttl,
        crate::state::spec_forget_all(core, evicted).members
            == core.members,
    decreases evicted.len(),
{
    reveal_with_fuel(crate::state::spec_forget_all, 1);
    if evicted.len() > 0 {
        lemma_forget_all_preserves_membership_fields(
            crate::verified::node_spec::spec_forget(
                core,
                evicted[0],
            ),
            evicted.drop_first(),
        );
    }
}

pub proof fn lemma_remember_preserves_control_fields(
    s: S,
    origin: Seq<char>,
    cached: crate::cache::CachedSpec,
)
    ensures
        ({
            let next = crate::state::spec_remember(
                s,
                origin,
                cached,
            );
            &&& next.cfg == s.cfg
            &&& next.ops == s.ops
            &&& next.next_op == s.next_op
            &&& next.next_flight == s.next_flight
            &&& next.flights == s.flights
            &&& next.timers == s.timers
            &&& next.node.core.id == s.node.core.id
            &&& next.node.core.ttl == s.node.core.ttl
            &&& next.node.core.members == s.node.core.members
        }),
{
    let (evicted, _) =
        crate::cache::spec_put(s.cache, origin, cached);
    lemma_forget_all_preserves_membership_fields(
        s.node.core,
        evicted,
    );
}

pub proof fn lemma_decision_preserves_semantic_relations(
    before: S,
    after: S,
    fid: u64,
    origin: Seq<char>,
    replacement: FlightSpec,
    document: StoredDocumentV,
    abstract_before: AbstractStoreV,
    abstract_after: AbstractStoreV,
)
    requires
        cache_related(
            before.cache,
            before.flights,
            abstract_before,
        ),
        flights_related(before.flights, abstract_before),
        active_flight_keys_distinct(before.flights),
        before.flights.inflight.contains_key(fid),
        before.flights.inflight[fid].target
            == TargetSpec::Origin(origin),
        replacement.id == fid,
        replacement.target == TargetSpec::Origin(origin),
        phase_after(replacement.phase) == Some(document),
        after.flights.inflight
            == before.flights.inflight.remove(fid).insert(
                fid,
                replacement,
            ),
        cache_entries_carried_except(
            before.cache,
            after.cache,
            origin,
        ),
        doc_rel(
            logical_key(TargetSpec::Origin(origin)),
            spec_stored_body(document),
            abstract_after,
        ),
        echod_concrete::interpret::others_kept(
            logical_key(TargetSpec::Origin(origin)),
            abstract_before,
            abstract_after,
        ),
    ensures
        cache_related(
            after.cache,
            after.flights,
            abstract_after,
        ),
        flights_related(after.flights, abstract_after),
{
    lemma_active_flights_frame_lane(before.flights, fid);
    lemma_concurrent_lanes_preserved(
        before.flights,
        fid,
        logical_key(TargetSpec::Origin(origin)),
        abstract_before,
        abstract_after,
    );
    assert forall|current: u64|
        after.flights.inflight.contains_key(current) implies {
            let flight =
                #[trigger] after.flights.inflight[current];
            match phase_after(flight.phase) {
                Some(after_document) => doc_rel(
                    logical_key(flight.target),
                    spec_stored_body(after_document),
                    abstract_after,
                ),
                None => true,
            }
        } by {
        if current == fid {
            assert(after.flights.inflight[current] == replacement);
        } else {
            assert(before.flights.inflight.contains_key(current));
            assert(after.flights.inflight[current]
                == before.flights.inflight[current]);
        }
    };
    assert forall|i: int|
        0 <= i < after.cache.entries.len() implies {
            let entry = #[trigger] after.cache.entries[i];
            let target = TargetSpec::Origin(entry.origin);
            &&& !(
                exists|current: u64|
                    after.flights.inflight.contains_key(current)
                        && after.flights.inflight[current].target
                            == target
                        && phase_after(
                            after.flights.inflight[current].phase,
                        ) is Some
            ) ==> doc_rel(
                logical_key(target),
                spec_loaded_body(entry.cached.loaded),
                abstract_after,
            )
        } by {
        let entry = after.cache.entries[i];
        let target = TargetSpec::Origin(entry.origin);
        if !(exists|current: u64|
            after.flights.inflight.contains_key(current)
                && after.flights.inflight[current].target == target
                && phase_after(
                    after.flights.inflight[current].phase,
                ) is Some)
        {
            if entry.origin == origin {
                assert(after.flights.inflight[fid] == replacement);
                assert(false);
            } else {
                assert(entry.origin != origin);
                let j = choose|j: int|
                    0 <= j < before.cache.entries.len()
                        && before.cache.entries[j] == entry;
                assert(before.cache.entries[j] == entry);
                assert(!(
                    exists|current: u64|
                        before.flights.inflight.contains_key(current)
                            && before.flights.inflight[current].target
                                == target
                            && phase_after(
                                before.flights.inflight[current].phase,
                            ) is Some
                )) by {
                    if exists|current: u64|
                        before.flights.inflight.contains_key(current)
                            && before.flights.inflight[current].target
                                == target
                            && phase_after(
                                before.flights.inflight[current].phase,
                            ) is Some
                    {
                        let current = choose|current: u64|
                            before.flights.inflight
                                .contains_key(current)
                                && before.flights.inflight[current].target
                                    == target
                                && phase_after(
                                    before.flights.inflight[current].phase,
                                ) is Some;
                        if current == fid {
                            assert(before.flights.inflight[current].target
                                == TargetSpec::Origin(origin));
                            assert(entry.origin == origin);
                            assert(false);
                        }
                        assert(after.flights.inflight
                            .contains_key(current));
                        assert(after.flights.inflight[current]
                            == before.flights.inflight[current]);
                        assert(exists|after_current: u64|
                            after.flights.inflight
                                .contains_key(after_current)
                                && after.flights.inflight[after_current]
                                    .target == target
                                && phase_after(
                                    after.flights.inflight[after_current]
                                        .phase,
                                ) is Some);
                        assert(false);
                    }
                };
                assert(origin_prefix() + entry.origin
                    != origin_prefix() + origin) by {
                    if origin_prefix() + entry.origin
                        == origin_prefix() + origin
                    {
                        assert(
                            (origin_prefix() + entry.origin).skip(
                                origin_prefix().len() as int,
                            ) =~= entry.origin
                        );
                        assert(
                            (origin_prefix() + origin).skip(
                                origin_prefix().len() as int,
                            ) =~= origin
                        );
                        assert(false);
                    }
                };
            }
        }
    };
}

pub open spec fn commit_documents_well_formed(
    commit: crate::handler_docs::CommittingSpec,
) -> bool {
    &&& loaded_document_well_formed(commit.w.loaded)
    &&& well_formed(commit.after)
    &&& document_ids_bounded(commit.after)
}

/// Every production document retained across events is suitable for the
/// verified request theorem. Loading phases retain only an optional cache
/// entry; decided phases retain both their source and candidate documents.
pub open spec fn phase_documents_well_formed(
    phase: PhaseSpec,
) -> bool {
    match phase {
        PhaseSpec::Idle
        | PhaseSpec::FireLoadingSchedule { .. } => true,
        PhaseSpec::Loading { revalidating, .. } => match revalidating {
            Some(cached) => cached_document_well_formed(cached),
            None => true,
        },
        PhaseSpec::Origin { commit, .. }
        | PhaseSpec::Schedule { commit, .. }
        | PhaseSpec::FireIdle { commit }
        | PhaseSpec::FireOrigin { commit, .. }
        | PhaseSpec::FireSchedule { commit } =>
            commit_documents_well_formed(commit),
        PhaseSpec::FireWaitingOrigin(ctx) =>
            loaded_document_well_formed(ctx.ws.loaded),
        PhaseSpec::FireLoadingOrigin {
            revalidating,
            ctx,
            ..
        } => {
            &&& loaded_document_well_formed(ctx.ws.loaded)
            &&& match revalidating {
                Some(cached) => cached_document_well_formed(cached),
                None => true,
            }
        },
    }
}

pub open spec fn retained_documents_well_formed(s: S) -> bool {
    &&& forall|i: int|
        0 <= i < s.cache.entries.len() ==>
            cached_document_well_formed(
                #[trigger] s.cache.entries[i].cached,
            )
    &&& forall|fid: u64|
        s.flights.inflight.contains_key(fid) ==>
            phase_documents_well_formed(
                #[trigger] s.flights.inflight[fid].phase,
            )
}

/// Pending operation owners still point to the control machine waiting for
/// that operation.
pub open spec fn owners_consistent(s: S) -> bool {
    forall|op: OpId|
        s.ops.contains_key(op) ==> match s.ops[op] {
            Owner::Flight(fid) =>
                s.flights.inflight.contains_key(fid)
                    && s.flights.inflight[fid].phase.expects() == Some(op),
            Owner::Members => match s.node.members.refresh {
                Some(refresh) => refresh.expects(op),
                None => false,
            },
            Owner::Timers => match s.timers.listing {
                Some(listing) => listing.expects(op),
                None => false,
            },
            Owner::Debug | Owner::Ignored => true,
        }
}

pub proof fn lemma_direct_write_preserves_owners(
    before: S,
    after: S,
    fid: u64,
    completed_op: OpId,
    write_op: OpId,
    replacement: FlightSpec,
)
    requires
        owners_consistent(before),
        before.flights.inflight.contains_key(fid),
        before.flights.inflight[fid].phase.expects()
            == Some(completed_op),
        replacement.id == fid,
        replacement.phase.expects() == Some(write_op),
        !before.ops.contains_key(write_op),
        after.ops == before.ops.remove(completed_op).insert(
            write_op,
            Owner::Flight(fid),
        ),
        after.flights.inflight
            == before.flights.inflight.remove(fid).insert(
                fid,
                replacement,
            ),
        after.node.members.refresh == before.node.members.refresh,
        after.timers.listing == before.timers.listing,
    ensures owners_consistent(after),
{
    assert forall|current: OpId|
        after.ops.contains_key(current) implies
            match after.ops[current] {
                Owner::Flight(owner) =>
                    after.flights.inflight.contains_key(owner)
                        && after.flights.inflight[owner]
                            .phase.expects() == Some(current),
                Owner::Members => match after.node.members.refresh {
                    Some(refresh) => refresh.expects(current),
                    None => false,
                },
                Owner::Timers => match after.timers.listing {
                    Some(listing) => listing.expects(current),
                    None => false,
                },
                Owner::Debug | Owner::Ignored => true,
            } by {
        if current == write_op {
            assert(after.ops[current] == Owner::Flight(fid));
            assert(after.flights.inflight[fid] == replacement);
        } else {
            assert(before.ops.contains_key(current));
            assert(current != completed_op);
            assert(after.ops[current] == before.ops[current]);
            match before.ops[current] {
                Owner::Flight(owner) => {
                    if owner == fid {
                        assert(before.flights.inflight[fid]
                            .phase.expects() == Some(current));
                        assert(current == completed_op);
                        assert(false);
                    } else {
                        assert(after.flights.inflight[owner]
                            == before.flights.inflight[owner]);
                    }
                },
                _ => {},
            }
        }
    };
}

pub open spec fn membership_consistent(s: S) -> bool {
    &&& s.node.core.id == s.cfg.node_id
    &&& s.node.core.ttl == s.cfg.node_ttl_ms as nat
    &&& s.node.core.members.no_duplicates()
}

pub open spec fn timers_consistent(timers: TimersSpec) -> bool {
    &&& forall|i: int, j: int|
        0 <= i < j < timers.wheel.armed.len() ==> {
            &&& timers.wheel.armed[i] != timers.wheel.armed[j]
            &&& spec_slot_before(
                timers.wheel.armed[i],
                timers.wheel.armed[j],
            )
        }
    &&& timers.inflight <= timers.backlog.len()
}

/// Runtime bookkeeping agrees with the operation table held by the core.
pub open spec fn pending_store_consistent(p: ProcessV) -> bool {
    &&& forall|op: OpId|
        p.pending_store.contains_key(op) ==> {
            &&& p.core.ops.contains_key(op)
            &&& p.pending_store[op].owner == Some(p.core.ops[op])
        }
    &&& forall|op: OpId|
        p.completed_store.contains(op) ==> !p.pending_store.contains_key(op)
}

/// The current relation. It is intentionally strong enough for the sequential
/// happy path and explicit about the pieces a full concurrent proof must
/// preserve.
pub open spec fn related(
    production: ProcessV,
    abstract_state: AbstractStateV,
) -> bool {
    &&& production.core.out.len() == 0
    &&& pending_store_consistent(production)
    &&& operation_id_fresh(production.core)
    &&& flight_id_fresh(production.core)
    &&& retained_documents_well_formed(production.core)
    &&& active_flight_keys_distinct(production.core.flights)
    &&& owners_consistent(production.core)
    &&& membership_consistent(production.core)
    &&& timers_consistent(production.core.timers)
    &&& flight_lanes_consistent(production.core.flights)
    &&& cache_related(
        production.core.cache,
        production.core.flights,
        abstract_state.store,
    )
    &&& flights_related(production.core.flights, abstract_state.store)
    // Normal external requests close their workflow internally, so this is
    // empty in the currently proved fragment. Fire/occurrence simulation must
    // relax it to a coverage relation.
    &&& abstract_state.pending.len() == 0
}

pub open spec fn initial_abstract() -> AbstractStateV {
    AbstractStateV {
        store: empty_store(),
        pending: Seq::empty(),
    }
}

pub open spec fn document_ids_bounded(document: StoredDocumentV) -> bool {
    match document {
        StoredDocumentV::Workflow(workflow) =>
            forall|id: Seq<char>| workflow.objects.contains_key(id) ==>
                id.len() <= usize::MAX as int,
        StoredDocumentV::Schedule(_) => true,
    }
}

/// The restricted normal-request slice in which production's atomic
/// request-plus-sweep transition leaves the same document body as the raw
/// handler used by the abstract request step. Requests that also consume due
/// work need a multi-step abstract simulation and are outside this predicate.
pub open spec fn normal_request_handler_aligned(
    document: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
) -> bool {
    echod_concrete::node::spec_stored_body(on_request(
        document,
        request,
        now,
        retry_timeout,
        REQUEST_SWEEP_STEPS as nat,
    )) == echod_concrete::node::spec_handle(
        echod_concrete::node::spec_stored_body(document),
        request,
        now,
    ).0
}

pub proof fn lemma_initial_related(cfg: ConfigSpec)
    ensures
        related(initial_process(cfg), initial_abstract()),
{
    let p = initial_process(cfg);
    assert(p.core == spec_state_new(cfg));
    assert(p.core.out =~= Seq::<EffectSpec>::empty());
    assert(p.core.ops =~= Map::<OpId, Owner>::empty());
    assert(p.core.cache.entries.len() == 0);
    assert(p.core.flights.inflight =~= Map::<u64, FlightSpec>::empty());
    assert(p.core.flights.slots.dom() =~= Set::<Seq<char>>::empty());
    assert(p.core.node.core.members =~= Seq::<Seq<char>>::empty());
    assert(p.core.timers.wheel.armed =~= Seq::<(u64, Seq<char>)>::empty());
    assert(p.core.timers.backlog =~= Seq::<(u64, Seq<char>)>::empty());
}

// ---------------------------------------------------------------------------
// The proved normal-request linearization fact
// ---------------------------------------------------------------------------

/// The document theorem needed when a successful Get has loaded a document
/// and the production flight decides the normal external request. It proves
/// both preservation and exact endpoint effects for the same atomic
/// transition used by `handler_docs::spec_decide`.
pub proof fn lemma_normal_request_happy_path(
    document: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
)
    requires
        well_formed(document),
        routed(document, request),
        echod_concrete::node::spec_stored_committed_at(document) <= now,
        now <= MAX_TIME,
        0 < retry_timeout <= MAX_TIME,
        safe_effect_config(now, retry_timeout),
        document_ids_bounded(document),
    ensures
        ({
            let after = on_request(
                document,
                request,
                now,
                retry_timeout,
                REQUEST_SWEEP_STEPS as nat,
            );
            let (_, _, _, notes) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(document),
                    request,
                    now,
                    retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                );
            &&& well_formed(after)
            &&& effects_match(document, after, notes)
        }),
{
    request_preserves_well_formed(
        document,
        request,
        now,
        retry_timeout,
    );
    lemma_request_transition_effects(
        document,
        request,
        now,
        retry_timeout,
        REQUEST_SWEEP_STEPS as nat,
    );
}

/// The linearization kernel for a normal external request. In addition to the
/// production preservation/effect facts, the independently implemented
/// abstract handler has exactly one agreeing served outcome on the document's
/// logical key. The process may take several Store steps before and after this
/// point; those steps are hidden by `observe_effects`.
pub proof fn lemma_normal_request_matches_abstract_handler(
    config: ServerConfig,
    document: StoredDocumentV,
    request: Request,
    key: Seq<char>,
    abstract_store: AbstractStoreV,
    now: u64,
)
    requires
        well_formed(document),
        routed(document, request),
        echod_concrete::node::spec_key(request) == Some(key),
        doc_rel(
            key,
            spec_stored_body(document),
            abstract_store,
        ),
        finite_store(abstract_store),
        echod_concrete::node::spec_stored_committed_at(document) <= now,
        now <= MAX_TIME,
        0 < config.retry_timeout <= MAX_TIME,
        safe_effect_config(now, config.retry_timeout),
        document_ids_bounded(document),
    ensures
        ({
            let after = on_request(
                document,
                request,
                now,
                config.retry_timeout,
                REQUEST_SWEEP_STEPS as nat,
            );
            let (_, _, _, notes) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(document),
                    request,
                    now,
                    config.retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                );
            &&& request_agrees(
                config,
                request,
                key,
                spec_stored_body(document),
                abstract_store,
                now,
            )
            &&& well_formed(after)
            &&& effects_match(document, after, notes)
        }),
{
    lemma_request_agrees(
        config,
        request,
        key,
        spec_stored_body(document),
        abstract_store,
        now,
    );
    lemma_normal_request_happy_path(
        document,
        request,
        now,
        config.retry_timeout,
    );
}

/// A successfully decoded normal Get has reached a concrete decision and the
/// commit sequencer has selected a direct conditional document write. This is
/// the exact production kernel used by the world-level linearization slice;
/// key/timer actions that precede the document write are intentionally not
/// covered by this direct-write theorem.
pub proof fn lemma_successful_get_issues_direct_write(
    s: S,
    flight: FlightSpec,
    origin: Seq<char>,
    response: StoreRes,
    loaded_state: S,
    working: WorkingSpec,
    decided_state: S,
    commit: CommittingSpec,
    done: DoneSpec,
    issued_state: S,
    issued_commit: CommittingSpec,
    write_op: OpId,
    mode: crate::types::WriteMode,
    change_count: usize,
    bytes: u64,
    len: usize,
)
    requires
        flight.target == TargetSpec::Origin(origin),
        flight.work is Request,
        crate::handler_docs::spec_loaded_origin(
            s,
            origin,
            None,
            response,
        ) == (loaded_state, Ok(working)),
        crate::handler_docs::spec_decide(
            loaded_state,
            flight.work,
            working,
        ) == (decided_state, commit, done),
        crate::handler_docs::spec_commit_advance(
            decided_state,
            flight.id,
            commit,
            None,
        ) == (
            issued_state,
            issued_commit,
            ProgressSpec::Issued,
        ),
        issued_commit.issued == Some(IssuedSpec::Write {
            op: write_op,
            mode,
            change_count,
            bytes,
            len,
        }),
    ensures
        crate::handler_docs::spec_answered_loading(
            s,
            flight,
            None,
            response,
        ) == crate::handler_docs::spec_inflight(
            issued_state,
            FlightSpec {
                phase: PhaseSpec::Origin {
                    commit: issued_commit,
                    done,
                },
                ..flight
            },
        ),
        issued_state.ops.contains_key(write_op),
        issued_state.ops[write_op] == Owner::Flight(flight.id),
{
    reveal(crate::handler_docs::spec_answered_loading);
    reveal(crate::handler_docs::spec_run_origin);
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_issue_write);
}

/// A successfully stored deadline key is armed in the timer wheel before the
/// same commit issues its conditional document write.
pub proof fn lemma_successful_deadline_key_issues_write(
    s: S,
    fid: u64,
    flight: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
    key: crate::verified::node::AKey,
    name: Seq<char>,
    key_op: OpId,
    issued_state: S,
    issued_commit: CommittingSpec,
    write_op: OpId,
    mode: crate::types::WriteMode,
    change_count: usize,
    bytes: u64,
    len: usize,
)
    requires
        commit.issued == Some(IssuedSpec::Key {
            op: key_op,
            key,
            name,
            arm: true,
        }),
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            Some(StoreRes::Put { result: Ok(()) }),
        ) == (
            issued_state,
            issued_commit,
            ProgressSpec::Issued,
        ),
        issued_commit.issued == Some(IssuedSpec::Write {
            op: write_op,
            mode,
            change_count,
            bytes,
            len,
        }),
    ensures
        issued_state.timers.wheel.armed
            == crate::state_timers::spec_arm(
                s.timers.wheel.armed,
                key.at as u64,
                name,
            ),
        crate::handler_docs::spec_answered_origin(
            s,
            fid,
            flight,
            commit,
            done,
            StoreRes::Put { result: Ok(()) },
        ) == crate::handler_docs::spec_inflight(
            issued_state,
            FlightSpec {
                phase: PhaseSpec::Origin {
                    commit: issued_commit,
                    done,
                },
                ..flight
            },
        ),
{
    reveal(crate::handler_docs::spec_answered_origin);
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
}

/// Once the direct conditional write has succeeded and the verified commit
/// sequence reports Done, production runs the committed Reply/Send path.
pub proof fn lemma_successful_conditional_write_commits(
    s: S,
    fid: u64,
    flight: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
    response: StoreRes,
    committed_state: S,
    committed_commit: CommittingSpec,
    fired: crate::types::Fired,
)
    requires
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            Some(response),
        ) == (
            committed_state,
            committed_commit,
            ProgressSpec::Done(fired),
        ),
    ensures
        crate::handler_docs::spec_answered_origin(
            s,
            fid,
            flight,
            commit,
            done,
            response,
        ) == crate::handler_docs::spec_committed(
            committed_state,
            flight,
            done,
            fired,
        ),
{
    reveal(crate::handler_docs::spec_answered_origin);
}

// ---------------------------------------------------------------------------
// Store failure and retry kernels used by the world-step proof
// ---------------------------------------------------------------------------

/// A conditional-write race follows the production retry path exactly. This
/// exposes the state on which a world-level stutter proof must re-establish
/// the flight/cache relation; it does not assume that preservation.
pub proof fn lemma_precondition_failed_retries(
    s: S,
    flight: FlightSpec,
)
    ensures
        crate::handler_docs::spec_commit_failed(
            s,
            flight,
            echod_concrete::store::StoreErrorSpec::PreconditionFailed,
        ) == crate::handler_docs::spec_retry(
            crate::state::spec_note(
                crate::state::spec_note(
                    match flight.target {
                        TargetSpec::Origin(origin) =>
                            crate::state::spec_forget_origin(s, origin),
                        _ => s,
                    },
                    crate::types::NoteSpec::Commit(
                        crate::types::CommitOutcome::Raced,
                    ),
                ),
                crate::types::NoteSpec::Raced {
                    target: crate::target::spec_name(flight.target),
                    attempt: flight.attempt,
                },
            ),
            flight,
        ),
{
    reveal(crate::handler_docs::spec_commit_failed);
}

/// An unavailable uncached Get fails the same request flight rather than
/// changing the document decision.
pub proof fn lemma_unavailable_get_fails_flight(
    s: S,
    flight: FlightSpec,
    origin: Seq<char>,
    error: echod_concrete::StoreError,
)
    requires
        flight.target == TargetSpec::Origin(origin),
    ensures
        crate::handler_docs::spec_answered_loading(
            s,
            flight,
            None,
            StoreRes::Get { result: Err(error) },
        ) == crate::handler_docs::spec_fail(
            s,
            flight,
            crate::types::spec_error_text(error.deep_view()),
        ),
{
    reveal(crate::handler_docs::spec_answered_loading);
    reveal(crate::handler_docs::spec_loaded_origin);
}

/// A response of the wrong Store variant fails an uncached origin load with
/// the production "unexpected" error.
pub proof fn lemma_mismatched_get_response_fails_flight(
    s: S,
    flight: FlightSpec,
    origin: Seq<char>,
    response: StoreRes,
)
    requires
        flight.target == TargetSpec::Origin(origin),
        !(response is Get),
    ensures
        crate::handler_docs::spec_answered_loading(
            s,
            flight,
            None,
            response,
        ) == crate::handler_docs::spec_fail(
            s,
            flight,
            crate::types::spec_error_text(
                crate::types::spec_unexpected(),
            ),
        ),
{
    reveal(crate::handler_docs::spec_answered_loading);
    reveal(crate::handler_docs::spec_loaded_origin);
    match response {
        StoreRes::Get { .. } => assert(false),
        _ => {},
    }
}

/// A response for an unknown operation is semantically hidden at the core:
/// with membership already scheduled, the handler may only update clock/wake
/// bookkeeping. Document lanes, cache, timers, membership, and operation
/// ownership are unchanged.
pub proof fn lemma_unknown_store_response_preserves_relation_fields(
    s: S,
    op: OpId,
    response: StoreRes,
    clock: u64,
)
    requires
        s.node.members.next_heartbeat is Some,
        !s.ops.contains_key(op),
        s.out.len() == 0,
    ensures
        ({
            let (next, effects) = spec_on_event(
                s,
                EventSpec::Store { op, response, clock },
            );
            &&& next.ops == s.ops
            &&& next.cache == s.cache
            &&& next.flights == s.flights
            &&& next.node == s.node
            &&& next.timers == s.timers
            &&& next.cfg == s.cfg
            &&& next.next_op == s.next_op
            &&& next.next_flight == s.next_flight
            &&& next.out.len() == 0
            &&& observe_effects(effects).len() == 0
            &&& effects.len() <= 1
            &&& forall|i: int| 0 <= i < effects.len() ==>
                #[trigger] effects[i] is Wake
        }),
{
    reveal(spec_on_event);
    reveal_with_fuel(observe_effects, 2);
    let clocked = S { clock, ..s };
    assert(clocked.ops.remove(op) == clocked.ops);
    let handled = S {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    assert(handled == clocked);
    reveal(crate::handler::spec_schedule_wake);
    let now = crate::state::spec_now(handled);
    let heartbeat = match handled.node.members.wake_at() {
        Some(at) => Some((at, Armed::Heartbeat)),
        None => None,
    };
    let timers = crate::state_timers::spec_next_wake(
        handled.timers,
        now,
    );
    let next_wake = match (heartbeat, timers) {
        (Some((ha, hb)), Some((ta, tb))) =>
            Some(if ha < ta { (ha, hb) } else { (ta, tb) }),
        (Some(h), None) => Some(h),
        (None, Some(t)) => Some(t),
        (None, None) => None,
    };
    let (scheduled, moved) =
        crate::state::spec_wake_moved(handled, next_wake);
    assert(scheduled.ops == s.ops);
    assert(scheduled.cache == s.cache);
    assert(scheduled.flights == s.flights);
    assert(scheduled.node == s.node);
    assert(scheduled.timers == s.timers);
    assert(scheduled.cfg == s.cfg);
    assert(scheduled.next_op == s.next_op);
    assert(scheduled.next_flight == s.next_flight);
    if moved {
        match next_wake {
            Some((at, armed)) => {
                assert(observe_effects(seq![EffectSpec::Wake {
                    after_ms: if at.saturating_sub(now) > 1 {
                        at.saturating_sub(now)
                    } else {
                        1
                    },
                    armed,
                }]).len() == 0);
            },
            None => {},
        }
    }
    let (next, effects) = spec_on_event(
        s,
        EventSpec::Store { op, response, clock },
    );
    assert(next.ops == s.ops);
    assert(next.cache == s.cache);
    assert(next.flights == s.flights);
    assert(next.node == s.node);
    assert(next.timers == s.timers);
    assert(next.cfg == s.cfg);
    assert(next.next_op == s.next_op);
    assert(next.next_flight == s.next_flight);
    assert(next.out =~= Seq::<EffectSpec>::empty());
    assert(observe_effects(effects).len() == 0);
    assert(effects.len() <= 1);
    assert forall|i: int| 0 <= i < effects.len() implies
        #[trigger] effects[i] is Wake by {
    };
}

// ---------------------------------------------------------------------------
// Explicit frontier: represented, but not yet simulated
// ---------------------------------------------------------------------------

pub ghost enum OpenCase {
    StoreUnavailable,
    StoreResponseShapeMismatch,
    ConditionalWriteRace,
    ConcurrentFlight,
    MembershipRefresh,
    TimerWake,
    ScheduleFire,
    OccurrenceCreation,
    CacheEvictionDuringFlight,
}

/// Machine-checkable classification of steps outside the proved sequential
/// request/successful-store fragment. This is a predicate, not an assumption.
pub open spec fn open_case(
    before: ProcessV,
    event: EventSpec,
    case: OpenCase,
) -> bool {
    match case {
        OpenCase::StoreUnavailable => match event {
            EventSpec::Store { response, .. } => match response {
                StoreRes::Get { result: Err(_) }
                | StoreRes::GetIfNoneMatch { result: Err(_) }
                | StoreRes::PutIfMatch { result: Err(_) }
                | StoreRes::PutIfNoneMatch { result: Err(_) }
                | StoreRes::AppIfMatch { result: Err(_) }
                | StoreRes::Put { result: Err(_) }
                | StoreRes::Del { result: Err(_) }
                | StoreRes::List { result: Err(_) }
                | StoreRes::ListPrefixes { result: Err(_) } => true,
                _ => false,
            },
            _ => false,
        },
        OpenCase::StoreResponseShapeMismatch => match event {
            EventSpec::Store { op, response, .. } =>
                before.pending_store.contains_key(op)
                    && !successful_response(
                        before.pending_store[op].request,
                        response,
                    ),
            _ => false,
        },
        OpenCase::ConditionalWriteRace => match event {
            EventSpec::Store { response, .. } => match response {
                StoreRes::PutIfMatch {
                    result: Err(echod_concrete::StoreError::PreconditionFailed),
                }
                | StoreRes::PutIfNoneMatch {
                    result: Err(echod_concrete::StoreError::PreconditionFailed),
                }
                | StoreRes::AppIfMatch {
                    result: Err(echod_concrete::StoreError::PreconditionFailed),
                } => true,
                _ => false,
            },
            _ => false,
        },
        OpenCase::ConcurrentFlight =>
            before.core.flights.inflight.dom().len() > 1,
        OpenCase::MembershipRefresh =>
            before.core.node.members.refresh is Some,
        OpenCase::TimerWake => event is Wake,
        OpenCase::ScheduleFire =>
            exists|fid: u64|
                before.core.flights.inflight.contains_key(fid)
                    && before.core.flights.inflight[fid].work is Fire,
        OpenCase::OccurrenceCreation =>
            before.core.timers.inflight > 0,
        OpenCase::CacheEvictionDuringFlight =>
            before.core.cache.evictions > 0
                && before.core.flights.inflight.dom().len() > 0,
    }
}

} // verus!
