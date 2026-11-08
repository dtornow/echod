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
//! Failure, racing-CAS, concurrent flights, membership listing/configuration
//! completions, and timer fire/commit steps remain classified by
//! [`open_case`]. The bounded startup wake and successful announcement
//! completion are proved below: they advance membership from announce to list,
//! leave document and timer state unchanged, and preserve the full relation as
//! abstract stutters. There are no admits or axioms in this module.

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
use crate::handler_docs::{FlightSpec, FlightsSpec, PhaseSpec};
#[cfg(verus_keep_ghost)]
use crate::state::{spec_state_new, Owner, S};
#[cfg(verus_keep_ghost)]
use crate::state_node::RefreshSpec;
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

pub open spec fn membership_consistent(s: S) -> bool {
    &&& s.node.core.id == s.cfg.node_id
    &&& s.node.core.ttl == s.cfg.node_ttl_ms as nat
    &&& s.node.core.members.no_duplicates()
}

pub open spec fn timer_wheel_ordered(timers: TimersSpec) -> bool {
    forall|i: int, j: int|
        0 <= i < j < timers.wheel.armed.len() ==> {
            &&& timers.wheel.armed[i] != timers.wheel.armed[j]
            &&& spec_slot_before(
                timers.wheel.armed[i],
                timers.wheel.armed[j],
            )
        }
}

pub open spec fn timers_consistent(timers: TimersSpec) -> bool {
    &&& timer_wheel_ordered(timers)
    &&& timers.inflight <= timers.backlog.len()
}

/// Every wheel slot is a real timer key and carries the deadline encoded by
/// that key. This is the representation invariant needed before a listed key
/// can safely join the ordered wheel.
pub open spec fn timer_wheel_keys_valid(s: S) -> bool {
    forall|i: int|
        0 <= i < s.timers.wheel.armed.len() ==> {
            let slot = #[trigger] s.timers.wheel.armed[i];
            match crate::keys::spec_parse_timer_key(slot.1) {
                Some(entry) => slot.0 == entry.deadline(),
                None => false,
            }
        }
}

/// A current wheel contains only this node's share. While a membership change
/// has marked the wheel for reload, stale ownership is allowed only until
/// `spec_reload` filters it; key validity and ordering still hold.
pub open spec fn timer_wheel_ownership_consistent(s: S) -> bool {
    s.timers.reload_pending || forall|i: int|
        0 <= i < s.timers.wheel.armed.len() ==> {
            let slot = #[trigger] s.timers.wheel.armed[i];
            match crate::keys::spec_parse_timer_key(slot.1) {
                Some(entry) => crate::handler_timers::spec_owns_entry(s, entry),
                None => false,
            }
        }
}

pub open spec fn timer_activity_consistent(s: S) -> bool {
    &&& timers_consistent(s.timers)
    &&& timer_wheel_keys_valid(s)
    &&& timer_wheel_ownership_consistent(s)
}

/// The exact empty successful bucket payload is the bounded completion case
/// proved below. It cannot perturb wheel order, key/deadline agreement, or
/// ownership because `spec_take_bucket` performs no arm operation.
pub proof fn lemma_empty_bucket_preserves_timer_activity(s: S, n: nat)
    requires
        timer_activity_consistent(s),
    ensures
        crate::handler_timers::spec_take_bucket(
            s,
            Seq::<Seq<char>>::empty(),
            n,
        ) == (s, n),
        timer_activity_consistent(
            crate::handler_timers::spec_take_bucket(
                s,
                Seq::<Seq<char>>::empty(),
                n,
            ).0,
        ),
{
    reveal(crate::handler_timers::spec_take_bucket);
}

/// With neither an armed key nor queued work, entering the production
/// due-dispatch path is an actual identity step. Nonempty due work is kept out
/// of the hidden slice.
pub proof fn lemma_empty_wheel_fire_due_is_idle(s: S, now: u64)
    requires
        s.timers.wheel.armed.len() == 0,
        s.timers.backlog.len() == 0,
    ensures
        crate::handler_timers::spec_fire_due(s, now) == s,
{
    reveal(crate::handler_timers::spec_fire_due);
    reveal(crate::state_timers::spec_take_due);
    reveal(crate::state_timers::spec_due_count);
    reveal(crate::handler_timers::spec_dispatch_due);
    assert(s.timers.wheel.armed =~= Seq::<crate::state_timers::SlotSpec>::empty());
    assert(s.timers.backlog =~= Seq::<crate::state_timers::SlotSpec>::empty());
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
    &&& owners_consistent(production.core)
    &&& membership_consistent(production.core)
    &&& timer_activity_consistent(production.core)
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

/// The first production wake is a control-plane step. It starts the
/// membership announcement, observes that timers have not started yet, and
/// leaves the abstract service state unchanged. Unlike a boundary-only
/// observation fact, this proves preservation of the full relation used by
/// this module, including operation ownership and pending-store bookkeeping.
pub proof fn lemma_initial_wake_membership_stutters(cfg: ConfigSpec)
    ensures
        ({
            let before = initial_process(cfg);
            let event = EventSpec::Wake {
                clock: 0,
                armed: Armed::Heartbeat,
            };
            let after = process_step(before, event);
            &&& related(after, initial_abstract())
            &&& after.boundary == before.boundary
            &&& after.core.node.members.refresh is Some
            &&& !after.core.timers.started
            &&& after.pending_store.dom().len() == 1
            &&& after.pending_store.dom()
                == Set::<OpId>::empty().insert(1)
            &&& after.completed_store
                == Set::<OpId>::empty()
            &&& after.pending_store.contains_key(1)
            &&& after.pending_store[1].owner == Some(Owner::Members)
            &&& after.core.ops.contains_key(1)
            &&& after.core.ops[1] == Owner::Members
            &&& after.core.ops.dom()
                == Set::<OpId>::empty().insert(1)
            &&& after.core.next_op == 2
            &&& after.core.clock == 0
            &&& !after.core.loops
            &&& match after.core.node.members.refresh {
                Some(RefreshSpec::Announcing { op, now }) =>
                    op == 1 && now == 0,
                _ => false,
            }
        }),
{
    let before = initial_process(cfg);
    let event = EventSpec::Wake {
        clock: 0,
        armed: Armed::Heartbeat,
    };
    reveal(spec_on_event);
    reveal(crate::handler_node::spec_members_tick);
    reveal(crate::handler_node::spec_members_refresh);
    reveal(crate::handler::spec_schedule_wake);
    reveal_with_fuel(apply_effects, 2);

    let accepted = accept_event(before, event);
    let (core, effects) = spec_on_event(accepted.core, event);
    assert(accepted.core == before.core);
    assert(before.core == spec_state_new(cfg));
    assert(effects.len() == 1);
    assert(effects[0] is Store);
    assert(core.out =~= Seq::<EffectSpec>::empty());
    assert(core.ops.dom().len() == 1);
    assert(core.node.members.refresh is Some);
    assert(!core.timers.started);

    let after = process_step(before, event);
    let base = ProcessV { core, ..accepted };
    assert(after == apply_effects(
        base,
        effects,
    ));
    assert(effects =~= seq![effects[0]]);
    assert(effects.drop_first() =~= Seq::<EffectSpec>::empty());
    match effects[0] {
        EffectSpec::Store { op, request } => {
            assert(op == 1);
            assert(after == apply_effect(
                base,
                EffectSpec::Store { op, request },
            ));
            lemma_store_effect_is_pending(base, op, request);
            assert(after.pending_store
                == base.pending_store.insert(
                    op,
                    PendingStoreV {
                        request,
                        owner: Some(Owner::Members),
                    },
                ));
        },
        _ => {
            assert(false);
        },
    }
    assert(after.pending_store.dom() =~= Set::<OpId>::empty().insert(1));
    assert(after.pending_store.dom().len() == 1);
    assert(after.pending_store.contains_key(1));
    assert(after.pending_store[1].owner == Some(Owner::Members));
    assert(after.boundary == before.boundary);
    assert(after.completed_store =~= Set::<OpId>::empty());
    assert(after.core == core);
    assert(after.core.ops.contains_key(1));
    assert(after.core.ops[1] == Owner::Members);
    assert(after.core.ops.dom() =~= Set::<OpId>::empty().insert(1));
    assert(after.core.next_op == 2);
    assert(after.core.clock == 0);
    assert(!after.core.loops);
    assert(match after.core.node.members.refresh {
        Some(RefreshSpec::Announcing { op, now }) =>
            op == 1 && now == 0,
        _ => false,
    });
    assert(after.core.out =~= Seq::<EffectSpec>::empty());
    assert(after.core.cache == before.core.cache);
    assert(after.core.flights == before.core.flights);
    assert(after.core.timers == before.core.timers);
    assert(after.core.node.core == before.core.node.core);

    assert(pending_store_consistent(after));
    assert(owners_consistent(after.core));
    assert(membership_consistent(after.core));
    assert(timers_consistent(after.core.timers));
    assert(timer_wheel_keys_valid(after.core));
    assert(timer_wheel_ownership_consistent(after.core));
    assert(timer_activity_consistent(after.core));
    assert(flight_lanes_consistent(after.core.flights));
    assert(cache_related(
        after.core.cache,
        after.core.flights,
        initial_abstract().store,
    ));
    assert(flights_related(
        after.core.flights,
        initial_abstract().store,
    ));
    assert(related(after, initial_abstract()));
}

/// Preconditions for the production core to accept a successful membership
/// announcement completion. The operation must be pending in both runtime
/// bookkeeping and the core, owned by the membership machine, and be the
/// announcement operation that machine currently expects.
pub open spec fn membership_announcement_completion_pre(
    before: ProcessV,
    event: EventSpec,
) -> bool {
    match event {
        EventSpec::Store { op, response, .. } => {
            &&& response == StoreRes::Put { result: Ok(()) }
            &&& before.pending_store.contains_key(op)
            &&& before.pending_store[op].owner
                == Some(Owner::Members)
            &&& before.core.ops.contains_key(op)
            &&& before.core.ops[op] == Owner::Members
            &&& match before.core.node.members.refresh {
                Some(RefreshSpec::Announcing {
                    op: expected,
                    ..
                }) => expected == op,
                _ => false,
            }
        },
        _ => false,
    }
}

/// Exact post-state of the bounded announcement-completion slice. Operation
/// `completed` has been consumed, operation `listing` is the newly issued
/// node-list call, and no document, cache, flight, timer, or boundary state
/// moved.
pub open spec fn membership_listing_started(
    before: ProcessV,
    after: ProcessV,
    completed: OpId,
    listing: OpId,
) -> bool {
    &&& !after.pending_store.contains_key(completed)
    &&& after.completed_store.contains(completed)
    &&& after.pending_store.contains_key(listing)
    &&& after.pending_store[listing].owner == Some(Owner::Members)
    &&& after.core.ops.contains_key(listing)
    &&& after.core.ops[listing] == Owner::Members
    &&& match after.core.node.members.refresh {
        Some(RefreshSpec::Listing { op, now }) =>
            op == listing && now == 0,
        _ => false,
    }
    &&& after.core.node.core == before.core.node.core
    &&& after.core.cache == before.core.cache
    &&& after.core.flights == before.core.flights
    &&& after.core.timers == before.core.timers
    &&& after.boundary == before.boundary
}

/// Completing the startup announcement replaces pending membership op `1`
/// with the node-list op `2`. This real Store event preserves the full
/// production/abstract relation and is therefore an abstract stutter.
pub proof fn lemma_initial_membership_announcement_completion_stutters(
    cfg: ConfigSpec,
)
    ensures
        ({
            let initial = initial_process(cfg);
            let wake = EventSpec::Wake {
                clock: 0,
                armed: Armed::Heartbeat,
            };
            let before = process_step(initial, wake);
            let event = EventSpec::Store {
                op: 1,
                response: StoreRes::Put { result: Ok(()) },
                clock: 0,
            };
            let after = process_step(before, event);
            &&& membership_announcement_completion_pre(before, event)
            &&& membership_listing_started(before, after, 1, 2)
            &&& related(after, initial_abstract())
        }),
{
    lemma_initial_wake_membership_stutters(cfg);
    let initial = initial_process(cfg);
    let wake = EventSpec::Wake {
        clock: 0,
        armed: Armed::Heartbeat,
    };
    let before = process_step(initial, wake);
    let event = EventSpec::Store {
        op: 1,
        response: StoreRes::Put { result: Ok(()) },
        clock: 0,
    };

    assert(related(before, initial_abstract()));
    assert(before.pending_store.contains_key(1));
    assert(before.pending_store[1].owner == Some(Owner::Members));
    assert(before.pending_store.dom()
        =~= Set::<OpId>::empty().insert(1));
    assert(before.core.ops.contains_key(1));
    assert(before.core.ops[1] == Owner::Members);
    assert(before.core.ops.dom()
        =~= Set::<OpId>::empty().insert(1));
    assert(before.core.next_op == 2);
    assert(before.core.clock == 0);
    assert(!before.core.loops);
    assert(match before.core.node.members.refresh {
        Some(RefreshSpec::Announcing { op, now }) =>
            op == 1 && now == 0,
        _ => false,
    });
    assert(membership_announcement_completion_pre(before, event));

    reveal(spec_on_event);
    reveal(crate::handler_node::spec_members_tick);
    reveal(crate::handler_node::spec_members_completed);
    reveal(crate::handler_node::spec_announced);
    reveal(crate::handler::spec_schedule_wake);
    reveal_with_fuel(apply_effects, 2);

    let accepted = accept_event(before, event);
    assert(!accepted.pending_store.contains_key(1));
    assert(accepted.pending_store =~= Map::<OpId, PendingStoreV>::empty());
    assert(accepted.completed_store.contains(1));
    assert(accepted.completed_store
        =~= Set::<OpId>::empty().insert(1));
    assert(accepted.core == before.core);
    assert(accepted.core.clock == 0);
    assert(!accepted.core.loops);
    let removed = S {
        ops: accepted.core.ops.remove(1),
        ..accepted.core
    };
    assert(!removed.ops.contains_key(1));
    assert(removed.ops =~= Map::<OpId, Owner>::empty());
    let handled = crate::handler_node::spec_members_completed(
        removed,
        1,
        StoreRes::Put { result: Ok(()) },
    );
    assert(!handled.ops.contains_key(1));
    assert(handled.ops.contains_key(2));
    assert(handled.ops[2] == Owner::Members);
    assert(match handled.node.members.refresh {
        Some(RefreshSpec::Listing { op, now }) =>
            op == 2 && now == 0,
        _ => false,
    });
    let (core, effects) = spec_on_event(accepted.core, event);
    assert(core.ops == handled.ops);
    assert(core.node.members.refresh == handled.node.members.refresh);
    assert(effects.len() == 1);
    assert(effects[0] is Store);
    assert(core.out =~= Seq::<EffectSpec>::empty());
    assert(!core.ops.contains_key(1));
    assert(core.ops.contains_key(2));
    assert(core.ops[2] == Owner::Members);
    assert(match core.node.members.refresh {
        Some(RefreshSpec::Listing { op, now }) =>
            op == 2 && now == 0,
        _ => false,
    });
    assert(core.node.core == before.core.node.core);
    assert(core.cache == before.core.cache);
    assert(core.flights == before.core.flights);
    assert(core.timers == before.core.timers);

    let after = process_step(before, event);
    let base = ProcessV { core, ..accepted };
    assert(after == apply_effects(base, effects));
    assert(effects =~= seq![effects[0]]);
    assert(effects.drop_first() =~= Seq::<EffectSpec>::empty());
    match effects[0] {
        EffectSpec::Store { op, request } => {
            assert(op == 2);
            assert(after == apply_effect(
                base,
                EffectSpec::Store { op, request },
            ));
            lemma_store_effect_is_pending(base, op, request);
            assert(after.pending_store
                == base.pending_store.insert(
                    op,
                    PendingStoreV {
                        request,
                        owner: Some(Owner::Members),
                    },
                ));
        },
        _ => {
            assert(false);
        },
    }
    assert(!after.pending_store.contains_key(1));
    assert(after.completed_store.contains(1));
    assert(after.pending_store.contains_key(2));
    assert(after.pending_store[2].owner == Some(Owner::Members));
    assert(after.pending_store.dom()
        =~= Set::<OpId>::empty().insert(2));
    assert(after.core == core);
    assert(after.core.ops.dom()
        =~= Set::<OpId>::empty().insert(2));
    assert(after.completed_store
        =~= Set::<OpId>::empty().insert(1));
    assert(membership_listing_started(before, after, 1, 2));

    assert forall|op: OpId|
        after.pending_store.contains_key(op) implies {
            &&& after.core.ops.contains_key(op)
            &&& after.pending_store[op].owner
                == Some(after.core.ops[op])
        } by {
        assert(op == 2);
    }
    assert forall|op: OpId|
        after.completed_store.contains(op) implies
            !after.pending_store.contains_key(op) by {
        assert(op == 1);
    }
    assert(pending_store_consistent(after));
    assert(owners_consistent(after.core));
    assert(membership_consistent(after.core));
    assert(timers_consistent(after.core.timers));
    assert(timer_wheel_keys_valid(after.core));
    assert(timer_wheel_ownership_consistent(after.core));
    assert(timer_activity_consistent(after.core));
    assert(flight_lanes_consistent(after.core.flights));
    assert(cache_related(
        after.core.cache,
        after.core.flights,
        initial_abstract().store,
    ));
    assert(flights_related(
        after.core.flights,
        initial_abstract().store,
    ));
    assert(related(after, initial_abstract()));
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
