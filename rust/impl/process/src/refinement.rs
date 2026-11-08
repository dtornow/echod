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
//! * the decision kernel for a normal loaded workflow request preserves the
//!   stored-document invariant and computes the exact endpoint-note delta;
//! * dispatchable endpoint notes become exactly one Send effect each, with
//!   the same unique effect keys.
//!
//! These local theorems intentionally reuse the two document theorems on which
//! a full process simulation must rest:
//! `quick_n_dirty::request_preserves_well_formed` and
//! `effects::lemma_request_transition_effects`.
//! They do not establish persistence, a Store-step invariant, or a global
//! refinement theorem.
//!
//! Failure, racing-CAS, detached two-document requests, concurrent flights,
//! membership refresh, and timer/fire steps are represented by the state and
//! classified by [`open_case`], but no refinement theorem is claimed for them.
//! There are no admits or axioms in this module.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::cache::{CacheSpec, CachedSpec};
#[cfg(verus_keep_ghost)]
use crate::config::ConfigSpec;
#[cfg(verus_keep_ghost)]
use crate::document::spec_loaded_body;
#[cfg(verus_keep_ghost)]
use crate::handler::{spec_on_event, spec_schedule_wake};
#[cfg(verus_keep_ghost)]
use crate::handler_docs::{
    spec_answered_loading, spec_answered_origin, spec_begin,
    spec_commit_advance, spec_commit_failed, spec_committed, spec_decide,
    spec_dispatch, spec_dispatches, spec_flight_completed, spec_inflight,
    spec_load_origin, spec_loaded_origin, spec_retry, spec_run_origin,
    spec_send_all, spec_take_flight, CommittingSpec, DoneSpec, FlightSpec,
    FlightsSpec, PhaseSpec, ProgressSpec, WorkSpec, WorkingSpec, SWEEP_STEPS,
};
#[cfg(verus_keep_ghost)]
use crate::state::{spec_state_new, Owner, S};
#[cfg(verus_keep_ghost)]
use crate::state_timers::{spec_slot_before, TimersSpec};
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;
#[cfg(verus_keep_ghost)]
use crate::types::{
    AnswerSpec, Armed, EffectSpec, EventSpec, Fired, MessageSpec, OpId,
};

#[cfg(verus_keep_ghost)]
use echod_abstract::model::{empty_store, StateV as AbstractStateV};
#[cfg(verus_keep_ghost)]
use echod_abstract::view::StoreV as AbstractStoreV;
#[cfg(verus_keep_ghost)]
use echod_abstract::ServerConfig;
#[cfg(verus_keep_ghost)]
use echod_concrete::document::{
    well_formed, ProtocolEffectKeyV, StoredDocumentV,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::effects::{
    effects_match, lemma_request_transition_effects, note_effect,
    note_effect_keys, note_effects, safe_effect_config,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::handlers::lemma_request_agrees;
#[cfg(verus_keep_ghost)]
use echod_concrete::interpret::{
    doc_rel, finite_store, origin_prefix, request_agrees, schedule_prefix,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::node::{
    spec_request_transition, spec_stored_body, NoteV, REQUEST_SWEEP_STEPS,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::quick_n_dirty::{on_request, request_preserves_well_formed, routed};
#[cfg(verus_keep_ghost)]
use echod_concrete::store::{StoreError, StoreErrorSpec, StoreReqSpec, StoreRes};
#[cfg(verus_keep_ghost)]
use echod_types::{Request, MAX_TIME};
#[cfg(verus_keep_ghost)]
use crate::verified::flight_spec::{
    answer_v, spec_advance, AAct, AAnswer, AOutcome, AStep,
};

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

// ---------------------------------------------------------------------------
// Endpoint notes become Send effects without filtering
// ---------------------------------------------------------------------------

/// Whether every endpoint note has an addressed production dispatch.
pub open spec fn notes_dispatchable(
    doc: echod_concrete::node::DocumentBodyV,
    notes: Seq<NoteV>,
) -> bool {
    forall|i: int| 0 <= i < notes.len() ==>
        spec_dispatch(doc, #[trigger] notes[i]) is Some
}

/// The logical idempotency key carried by an addressed production message.
pub open spec fn dispatch_effect_key(
    dispatch: (Seq<char>, MessageSpec),
) -> ProtocolEffectKeyV {
    match dispatch.1 {
        MessageSpec::Execute { task_id, .. } =>
            ProtocolEffectKeyV::Execute { id: task_id },
        MessageSpec::Unblock(promise) =>
            ProtocolEffectKeyV::Unblock {
                promise: promise.id@,
                address: dispatch.0,
            },
    }
}

pub open spec fn dispatch_effect_keys(
    dispatches: Seq<(Seq<char>, MessageSpec)>,
) -> Seq<ProtocolEffectKeyV>
    decreases dispatches.len(),
{
    if dispatches.len() == 0 {
        Seq::empty()
    } else {
        dispatch_effect_keys(dispatches.drop_last()).push(
            dispatch_effect_key(dispatches.last()),
        )
    }
}

/// Turn an addressed outbox into the exact process effects it emits.
pub open spec fn send_effects(
    dispatches: Seq<(Seq<char>, MessageSpec)>,
) -> Seq<EffectSpec>
    decreases dispatches.len(),
{
    if dispatches.len() == 0 {
        Seq::empty()
    } else {
        seq![EffectSpec::Send {
            address: dispatches[0].0,
            message: dispatches[0].1,
        }] + send_effects(dispatches.drop_first())
    }
}

proof fn lemma_targeted_has_dispatch_address(
    tags: echod_types::Tags,
    i: int,
)
    requires
        0 <= i,
        echod_concrete::node::spec_tag_key(
            tags,
            "resonate:target"@,
            i,
        ),
    ensures
        crate::reason::spec_target_of(tags@.skip(i)) is Some,
    decreases tags@.len() - i,
{
    reveal(echod_concrete::node::spec_tag_key);
    reveal(crate::reason::spec_target_of);
    reveal_strlit("resonate:target");
    if i < tags@.len() {
        assert(tags@.skip(i)[0] == tags@[i]);
        if tags@[i].0@ != "resonate:target"@ {
            lemma_targeted_has_dispatch_address(tags, i + 1);
            assert(tags@.skip(i).drop_first() =~= tags@.skip(i + 1));
        }
    }
}

proof fn lemma_targeted_has_dispatch_address_at_zero(
    tags: echod_types::Tags,
)
    requires
        echod_concrete::node::spec_targeted(tags),
    ensures
        crate::reason::spec_target_of(tags@) is Some,
{
    reveal(echod_concrete::node::spec_targeted);
    reveal_strlit("resonate:target");
    assert(seq![
        'r','e','s','o','n','a','t','e',':','t','a','r','g','e','t'
    ] =~= "resonate:target"@);
    lemma_targeted_has_dispatch_address(tags, 0);
    assert(tags@.skip(0) =~= tags@);
}

/// Well-formed workflow endpoint notes are all addressable.  This is the
/// semantic fact that prevents `spec_dispatches` from filtering an Execute.
pub proof fn lemma_workflow_effect_notes_dispatchable(
    before: StoredDocumentV,
    after: StoredDocumentV,
    notes: Seq<NoteV>,
)
    requires
        before is Workflow,
        after is Workflow,
        well_formed(after),
        effects_match(before, after, notes),
    ensures
        notes_dispatchable(spec_stored_body(after), notes),
{
    assert forall|i: int| 0 <= i < notes.len() implies
        spec_dispatch(
            spec_stored_body(after),
            #[trigger] notes[i],
        ) is Some by {
        let note = notes[i];
        assert(note_effects(notes).contains(note_effect(note))) by {
            reveal(note_effects);
            assert(exists|j: int|
                0 <= j < notes.len()
                    && note_effect(notes[j]) == note_effect(note)) by {
                assert(0 <= i < notes.len());
            };
        };
        assert(echod_concrete::document::document_effects(before, after)
            .contains(note_effect(note)));
        match note {
            NoteV::Execute { id, version } => {
                reveal(echod_concrete::document::document_effects);
                reveal(echod_concrete::document::workflow_effects);
                reveal(echod_concrete::document::offer_committed);
                let workflow = after->Workflow_0;
                assert(workflow.objects.contains_key(id));
                assert(workflow.objects[id].task is Some);
                reveal(echod_concrete::document::well_formed);
                reveal(echod_concrete::document::workflow_well_formed);
                assert(echod_concrete::document::task_well_formed(
                    workflow.objects[id],
                    workflow.committed_at,
                ));
                reveal(echod_concrete::document::task_well_formed);
                assert(echod_concrete::node::spec_targeted(
                    workflow.objects[id].promise.tags,
                ));
                lemma_targeted_has_dispatch_address_at_zero(
                    workflow.objects[id].promise.tags,
                );
                reveal(spec_dispatch);
            },
            NoteV::Unblock { .. } => {
                reveal(spec_dispatch);
            },
        }
    };
}

proof fn lemma_dispatch_key_of_note(
    doc: echod_concrete::node::DocumentBodyV,
    note: NoteV,
)
    requires
        spec_dispatch(doc, note) is Some,
    ensures
        dispatch_effect_key(spec_dispatch(doc, note)->Some_0)
            == echod_concrete::document::protocol_effect_key(note_effect(note)),
{
    reveal(spec_dispatch);
    match note {
        NoteV::Execute { .. } => {},
        NoteV::Unblock { .. } => {},
    }
}

/// `spec_dispatches` preserves every dispatchable note, in order, and
/// preserves its endpoint idempotency key.
pub proof fn lemma_dispatches_preserve_endpoint_notes(
    doc: echod_concrete::node::DocumentBodyV,
    notes: Seq<NoteV>,
)
    requires
        notes_dispatchable(doc, notes),
    ensures
        ({
            let outbox = spec_dispatches(doc, notes);
            &&& outbox.len() == notes.len()
            &&& dispatch_effect_keys(outbox) == note_effect_keys(notes)
        }),
    decreases notes.len(),
{
    if notes.len() == 0 {
        assert(spec_dispatches(doc, notes)
            =~= Seq::<(Seq<char>, MessageSpec)>::empty());
        assert(note_effect_keys(notes)
            =~= Seq::<ProtocolEffectKeyV>::empty());
    } else {
        let prefix = notes.drop_last();
        let note = notes.last();
        assert(notes_dispatchable(doc, prefix)) by {
            assert forall|i: int| 0 <= i < prefix.len() implies
                spec_dispatch(doc, #[trigger] prefix[i]) is Some by {
                assert(prefix[i] == notes[i]);
            };
        };
        lemma_dispatches_preserve_endpoint_notes(doc, prefix);
        let dispatch = spec_dispatch(doc, note)->Some_0;
        lemma_dispatch_key_of_note(doc, note);
        reveal(spec_dispatches);
        assert(prefix.push(note) =~= notes);
        assert(spec_dispatches(doc, notes)
            == spec_dispatches(doc, prefix).push(dispatch));
        let prefix_outbox = spec_dispatches(doc, prefix);
        let outbox = prefix_outbox.push(dispatch);
        assert(outbox.drop_last() =~= prefix_outbox);
        assert(outbox.last() == dispatch);
        reveal(dispatch_effect_keys);
        assert(dispatch_effect_keys(outbox)
            == dispatch_effect_keys(prefix_outbox).push(
                dispatch_effect_key(dispatch),
            ));
        assert(dispatch_effect_keys(spec_dispatches(doc, notes))
            == dispatch_effect_keys(spec_dispatches(doc, prefix)).push(
                dispatch_effect_key(dispatch),
            ));
        assert(note_effect_keys(notes)
            == note_effect_keys(prefix).push(
                echod_concrete::document::protocol_effect_key(note_effect(note)),
            ));
    }
}

/// The production `send_all` fold appends exactly one `EffectSpec::Send` for
/// each addressed outbox entry and no other effect.
pub proof fn lemma_send_all_exact(
    s: S,
    outbox: Seq<(Seq<char>, MessageSpec)>,
)
    ensures
        spec_send_all(s, outbox).out == s.out + send_effects(outbox),
    decreases outbox.len(),
{
    if outbox.len() == 0 {
        assert(s.out + Seq::<EffectSpec>::empty() =~= s.out);
    } else {
        let first = outbox[0];
        let tail = outbox.drop_first();
        lemma_send_all_exact(
            crate::state::spec_emit(
                s,
                EffectSpec::Send {
                    address: first.0,
                    message: first.1,
                },
            ),
            tail,
        );
        assert(send_effects(outbox)
            == seq![EffectSpec::Send {
                address: first.0,
                message: first.1,
            }] + send_effects(tail));
        assert(crate::state::spec_emit(
            s,
            EffectSpec::Send {
                address: first.0,
                message: first.1,
            },
        ).out == s.out.push(EffectSpec::Send {
            address: first.0,
            message: first.1,
        }));
    }
}

/// Combined endpoint bridge: no note is filtered, each note becomes one Send,
/// and the resulting sends retain the notes' unique effect keys.
pub proof fn lemma_endpoint_notes_send_exact(
    s: S,
    doc: echod_concrete::node::DocumentBodyV,
    notes: Seq<NoteV>,
)
    requires
        notes_dispatchable(doc, notes),
        note_effect_keys(notes).no_duplicates(),
    ensures
        ({
            let outbox = spec_dispatches(doc, notes);
            &&& spec_send_all(s, outbox).out
                == s.out + send_effects(outbox)
            &&& outbox.len() == notes.len()
            &&& dispatch_effect_keys(outbox)
                == note_effect_keys(notes)
            &&& dispatch_effect_keys(outbox).no_duplicates()
        }),
{
    lemma_dispatches_preserve_endpoint_notes(doc, notes);
    lemma_send_all_exact(s, spec_dispatches(doc, notes));
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

/// Mechanical shape of `handler_docs::spec_decide` for request work.
#[verifier::spinoff_prover]
proof fn lemma_spec_decide_request_shape(
    s: S,
    w: WorkingSpec,
    id: u64,
    kind: Seq<char>,
    corr: Seq<char>,
    request: Request,
    action_kind: Option<Seq<char>>,
    offered_now: u64,
)
    ensures
        ({
            let work = WorkSpec::Request {
                id,
                kind,
                corr,
                req: request,
                action_kind,
                now: offered_now,
            };
            let now = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            );
            let (next, commit, done) = spec_decide(s, work, w);
            let (body, _, _, notes) = spec_request_transition(
                spec_stored_body(w.loaded.document),
                request,
                now,
                s.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            );
            &&& next.cfg == s.cfg
            &&& done.outbox == spec_dispatches(body, notes)
            &&& commit.w == w
            &&& commit.now == now
            &&& commit.issued is None
            &&& commit.after
                == echod_concrete::node::spec_advance_stored(
                    w.loaded.document,
                    body,
                    now,
                )
            &&& commit.seq.changed
                == (body != spec_stored_body(w.loaded.document))
            &&& commit.seq.fired is None
            &&& commit.seq.step is Start
            &&& !commit.seq.changed ==> spec_advance(
                commit.seq,
                next.node.core,
                AAnswer::Fresh,
            ).2 == AOutcome::Act(AAct::Done { deleted: false })
        }),
{
    let work = WorkSpec::Request {
        id,
        kind,
        corr,
        req: request,
        action_kind,
        now: offered_now,
    };
    reveal(spec_decide);
    reveal(crate::handler_docs::spec_commit_new);
    let (next, commit, done) = spec_decide(s, work, w);
    if !commit.seq.changed {
        assert(spec_advance(
            commit.seq,
            next.node.core,
            AAnswer::Fresh,
        ).2 == AOutcome::Act(AAct::Done { deleted: false }));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
proof fn lemma_request_logical_after_shape(
    before: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
)
    requires
        before is Workflow,
        routed(before, request),
        well_formed(before),
        echod_concrete::node::spec_stored_committed_at(before) <= now,
        now <= MAX_TIME,
        0 < retry_timeout <= MAX_TIME,
    ensures
        ({
            let (body, _, _, _) = spec_request_transition(
                spec_stored_body(before),
                request,
                now,
                retry_timeout,
                SWEEP_STEPS as nat,
            );
            let logical_after = on_request(
                before,
                request,
                now,
                retry_timeout,
                SWEEP_STEPS as nat,
            );
            &&& spec_stored_body(logical_after) == body
            &&& logical_after is Workflow
            &&& if body != spec_stored_body(before) {
                logical_after == echod_concrete::node::spec_advance_stored(
                    before,
                    body,
                    now,
                )
            } else {
                logical_after == before
            }
        }),
{
    reveal(routed);
    reveal(echod_concrete::quick_n_dirty::request_matches);
    let workflow = before->Workflow_0;
    let original = spec_stored_body(before);
    echod_concrete::quick_n_dirty::lemma_full_implies_relaxed(
        workflow,
        now,
    );
    echod_concrete::quick_n_dirty::lemma_sweep_preserves_relaxed(
        workflow.document,
        workflow.objects,
        now,
        retry_timeout,
        SWEEP_STEPS as nat,
    );
    let swept = echod_concrete::node::spec_sweep(
        original,
        now,
        retry_timeout,
        SWEEP_STEPS as nat,
    ).0;
    assert(swept is Workflow);
    if echod_concrete::node::spec_earliest_in(swept, now) is None {
        echod_concrete::quick_n_dirty::lemma_handle_preserves_relaxed(
            workflow.document,
            swept->Workflow_0,
            request,
            now,
        );
        let handled =
            echod_concrete::node::spec_handle(swept, request, now).0;
        assert(handled is Workflow);
        echod_concrete::quick_n_dirty::lemma_sweep_preserves_relaxed(
            workflow.document,
            handled->Workflow_0,
            now,
            retry_timeout,
            SWEEP_STEPS as nat,
        );
        let closed = echod_concrete::node::spec_sweep(
            handled,
            now,
            retry_timeout,
            SWEEP_STEPS as nat,
        ).0;
        assert(closed is Workflow);
    }
    let (body, response, _, _) = spec_request_transition(
        spec_stored_body(before),
        request,
        now,
        retry_timeout,
        SWEEP_STEPS as nat,
    );
    reveal(on_request);
    if response == echod_concrete::node::spec_unavailable(request) {
        reveal(spec_request_transition);
        assert(body == spec_stored_body(before));
    }
    reveal(spec_request_transition);
    assert(body is Workflow);
}

#[verifier::spinoff_prover]
/// The exact decision made by a normal loaded workflow request.
///
/// `logical_after` is the document that may become persistent.  The
/// `CommittingSpec::after` field is an advanced candidate even when the body
/// did not change, so it is identified with `logical_after` only in the
/// changed branch.  In the unchanged/rejected branch the sequence's first act
/// is `Done`, proving that the advanced candidate is not written.
pub proof fn lemma_normal_request_decision_kernel(
    s: S,
    w: WorkingSpec,
    id: u64,
    kind: Seq<char>,
    corr: Seq<char>,
    request: Request,
    action_kind: Option<Seq<char>>,
    offered_now: u64,
)
    requires
        w.loaded.document is Workflow,
        w.target
            == echod_concrete::node::spec_stored_name(w.loaded.document),
        well_formed(w.loaded.document),
        routed(w.loaded.document, request),
        crate::document::spec_clamp_now(
            crate::document::spec_loaded_committed_at(w.loaded),
            offered_now,
        ) <= MAX_TIME,
        0 < s.cfg.retry_timeout <= MAX_TIME,
        safe_effect_config(
            crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            ),
            s.cfg.retry_timeout,
        ),
        document_ids_bounded(w.loaded.document),
    ensures
        ({
            let work = WorkSpec::Request {
                id,
                kind,
                corr,
                req: request,
                action_kind,
                now: offered_now,
            };
            let now = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            );
            let (next, commit, done) = spec_decide(s, work, w);
            let (body, _, _, notes) = spec_request_transition(
                spec_stored_body(w.loaded.document),
                request,
                now,
                s.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            );
            let logical_after = on_request(
                w.loaded.document,
                request,
                now,
                s.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            );
            &&& next.cfg == s.cfg
            &&& logical_after is Workflow
            &&& well_formed(logical_after)
            &&& effects_match(w.loaded.document, logical_after, notes)
            &&& spec_stored_body(logical_after) == body
            &&& note_effect_keys(notes).no_duplicates()
            &&& notes_dispatchable(
                spec_stored_body(logical_after),
                notes,
            )
            &&& done.outbox == spec_dispatches(body, notes)
            &&& commit.w == w
            &&& commit.now == now
            &&& commit.issued is None
            &&& commit.seq.changed
                == (body != spec_stored_body(w.loaded.document))
            &&& commit.seq.fired is None
            &&& commit.seq.step is Start
            &&& if commit.seq.changed {
                commit.after == logical_after
            } else {
                &&& logical_after == w.loaded.document
                &&& spec_advance(
                    commit.seq,
                    next.node.core,
                    AAnswer::Fresh,
                ).2 == AOutcome::Act(AAct::Done { deleted: false })
            }
        }),
{
    let work = WorkSpec::Request {
        id,
        kind,
        corr,
        req: request,
        action_kind,
        now: offered_now,
    };
    let now = crate::document::spec_clamp_now(
        crate::document::spec_loaded_committed_at(w.loaded),
        offered_now,
    );
    let before = w.loaded.document;
    let (body, response, born, notes) = spec_request_transition(
        spec_stored_body(before),
        request,
        now,
        s.cfg.retry_timeout,
        SWEEP_STEPS as nat,
    );
    let logical_after = on_request(
        before,
        request,
        now,
        s.cfg.retry_timeout,
        SWEEP_STEPS as nat,
    );

    assert(echod_concrete::node::spec_stored_committed_at(before) <= now);
    lemma_normal_request_happy_path(
        before,
        request,
        now,
        s.cfg.retry_timeout,
    );
    lemma_request_logical_after_shape(
        before,
        request,
        now,
        s.cfg.retry_timeout,
    );
    lemma_spec_decide_request_shape(
        s,
        w,
        id,
        kind,
        corr,
        request,
        action_kind,
        offered_now,
    );
    let (next, commit, done) = spec_decide(s, work, w);

    if body != spec_stored_body(before) {
        assert(commit.after == logical_after);
    } else {
        assert(logical_after == before);
        assert(spec_advance(
            commit.seq,
            next.node.core,
            AAnswer::Fresh,
        ).2 == AOutcome::Act(AAct::Done { deleted: false }));
    }
    assert(logical_after is Workflow);
    lemma_workflow_effect_notes_dispatchable(
        before,
        logical_after,
        notes,
    );
}

// ---------------------------------------------------------------------------
// A changed normal request while its origin commit is in flight
// ---------------------------------------------------------------------------

/// The semantic payload carried through one changed normal-request commit.
/// `candidate` is only an in-flight value; this witness says nothing about
/// the contents of the external Store.
pub ghost struct NormalRequestCommitV {
    pub before: StoredDocumentV,
    pub candidate: StoredDocumentV,
    pub notes: Seq<NoteV>,
}

/// A changed normal request in an actual `PhaseSpec::Origin` commit phase.
///
/// The loaded document and candidate remain in `CommittingSpec`, while
/// `DoneSpec` retains the exact outbox.  The allowed sequence steps are the
/// only waiting phases reachable by a normal request: optional key put,
/// conditional document write, and optional previous-key delete.
pub open spec fn normal_request_origin_phase(
    flight: FlightSpec,
    retry_timeout: u64,
    witness: NormalRequestCommitV,
) -> bool {
    match (flight.work, flight.phase) {
        (
            WorkSpec::Request {
                req,
                now: offered_now,
                ..
            },
            PhaseSpec::Origin { commit, done },
        ) => {
            let now = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(commit.w.loaded),
                offered_now,
            );
            let (body, _, _, notes) = spec_request_transition(
                spec_stored_body(witness.before),
                req,
                now,
                retry_timeout,
                SWEEP_STEPS as nat,
            );
            &&& commit.w.loaded.document == witness.before
            &&& commit.after == witness.candidate
            &&& commit.now == now
            &&& commit.seq.changed
            &&& commit.seq.fired is None
            &&& (
                commit.seq.step is PuttingKey
                || commit.seq.step is Writing
                || commit.seq.step is DeletingPrevious
            )
            &&& witness.before is Workflow
            &&& witness.candidate is Workflow
            &&& routed(witness.before, req)
            &&& witness.candidate == on_request(
                witness.before,
                req,
                now,
                retry_timeout,
                SWEEP_STEPS as nat,
            )
            &&& well_formed(witness.before)
            &&& well_formed(witness.candidate)
            &&& witness.notes == notes
            &&& effects_match(
                witness.before,
                witness.candidate,
                witness.notes,
            )
            &&& spec_stored_body(witness.candidate) == body
            &&& notes_dispatchable(
                spec_stored_body(witness.candidate),
                witness.notes,
            )
            &&& note_effect_keys(witness.notes).no_duplicates()
            &&& done.outbox == spec_dispatches(
                spec_stored_body(witness.candidate),
                witness.notes,
            )
        },
        _ => false,
    }
}

pub open spec fn normal_request_inflight(
    s: S,
    fid: u64,
    witness: NormalRequestCommitV,
) -> bool {
    s.flights.inflight.contains_key(fid)
        && normal_request_origin_phase(
            s.flights.inflight[fid],
            s.cfg.retry_timeout,
            witness,
        )
}

/// A normal request whose raced candidate has been discarded and whose next
/// load is now the only Store operation carried by the flight.
pub open spec fn normal_request_reloading(s: S, fid: u64) -> bool {
    s.flights.inflight.contains_key(fid)
        && match s.flights.inflight[fid] {
            FlightSpec {
                work: WorkSpec::Request { .. },
                target: TargetSpec::Origin(_),
                phase: PhaseSpec::Loading { op, .. },
                firing: None,
                debug: false,
                ..
            } => {
                s.ops.contains_key(op)
                    && s.ops[op] == Owner::Flight(fid)
            },
            _ => false,
        }
}

/// The pre-dispatch membership bootstrap branch of `spec_on_event` is not
/// taken. Store-response theorems state this separately from their flight
/// invariants because that branch is an independent state transition.
pub open spec fn startup_membership_tick_skipped(s: S) -> bool {
    !(s.node.members.next_heartbeat is None
        && !s.node.members.refreshing())
}

/// A changed decision always issues the first commit call and enters the
/// actual Origin phase carrying the decision witness.
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn lemma_changed_normal_request_enters_origin_phase(
    s: S,
    f: FlightSpec,
    w: WorkingSpec,
    id: u64,
    kind: Seq<char>,
    corr: Seq<char>,
    request: Request,
    action_kind: Option<Seq<char>>,
    offered_now: u64,
)
    requires
        f.id == id,
        f.work == (WorkSpec::Request {
            id,
            kind,
            corr,
            req: request,
            action_kind,
            now: offered_now,
        }),
        f.phase is Idle,
        f.target == TargetSpec::Origin(w.target),
        f.firing is None,
        !f.debug,
        w.loaded.document is Workflow,
        w.target
            == echod_concrete::node::spec_stored_name(w.loaded.document),
        well_formed(w.loaded.document),
        routed(w.loaded.document, request),
        crate::document::spec_clamp_now(
            crate::document::spec_loaded_committed_at(w.loaded),
            offered_now,
        ) <= MAX_TIME,
        0 < s.cfg.retry_timeout <= MAX_TIME,
        safe_effect_config(
            crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            ),
            s.cfg.retry_timeout,
        ),
        document_ids_bounded(w.loaded.document),
        ({
            let now = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            );
            spec_request_transition(
                spec_stored_body(w.loaded.document),
                request,
                now,
                s.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            ).0 != spec_stored_body(w.loaded.document)
        }),
    ensures
        ({
            let now = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            );
            let notes = spec_request_transition(
                spec_stored_body(w.loaded.document),
                request,
                now,
                s.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            ).3;
            let candidate = on_request(
                w.loaded.document,
                request,
                now,
                s.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            );
            normal_request_inflight(
                spec_run_origin(s, f, w),
                f.id,
                NormalRequestCommitV {
                    before: w.loaded.document,
                    candidate,
                    notes,
                },
            )
        }),
{
    let work = WorkSpec::Request {
        id,
        kind,
        corr,
        req: request,
        action_kind,
        now: offered_now,
    };
    let now = crate::document::spec_clamp_now(
        crate::document::spec_loaded_committed_at(w.loaded),
        offered_now,
    );
    let notes = spec_request_transition(
        spec_stored_body(w.loaded.document),
        request,
        now,
        s.cfg.retry_timeout,
        SWEEP_STEPS as nat,
    ).3;
    let candidate = on_request(
        w.loaded.document,
        request,
        now,
        s.cfg.retry_timeout,
        SWEEP_STEPS as nat,
    );
    lemma_normal_request_decision_kernel(
        s,
        w,
        id,
        kind,
        corr,
        request,
        action_kind,
        offered_now,
    );
    let (decided, commit, done) = spec_decide(s, work, w);
    assert(commit.issued is None);
    assert(commit.seq.step is Start);
    assert(commit.seq.changed);
    reveal(spec_commit_advance);
    let (advanced, next_commit, progress) =
        spec_commit_advance(decided, f.id, commit, None);
    reveal(crate::handler_docs::spec_issue_write);
    match commit.seq.plan.deadline {
        Some(_) => {
            if commit.seq.plan.rearm {
                assert(progress is Issued);
                assert(next_commit.seq.step is PuttingKey);
            } else {
                assert(progress is Issued);
                assert(next_commit.seq.step is Writing);
            }
        },
        None => {
            assert(progress is Issued);
            assert(next_commit.seq.step is Writing);
        },
    }
    assert(next_commit.w == commit.w);
    assert(next_commit.after == commit.after);
    assert(next_commit.now == commit.now);
    assert(next_commit.seq.changed == commit.seq.changed);
    assert(next_commit.seq.fired == commit.seq.fired);
    assert(next_commit.w.loaded.document == w.loaded.document);
    assert(next_commit.after == candidate);
    assert(next_commit.now == now);
    assert(next_commit.seq.changed);
    assert(next_commit.seq.fired is None);
    assert(now == crate::document::spec_clamp_now(
        crate::document::spec_loaded_committed_at(
            next_commit.w.loaded,
        ),
        offered_now,
    ));
    assert(candidate is Workflow);
    assert(candidate == on_request(
        w.loaded.document,
        request,
        now,
        s.cfg.retry_timeout,
        SWEEP_STEPS as nat,
    ));
    assert(well_formed(candidate));
    assert(effects_match(
        w.loaded.document,
        candidate,
        notes,
    ));
    assert(notes == spec_request_transition(
        spec_stored_body(w.loaded.document),
        request,
        now,
        s.cfg.retry_timeout,
        SWEEP_STEPS as nat,
    ).3);
    assert(spec_stored_body(candidate)
        == spec_request_transition(
            spec_stored_body(w.loaded.document),
            request,
            now,
            s.cfg.retry_timeout,
            SWEEP_STEPS as nat,
        ).0);
    assert(done.outbox == spec_dispatches(
        spec_stored_body(candidate),
        notes,
    ));
    assert(notes_dispatchable(
        spec_stored_body(candidate),
        notes,
    ));
    assert(note_effect_keys(notes).no_duplicates());
    reveal(spec_run_origin);
    reveal(spec_inflight);
    let next_flight = FlightSpec {
        phase: PhaseSpec::Origin {
            commit: next_commit,
            done,
        },
        ..f
    };
    assert(normal_request_origin_phase(
        next_flight,
        s.cfg.retry_timeout,
        NormalRequestCommitV {
            before: w.loaded.document,
            candidate,
            notes,
        },
    ));
    assert(spec_run_origin(s, f, w)
        == spec_inflight(advanced, next_flight));
    assert(decided.cfg == s.cfg);
    assert(advanced.cfg == decided.cfg);
    let result = spec_run_origin(s, f, w);
    assert(result.cfg == s.cfg);
    assert(result.flights.inflight.contains_key(f.id));
    assert(result.flights.inflight[f.id] == next_flight);
    assert(normal_request_inflight(
        result,
        f.id,
        NormalRequestCommitV {
            before: w.loaded.document,
            candidate,
            notes,
        },
    ));
}

/// Any response that makes the production commit driver issue another call
/// preserves the whole in-flight witness.  In this normal-request slice that
/// covers key-put success (next: write) and write success when an old key must
/// be deleted (next: delete).
#[verifier::spinoff_prover]
pub proof fn lemma_normal_request_issued_phase_preserves(
    s: S,
    fid: u64,
    f: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
    response: StoreRes,
    witness: NormalRequestCommitV,
)
    requires
        normal_request_origin_phase(
            FlightSpec {
                phase: PhaseSpec::Origin { commit, done },
                ..f
            },
            s.cfg.retry_timeout,
            witness,
        ),
        spec_commit_advance(s, fid, commit, Some(response)).2 is Issued,
    ensures
        ({
            let next = spec_commit_advance(s, fid, commit, Some(response)).1;
            normal_request_origin_phase(
                FlightSpec {
                    phase: PhaseSpec::Origin { commit: next, done },
                    ..f
                },
                s.cfg.retry_timeout,
                witness,
            )
        }),
{
    reveal(spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    match commit.seq.step {
        AStep::PuttingKey(_) => {},
        AStep::Writing { .. } => {},
        AStep::DeletingPrevious(_) => {},
        _ => {},
    }
}

/// A successful answer to the key put advances the production driver to the
/// conditional document write without changing the request witness.
#[verifier::spinoff_prover]
pub proof fn lemma_normal_request_key_put_success(
    s: S,
    fid: u64,
    f: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
    response: StoreRes,
    witness: NormalRequestCommitV,
)
    requires
        normal_request_origin_phase(
            FlightSpec {
                phase: PhaseSpec::Origin { commit, done },
                ..f
            },
            s.cfg.retry_timeout,
            witness,
        ),
        commit.seq.step is PuttingKey,
        answer_v(commit.seq.step, Some(response))
            == AAnswer::Done,
    ensures
        spec_commit_advance(s, fid, commit, Some(response)).2 is Issued,
        ({
            let next = spec_commit_advance(
                s,
                fid,
                commit,
                Some(response),
            ).1;
            &&& next.seq.step is Writing
            &&& normal_request_origin_phase(
                FlightSpec {
                    phase: PhaseSpec::Origin { commit: next, done },
                    ..f
                },
                s.cfg.retry_timeout,
                witness,
            )
        }),
{
    reveal(spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    lemma_normal_request_issued_phase_preserves(
        s,
        fid,
        f,
        commit,
        done,
        response,
        witness,
    );
}

/// A successful conditional document-write answer either completes the
/// normal commit or issues the best-effort deletion of the previous key.
/// This is a response-path statement only; it does not assert that the Store
/// durably performed the write.
#[verifier::spinoff_prover]
pub proof fn lemma_normal_request_document_write_success(
    s: S,
    fid: u64,
    f0: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
    response: StoreRes,
    tag: Seq<char>,
    witness: NormalRequestCommitV,
)
    requires
        f0.phase is Idle,
        normal_request_origin_phase(
            FlightSpec {
                phase: PhaseSpec::Origin { commit, done },
                ..f0
            },
            s.cfg.retry_timeout,
            witness,
        ),
        commit.seq.step is Writing,
        answer_v(commit.seq.step, Some(response))
            == AAnswer::Written(tag),
    ensures
        ({
            let advanced =
                spec_commit_advance(s, fid, commit, Some(response));
            &&& (
                advanced.2 is Issued
                || advanced.2 == ProgressSpec::Done(Fired::Kept)
            )
            &&& if advanced.2 is Issued {
                &&& advanced.1.seq.step is DeletingPrevious
                &&& normal_request_origin_phase(
                    FlightSpec {
                        phase: PhaseSpec::Origin {
                            commit: advanced.1,
                            done,
                        },
                        ..f0
                    },
                    s.cfg.retry_timeout,
                    witness,
                )
            } else {
                spec_answered_origin(
                    s,
                    fid,
                    f0,
                    commit,
                    done,
                    response,
                ) == spec_committed(
                    advanced.0,
                    f0,
                    done,
                    Fired::Kept,
                )
            }
        }),
{
    reveal(spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(spec_answered_origin);
    let advanced = spec_commit_advance(
        s,
        fid,
        commit,
        Some(response),
    );
    if advanced.2 is Issued {
        lemma_normal_request_issued_phase_preserves(
            s,
            fid,
            f0,
            commit,
            done,
            response,
            witness,
        );
    }
}

/// Once the previous-key deletion is answered (successfully or not), the
/// normal sequence is complete.  Deletion is deliberately best effort.
#[verifier::spinoff_prover]
pub proof fn lemma_normal_request_previous_key_delete_completes(
    s: S,
    fid: u64,
    f0: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
    response: StoreRes,
    witness: NormalRequestCommitV,
)
    requires
        f0.phase is Idle,
        normal_request_origin_phase(
            FlightSpec {
                phase: PhaseSpec::Origin { commit, done },
                ..f0
            },
            s.cfg.retry_timeout,
            witness,
        ),
        commit.seq.step is DeletingPrevious,
    ensures
        spec_commit_advance(s, fid, commit, Some(response)).2
            == ProgressSpec::Done(Fired::Kept),
        ({
            let advanced =
                spec_commit_advance(s, fid, commit, Some(response));
            spec_answered_origin(
                s,
                fid,
                f0,
                commit,
                done,
                response,
            ) == spec_committed(
                advanced.0,
                f0,
                done,
                Fired::Kept,
            )
        }),
{
    reveal(spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(spec_answered_origin);
}

/// A precondition race from either the key-put or conditional-write phase
/// strips the Origin phase before retry.  In particular,
/// `spec_commit_failed` receives `f0`, whose phase is Idle: neither the
/// candidate in `commit` nor `done.outbox` is passed to `spec_retry`.
#[verifier::spinoff_prover]
pub proof fn lemma_normal_request_precondition_failed_discards(
    s: S,
    fid: u64,
    f0: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
    response: StoreRes,
    witness: NormalRequestCommitV,
)
    requires
        f0.phase is Idle,
        normal_request_origin_phase(
            FlightSpec {
                phase: PhaseSpec::Origin { commit, done },
                ..f0
            },
            s.cfg.retry_timeout,
            witness,
        ),
        commit.seq.step is PuttingKey
            || commit.seq.step is Writing,
        answer_v(commit.seq.step, Some(response))
            == AAnswer::Failed(StoreError::PreconditionFailed),
    ensures
        spec_commit_advance(s, fid, commit, Some(response)).2
            == ProgressSpec::Failed(
                StoreErrorSpec::PreconditionFailed,
            ),
        ({
            let advanced =
                spec_commit_advance(s, fid, commit, Some(response));
            spec_answered_origin(
                s,
                fid,
                f0,
                commit,
                done,
                response,
            ) == spec_commit_failed(
                advanced.0,
                f0,
                StoreErrorSpec::PreconditionFailed,
            )
        }),
        !normal_request_origin_phase(
            f0,
            s.cfg.retry_timeout,
            witness,
        ),
{
    reveal(spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(spec_answered_origin);
}

/// With retry budget remaining, a precondition race immediately starts a
/// fresh origin load.  The only payload retained by the flight is its original
/// request metadata; the failed `commit` and `done` values are absent from the
/// resulting Loading phase.
#[verifier::spinoff_prover]
pub proof fn lemma_normal_request_precondition_failed_starts_reload(
    s: S,
    fid: u64,
    f0: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
    response: StoreRes,
    witness: NormalRequestCommitV,
)
    requires
        f0.id == fid,
        f0.phase is Idle,
        f0.target is Origin,
        f0.firing is None,
        !f0.debug,
        f0.attempt.wrapping_add(1)
            <= s.flights.max_retries,
        normal_request_origin_phase(
            FlightSpec {
                phase: PhaseSpec::Origin { commit, done },
                ..f0
            },
            s.cfg.retry_timeout,
            witness,
        ),
        commit.seq.step is PuttingKey
            || commit.seq.step is Writing,
        answer_v(commit.seq.step, Some(response))
            == AAnswer::Failed(StoreError::PreconditionFailed),
    ensures
        normal_request_reloading(
            spec_answered_origin(
                s,
                fid,
                f0,
                commit,
                done,
                response,
            ),
            fid,
        ),
{
    lemma_normal_request_precondition_failed_discards(
        s,
        fid,
        f0,
        commit,
        done,
        response,
        witness,
    );
    reveal(spec_commit_advance);
    reveal(crate::handler_docs::spec_answered);
    reveal(spec_commit_failed);
    reveal(spec_retry);
    reveal(spec_begin);
    reveal(spec_load_origin);
    reveal(crate::cache::spec_get);
    reveal(spec_inflight);
    let result = spec_answered_origin(
        s,
        fid,
        f0,
        commit,
        done,
        response,
    );
    let advanced =
        spec_commit_advance(s, fid, commit, Some(response));
    assert(result == spec_commit_failed(
        advanced.0,
        f0,
        StoreErrorSpec::PreconditionFailed,
    ));
    assert(advanced.0.flights.max_retries
        == s.flights.max_retries);
    match f0.target {
        TargetSpec::Origin(origin) => {
            assert(result.flights.inflight.contains_key(fid));
            let reload = result.flights.inflight[fid];
            assert(reload.work == f0.work);
            assert(reload.target == f0.target);
            assert(reload.firing is None);
            assert(!reload.debug);
            assert(reload.phase is Loading);
            let load_op = match reload.phase {
                PhaseSpec::Loading { op, .. } => op,
                _ => fid,
            };
            assert(result.ops.contains_key(load_op));
            assert(result.ops[load_op] == Owner::Flight(fid));
            assert(normal_request_reloading(result, fid));
        },
        _ => {},
    }
}

/// A successful matching reload re-runs the normal request against the newly
/// loaded document and establishes a fresh candidate/outbox witness.
///
/// `spec_decode_workflow` is currently uninterpreted, so `well_formed` and the
/// loaded document's origin are explicit preconditions rather than codec
/// conclusions.
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn lemma_matching_well_formed_reload_reestablishes_origin_phase(
    s: S,
    fid: u64,
    op: u64,
    outcome: StoreRes,
    flight: FlightSpec,
    revalidating: Option<CachedSpec>,
    w: WorkingSpec,
    origin: Seq<char>,
    id: u64,
    kind: Seq<char>,
    corr: Seq<char>,
    request: Request,
    action_kind: Option<Seq<char>>,
    offered_now: u64,
)
    requires
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid] == flight,
        flight.id == fid,
        fid == id,
        flight.work == (WorkSpec::Request {
            id,
            kind,
            corr,
            req: request,
            action_kind,
            now: offered_now,
        }),
        flight.target == TargetSpec::Origin(origin),
        flight.phase
            == (PhaseSpec::Loading { op, revalidating }),
        flight.firing is None,
        !flight.debug,
        ({
            let taken = spec_take_flight(s, fid);
            spec_loaded_origin(
                taken,
                origin,
                revalidating,
                outcome,
            ).1 == Ok(w)
        }),
        w.target == origin,
        w.loaded.document is Workflow,
        w.target
            == echod_concrete::node::spec_stored_name(w.loaded.document),
        // Explicit until the codec has a well-formedness law.
        well_formed(w.loaded.document),
        routed(w.loaded.document, request),
        ({
            let taken = spec_take_flight(s, fid);
            let loaded = spec_loaded_origin(
                taken,
                origin,
                revalidating,
                outcome,
            ).0;
            let now = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            );
            &&& now <= MAX_TIME
            &&& 0 < loaded.cfg.retry_timeout <= MAX_TIME
            &&& safe_effect_config(
                now,
                loaded.cfg.retry_timeout,
            )
            &&& document_ids_bounded(w.loaded.document)
            &&& spec_request_transition(
                spec_stored_body(w.loaded.document),
                request,
                now,
                loaded.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            ).0 != spec_stored_body(w.loaded.document)
        }),
    ensures
        ({
            let taken = spec_take_flight(s, fid);
            let loaded = spec_loaded_origin(
                taken,
                origin,
                revalidating,
                outcome,
            ).0;
            let now = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            );
            let notes = spec_request_transition(
                spec_stored_body(w.loaded.document),
                request,
                now,
                loaded.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            ).3;
            let candidate = on_request(
                w.loaded.document,
                request,
                now,
                loaded.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            );
            normal_request_inflight(
                spec_flight_completed(s, fid, op, outcome),
                fid,
                NormalRequestCommitV {
                    before: w.loaded.document,
                    candidate,
                    notes,
                },
            )
        }),
{
    let taken = spec_take_flight(s, fid);
    let (loaded, result) = spec_loaded_origin(
        taken,
        origin,
        revalidating,
        outcome,
    );
    let f0 = FlightSpec {
        phase: PhaseSpec::Idle,
        ..flight
    };
    lemma_changed_normal_request_enters_origin_phase(
        loaded,
        f0,
        w,
        id,
        kind,
        corr,
        request,
        action_kind,
        offered_now,
    );
    reveal(spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    reveal(spec_answered_loading);
}

/// A matching flight-owned operation whose flight is in Origin reaches
/// `spec_answered_origin` with an Idle copy of the flight.  This is the point
/// at which failed commits cannot accidentally retain the candidate/outbox.
#[verifier::spinoff_prover]
pub proof fn lemma_matching_origin_store_response_routes_answer(
    s: S,
    fid: u64,
    op: u64,
    response: StoreRes,
    flight: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
)
    requires
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid] == flight,
        flight.phase == (PhaseSpec::Origin { commit, done }),
        flight.phase.expects() == Some(op),
    ensures
        spec_flight_completed(s, fid, op, response)
            == spec_answered_origin(
                spec_take_flight(s, fid),
                fid,
                FlightSpec { phase: PhaseSpec::Idle, ..flight },
                commit,
                done,
                response,
            ),
{
    reveal(spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
}

proof fn lemma_schedule_wake_preserves_flights_and_ops(s: S)
    ensures
        spec_schedule_wake(s).flights == s.flights,
        spec_schedule_wake(s).ops == s.ops,
        spec_schedule_wake(s).cfg == s.cfg,
{
    reveal(spec_schedule_wake);
}

/// The actual production Store event for a matching raced Origin call returns
/// the flight to Loading, provided retry budget remains.  The independent
/// startup membership tick is explicitly excluded.
#[verifier::spinoff_prover]
pub proof fn lemma_matching_precondition_failed_store_event_starts_reload(
    s: S,
    fid: u64,
    op: u64,
    response: StoreRes,
    clock: u64,
    flight: FlightSpec,
    commit: CommittingSpec,
    done: DoneSpec,
    witness: NormalRequestCommitV,
)
    requires
        startup_membership_tick_skipped(s),
        s.ops.contains_key(op),
        s.ops[op] == Owner::Flight(fid),
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid] == flight,
        flight.id == fid,
        flight.phase == (PhaseSpec::Origin { commit, done }),
        flight.phase.expects() == Some(op),
        flight.target is Origin,
        flight.firing is None,
        !flight.debug,
        flight.attempt.wrapping_add(1)
            <= s.flights.max_retries,
        normal_request_origin_phase(
            flight,
            s.cfg.retry_timeout,
            witness,
        ),
        commit.seq.step is PuttingKey
            || commit.seq.step is Writing,
        answer_v(commit.seq.step, Some(response))
            == AAnswer::Failed(StoreError::PreconditionFailed),
    ensures
        normal_request_reloading(
            spec_on_event(
                s,
                EventSpec::Store { op, response, clock },
            ).0,
            fid,
        ),
{
    let timed = S { clock, ..s };
    let without_op = S {
        ops: timed.ops.remove(op),
        ..timed
    };
    let f0 = FlightSpec { phase: PhaseSpec::Idle, ..flight };
    let taken = spec_take_flight(without_op, fid);
    lemma_matching_origin_store_response_routes_answer(
        without_op,
        fid,
        op,
        response,
        flight,
        commit,
        done,
    );
    lemma_normal_request_precondition_failed_starts_reload(
        taken,
        fid,
        f0,
        commit,
        done,
        response,
        witness,
    );
    let handled =
        spec_flight_completed(without_op, fid, op, response);
    lemma_schedule_wake_preserves_flights_and_ops(handled);
    reveal(spec_on_event);
}

/// The matching production Store event for a successful, well-formed reload
/// recomputes the request decision from the reloaded document.  As above, the
/// startup membership tick is an explicit exclusion, not folded into the
/// reload assumptions.
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn lemma_matching_well_formed_reload_store_event_reestablishes_origin(
    s: S,
    fid: u64,
    op: u64,
    outcome: StoreRes,
    clock: u64,
    flight: FlightSpec,
    revalidating: Option<CachedSpec>,
    w: WorkingSpec,
    origin: Seq<char>,
    id: u64,
    kind: Seq<char>,
    corr: Seq<char>,
    request: Request,
    action_kind: Option<Seq<char>>,
    offered_now: u64,
)
    requires
        startup_membership_tick_skipped(s),
        s.ops.contains_key(op),
        s.ops[op] == Owner::Flight(fid),
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid] == flight,
        flight.id == fid,
        fid == id,
        flight.work == (WorkSpec::Request {
            id,
            kind,
            corr,
            req: request,
            action_kind,
            now: offered_now,
        }),
        flight.target == TargetSpec::Origin(origin),
        flight.phase
            == (PhaseSpec::Loading { op, revalidating }),
        flight.firing is None,
        !flight.debug,
        ({
            let timed = S { clock, ..s };
            let without_op = S {
                ops: timed.ops.remove(op),
                ..timed
            };
            let taken = spec_take_flight(without_op, fid);
            spec_loaded_origin(
                taken,
                origin,
                revalidating,
                outcome,
            ).1 == Ok(w)
        }),
        w.target == origin,
        w.loaded.document is Workflow,
        w.target
            == echod_concrete::node::spec_stored_name(w.loaded.document),
        // Explicit until the codec has a well-formedness law.
        well_formed(w.loaded.document),
        routed(w.loaded.document, request),
        ({
            let timed = S { clock, ..s };
            let without_op = S {
                ops: timed.ops.remove(op),
                ..timed
            };
            let taken = spec_take_flight(without_op, fid);
            let loaded = spec_loaded_origin(
                taken,
                origin,
                revalidating,
                outcome,
            ).0;
            let now = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            );
            &&& now <= MAX_TIME
            &&& 0 < loaded.cfg.retry_timeout <= MAX_TIME
            &&& safe_effect_config(
                now,
                loaded.cfg.retry_timeout,
            )
            &&& document_ids_bounded(w.loaded.document)
            &&& spec_request_transition(
                spec_stored_body(w.loaded.document),
                request,
                now,
                loaded.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            ).0 != spec_stored_body(w.loaded.document)
        }),
    ensures
        ({
            let timed = S { clock, ..s };
            let without_op = S {
                ops: timed.ops.remove(op),
                ..timed
            };
            let taken = spec_take_flight(without_op, fid);
            let loaded = spec_loaded_origin(
                taken,
                origin,
                revalidating,
                outcome,
            ).0;
            let now = crate::document::spec_clamp_now(
                crate::document::spec_loaded_committed_at(w.loaded),
                offered_now,
            );
            let notes = spec_request_transition(
                spec_stored_body(w.loaded.document),
                request,
                now,
                loaded.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            ).3;
            let candidate = on_request(
                w.loaded.document,
                request,
                now,
                loaded.cfg.retry_timeout,
                SWEEP_STEPS as nat,
            );
            normal_request_inflight(
                spec_on_event(
                    s,
                    EventSpec::Store { op, response: outcome, clock },
                ).0,
                fid,
                NormalRequestCommitV {
                    before: w.loaded.document,
                    candidate,
                    notes,
                },
            )
        }),
{
    let timed = S { clock, ..s };
    let without_op = S {
        ops: timed.ops.remove(op),
        ..timed
    };
    lemma_matching_well_formed_reload_reestablishes_origin_phase(
        without_op,
        fid,
        op,
        outcome,
        flight,
        revalidating,
        w,
        origin,
        id,
        kind,
        corr,
        request,
        action_kind,
        offered_now,
    );
    let handled =
        spec_flight_completed(without_op, fid, op, outcome);
    lemma_schedule_wake_preserves_flights_and_ops(handled);
    reveal(spec_on_event);
}

/// The matching production `EventSpec::Store` arm removes the operation,
/// routes the response to the owning flight, schedules the next wake, and
/// returns (then clears) the accumulated outbox.  This is the direct bridge
/// from the response lemmas above to `spec_on_event`; it still says nothing
/// about a Rover Store transition or durable bytes.
#[verifier::spinoff_prover]
pub proof fn lemma_owned_store_event_runs_flight_completion(
    s: S,
    fid: u64,
    op: u64,
    response: StoreRes,
    clock: u64,
)
    requires
        startup_membership_tick_skipped(s),
        s.ops.contains_key(op),
        s.ops[op] == Owner::Flight(fid),
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid].phase.expects() == Some(op),
    ensures
        ({
            let timed = S { clock, ..s };
            let without_op = S {
                ops: timed.ops.remove(op),
                ..timed
            };
            let handled =
                spec_flight_completed(without_op, fid, op, response);
            let scheduled = spec_schedule_wake(handled);
            spec_on_event(
                s,
                EventSpec::Store { op, response, clock },
            ) == (
                S { out: Seq::empty(), ..scheduled },
                scheduled.out,
            )
        }),
{
    reveal(spec_on_event);
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
