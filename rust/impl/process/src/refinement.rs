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
//! Failure, racing-CAS, concurrent flights, membership listing/configuration
//! completions, and timer fire/commit steps remain classified by
//! [`open_case`]. The bounded startup wake and successful announcement
//! completion are proved below: they advance membership from announce to list,
//! leave document and timer state unchanged, and preserve the full relation as
//! abstract stutters. There are no admits or axioms in this module.

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
    FlightsSpec, PhaseSpec, ProgressSpec, WorkSpec, WorkingSpec,
};
#[cfg(verus_keep_ghost)]
use crate::state::{spec_state_new, Owner, S};
#[cfg(verus_keep_ghost)]
use crate::state_node::RefreshSpec;
#[cfg(verus_keep_ghost)]
use crate::state_timers::{spec_slot_before, ListingSpec, TimersSpec};
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
    spec_request_transition, spec_stored_body, NoteV,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::quick_n_dirty::{on_request, request_preserves_well_formed, routed};
#[cfg(verus_keep_ghost)]
use echod_concrete::store::{
    spec_before, StoreError, StoreErrorSpec, StoreReqSpec, StoreRes,
};
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

pub open spec fn timer_slots_pairwise_ordered(
    slots: Seq<crate::state_timers::SlotSpec>,
) -> bool {
    forall|i: int, j: int|
        #![trigger slots[i], slots[j]]
        0 <= i < j < slots.len() ==> {
            &&& slots[i] != slots[j]
            &&& spec_slot_before(
                slots[i],
                slots[j],
            )
        }
}

pub open spec fn timer_wheel_ordered(timers: TimersSpec) -> bool {
    timer_slots_pairwise_ordered(timers.wheel.armed)
}

pub open spec fn timer_slots_adjacent_ordered(
    slots: Seq<crate::state_timers::SlotSpec>,
) -> bool
    decreases slots.len(),
{
    slots.len() <= 1 || (
        spec_slot_before(slots[0], slots[1])
        && timer_slots_adjacent_ordered(slots.drop_first())
    )
}

proof fn lemma_timer_key_before_irreflexive(key: Seq<char>)
    ensures
        !spec_before(key, key),
    decreases key.len(),
{
    if key.len() > 0 {
        lemma_timer_key_before_irreflexive(key.drop_first());
    }
}

proof fn lemma_timer_key_before_transitive(
    a: Seq<char>,
    b: Seq<char>,
    c: Seq<char>,
)
    requires
        spec_before(a, b),
        spec_before(b, c),
    ensures
        spec_before(a, c),
    decreases a.len() + b.len() + c.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if c.len() == 0 {
    } else if a[0] != b[0] {
    } else if b[0] != c[0] {
    } else {
        lemma_timer_key_before_transitive(
            a.drop_first(),
            b.drop_first(),
            c.drop_first(),
        );
    }
}

proof fn lemma_timer_key_before_total(a: Seq<char>, b: Seq<char>)
    requires
        a != b,
    ensures
        spec_before(a, b) || spec_before(b, a),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        if b.len() == 0 {
            assert(a =~= b);
        }
    } else if b.len() == 0 {
    } else if a[0] != b[0] {
        assert(a[0] < b[0] || b[0] < a[0]);
    } else {
        assert(a =~= seq![a[0]] + a.drop_first());
        assert(b =~= seq![b[0]] + b.drop_first());
        if a.drop_first() == b.drop_first() {
            assert(a == b);
        }
        lemma_timer_key_before_total(a.drop_first(), b.drop_first());
    }
}

proof fn lemma_timer_slot_before_transitive(
    a: crate::state_timers::SlotSpec,
    b: crate::state_timers::SlotSpec,
    c: crate::state_timers::SlotSpec,
)
    requires
        spec_slot_before(a, b),
        spec_slot_before(b, c),
    ensures
        spec_slot_before(a, c),
{
    if a.0 == b.0 && b.0 == c.0 {
        lemma_timer_key_before_transitive(a.1, b.1, c.1);
    }
}

proof fn lemma_timer_slot_before_irreflexive(
    slot: crate::state_timers::SlotSpec,
)
    ensures
        !spec_slot_before(slot, slot),
{
    lemma_timer_key_before_irreflexive(slot.1);
}

proof fn lemma_timer_slot_before_total(
    a: crate::state_timers::SlotSpec,
    b: crate::state_timers::SlotSpec,
)
    requires
        a != b,
    ensures
        spec_slot_before(a, b) || spec_slot_before(b, a),
{
    if a.0 == b.0 {
        assert(a.1 != b.1);
        lemma_timer_key_before_total(a.1, b.1);
    }
}

proof fn lemma_adjacent_ordered_head_before(
    slots: Seq<crate::state_timers::SlotSpec>,
    j: int,
)
    requires
        timer_slots_adjacent_ordered(slots),
        0 < j < slots.len(),
    ensures
        spec_slot_before(slots[0], slots[j]),
    decreases j,
{
    reveal(timer_slots_adjacent_ordered);
    if j > 1 {
        lemma_adjacent_ordered_head_before(
            slots.drop_first(),
            j - 1,
        );
        assert(slots.drop_first()[0] == slots[1]);
        assert(slots.drop_first()[j - 1] == slots[j]);
        lemma_timer_slot_before_transitive(
            slots[0],
            slots[1],
            slots[j],
        );
    }
}

proof fn lemma_adjacent_ordered_skip(
    slots: Seq<crate::state_timers::SlotSpec>,
    i: int,
)
    requires
        timer_slots_adjacent_ordered(slots),
        0 <= i <= slots.len(),
    ensures
        timer_slots_adjacent_ordered(slots.skip(i)),
    decreases i,
{
    reveal(timer_slots_adjacent_ordered);
    if i == 0 {
        assert(slots.skip(0) =~= slots);
    } else {
        lemma_adjacent_ordered_skip(slots.drop_first(), i - 1);
        assert(slots.drop_first().skip(i - 1) =~= slots.skip(i));
    }
}

proof fn lemma_adjacent_ordered_implies_pairwise(
    slots: Seq<crate::state_timers::SlotSpec>,
)
    requires
        timer_slots_adjacent_ordered(slots),
    ensures
        timer_slots_pairwise_ordered(slots),
{
    assert(timer_slots_pairwise_ordered(slots)) by {
        reveal(timer_slots_pairwise_ordered);
        assert forall|i: int, j: int|
            #![trigger slots[i], slots[j]]
            0 <= i < j < slots.len() implies {
                &&& slots[i] != slots[j]
                &&& spec_slot_before(slots[i], slots[j])
            } by {
            let suffix = slots.skip(i);
            assert(suffix[0] == slots[i]);
            assert(suffix[j - i] == slots[j]);
            lemma_adjacent_ordered_skip(slots, i);
            lemma_adjacent_ordered_head_before(suffix, j - i);
            assert(spec_slot_before(slots[i], slots[j]));
            if slots[i] == slots[j] {
                lemma_timer_slot_before_irreflexive(slots[i]);
                assert(false);
            }
        }
    }
}

proof fn lemma_pairwise_implies_adjacent_ordered(
    slots: Seq<crate::state_timers::SlotSpec>,
)
    requires
        timer_slots_pairwise_ordered(slots),
    ensures
        timer_slots_adjacent_ordered(slots),
    decreases slots.len(),
{
    reveal(timer_slots_adjacent_ordered);
    reveal(timer_slots_pairwise_ordered);
    if slots.len() > 1 {
        assert forall|i: int, j: int|
            0 <= i < j < slots.drop_first().len() implies {
                &&& slots.drop_first()[i]
                    != slots.drop_first()[j]
                &&& spec_slot_before(
                    slots.drop_first()[i],
                    slots.drop_first()[j],
                )
            } by {
            assert(slots.drop_first()[i] == slots[i + 1]);
            assert(slots.drop_first()[j] == slots[j + 1]);
            assert(slots[i + 1] != slots[j + 1]);
            assert(spec_slot_before(
                slots[i + 1],
                slots[j + 1],
            ));
        }
        lemma_pairwise_implies_adjacent_ordered(
            slots.drop_first(),
        );
    }
}

proof fn lemma_arm_preserves_adjacent_order(
    slots: Seq<crate::state_timers::SlotSpec>,
    at: u64,
    key: Seq<char>,
)
    requires
        timer_slots_adjacent_ordered(slots),
    ensures
        timer_slots_adjacent_ordered(
            crate::state_timers::spec_arm(slots, at, key),
        ),
    decreases slots.len(),
{
    reveal(timer_slots_adjacent_ordered);
    let added = (at, key);
    if slots.len() == 0 {
        assert(crate::state_timers::spec_arm(slots, at, key)
            =~= seq![added]);
    } else if slots[0] == added {
        assert(crate::state_timers::spec_arm(slots, at, key)
            == slots);
    } else if spec_slot_before(added, slots[0]) {
        let prepended = seq![added] + slots;
        assert(crate::state_timers::spec_arm(slots, at, key)
            =~= prepended);
        assert(prepended[0] == added);
        assert(prepended[1] == slots[0]);
        assert(prepended.drop_first() =~= slots);
        assert(timer_slots_adjacent_ordered(
            prepended.drop_first(),
        ));
        assert(timer_slots_adjacent_ordered(prepended));
    } else {
        lemma_timer_slot_before_total(slots[0], added);
        assert(spec_slot_before(slots[0], added));
        lemma_arm_preserves_adjacent_order(
            slots.drop_first(),
            at,
            key,
        );
        let tail = crate::state_timers::spec_arm(
            slots.drop_first(),
            at,
            key,
        );
        assert(timer_slots_adjacent_ordered(tail));
        assert(tail.len() > 0);
        if slots.drop_first().len() == 0
            || slots.drop_first()[0] == added
            || spec_slot_before(added, slots.drop_first()[0])
        {
            assert(tail[0] == added);
            assert(spec_slot_before(slots[0], tail[0]));
        } else {
            assert(tail[0] == slots.drop_first()[0]);
            assert(slots.len() > 1);
            assert(spec_slot_before(slots[0], slots[1]));
            assert(slots.drop_first()[0] == slots[1]);
            assert(spec_slot_before(slots[0], tail[0]));
        }
        let prepended = seq![slots[0]] + tail;
        assert(crate::state_timers::spec_arm(slots, at, key)
            =~= prepended);
        assert(prepended[0] == slots[0]);
        assert(prepended[1] == tail[0]);
        assert(prepended.drop_first() =~= tail);
        assert(timer_slots_adjacent_ordered(
            prepended.drop_first(),
        ));
        assert(timer_slots_adjacent_ordered(prepended));
    }
    assert(timer_slots_adjacent_ordered(
        crate::state_timers::spec_arm(slots, at, key),
    ));
}

pub proof fn lemma_arm_preserves_timer_wheel_order(
    slots: Seq<crate::state_timers::SlotSpec>,
    at: u64,
    key: Seq<char>,
)
    requires
        timer_slots_pairwise_ordered(slots),
    ensures
        timer_slots_pairwise_ordered(
            crate::state_timers::spec_arm(slots, at, key),
        ),
{
    lemma_pairwise_implies_adjacent_ordered(slots);
    lemma_arm_preserves_adjacent_order(slots, at, key);
    lemma_adjacent_ordered_implies_pairwise(
        crate::state_timers::spec_arm(slots, at, key),
    );
}

/// `inflight` is the number of accepted timer firings that have not called
/// `spec_timer_fired` yet.  It reserves sweep capacity even when the target's
/// document lane is busy and `spec_submit` queues the work.  The backlog is a
/// separate queue of due keys that have not reserved capacity, so there is no
/// ordering relation between their lengths.
pub open spec fn timer_accounting_consistent(timers: TimersSpec) -> bool {
    timers.inflight <= crate::state_timers::CONCURRENCY
}

pub open spec fn timers_consistent(timers: TimersSpec) -> bool {
    &&& timer_wheel_ordered(timers)
    &&& timer_accounting_consistent(timers)
}

/// Every wheel slot is a real timer key and wakes no earlier than the logical
/// deadline encoded by that key. Fresh listing uses equality; retry rearming
/// may move only the operational wake slot later.
pub open spec fn timer_slots_keys_valid(
    slots: Seq<crate::state_timers::SlotSpec>,
) -> bool {
    forall|i: int|
        0 <= i < slots.len() ==> {
            let slot = #[trigger] slots[i];
            match crate::keys::spec_parse_timer_key(slot.1) {
                Some(entry) => slot.0 >= entry.deadline(),
                None => false,
            }
        }
}

pub open spec fn timer_slot_key_deadline_exact(
    slot: crate::state_timers::SlotSpec,
) -> bool {
    match crate::keys::spec_parse_timer_key(slot.1) {
        Some(entry) => slot.0 == entry.deadline(),
        None => false,
    }
}

/// Keys read from Store are initially armed at their encoded logical
/// deadline, before any operational retry delay is applied.
pub proof fn lemma_fresh_timer_slot_has_exact_deadline(
    key: Seq<char>,
    entry: crate::keys::TimerEntrySpec,
)
    requires
        crate::keys::spec_parse_timer_key(key) == Some(entry),
    ensures
        timer_slot_key_deadline_exact((entry.deadline(), key)),
        timer_slots_keys_valid(seq![(entry.deadline(), key)]),
{
}

pub open spec fn timer_wheel_keys_valid(s: S) -> bool {
    timer_slots_keys_valid(s.timers.wheel.armed)
}

/// A current wheel contains only this node's share. While a membership change
/// has marked the wheel for reload, stale ownership is allowed only until
/// `spec_reload` filters it; key validity and ordering still hold.
pub open spec fn timer_slots_owned(
    s: S,
    slots: Seq<crate::state_timers::SlotSpec>,
) -> bool {
    forall|i: int|
        0 <= i < slots.len() ==> {
            let slot = #[trigger] slots[i];
            match crate::keys::spec_parse_timer_key(slot.1) {
                Some(entry) =>
                    crate::handler_timers::spec_owns_entry(s, entry),
                None => false,
            }
        }
}

pub open spec fn timer_wheel_ownership_consistent(s: S) -> bool {
    s.timers.reload_pending
        || timer_slots_owned(s, s.timers.wheel.armed)
}

pub open spec fn timer_backlog_keys_valid(s: S) -> bool {
    timer_slots_keys_valid(s.timers.backlog)
}

pub open spec fn timer_backlog_ownership_consistent(s: S) -> bool {
    s.timers.reload_pending
        || timer_slots_owned(s, s.timers.backlog)
}

pub open spec fn timer_activity_consistent(s: S) -> bool {
    &&& timers_consistent(s.timers)
    &&& timer_wheel_keys_valid(s)
    &&& timer_wheel_ownership_consistent(s)
    &&& timer_backlog_keys_valid(s)
    &&& timer_backlog_ownership_consistent(s)
}

pub proof fn lemma_timer_activity_preserved_by_control_state(
    before: S,
    after: S,
)
    requires
        timer_activity_consistent(before),
        after.timers.wheel == before.timers.wheel,
        after.timers.inflight == before.timers.inflight,
        after.timers.backlog == before.timers.backlog,
        after.timers.reload_pending
            == before.timers.reload_pending,
        after.node.core.members == before.node.core.members,
        after.cfg.node_id == before.cfg.node_id,
    ensures
        timer_activity_consistent(after),
{
    if !after.timers.reload_pending {
        assert(timer_slots_owned(
            after,
            after.timers.wheel.armed,
        )) by {
            assert forall|i: int|
                0 <= i < after.timers.wheel.armed.len() implies {
                    let slot =
                        #[trigger] after.timers.wheel.armed[i];
                    match crate::keys::spec_parse_timer_key(slot.1) {
                        Some(entry) =>
                            crate::handler_timers::spec_owns_entry(
                                after,
                                entry,
                            ),
                        None => false,
                    }
                } by {
                assert(after.timers.wheel.armed[i]
                    == before.timers.wheel.armed[i]);
                assert(crate::handler_timers::spec_owns_entry(
                    after,
                    crate::keys::spec_parse_timer_key(
                        after.timers.wheel.armed[i].1,
                    )->Some_0,
                ) == crate::handler_timers::spec_owns_entry(
                    before,
                    crate::keys::spec_parse_timer_key(
                        before.timers.wheel.armed[i].1,
                    )->Some_0,
                ));
            }
        }
        assert(timer_slots_owned(
            after,
            after.timers.backlog,
        )) by {
            assert forall|i: int|
                0 <= i < after.timers.backlog.len() implies {
                    let slot = #[trigger] after.timers.backlog[i];
                    match crate::keys::spec_parse_timer_key(slot.1) {
                        Some(entry) =>
                            crate::handler_timers::spec_owns_entry(
                                after,
                                entry,
                            ),
                        None => false,
                    }
                } by {
                assert(after.timers.backlog[i]
                    == before.timers.backlog[i]);
                assert(crate::handler_timers::spec_owns_entry(
                    after,
                    crate::keys::spec_parse_timer_key(
                        after.timers.backlog[i].1,
                    )->Some_0,
                ) == crate::handler_timers::spec_owns_entry(
                    before,
                    crate::keys::spec_parse_timer_key(
                        before.timers.backlog[i].1,
                    )->Some_0,
                ));
            }
        }
    }
}

pub proof fn lemma_timer_accounting_initial()
    ensures
        timer_accounting_consistent(
            crate::state_timers::spec_timers_new(),
        ),
        timers_consistent(crate::state_timers::spec_timers_new()),
{
    reveal(crate::state_timers::spec_timers_new);
}

/// Submitting or queueing document work does not itself alter timer
/// accounting.  Capacity is reserved by `spec_timer_fire` immediately before
/// this call, including when the target lane is already busy.
pub proof fn lemma_submit_preserves_timer_accounting(
    s: S,
    target: TargetSpec,
    work: WorkSpec,
    firing: Option<crate::handler_docs::FiringSpec>,
    debug: bool,
)
    ensures
        crate::handler_docs::spec_submit(
            s,
            target,
            work,
            firing,
            debug,
        ).timers == s.timers,
{
    reveal(crate::handler_docs::spec_submit);
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_slot_of);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_note);
}

/// `spec_timer_fire` is called by the dispatcher only while capacity remains.
/// A successful owned firing reserves one slot; malformed, foreign, or
/// inactive keys reserve none.
pub proof fn lemma_timer_fire_preserves_accounting(
    s: S,
    key: Seq<char>,
    at: u64,
    now: u64,
)
    requires
        timer_accounting_consistent(s.timers),
        s.timers.inflight < crate::state_timers::CONCURRENCY,
    ensures
        timer_accounting_consistent(
            crate::handler_timers::spec_timer_fire(
                s,
                key,
                at,
                now,
            ).timers,
        ),
{
    reveal(crate::handler_timers::spec_timer_fire);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state::spec_note);
    match crate::keys::spec_parse_timer_key(key) {
        Some(entry) => {
            if crate::handler_timers::spec_owns_entry(s, entry)
                && crate::verified::node_spec::spec_acts(
                    s.node.core,
                    entry.target(),
                    now as nat,
                )
            {
                let counted = crate::handler_timers::spec_with_timers(
                    s,
                    TimersSpec {
                        inflight:
                            s.timers.inflight.saturating_add(1),
                        ..s.timers
                    },
                );
                match entry {
                    crate::keys::TimerEntrySpec::Origin {
                        origin,
                        deadline,
                        token,
                        by,
                    } => {
                        let fired = crate::verified::flight_spec::AFired {
                            key: crate::verified::node::AKey {
                                origin,
                                at: deadline as nat,
                                token: token as nat,
                            },
                            by,
                        };
                        lemma_submit_preserves_timer_accounting(
                            counted,
                            TargetSpec::Origin(origin),
                            WorkSpec::Sweep {
                                fired: Some(fired),
                                now,
                            },
                            Some(crate::handler_docs::FiringSpec {
                                key,
                                at,
                                kind: crate::types::TimerKind::Origin,
                                lag: now.saturating_sub(at),
                            }),
                            false,
                        );
                    },
                    crate::keys::TimerEntrySpec::Schedule {
                        id,
                        deadline,
                        token,
                        by,
                    } => {
                        let fired = crate::verified::flight_spec::AFired {
                            key: crate::verified::node::AKey {
                                origin: "sched:"@ + id,
                                at: deadline as nat,
                                token: token as nat,
                            },
                            by,
                        };
                        lemma_submit_preserves_timer_accounting(
                            counted,
                            TargetSpec::Schedule(id),
                            WorkSpec::Fire {
                                schedule: id,
                                fired: Some(fired),
                                now,
                            },
                            Some(crate::handler_docs::FiringSpec {
                                key,
                                at,
                                kind:
                                    crate::types::TimerKind::Schedule,
                                lag: now.saturating_sub(at),
                            }),
                            false,
                        );
                    },
                }
            }
        },
        None => {},
    }
}

/// Backlog length is intentionally unrestricted: dispatch reserves at most
/// `CONCURRENCY` slots and leaves every additional due key queued.
pub proof fn lemma_dispatch_due_preserves_accounting(
    s: S,
    now: u64,
    fuel: nat,
)
    requires
        timer_accounting_consistent(s.timers),
    ensures
        timer_accounting_consistent(
            crate::handler_timers::spec_dispatch_due(s, now, fuel).timers,
        ),
    decreases fuel,
{
    reveal(crate::handler_timers::spec_dispatch_due);
    if fuel > 0
        && s.timers.inflight < crate::state_timers::CONCURRENCY
        && s.timers.backlog.len() > 0
    {
        let key = s.timers.backlog[0].1;
        let at = s.timers.backlog[0].0;
        let popped = crate::handler_timers::spec_with_timers(
            s,
            TimersSpec {
                backlog: s.timers.backlog.drop_first(),
                ..s.timers
            },
        );
        reveal(crate::handler_timers::spec_with_timers);
        assert(timer_accounting_consistent(popped.timers));
        lemma_timer_fire_preserves_accounting(popped, key, at, now);
        lemma_dispatch_due_preserves_accounting(
            crate::handler_timers::spec_timer_fire(
                popped,
                key,
                at,
                now,
            ),
            now,
            (fuel - 1) as nat,
        );
    }
}

/// Once all sweep reservations are occupied, dispatch is an exact stutter:
/// every due key remains in the backlog until a completion decrements the
/// reservation count.
pub proof fn lemma_dispatch_due_at_capacity_keeps_backlog(
    s: S,
    now: u64,
    fuel: nat,
)
    requires
        s.timers.inflight == crate::state_timers::CONCURRENCY,
    ensures
        crate::handler_timers::spec_dispatch_due(s, now, fuel) == s,
{
    reveal(crate::handler_timers::spec_dispatch_due);
}

/// Completion releases exactly one reservation (saturating defensively at
/// zero), optionally rearms the key, and then fills available capacity from
/// the independent backlog.
pub proof fn lemma_timer_fired_preserves_accounting(
    s: S,
    firing: crate::handler_docs::FiringSpec,
    now: u64,
    result: Result<crate::types::Fired, Seq<char>>,
)
    requires
        timer_accounting_consistent(s.timers),
    ensures
        timer_accounting_consistent(
            crate::handler_timers::spec_timer_fired(
                s,
                firing,
                now,
                result,
            ).timers,
        ),
{
    reveal(crate::handler_timers::spec_timer_fired);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state::spec_note);
    let decremented = crate::handler_timers::spec_with_timers(
        s,
        TimersSpec {
            inflight: s.timers.inflight.saturating_sub(1),
            ..s.timers
        },
    );
    assert(timer_accounting_consistent(decremented.timers));
    let rearm = crate::state_timers::spec_max(now, firing.at)
        .saturating_add(crate::state_timers::RETRY_AFTER_MS);
    let (staged, outcome) = match result {
        Ok(crate::types::Fired::Deleted) => (
            decremented,
            crate::types::FireOutcome::Deleted,
        ),
        Ok(crate::types::Fired::Kept) => (
            crate::handler_timers::spec_with_timers(
                decremented,
                TimersSpec {
                    wheel: crate::state_timers::TimerWheelSpec {
                        armed: crate::state_timers::spec_arm(
                            decremented.timers.wheel.armed,
                            rearm,
                            firing.key,
                        ),
                    },
                    ..decremented.timers
                },
            ),
            crate::types::FireOutcome::Kept,
        ),
        Err(error) => {
            let noted = crate::state::spec_note(
                decremented,
                crate::types::NoteSpec::FireFailed {
                    key: firing.key,
                    error,
                },
            );
            (
                crate::handler_timers::spec_with_timers(
                    noted,
                    TimersSpec {
                        wheel: crate::state_timers::TimerWheelSpec {
                            armed: crate::state_timers::spec_arm(
                                noted.timers.wheel.armed,
                                rearm,
                                firing.key,
                            ),
                        },
                        ..noted.timers
                    },
                ),
                crate::types::FireOutcome::Failed,
            )
        },
    };
    let ready = crate::state::spec_note(
        staged,
        crate::types::NoteSpec::TimerFire {
            kind: firing.kind,
            outcome,
            lag_ms: firing.lag,
        },
    );
    assert(timer_accounting_consistent(ready.timers));
    lemma_dispatch_due_preserves_accounting(
        ready,
        now,
        ready.timers.backlog.len(),
    );
    assert(crate::handler_timers::spec_timer_fired(
        s,
        firing,
        now,
        result,
    ) == crate::handler_timers::spec_dispatch_due(
        ready,
        now,
        ready.timers.backlog.len(),
    ));
}

pub proof fn lemma_arm_preserves_timer_key_deadlines(
    slots: Seq<crate::state_timers::SlotSpec>,
    at: u64,
    key: Seq<char>,
    entry: crate::keys::TimerEntrySpec,
)
    requires
        timer_slots_keys_valid(slots),
        crate::keys::spec_parse_timer_key(key) == Some(entry),
        at >= entry.deadline(),
    ensures
        timer_slots_keys_valid(crate::state_timers::spec_arm(
            slots,
            at,
            key,
        )),
    decreases slots.len(),
{
    let added = (at, key);
    if slots.len() > 0
        && slots[0] != added
        && !spec_slot_before(added, slots[0])
    {
        lemma_arm_preserves_timer_key_deadlines(
            slots.drop_first(),
            at,
            key,
            entry,
        );
        let result = crate::state_timers::spec_arm(
            slots,
            at,
            key,
        );
        assert forall|i: int|
            0 <= i
                < result.len() implies {
                let slot = #[trigger] result[i];
                match crate::keys::spec_parse_timer_key(slot.1) {
                    Some(parsed) => slot.0 >= parsed.deadline(),
                    None => false,
                }
            } by {
            if i > 0 {
                let tail = crate::state_timers::spec_arm(
                    slots.drop_first(),
                    at,
                    key,
                );
                assert(result[i] == tail[i - 1]);
            }
        }
    }
}

pub proof fn lemma_arm_preserves_timer_ownership(
    s: S,
    slots: Seq<crate::state_timers::SlotSpec>,
    at: u64,
    key: Seq<char>,
    entry: crate::keys::TimerEntrySpec,
)
    requires
        timer_slots_owned(s, slots),
        crate::keys::spec_parse_timer_key(key) == Some(entry),
        crate::handler_timers::spec_owns_entry(s, entry),
    ensures
        timer_slots_owned(
            s,
            crate::state_timers::spec_arm(
                slots,
                at,
                key,
            ),
        ),
    decreases slots.len(),
{
    let added = (at, key);
    if slots.len() > 0
        && slots[0] != added
        && !spec_slot_before(added, slots[0])
    {
        lemma_arm_preserves_timer_ownership(
            s,
            slots.drop_first(),
            at,
            key,
            entry,
        );
        let result = crate::state_timers::spec_arm(
            slots,
            at,
            key,
        );
        assert forall|i: int|
            0 <= i
                < result.len() implies {
                let slot = #[trigger] result[i];
                match crate::keys::spec_parse_timer_key(slot.1) {
                    Some(parsed) =>
                        crate::handler_timers::spec_owns_entry(
                            s,
                            parsed,
                        ),
                    None => false,
                }
            } by {
            if i > 0 {
                let tail = crate::state_timers::spec_arm(
                    slots.drop_first(),
                    at,
                    key,
                );
                assert(result[i] == tail[i - 1]);
            }
        }
    }
}

pub proof fn lemma_timer_fire_preserves_activity(
    s: S,
    key: Seq<char>,
    at: u64,
    entry: crate::keys::TimerEntrySpec,
    now: u64,
)
    requires
        timer_activity_consistent(s),
        crate::keys::spec_parse_timer_key(key) == Some(entry),
        at >= entry.deadline(),
        s.timers.reload_pending
            || crate::handler_timers::spec_owns_entry(s, entry),
        s.timers.inflight < crate::state_timers::CONCURRENCY,
    ensures
        timer_activity_consistent(
            crate::handler_timers::spec_timer_fire(
                s,
                key,
                at,
                now,
            ),
        ),
{
    lemma_timer_fire_preserves_accounting(s, key, at, now);
    let retry = crate::state_timers::spec_max(now, at)
        .saturating_add(crate::state_timers::RETRY_AFTER_MS);
    assert(retry >= at);
    assert(retry >= entry.deadline());
    lemma_arm_preserves_timer_wheel_order(
        s.timers.wheel.armed,
        retry,
        key,
    );
    lemma_arm_preserves_timer_key_deadlines(
        s.timers.wheel.armed,
        retry,
        key,
        entry,
    );
    if !s.timers.reload_pending {
        lemma_arm_preserves_timer_ownership(
            s,
            s.timers.wheel.armed,
            retry,
            key,
            entry,
        );
    }
    reveal(crate::handler_timers::spec_timer_fire);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::handler_docs::spec_submit);
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_slot_of);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_note);
}

/// Every queued key carries the same parse/deadline/ownership facts as wheel
/// entries. Recursive dispatch may consume, defer/rearm, or submit each head
/// while preserving the full timer relation.
pub proof fn lemma_dispatch_due_preserves_activity(
    s: S,
    now: u64,
    fuel: nat,
)
    requires
        timer_activity_consistent(s),
    ensures
        timer_activity_consistent(
            crate::handler_timers::spec_dispatch_due(s, now, fuel),
        ),
    decreases fuel,
{
    reveal(crate::handler_timers::spec_dispatch_due);
    if fuel > 0
        && s.timers.inflight < crate::state_timers::CONCURRENCY
        && s.timers.backlog.len() > 0
    {
        let slot = s.timers.backlog[0];
        let entry = crate::keys::spec_parse_timer_key(slot.1)->Some_0;
        let popped = crate::handler_timers::spec_with_timers(
            s,
            TimersSpec {
                backlog: s.timers.backlog.drop_first(),
                ..s.timers
            },
        );
        reveal(crate::handler_timers::spec_with_timers);
        assert(crate::keys::spec_parse_timer_key(slot.1) is Some);
        assert(slot.0 >= entry.deadline());
        assert(s.timers.reload_pending
            || crate::handler_timers::spec_owns_entry(s, entry));
        assert(timer_slots_keys_valid(popped.timers.backlog)) by {
            assert forall|i: int|
                0 <= i < popped.timers.backlog.len() implies {
                    let queued = #[trigger] popped.timers.backlog[i];
                    match crate::keys::spec_parse_timer_key(queued.1) {
                        Some(parsed) => queued.0 >= parsed.deadline(),
                        None => false,
                    }
                } by {
                assert(popped.timers.backlog[i]
                    == s.timers.backlog[i + 1]);
            }
        }
        if !s.timers.reload_pending {
            assert(timer_slots_owned(popped, popped.timers.backlog)) by {
                assert forall|i: int|
                    0 <= i < popped.timers.backlog.len() implies {
                        let queued =
                            #[trigger] popped.timers.backlog[i];
                        match crate::keys::spec_parse_timer_key(queued.1) {
                            Some(parsed) =>
                                crate::handler_timers::spec_owns_entry(
                                    popped,
                                    parsed,
                                ),
                            None => false,
                        }
                    } by {
                    assert(popped.timers.backlog[i]
                        == s.timers.backlog[i + 1]);
                }
            }
        }
        assert(timer_activity_consistent(popped));
        lemma_timer_fire_preserves_activity(
            popped,
            slot.1,
            slot.0,
            entry,
            now,
        );
        let fired = crate::handler_timers::spec_timer_fire(
            popped,
            slot.1,
            slot.0,
            now,
        );
        lemma_dispatch_due_preserves_activity(
            fired,
            now,
            (fuel - 1) as nat,
        );
    }
}

/// Every parseable key owned by this node can be folded into the wheel while
/// preserving strict order, key/deadline agreement, and current ownership.
/// Unparseable and foreign keys are ignored by the production fold.
pub proof fn lemma_take_bucket_preserves_timer_activity(
    s: S,
    keys: Seq<Seq<char>>,
    n: nat,
)
    requires
        timer_activity_consistent(s),
    ensures
        ({
            let after =
                crate::handler_timers::spec_take_bucket(s, keys, n).0;
            &&& timer_activity_consistent(after)
            &&& after.node == s.node
            &&& after.cache == s.cache
            &&& after.flights == s.flights
            &&& after.loops == s.loops
            &&& after.keys == s.keys
            &&& after.cfg == s.cfg
            &&& after.out == s.out
            &&& after.ops == s.ops
            &&& after.next_op == s.next_op
            &&& after.timers == TimersSpec {
                wheel: after.timers.wheel,
                ..s.timers
            }
        }),
    decreases keys.len(),
{
    reveal(crate::handler_timers::spec_take_bucket);
    if keys.len() > 0 {
        let key = keys[0];
        match crate::keys::spec_parse_timer_key(key) {
            Some(entry) => {
                if crate::handler_timers::spec_owns_entry(s, entry) {
                    let armed = crate::state_timers::spec_arm(
                        s.timers.wheel.armed,
                        entry.deadline(),
                        key,
                    );
                    lemma_arm_preserves_timer_wheel_order(
                        s.timers.wheel.armed,
                        entry.deadline(),
                        key,
                    );
                    lemma_arm_preserves_timer_key_deadlines(
                        s.timers.wheel.armed,
                        entry.deadline(),
                        key,
                        entry,
                    );
                    if !s.timers.reload_pending {
                        lemma_arm_preserves_timer_ownership(
                            s,
                            s.timers.wheel.armed,
                            entry.deadline(),
                            key,
                            entry,
                        );
                    }
                    let next = crate::handler_timers::spec_with_timers(
                        s,
                        crate::state_timers::TimersSpec {
                            wheel: crate::state_timers::TimerWheelSpec {
                                armed,
                            },
                            ..s.timers
                        },
                    );
                    assert(crate::handler_timers::spec_owns_entry(
                        next,
                        entry,
                    ) == crate::handler_timers::spec_owns_entry(
                        s,
                        entry,
                    ));
                    assert(timer_activity_consistent(next));
                    lemma_take_bucket_preserves_timer_activity(
                        next,
                        keys.drop_first(),
                        n + 1,
                    );
                } else {
                    lemma_take_bucket_preserves_timer_activity(
                        s,
                        keys.drop_first(),
                        n,
                    );
                }
            },
            None => {
                lemma_take_bucket_preserves_timer_activity(
                    s,
                    keys.drop_first(),
                    n,
                );
            },
        }
    }
}

pub proof fn lemma_nonempty_relisted_requeues_preserves_timer_activity(
    s: S,
    bucket: u64,
    now: u64,
    keys: Vec<String>,
)
    requires
        timer_activity_consistent(s),
        keys.deep_view().len() > 0,
        s.timers.started,
        s.timers.listing is None,
        s.timers.backoff_until is None,
        !s.timers.reload_pending,
        s.timers.loaded_through is Some,
        s.timers.loaded_through->Some_0
            < crate::handler_timers::spec_horizon(s, now),
    ensures
        ({
            let after = crate::handler_timers::spec_relisted(
                s,
                bucket,
                now,
                StoreRes::List { result: Ok(keys) },
            );
            &&& timer_activity_consistent(after)
            &&& after.node == s.node
            &&& after.cache == s.cache
            &&& after.flights == s.flights
            &&& after.loops == s.loops
            &&& after.out.len() == s.out.len() + 3
            &&& after.out[s.out.len() as int] is Note
            &&& after.out[s.out.len() as int + 1] is Note
            &&& after.out[s.out.len() as int + 2] is Store
            &&& match after.timers.listing {
                Some(ListingSpec::Extend { op, .. }) => {
                    &&& after.ops.contains_key(op)
                    &&& after.ops[op] == Owner::Timers
                },
                _ => false,
            }
        }),
{
    reveal(crate::handler_timers::spec_relisted);
    reveal(crate::handler_timers::spec_take_bucket);
    reveal(crate::handler_timers::spec_timers_run);
    lemma_take_bucket_preserves_timer_activity(
        s,
        keys.deep_view(),
        0,
    );
    let taken_result = crate::handler_timers::spec_take_bucket(
        s,
        keys.deep_view(),
        0,
    );
    let taken = taken_result.0;
    let n = taken_result.1;
    assert(taken.node == s.node);
    assert(taken.cache == s.cache);
    assert(taken.flights == s.flights);
    assert(taken.loops == s.loops);
    assert(taken.out == s.out);
    assert(taken.timers.loaded_through
        == s.timers.loaded_through);
    assert(timer_activity_consistent(taken));
    let noted_bucket = crate::state::spec_note(
        taken,
        crate::types::NoteSpec::BucketLoaded {
            bucket,
            deadlines: n as usize,
        },
    );
    lemma_timer_activity_preserved_by_control_state(
        taken,
        noted_bucket,
    );
    let noted_listing = crate::state::spec_note(
        noted_bucket,
        crate::types::NoteSpec::TimerListing { ok: true },
    );
    lemma_timer_activity_preserved_by_control_state(
        noted_bucket,
        noted_listing,
    );
    assert(noted_bucket.timers == taken.timers);
    assert(noted_listing.timers == noted_bucket.timers);
    let advanced = crate::handler_timers::spec_with_timers(
        noted_listing,
        TimersSpec {
            closed_through: Some(bucket),
            ..noted_listing.timers
        },
    );
    lemma_timer_activity_preserved_by_control_state(
        noted_listing,
        advanced,
    );
    assert(advanced.timers.loaded_through
        == s.timers.loaded_through);
    assert(advanced.timers.loaded_through->Some_0
        < crate::handler_timers::spec_horizon(advanced, now));
    let after =
        crate::handler_timers::spec_timers_run(advanced, now);
    assert(crate::handler_timers::spec_relisted(
        s,
        bucket,
        now,
        StoreRes::List { result: Ok(keys) },
    ) == after);
    assert(after.timers.wheel == advanced.timers.wheel);
    assert(after.timers.inflight == advanced.timers.inflight);
    assert(after.timers.backlog == advanced.timers.backlog);
    assert(after.timers.reload_pending
        == advanced.timers.reload_pending);
    assert(after.node.core.members
        == advanced.node.core.members);
    assert(after.cfg.node_id == advanced.cfg.node_id);
    lemma_timer_activity_preserved_by_control_state(
        advanced,
        after,
    );
    assert(timer_activity_consistent(after));
    assert(after.node == s.node);
    assert(after.cache == s.cache);
    assert(after.flights == s.flights);
    assert(after.loops == s.loops);
    assert(after.out.len() == s.out.len() + 3);
    assert(after.out[s.out.len() as int] is Note);
    assert(after.out[s.out.len() as int + 1] is Note);
    assert(after.out[s.out.len() as int + 2] is Store);
    assert(match after.timers.listing {
        Some(ListingSpec::Extend { op, .. }) => {
            &&& after.ops.contains_key(op)
            &&& after.ops[op] == Owner::Timers
        },
        _ => false,
    });
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
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state_timers::spec_take_due);
    reveal(crate::state_timers::spec_due_count);
    reveal(crate::handler_timers::spec_dispatch_due);
    assert(s.timers.wheel.armed =~= Seq::<crate::state_timers::SlotSpec>::empty());
    assert(s.timers.backlog =~= Seq::<crate::state_timers::SlotSpec>::empty());
}

/// The exact, common singleton due-dispatch shape.  A successful fire consumes
/// the backlog entry before `spec_timer_fire` increments `inflight`.
pub open spec fn singleton_due_dispatch_base(
    s: S,
) -> S {
    crate::handler_timers::spec_with_timers(
        s,
        TimersSpec {
            wheel: crate::state_timers::TimerWheelSpec {
                armed: Seq::empty(),
            },
            backlog: Seq::empty(),
            ..s.timers
        },
    )
}

pub proof fn lemma_singleton_take_due(
    at: u64,
    key: Seq<char>,
    now: u64,
)
    requires
        at <= now,
    ensures
        crate::state_timers::spec_take_due(seq![(at, key)], now)
            == (
                seq![(at, key)],
                Seq::<crate::state_timers::SlotSpec>::empty(),
            ),
{
    reveal(crate::state_timers::spec_take_due);
    reveal(crate::state_timers::spec_due_count);
    assert(seq![(at, key)].drop_first()
        =~= Seq::<crate::state_timers::SlotSpec>::empty());
    assert(crate::state_timers::spec_due_count(
        Seq::<crate::state_timers::SlotSpec>::empty(),
        now,
    ) == 0);
}

pub proof fn lemma_dispatch_due_zero(s: S, now: u64)
    ensures
        crate::handler_timers::spec_dispatch_due(s, now, 0) == s,
{
    reveal(crate::handler_timers::spec_dispatch_due);
}

/// A real origin-key dispatch starts exactly one origin sweep.  The theorem
/// states the resulting reservation and flight shape and proves the repaired
/// timer activity and lane invariants.
pub proof fn lemma_singleton_due_origin_starts_sweep(
    s: S,
    now: u64,
    at: u64,
    key: Seq<char>,
    origin: Seq<char>,
    deadline: u64,
    token: u64,
    by: Seq<char>,
)
    requires
        s.timers.wheel.armed == seq![(at, key)],
        s.timers.backlog == Seq::<crate::state_timers::SlotSpec>::empty(),
        s.timers.inflight == 0,
        timer_activity_consistent(s),
        at <= now,
        crate::keys::spec_parse_timer_key(key)
            == Some(crate::keys::TimerEntrySpec::Origin {
                origin,
                deadline,
                token,
                by,
            }),
        crate::handler_timers::spec_owns_entry(
            s,
            crate::keys::TimerEntrySpec::Origin {
                origin,
                deadline,
                token,
                by,
            },
        ),
        crate::verified::node_spec::spec_acts(
            s.node.core,
            origin,
            now as nat,
        ),
        crate::handler_docs::spec_slot_of(s, origin).busy is None,
        !s.flights.inflight.contains_key(s.next_flight),
        !s.ops.contains_key(s.next_op),
        owners_consistent(s),
        flight_lanes_consistent(s.flights),
    ensures
        ({
            let after = crate::handler_timers::spec_fire_due(s, now);
            let fid = s.next_flight;
            let fired = crate::verified::flight_spec::AFired {
                key: crate::verified::node::AKey {
                    origin,
                    at: deadline as nat,
                    token: token as nat,
                },
                by,
            };
            &&& after.timers.wheel.armed.len() == 0
            &&& after.timers.backlog.len() == 0
            &&& after.timers.inflight == 1
            &&& after.flights.inflight.contains_key(fid)
            &&& after.flights.inflight[fid].target
                == TargetSpec::Origin(origin)
            &&& after.flights.inflight[fid].work
                == WorkSpec::Sweep {
                    fired: Some(fired),
                    now,
                }
            &&& after.flights.inflight[fid].firing
                == Some(crate::handler_docs::FiringSpec {
                    key,
                    at,
                    kind: crate::types::TimerKind::Origin,
                    lag: now.saturating_sub(at),
                })
            &&& after.flights.inflight[fid].phase is Loading
            &&& forall|old_fid: crate::types::FlightId|
                s.flights.inflight.contains_key(old_fid) ==>
                    after.flights.inflight.contains_key(old_fid)
                    && after.flights.inflight[old_fid]
                        == s.flights.inflight[old_fid]
            &&& flight_lanes_consistent(after.flights)
            &&& owners_consistent(after)
            &&& timers_consistent(after.timers)
            &&& timer_activity_consistent(after)
        }),
{
    lemma_singleton_take_due(at, key, now);
    assert(crate::state_timers::spec_take_due(
        s.timers.wheel.armed,
        now,
    ) == (
        seq![(at, key)],
        Seq::<crate::state_timers::SlotSpec>::empty(),
    ));
    reveal(crate::handler_timers::spec_fire_due);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state_timers::spec_take_due);
    reveal(crate::state_timers::spec_due_count);
    reveal(crate::handler_timers::spec_dispatch_due);
    reveal(crate::handler_timers::spec_timer_fire);
    reveal(crate::handler_docs::spec_submit);
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_slot_of);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_note);
    let base = singleton_due_dispatch_base(s);
    let queued = crate::handler_timers::spec_with_timers(
        s,
        TimersSpec {
            wheel: crate::state_timers::TimerWheelSpec {
                armed: Seq::empty(),
            },
            backlog: seq![(at, key)],
            ..s.timers
        },
    );
    assert(s.timers.backlog + seq![(at, key)] == seq![(at, key)]);
    assert(crate::handler_timers::spec_fire_due(s, now)
        == crate::handler_timers::spec_dispatch_due(queued, now, 1));
    assert(queued.timers.backlog.drop_first()
        =~= Seq::<crate::state_timers::SlotSpec>::empty());
    assert(crate::handler_timers::spec_with_timers(
        queued,
        TimersSpec {
            backlog: queued.timers.backlog.drop_first(),
            ..queued.timers
        },
    ) == base);
    let fired = crate::handler_timers::spec_timer_fire(base, key, at, now);
    lemma_dispatch_due_zero(fired, now);
    assert(crate::handler_timers::spec_fire_due(s, now) == fired);
    let after = crate::handler_timers::spec_fire_due(s, now);
    let fid = s.next_flight;
    assert(after.timers.wheel.armed.len() == 0);
    assert(after.timers.backlog.len() == 0);
    assert(after.timers.inflight == 1);
    assert(after.flights.inflight.contains_key(fid));
    assert(after.flights.inflight[fid].target == TargetSpec::Origin(origin));
    assert(after.flights.inflight[fid].work is Sweep);
    assert(after.flights.inflight[fid].firing is Some);
    assert(after.flights.inflight[fid].phase is Loading);
    assert(flight_lanes_consistent(after.flights));
    assert(owners_consistent(after));
    assert(timer_accounting_consistent(after.timers));
    assert(timers_consistent(after.timers));
    assert(timer_activity_consistent(after));
}

/// The schedule counterpart starts the exact `Fire` flight and loads the
/// named schedule while preserving timer activity and every existing lane.
pub proof fn lemma_singleton_due_schedule_starts_fire(
    s: S,
    now: u64,
    at: u64,
    key: Seq<char>,
    id: Seq<char>,
    deadline: u64,
    token: u64,
    by: Seq<char>,
)
    requires
        s.timers.wheel.armed == seq![(at, key)],
        s.timers.backlog == Seq::<crate::state_timers::SlotSpec>::empty(),
        s.timers.inflight == 0,
        timer_activity_consistent(s),
        at <= now,
        crate::keys::spec_parse_timer_key(key)
            == Some(crate::keys::TimerEntrySpec::Schedule {
                id,
                deadline,
                token,
                by,
            }),
        crate::handler_timers::spec_owns_entry(
            s,
            crate::keys::TimerEntrySpec::Schedule {
                id,
                deadline,
                token,
                by,
            },
        ),
        crate::verified::node_spec::spec_acts(
            s.node.core,
            id,
            now as nat,
        ),
        crate::handler_docs::spec_slot_of(
            s,
            crate::target::spec_name(TargetSpec::Schedule(id)),
        ).busy is None,
        !s.flights.inflight.contains_key(s.next_flight),
        !s.ops.contains_key(s.next_op),
        owners_consistent(s),
        flight_lanes_consistent(s.flights),
    ensures
        ({
            let after = crate::handler_timers::spec_fire_due(s, now);
            let fid = s.next_flight;
            let fired = crate::verified::flight_spec::AFired {
                key: crate::verified::node::AKey {
                    origin: "sched:"@ + id,
                    at: deadline as nat,
                    token: token as nat,
                },
                by,
            };
            &&& after.timers.wheel.armed.len() == 0
            &&& after.timers.backlog.len() == 0
            &&& after.timers.inflight == 1
            &&& after.flights.inflight.contains_key(fid)
            &&& after.flights.inflight[fid].target
                == TargetSpec::Schedule(id)
            &&& after.flights.inflight[fid].work
                == WorkSpec::Fire {
                    schedule: id,
                    fired: Some(fired),
                    now,
                }
            &&& after.flights.inflight[fid].firing
                == Some(crate::handler_docs::FiringSpec {
                    key,
                    at,
                    kind: crate::types::TimerKind::Schedule,
                    lag: now.saturating_sub(at),
                })
            &&& after.flights.inflight[fid].phase is FireLoadingSchedule
            &&& forall|old_fid: crate::types::FlightId|
                s.flights.inflight.contains_key(old_fid) ==>
                    after.flights.inflight.contains_key(old_fid)
                    && after.flights.inflight[old_fid]
                        == s.flights.inflight[old_fid]
            &&& flight_lanes_consistent(after.flights)
            &&& owners_consistent(after)
            &&& timers_consistent(after.timers)
            &&& timer_activity_consistent(after)
        }),
{
    lemma_singleton_take_due(at, key, now);
    assert(crate::state_timers::spec_take_due(
        s.timers.wheel.armed,
        now,
    ) == (
        seq![(at, key)],
        Seq::<crate::state_timers::SlotSpec>::empty(),
    ));
    reveal(crate::handler_timers::spec_fire_due);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state_timers::spec_take_due);
    reveal(crate::state_timers::spec_due_count);
    reveal(crate::handler_timers::spec_dispatch_due);
    reveal(crate::handler_timers::spec_timer_fire);
    reveal(crate::handler_docs::spec_submit);
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_slot_of);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_note);
    let base = singleton_due_dispatch_base(s);
    let queued = crate::handler_timers::spec_with_timers(
        s,
        TimersSpec {
            wheel: crate::state_timers::TimerWheelSpec {
                armed: Seq::empty(),
            },
            backlog: seq![(at, key)],
            ..s.timers
        },
    );
    assert(s.timers.backlog + seq![(at, key)] == seq![(at, key)]);
    assert(crate::handler_timers::spec_fire_due(s, now)
        == crate::handler_timers::spec_dispatch_due(queued, now, 1));
    assert(queued.timers.backlog.drop_first()
        =~= Seq::<crate::state_timers::SlotSpec>::empty());
    assert(crate::handler_timers::spec_with_timers(
        queued,
        TimersSpec {
            backlog: queued.timers.backlog.drop_first(),
            ..queued.timers
        },
    ) == base);
    let fired = crate::handler_timers::spec_timer_fire(base, key, at, now);
    lemma_dispatch_due_zero(fired, now);
    assert(crate::handler_timers::spec_fire_due(s, now) == fired);
    let after = crate::handler_timers::spec_fire_due(s, now);
    let fid = s.next_flight;
    assert(after.timers.wheel.armed.len() == 0);
    assert(after.timers.backlog.len() == 0);
    assert(after.timers.inflight == 1);
    assert(after.flights.inflight.contains_key(fid));
    assert(after.flights.inflight[fid].target == TargetSpec::Schedule(id));
    assert(after.flights.inflight[fid].work is Fire);
    assert(after.flights.inflight[fid].firing is Some);
    assert(after.flights.inflight[fid].phase is FireLoadingSchedule);
    assert(flight_lanes_consistent(after.flights));
    assert(owners_consistent(after));
    assert(timer_accounting_consistent(after.timers));
    assert(timers_consistent(after.timers));
    assert(timer_activity_consistent(after));
}

/// The whole-map transition preserves the relaxed invariant and closes
/// directly to full document well-formedness.
pub proof fn lemma_bulk_sweep_preserves_well_formed(
    workflow: echod_concrete::document::WorkflowDocumentV,
    now: u64,
    retry_timeout: u64,
)
    requires
        echod_concrete::document::workflow_well_formed(workflow),
        workflow.committed_at <= now,
        now <= MAX_TIME,
        0 < retry_timeout <= MAX_TIME,
    ensures
        ({
            let swept = echod_concrete::node::spec_sweep(
                echod_concrete::node::DocumentBodyV::Workflow(workflow.objects),
                now,
                retry_timeout,
            ).0;
            &&& echod_concrete::node::spec_earliest_in(swept, now) is None
            &&&
            well_formed(echod_concrete::node::spec_advance_stored(
                StoredDocumentV::Workflow(workflow),
                swept,
                now,
            ))
        }),
{
    echod_concrete::quick_n_dirty::lemma_full_implies_relaxed(workflow, now);
    echod_concrete::quick_n_dirty::lemma_sweep_preserves_relaxed(
        workflow.document,
        workflow.objects,
        now,
        retry_timeout,
    );
    let swept = echod_concrete::node::spec_sweep(
        echod_concrete::node::DocumentBodyV::Workflow(workflow.objects),
        now,
        retry_timeout,
    ).0;
    assert(swept is Workflow);
    echod_concrete::quick_n_dirty::lemma_relaxed_closed(
        workflow.document,
        swept->Workflow_0,
        now,
    );
    reveal(echod_concrete::document::well_formed);
    reveal(echod_concrete::document::workflow_well_formed);
    reveal(echod_concrete::node::spec_advance_stored);
}

/// A standalone workflow transition enters the normal CAS-gated commit path
/// with a fully well-formed endpoint.
pub proof fn lemma_standalone_origin_sweep_commits_well_formed(
    s: S,
    flight: FlightSpec,
    working: crate::handler_docs::WorkingSpec,
    workflow: echod_concrete::document::WorkflowDocumentV,
)
    requires
        flight.work is Sweep,
        working.loaded.document
            == StoredDocumentV::Workflow(workflow),
        echod_concrete::document::workflow_well_formed(workflow),
        workflow.committed_at <= flight.work.now(),
        flight.work.now() <= MAX_TIME,
        0 < s.cfg.retry_timeout <= MAX_TIME,
    ensures
        ({
            let now = flight.work.now();
            let swept = echod_concrete::node::spec_sweep(
                echod_concrete::node::DocumentBodyV::Workflow(
                    workflow.objects,
                ),
                now,
                s.cfg.retry_timeout,
            ).0;
            let decided =
                crate::handler_docs::spec_decide(
                    s,
                    flight.work,
                    working,
                );
            &&& echod_concrete::node::spec_earliest_in(swept, now) is None
            &&& decided.1.after
                == echod_concrete::node::spec_advance_stored(
                    StoredDocumentV::Workflow(workflow),
                    swept,
                    now,
                )
            &&& well_formed(decided.1.after)
        }),
{
    let now = flight.work.now();
    let swept = echod_concrete::node::spec_sweep(
        echod_concrete::node::DocumentBodyV::Workflow(
            workflow.objects,
        ),
        now,
        s.cfg.retry_timeout,
    ).0;
    reveal(crate::handler_docs::spec_decide);
    reveal(crate::verified::flight_spec::spec_step);
    reveal(crate::handler_docs::spec_commit_new);
    lemma_bulk_sweep_preserves_well_formed(
        workflow,
        now,
        s.cfg.retry_timeout,
    );
}

/// Non-sweep work enters the same CAS-gated commit state.
pub proof fn lemma_non_sweep_origin_commit_path_unchanged(
    s: S,
    flight: FlightSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        !(flight.work is Sweep),
    ensures
        ({
            let (decided, commit, done) =
                crate::handler_docs::spec_decide(
                    s,
                    flight.work,
                    working,
                );
            let (advanced, next, progress) =
                crate::handler_docs::spec_commit_advance(
                    decided,
                    flight.id,
                    commit,
                    None,
                );
            crate::handler_docs::spec_run_origin(
                s,
                flight,
                working,
            ) == match progress {
                crate::handler_docs::ProgressSpec::Issued =>
                    crate::handler_docs::spec_inflight(
                        advanced,
                        FlightSpec {
                            phase: PhaseSpec::Origin {
                                commit: next,
                                done,
                            },
                            ..flight
                        },
                    ),
                crate::handler_docs::ProgressSpec::Done(fired) =>
                    crate::handler_docs::spec_committed(
                        advanced,
                        flight,
                        done,
                        fired,
                    ),
                crate::handler_docs::ProgressSpec::Failed(error) =>
                    crate::handler_docs::spec_commit_failed(
                        advanced,
                        flight,
                        error,
                    ),
            }
        }),
{
    reveal(crate::handler_docs::spec_run_origin);
}

/// Exact abstract alignment for the atomic origin transition.
/// A finite timeout trace represents the two whole-map passes.
pub open spec fn origin_sweep_matches(
    config: ServerConfig,
    key: Seq<char>,
    document: echod_concrete::node::DocumentBodyV,
    abstract_state: AbstractStateV,
    now: u64,
) -> bool {
    let (next, _, born, notes) = echod_concrete::node::spec_due_transition(
        document,
        now,
        config.retry_timeout,
    );
    ||| next == document && born.len() == 0 && notes.len() == 0
    ||| exists|work: Seq<echod_abstract::view::InternalV>|
        #[trigger] echod_concrete::relation::timeout_trace_legal(
            config,
            abstract_state,
            now,
            work,
        ) && {
        let trace = echod_concrete::relation::spec_timeout_trace(
            config, abstract_state, now, work,
        );
        &&& echod_concrete::relation::note_sends(notes).to_set()
            .subset_of(trace.send.to_set())
        &&& trace.state.pending
            == abstract_state.pending
                + echod_concrete::relation::items(born)
        &&& doc_rel(key, next, trace.state.store)
        &&& echod_concrete::interpret::others_kept(
            key,
            abstract_state.store,
            trace.state.store,
        )
        &&& finite_store(trace.state.store)
    }
}

/// Relate the production workflow transition to the
/// corresponding sequence of exact abstract internal transitions.
pub proof fn lemma_origin_sweep_matches_abstract_bulk_transition(
    config: ServerConfig,
    key: Seq<char>,
    document: echod_concrete::node::DocumentBodyV,
    abstract_state: AbstractStateV,
    now: u64,
)
    requires
        doc_rel(key, document, abstract_state.store),
        finite_store(abstract_state.store),
    ensures
        origin_sweep_matches(
            config,
            key,
            document,
            abstract_state,
            now,
        ),
{
    echod_concrete::timers::lemma_due_agrees(
        config,
        key,
        document,
        abstract_state,
        now,
    );
    reveal(origin_sweep_matches);
    reveal(echod_concrete::relation::due_agrees);
}

/// The endpoint of the finite abstract timeout trace corresponding to the
/// atomic concrete workflow transition.
pub open spec fn origin_bulk_transition_to(
    config: ServerConfig,
    key: Seq<char>,
    document: echod_concrete::node::DocumentBodyV,
    abstract_state: AbstractStateV,
    now: u64,
    final_state: AbstractStateV,
) -> bool {
    let (next, _, born, notes) = echod_concrete::node::spec_due_transition(
        document,
        now,
        config.retry_timeout,
    );
    ||| next == document
        && born.len() == 0
        && notes.len() == 0
        && final_state == abstract_state
    ||| exists|work: Seq<echod_abstract::view::InternalV>|
        #[trigger] echod_concrete::relation::timeout_trace_legal(
            config,
            abstract_state,
            now,
            work,
        ) && {
        let trace = echod_concrete::relation::spec_timeout_trace(
            config, abstract_state, now, work,
        );
        &&& final_state == trace.state
        &&& echod_concrete::relation::note_sends(notes).to_set()
            .subset_of(trace.send.to_set())
        &&& trace.state.pending
            == abstract_state.pending
                + echod_concrete::relation::items(born)
        &&& doc_rel(key, next, trace.state.store)
        &&& echod_concrete::interpret::others_kept(
            key,
            abstract_state.store,
            trace.state.store,
        )
        &&& finite_store(trace.state.store)
    }
}

pub proof fn lemma_origin_bulk_transition_endpoint_exists(
    config: ServerConfig,
    key: Seq<char>,
    document: echod_concrete::node::DocumentBodyV,
    abstract_state: AbstractStateV,
    now: u64,
)
    requires
        doc_rel(key, document, abstract_state.store),
        finite_store(abstract_state.store),
    ensures
        exists|final_state: AbstractStateV|
            origin_bulk_transition_to(
                config,
                key,
                document,
                abstract_state,
                now,
                final_state,
            ),
{
    let (next, _, born, notes) =
        echod_concrete::node::spec_due_transition(
            document,
            now,
            config.retry_timeout,
        );
    echod_concrete::timers::lemma_due_agrees(
        config,
        key,
        document,
        abstract_state,
        now,
    );
    reveal(echod_concrete::relation::due_agrees);
    reveal(origin_bulk_transition_to);
    if next == document && born.len() == 0 && notes.len() == 0 {
        assert(origin_bulk_transition_to(
            config, key, document, abstract_state, now, abstract_state,
        ));
    } else {
        let work = choose|work: Seq<echod_abstract::view::InternalV>|
            echod_concrete::relation::timeout_trace_legal(
                config, abstract_state, now, work,
            ) && {
                let trace = echod_concrete::relation::spec_timeout_trace(
                    config, abstract_state, now, work,
                );
                &&& echod_concrete::relation::note_sends(notes).to_set()
                    .subset_of(trace.send.to_set())
                &&& trace.state.pending
                    == abstract_state.pending + echod_concrete::relation::items(born)
                &&& doc_rel(key, next, trace.state.store)
                &&& echod_concrete::interpret::others_kept(
                    key, abstract_state.store, trace.state.store,
                )
                &&& finite_store(trace.state.store)
            };
        let trace = echod_concrete::relation::spec_timeout_trace(
            config, abstract_state, now, work,
        );
        assert(origin_bulk_transition_to(
            config, key, document, abstract_state, now, trace.state,
        ));
    }
}

pub proof fn lemma_origin_bulk_transition_endpoint_frames(
    config: ServerConfig,
    key: Seq<char>,
    document: echod_concrete::node::DocumentBodyV,
    abstract_state: AbstractStateV,
    now: u64,
    final_state: AbstractStateV,
)
    requires
        document is Workflow,
        doc_rel(key, document, abstract_state.store),
        finite_store(abstract_state.store),
        origin_bulk_transition_to(
            config,
            key,
            document,
            abstract_state,
            now,
            final_state,
        ),
    ensures
        ({
            let swept = echod_concrete::node::spec_sweep(
                document,
                now,
                config.retry_timeout,
            ).0;
            &&& doc_rel(key, swept, final_state.store)
            &&& echod_concrete::interpret::others_kept(
                key,
                abstract_state.store,
                final_state.store,
            )
            &&& finite_store(final_state.store)
            &&& final_state.pending == abstract_state.pending
        }),
{
    reveal(origin_bulk_transition_to);
    reveal(echod_concrete::node::spec_sweep);
    let (next, _, born, notes) =
        echod_concrete::node::spec_due_transition(
            document,
            now,
            config.retry_timeout,
        );
    if next == document {
        assert forall|other: Seq<char>,
            body: echod_concrete::node::DocumentBodyV|
            other != key
                && doc_rel(other, body, abstract_state.store)
            implies #[trigger] doc_rel(other, body, final_state.store) by {
        }
    } else {
        assert(next is Workflow);
        assert(born =~= Seq::<echod_concrete::node::PendingV>::empty());
        assert forall|other: Seq<char>,
            body: echod_concrete::node::DocumentBodyV|
            other != key
                && doc_rel(other, body, abstract_state.store)
            implies #[trigger] doc_rel(other, body, final_state.store) by {
        }
        assert(echod_concrete::relation::items(born).len() == 0);
    }
}

/// `spec_commit_new` stores the fully closed bulk sweep result. The sequence
/// may subsequently issue deadline-key
/// actions before its conditional document write, but its committed payload is
/// already fixed here.
pub proof fn lemma_origin_commit_new_records_bulk_sweep(
    s: S,
    w: crate::handler_docs::WorkingSpec,
    workflow: echod_concrete::document::WorkflowDocumentV,
    now: u64,
    retry_timeout: u64,
)
    requires
        w.loaded.document == StoredDocumentV::Workflow(workflow),
        echod_concrete::document::workflow_well_formed(workflow),
        workflow.committed_at <= now,
        now <= MAX_TIME,
        0 < retry_timeout <= MAX_TIME,
    ensures
        ({
            let swept = echod_concrete::node::spec_sweep(
                echod_concrete::node::DocumentBodyV::Workflow(
                    workflow.objects,
                ),
                now,
                retry_timeout,
            ).0;
            let (_, commit) = crate::handler_docs::spec_commit_new(
                s,
                w,
                swept,
                echod_concrete::node::spec_body_deadline(swept),
                now,
                None,
            );
            &&& commit.after
                == echod_concrete::node::spec_advance_stored(
                    StoredDocumentV::Workflow(workflow),
                    swept,
                    now,
                )
            &&& well_formed(commit.after)
            &&& commit.issued is None
        }),
{
    lemma_bulk_sweep_preserves_well_formed(
        workflow,
        now,
        retry_timeout,
    );
    reveal(crate::handler_docs::spec_commit_new);
}

/// The production commit begins with the optional new deadline key and then
/// the conditional document write.  Its verified sequence subsequently
/// includes the optional previous-key deletion and fired-key collection before
/// `Done`; all five shapes are the actions consumed by `spec_commit_advance`.
pub proof fn lemma_bulk_origin_commit_sequence_covers_write_cleanup(
    s: S,
    fid: u64,
    w: crate::handler_docs::WorkingSpec,
    workflow: echod_concrete::document::WorkflowDocumentV,
    now: u64,
    retry_timeout: u64,
    tag: Seq<char>,
)
    requires
        w.loaded.document == StoredDocumentV::Workflow(workflow),
        echod_concrete::document::workflow_well_formed(workflow),
        workflow.committed_at <= now,
        now <= MAX_TIME,
        0 < retry_timeout <= MAX_TIME,
        ({
            let document =
                echod_concrete::node::DocumentBodyV::Workflow(
                    workflow.objects,
                );
            let swept = echod_concrete::node::spec_sweep(
                document,
                now,
                retry_timeout,
            ).0;
            swept != document
        }),
    ensures
        ({
            let document =
                echod_concrete::node::DocumentBodyV::Workflow(
                    workflow.objects,
                );
            let swept = echod_concrete::node::spec_sweep(
                document,
                now,
                retry_timeout,
            ).0;
            let (planned, commit) =
                crate::handler_docs::spec_commit_new(
                    s,
                    w,
                    swept,
                    echod_concrete::node::spec_body_deadline(swept),
                    now,
                    None,
                );
            let (started, first, progress) =
                crate::handler_docs::spec_commit_advance(
                    planned,
                    fid,
                    commit,
                    None,
                );
            let calls =
                crate::verified::flight_spec::spec_calls(
                    commit.seq,
                    planned.node.core,
                );
            let run = crate::verified::flight_spec::spec_run(
                commit.seq,
                planned.node.core,
                tag,
                6,
            );
            &&& commit.seq.step is Start
            &&& commit.seq.changed
            &&& progress is Issued
            &&& first.issued is Some
            &&& calls.len() >= 2
            &&& match calls[0] {
                crate::verified::flight_spec::AAct::PutKey(_) =>
                    first.issued->Some_0 is Key,
                crate::verified::flight_spec::AAct::Write { .. } =>
                    first.issued->Some_0 is Write,
                _ => false,
            }
            &&& run.0 == calls
            &&& run.1.step is Over
            &&& run.2
                == crate::verified::flight_spec::spec_node_after(
                    commit.seq,
                    planned.node.core,
                    tag,
                )
        }),
{
    let document =
        echod_concrete::node::DocumentBodyV::Workflow(workflow.objects);
    let swept = echod_concrete::node::spec_sweep(
        document,
        now,
        retry_timeout,
    ).0;
    lemma_origin_commit_new_records_bulk_sweep(
        s,
        w,
        workflow,
        now,
        retry_timeout,
    );
    let (planned, commit) = crate::handler_docs::spec_commit_new(
        s,
        w,
        swept,
        echod_concrete::node::spec_body_deadline(swept),
        now,
        None,
    );
    reveal(crate::handler_docs::spec_commit_new);
    crate::verified::flight_spec::lemma_sequence(
        commit.seq,
        planned.node.core,
        tag,
    );
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::verified::flight_spec::spec_calls);
    reveal(crate::state::spec_store);
}

/// A successful conditional document response records the exact committed
/// origin payload and etag while leaving timer accounting, wheel/backlog
/// activity, and concurrent document lanes untouched.
pub proof fn lemma_successful_origin_write_answer_preserves_timer_lanes(
    s: S,
    commit: crate::handler_docs::CommittingSpec,
    issued: crate::handler_docs::IssuedSpec,
    answer: Option<StoreRes>,
)
    requires
        issued is Write,
        commit.after is Workflow,
        match answer {
            Some(StoreRes::PutIfMatch { result: Ok(_) })
            | Some(StoreRes::PutIfNoneMatch { result: Ok(_) })
            | Some(StoreRes::AppIfMatch { result: Ok(_) }) => true,
            _ => false,
        },
    ensures
        ({
            let (after, next) = crate::handler_docs::spec_answered(
                s,
                commit,
                issued,
                answer,
            );
            &&& next.after == commit.after
            &&& next.issued == commit.issued
            &&& after.timers == s.timers
            &&& after.flights == s.flights
        }),
{
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_remember);
}

/// A successfully loaded due schedule determines the promise carried by the
/// exact abstract `ScheduleTimeout`; no occurrence is committed by this
/// identification theorem.
pub proof fn lemma_loaded_schedule_identifies_timeout(
    config: ServerConfig,
    key: Seq<char>,
    id: Seq<char>,
    schedule: echod_types::Schedule,
    abstract_state: AbstractStateV,
    now: u64,
)
    requires
        key == echod_concrete::node::spec_schedule_key(id),
        echod_concrete::interpret::slot_rel(
            Some(schedule),
            id,
            abstract_state.store,
        ),
        finite_store(abstract_state.store),
        schedule.next_run_at <= now,
        schedule.next_run_at <= MAX_TIME,
    ensures
        ({
            let work = echod_concrete::timers::schedule_work(
                abstract_state.store,
                id,
            );
            let abstract_schedule = abstract_state.store.schedules[id];
            &&& work
                == echod_abstract::view::InternalV::ScheduleTimeout {
                    id,
                    promise:
                        echod_abstract::trusted::spec_expand(
                            abstract_schedule.promise_id,
                            id,
                            abstract_schedule.next_run_at,
                        ),
                }
            &&& echod_concrete::timers::work_known(
                abstract_state.store,
                work,
                now,
            )
            &&& echod_concrete::timers::offered(
                config,
                abstract_state,
                now,
                work,
                echod_abstract::model::spec_run_timeout(
                    config,
                    abstract_state,
                    now,
                ),
            )
            &&& echod_concrete::relation::due_agrees(
                config,
                key,
                echod_concrete::node::DocumentBodyV::Schedule(
                    Some(schedule),
                ),
                abstract_state,
                now,
            )
        }),
{
    let work = echod_concrete::timers::schedule_work(
        abstract_state.store,
        id,
    );
    assert(abstract_state.store.schedules.contains_key(id));
    assert(echod_concrete::timers::work_known(
        abstract_state.store,
        work,
        now,
    ));
    echod_concrete::timers::lemma_work_offered(
        config,
        abstract_state,
        now,
        work,
    );
    echod_concrete::timers::lemma_schedule_due(
        config,
        key,
        id,
        schedule,
        abstract_state,
        now,
    );
}

/// The exact abstract trace represented by a successful split schedule fire.
/// The schedule advance and occurrence insertion are exact indexed timeout
/// results. The origin's atomic post-insertion bulk sweep is represented by
/// its corresponding finite abstract timeout trace.
pub open spec fn schedule_fire_atomic_trace(
    config: ServerConfig,
    schedule_key: Seq<char>,
    schedule_doc: echod_concrete::node::DocumentBodyV,
    origin_key: Seq<char>,
    origin_doc: echod_concrete::node::DocumentBodyV,
    abstract_before: AbstractStateV,
    now: u64,
    scheduled: AbstractStateV,
    occurred: AbstractStateV,
    abstract_after: AbstractStateV,
) -> bool {
    let schedule_step = echod_concrete::node::spec_due_transition(
        schedule_doc,
        now,
        config.retry_timeout,
    );
    let pending = schedule_step.2[0];
    let schedule_results = echod_abstract::model::spec_run_timeout(
        config,
        abstract_before,
        now,
    );
    let occurrence_work =
        echod_concrete::relation::as_item(pending);
    let occurrence_out =
        echod_abstract::machine::spec_process_work(
            config,
            echod_abstract::machine::spec_body(occurrence_work),
            scheduled.store,
            now,
        );
    let occurrence_result =
        echod_abstract::model::spec_internal_result(
            scheduled,
            0,
            occurrence_out,
        );
    let raw = echod_concrete::node::spec_occurrence(
        origin_doc,
        pending,
        now,
    );
    let retry_step = echod_concrete::node::spec_due_transition(
        raw,
        now,
        config.retry_timeout,
    );
    &&& schedule_step.2.len() == 1
    &&& exists|schedule_index: int|
        #![trigger schedule_results[schedule_index]]
        0 <= schedule_index < schedule_results.len()
            && schedule_results[schedule_index].state == scheduled
    &&& scheduled.pending == seq![occurrence_work]
    &&& occurrence_result.state == occurred
    &&& echod_abstract::model::spec_run_timeout(
        config,
        scheduled,
        now,
    ).len() > 0
    &&& echod_abstract::model::spec_run_timeout(
        config,
        scheduled,
        now,
    )[0] == occurrence_result
    &&& occurred.pending.len() == 0
    &&& exists|work: Seq<echod_abstract::view::InternalV>|
        #[trigger] echod_concrete::relation::timeout_trace_legal(
            config, occurred, now, work,
        ) && {
            let trace =
                echod_concrete::relation::spec_timeout_trace(
                    config, occurred, now, work,
                );
            &&& trace.state == abstract_after
            &&& echod_concrete::relation::note_sends(
                    retry_step.3,
                ).to_set().subset_of(trace.send.to_set())
        }
    &&& doc_rel(schedule_key, schedule_step.0, abstract_after.store)
    &&& doc_rel(origin_key, retry_step.0, abstract_after.store)
    &&& finite_store(abstract_after.store)
}

/// Explicit relation at the split implementation's intermediate point:
/// the origin candidate (including its exact CAS-gated effects) is complete,
/// while the schedule candidate is the already-decided second commit.  The
/// related abstract side has taken the atomic ScheduleTimeout, queued and
/// created that exact occurrence, and—when runnable—taken its exact retry
/// dispatch.
pub open spec fn schedule_fire_split_intermediate(
    config: ServerConfig,
    schedule_key: Seq<char>,
    schedule_doc: echod_concrete::node::DocumentBodyV,
    origin_key: Seq<char>,
    origin_doc: echod_concrete::node::DocumentBodyV,
    abstract_before: AbstractStateV,
    now: u64,
    scheduled: AbstractStateV,
    occurred: AbstractStateV,
    abstract_after: AbstractStateV,
) -> bool {
    let schedule_step = echod_concrete::node::spec_due_transition(
        schedule_doc,
        now,
        config.retry_timeout,
    );
    let pending = schedule_step.2[0];
    let origin_transition =
        echod_concrete::node::spec_occurrence_transition(
            origin_doc,
            pending,
            now,
            config.retry_timeout,
        );
    let raw = echod_concrete::node::spec_occurrence(
        origin_doc,
        pending,
        now,
    );
    let retry_step = echod_concrete::node::spec_due_transition(
        raw,
        now,
        config.retry_timeout,
    );
    &&& origin_transition.0 == retry_step.0
    &&& origin_transition.1
        == echod_concrete::node::spec_committed_notes(
            origin_doc,
            retry_step.0,
            now,
        )
    &&& schedule_fire_atomic_trace(
        config,
        schedule_key,
        schedule_doc,
        origin_key,
        origin_doc,
        abstract_before,
        now,
        scheduled,
        occurred,
        abstract_after,
    )
}

/// Relation retained after an origin CAS succeeds but the schedule CAS loses a
/// race. Reloading the still-due schedule chooses the same deterministic
/// occurrence, while the committed origin is a fixed point with no candidate
/// effects. The abstract side therefore stays at the one already-taken atomic
/// timeout endpoint instead of taking a duplicate timeout.
pub open spec fn schedule_fire_retry_stutter_relation(
    config: ServerConfig,
    schedule_key: Seq<char>,
    schedule_doc: echod_concrete::node::DocumentBodyV,
    origin_key: Seq<char>,
    origin_doc: echod_concrete::node::DocumentBodyV,
    abstract_before: AbstractStateV,
    now: u64,
    scheduled: AbstractStateV,
    occurred: AbstractStateV,
    abstract_after: AbstractStateV,
) -> bool {
    let schedule_step = echod_concrete::node::spec_due_transition(
        schedule_doc,
        now,
        config.retry_timeout,
    );
    let pending = schedule_step.2[0];
    let first = echod_concrete::node::spec_occurrence_transition(
        origin_doc,
        pending,
        now,
        config.retry_timeout,
    );
    let retry = echod_concrete::node::spec_occurrence_transition(
        first.0,
        pending,
        now,
        config.retry_timeout,
    );
    &&& schedule_fire_split_intermediate(
        config,
        schedule_key,
        schedule_doc,
        origin_key,
        origin_doc,
        abstract_before,
        now,
        scheduled,
        occurred,
        abstract_after,
    )
    &&& retry == (
        first.0,
        Seq::<echod_concrete::node::NoteV>::empty(),
    )
    &&& echod_concrete::node::spec_due_transition(
        schedule_doc,
        now,
        config.retry_timeout,
    ) == schedule_step
}

pub proof fn lemma_schedule_cas_race_retry_is_idempotent(
    config: ServerConfig,
    schedule_key: Seq<char>,
    schedule_doc: echod_concrete::node::DocumentBodyV,
    origin_key: Seq<char>,
    origin_doc: echod_concrete::node::DocumentBodyV,
    abstract_before: AbstractStateV,
    now: u64,
    scheduled: AbstractStateV,
    occurred: AbstractStateV,
    abstract_after: AbstractStateV,
)
    requires
        schedule_fire_split_intermediate(
            config,
            schedule_key,
            schedule_doc,
            origin_key,
            origin_doc,
            abstract_before,
            now,
            scheduled,
            occurred,
            abstract_after,
        ),
        ({
            let schedule_step =
                echod_concrete::node::spec_due_transition(
                    schedule_doc,
                    now,
                    config.retry_timeout,
                );
            let pending = schedule_step.2[0];
            let first =
                echod_concrete::node::spec_occurrence_transition(
                    origin_doc,
                    pending,
                    now,
                    config.retry_timeout,
                );
            &&& first.0 is Workflow
            &&& first.0->Workflow_0.contains_key(
                pending.promise,
            )
            &&& echod_concrete::node::spec_earliest_in(
                first.0,
                now,
            ) is None
            &&& echod_concrete::node::spec_due_transition(
                first.0,
                now,
                config.retry_timeout,
            ).0 == first.0
        }),
    ensures
        schedule_fire_retry_stutter_relation(
            config,
            schedule_key,
            schedule_doc,
            origin_key,
            origin_doc,
            abstract_before,
            now,
            scheduled,
            occurred,
            abstract_after,
        ),
{
    let schedule_step =
        echod_concrete::node::spec_due_transition(
            schedule_doc,
            now,
            config.retry_timeout,
        );
    let pending = schedule_step.2[0];
    let first =
        echod_concrete::node::spec_occurrence_transition(
            origin_doc,
            pending,
            now,
            config.retry_timeout,
        );
    lemma_existing_occurrence_transition_is_idempotent(
        first.0,
        pending,
        now,
        config.retry_timeout,
    );
}

/// Bounded schedule-fire match for an already closed origin.  The production
/// document path is exactly raw occurrence creation followed by one changing
/// retry step and then idle.  The abstract witness is the indexed
/// `ScheduleTimeout`, its queued `Occurrence`, and the exact retry result
/// carrying the production Execute effect.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub proof fn lemma_closed_origin_schedule_fire_matches_atomic_timeout(
    config: ServerConfig,
    schedule_key: Seq<char>,
    schedule_doc: echod_concrete::node::DocumentBodyV,
    origin_key: Seq<char>,
    origin_doc: echod_concrete::node::DocumentBodyV,
    abstract_before: AbstractStateV,
    now: u64,
)
    requires
        schedule_key != origin_key,
        doc_rel(schedule_key, schedule_doc, abstract_before.store),
        doc_rel(origin_key, origin_doc, abstract_before.store),
        finite_store(abstract_before.store),
        abstract_before.pending.len() == 0,
        ({
            let schedule_step =
                echod_concrete::node::spec_due_transition(
                    schedule_doc,
                    now,
                    config.retry_timeout,
                );
            &&& schedule_step.0 != schedule_doc
            &&& schedule_step.2.len() == 1
            &&& origin_key
                == echod_concrete::node::spec_origin_key(
                    echod_types::origin(
                        schedule_step.2[0].promise,
                    ),
                )
        }),
        ({
            let pending =
                echod_concrete::node::spec_due_transition(
                    schedule_doc,
                    now,
                    config.retry_timeout,
                ).2[0];
            let raw = echod_concrete::node::spec_occurrence(
                origin_doc,
                pending,
                now,
            );
            let retry = echod_concrete::node::spec_due_transition(
                raw,
                now,
                config.retry_timeout,
            );
            &&& echod_concrete::node::spec_earliest_in(
                origin_doc,
                now,
            ) is None
            &&& echod_concrete::node::spec_due_transition(
                origin_doc,
                now,
                config.retry_timeout,
            ).0 == origin_doc
            &&& raw != origin_doc
            &&& retry.0 != raw
            &&& retry.2.len() == 0
            &&& echod_concrete::node::spec_earliest_in(
                retry.0,
                now,
            ) is None
            &&& echod_concrete::node::spec_due_transition(
                retry.0,
                now,
                config.retry_timeout,
            ).0 == retry.0
        }),
    ensures
        exists|scheduled: AbstractStateV,
            occurred: AbstractStateV,
            abstract_after: AbstractStateV|
            schedule_fire_split_intermediate(
                config,
                schedule_key,
                schedule_doc,
                origin_key,
                origin_doc,
                abstract_before,
                now,
                scheduled,
                occurred,
                abstract_after,
            ),
{
    let schedule_step = echod_concrete::node::spec_due_transition(
        schedule_doc,
        now,
        config.retry_timeout,
    );
    let pending = schedule_step.2[0];
    echod_concrete::timers::lemma_due_agrees(
        config,
        schedule_key,
        schedule_doc,
        abstract_before,
        now,
    );
    echod_concrete::timers::lemma_changing_schedule_due_exact(
        config,
        schedule_key,
        schedule_doc,
        abstract_before,
        now,
    );
    reveal(echod_concrete::relation::due_agrees);
    reveal(echod_concrete::timers::schedule_due_exact);
    let schedule_results =
        echod_abstract::model::spec_run_timeout(
            config,
            abstract_before,
            now,
        );
    let schedule_index = choose|j: int|
        #![trigger schedule_results[j]]
        0 <= j < schedule_results.len()
            && schedule_results[j].state.pending
                == abstract_before.pending
                    + echod_concrete::relation::items(
                        schedule_step.2,
                    )
            && doc_rel(
                schedule_key,
                schedule_step.0,
                schedule_results[j].state.store,
            )
            && echod_concrete::interpret::others_kept(
                schedule_key,
                abstract_before.store,
                schedule_results[j].state.store,
            )
            && finite_store(schedule_results[j].state.store);
    let scheduled = schedule_results[schedule_index].state;
    assert(echod_concrete::relation::items(schedule_step.2)
        =~= seq![echod_concrete::relation::as_item(pending)]);
    assert(scheduled.pending
        =~= seq![echod_concrete::relation::as_item(pending)]);
    assert(doc_rel(origin_key, origin_doc, scheduled.store));

    let raw = echod_concrete::node::spec_occurrence(
        origin_doc,
        pending,
        now,
    );
    echod_concrete::timers::lemma_occurrence_agrees(
        pending,
        origin_doc,
        scheduled.store,
        now,
    );
    reveal(echod_concrete::relation::occurrence_agrees);
    let occurrence_work =
        echod_concrete::relation::as_item(pending);
    let occurrence_out =
        echod_abstract::machine::spec_process_work(
            config,
            echod_abstract::machine::spec_body(occurrence_work),
            scheduled.store,
            now,
        );
    let occurrence_result =
        echod_abstract::model::spec_internal_result(
            scheduled,
            0,
            occurrence_out,
        );
    let occurred = occurrence_result.state;
    reveal(echod_concrete::node::spec_due_transition);
    assert(pending.at <= now);
    reveal(echod_concrete::relation::as_item);
    reveal(echod_abstract::machine::spec_body);
    reveal(echod_abstract::model::spec_ready);
    reveal(echod_abstract::machine::spec_process_work);
    reveal(echod_abstract::machine::spec_create_if_absent);
    assert(echod_abstract::model::spec_ready(
        echod_abstract::machine::spec_body(occurrence_work),
        now,
    ));
    assert(!occurrence_out.not_due);
    reveal(echod_abstract::model::spec_run_timeout);
    reveal(echod_abstract::model::spec_queue);
    assert(echod_abstract::model::spec_run_timeout(
        config,
        scheduled,
        now,
    )[0] == occurrence_result);
    reveal(echod_abstract::model::spec_internal_result);
    reveal(echod_abstract::model::remove_at);
    assert(occurred.pending.len() == 0);
    assert(doc_rel(origin_key, raw, occurred.store));
    assert(finite_store(occurred.store));
    assert(doc_rel(schedule_key, schedule_step.0, occurred.store));

    let retry_step = echod_concrete::node::spec_due_transition(
        raw,
        now,
        config.retry_timeout,
    );
    echod_concrete::timers::lemma_due_agrees(
        config,
        origin_key,
        raw,
        occurred,
        now,
    );
    reveal(echod_concrete::relation::due_agrees);
    let retry_work =
        choose|work: Seq<echod_abstract::view::InternalV>|
            #[trigger]
            echod_concrete::relation::timeout_trace_legal(
                config, occurred, now, work,
            ) && {
                let trace =
                    echod_concrete::relation::spec_timeout_trace(
                        config, occurred, now, work,
                    );
                &&& echod_concrete::relation::note_sends(
                        retry_step.3,
                    ).to_set().subset_of(trace.send.to_set())
                &&& trace.state.pending
                    == occurred.pending
                        + echod_concrete::relation::items(
                            retry_step.2,
                        )
                &&& doc_rel(
                    origin_key,
                    retry_step.0,
                    trace.state.store,
                )
                &&& echod_concrete::interpret::others_kept(
                    origin_key,
                    occurred.store,
                    trace.state.store,
                )
                &&& finite_store(trace.state.store)
            };
    let retry_trace =
        echod_concrete::relation::spec_timeout_trace(
            config, occurred, now, retry_work,
        );
    let abstract_after = retry_trace.state;
    reveal(echod_concrete::interpret::others_kept);
    assert(doc_rel(
        schedule_key,
        schedule_step.0,
        abstract_after.store,
    ));
    assert(schedule_fire_atomic_trace(
        config,
        schedule_key,
        schedule_doc,
        origin_key,
        origin_doc,
        abstract_before,
        now,
        scheduled,
        occurred,
        abstract_after,
    ));
    reveal(echod_concrete::node::spec_occurrence_transition);
    reveal(echod_concrete::node::spec_sweep);
    assert(echod_concrete::node::spec_due_transition(
        origin_doc,
        now,
        config.retry_timeout,
    ).0 == origin_doc);
    assert(echod_concrete::node::spec_sweep(
        origin_doc,
        now,
        config.retry_timeout,
    ).0 == origin_doc);
    assert(echod_concrete::node::spec_sweep(
        raw,
        now,
        config.retry_timeout,
    ).0 == retry_step.0);
    assert(schedule_fire_split_intermediate(
        config,
        schedule_key,
        schedule_doc,
        origin_key,
        origin_doc,
        abstract_before,
        now,
        scheduled,
        occurred,
        abstract_after,
    ));
}

/// State match when the loaded origin contains arbitrary valid due work. The
/// origin bulk transition linearizes first; the schedule timeout then uses
/// that closed endpoint. The production occurrence transition reaches the
/// same final document.
pub open spec fn schedule_fire_preswept_trace(
    config: ServerConfig,
    schedule_key: Seq<char>,
    schedule_doc: echod_concrete::node::DocumentBodyV,
    origin_key: Seq<char>,
    origin_doc: echod_concrete::node::DocumentBodyV,
    abstract_before: AbstractStateV,
    now: u64,
    preswept: AbstractStateV,
    scheduled: AbstractStateV,
    occurred: AbstractStateV,
    abstract_after: AbstractStateV,
) -> bool {
    let swept = echod_concrete::node::spec_sweep(
        origin_doc,
        now,
        config.retry_timeout,
    ).0;
    let schedule_step = echod_concrete::node::spec_due_transition(
        schedule_doc,
        now,
        config.retry_timeout,
    );
    let pending = schedule_step.2[0];
    &&& origin_bulk_transition_to(
        config,
        origin_key,
        origin_doc,
        abstract_before,
        now,
        preswept,
    )
    &&& schedule_fire_split_intermediate(
        config,
        schedule_key,
        schedule_doc,
        origin_key,
        swept,
        preswept,
        now,
        scheduled,
        occurred,
        abstract_after,
    )
    &&& echod_concrete::node::spec_occurrence_transition(
        origin_doc,
        pending,
        now,
        config.retry_timeout,
    ).0
        == echod_concrete::node::spec_occurrence_transition(
            swept,
            pending,
            now,
            config.retry_timeout,
        ).0
}

pub proof fn lemma_preswept_origin_schedule_fire_matches_atomic_timeout(
    config: ServerConfig,
    schedule_key: Seq<char>,
    schedule_doc: echod_concrete::node::DocumentBodyV,
    origin_key: Seq<char>,
    origin_doc: echod_concrete::node::DocumentBodyV,
    abstract_before: AbstractStateV,
    now: u64,
    preswept: AbstractStateV,
)
    requires
        schedule_key != origin_key,
        origin_doc is Workflow,
        doc_rel(schedule_key, schedule_doc, abstract_before.store),
        doc_rel(origin_key, origin_doc, abstract_before.store),
        finite_store(abstract_before.store),
        abstract_before.pending.len() == 0,
        origin_bulk_transition_to(
            config,
            origin_key,
            origin_doc,
            abstract_before,
            now,
            preswept,
        ),
        ({
            let swept = echod_concrete::node::spec_sweep(
                origin_doc,
                now,
                config.retry_timeout,
            ).0;
            &&& echod_concrete::node::spec_earliest_in(
                swept,
                now,
            ) is None
            &&& echod_concrete::node::spec_due_transition(
                swept,
                now,
                config.retry_timeout,
            ).0 == swept
        }),
        ({
            let schedule_step =
                echod_concrete::node::spec_due_transition(
                    schedule_doc,
                    now,
                    config.retry_timeout,
                );
            &&& schedule_step.0 != schedule_doc
            &&& schedule_step.2.len() == 1
            &&& origin_key
                == echod_concrete::node::spec_origin_key(
                    echod_types::origin(
                        schedule_step.2[0].promise,
                    ),
                )
        }),
        ({
            let swept = echod_concrete::node::spec_sweep(
                origin_doc,
                now,
                config.retry_timeout,
            ).0;
            let pending =
                echod_concrete::node::spec_due_transition(
                    schedule_doc,
                    now,
                    config.retry_timeout,
                ).2[0];
            let raw = echod_concrete::node::spec_occurrence(
                swept,
                pending,
                now,
            );
            let retry = echod_concrete::node::spec_due_transition(
                raw,
                now,
                config.retry_timeout,
            );
            &&& raw != swept
            &&& retry.0 != raw
            &&& retry.2.len() == 0
            &&& echod_concrete::node::spec_earliest_in(
                retry.0,
                now,
            ) is None
            &&& echod_concrete::node::spec_due_transition(
                retry.0,
                now,
                config.retry_timeout,
            ).0 == retry.0
        }),
    ensures
        exists|scheduled: AbstractStateV,
            occurred: AbstractStateV,
            abstract_after: AbstractStateV|
            schedule_fire_preswept_trace(
                config,
                schedule_key,
                schedule_doc,
                origin_key,
                origin_doc,
                abstract_before,
                now,
                preswept,
                scheduled,
                occurred,
                abstract_after,
            ),
{
    let swept = echod_concrete::node::spec_sweep(
        origin_doc,
        now,
        config.retry_timeout,
    ).0;
    lemma_origin_bulk_transition_endpoint_frames(
        config,
        origin_key,
        origin_doc,
        abstract_before,
        now,
        preswept,
    );
    assert(doc_rel(
        schedule_key,
        schedule_doc,
        preswept.store,
    ));
    assert(preswept.pending.len() == 0);
    lemma_closed_origin_schedule_fire_matches_atomic_timeout(
        config,
        schedule_key,
        schedule_doc,
        origin_key,
        swept,
        preswept,
        now,
    );
    reveal(echod_concrete::node::spec_occurrence_transition);
    assert forall|scheduled: AbstractStateV,
        occurred: AbstractStateV,
        abstract_after: AbstractStateV|
        #[trigger] schedule_fire_split_intermediate(
            config,
            schedule_key,
            schedule_doc,
            origin_key,
            swept,
            preswept,
            now,
            scheduled,
            occurred,
            abstract_after,
        ) implies schedule_fire_preswept_trace(
            config,
            schedule_key,
            schedule_doc,
            origin_key,
            origin_doc,
            abstract_before,
            now,
            preswept,
            scheduled,
            occurred,
            abstract_after,
        ) by {
    }
}

/// The production occurrence transition closes both endpoints and derives
/// exactly the canonical endpoint effects.
pub proof fn lemma_occurrence_transition_is_bulk(
    document: echod_concrete::node::DocumentBodyV,
    pending: echod_concrete::node::PendingV,
    now: u64,
    retry_timeout: u64,
)
    ensures
        ({
            let before = echod_concrete::node::spec_sweep(
                document,
                now,
                retry_timeout,
            ).0;
            let created = echod_concrete::node::spec_occurrence(
                before,
                pending,
                now,
            );
            let after = echod_concrete::node::spec_sweep(
                created,
                now,
                retry_timeout,
            ).0;
            let result =
                echod_concrete::node::spec_occurrence_transition(
                    document,
                    pending,
                    now,
                    retry_timeout,
                );
            result == (
                    after,
                    echod_concrete::node::spec_committed_notes(
                    document,
                        after,
                        now,
                    ),
                )
        }),
{
    reveal(echod_concrete::node::spec_occurrence_transition);
}

proof fn lemma_execute_notes_same_empty(
    map: Map<Seq<char>, echod_concrete::node::ObjV>,
    now: u64,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= keys.len(),
    ensures
        echod_concrete::node::spec_execute_notes(
            map,
            map,
            now,
            keys,
            count,
        ) == Seq::<echod_concrete::node::NoteV>::empty(),
    decreases count,
{
    reveal(echod_concrete::node::spec_execute_notes);
    if count > 0 {
        lemma_execute_notes_same_empty(
            map,
            now,
            keys,
            (count - 1) as nat,
        );
        reveal(echod_concrete::document::offer_committed);
    }
}

proof fn lemma_unblock_notes_for_same_empty(
    map: Map<Seq<char>, echod_concrete::node::ObjV>,
    promise: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= listeners.len(),
    ensures
        echod_concrete::node::spec_unblock_notes_for(
            map,
            map,
            promise,
            listeners,
            count,
        ) == Seq::<echod_concrete::node::NoteV>::empty(),
    decreases count,
{
    reveal(echod_concrete::node::spec_unblock_notes_for);
    if count > 0 {
        lemma_unblock_notes_for_same_empty(
            map,
            promise,
            listeners,
            (count - 1) as nat,
        );
        reveal(echod_concrete::document::listener_committed);
    }
}

proof fn lemma_unblock_notes_same_empty(
    map: Map<Seq<char>, echod_concrete::node::ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= keys.len(),
        forall|i: int|
            0 <= i < count ==> map.contains_key(#[trigger] keys[i]),
    ensures
        echod_concrete::node::spec_unblock_notes(
            map,
            map,
            keys,
            count,
        ) == Seq::<echod_concrete::node::NoteV>::empty(),
    decreases count,
{
    reveal(echod_concrete::node::spec_unblock_notes);
    if count > 0 {
        lemma_unblock_notes_same_empty(
            map,
            keys,
            (count - 1) as nat,
        );
        let promise = keys[count as int - 1];
        lemma_unblock_notes_for_same_empty(
            map,
            promise,
            map[promise].promise.listeners,
            map[promise].promise.listeners.len(),
        );
    }
}

/// Retrying a schedule fire after its origin CAS has already committed cannot
/// recreate or redispatch that occurrence.  A closed origin containing the
/// deterministic occurrence id is an exact fixed point of occurrence
/// insertion and both whole-map phases; endpoint-derived effects are empty.
pub proof fn lemma_existing_occurrence_transition_is_idempotent(
    document: echod_concrete::node::DocumentBodyV,
    pending: echod_concrete::node::PendingV,
    now: u64,
    retry_timeout: u64,
)
    requires
        document is Workflow,
        document->Workflow_0.contains_key(pending.promise),
        echod_concrete::node::spec_earliest_in(document, now) is None,
        echod_concrete::node::spec_due_transition(
            document,
            now,
            retry_timeout,
        ).0 == document,
    ensures
        echod_concrete::node::spec_occurrence_transition(
            document,
            pending,
            now,
            retry_timeout,
        ) == (
            document,
            Seq::<echod_concrete::node::NoteV>::empty(),
        ),
{
    reveal(echod_concrete::node::spec_occurrence_transition);
    reveal(echod_concrete::node::spec_sweep);
    reveal(echod_concrete::node::spec_occurrence);
    reveal(echod_concrete::node::spec_opened);
    assert(echod_concrete::node::spec_sweep(
        document,
        now,
        retry_timeout,
    ).0 == document);
    assert(echod_concrete::node::spec_occurrence(
        document,
        pending,
        now,
    ) == document);
    let map = document->Workflow_0;
    let keys = echod_concrete::node::spec_sorted_present(map);
    echod_concrete::timers::lemma_sorted(map.dom());
    lemma_execute_notes_same_empty(
        map,
        now,
        keys,
        keys.len(),
    );
    lemma_unblock_notes_same_empty(
        map,
        keys,
        keys.len(),
    );
    reveal(echod_concrete::node::spec_committed_notes);
    assert(echod_concrete::node::spec_committed_notes(
        document,
        document,
        now,
    ) =~= Seq::<echod_concrete::node::NoteV>::empty());
}

/// The bulk occurrence transition preserves the full stored-document
/// invariant. The raw insertion preserves the relaxed invariant under the
/// schedule's key/tag validity facts, and phase 2 upgrades directly to full
/// `well_formed`.
pub proof fn lemma_occurrence_transition_preserves_well_formed(
    workflow: echod_concrete::document::WorkflowDocumentV,
    pending: echod_concrete::node::PendingV,
    now: u64,
    retry_timeout: u64,
)
    requires
        echod_concrete::document::workflow_well_formed(workflow),
        workflow.committed_at <= now,
        now <= MAX_TIME,
        0 < retry_timeout <= MAX_TIME,
        pending.at <= now,
        exists|id: String| id@ == pending.promise,
        echod_concrete::store::spec_sat_add(
            pending.at,
            pending.timeout,
        ) <= MAX_TIME,
        echod_types::origin(pending.promise) == workflow.document,
        !(echod_concrete::node::spec_timer(pending.tags)
            && echod_concrete::node::spec_targeted(pending.tags)),
    ensures
        ({
            let after =
                echod_concrete::node::spec_occurrence_transition(
                    echod_concrete::node::DocumentBodyV::Workflow(
                        workflow.objects,
                    ),
                    pending,
                    now,
                    retry_timeout,
                ).0;
            well_formed(
                echod_concrete::node::spec_advance_stored(
                    StoredDocumentV::Workflow(workflow),
                    after,
                    now,
                ),
            )
        }),
{
    let document =
        echod_concrete::node::DocumentBodyV::Workflow(
            workflow.objects,
        );
    let before = echod_concrete::node::spec_sweep(
        document,
        now,
        retry_timeout,
    ).0;
    let created = echod_concrete::node::spec_occurrence(
        before,
        pending,
        now,
    );
    let after = echod_concrete::node::spec_sweep(
        created,
        now,
        retry_timeout,
    ).0;
    echod_concrete::quick_n_dirty::lemma_full_implies_relaxed(
        workflow,
        now,
    );
    echod_concrete::quick_n_dirty::lemma_sweep_preserves_relaxed(
        workflow.document,
        workflow.objects,
        now,
        retry_timeout,
    );
    assert(before is Workflow);
    reveal(echod_concrete::node::spec_occurrence_transition);
    assert(echod_concrete::node::spec_earliest_in(before, now)
        is None);
    echod_concrete::quick_n_dirty::lemma_occurrence_preserves_relaxed(
        workflow.document,
        before->Workflow_0,
        pending,
        now,
    );
    assert(created is Workflow);
    echod_concrete::quick_n_dirty::lemma_sweep_preserves_relaxed(
        workflow.document,
        created->Workflow_0,
        now,
        retry_timeout,
    );
    assert(echod_concrete::node::spec_earliest_in(after, now)
        is None);
    assert(after is Workflow);
    echod_concrete::quick_n_dirty::lemma_relaxed_closed(
        workflow.document,
        after->Workflow_0,
        now,
    );
    reveal(echod_concrete::document::well_formed);
    reveal(echod_concrete::document::workflow_well_formed);
    reveal(echod_concrete::node::spec_advance_stored);
}

/// The exact conditional document request selected by the production write
/// path.  This is a definition of production control, not a codec premise:
/// key, CAS kind, base offset, etag, and full-vs-delta choice are all fixed by
/// `CommittingSpec` and the process configuration.
pub open spec fn commit_write_request(
    s: S,
    commit: crate::handler_docs::CommittingSpec,
    cond: Option<Seq<char>>,
) -> StoreReqSpec {
    match cond {
        None => StoreReqSpec::PutIfNoneMatch {
            key: commit.w.key,
            body: crate::document::spec_encode(commit.after),
        },
        Some(etag) => {
            let after =
                echod_concrete::node::spec_stored_body(commit.after);
            let (delta, changed) =
                crate::document::spec_encode_delta(
                    commit.w.loaded.document,
                    commit.after,
                );
            let removed = crate::document::spec_removed_any(
                crate::document::spec_loaded_body(commit.w.loaded),
                after,
            );
            let after_len =
                echod_concrete::node::spec_body_len(after) as usize;
            let stale_after = commit.w.loaded.change_count
                .saturating_add(changed)
                .saturating_sub(after_len);
            let append =
                crate::document::spec_loaded_version(commit.w.loaded) > 0
                && !removed
                && s.cfg.appendable
                && s.cfg.compact > 0
                && stale_after < s.cfg.compact as usize;
            if append {
                StoreReqSpec::AppIfMatch {
                    key: commit.w.key,
                    offset: commit.w.loaded.bytes,
                    body: delta,
                    etag: echod_concrete::store::EtagSpec(etag),
                }
            } else {
                StoreReqSpec::PutIfMatch {
                    key: commit.w.key,
                    body: crate::document::spec_encode(commit.after),
                    etag: echod_concrete::store::EtagSpec(etag),
                }
            }
        },
    }
}

/// The state and commit after consuming the previous sequence action's
/// answer, immediately before `spec_advance` selects the next action.
pub open spec fn settled_commit(
    s: S,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<StoreRes>,
) -> (S, crate::handler_docs::CommittingSpec) {
    match commit.issued {
        Some(issued) => crate::handler_docs::spec_answered(
            s,
            crate::handler_docs::CommittingSpec {
                issued: None,
                ..commit
            },
            issued,
            answer,
        ),
        None => (s, commit),
    }
}

/// The real verified commit sequence is at its document-write action.
pub open spec fn commit_write_phase(
    s: S,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<StoreRes>,
    cond: Option<Seq<char>>,
    idle: bool,
) -> bool {
    let settled = settled_commit(s, commit, answer);
    crate::verified::flight_spec::spec_advance(
        settled.1.seq,
        settled.0.node.core,
        crate::verified::flight_spec::answer_v(
            settled.1.seq.step,
            answer,
        ),
    ).2 == crate::verified::flight_spec::AOutcome::Act(
        crate::verified::flight_spec::AAct::Write { cond, idle },
    )
}

/// Exact observable consequences of a write action.  In particular, the
/// request is appended by `spec_store` with the flight owner and the issued
/// phase records that same operation id.
pub open spec fn commit_advance_issues_write(
    s: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<StoreRes>,
    cond: Option<Seq<char>>,
    idle: bool,
) -> bool {
    let settled = settled_commit(s, commit, answer);
    let request = commit_write_request(settled.0, settled.1, cond);
    let op = settled.0.next_op;
    let advanced =
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            answer,
        );
    &&& advanced.0.out == settled.0.out.push(
        EffectSpec::Store { op, request },
    )
    &&& advanced.0.ops
        == settled.0.ops.insert(op, Owner::Flight(fid))
    &&& advanced.0.next_op == settled.0.next_op.wrapping_add(1)
    &&& advanced.1.issued is Some
    &&& match advanced.1.issued->Some_0 {
        crate::handler_docs::IssuedSpec::Write {
            op: issued_op,
            ..
        } => issued_op == op,
        _ => false,
    }
    &&& advanced.2 == crate::handler_docs::ProgressSpec::Issued
}

/// Production derives every Store control field from the commit itself.
pub proof fn lemma_commit_write_request_fields(
    s: S,
    commit: crate::handler_docs::CommittingSpec,
    cond: Option<Seq<char>>,
)
    ensures
        ({
            let request = commit_write_request(s, commit, cond);
            match cond {
                None => request == StoreReqSpec::PutIfNoneMatch {
                    key: commit.w.key,
                    body: crate::document::spec_encode(commit.after),
                },
                Some(etag) => {
                    let after =
                        echod_concrete::node::spec_stored_body(
                            commit.after,
                        );
                    let (delta, changed) =
                        crate::document::spec_encode_delta(
                            commit.w.loaded.document,
                            commit.after,
                        );
                    let removed = crate::document::spec_removed_any(
                        crate::document::spec_loaded_body(
                            commit.w.loaded,
                        ),
                        after,
                    );
                    let after_len =
                        echod_concrete::node::spec_body_len(after)
                            as usize;
                    let stale_after = commit.w.loaded.change_count
                        .saturating_add(changed)
                        .saturating_sub(after_len);
                    let append =
                        crate::document::spec_loaded_version(
                            commit.w.loaded,
                        ) > 0
                        && !removed
                        && s.cfg.appendable
                        && s.cfg.compact > 0
                        && stale_after < s.cfg.compact as usize;
                    if append {
                        request == StoreReqSpec::AppIfMatch {
                            key: commit.w.key,
                            offset: commit.w.loaded.bytes,
                            body: delta,
                            etag: echod_concrete::store::EtagSpec(etag),
                        }
                    } else {
                        request == StoreReqSpec::PutIfMatch {
                            key: commit.w.key,
                            body: crate::document::spec_encode(
                                commit.after,
                            ),
                            etag: echod_concrete::store::EtagSpec(etag),
                        }
                    }
                },
            }
        }),
{
    reveal(commit_write_request);
}

pub proof fn lemma_commit_write_phase_issues_exact_request(
    s: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<StoreRes>,
    cond: Option<Seq<char>>,
    idle: bool,
)
    requires
        commit_write_phase(s, commit, answer, cond, idle),
    ensures
        commit_advance_issues_write(
            s,
            fid,
            commit,
            answer,
            cond,
            idle,
        ),
{
    reveal(commit_write_phase);
    reveal(commit_advance_issues_write);
    reveal(settled_commit);
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store);
}

pub open spec fn is_fire_origin_commit(
    phase: PhaseSpec,
    commit: crate::handler_docs::CommittingSpec,
) -> bool {
    match phase {
        PhaseSpec::FireOrigin {
            commit: actual,
            ..
        } => actual == commit,
        _ => false,
    }
}

pub open spec fn is_fire_schedule_commit(
    phase: PhaseSpec,
    commit: crate::handler_docs::CommittingSpec,
) -> bool {
    match phase {
        PhaseSpec::FireSchedule {
            commit: actual,
        } => actual == commit,
        _ => false,
    }
}

pub proof fn lemma_schedule_fire_origin_phase_issues_exact_write(
    s: S,
    fid: u64,
    phase: PhaseSpec,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<StoreRes>,
    cond: Option<Seq<char>>,
    idle: bool,
)
    requires
        is_fire_origin_commit(phase, commit),
        commit_write_phase(s, commit, answer, cond, idle),
    ensures
        commit_advance_issues_write(
            s,
            fid,
            commit,
            answer,
            cond,
            idle,
        ),
{
    lemma_commit_write_phase_issues_exact_request(
        s,
        fid,
        commit,
        answer,
        cond,
        idle,
    );
}

pub proof fn lemma_schedule_fire_schedule_phase_issues_exact_write(
    s: S,
    fid: u64,
    phase: PhaseSpec,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<StoreRes>,
    cond: Option<Seq<char>>,
    idle: bool,
)
    requires
        is_fire_schedule_commit(phase, commit),
        commit_write_phase(s, commit, answer, cond, idle),
    ensures
        commit_advance_issues_write(
            s,
            fid,
            commit,
            answer,
            cond,
            idle,
        ),
{
    lemma_commit_write_phase_issues_exact_request(
        s,
        fid,
        commit,
        answer,
        cond,
        idle,
    );
}

/// Exact origin-CAS success branch.  The canonical occurrence effects are
/// released only after `spec_commit_advance` reports Done; the origin lane is
/// then released and the schedule commit begins.
pub proof fn lemma_schedule_origin_cas_success_emits_exact_effects(
    s: S,
    fid: u64,
    flight: FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    ctx: crate::handler_docs::FireCtxSpec,
    t: u64,
    outbox: Seq<(Seq<char>, MessageSpec)>,
    outcome: StoreRes,
    advanced: S,
    next: crate::handler_docs::CommittingSpec,
    fired: crate::types::Fired,
)
    requires
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            Some(outcome),
        ) == (
            advanced,
            next,
            crate::handler_docs::ProgressSpec::Done(fired),
        ),
    ensures
        crate::handler_docs::spec_answered_fire_origin(
            s,
            fid,
            flight,
            commit,
            ctx,
            t,
            outbox,
            outcome,
        ) == crate::handler_sched::spec_fire_advance(
            crate::handler_docs::spec_release(
                crate::handler_docs::spec_send_all(
                    crate::state::spec_note(
                        crate::state::spec_note(
                            advanced,
                            crate::types::NoteSpec::FireEnd {
                                flight: fid,
                                committed: true,
                            },
                        ),
                        crate::types::NoteSpec::Commit(
                            crate::types::CommitOutcome::Committed,
                        ),
                    ),
                    outbox,
                ),
                ctx.origin,
            ),
            flight,
            ctx,
            t,
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_origin);
}

/// An origin commit with more key actions outstanding remains in flight with
/// the exact candidate outbox still gated behind the eventual document CAS.
pub proof fn lemma_schedule_origin_cas_retry_keeps_effects_gated(
    s: S,
    fid: u64,
    flight: FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    ctx: crate::handler_docs::FireCtxSpec,
    t: u64,
    outbox: Seq<(Seq<char>, MessageSpec)>,
    outcome: StoreRes,
    advanced: S,
    next: crate::handler_docs::CommittingSpec,
)
    requires
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            Some(outcome),
        ) == (
            advanced,
            next,
            crate::handler_docs::ProgressSpec::Issued,
        ),
    ensures
        crate::handler_docs::spec_answered_fire_origin(
            s,
            fid,
            flight,
            commit,
            ctx,
            t,
            outbox,
            outcome,
        ) == crate::handler_docs::spec_inflight(
            advanced,
            FlightSpec {
                phase: PhaseSpec::FireOrigin {
                    commit: next,
                    ctx,
                    t,
                    outbox,
                },
                ..flight
            },
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_origin);
}

/// A failed origin CAS never evaluates `spec_send_all`.  Precondition failure
/// enters the normal re-load/re-decide retry path; every other Store error
/// terminates the flight.  In both cases the candidate occurrence effects are
/// discarded.
pub proof fn lemma_schedule_origin_cas_failure_discards_effects(
    s: S,
    fid: u64,
    flight: FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    ctx: crate::handler_docs::FireCtxSpec,
    t: u64,
    outbox: Seq<(Seq<char>, MessageSpec)>,
    outcome: StoreRes,
    advanced: S,
    next: crate::handler_docs::CommittingSpec,
    error: echod_concrete::store::StoreErrorSpec,
)
    requires
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            Some(outcome),
        ) == (
            advanced,
            next,
            crate::handler_docs::ProgressSpec::Failed(error),
        ),
    ensures
        crate::handler_docs::spec_answered_fire_origin(
            s,
            fid,
            flight,
            commit,
            ctx,
            t,
            outbox,
            outcome,
        ) == crate::handler_docs::spec_commit_failed(
            crate::handler_docs::spec_release(
                crate::state::spec_forget_origin(
                    crate::state::spec_note(
                        advanced,
                        crate::types::NoteSpec::FireEnd {
                            flight: fid,
                            committed: false,
                        },
                    ),
                    ctx.origin,
                ),
                ctx.origin,
            ),
            flight,
            error,
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_origin);
}

/// Exact second-CAS success branch.  No occurrence effect is delayed to this
/// point: schedule success only records AdvanceEnd/Commit and finishes the
/// timer flight with the fired-key result.
pub proof fn lemma_schedule_advance_cas_success_finishes_exactly(
    s: S,
    fid: u64,
    flight: FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    outcome: StoreRes,
    advanced: S,
    next: crate::handler_docs::CommittingSpec,
    fired: crate::types::Fired,
)
    requires
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            Some(outcome),
        ) == (
            advanced,
            next,
            crate::handler_docs::ProgressSpec::Done(fired),
        ),
    ensures
        crate::handler_docs::spec_answered_fire_schedule(
            s,
            fid,
            flight,
            commit,
            outcome,
        ) == crate::handler_docs::spec_finish(
            crate::state::spec_note(
                crate::state::spec_note(
                    advanced,
                    crate::types::NoteSpec::AdvanceEnd {
                        flight: fid,
                        committed: true,
                    },
                ),
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Committed,
                ),
            ),
            flight,
            Ok(fired),
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_schedule);
}

/// Outstanding key cleanup for the schedule commit is hidden in the same
/// flight.  It preserves the decided second commit and emits no occurrence
/// effect.
pub proof fn lemma_schedule_advance_cas_retry_preserves_second_commit(
    s: S,
    fid: u64,
    flight: FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    outcome: StoreRes,
    advanced: S,
    next: crate::handler_docs::CommittingSpec,
)
    requires
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            Some(outcome),
        ) == (
            advanced,
            next,
            crate::handler_docs::ProgressSpec::Issued,
        ),
    ensures
        crate::handler_docs::spec_answered_fire_schedule(
            s,
            fid,
            flight,
            commit,
            outcome,
        ) == crate::handler_docs::spec_inflight(
            advanced,
            FlightSpec {
                phase: PhaseSpec::FireSchedule {
                    commit: next,
                },
                ..flight
            },
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_schedule);
}

/// A failed schedule CAS records the failed advance and follows the existing
/// commit-failure policy.  In particular, precondition failure re-loads and
/// re-decides, while terminal Store failures discard this attempt; no
/// occurrence effect is duplicated at this second commit.
pub proof fn lemma_schedule_advance_cas_failure_retries_or_discards(
    s: S,
    fid: u64,
    flight: FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    outcome: StoreRes,
    advanced: S,
    next: crate::handler_docs::CommittingSpec,
    error: echod_concrete::store::StoreErrorSpec,
)
    requires
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            Some(outcome),
        ) == (
            advanced,
            next,
            crate::handler_docs::ProgressSpec::Failed(error),
        ),
    ensures
        crate::handler_docs::spec_answered_fire_schedule(
            s,
            fid,
            flight,
            commit,
            outcome,
        ) == crate::handler_docs::spec_commit_failed(
            crate::state::spec_note(
                advanced,
                crate::types::NoteSpec::AdvanceEnd {
                    flight: fid,
                    committed: false,
                },
            ),
            flight,
            error,
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_schedule);
}

/// A schedule CAS race restarts the same Fire flight by reloading the schedule.
/// The origin outbox was already consumed at the first CAS and is absent from
/// this phase, so the retry can only issue the hidden schedule Get; the
/// existing-occurrence fixed-point theorem governs the later origin reload.
pub proof fn lemma_schedule_advance_cas_race_reloads_fire(
    s: S,
    fid: u64,
    flight: FlightSpec,
    commit: crate::handler_docs::CommittingSpec,
    outcome: StoreRes,
    advanced: S,
    next: crate::handler_docs::CommittingSpec,
)
    requires
        flight.work is Fire,
        flight.target is Schedule,
        crate::handler_docs::spec_commit_advance(
            s,
            fid,
            commit,
            Some(outcome),
        ) == (
            advanced,
            next,
            crate::handler_docs::ProgressSpec::Failed(
                echod_concrete::store::StoreErrorSpec::PreconditionFailed,
            ),
        ),
    ensures
        crate::handler_docs::spec_answered_fire_schedule(
            s,
            fid,
            flight,
            commit,
            outcome,
        ) == crate::handler_docs::spec_retry(
            crate::state::spec_note(
                crate::state::spec_note(
                    crate::state::spec_note(
                        advanced,
                        crate::types::NoteSpec::AdvanceEnd {
                            flight: fid,
                            committed: false,
                        },
                    ),
                    crate::types::NoteSpec::Commit(
                        crate::types::CommitOutcome::Raced,
                    ),
                ),
                crate::types::NoteSpec::Raced {
                    target: crate::target::spec_name(
                        flight.target,
                    ),
                    attempt: flight.attempt,
                },
            ),
            flight,
        ),
{
    reveal(crate::handler_docs::spec_answered_fire_schedule);
    reveal(crate::handler_docs::spec_commit_failed);
}

/// Store-loading phases have not selected a durable document transition yet,
/// so they remain hidden before either identification theorem applies.
pub proof fn lemma_timeout_load_phases_are_prelinearized(
    load_op: OpId,
    cached: Option<crate::cache::CachedSpec>,
)
    ensures
        phase_after(PhaseSpec::Loading {
            op: load_op,
            revalidating: cached,
        }) is None,
        phase_after(PhaseSpec::FireLoadingSchedule {
            op: load_op,
        }) is None,
{
}

/// Kept/failed completion retains the encoded logical deadline and moves only
/// the operational wake slot. Saturation at `u64::MAX` is harmless: the slot
/// remains no earlier than both the firing slot and encoded deadline.
pub proof fn lemma_retry_slot_preserves_key_deadline(
    slots: Seq<crate::state_timers::SlotSpec>,
    key: Seq<char>,
    entry: crate::keys::TimerEntrySpec,
    firing_at: u64,
    now: u64,
)
    requires
        timer_slots_keys_valid(slots),
        crate::keys::spec_parse_timer_key(key) == Some(entry),
        firing_at >= entry.deadline(),
    ensures
        ({
            let retry =
                crate::state_timers::spec_max(now, firing_at)
                    .saturating_add(
                        crate::state_timers::RETRY_AFTER_MS,
                    );
            &&& retry >= firing_at
            &&& retry >= entry.deadline()
            &&& timer_slots_keys_valid(
                crate::state_timers::spec_arm(slots, retry, key),
            )
        }),
{
    let retry = crate::state_timers::spec_max(now, firing_at)
        .saturating_add(crate::state_timers::RETRY_AFTER_MS);
    assert(crate::state_timers::spec_max(now, firing_at)
        >= firing_at);
    assert(retry >= crate::state_timers::spec_max(now, firing_at));
    assert(retry >= firing_at);
    assert(retry >= entry.deadline());
    lemma_arm_preserves_timer_key_deadlines(
        slots,
        retry,
        key,
        entry,
    );
}

pub open spec fn timer_fired_ready(
    s: S,
    firing: crate::handler_docs::FiringSpec,
    now: u64,
    result: Result<crate::types::Fired, Seq<char>>,
) -> S {
    let decremented = crate::handler_timers::spec_with_timers(
        s,
        TimersSpec {
            inflight: s.timers.inflight.saturating_sub(1),
            ..s.timers
        },
    );
    let retry = crate::state_timers::spec_max(now, firing.at)
        .saturating_add(crate::state_timers::RETRY_AFTER_MS);
    let (staged, outcome) = match result {
        Ok(crate::types::Fired::Deleted) => (
            decremented,
            crate::types::FireOutcome::Deleted,
        ),
        Ok(crate::types::Fired::Kept) => (
            crate::handler_timers::spec_with_timers(
                decremented,
                TimersSpec {
                    wheel: crate::state_timers::TimerWheelSpec {
                        armed: crate::state_timers::spec_arm(
                            decremented.timers.wheel.armed,
                            retry,
                            firing.key,
                        ),
                    },
                    ..decremented.timers
                },
            ),
            crate::types::FireOutcome::Kept,
        ),
        Err(error) => {
            let noted = crate::state::spec_note(
                decremented,
                crate::types::NoteSpec::FireFailed {
                    key: firing.key,
                    error,
                },
            );
            (
                crate::handler_timers::spec_with_timers(
                    noted,
                    TimersSpec {
                        wheel: crate::state_timers::TimerWheelSpec {
                            armed: crate::state_timers::spec_arm(
                                noted.timers.wheel.armed,
                                retry,
                                firing.key,
                            ),
                        },
                        ..noted.timers
                    },
                ),
                crate::types::FireOutcome::Failed,
            )
        },
    };
    crate::state::spec_note(
        staged,
        crate::types::NoteSpec::TimerFire {
            kind: firing.kind,
            outcome,
            lag_ms: firing.lag,
        },
    )
}

/// A completed timer flight decrements its reservation and, for Kept/failed
/// outcomes, rearms at the operational retry slot. Arbitrary valid backlog
/// entries are then recursively redispatched under the full timer relation.
pub proof fn lemma_timer_fired_preserves_activity(
    s: S,
    firing: crate::handler_docs::FiringSpec,
    entry: crate::keys::TimerEntrySpec,
    now: u64,
    result: Result<crate::types::Fired, Seq<char>>,
)
    requires
        timer_activity_consistent(s),
        crate::keys::spec_parse_timer_key(firing.key) == Some(entry),
        firing.at >= entry.deadline(),
        s.timers.reload_pending
            || crate::handler_timers::spec_owns_entry(s, entry),
    ensures
        timer_activity_consistent(
            crate::handler_timers::spec_timer_fired(
                s,
                firing,
                now,
                result,
            ),
        ),
{
    lemma_timer_fired_preserves_accounting(s, firing, now, result);
    let retry = crate::state_timers::spec_max(now, firing.at)
        .saturating_add(crate::state_timers::RETRY_AFTER_MS);
    assert(retry >= firing.at);
    assert(retry >= entry.deadline());
    lemma_arm_preserves_timer_wheel_order(
        s.timers.wheel.armed,
        retry,
        firing.key,
    );
    lemma_retry_slot_preserves_key_deadline(
        s.timers.wheel.armed,
        firing.key,
        entry,
        firing.at,
        now,
    );
    if !s.timers.reload_pending {
        lemma_arm_preserves_timer_ownership(
            s,
            s.timers.wheel.armed,
            retry,
            firing.key,
            entry,
        );
    }
    let ready = timer_fired_ready(s, firing, now, result);
    reveal(timer_fired_ready);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state::spec_note);
    assert(timer_activity_consistent(ready));
    lemma_dispatch_due_preserves_activity(
        ready,
        now,
        ready.timers.backlog.len(),
    );
    reveal(crate::handler_timers::spec_timer_fired);
    assert(crate::handler_timers::spec_timer_fired(
        s,
        firing,
        now,
        result,
    ) == crate::handler_timers::spec_dispatch_due(
        ready,
        now,
        ready.timers.backlog.len(),
    ));
    assert(timer_activity_consistent(
        crate::handler_timers::spec_timer_fired(
            s,
            firing,
            now,
            result,
        ),
    ));
}

pub proof fn lemma_send_all_preserves_timer_control(
    s: S,
    outbox: Seq<(Seq<char>, MessageSpec)>,
)
    ensures
        ({
            let after =
                crate::handler_docs::spec_send_all(s, outbox);
            &&& after.timers == s.timers
            &&& after.node.core.members == s.node.core.members
            &&& after.cfg.node_id == s.cfg.node_id
            &&& after.flights == s.flights
        }),
    decreases outbox.len(),
{
    reveal(crate::handler_docs::spec_send_all);
    if outbox.len() > 0 {
        let emitted = crate::state::spec_emit(
            s,
            EffectSpec::Send {
                address: outbox[0].0,
                message: outbox[0].1,
            },
        );
        reveal(crate::state::spec_emit);
        lemma_send_all_preserves_timer_control(
            emitted,
            outbox.drop_first(),
        );
    }
}

/// Completing the atomic origin transition releases only its own empty lane and
/// then returns the firing reservation to the timer dispatcher.  Concurrent
/// lanes and an arbitrary backlog remain covered by the full timer activity
/// invariant.
pub proof fn lemma_closed_origin_flight_finish_preserves_timer_activity(
    s: S,
    flight: FlightSpec,
    done: crate::handler_docs::DoneSpec,
    firing: crate::handler_docs::FiringSpec,
    entry: crate::keys::TimerEntrySpec,
    fired: crate::types::Fired,
)
    requires
        timer_activity_consistent(s),
        flight.work is Sweep,
        flight.firing == Some(firing),
        !flight.debug,
        s.flights.slots.contains_key(
            crate::target::spec_name(flight.target),
        ),
        s.flights.slots[
            crate::target::spec_name(flight.target)
        ].queue.len() == 0,
        crate::keys::spec_parse_timer_key(firing.key)
            == Some(entry),
        firing.at >= entry.deadline(),
        s.timers.reload_pending
            || crate::handler_timers::spec_owns_entry(s, entry),
    ensures
        timer_activity_consistent(
            crate::handler_docs::spec_committed(
                s,
                flight,
                done,
                fired,
            ),
        ),
{
    let noted = crate::state::spec_note(
        s,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    lemma_send_all_preserves_timer_control(noted, done.outbox);
    let sent = crate::handler_docs::spec_send_all(
        noted,
        done.outbox,
    );
    let swept = crate::state::spec_note(
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
    );
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_emit);
    lemma_timer_activity_preserved_by_control_state(s, swept);
    let name = crate::target::spec_name(flight.target);
    let released = crate::handler_docs::spec_release(swept, name);
    reveal(crate::handler_docs::spec_release);
    reveal(crate::handler_docs::spec_without_slot);
    assert(released.timers == swept.timers);
    assert(released.node.core.members == swept.node.core.members);
    assert(released.cfg.node_id == swept.cfg.node_id);
    lemma_timer_activity_preserved_by_control_state(swept, released);
    assert(crate::handler_timers::spec_owns_entry(
        released,
        entry,
    ) == crate::handler_timers::spec_owns_entry(s, entry));
    lemma_timer_fired_preserves_activity(
        released,
        firing,
        entry,
        crate::state::spec_now(released),
        Ok(fired),
    );
    reveal(crate::handler_docs::spec_committed);
    reveal(crate::handler_docs::spec_finish);
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

/// The unchanged abstract frame for a production due submission.  Starting a
/// document load neither chooses an abstract origin timeout nor executes a
/// schedule timeout: that match is delayed until the loaded document makes
/// the internal transition identifiable.  This frame retains every existing
/// ownership, membership, lane, cache, and Store-operation requirement.
pub open spec fn due_submission_frame_related(
    production: ProcessV,
    abstract_state: AbstractStateV,
) -> bool {
    &&& production.core.out.len() == 0
    &&& pending_store_consistent(production)
    &&& owners_consistent(production.core)
    &&& membership_consistent(production.core)
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

/// The current relation.  The decomposition makes the repaired due-dispatch
/// proof obligation explicit without removing any conjunct.
pub open spec fn related(
    production: ProcessV,
    abstract_state: AbstractStateV,
) -> bool {
    &&& due_submission_frame_related(production, abstract_state)
    &&& timer_activity_consistent(production.core)
}

/// Everything a completed origin flight must retain around the one document
/// it linearizes.  The target cache entry is tied to the exact swept body;
/// every other decided document is interpreted in the pre-trace store and is
/// transferred to the post-trace store by `others_kept`.
pub open spec fn closed_origin_commit_endpoint_frame(
    production: ProcessV,
    before: AbstractStateV,
    key: Seq<char>,
    swept: echod_concrete::node::DocumentBodyV,
) -> bool {
    &&& production.core.out.len() == 0
    &&& pending_store_consistent(production)
    &&& owners_consistent(production.core)
    &&& membership_consistent(production.core)
    &&& flight_lanes_consistent(production.core.flights)
    &&& timer_activity_consistent(production.core)
    &&& before.pending.len() == 0
    &&& forall|i: int|
        0 <= i < production.core.cache.entries.len() ==> {
            let entry = #[trigger] production.core.cache.entries[i];
            let entry_key =
                logical_key(TargetSpec::Origin(entry.origin));
            if entry_key == key {
                spec_loaded_body(entry.cached.loaded) == swept
            } else {
                doc_rel(
                    entry_key,
                    spec_loaded_body(entry.cached.loaded),
                    before.store,
                )
            }
        }
    &&& forall|fid: u64|
        production.core.flights.inflight.contains_key(fid) ==> {
            let flight = production.core.flights.inflight[fid];
            match phase_after(flight.phase) {
                Some(after) => {
                    &&& logical_key(flight.target) != key
                    &&& doc_rel(
                        logical_key(flight.target),
                        spec_stored_body(after),
                        before.store,
                    )
                },
                None => true,
            }
        }
}

/// Full process relation at the successful document-write linearization
/// endpoint.  The abstract endpoint is constrained by every actual timeout
/// result in the bulk transition; the production endpoint retains all runtime,
/// ownership, membership, lane, cache, and timer invariants.
pub proof fn lemma_closed_origin_commit_endpoint_related(
    production: ProcessV,
    config: ServerConfig,
    key: Seq<char>,
    workflow: echod_concrete::document::WorkflowDocumentV,
    abstract_before: AbstractStateV,
    abstract_after: AbstractStateV,
    now: u64,
)
    requires
        key == echod_concrete::node::spec_origin_key(
            workflow.document,
        ),
        doc_rel(
            key,
            echod_concrete::node::DocumentBodyV::Workflow(
                workflow.objects,
            ),
            abstract_before.store,
        ),
        finite_store(abstract_before.store),
        echod_concrete::document::workflow_well_formed(workflow),
        workflow.committed_at <= now,
        now <= MAX_TIME,
        0 < config.retry_timeout <= MAX_TIME,
        ({
            let swept = echod_concrete::node::spec_sweep(
                echod_concrete::node::DocumentBodyV::Workflow(
                    workflow.objects,
                ),
                now,
                config.retry_timeout,
            ).0;
            &&& echod_concrete::node::spec_earliest_in(
                swept,
                now,
            ) is None
            &&& origin_bulk_transition_to(
                config,
                key,
                echod_concrete::node::DocumentBodyV::Workflow(
                    workflow.objects,
                ),
                abstract_before,
                now,
                abstract_after,
            )
            &&& closed_origin_commit_endpoint_frame(
                production,
                abstract_before,
                key,
                swept,
            )
        }),
    ensures
        ({
            let swept = echod_concrete::node::spec_sweep(
                echod_concrete::node::DocumentBodyV::Workflow(
                    workflow.objects,
                ),
                now,
                config.retry_timeout,
            ).0;
            &&& related(production, abstract_after)
            &&& well_formed(
                echod_concrete::node::spec_advance_stored(
                    StoredDocumentV::Workflow(workflow),
                    swept,
                    now,
                ),
            )
        }),
{
    let document =
        echod_concrete::node::DocumentBodyV::Workflow(workflow.objects);
    let swept = echod_concrete::node::spec_sweep(
        document,
        now,
        config.retry_timeout,
    ).0;
    lemma_bulk_sweep_preserves_well_formed(
        workflow,
        now,
        config.retry_timeout,
    );
    lemma_origin_bulk_transition_endpoint_frames(
        config,
        key,
        document,
        abstract_before,
        now,
        abstract_after,
    );
    assert(cache_related(
        production.core.cache,
        production.core.flights,
        abstract_after.store,
    )) by {
        assert forall|i: int|
            0 <= i < production.core.cache.entries.len()
            implies {
                let entry =
                    #[trigger] production.core.cache.entries[i];
                let target = TargetSpec::Origin(entry.origin);
                !(
                    exists|fid: u64|
                        production.core.flights.inflight
                            .contains_key(fid)
                            && production.core.flights.inflight[fid]
                                .target == target
                            && phase_after(
                                production.core.flights.inflight[fid]
                                    .phase,
                            ) is Some
                ) ==> doc_rel(
                    logical_key(target),
                    spec_loaded_body(entry.cached.loaded),
                    abstract_after.store,
                )
            } by {
            let entry = production.core.cache.entries[i];
            let entry_key =
                logical_key(TargetSpec::Origin(entry.origin));
            if entry_key == key {
                assert(spec_loaded_body(entry.cached.loaded) == swept);
            } else {
                assert(echod_concrete::interpret::others_kept(
                    key,
                    abstract_before.store,
                    abstract_after.store,
                ));
            }
        }
    }
    assert(flights_related(
        production.core.flights,
        abstract_after.store,
    )) by {
        assert forall|fid: u64|
            production.core.flights.inflight.contains_key(fid)
            implies {
                let flight =
                    production.core.flights.inflight[fid];
                match phase_after(flight.phase) {
                    Some(after) => doc_rel(
                        logical_key(flight.target),
                        spec_stored_body(after),
                        abstract_after.store,
                    ),
                    None => true,
                }
            } by {
            let flight = production.core.flights.inflight[fid];
            match phase_after(flight.phase) {
                Some(after) => {
                    assert(echod_concrete::interpret::others_kept(
                        key,
                        abstract_before.store,
                        abstract_after.store,
                    ));
                },
                None => {},
            }
        }
    }
    assert(abstract_after.pending.len() == 0);
}

pub proof fn lemma_due_submission_frame_closes_related(
    production: ProcessV,
    abstract_state: AbstractStateV,
)
    requires
        due_submission_frame_related(production, abstract_state),
        timer_activity_consistent(production.core),
    ensures
        related(production, abstract_state),
{
}

/// Conversely, a genuine production-side timer-activity violation cannot be
/// hidden by choosing a different abstract state.
pub proof fn lemma_failed_timer_activity_has_no_abstract_match(
    production: ProcessV,
    abstract_state: AbstractStateV,
)
    requires
        !timer_activity_consistent(production.core),
    ensures
        !related(production, abstract_state),
{
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
            );
            let (_, _, _, notes) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(document),
                    request,
                    now,
                    retry_timeout,
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
            );
            let logical_after = on_request(
                before,
                request,
                now,
                retry_timeout,
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
    );
    let swept = echod_concrete::node::spec_sweep(
        original,
        now,
        retry_timeout,
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
        );
        let closed = echod_concrete::node::spec_sweep(
            handled,
            now,
            retry_timeout,
        ).0;
        assert(closed is Workflow);
    }
    let (body, response, _, _) = spec_request_transition(
        spec_stored_body(before),
        request,
        now,
        retry_timeout,
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
            );
            let logical_after = on_request(
                w.loaded.document,
                request,
                now,
                s.cfg.retry_timeout,
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
    );
    let logical_after = on_request(
        before,
        request,
        now,
        s.cfg.retry_timeout,
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
            ).3;
            let candidate = on_request(
                w.loaded.document,
                request,
                now,
                s.cfg.retry_timeout,
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
    ).3;
    let candidate = on_request(
        w.loaded.document,
        request,
        now,
        s.cfg.retry_timeout,
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
    ).3);
    assert(spec_stored_body(candidate)
        == spec_request_transition(
            spec_stored_body(w.loaded.document),
            request,
            now,
            s.cfg.retry_timeout,
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
            ).3;
            let candidate = on_request(
                w.loaded.document,
                request,
                now,
                loaded.cfg.retry_timeout,
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
            ).3;
            let candidate = on_request(
                w.loaded.document,
                request,
                now,
                loaded.cfg.retry_timeout,
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
            );
            let (_, _, _, notes) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(document),
                    request,
                    now,
                    config.retry_timeout,
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
