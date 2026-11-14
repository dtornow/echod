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
//! * a quiet empty-heartbeat core step emits exactly its successful reply;
//! * a quiet cache-miss origin request starts one real loading flight and Get;
//! * a normal atomic request preserves the stored-document invariant and its
//!   Reply/Send effects are exactly the endpoint delta.
//!
//! The last theorem intentionally reuses the two document theorems on which a
//! full process simulation must rest:
//! `quick_n_dirty::request_preserves_well_formed` and
//! `effects::lemma_request_transition_effects`.
//!
//! Bounded normal-origin theorems also cover a racing CAS reload/redecision,
//! unavailable and wrong-shaped write responses, and stale responses.
//! Detached two-document requests, whole-system concurrent-flight simulation,
//! membership refresh, and timer/fire steps remain classified by
//! [`open_case`] without a global refinement theorem.
//! There are no admits or axioms in this module.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::cache::CacheSpec;
#[cfg(verus_keep_ghost)]
use crate::config::ConfigSpec;
#[cfg(verus_keep_ghost)]
use crate::document::{spec_decode_workflow, spec_encode, spec_loaded_body, LoadedSpec};
#[cfg(verus_keep_ghost)]
use crate::handler::{spec_on_event, spec_request, spec_schedule_wake};
#[cfg(verus_keep_ghost)]
use crate::handler_docs::{
    spec_answered, spec_answered_loading, spec_answered_origin,
    spec_answered_phase, spec_begin, spec_commit_advance, spec_commit_new,
    spec_commit_failed, spec_committed, spec_decide, spec_fail, spec_finish, spec_flight_completed,
    spec_inflight, spec_issue_write, spec_load_origin, spec_loaded_origin,
    spec_release, spec_retry, spec_run_origin, spec_send_all, spec_slot_of, spec_start,
    spec_submit, CommittingSpec, FlightSpec, FlightsSpec, IssuedSpec,
    PhaseSpec, ProgressSpec, WorkSpec,
};
#[cfg(verus_keep_ghost)]
use crate::keys::spec_doc_key;
#[cfg(verus_keep_ghost)]
use crate::state::{
    spec_emit, spec_note, spec_state_new, spec_store, Owner, S,
};
#[cfg(verus_keep_ghost)]
use crate::state_timers::{spec_slot_before, TimersSpec};
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;
#[cfg(verus_keep_ghost)]
use crate::types::{
    AnswerSpec, Armed, CacheResult, CallSpec, EffectSpec, EventSpec,
    Fired, MessageSpec, NoteSpec, OpId, RequestEventSpec,
    spec_error_text, spec_unexpected,
};
#[cfg(verus_keep_ghost)]
use crate::verified::commit_spec::spec_to_disarm;
#[cfg(verus_keep_ghost)]
use crate::verified::flight_spec::{
    answer_v, spec_advance, AAnswer, AAct, AOutcome, AStep,
};
#[cfg(verus_keep_ghost)]
use crate::verified::node::AKey;
#[cfg(verus_keep_ghost)]
use crate::verified::node_spec::spec_forget;

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
use echod_concrete::node::{
    spec_advance_stored, spec_body_deadline, spec_request_transition,
    spec_stored_body, spec_unavailable, REQUEST_SWEEP_STEPS,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::quick_n_dirty::{on_request, request_preserves_well_formed, routed};
#[cfg(verus_keep_ghost)]
use echod_concrete::store::{
    Etag, StoreError, StoreErrorSpec, StoreReqSpec, StoreRes,
};
#[cfg(verus_keep_ghost)]
use echod_types::{Request, Response, StatusRes, MAX_TIME};

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

pub open spec fn outbound_send_effects(
    outbox: Seq<(Seq<char>, MessageSpec)>,
) -> Seq<EffectSpec>
    decreases outbox.len(),
{
    if outbox.len() == 0 {
        Seq::empty()
    } else {
        seq![EffectSpec::Send {
            address: outbox[0].0,
            message: outbox[0].1,
        }] + outbound_send_effects(outbox.drop_first())
    }
}

pub open spec fn no_reply_effects(effects: Seq<EffectSpec>) -> bool
    decreases effects.len(),
{
    if effects.len() == 0 {
        true
    } else {
        !(effects.last() is Reply)
            && no_reply_effects(effects.drop_last())
    }
}

pub proof fn lemma_no_reply_effects_drop_last(
    effects: Seq<EffectSpec>,
)
    requires
        no_reply_effects(effects),
        effects.len() > 0,
    ensures
        no_reply_effects(effects.drop_last()),
        !(effects.last() is Reply),
    decreases effects.len(),
{
    reveal_with_fuel(no_reply_effects, 2);
}

proof fn lemma_no_reply_effects_push(
    effects: Seq<EffectSpec>,
    effect: EffectSpec,
)
    requires
        no_reply_effects(effects),
        !(effect is Reply),
    ensures
        no_reply_effects(effects.push(effect)),
{
    assert(effects.push(effect).len() > 0);
    assert(effects.push(effect).last() == effect);
    assert(effects.push(effect).drop_last() =~= effects);
    reveal_with_fuel(no_reply_effects, 2);
}

proof fn lemma_no_reply_effects_concat(
    left: Seq<EffectSpec>,
    right: Seq<EffectSpec>,
)
    requires
        no_reply_effects(left),
        no_reply_effects(right),
    ensures
        no_reply_effects(left + right),
    decreases right.len(),
{
    reveal_with_fuel(no_reply_effects, 2);
    if right.len() == 0 {
        assert(right =~= Seq::<EffectSpec>::empty());
    } else {
        lemma_no_reply_effects_concat(
            left,
            right.drop_last(),
        );
        assert((left + right).drop_last()
            =~= left + right.drop_last());
        assert((left + right).last() == right.last());
    }
}

proof fn lemma_outbound_send_effects_no_reply(
    outbox: Seq<(Seq<char>, MessageSpec)>,
)
    ensures
        no_reply_effects(outbound_send_effects(outbox)),
    decreases outbox.len(),
{
    reveal_with_fuel(no_reply_effects, 2);
    if outbox.len() > 0 {
        lemma_outbound_send_effects_no_reply(outbox.drop_first());
        assert(no_reply_effects(seq![EffectSpec::Send {
            address: outbox[0].0,
            message: outbox[0].1,
        }]));
        lemma_no_reply_effects_concat(
            seq![EffectSpec::Send {
                address: outbox[0].0,
                message: outbox[0].1,
            }],
            outbound_send_effects(outbox.drop_first()),
        );
    }
}

proof fn lemma_answered_write_success_no_reply(
    s: S,
    c: CommittingSpec,
    issued: IssuedSpec,
    written_etag: Etag,
)
    requires
        no_reply_effects(s.out),
        issued is Write,
    ensures
        no_reply_effects(spec_answered(
            s,
            c,
            issued,
            Some(StoreRes::PutIfMatch {
                result: Ok(written_etag),
            }),
        ).0.out),
{
    reveal(spec_answered);
    reveal(crate::state::spec_remember);
    let note = EffectSpec::Note(NoteSpec::DocumentWrite {
        mode: issued->Write_mode,
        bytes: issued->Write_len,
    });
    lemma_no_reply_effects_push(s.out, note);
}

proof fn lemma_answered_key_delete_success_no_reply(
    s: S,
    c: CommittingSpec,
    issued: IssuedSpec,
)
    requires
        no_reply_effects(s.out),
        issued is Key,
    ensures
        no_reply_effects(spec_answered(
            s,
            c,
            issued,
            Some(StoreRes::Del { result: Ok(()) }),
        ).0.out),
{
    reveal(spec_answered);
}

proof fn lemma_send_all_frame(
    s: S,
    outbox: Seq<(Seq<char>, MessageSpec)>,
)
    ensures
        spec_send_all(s, outbox) == (S {
            out: s.out + outbound_send_effects(outbox),
            ..s
        }),
    decreases outbox.len(),
{
    if outbox.len() == 0 {
        assert(s.out + Seq::<EffectSpec>::empty() =~= s.out);
    } else {
        let first = EffectSpec::Send {
            address: outbox[0].0,
            message: outbox[0].1,
        };
        lemma_send_all_frame(
            spec_emit(s, first),
            outbox.drop_first(),
        );
        assert(s.out.push(first)
            + outbound_send_effects(outbox.drop_first())
            =~= s.out + outbound_send_effects(outbox));
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
// Bounded production request steps
// ---------------------------------------------------------------------------

/// No background membership or wake work can be inserted around a request.
///
/// This is an exact production-state precondition, not an alternate
/// transition relation. A refresh in progress suppresses the implicit
/// membership tick, and `loops == false` makes `spec_schedule_wake` a no-op.
pub open spec fn quiet_request_ready(s: S) -> bool {
    &&& s.out.len() == 0
    &&& s.node.members.refresh is Some
    &&& !s.loops
}

/// Under a quiet production state, the real `State::on_event` transition for
/// an empty task heartbeat changes only the observed clock and emits exactly
/// the successful reply.
pub proof fn lemma_empty_heartbeat_core_step(
    s: S,
    clock: u64,
    id: u64,
    kind: Seq<char>,
    corr: Seq<char>,
    action_kind: Option<Seq<char>>,
)
    requires
        quiet_request_ready(s),
    ensures
        spec_on_event(
            s,
            EventSpec::Request {
                clock,
                request: RequestEventSpec::EmptyHeartbeat {
                    id,
                    kind,
                    corr,
                    action_kind,
                },
            },
        ) == (
            S {
                clock,
                out: Seq::empty(),
                ..s
            },
            seq![EffectSpec::Reply {
                id,
                response: Ok(AnswerSpec::Step {
                    kind,
                    corr,
                    action_kind,
                    response: Response::Status(StatusRes { status: 200 }),
                    why: None,
                }),
            }],
        ),
{
    reveal(spec_on_event);
    reveal(spec_schedule_wake);
    assert(s.node.members.refreshing());
    assert(s.out =~= Seq::<EffectSpec>::empty());
}

/// Exact preconditions for the first, cache-miss step of one ordinary origin
/// request. Fresh operation/flight ids and an absent slot prevent this slice
/// from silently overwriting concurrent production work.
pub open spec fn normal_origin_request_ready(
    s: S,
    origin: Seq<char>,
) -> bool {
    let name = crate::target::spec_name(TargetSpec::Origin(origin));
    &&& quiet_request_ready(s)
    &&& !s.ops.contains_key(s.next_op)
    &&& !s.flights.inflight.contains_key(s.next_flight)
    &&& !s.flights.slots.contains_key(name)
    &&& crate::cache::spec_get(s.cache, origin).1 is None
    &&& spec_doc_key(s.keys.prefix, origin).len() <= usize::MAX as int
}

/// The first real production transition for a normal origin request starts a
/// flight and issues the document Get. The load response and commit sequence
/// are deliberately outside this one-step slice.
pub proof fn lemma_normal_origin_request_starts_load(
    s: S,
    call: CallSpec,
    origin: Seq<char>,
    clock: u64,
)
    requires
        call.target == TargetSpec::Origin(origin),
        normal_origin_request_ready(s, origin),
    ensures
        ({
            let event = EventSpec::Request {
                clock,
                request: RequestEventSpec::Protocol(call),
            };
            let (next, effects) = spec_on_event(s, event);
            let op = s.next_op;
            let fid = s.next_flight;
            let request_now =
                if call.pinned || call.now > s.node.fleet_at {
                    call.now
                } else {
                    s.node.fleet_at
                };
            let work = WorkSpec::Request {
                id: call.id,
                kind: call.kind,
                corr: call.corr,
                req: call.request,
                action_kind: call.action_kind,
                now: request_now,
            };
            &&& effects == seq![
                EffectSpec::Note(NoteSpec::Cache(CacheResult::Miss)),
                EffectSpec::Store {
                    op,
                    request: StoreReqSpec::Get {
                        key: spec_doc_key(s.keys.prefix, origin),
                    },
                },
            ]
            &&& next.out.len() == 0
            &&& next.ops.contains_key(op)
            &&& next.ops[op] == Owner::Flight(fid)
            &&& next.flights.inflight.contains_key(fid)
            &&& next.flights.inflight[fid].target
                == TargetSpec::Origin(origin)
            &&& next.flights.inflight[fid].work == work
            &&& next.flights.inflight[fid].phase
                == PhaseSpec::Loading {
                    op,
                    revalidating: None,
                }
            &&& spec_slot_of(
                next,
                crate::target::spec_name(TargetSpec::Origin(origin)),
            ).busy == Some(fid)
        }),
{
    reveal(spec_on_event);
    reveal(spec_request);
    reveal(spec_submit);
    reveal(spec_start);
    reveal(spec_begin);
    reveal(spec_load_origin);
    reveal(spec_schedule_wake);
    assert(s.node.members.refreshing());
    assert(s.out =~= Seq::<EffectSpec>::empty());
    assert(spec_slot_of(
        s,
        crate::target::spec_name(TargetSpec::Origin(origin)),
    ).busy is None);
}

/// Exact preconditions under which the successful cache-miss Get continuation
/// decodes a workflow, decides a changing request, and can issue its document
/// CAS immediately (there is no deadline key to arm first).
pub open spec fn normal_origin_get_write_ready(
    s: S,
    call: CallSpec,
    origin: Seq<char>,
    at: u64,
    loaded: LoadedSpec,
    etag: Etag,
) -> bool {
    let (after_body, response, _, _) = spec_request_transition(
        spec_stored_body(loaded.document),
        call.request,
        at,
        s.cfg.retry_timeout,
        REQUEST_SWEEP_STEPS as nat,
    );
    let after_document =
        spec_advance_stored(loaded.document, after_body, at);
    &&& call.target == TargetSpec::Origin(origin)
    &&& !call.pinned
    &&& call.now == at
    &&& s.node.fleet_at <= at
    &&& normal_origin_request_ready(s, origin)
    &&& s.next_op < u64::MAX
    &&& !s.ops.contains_key(s.next_op.wrapping_add(1))
    &&& !s.ops.contains_key(s.next_op.wrapping_add(2))
    &&& !s.cfg.appendable
    &&& well_formed(loaded.document)
    &&& routed(loaded.document, call.request)
    &&& echod_concrete::node::spec_stored_committed_at(
        loaded.document,
    ) <= at
    &&& at <= MAX_TIME
    &&& 0 < s.cfg.retry_timeout <= MAX_TIME
    &&& safe_effect_config(at, s.cfg.retry_timeout)
    &&& document_ids_bounded(loaded.document)
    &&& response != spec_unavailable(call.request)
    &&& after_body != spec_stored_body(loaded.document)
    &&& spec_body_deadline(after_body) is None
    &&& spec_encode(after_document).len() <= usize::MAX as int
    &&& etag.0@.len() <= usize::MAX as int
}

/// The production `State::on_event` continuation for a decoded successful
/// Get. Under [`normal_origin_get_write_ready`] it emits exactly one
/// `PutIfMatch` owned by the same flight and preserves `well_formed` for the
/// document selected for that write.
#[verifier::rlimit(30)]
pub proof fn lemma_normal_origin_successful_get_issues_put_if_match(
    s: S,
    call: CallSpec,
    origin: Seq<char>,
    at: u64,
    response_at: u64,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
)
    requires
        at <= response_at,
        spec_decode_workflow(bytes@) == Ok(loaded),
        normal_origin_get_write_ready(
            s,
            call,
            origin,
            at,
            loaded,
            etag,
        ),
    ensures
        ({
            let request_event = EventSpec::Request {
                clock: at,
                request: RequestEventSpec::Protocol(call),
            };
            let admitted = spec_on_event(s, request_event).0;
            let get_response = StoreRes::Get {
                result: Ok(Some((bytes, etag))),
            };
            let store_event = EventSpec::Store {
                op: s.next_op,
                response: get_response,
                clock: response_at,
            };
            let (next, effects) = spec_on_event(admitted, store_event);
            let (after_body, response, _, _) = spec_request_transition(
                spec_stored_body(loaded.document),
                call.request,
                at,
                s.cfg.retry_timeout,
                REQUEST_SWEEP_STEPS as nat,
            );
            let after_document =
                spec_advance_stored(loaded.document, after_body, at);
            let write_op = s.next_op.wrapping_add(1);
            let fid = s.next_flight;
            let write = StoreReqSpec::PutIfMatch {
                key: spec_doc_key(s.keys.prefix, origin),
                body: spec_encode(after_document),
                etag: etag.deep_view(),
            };
            &&& effects == seq![EffectSpec::Store {
                op: write_op,
                request: write,
            }]
            &&& next.out.len() == 0
            &&& !next.loops
            &&& next.node.members.refreshing()
            &&& next.next_op == s.next_op.wrapping_add(2)
            &&& !next.ops.contains_key(next.next_op)
            &&& next.ops.contains_key(write_op)
            &&& next.ops[write_op] == Owner::Flight(fid)
            &&& next.flights.inflight.contains_key(fid)
            &&& next.flights.inflight[fid].target
                == TargetSpec::Origin(origin)
            &&& next.flights.inflight[fid].id == fid
            &&& next.flights.inflight[fid].work is Request
            &&& next.flights.inflight[fid].work->Request_id == call.id
            &&& next.flights.inflight[fid].work->Request_kind == call.kind
            &&& next.flights.inflight[fid].work->Request_corr == call.corr
            &&& next.flights.inflight[fid].work->Request_action_kind
                == call.action_kind
            &&& next.flights.inflight[fid].firing is None
            &&& !next.flights.inflight[fid].debug
            &&& next.flights.inflight[fid].phase is Origin
            &&& next.flights.inflight[fid].phase->Origin_done.response
                == Some(response)
            &&& next.flights.inflight[fid].phase->Origin_commit.seq.step
                == (AStep::Writing { idle: false })
            &&& next.flights.inflight[
                fid
            ].phase->Origin_commit.seq.changed
            &&& next.flights.inflight[
                fid
            ].phase->Origin_commit.seq.fired is None
            &&& next.flights.inflight[fid].phase->Origin_commit.after
                == after_document
            &&& next.flights.inflight[fid].phase->Origin_commit.issued
                == Some(IssuedSpec::Write {
                    op: write_op,
                    mode: crate::types::WriteMode::Rewrite,
                    change_count:
                        echod_concrete::node::spec_body_len(after_body)
                            as usize,
                    bytes: spec_encode(after_document).len() as u64,
                    len: spec_encode(after_document).len() as usize,
                })
            &&& next.flights.slots.contains_key(
                crate::target::spec_name(TargetSpec::Origin(origin)),
            )
            &&& next.flights.slots[
                crate::target::spec_name(TargetSpec::Origin(origin))
            ].busy == Some(fid)
            &&& next.flights.slots[
                crate::target::spec_name(TargetSpec::Origin(origin))
            ].queue.len() == 0
            &&& well_formed(after_document)
        }),
{
    lemma_normal_origin_request_starts_load(s, call, origin, at);
    lemma_normal_request_happy_path(
        loaded.document,
        call.request,
        at,
        s.cfg.retry_timeout,
    );
    reveal(spec_on_event);
    reveal(spec_request);
    reveal(spec_submit);
    reveal(spec_start);
    reveal(spec_begin);
    reveal(spec_load_origin);
    reveal(spec_flight_completed);
    reveal(spec_answered_phase);
    reveal(spec_answered_loading);
    reveal(spec_loaded_origin);
    reveal(spec_run_origin);
    reveal(spec_decide);
    reveal(spec_commit_new);
    reveal(spec_commit_advance);
    reveal(spec_issue_write);
    reveal(spec_schedule_wake);
    reveal(echod_concrete::quick_n_dirty::on_request);
    reveal(crate::verified::flight_spec::spec_advance);
    reveal(crate::verified::commit_spec::spec_prepare);
    assert(s.node.members.refreshing());
}

pub open spec fn normal_origin_write_issued_state(
    s: S,
    call: CallSpec,
    origin: Seq<char>,
    at: u64,
    get_response_at: u64,
    bytes: Vec<u8>,
    etag: Etag,
) -> S {
    let admitted = spec_on_event(
        s,
        EventSpec::Request {
            clock: at,
            request: RequestEventSpec::Protocol(call),
        },
    ).0;
    spec_on_event(
        admitted,
        EventSpec::Store {
            op: s.next_op,
            response: StoreRes::Get {
                result: Ok(Some((bytes, etag))),
            },
            clock: get_response_at,
        },
    ).0
}

pub open spec fn normal_origin_write_commit(
    s: S,
    call: CallSpec,
    origin: Seq<char>,
    at: u64,
    get_response_at: u64,
    bytes: Vec<u8>,
    etag: Etag,
) -> CommittingSpec {
    normal_origin_write_issued_state(
        s,
        call,
        origin,
        at,
        get_response_at,
        bytes,
        etag,
    ).flights.inflight[s.next_flight].phase->Origin_commit
}

/// The exact deadline-key branch selected after a successful document CAS.
/// `None` completes directly; `Some(key)` must issue and await deletion of
/// that previously armed key before the request can reply.
pub open spec fn normal_origin_previous_deadline_key(
    s: S,
    call: CallSpec,
    origin: Seq<char>,
    at: u64,
    get_response_at: u64,
    bytes: Vec<u8>,
    etag: Etag,
) -> Option<AKey> {
    spec_to_disarm(normal_origin_write_commit(
        s,
        call,
        origin,
        at,
        get_response_at,
        bytes,
        etag,
    ).seq.plan)
}

pub open spec fn normal_request_reply_effect(
    flight: FlightSpec,
    done: crate::handler_docs::DoneSpec,
) -> EffectSpec {
    let response = match done.response {
        Some(response) => Ok(AnswerSpec::Step {
            kind: flight.work->Request_kind,
            corr: flight.work->Request_corr,
            action_kind: flight.work->Request_action_kind,
            response,
            why: done.why,
        }),
        None => Err("no answer"@),
    };
    EffectSpec::Reply {
        id: flight.work->Request_id,
        response,
    }
}

/// A successful document write completes directly when the exact production
/// commit waiting on it has no previous deadline key to disarm.
#[verifier::rlimit(20)]
pub proof fn lemma_successful_origin_write_completes_directly(
    s: S,
    fid: u64,
    op: u64,
    response_at: u64,
    written_etag: Etag,
)
    requires
        s.out.len() == 0,
        s.node.members.refreshing(),
        !s.loops,
        s.ops.contains_key(op),
        s.ops[op] == Owner::Flight(fid),
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid].id == fid,
        s.flights.inflight[fid].work is Request,
        s.flights.inflight[fid].firing is None,
        !s.flights.inflight[fid].debug,
        s.flights.inflight[fid].phase is Origin,
        s.flights.inflight[fid].phase.expects() == Some(op),
        s.flights.inflight[fid].phase->Origin_commit.seq.step
            == (AStep::Writing { idle: false }),
        s.flights.inflight[fid].phase->Origin_commit.seq.changed,
        s.flights.inflight[fid].phase->Origin_commit.seq.fired is None,
        s.flights.slots.contains_key(crate::target::spec_name(
            s.flights.inflight[fid].target,
        )),
        s.flights.slots[crate::target::spec_name(
            s.flights.inflight[fid].target,
        )].busy == Some(fid),
        s.flights.slots[crate::target::spec_name(
            s.flights.inflight[fid].target,
        )].queue.len() == 0,
        s.flights.inflight[fid].phase->Origin_commit.issued
            is Some,
        s.flights.inflight[fid].phase->Origin_commit.issued->Some_0
            is Write,
        s.flights.inflight[fid].phase->Origin_commit.issued->Some_0
            ->Write_op == op,
        spec_to_disarm(
            s.flights.inflight[fid].phase->Origin_commit.seq.plan,
        ) is None,
    ensures
        ({
            let (next, effects) = spec_on_event(
                s,
                EventSpec::Store {
                    op,
                    response: StoreRes::PutIfMatch {
                        result: Ok(written_etag),
                    },
                    clock: response_at,
                },
            );
            &&& !next.ops.contains_key(op)
            &&& !next.flights.inflight.contains_key(fid)
            &&& effects.len() > 0
            &&& effects.last() == normal_request_reply_effect(
                s.flights.inflight[fid],
                s.flights.inflight[fid].phase->Origin_done,
            )
            &&& no_reply_effects(effects.drop_last())
        }),
{
    reveal(spec_on_event);
    reveal(spec_flight_completed);
    reveal(spec_answered_phase);
    reveal(spec_answered_origin);
    reveal(spec_commit_advance);
    reveal(spec_answered);
    reveal(spec_committed);
    reveal(spec_send_all);
    reveal(spec_finish);
    reveal(spec_release);
    reveal(spec_schedule_wake);
    reveal(spec_advance);
    let clocked = S { clock: response_at, ..s };
    assert(clocked.node.members.refreshing());
    assert(!(clocked.node.members.next_heartbeat is None
        && !clocked.node.members.refreshing()));
    let without_op = S {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    assert(spec_flight_completed(
        without_op,
        fid,
        op,
        StoreRes::PutIfMatch { result: Ok(written_etag) },
    ) == spec_answered_phase(
        crate::handler_docs::spec_take_flight(without_op, fid),
        fid,
        FlightSpec {
            phase: PhaseSpec::Idle,
            ..s.flights.inflight[fid]
        },
        s.flights.inflight[fid].phase,
        StoreRes::PutIfMatch { result: Ok(written_etag) },
    ));
    let commit = s.flights.inflight[fid].phase->Origin_commit;
    let (advanced, core, outcome) = spec_advance(
        commit.seq,
        without_op.node.core,
        AAnswer::Written(written_etag.0@),
    );
    assert(outcome == AOutcome::Act(AAct::Done { deleted: false }));
    let taken = crate::handler_docs::spec_take_flight(
        without_op,
        fid,
    );
    assert(no_reply_effects(taken.out));
    lemma_answered_write_success_no_reply(
        taken,
        CommittingSpec { issued: None, ..commit },
        commit.issued->Some_0,
        written_etag,
    );
    let (answered, commit2, progress) = spec_commit_advance(
        taken,
        fid,
        commit,
        Some(StoreRes::PutIfMatch {
            result: Ok(written_etag),
        }),
    );
    assert(progress == ProgressSpec::Done(Fired::Kept));
    let flight0 = FlightSpec {
        phase: PhaseSpec::Idle,
        ..s.flights.inflight[fid]
    };
    assert(spec_answered_origin(
        taken,
        fid,
        flight0,
        commit,
        s.flights.inflight[fid].phase->Origin_done,
        StoreRes::PutIfMatch { result: Ok(written_etag) },
    ) == spec_committed(
        answered,
        flight0,
        s.flights.inflight[fid].phase->Origin_done,
        Fired::Kept,
    ));
    let committed = spec_committed(
        answered,
        flight0,
        s.flights.inflight[fid].phase->Origin_done,
        Fired::Kept,
    );
    let done = s.flights.inflight[fid].phase->Origin_done;
    let response = match done.response {
        Some(response) => Ok(AnswerSpec::Step {
            kind: s.flights.inflight[fid].work->Request_kind,
            corr: s.flights.inflight[fid].work->Request_corr,
            action_kind:
                s.flights.inflight[fid].work->Request_action_kind,
            response,
            why: done.why,
        }),
        None => Err("no answer"@),
    };
    let noted = spec_note(
        answered,
        NoteSpec::Commit(crate::types::CommitOutcome::Committed),
    );
    let sent = spec_send_all(noted, done.outbox);
    lemma_send_all_frame(noted, done.outbox);
    assert(no_reply_effects(answered.out));
    lemma_no_reply_effects_push(
        answered.out,
        EffectSpec::Note(NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        )),
    );
    assert(no_reply_effects(noted.out));
    lemma_outbound_send_effects_no_reply(done.outbox);
    lemma_no_reply_effects_concat(
        noted.out,
        outbound_send_effects(done.outbox),
    );
    assert(no_reply_effects(sent.out));
    let replied = spec_emit(sent, EffectSpec::Reply {
        id: s.flights.inflight[fid].work->Request_id,
        response,
    });
    assert(replied.out.last() is Reply);
    assert(replied.out.last()->Reply_id
        == s.flights.inflight[fid].work->Request_id);
    assert(replied.out.last() == normal_request_reply_effect(
        s.flights.inflight[fid],
        done,
    ));
    assert(replied.out.drop_last() == sent.out);
    assert(committed == spec_finish(
        replied,
        FlightSpec { idle: !done.did, ..flight0 },
        Ok(Fired::Kept),
    ));
    assert(answered.ops == taken.ops);
    assert(taken.ops == without_op.ops);
    assert(replied.ops == without_op.ops);
    assert(replied.flights.inflight == taken.flights.inflight);
    assert(!committed.ops.contains_key(op));
    assert(!committed.flights.inflight.contains_key(fid));
    assert(committed.out.len() > 0);
    assert(committed.out.last() is Reply);
    assert(committed.out.last()->Reply_id
        == s.flights.inflight[fid].work->Request_id);
    assert(committed.out.last() == normal_request_reply_effect(
        s.flights.inflight[fid],
        done,
    ));
    let (next, effects) = spec_on_event(
        s,
        EventSpec::Store {
            op,
            response: StoreRes::PutIfMatch {
                result: Ok(written_etag),
            },
            clock: response_at,
        },
    );
    assert(!next.ops.contains_key(op));
    assert(!next.flights.inflight.contains_key(fid));
    assert(effects.len() > 0);
    assert(effects.last() is Reply);
    assert(effects.last()->Reply_id
        == s.flights.inflight[fid].work->Request_id);
    assert(effects.last() == normal_request_reply_effect(
        s.flights.inflight[fid],
        done,
    ));
    assert(no_reply_effects(effects.drop_last()));
}

/// The other successful-write branch emits the exact delete for the
/// production commit's previous deadline key.
#[verifier::rlimit(20)]
pub proof fn lemma_successful_origin_write_issues_previous_key_delete(
    s: S,
    fid: u64,
    op: u64,
    response_at: u64,
    written_etag: Etag,
    previous: AKey,
)
    requires
        s.out.len() == 0,
        s.node.members.refreshing(),
        !s.loops,
        !s.ops.contains_key(s.next_op),
        s.ops.contains_key(op),
        s.ops[op] == Owner::Flight(fid),
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid].id == fid,
        s.flights.inflight[fid].work is Request,
        s.flights.inflight[fid].firing is None,
        !s.flights.inflight[fid].debug,
        s.flights.inflight[fid].phase is Origin,
        s.flights.inflight[fid].phase.expects() == Some(op),
        s.flights.inflight[fid].phase->Origin_commit.seq.step
            == (AStep::Writing { idle: false }),
        s.flights.inflight[fid].phase->Origin_commit.seq.changed,
        s.flights.inflight[fid].phase->Origin_commit.seq.fired is None,
        s.flights.inflight[fid].phase->Origin_commit.issued
            is Some,
        s.flights.inflight[fid].phase->Origin_commit.issued->Some_0
            is Write,
        s.flights.inflight[fid].phase->Origin_commit.issued->Some_0
            ->Write_op == op,
        spec_to_disarm(
            s.flights.inflight[fid].phase->Origin_commit.seq.plan,
        ) == Some(previous),
        s.flights.slots.contains_key(crate::target::spec_name(
            s.flights.inflight[fid].target,
        )),
        s.flights.slots[crate::target::spec_name(
            s.flights.inflight[fid].target,
        )].busy == Some(fid),
        s.flights.slots[crate::target::spec_name(
            s.flights.inflight[fid].target,
        )].queue.len() == 0,
    ensures
        ({
            let (next, effects) = spec_on_event(
                s,
                EventSpec::Store {
                    op,
                    response: StoreRes::PutIfMatch {
                        result: Ok(written_etag),
                    },
                    clock: response_at,
                },
            );
            let delete_name = next.flights.inflight[
                fid
            ].phase->Origin_commit.issued->Some_0->Key_name;
            &&& effects.len() > 0
            &&& effects.last() == EffectSpec::Store {
                op: s.next_op,
                request: StoreReqSpec::Del { key: delete_name },
            }
            &&& no_reply_effects(effects)
            &&& next.out.len() == 0
            &&& next.node.members.refreshing()
            &&& !next.loops
            &&& next.ops.contains_key(s.next_op)
            &&& next.ops[s.next_op] == Owner::Flight(fid)
            &&& next.flights.inflight.contains_key(fid)
            &&& next.flights.inflight[fid].id == fid
            &&& next.flights.inflight[fid].work
                == s.flights.inflight[fid].work
            &&& next.flights.inflight[fid].work is Request
            &&& next.flights.inflight[fid].firing is None
            &&& !next.flights.inflight[fid].debug
            &&& next.flights.inflight[fid].phase is Origin
            &&& next.flights.inflight[fid].phase->Origin_done
                == s.flights.inflight[fid].phase->Origin_done
            &&& next.flights.inflight[
                fid
            ].phase->Origin_commit.seq.step
                == AStep::DeletingPrevious(previous)
            &&& next.flights.inflight[
                fid
            ].phase->Origin_commit.seq.fired is None
            &&& next.flights.inflight[
                fid
            ].phase->Origin_commit.issued == Some(IssuedSpec::Key {
                op: s.next_op,
                key: previous,
                name: delete_name,
                arm: false,
            })
            &&& next.flights.slots.contains_key(crate::target::spec_name(
                next.flights.inflight[fid].target,
            ))
            &&& next.flights.slots[crate::target::spec_name(
                next.flights.inflight[fid].target,
            )].busy == Some(fid)
            &&& next.flights.slots[crate::target::spec_name(
                next.flights.inflight[fid].target,
            )].queue.len() == 0
        }),
{
    reveal(spec_on_event);
    reveal(spec_flight_completed);
    reveal(spec_answered_phase);
    reveal(spec_answered_origin);
    reveal(spec_commit_advance);
    reveal(spec_answered);
    reveal(spec_inflight);
    reveal(spec_store);
    reveal(spec_schedule_wake);
    reveal(spec_advance);
    let clocked = S { clock: response_at, ..s };
    assert(clocked.node.members.refreshing());
    let without_op = S {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    let taken = crate::handler_docs::spec_take_flight(
        without_op,
        fid,
    );
    let commit = s.flights.inflight[fid].phase->Origin_commit;
    assert(no_reply_effects(taken.out));
    lemma_answered_write_success_no_reply(
        taken,
        CommittingSpec { issued: None, ..commit },
        commit.issued->Some_0,
        written_etag,
    );
    let (advanced, core, outcome) = spec_advance(
        commit.seq,
        without_op.node.core,
        AAnswer::Written(written_etag.0@),
    );
    assert(outcome == AOutcome::Act(AAct::DeleteKey {
        key: previous,
        by: without_op.node.core.id,
    }));
    let (after_answer, commit2, progress) = spec_commit_advance(
        taken,
        fid,
        commit,
        Some(StoreRes::PutIfMatch {
            result: Ok(written_etag),
        }),
    );
    assert(progress == ProgressSpec::Issued);
    assert(commit2.issued is Some);
    assert(commit2.issued->Some_0 is Key);
    assert(commit2.issued->Some_0->Key_op == s.next_op);
    assert(commit2.issued->Some_0->Key_key == previous);
    assert(!commit2.issued->Some_0->Key_arm);
    let issued_delete_name = commit2.issued->Some_0->Key_name;
    assert(after_answer.ops.contains_key(s.next_op));
    assert(after_answer.ops[s.next_op] == Owner::Flight(fid));
    assert(after_answer.out.last() == EffectSpec::Store {
        op: s.next_op,
        request: StoreReqSpec::Del { key: issued_delete_name },
    });
    let flight0 = FlightSpec {
        phase: PhaseSpec::Idle,
        ..s.flights.inflight[fid]
    };
    let waiting_flight = FlightSpec {
        phase: PhaseSpec::Origin {
            commit: commit2,
            done: s.flights.inflight[fid].phase->Origin_done,
        },
        ..flight0
    };
    let waiting = S {
        flights: FlightsSpec {
            inflight: after_answer.flights.inflight.insert(
                fid,
                waiting_flight,
            ),
            ..after_answer.flights
        },
        ..after_answer
    };
    assert(spec_inflight(after_answer, waiting_flight) == waiting);
    assert(spec_answered_origin(
        taken,
        fid,
        flight0,
        commit,
        s.flights.inflight[fid].phase->Origin_done,
        StoreRes::PutIfMatch { result: Ok(written_etag) },
    ) == waiting);
    assert(spec_flight_completed(
        without_op,
        fid,
        op,
        StoreRes::PutIfMatch { result: Ok(written_etag) },
    ) == waiting);
    assert(waiting.flights.inflight
        == after_answer.flights.inflight.insert(
            fid,
            waiting_flight,
        ));
    assert(waiting.flights.inflight.contains_key(fid));
    assert(waiting.out == after_answer.out);
    let (next, effects) = spec_on_event(
        s,
        EventSpec::Store {
            op,
            response: StoreRes::PutIfMatch {
                result: Ok(written_etag),
            },
            clock: response_at,
        },
    );
    let delete_name = next.flights.inflight[
        fid
    ].phase->Origin_commit.issued->Some_0->Key_name;
    assert(effects == waiting.out);
    assert(next == (S { out: Seq::empty(), ..waiting }));
    assert(next.out.len() == 0);
    assert(effects.last() == EffectSpec::Store {
        op: s.next_op,
        request: StoreReqSpec::Del { key: delete_name },
    });
    let (answered, answered_commit) = spec_answered(
        taken,
        CommittingSpec { issued: None, ..commit },
        commit.issued->Some_0,
        Some(StoreRes::PutIfMatch {
            result: Ok(written_etag),
        }),
    );
    assert(no_reply_effects(answered.out));
    assert(after_answer.out == answered.out.push(
        EffectSpec::Store {
            op: s.next_op,
            request: StoreReqSpec::Del { key: delete_name },
        },
    ));
    assert(after_answer.out.len() > 0);
    lemma_no_reply_effects_push(
        answered.out,
        EffectSpec::Store {
            op: s.next_op,
            request: StoreReqSpec::Del { key: delete_name },
        },
    );
    assert(no_reply_effects(effects));
    assert(effects.len() > 0);
    assert(next.ops.contains_key(s.next_op));
    assert(next.ops[s.next_op] == Owner::Flight(fid));
    assert(next.flights.inflight.contains_key(fid));
    assert(next.flights.inflight[fid].phase is Origin);
    assert(next.flights.inflight[
        fid
    ].phase->Origin_commit.issued == Some(IssuedSpec::Key {
        op: s.next_op,
        key: previous,
        name: delete_name,
        arm: false,
    }));
}

/// A successful response to that exact previous-key delete closes the flight
/// and emits its final Reply after any request Send effects.
#[verifier::rlimit(20)]
pub proof fn lemma_successful_previous_key_delete_completes(
    s: S,
    fid: u64,
    op: u64,
    response_at: u64,
)
    requires
        s.out.len() == 0,
        s.node.members.refreshing(),
        !s.loops,
        s.ops.contains_key(op),
        s.ops[op] == Owner::Flight(fid),
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid].id == fid,
        s.flights.inflight[fid].work is Request,
        s.flights.inflight[fid].firing is None,
        !s.flights.inflight[fid].debug,
        s.flights.inflight[fid].phase is Origin,
        s.flights.inflight[fid].phase.expects() == Some(op),
        s.flights.inflight[fid].phase->Origin_commit.issued
            is Some,
        s.flights.inflight[fid].phase->Origin_commit.issued->Some_0
            is Key,
        s.flights.inflight[fid].phase->Origin_commit.seq.step
            == AStep::DeletingPrevious(
                s.flights.inflight[fid].phase->Origin_commit.issued
                    ->Some_0->Key_key,
            ),
        s.flights.inflight[fid].phase->Origin_commit.seq.fired is None,
        s.flights.slots.contains_key(crate::target::spec_name(
            s.flights.inflight[fid].target,
        )),
        s.flights.slots[crate::target::spec_name(
            s.flights.inflight[fid].target,
        )].busy == Some(fid),
        s.flights.slots[crate::target::spec_name(
            s.flights.inflight[fid].target,
        )].queue.len() == 0,
        s.flights.inflight[fid].phase->Origin_commit.issued->Some_0
            ->Key_op == op,
        !s.flights.inflight[fid].phase->Origin_commit.issued->Some_0
            ->Key_arm,
    ensures
        ({
            let (next, effects) = spec_on_event(
                s,
                EventSpec::Store {
                    op,
                    response: StoreRes::Del { result: Ok(()) },
                    clock: response_at,
                },
            );
            &&& !next.ops.contains_key(op)
            &&& !next.flights.inflight.contains_key(fid)
            &&& effects.len() > 0
            &&& effects.last() == normal_request_reply_effect(
                s.flights.inflight[fid],
                s.flights.inflight[fid].phase->Origin_done,
            )
            &&& no_reply_effects(effects.drop_last())
        }),
{
    reveal(spec_on_event);
    reveal(spec_flight_completed);
    reveal(spec_answered_phase);
    reveal(spec_answered_origin);
    reveal(spec_commit_advance);
    reveal(spec_answered);
    reveal(spec_committed);
    reveal(spec_send_all);
    reveal(spec_finish);
    reveal(spec_release);
    reveal(spec_schedule_wake);
    reveal(spec_advance);
    let clocked = S { clock: response_at, ..s };
    assert(clocked.node.members.refreshing());
    let without_op = S {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    let taken = crate::handler_docs::spec_take_flight(
        without_op,
        fid,
    );
    let commit = s.flights.inflight[fid].phase->Origin_commit;
    let (advanced, core, outcome) = spec_advance(
        commit.seq,
        without_op.node.core,
        AAnswer::Done,
    );
    assert(outcome == AOutcome::Act(AAct::Done { deleted: false }));
    assert(no_reply_effects(taken.out));
    lemma_answered_key_delete_success_no_reply(
        taken,
        CommittingSpec { issued: None, ..commit },
        commit.issued->Some_0,
    );
    let (answered, commit2, progress) = spec_commit_advance(
        taken,
        fid,
        commit,
        Some(StoreRes::Del { result: Ok(()) }),
    );
    assert(progress == ProgressSpec::Done(Fired::Kept));
    let flight0 = FlightSpec {
        phase: PhaseSpec::Idle,
        ..s.flights.inflight[fid]
    };
    let done = s.flights.inflight[fid].phase->Origin_done;
    let response = match done.response {
        Some(response) => Ok(AnswerSpec::Step {
            kind: s.flights.inflight[fid].work->Request_kind,
            corr: s.flights.inflight[fid].work->Request_corr,
            action_kind:
                s.flights.inflight[fid].work->Request_action_kind,
            response,
            why: done.why,
        }),
        None => Err("no answer"@),
    };
    let noted = spec_note(
        answered,
        NoteSpec::Commit(crate::types::CommitOutcome::Committed),
    );
    let sent = spec_send_all(noted, done.outbox);
    lemma_send_all_frame(noted, done.outbox);
    assert(no_reply_effects(answered.out));
    lemma_no_reply_effects_push(
        answered.out,
        EffectSpec::Note(NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        )),
    );
    assert(no_reply_effects(noted.out));
    lemma_outbound_send_effects_no_reply(done.outbox);
    lemma_no_reply_effects_concat(
        noted.out,
        outbound_send_effects(done.outbox),
    );
    assert(no_reply_effects(sent.out));
    let replied = spec_emit(sent, EffectSpec::Reply {
        id: s.flights.inflight[fid].work->Request_id,
        response,
    });
    assert(replied.out.last() is Reply);
    assert(replied.out.last()->Reply_id
        == s.flights.inflight[fid].work->Request_id);
    assert(replied.out.last() == normal_request_reply_effect(
        s.flights.inflight[fid],
        done,
    ));
    assert(replied.out.drop_last() == sent.out);
    let committed = spec_committed(
        answered,
        flight0,
        done,
        Fired::Kept,
    );
    assert(committed == spec_finish(
        replied,
        FlightSpec { idle: !done.did, ..flight0 },
        Ok(Fired::Kept),
    ));
    assert(answered.ops == taken.ops);
    assert(taken.ops == without_op.ops);
    assert(replied.ops == without_op.ops);
    assert(replied.flights.inflight == taken.flights.inflight);
    assert(!committed.ops.contains_key(op));
    assert(!committed.flights.inflight.contains_key(fid));
    assert(committed.out.len() > 0);
    assert(committed.out.last() is Reply);
    assert(committed.out.last()->Reply_id
        == s.flights.inflight[fid].work->Request_id);
    assert(committed.out.last() == normal_request_reply_effect(
        s.flights.inflight[fid],
        done,
    ));
    let (next, effects) = spec_on_event(
        s,
        EventSpec::Store {
            op,
            response: StoreRes::Del { result: Ok(()) },
            clock: response_at,
        },
    );
    assert(!next.ops.contains_key(op));
    assert(!next.flights.inflight.contains_key(fid));
    assert(effects.len() > 0);
    assert(effects.last() is Reply);
    assert(effects.last()->Reply_id
        == s.flights.inflight[fid].work->Request_id);
    assert(effects.last() == normal_request_reply_effect(
        s.flights.inflight[fid],
        done,
    ));
    assert(no_reply_effects(effects.drop_last()));
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
// Normal-origin failure, retry, and stale-response slices
// ---------------------------------------------------------------------------

/// A lost conditional-write race does not answer the request. The production
/// commit forgets the stale cache entry, increments the same flight's attempt,
/// and emits the exact document Get used to re-decide the request.
#[verifier::rlimit(30)]
pub proof fn lemma_origin_write_precondition_failed_reloads(
    s: S,
    fid: u64,
    op: u64,
    response_at: u64,
)
    requires
        s.out.len() == 0,
        s.node.members.refreshing(),
        !s.loops,
        !s.ops.contains_key(s.next_op),
        s.ops.contains_key(op),
        s.ops[op] == Owner::Flight(fid),
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid].id == fid,
        s.flights.inflight[fid].target is Origin,
        s.flights.inflight[fid].work is Request,
        s.flights.inflight[fid].phase is Origin,
        s.flights.inflight[fid].phase.expects() == Some(op),
        s.flights.inflight[fid].phase->Origin_commit.seq.step
            == (AStep::Writing { idle: false }),
        s.flights.inflight[fid].phase->Origin_commit.issued is Some,
        s.flights.inflight[fid].phase->Origin_commit.issued->Some_0
            is Write,
        s.flights.inflight[fid].phase->Origin_commit.issued->Some_0
            ->Write_op == op,
        s.flights.inflight[fid].attempt < u32::MAX,
        s.flights.inflight[fid].attempt + 1
            <= s.flights.max_retries,
        crate::cache::spec_find(
            crate::cache::spec_remove(
                s.cache,
                s.flights.inflight[fid].target->Origin_0,
            ).entries,
            s.flights.inflight[fid].target->Origin_0,
        ) is None,
    ensures
        ({
            let origin = s.flights.inflight[fid].target->Origin_0;
            let (next, effects) = spec_on_event(
                s,
                EventSpec::Store {
                    op,
                    response: StoreRes::PutIfMatch {
                        result: Err(StoreError::PreconditionFailed),
                    },
                    clock: response_at,
                },
            );
            &&& !next.ops.contains_key(op)
            &&& next.ops.contains_key(s.next_op)
            &&& next.ops[s.next_op] == Owner::Flight(fid)
            &&& next.flights.inflight.contains_key(fid)
            &&& next.flights.inflight[fid].id == fid
            &&& next.flights.inflight[fid].target
                == s.flights.inflight[fid].target
            &&& next.flights.inflight[fid].work
                == s.flights.inflight[fid].work
            &&& next.flights.inflight[fid].attempt
                == s.flights.inflight[fid].attempt + 1
            &&& next.flights.inflight[fid].phase
                == PhaseSpec::Loading {
                    op: s.next_op,
                    revalidating: None,
                }
            &&& effects == seq![
                EffectSpec::Note(NoteSpec::Commit(
                    crate::types::CommitOutcome::Raced,
                )),
                EffectSpec::Note(NoteSpec::Raced {
                    target: origin,
                    attempt: s.flights.inflight[fid].attempt,
                }),
                EffectSpec::Note(NoteSpec::Cache(CacheResult::Miss)),
                EffectSpec::Store {
                    op: s.next_op,
                    request: StoreReqSpec::Get {
                        key: spec_doc_key(s.keys.prefix, origin),
                    },
                },
            ]
            &&& no_reply_effects(effects)
        }),
{
    reveal(spec_on_event);
    reveal(spec_flight_completed);
    reveal(spec_answered_phase);
    reveal(spec_answered_origin);
    reveal(spec_commit_advance);
    reveal(spec_answered);
    reveal(spec_advance);
    reveal(spec_commit_failed);
    reveal(spec_retry);
    reveal(spec_begin);
    reveal(spec_load_origin);
    reveal(crate::state::spec_forget_origin);
    reveal(crate::cache::spec_remove);
    reveal(crate::cache::spec_get);
    reveal(spec_store);
    reveal(spec_inflight);
    reveal(spec_schedule_wake);
    let clocked = S { clock: response_at, ..s };
    let without_op = S {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    let taken = crate::handler_docs::spec_take_flight(
        without_op,
        fid,
    );
    let commit = s.flights.inflight[fid].phase->Origin_commit;
    let (answered, commit2, progress) = spec_commit_advance(
        taken,
        fid,
        commit,
        Some(StoreRes::PutIfMatch {
            result: Err(StoreError::PreconditionFailed),
        }),
    );
    assert(progress == ProgressSpec::Failed(
        StoreErrorSpec::PreconditionFailed,
    ));
    let origin = s.flights.inflight[fid].target->Origin_0;
    assert(s.flights.inflight[fid].attempt.wrapping_add(1)
        == s.flights.inflight[fid].attempt + 1);
    assert(s.flights.inflight[fid].attempt.wrapping_add(1)
        <= s.flights.max_retries);
    let retrying = spec_commit_failed(
        answered,
        FlightSpec {
            phase: PhaseSpec::Idle,
            ..s.flights.inflight[fid]
        },
        StoreErrorSpec::PreconditionFailed,
    );
    assert(retrying.flights.inflight.contains_key(fid));
    assert(retrying.flights.inflight[fid].phase
        == PhaseSpec::Loading {
            op: s.next_op,
            revalidating: None,
        });
    assert(retrying.out.len() > 0);
    assert(retrying.out.last() == EffectSpec::Store {
        op: s.next_op,
        request: StoreReqSpec::Get {
            key: spec_doc_key(s.keys.prefix, origin),
        },
    });
    let (next, effects) = spec_on_event(
        s,
        EventSpec::Store {
            op,
            response: StoreRes::PutIfMatch {
                result: Err(StoreError::PreconditionFailed),
            },
            clock: response_at,
        },
    );
    assert(effects == retrying.out);
    assert(next == S {
        out: Seq::empty(),
        ..retrying
    });
    assert(next.node.core == spec_forget(s.node.core, origin));
    assert(next.ops == s.ops.remove(op).insert(
        s.next_op,
        Owner::Flight(fid),
    ));
    assert(!next.ops.contains_key(op));
    assert(next.ops.contains_key(s.next_op));
    assert(next.ops[s.next_op] == Owner::Flight(fid));
    assert(next.next_op == s.next_op.wrapping_add(1));
    assert(next.flights.inflight.contains_key(fid));
    assert(next.flights.inflight[fid].id == fid);
    assert(next.flights.inflight[fid].target
        == s.flights.inflight[fid].target);
    assert(next.flights.inflight[fid].work
        == s.flights.inflight[fid].work);
    assert(next.flights.inflight[fid].attempt
        == s.flights.inflight[fid].attempt + 1);
    assert(next.flights.inflight[fid].phase
        == PhaseSpec::Loading {
            op: s.next_op,
            revalidating: None,
        });
    assert(effects.len() > 0);
    assert(effects.last() == EffectSpec::Store {
        op: s.next_op,
        request: StoreReqSpec::Get {
            key: spec_doc_key(s.keys.prefix, origin),
        },
    });
    assert(effects == seq![
        EffectSpec::Note(NoteSpec::Commit(
            crate::types::CommitOutcome::Raced,
        )),
        EffectSpec::Note(NoteSpec::Raced {
            target: origin,
            attempt: s.flights.inflight[fid].attempt,
        }),
        EffectSpec::Note(NoteSpec::Cache(CacheResult::Miss)),
        EffectSpec::Store {
            op: s.next_op,
            request: StoreReqSpec::Get {
                key: spec_doc_key(s.keys.prefix, origin),
            },
        },
    ]);
    reveal_with_fuel(no_reply_effects, 10);
    assert(no_reply_effects(effects));
}

/// Exact state and document premises for deciding the same request after a
/// raced conditional write has re-entered its cache-miss load phase.
pub open spec fn origin_retry_reload_write_ready(
    s: S,
    fid: u64,
    reload_op: u64,
    call: CallSpec,
    origin: Seq<char>,
    loaded: LoadedSpec,
    etag: Etag,
) -> bool {
    let at = call.now;
    let (after_body, response, _, _) = spec_request_transition(
        spec_stored_body(loaded.document),
        call.request,
        at,
        s.cfg.retry_timeout,
        REQUEST_SWEEP_STEPS as nat,
    );
    let after_document =
        spec_advance_stored(loaded.document, after_body, at);
    &&& s.out.len() == 0
    &&& s.node.members.refreshing()
    &&& !s.loops
    &&& s.ops.contains_key(reload_op)
    &&& s.ops[reload_op] == Owner::Flight(fid)
    &&& !s.ops.contains_key(s.next_op)
    &&& s.flights.inflight.contains_key(fid)
    &&& s.flights.inflight[fid].id == fid
    &&& s.flights.inflight[fid].target
        == TargetSpec::Origin(origin)
    &&& s.flights.inflight[fid].work == WorkSpec::Request {
        id: call.id,
        kind: call.kind,
        corr: call.corr,
        req: call.request,
        action_kind: call.action_kind,
        now: at,
    }
    &&& s.flights.inflight[fid].firing is None
    &&& !s.flights.inflight[fid].debug
    &&& s.flights.inflight[fid].phase == PhaseSpec::Loading {
        op: reload_op,
        revalidating: None,
    }
    &&& spec_slot_of(
        s,
        crate::target::spec_name(TargetSpec::Origin(origin)),
    ).busy == Some(fid)
    &&& spec_slot_of(
        s,
        crate::target::spec_name(TargetSpec::Origin(origin)),
    ).queue.len() == 0
    &&& !s.cfg.appendable
    &&& well_formed(loaded.document)
    &&& routed(loaded.document, call.request)
    &&& echod_concrete::node::spec_stored_committed_at(
        loaded.document,
    ) <= at
    &&& at <= MAX_TIME
    &&& 0 < s.cfg.retry_timeout <= MAX_TIME
    &&& safe_effect_config(at, s.cfg.retry_timeout)
    &&& document_ids_bounded(loaded.document)
    &&& response != spec_unavailable(call.request)
    &&& after_body != spec_stored_body(loaded.document)
    &&& spec_body_deadline(after_body) is None
    &&& spec_encode(after_document).len() <= usize::MAX as int
    &&& etag.0@.len() <= usize::MAX as int
}

/// The matching successful reload after a CAS race decodes the newly loaded
/// workflow, decides the original request again, and emits the next real
/// `PutIfMatch` from `State::on_event`.
#[verifier::rlimit(30)]
pub proof fn lemma_origin_retry_reload_success_issues_put_if_match(
    s: S,
    fid: u64,
    reload_op: u64,
    call: CallSpec,
    origin: Seq<char>,
    response_at: u64,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
)
    requires
        call.now <= response_at,
        spec_decode_workflow(bytes@) == Ok(loaded),
        origin_retry_reload_write_ready(
            s,
            fid,
            reload_op,
            call,
            origin,
            loaded,
            etag,
        ),
    ensures
        ({
            let (next, effects) = spec_on_event(
                s,
                EventSpec::Store {
                    op: reload_op,
                    response: StoreRes::Get {
                        result: Ok(Some((bytes, etag))),
                    },
                    clock: response_at,
                },
            );
            let (after_body, response, _, _) =
                spec_request_transition(
                    spec_stored_body(loaded.document),
                    call.request,
                    call.now,
                    s.cfg.retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                );
            let after_document = spec_advance_stored(
                loaded.document,
                after_body,
                call.now,
            );
            &&& !next.ops.contains_key(reload_op)
            &&& next.ops.contains_key(s.next_op)
            &&& next.ops[s.next_op] == Owner::Flight(fid)
            &&& next.next_op == s.next_op.wrapping_add(1)
            &&& next.flights.inflight.contains_key(fid)
            &&& next.flights.inflight[fid].work
                == s.flights.inflight[fid].work
            &&& next.flights.inflight[fid].attempt
                == s.flights.inflight[fid].attempt
            &&& next.flights.inflight[fid].phase is Origin
            &&& next.flights.inflight[fid].phase->Origin_done.response
                == Some(response)
            &&& next.flights.inflight[
                fid
            ].phase->Origin_commit.after == after_document
            &&& next.flights.inflight[
                fid
            ].phase->Origin_commit.issued == Some(IssuedSpec::Write {
                op: s.next_op,
                mode: crate::types::WriteMode::Rewrite,
                change_count:
                    echod_concrete::node::spec_body_len(after_body)
                        as usize,
                bytes: spec_encode(after_document).len() as u64,
                len: spec_encode(after_document).len() as usize,
            })
            &&& effects == seq![EffectSpec::Store {
                op: s.next_op,
                request: StoreReqSpec::PutIfMatch {
                    key: spec_doc_key(s.keys.prefix, origin),
                    body: spec_encode(after_document),
                    etag: etag.deep_view(),
                },
            }]
            &&& no_reply_effects(effects)
            &&& well_formed(after_document)
        }),
{
    lemma_normal_request_happy_path(
        loaded.document,
        call.request,
        call.now,
        s.cfg.retry_timeout,
    );
    reveal(spec_on_event);
    reveal(spec_flight_completed);
    reveal(spec_answered_phase);
    reveal(spec_answered_loading);
    reveal(spec_loaded_origin);
    reveal(spec_run_origin);
    reveal(spec_decide);
    reveal(spec_commit_new);
    reveal(spec_commit_advance);
    reveal(spec_issue_write);
    reveal(spec_schedule_wake);
    reveal(echod_concrete::quick_n_dirty::on_request);
    reveal(crate::verified::flight_spec::spec_advance);
    reveal(crate::verified::commit_spec::spec_prepare);
    reveal_with_fuel(no_reply_effects, 6);
    let (after_body, _, _, _) = spec_request_transition(
        spec_stored_body(loaded.document),
        call.request,
        call.now,
        s.cfg.retry_timeout,
        REQUEST_SWEEP_STEPS as nat,
    );
    let after_document =
        spec_advance_stored(loaded.document, after_body, call.now);
    let effects = spec_on_event(
        s,
        EventSpec::Store {
            op: reload_op,
            response: StoreRes::Get {
                result: Ok(Some((bytes, etag))),
            },
            clock: response_at,
        },
    ).1;
    assert(effects == seq![EffectSpec::Store {
        op: s.next_op,
        request: StoreReqSpec::PutIfMatch {
            key: spec_doc_key(s.keys.prefix, origin),
            body: spec_encode(after_document),
            etag: etag.deep_view(),
        },
    }]);
}

/// An unavailable answer to the currently owned document write fails the
/// request exactly once. With an empty lane queue and no timer/debug owner,
/// cleanup cannot start another flight or emit a Send/Store effect.
pub proof fn lemma_origin_write_unavailable_replies_once(
    s: S,
    fid: u64,
    op: u64,
    response_at: u64,
    message: String,
)
    requires
        s.out.len() == 0,
        s.node.members.refreshing(),
        !s.loops,
        s.ops.contains_key(op),
        s.ops[op] == Owner::Flight(fid),
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid].id == fid,
        s.flights.inflight[fid].target is Origin,
        s.flights.inflight[fid].work is Request,
        s.flights.inflight[fid].firing is None,
        !s.flights.inflight[fid].debug,
        s.flights.inflight[fid].phase is Origin,
        s.flights.inflight[fid].phase.expects() == Some(op),
        s.flights.inflight[fid].phase->Origin_commit.seq.step
            == (AStep::Writing { idle: false }),
        s.flights.inflight[fid].phase->Origin_commit.issued
            is Some,
        s.flights.inflight[
            fid
        ].phase->Origin_commit.issued->Some_0 is Write,
        s.flights.inflight[
            fid
        ].phase->Origin_commit.issued->Some_0->Write_op == op,
        spec_slot_of(
            s,
            crate::target::spec_name(
                s.flights.inflight[fid].target,
            ),
        ).busy == Some(fid),
        spec_slot_of(
            s,
            crate::target::spec_name(
                s.flights.inflight[fid].target,
            ),
        ).queue.len() == 0,
    ensures
        ({
            let (next, effects) = spec_on_event(
                s,
                EventSpec::Store {
                    op,
                    response: StoreRes::PutIfMatch {
                        result: Err(StoreError::Unavailable(message)),
                    },
                    clock: response_at,
                },
            );
            &&& !next.ops.contains_key(op)
            &&& !next.flights.inflight.contains_key(fid)
            &&& effects == seq![
                EffectSpec::Note(NoteSpec::Commit(
                    crate::types::CommitOutcome::Failed,
                )),
                EffectSpec::Reply {
                    id: s.flights.inflight[fid].work->Request_id,
                    response: Err(spec_error_text(
                        StoreErrorSpec::Unavailable(message@),
                    )),
                },
            ]
            &&& no_reply_effects(effects.drop_last())
        }),
{
    reveal(spec_on_event);
    reveal(spec_flight_completed);
    reveal(spec_answered_phase);
    reveal(spec_answered_origin);
    reveal(spec_commit_advance);
    reveal(spec_answered);
    reveal(spec_advance);
    reveal(spec_commit_failed);
    reveal(spec_fail);
    reveal(spec_finish);
    reveal(spec_release);
    reveal(crate::state::spec_forget_origin);
    reveal(spec_schedule_wake);
    reveal_with_fuel(no_reply_effects, 5);
    let (next, effects) = spec_on_event(
        s,
        EventSpec::Store {
            op,
            response: StoreRes::PutIfMatch {
                result: Err(StoreError::Unavailable(message)),
            },
            clock: response_at,
        },
    );
    assert(!next.ops.contains_key(op));
    assert(!next.flights.inflight.contains_key(fid));
    assert(effects.len() > 0);
    assert(effects.last() == EffectSpec::Reply {
        id: s.flights.inflight[fid].work->Request_id,
        response: Err(spec_error_text(
            StoreErrorSpec::Unavailable(message@),
        )),
    });
    assert(effects == seq![
        EffectSpec::Note(NoteSpec::Commit(
            crate::types::CommitOutcome::Failed,
        )),
        EffectSpec::Reply {
            id: s.flights.inflight[fid].work->Request_id,
            response: Err(spec_error_text(
                StoreErrorSpec::Unavailable(message@),
            )),
        },
    ]);
    assert(no_reply_effects(effects.drop_last()));
}

/// A response of the wrong Store shape for an owned `PutIfMatch` is the
/// production "unexpected store response" failure: one Reply, no Send.
pub proof fn lemma_origin_write_mismatched_response_replies_once(
    s: S,
    fid: u64,
    op: u64,
    response_at: u64,
)
    requires
        s.out.len() == 0,
        s.node.members.refreshing(),
        !s.loops,
        s.ops.contains_key(op),
        s.ops[op] == Owner::Flight(fid),
        s.flights.inflight.contains_key(fid),
        s.flights.inflight[fid].id == fid,
        s.flights.inflight[fid].target is Origin,
        s.flights.inflight[fid].work is Request,
        s.flights.inflight[fid].firing is None,
        !s.flights.inflight[fid].debug,
        s.flights.inflight[fid].phase is Origin,
        s.flights.inflight[fid].phase.expects() == Some(op),
        s.flights.inflight[fid].phase->Origin_commit.seq.step
            == (AStep::Writing { idle: false }),
        s.flights.inflight[fid].phase->Origin_commit.issued
            is Some,
        s.flights.inflight[
            fid
        ].phase->Origin_commit.issued->Some_0 is Write,
        s.flights.inflight[
            fid
        ].phase->Origin_commit.issued->Some_0->Write_op == op,
        spec_slot_of(
            s,
            crate::target::spec_name(
                s.flights.inflight[fid].target,
            ),
        ).busy == Some(fid),
        spec_slot_of(
            s,
            crate::target::spec_name(
                s.flights.inflight[fid].target,
            ),
        ).queue.len() == 0,
    ensures
        ({
            let (next, effects) = spec_on_event(
                s,
                EventSpec::Store {
                    op,
                    response: StoreRes::Del {
                        result: Ok(()),
                    },
                    clock: response_at,
                },
            );
            &&& !next.ops.contains_key(op)
            &&& !next.flights.inflight.contains_key(fid)
            &&& effects == seq![
                EffectSpec::Note(NoteSpec::Commit(
                    crate::types::CommitOutcome::Failed,
                )),
                EffectSpec::Reply {
                    id: s.flights.inflight[fid].work->Request_id,
                    response: Err(spec_error_text(spec_unexpected())),
                },
            ]
            &&& no_reply_effects(effects.drop_last())
        }),
{
    reveal(spec_on_event);
    reveal(spec_flight_completed);
    reveal(spec_answered_phase);
    reveal(spec_answered_origin);
    reveal(spec_commit_advance);
    reveal(spec_answered);
    reveal(spec_advance);
    reveal(spec_commit_failed);
    reveal(spec_fail);
    reveal(spec_finish);
    reveal(spec_release);
    reveal(crate::state::spec_forget_origin);
    reveal(spec_schedule_wake);
    reveal_with_fuel(no_reply_effects, 5);
    let (next, effects) = spec_on_event(
        s,
        EventSpec::Store {
            op,
            response: StoreRes::Del { result: Ok(()) },
            clock: response_at,
        },
    );
    assert(!next.ops.contains_key(op));
    assert(!next.flights.inflight.contains_key(fid));
    assert(effects.len() > 0);
    assert(effects.last() == EffectSpec::Reply {
        id: s.flights.inflight[fid].work->Request_id,
        response: Err(spec_error_text(spec_unexpected())),
    });
    assert(effects == seq![
        EffectSpec::Note(NoteSpec::Commit(
            crate::types::CommitOutcome::Failed,
        )),
        EffectSpec::Reply {
            id: s.flights.inflight[fid].work->Request_id,
            response: Err(spec_error_text(spec_unexpected())),
        },
    ]);
    assert(no_reply_effects(effects.drop_last()));
}

/// A Store completion for an op that is no longer owned is stale. It only
/// advances the production clock; it cannot alter the core flight state,
/// pending operations, or emit an effect.
pub proof fn lemma_stale_store_response_stutters(
    s: S,
    op: u64,
    response: StoreRes,
    response_at: u64,
)
    requires
        s.out.len() == 0,
        s.node.members.refreshing(),
        !s.loops,
        !s.ops.contains_key(op),
    ensures
        spec_on_event(
            s,
            EventSpec::Store {
                op,
                response,
                clock: response_at,
            },
        ) == (
            S {
                clock: response_at,
                ..s
            },
            Seq::<EffectSpec>::empty(),
        ),
{
    reveal(spec_on_event);
    reveal(spec_schedule_wake);
    assert(s.ops.remove(op) =~= s.ops);
    let (next, effects) = spec_on_event(
        s,
        EventSpec::Store {
            op,
            response,
            clock: response_at,
        },
    );
    assert(effects =~= Seq::<EffectSpec>::empty());
    assert(next == S { clock: response_at, ..s });
}

// ---------------------------------------------------------------------------
// Explicit global frontier beyond the bounded slices above
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

/// Machine-checkable classification of cases still outside the global
/// simulation theorem. Some variants have bounded normal-origin lemmas above;
/// this predicate remains useful for all other owners and request shapes.
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
