//! Refinement target for the production-backed Rover model.
//!
//! The existing concrete-to-abstract proof cannot simply be renamed: its
//! relation is over `echod_concrete::model::NodeV`, while the production model
//! now steps [`crate::state::StateSpec`] with caches, concurrent flights,
//! membership refresh, wake replacement, and the full store-call sequence.
//! This module records the exact theorem target and proves bounded slices of
//! the real Rover transition relation: a quiet empty task heartbeat and a
//! normal origin request through admission, hidden Store Get delivery, the
//! matching successful StoreRes, decode/decision, conditional-write delivery,
//! and final Reply. The previous-deadline-key branch additionally proves the
//! exact hidden Del delivery and matching successful response. Bounded
//! production-step theorems also cover CAS-race reload/redecision, unavailable
//! and wrong-shaped write failures, stale responses, and unrelated-lane
//! framing.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::document::{spec_decode_workflow, spec_encode, LoadedSpec};
#[cfg(verus_keep_ghost)]
use crate::refinement::{
    document_ids_bounded,
    lemma_empty_heartbeat_core_step,
    lemma_normal_origin_request_starts_load,
    lemma_normal_origin_successful_get_issues_put_if_match,
    lemma_normal_request_matches_abstract_handler,
    lemma_origin_write_mismatched_response_replies_once,
    lemma_origin_write_precondition_failed_reloads,
    lemma_origin_write_unavailable_replies_once,
    lemma_origin_retry_reload_success_issues_put_if_match,
    lemma_stale_store_response_stutters,
    lemma_successful_origin_write_completes_directly,
    lemma_successful_origin_write_issues_previous_key_delete,
    lemma_successful_previous_key_delete_completes,
    lemma_no_reply_effects_drop_last,
    no_reply_effects,
    normal_origin_previous_deadline_key,
    origin_retry_reload_write_ready,
    normal_request_reply_effect,
    normal_origin_request_ready,
    normal_origin_get_write_ready,
    quiet_request_ready,
};
#[cfg(verus_keep_ghost)]
use crate::rover::{
    spec_call, spec_effect, spec_effects, spec_node_step,
    spec_store_request, spec_store_step, spec_take_pending, LocalV, Message,
    Model as ProductionModel, NodeV,
};
#[cfg(verus_keep_ghost)]
use crate::state::{Owner, S};
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;
#[cfg(verus_keep_ghost)]
use crate::types::{AnswerSpec, EventSpec, RequestEventSpec};
#[cfg(verus_keep_ghost)]
use echod_abstract::{
    Call as BoundaryCall, Model as AbstractModel, Output, ServerConfig,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::view::StoreV as AbstractStoreV;
#[cfg(verus_keep_ghost)]
use echod_concrete::document::{well_formed, StoredDocumentV};
#[cfg(verus_keep_ghost)]
use echod_concrete::effects::{effects_match, safe_effect_config};
#[cfg(verus_keep_ghost)]
use echod_concrete::interpret::{doc_rel, finite_store, request_agrees};
#[cfg(verus_keep_ghost)]
use echod_concrete::node::{
    spec_stored_body, spec_unavailable, REQUEST_SWEEP_STEPS,
};
#[cfg(verus_keep_ghost)]
use echod_concrete::quick_n_dirty::{on_request, routed};
#[cfg(verus_keep_ghost)]
use echod_concrete::relation::agreement;
#[cfg(verus_keep_ghost)]
use echod_concrete::model::Pid;
#[cfg(verus_keep_ghost)]
use echod_concrete::store::{
    spec_apply, Etag, StoreError, StoreReq, StoreReqSpec, StoreRes,
    StoreV,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::refinement::{concrete_refines_abstract, refines, simulation};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{
    event_valid, is_process, land, step, initial, Label, StepResultV, World,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::{ProcessEvent, RoverModel};
#[cfg(verus_keep_ghost)]
use echod_types::{Response, StatusRes, MAX_TIME};
#[cfg(verus_keep_ghost)]
use crate::verified::node::AKey;

verus! {

/// The abstract service configuration implemented by one production node.
pub open spec fn abstract_config(config: crate::Config) -> ServerConfig {
    ServerConfig {
        retry_timeout: config.retry_timeout,
    }
}

/// The production document decisions already share the concrete handler,
/// due-step, occurrence, and effect proofs used by the established
/// concrete-to-abstract simulation.
pub proof fn lemma_shared_handler_agreement(config: crate::Config)
    ensures
        agreement(abstract_config(config)),
{
    echod_concrete::timers::lemma_agreement(abstract_config(config));
}

// ---------------------------------------------------------------------------
// Production-backed Rover request slices
// ---------------------------------------------------------------------------

pub open spec fn pending_id_fresh(
    pending: Seq<(u64, BoundaryCall)>,
    id: u64,
) -> bool {
    forall|i: int| 0 <= i < pending.len() ==> pending[i].0 != id
}

proof fn lemma_take_pending_fresh(
    pending: Seq<(u64, BoundaryCall)>,
    id: u64,
)
    requires
        pending_id_fresh(pending, id),
    ensures
        spec_take_pending(pending, id) == (None, pending),
    decreases pending.len(),
{
    if pending.len() == 0 {
        assert(pending =~= Seq::<(u64, BoundaryCall)>::empty());
    } else {
        let prefix = pending.drop_last();
        assert(pending_id_fresh(prefix, id)) by {
            assert forall|i: int| 0 <= i < prefix.len()
                implies prefix[i].0 != id by {
                assert(prefix[i] == pending[i]);
            }
        }
        lemma_take_pending_fresh(prefix, id);
        assert(pending.last().0 != id);
        assert(prefix.push(pending.last()) =~= pending);
    }
}

proof fn lemma_take_pending_fresh_push(
    pending: Seq<(u64, BoundaryCall)>,
    call: BoundaryCall,
)
    requires
        pending_id_fresh(pending, call.id),
    ensures
        spec_take_pending(
            pending.push((call.id, call)),
            call.id,
        ) == (Some(call), pending),
{
    lemma_take_pending_fresh(pending, call.id);
    assert(pending.push((call.id, call)).drop_last() =~= pending);
    assert(pending.push((call.id, call)).last() == (call.id, call));
}

proof fn lemma_no_reply_effects_preserve_pending(
    node: NodeV,
    at: u64,
    effects: Seq<crate::types::EffectSpec>,
)
    requires
        no_reply_effects(effects),
    ensures
        spec_effects(node, at, effects).0.pending == node.pending,
    decreases effects.len(),
{
    reveal_with_fuel(no_reply_effects, 2);
    reveal(spec_effects);
    reveal(spec_effect);
    if effects.len() > 0 {
        let prefix = effects.drop_last();
        lemma_no_reply_effects_drop_last(effects);
        lemma_no_reply_effects_preserve_pending(node, at, prefix);
        let (before_last, send) = spec_effects(node, at, prefix);
        match effects.last() {
            crate::types::EffectSpec::Reply { .. } => {
                assert(false);
            },
            _ => {},
        }
    }
}

proof fn lemma_effects_preserve_core(
    node: NodeV,
    at: u64,
    effects: Seq<crate::types::EffectSpec>,
)
    ensures
        spec_effects(node, at, effects).0.core == node.core,
    decreases effects.len(),
{
    reveal(spec_effects);
    if effects.len() > 0 {
        let prefix = effects.drop_last();
        lemma_effects_preserve_core(node, at, prefix);
        let (before_last, send) = spec_effects(node, at, prefix);
        reveal(spec_effect);
    }
}

pub open spec fn request_event(
    call: BoundaryCall,
) -> ProcessEvent<Pid, Message> {
    ProcessEvent::Receive {
        sender: Pid::Outside,
        message: Message::Request(call),
    }
}

pub open spec fn empty_heartbeat_reply(
    call: BoundaryCall,
) -> (Pid, Message) {
    (
        Pid::Outside,
        Message::Reply(Output::Response {
            client: call.client,
            id: call.id,
            response: Response::Status(StatusRes { status: 200 }),
        }),
    )
}

pub open spec fn empty_heartbeat_result(
    node: NodeV,
    at: u64,
    call: BoundaryCall,
) -> StepResultV<LocalV, Pid, Message> {
    StepResultV {
        state: LocalV::Node(NodeV {
            core: S {
                clock: at,
                out: Seq::empty(),
                ..node.core
            },
            pending: node.pending,
            wake: node.wake,
        }),
        send: seq![empty_heartbeat_reply(call)],
    }
}

/// The node-level Rover outcome for an empty task heartbeat. Its core is the
/// real `spec_on_event` transition proved in `refinement`, and its reply is
/// interpreted by the same adapter used by executable `Node::step`.
pub proof fn lemma_empty_heartbeat_node_step(
    node: NodeV,
    at: u64,
    call: BoundaryCall,
)
    requires
        crate::rover::spec_empty_heartbeat(call.request),
        quiet_request_ready(node.core),
        pending_id_fresh(node.pending, call.id),
    ensures
        spec_node_step(node, at, request_event(call))
            == seq![empty_heartbeat_result(node, at, call)],
{
    reveal(spec_node_step);
    assert(crate::rover::spec_target(call.request) is None);
    let event = EventSpec::Request {
        clock: at,
        request: RequestEventSpec::EmptyHeartbeat {
            id: call.id,
            kind: Seq::empty(),
            corr: call.client@,
            action_kind: None,
        },
    };
    lemma_empty_heartbeat_core_step(
        node.core,
        at,
        call.id,
        Seq::empty(),
        call.client@,
        None,
    );
    let core = S {
        clock: at,
        out: Seq::empty(),
        ..node.core
    };
    let reply = crate::types::EffectSpec::Reply {
        id: call.id,
        response: Ok(AnswerSpec::Step {
            kind: Seq::empty(),
            corr: call.client@,
            action_kind: None,
            response: Response::Status(StatusRes { status: 200 }),
            why: None,
        }),
    };
    assert(crate::handler::spec_on_event(node.core, event)
        == (core, seq![reply]));
    lemma_take_pending_fresh_push(node.pending, call);
    reveal_with_fuel(spec_effects, 3);
    reveal(spec_effect);
    let started = NodeV {
        core,
        pending: node.pending.push((call.id, call)),
        wake: node.wake,
    };
    assert(spec_effects(started, at, seq![reply]) == (
        empty_heartbeat_result(node, at, call).state->Node_0,
        seq![empty_heartbeat_reply(call)],
    ));
    assert(spec_node_step(node, at, request_event(call))
        =~= seq![empty_heartbeat_result(node, at, call)]);
}

pub open spec fn empty_heartbeat_slice_ready(
    before: World<ProductionModel>,
    at: u64,
    call: BoundaryCall,
) -> bool {
    &&& before.process.len() > 0
    &&& before.process[0].0 == Pid::Node(0)
    &&& before.process[0].1 is Node
    &&& before.now <= at
    &&& event_valid(before, Pid::Node(0), request_event(call))
    &&& crate::rover::spec_empty_heartbeat(call.request)
    &&& quiet_request_ready(before.process[0].1->Node_0.core)
    &&& pending_id_fresh(
        before.process[0].1->Node_0.pending,
        call.id,
    )
}

/// A precisely bounded slice of Rover's real transition relation for one
/// external empty task heartbeat.
pub open spec fn empty_heartbeat_rover_step(
    config: crate::Config,
    before: World<ProductionModel>,
    at: u64,
    call: BoundaryCall,
    after: World<ProductionModel>,
) -> bool {
    let node = before.process[0].1->Node_0;
    let result = empty_heartbeat_result(node, at, call);
    &&& empty_heartbeat_slice_ready(before, at, call)
    &&& after == land(before, 0, Pid::Node(0), at, result)
    &&& step(
        ProductionModel,
        config,
        before,
        Label::Process {
            process: Pid::Node(0),
            at,
            event: request_event(call),
            send: result.send,
        },
        after,
    )
}

#[verifier::rlimit(10)]
pub proof fn lemma_empty_heartbeat_rover_step(
    config: crate::Config,
    before: World<ProductionModel>,
    at: u64,
    call: BoundaryCall,
)
    requires
        empty_heartbeat_slice_ready(before, at, call),
    ensures
        empty_heartbeat_rover_step(
            config,
            before,
            at,
            call,
            land(
                before,
                0,
                Pid::Node(0),
                at,
                empty_heartbeat_result(
                    before.process[0].1->Node_0,
                    at,
                    call,
                ),
            ),
        ),
{
    let node = before.process[0].1->Node_0;
    let result = empty_heartbeat_result(node, at, call);
    lemma_empty_heartbeat_node_step(node, at, call);
    lemma_node_rover_step(
        config,
        before,
        0,
        at,
        request_event(call),
        result,
    );
}

pub open spec fn normal_origin_admission_result(
    node: NodeV,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
) -> StepResultV<LocalV, Pid, Message> {
    let process_call =
        spec_call(call, TargetSpec::Origin(origin), at);
    let event = EventSpec::Request {
        clock: at,
        request: RequestEventSpec::Protocol(process_call),
    };
    let (core, _) = crate::handler::spec_on_event(node.core, event);
    StepResultV {
        state: LocalV::Node(NodeV {
            core,
            pending: node.pending.push((call.id, call)),
            wake: node.wake,
        }),
        send: seq![(
            Pid::Store,
            Message::StoreReq {
                op: node.core.next_op,
                request: spec_store_request(StoreReqSpec::Get {
                    key: crate::keys::spec_doc_key(
                        node.core.keys.prefix,
                        origin,
                    ),
                }),
            },
        )],
    }
}

/// The first normal-request node step is the actual production admission
/// transition: it creates one loading flight and emits the document Get.
pub proof fn lemma_normal_origin_request_node_step(
    node: NodeV,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
)
    requires
        crate::rover::spec_target(call.request)
            == Some(TargetSpec::Origin(origin)),
        normal_origin_request_ready(node.core, origin),
    ensures
        ({
            let result =
                normal_origin_admission_result(node, at, call, origin);
            &&& spec_node_step(node, at, request_event(call))
                == seq![result]
            &&& result.state->Node_0.core.ops.contains_key(
                node.core.next_op,
            )
            &&& result.state->Node_0.core.ops[node.core.next_op]
                == crate::state::Owner::Flight(node.core.next_flight)
            &&& result.state->Node_0.core.flights.inflight.contains_key(
                node.core.next_flight,
            )
            &&& result.state->Node_0.core.flights.inflight[
                node.core.next_flight
            ].target == TargetSpec::Origin(origin)
        }),
{
    let process_call =
        spec_call(call, TargetSpec::Origin(origin), at);
    lemma_normal_origin_request_starts_load(
        node.core,
        process_call,
        origin,
        at,
    );
    let event = EventSpec::Request {
        clock: at,
        request: RequestEventSpec::Protocol(process_call),
    };
    let (core, effects) =
        crate::handler::spec_on_event(node.core, event);
    let result =
        normal_origin_admission_result(node, at, call, origin);
    reveal(spec_node_step);
    assert(effects == seq![
        crate::types::EffectSpec::Note(
            crate::types::NoteSpec::Cache(
                crate::types::CacheResult::Miss,
            ),
        ),
        crate::types::EffectSpec::Store {
            op: node.core.next_op,
            request: StoreReqSpec::Get {
                key: crate::keys::spec_doc_key(
                    node.core.keys.prefix,
                    origin,
                ),
            },
        },
    ]);
    reveal_with_fuel(spec_effects, 4);
    reveal(spec_effect);
    assert(spec_effects(
        NodeV {
            core,
            pending: node.pending.push((call.id, call)),
            wake: node.wake,
        },
        at,
        effects,
    ) == (result.state->Node_0, result.send));
    assert(spec_node_step(node, at, request_event(call))
        =~= seq![result]);
    assert(result.state->Node_0.core == core);
}

pub open spec fn normal_origin_slice_ready(
    before: World<ProductionModel>,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
) -> bool {
    &&& before.process.len() > 0
    &&& before.process[0].0 == Pid::Node(0)
    &&& before.process[0].1 is Node
    &&& before.now <= at
    &&& event_valid(before, Pid::Node(0), request_event(call))
    &&& crate::rover::spec_target(call.request)
        == Some(TargetSpec::Origin(origin))
    &&& pending_id_fresh(
        before.process[0].1->Node_0.pending,
        call.id,
    )
    &&& normal_origin_request_ready(
        before.process[0].1->Node_0.core,
        origin,
    )
}

/// One real Rover process transition for a normal external origin request.
/// The predicate stops exactly after admission and the cache-miss Get; the
/// subsequent StoreRes/conditional-write sequence is not hidden in it.
pub open spec fn normal_origin_request_rover_step(
    config: crate::Config,
    before: World<ProductionModel>,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    after: World<ProductionModel>,
) -> bool {
    let node = before.process[0].1->Node_0;
    let result = normal_origin_admission_result(
        node,
        at,
        call,
        origin,
    );
    &&& normal_origin_slice_ready(before, at, call, origin)
    &&& after == land(before, 0, Pid::Node(0), at, result)
    &&& step(
        ProductionModel,
        config,
        before,
        Label::Process {
            process: Pid::Node(0),
            at,
            event: request_event(call),
            send: result.send,
        },
        after,
    )
    &&& result.state->Node_0.core.ops.contains_key(node.core.next_op)
    &&& result.state->Node_0.core.ops[node.core.next_op]
        == crate::state::Owner::Flight(node.core.next_flight)
    &&& result.state->Node_0.core.flights.inflight.contains_key(
        node.core.next_flight,
    )
    &&& result.state->Node_0.core.flights.inflight[
        node.core.next_flight
    ].target == TargetSpec::Origin(origin)
}

pub proof fn lemma_normal_origin_request_rover_step(
    config: crate::Config,
    before: World<ProductionModel>,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
)
    requires
        normal_origin_slice_ready(before, at, call, origin),
    ensures
        normal_origin_request_rover_step(
            config,
            before,
            at,
            call,
            origin,
            land(
                before,
                0,
                Pid::Node(0),
                at,
                normal_origin_admission_result(
                    before.process[0].1->Node_0,
                    at,
                    call,
                    origin,
                ),
            ),
        ),
{
    let node = before.process[0].1->Node_0;
    let result = normal_origin_admission_result(
        node,
        at,
        call,
        origin,
    );
    lemma_normal_origin_request_node_step(node, at, call, origin);
    assert(spec_node_step(node, at, request_event(call))
        == seq![result]);
    assert(spec_node_step(node, at, request_event(call)).len() == 1);
    reveal(step);
    assert(spec_node_step(node, at, request_event(call))[0] == result);
    assert(is_process(ProductionModel, before, Pid::Node(0))) by {
        assert(before.process[0].0 == Pid::Node(0));
    }
    assert(exists|i: int, j: int|
        #![trigger ProductionModel.spec_on_event(
            config,
            Pid::Node(0),
            before.process[i].1,
            at,
            request_event(call),
        )[j]]
        {
            &&& 0 <= i < before.process.len()
            &&& before.process[i].0 == Pid::Node(0)
            &&& {
                let outcomes = ProductionModel.spec_on_event(
                    config,
                    Pid::Node(0),
                    before.process[i].1,
                    at,
                    request_event(call),
                );
                &&& 0 <= j < outcomes.len()
                &&& outcomes[j].send == result.send
                &&& land(before, i, Pid::Node(0), at, outcomes[j])
                    == land(before, 0, Pid::Node(0), at, result)
            }
        }
    ) by {
        let i: int = 0;
        let j: int = 0;
        assert(ProductionModel.spec_on_event(
            config,
            Pid::Node(0),
            before.process[i].1,
            at,
            request_event(call),
        ) == seq![result]);
    }
}

pub open spec fn normal_origin_get_request(
    node: NodeV,
    origin: Seq<char>,
) -> StoreReq {
    spec_store_request(StoreReqSpec::Get {
        key: crate::keys::spec_doc_key(
            node.core.keys.prefix,
            origin,
        ),
    })
}

pub open spec fn normal_origin_admitted_world(
    before: World<ProductionModel>,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
) -> World<ProductionModel> {
    land(
        before,
        0,
        Pid::Node(0),
        at,
        normal_origin_admission_result(
            before.process[0].1->Node_0,
            at,
            call,
            origin,
        ),
    )
}

pub open spec fn fresh_store_delivery_result(
    store: StoreV,
    sender: Pid,
    op: u64,
    request: StoreReq,
) -> StepResultV<LocalV, Pid, Message> {
    let (next, response) = spec_apply(store, request);
    StepResultV {
        state: LocalV::Store(StoreV {
            seen: store.seen.push((sender, op)),
            ..next
        }),
        send: seq![(
            sender,
            Message::StoreRes { op, response },
        )],
    }
}

/// A fresh hidden StoreReq envelope executes the production store's
/// `spec_apply` transition exactly once and returns its matching StoreRes.
pub proof fn lemma_fresh_store_request_delivery(
    store: StoreV,
    sender: Pid,
    op: u64,
    request: StoreReq,
)
    requires
        !store.seen.contains((sender, op)),
    ensures
        spec_store_step(
            store,
            ProcessEvent::Receive {
                sender,
                message: Message::StoreReq { op, request },
            },
        ) == seq![fresh_store_delivery_result(
            store,
            sender,
            op,
            request,
        )],
{
}

/// Lift one fresh production Store request through Rover once its exact
/// hidden envelope is present.
pub proof fn lemma_fresh_store_rover_step(
    config: crate::Config,
    before: World<ProductionModel>,
    store_slot: int,
    at: u64,
    sender: Pid,
    op: u64,
    request: StoreReq,
)
    requires
        before.now <= at,
        0 <= store_slot < before.process.len(),
        before.process[store_slot].0 == Pid::Store,
        before.process[store_slot].1 is Store,
        event_valid(
            before,
            Pid::Store,
            ProcessEvent::Receive {
                sender,
                message: Message::StoreReq { op, request },
            },
        ),
        !before.process[
            store_slot
        ].1->Store_0.seen.contains((sender, op)),
    ensures
        ({
            let store = before.process[store_slot].1->Store_0;
            let event = ProcessEvent::Receive {
                sender,
                message: Message::StoreReq { op, request },
            };
            let result = fresh_store_delivery_result(
                store,
                sender,
                op,
                request,
            );
            step(
                ProductionModel,
                config,
                before,
                Label::Process {
                    process: Pid::Store,
                    at,
                    event,
                    send: result.send,
                },
                land(before, store_slot, Pid::Store, at, result),
            )
        }),
{
    let store = before.process[store_slot].1->Store_0;
    let event = ProcessEvent::Receive {
        sender,
        message: Message::StoreReq { op, request },
    };
    let result = fresh_store_delivery_result(
        store,
        sender,
        op,
        request,
    );
    lemma_fresh_store_request_delivery(store, sender, op, request);
    assert(is_process(ProductionModel, before, Pid::Store)) by {
        assert(before.process[store_slot].0 == Pid::Store);
    }
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Store,
        before.process[store_slot].1,
        at,
        event,
    ) == seq![result]);
    echod_concrete::simulation::lemma_process_step(
        ProductionModel,
        config,
        before,
        store_slot,
        at,
        event,
        0,
    );
}

/// Lift one exact production Node continuation through Rover once its
/// matching hidden response envelope is present.
pub proof fn lemma_node_rover_step(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    at: u64,
    event: ProcessEvent<Pid, Message>,
    result: StepResultV<LocalV, Pid, Message>,
)
    requires
        before.now <= at,
        0 <= node_slot < before.process.len(),
        before.process[node_slot].0 == Pid::Node(0),
        before.process[node_slot].1 is Node,
        event_valid(before, Pid::Node(0), event),
        spec_node_step(
            before.process[node_slot].1->Node_0,
            at,
            event,
        ) == seq![result],
    ensures
        step(
            ProductionModel,
            config,
            before,
            Label::Process {
                process: Pid::Node(0),
                at,
                event,
                send: result.send,
            },
            land(before, node_slot, Pid::Node(0), at, result),
        ),
{
    assert(is_process(ProductionModel, before, Pid::Node(0))) by {
        assert(before.process[node_slot].0 == Pid::Node(0));
    }
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Node(0),
        before.process[node_slot].1,
        at,
        event,
    ) == seq![result]);
    echod_concrete::simulation::lemma_process_step(
        ProductionModel,
        config,
        before,
        node_slot,
        at,
        event,
        0,
    );
}

/// A real production Node transition changes only its selected local lane.
/// Unrelated concurrent process lanes are byte-for-byte framed, while the
/// network changes only by the exact envelopes emitted by this result.
pub proof fn lemma_node_rover_step_preserves_unrelated_lanes(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    at: u64,
    event: ProcessEvent<Pid, Message>,
    result: StepResultV<LocalV, Pid, Message>,
)
    requires
        before.now <= at,
        0 <= node_slot < before.process.len(),
        before.process[node_slot].0 == Pid::Node(0),
        before.process[node_slot].1 is Node,
        event_valid(before, Pid::Node(0), event),
        spec_node_step(
            before.process[node_slot].1->Node_0,
            at,
            event,
        ) == seq![result],
    ensures
        ({
            let after =
                land(before, node_slot, Pid::Node(0), at, result);
            &&& step(
                ProductionModel,
                config,
                before,
                Label::Process {
                    process: Pid::Node(0),
                    at,
                    event,
                    send: result.send,
                },
                after,
            )
            &&& forall|j: int|
                0 <= j < before.process.len() && j != node_slot
                    ==> #[trigger] after.process[j]
                        == before.process[j]
            &&& after.network == before.network
                + echod_rover::rover::semantics::envelopes(
                    Pid::Node(0),
                    result.send,
                )
        }),
{
    lemma_node_rover_step(
        config,
        before,
        node_slot,
        at,
        event,
        result,
    );
}

/// The production Node adapter exposes a stale Store response as one local
/// stutter result: only the observed clock advances and no envelope is sent.
pub proof fn lemma_stale_store_response_node_step(
    node: NodeV,
    op: u64,
    response: StoreRes,
    at: u64,
)
    requires
        node.core.out.len() == 0,
        node.core.node.members.refreshing(),
        !node.core.loops,
        !node.core.ops.contains_key(op),
    ensures
        spec_node_step(
            node,
            at,
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            },
        ) == seq![StepResultV {
            state: LocalV::Node(NodeV {
                core: S {
                    clock: at,
                    ..node.core
                },
                ..node
            }),
            send: Seq::empty(),
        }],
{
    lemma_stale_store_response_stutters(
        node.core,
        op,
        response,
        at,
    );
    reveal(spec_node_step);
    reveal(spec_effects);
}

/// A stale or duplicate Store response is a real Rover Node step with an
/// empty send set and full framing of every unrelated process lane.
pub proof fn lemma_stale_store_response_rover_step_frames_lanes(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    op: u64,
    response: StoreRes,
    at: u64,
)
    requires
        before.now <= at,
        0 <= node_slot < before.process.len(),
        before.process[node_slot].0 == Pid::Node(0),
        before.process[node_slot].1 is Node,
        before.process[node_slot].1->Node_0.core.out.len() == 0,
        before.process[
            node_slot
        ].1->Node_0.core.node.members.refreshing(),
        !before.process[node_slot].1->Node_0.core.loops,
        !before.process[
            node_slot
        ].1->Node_0.core.ops.contains_key(op),
        event_valid(
            before,
            Pid::Node(0),
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            },
        ),
    ensures
        ({
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            };
            let result = StepResultV {
                state: LocalV::Node(NodeV {
                    core: S {
                        clock: at,
                        ..before.process[node_slot].1->Node_0.core
                    },
                    ..before.process[node_slot].1->Node_0
                }),
                send: Seq::empty(),
            };
            let after =
                land(before, node_slot, Pid::Node(0), at, result);
            &&& step(
                ProductionModel,
                config,
                before,
                Label::Process {
                    process: Pid::Node(0),
                    at,
                    event,
                    send: Seq::empty(),
                },
                after,
            )
            &&& after.network == before.network
            &&& forall|j: int|
                0 <= j < before.process.len() && j != node_slot
                    ==> #[trigger] after.process[j]
                        == before.process[j]
        }),
{
    let node = before.process[node_slot].1->Node_0;
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes { op, response },
    };
    let result = StepResultV {
        state: LocalV::Node(NodeV {
            core: S { clock: at, ..node.core },
            ..node
        }),
        send: Seq::empty(),
    };
    lemma_stale_store_response_node_step(
        node,
        op,
        response,
        at,
    );
    lemma_node_rover_step_preserves_unrelated_lanes(
        config,
        before,
        node_slot,
        at,
        event,
        result,
    );
    assert(echod_rover::rover::semantics::envelopes(
        Pid::Node(0),
        Seq::<(Pid, Message)>::empty(),
    ) =~= Seq::empty());
}

/// Exact production state premises for the retryable write-race branch.
pub open spec fn origin_write_retry_ready(
    node: NodeV,
    fid: u64,
    op: u64,
) -> bool {
    &&& node.core.out.len() == 0
    &&& node.core.node.members.refreshing()
    &&& !node.core.loops
    &&& node.core.ops.contains_key(op)
    &&& node.core.ops[op] == Owner::Flight(fid)
    &&& !node.core.ops.contains_key(node.core.next_op)
    &&& node.core.flights.inflight.contains_key(fid)
    &&& node.core.flights.inflight[fid].id == fid
    &&& node.core.flights.inflight[fid].target is Origin
    &&& node.core.flights.inflight[fid].work is Request
    &&& node.core.flights.inflight[fid].firing is None
    &&& !node.core.flights.inflight[fid].debug
    &&& node.core.flights.inflight[fid].phase is Origin
    &&& node.core.flights.inflight[fid].phase.expects() == Some(op)
    &&& node.core.flights.inflight[
        fid
    ].phase->Origin_commit.seq.step
        == (crate::verified::flight_spec::AStep::Writing {
            idle: false,
        })
    &&& node.core.flights.inflight[
        fid
    ].phase->Origin_commit.issued is Some
    &&& node.core.flights.inflight[
        fid
    ].phase->Origin_commit.issued->Some_0 is Write
    &&& node.core.flights.inflight[
        fid
    ].phase->Origin_commit.issued->Some_0->Write_op == op
    &&& node.core.flights.inflight[fid].attempt < u32::MAX
    &&& node.core.flights.inflight[fid].attempt + 1
        <= node.core.flights.max_retries
    &&& crate::cache::spec_find(
        crate::cache::spec_remove(
            node.core.cache,
            node.core.flights.inflight[fid].target->Origin_0,
        ).entries,
        node.core.flights.inflight[fid].target->Origin_0,
    ) is None
}

/// A retryable CAS race passes through the real Node adapter, emits the exact
/// cache-miss Get, and emits neither a boundary Reply nor an application Send.
pub proof fn lemma_origin_write_precondition_failed_node_reloads(
    node: NodeV,
    fid: u64,
    op: u64,
    at: u64,
)
    requires
        origin_write_retry_ready(node, fid, op),
    ensures
        ({
            let origin =
                node.core.flights.inflight[fid].target->Origin_0;
            let response = StoreRes::PutIfMatch {
                result: Err(StoreError::PreconditionFailed),
            };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            };
            let core = crate::handler::spec_on_event(
                node.core,
                EventSpec::Store { op, response, clock: at },
            ).0;
            &&& spec_node_step(node, at, event)
                == seq![StepResultV {
                    state: LocalV::Node(NodeV { core, ..node }),
                    send: seq![(
                        Pid::Store,
                        Message::StoreReq {
                            op: node.core.next_op,
                            request: spec_store_request(
                                StoreReqSpec::Get {
                                    key: crate::keys::spec_doc_key(
                                        node.core.keys.prefix,
                                        origin,
                                    ),
                                },
                            ),
                        },
                    )],
                }]
            &&& core.flights.inflight.contains_key(fid)
            &&& core.flights.inflight[fid].attempt
                == node.core.flights.inflight[fid].attempt + 1
        }),
{
    lemma_origin_write_precondition_failed_reloads(
        node.core,
        fid,
        op,
        at,
    );
    reveal(spec_node_step);
    reveal_with_fuel(spec_effects, 10);
    reveal(spec_effect);
}

/// The retryable CAS race is one actual Rover Node transition whose only
/// emitted envelope is the hidden reload Get.
pub proof fn lemma_origin_write_precondition_failed_rover_step_reloads(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    fid: u64,
    op: u64,
    at: u64,
)
    requires
        before.now <= at,
        0 <= node_slot < before.process.len(),
        before.process[node_slot].0 == Pid::Node(0),
        before.process[node_slot].1 is Node,
        origin_write_retry_ready(
            before.process[node_slot].1->Node_0,
            fid,
            op,
        ),
        event_valid(
            before,
            Pid::Node(0),
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op,
                    response: StoreRes::PutIfMatch {
                        result: Err(StoreError::PreconditionFailed),
                    },
                },
            },
        ),
    ensures
        ({
            let node = before.process[node_slot].1->Node_0;
            let origin =
                node.core.flights.inflight[fid].target->Origin_0;
            let response = StoreRes::PutIfMatch {
                result: Err(StoreError::PreconditionFailed),
            };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            };
            let core = crate::handler::spec_on_event(
                node.core,
                EventSpec::Store { op, response, clock: at },
            ).0;
            let result = StepResultV {
                state: LocalV::Node(NodeV { core, ..node }),
                send: seq![(
                    Pid::Store,
                    Message::StoreReq {
                        op: node.core.next_op,
                        request: spec_store_request(
                            StoreReqSpec::Get {
                                key: crate::keys::spec_doc_key(
                                    node.core.keys.prefix,
                                    origin,
                                ),
                            },
                        ),
                    },
                )],
            };
            step(
                ProductionModel,
                config,
                before,
                Label::Process {
                    process: Pid::Node(0),
                    at,
                    event,
                    send: result.send,
                },
                land(
                    before,
                    node_slot,
                    Pid::Node(0),
                    at,
                    result,
                ),
            )
        }),
{
    let node = before.process[node_slot].1->Node_0;
    let origin = node.core.flights.inflight[fid].target->Origin_0;
    let response = StoreRes::PutIfMatch {
        result: Err(StoreError::PreconditionFailed),
    };
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes { op, response },
    };
    let core = crate::handler::spec_on_event(
        node.core,
        EventSpec::Store { op, response, clock: at },
    ).0;
    let result = StepResultV {
        state: LocalV::Node(NodeV { core, ..node }),
        send: seq![(
            Pid::Store,
            Message::StoreReq {
                op: node.core.next_op,
                request: spec_store_request(StoreReqSpec::Get {
                    key: crate::keys::spec_doc_key(
                        node.core.keys.prefix,
                        origin,
                    ),
                }),
            },
        )],
    };
    lemma_origin_write_precondition_failed_node_reloads(
        node,
        fid,
        op,
        at,
    );
    lemma_node_rover_step(
        config,
        before,
        node_slot,
        at,
        event,
        result,
    );
}

/// The emitted retry Get is delivered by an actual hidden Store lane step.
/// The executable request is tied explicitly to the production document key.
pub proof fn lemma_origin_retry_reload_store_delivery_rover_step(
    config: crate::Config,
    before: World<ProductionModel>,
    store_slot: int,
    sender: Pid,
    reload_op: u64,
    origin: Seq<char>,
    prefix: Seq<char>,
    request: StoreReq,
    at: u64,
)
    requires
        before.now <= at,
        0 <= store_slot < before.process.len(),
        before.process[store_slot].0 == Pid::Store,
        before.process[store_slot].1 is Store,
        request.deep_view() == (StoreReqSpec::Get {
            key: crate::keys::spec_doc_key(prefix, origin),
        }),
        event_valid(
            before,
            Pid::Store,
            ProcessEvent::Receive {
                sender,
                message: Message::StoreReq {
                    op: reload_op,
                    request,
                },
            },
        ),
        !before.process[
            store_slot
        ].1->Store_0.seen.contains((sender, reload_op)),
    ensures
        ({
            let store = before.process[store_slot].1->Store_0;
            let event = ProcessEvent::Receive {
                sender,
                message: Message::StoreReq {
                    op: reload_op,
                    request,
                },
            };
            let result = fresh_store_delivery_result(
                store,
                sender,
                reload_op,
                request,
            );
            step(
                ProductionModel,
                config,
                before,
                Label::Process {
                    process: Pid::Store,
                    at,
                    event,
                    send: result.send,
                },
                land(
                    before,
                    store_slot,
                    Pid::Store,
                    at,
                    result,
                ),
            )
        }),
{
    lemma_fresh_store_rover_step(
        config,
        before,
        store_slot,
        at,
        sender,
        reload_op,
        request,
    );
}

/// The matching successful reload response is interpreted by the real Node
/// adapter as the newly re-decided conditional write and nothing else.
#[verifier::rlimit(40)]
pub proof fn lemma_origin_retry_reload_success_node_issues_put_if_match(
    node: NodeV,
    fid: u64,
    reload_op: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    request_at: u64,
    response_at: u64,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
)
    requires
        request_at <= response_at,
        crate::rover::spec_target(call.request)
            == Some(TargetSpec::Origin(origin)),
        spec_decode_workflow(bytes@) == Ok(loaded),
        origin_retry_reload_write_ready(
            node.core,
            fid,
            reload_op,
            spec_call(
                call,
                TargetSpec::Origin(origin),
                request_at,
            ),
            origin,
            loaded,
            etag,
        ),
    ensures
        ({
            let response = StoreRes::Get {
                result: Ok(Some((bytes, etag))),
            };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: reload_op,
                    response,
                },
            };
            let core = crate::handler::spec_on_event(
                node.core,
                EventSpec::Store {
                    op: reload_op,
                    response,
                    clock: response_at,
                },
            ).0;
            let (after_body, _, _, _) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(loaded.document),
                    call.request,
                    request_at,
                    node.core.cfg.retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                );
            let after_document =
                echod_concrete::node::spec_advance_stored(
                    loaded.document,
                    after_body,
                    request_at,
                );
            &&& spec_node_step(node, response_at, event)
                == seq![StepResultV {
                    state: LocalV::Node(NodeV { core, ..node }),
                    send: seq![(
                        Pid::Store,
                        Message::StoreReq {
                            op: node.core.next_op,
                            request: spec_store_request(
                                StoreReqSpec::PutIfMatch {
                                    key: crate::keys::spec_doc_key(
                                        node.core.keys.prefix,
                                        origin,
                                    ),
                                    body: spec_encode(after_document),
                                    etag: etag.deep_view(),
                                },
                            ),
                        },
                    )],
                }]
            &&& well_formed(after_document)
        }),
{
    lemma_origin_retry_reload_success_issues_put_if_match(
        node.core,
        fid,
        reload_op,
        spec_call(
            call,
            TargetSpec::Origin(origin),
            request_at,
        ),
        origin,
        response_at,
        bytes,
        etag,
        loaded,
    );
    reveal(spec_node_step);
    reveal_with_fuel(spec_effects, 8);
    reveal(spec_effect);
}

/// The successful reload/redecision is an actual Rover Node transition that
/// emits exactly the next hidden `PutIfMatch`.
pub proof fn lemma_origin_retry_reload_success_rover_step_issues_put_if_match(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    fid: u64,
    reload_op: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    request_at: u64,
    response_at: u64,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
)
    requires
        before.now <= response_at,
        0 <= node_slot < before.process.len(),
        before.process[node_slot].0 == Pid::Node(0),
        before.process[node_slot].1 is Node,
        request_at <= response_at,
        crate::rover::spec_target(call.request)
            == Some(TargetSpec::Origin(origin)),
        spec_decode_workflow(bytes@) == Ok(loaded),
        origin_retry_reload_write_ready(
            before.process[node_slot].1->Node_0.core,
            fid,
            reload_op,
            spec_call(
                call,
                TargetSpec::Origin(origin),
                request_at,
            ),
            origin,
            loaded,
            etag,
        ),
        event_valid(
            before,
            Pid::Node(0),
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: reload_op,
                    response: StoreRes::Get {
                        result: Ok(Some((bytes, etag))),
                    },
                },
            },
        ),
    ensures
        ({
            let node = before.process[node_slot].1->Node_0;
            let response = StoreRes::Get {
                result: Ok(Some((bytes, etag))),
            };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: reload_op,
                    response,
                },
            };
            let core = crate::handler::spec_on_event(
                node.core,
                EventSpec::Store {
                    op: reload_op,
                    response,
                    clock: response_at,
                },
            ).0;
            let (after_body, _, _, _) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(loaded.document),
                    call.request,
                    request_at,
                    node.core.cfg.retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                );
            let after_document =
                echod_concrete::node::spec_advance_stored(
                    loaded.document,
                    after_body,
                    request_at,
                );
            let result = StepResultV {
                state: LocalV::Node(NodeV { core, ..node }),
                send: seq![(
                    Pid::Store,
                    Message::StoreReq {
                        op: node.core.next_op,
                        request: spec_store_request(
                            StoreReqSpec::PutIfMatch {
                                key: crate::keys::spec_doc_key(
                                    node.core.keys.prefix,
                                    origin,
                                ),
                                body: spec_encode(after_document),
                                etag: etag.deep_view(),
                            },
                        ),
                    },
                )],
            };
            step(
                ProductionModel,
                config,
                before,
                Label::Process {
                    process: Pid::Node(0),
                    at: response_at,
                    event,
                    send: result.send,
                },
                land(
                    before,
                    node_slot,
                    Pid::Node(0),
                    response_at,
                    result,
                ),
            )
        }),
{
    let node = before.process[node_slot].1->Node_0;
    let response = StoreRes::Get {
        result: Ok(Some((bytes, etag))),
    };
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes {
            op: reload_op,
            response,
        },
    };
    let core = crate::handler::spec_on_event(
        node.core,
        EventSpec::Store {
            op: reload_op,
            response,
            clock: response_at,
        },
    ).0;
    let (after_body, _, _, _) =
        echod_concrete::node::spec_request_transition(
            spec_stored_body(loaded.document),
            call.request,
            request_at,
            node.core.cfg.retry_timeout,
            REQUEST_SWEEP_STEPS as nat,
        );
    let after_document =
        echod_concrete::node::spec_advance_stored(
            loaded.document,
            after_body,
            request_at,
        );
    let result = StepResultV {
        state: LocalV::Node(NodeV { core, ..node }),
        send: seq![(
            Pid::Store,
            Message::StoreReq {
                op: node.core.next_op,
                request: spec_store_request(
                    StoreReqSpec::PutIfMatch {
                        key: crate::keys::spec_doc_key(
                            node.core.keys.prefix,
                            origin,
                        ),
                        body: spec_encode(after_document),
                        etag: etag.deep_view(),
                    },
                ),
            },
        )],
    };
    lemma_origin_retry_reload_success_node_issues_put_if_match(
        node,
        fid,
        reload_op,
        call,
        origin,
        request_at,
        response_at,
        bytes,
        etag,
        loaded,
    );
    lemma_node_rover_step(
        config,
        before,
        node_slot,
        response_at,
        event,
        result,
    );
}

/// From a world where the raced write has emitted its reload Get, this
/// bounded slice proves the actual hidden Store delivery followed by the
/// matching successful Node reload/redecision. All key, decode, freshness,
/// response, and envelope-validity facts are explicit premises.
pub proof fn lemma_origin_retry_reload_delivery_and_redecision_rover_steps(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    store_slot: int,
    fid: u64,
    reload_op: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    request_at: u64,
    store_at: u64,
    response_at: u64,
    request: StoreReq,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
)
    requires
        before.now <= store_at <= response_at,
        0 <= node_slot < before.process.len(),
        0 <= store_slot < before.process.len(),
        node_slot != store_slot,
        before.process[node_slot].0 == Pid::Node(0),
        before.process[node_slot].1 is Node,
        before.process[store_slot].0 == Pid::Store,
        before.process[store_slot].1 is Store,
        request_at <= response_at,
        crate::rover::spec_target(call.request)
            == Some(TargetSpec::Origin(origin)),
        request.deep_view() == (StoreReqSpec::Get {
            key: crate::keys::spec_doc_key(
                before.process[
                    node_slot
                ].1->Node_0.core.keys.prefix,
                origin,
            ),
        }),
        spec_decode_workflow(bytes@) == Ok(loaded),
        origin_retry_reload_write_ready(
            before.process[node_slot].1->Node_0.core,
            fid,
            reload_op,
            spec_call(
                call,
                TargetSpec::Origin(origin),
                request_at,
            ),
            origin,
            loaded,
            etag,
        ),
        event_valid(
            before,
            Pid::Store,
            ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: Message::StoreReq {
                    op: reload_op,
                    request,
                },
            },
        ),
        !before.process[
            store_slot
        ].1->Store_0.seen.contains((Pid::Node(0), reload_op)),
        spec_apply(
            before.process[store_slot].1->Store_0,
            request,
        ).1 == (StoreRes::Get {
            result: Ok(Some((bytes, etag))),
        }),
        ({
            let store = before.process[store_slot].1->Store_0;
            let store_result = fresh_store_delivery_result(
                store,
                Pid::Node(0),
                reload_op,
                request,
            );
            let delivered = land(
                before,
                store_slot,
                Pid::Store,
                store_at,
                store_result,
            );
            event_valid(
                delivered,
                Pid::Node(0),
                ProcessEvent::Receive {
                    sender: Pid::Store,
                    message: Message::StoreRes {
                        op: reload_op,
                        response: StoreRes::Get {
                            result: Ok(Some((bytes, etag))),
                        },
                    },
                },
            )
        }),
    ensures
        ({
            let node = before.process[node_slot].1->Node_0;
            let store = before.process[store_slot].1->Store_0;
            let store_event = ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: Message::StoreReq {
                    op: reload_op,
                    request,
                },
            };
            let store_result = fresh_store_delivery_result(
                store,
                Pid::Node(0),
                reload_op,
                request,
            );
            let delivered = land(
                before,
                store_slot,
                Pid::Store,
                store_at,
                store_result,
            );
            let response = StoreRes::Get {
                result: Ok(Some((bytes, etag))),
            };
            let node_event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: reload_op,
                    response,
                },
            };
            let core = crate::handler::spec_on_event(
                node.core,
                EventSpec::Store {
                    op: reload_op,
                    response,
                    clock: response_at,
                },
            ).0;
            let (after_body, _, _, _) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(loaded.document),
                    call.request,
                    request_at,
                    node.core.cfg.retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                );
            let after_document =
                echod_concrete::node::spec_advance_stored(
                    loaded.document,
                    after_body,
                    request_at,
                );
            let node_result = StepResultV {
                state: LocalV::Node(NodeV { core, ..node }),
                send: seq![(
                    Pid::Store,
                    Message::StoreReq {
                        op: node.core.next_op,
                        request: spec_store_request(
                            StoreReqSpec::PutIfMatch {
                                key: crate::keys::spec_doc_key(
                                    node.core.keys.prefix,
                                    origin,
                                ),
                                body: spec_encode(after_document),
                                etag: etag.deep_view(),
                            },
                        ),
                    },
                )],
            };
            &&& step(
                ProductionModel,
                config,
                before,
                Label::Process {
                    process: Pid::Store,
                    at: store_at,
                    event: store_event,
                    send: store_result.send,
                },
                delivered,
            )
            &&& step(
                ProductionModel,
                config,
                delivered,
                Label::Process {
                    process: Pid::Node(0),
                    at: response_at,
                    event: node_event,
                    send: node_result.send,
                },
                land(
                    delivered,
                    node_slot,
                    Pid::Node(0),
                    response_at,
                    node_result,
                ),
            )
        }),
{
    let node = before.process[node_slot].1->Node_0;
    let store = before.process[store_slot].1->Store_0;
    let store_result = fresh_store_delivery_result(
        store,
        Pid::Node(0),
        reload_op,
        request,
    );
    let delivered = land(
        before,
        store_slot,
        Pid::Store,
        store_at,
        store_result,
    );
    lemma_origin_retry_reload_store_delivery_rover_step(
        config,
        before,
        store_slot,
        Pid::Node(0),
        reload_op,
        origin,
        node.core.keys.prefix,
        request,
        store_at,
    );
    assert(delivered.process[node_slot] == before.process[node_slot]);
    assert(delivered.process[node_slot].1->Node_0 == node);
    lemma_origin_retry_reload_success_rover_step_issues_put_if_match(
        config,
        delivered,
        node_slot,
        fid,
        reload_op,
        call,
        origin,
        request_at,
        response_at,
        bytes,
        etag,
        loaded,
    );
}

/// Exact adapter premises for a normal request waiting on its document CAS.
pub open spec fn origin_write_failure_ready(
    node: NodeV,
    fid: u64,
    op: u64,
    call: BoundaryCall,
) -> bool {
    &&& node.core.out.len() == 0
    &&& node.core.node.members.refreshing()
    &&& !node.core.loops
    &&& node.core.ops.contains_key(op)
    &&& node.core.ops[op] == Owner::Flight(fid)
    &&& node.core.flights.inflight.contains_key(fid)
    &&& node.core.flights.inflight[fid].id == fid
    &&& node.core.flights.inflight[fid].target is Origin
    &&& node.core.flights.inflight[fid].work is Request
    &&& node.core.flights.inflight[fid].work->Request_id == call.id
    &&& node.core.flights.inflight[fid].firing is None
    &&& !node.core.flights.inflight[fid].debug
    &&& node.core.flights.inflight[fid].phase is Origin
    &&& node.core.flights.inflight[fid].phase.expects() == Some(op)
    &&& node.core.flights.inflight[
        fid
    ].phase->Origin_commit.seq.step
        == (crate::verified::flight_spec::AStep::Writing {
            idle: false,
        })
    &&& node.core.flights.inflight[
        fid
    ].phase->Origin_commit.issued is Some
    &&& node.core.flights.inflight[
        fid
    ].phase->Origin_commit.issued->Some_0 is Write
    &&& node.core.flights.inflight[
        fid
    ].phase->Origin_commit.issued->Some_0->Write_op == op
    &&& crate::handler_docs::spec_slot_of(
        node.core,
        crate::target::spec_name(
            node.core.flights.inflight[fid].target,
        ),
    ).busy == Some(fid)
    &&& crate::handler_docs::spec_slot_of(
        node.core,
        crate::target::spec_name(
            node.core.flights.inflight[fid].target,
        ),
    ).queue.len() == 0
    &&& spec_take_pending(node.pending, call.id).0 == Some(call)
}

/// The adapter turns an unavailable CAS answer into exactly one boundary
/// failure response. No application `Message::Send` or Store request escapes.
pub proof fn lemma_origin_write_unavailable_node_replies_once_no_send(
    node: NodeV,
    fid: u64,
    op: u64,
    call: BoundaryCall,
    message: String,
    at: u64,
)
    requires
        origin_write_failure_ready(node, fid, op, call),
    ensures
        ({
            let response = StoreRes::PutIfMatch {
                result: Err(StoreError::Unavailable(message)),
            };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            };
            let core_event = EventSpec::Store {
                op,
                response,
                clock: at,
            };
            let core = crate::handler::spec_on_event(
                node.core,
                core_event,
            ).0;
            let pending = spec_take_pending(node.pending, call.id).1;
            &&& spec_node_step(node, at, event)
                == seq![StepResultV {
                    state: LocalV::Node(NodeV {
                        core,
                        pending,
                        ..node
                    }),
                    send: seq![(
                        Pid::Outside,
                        Message::Reply(Output::Response {
                            client: call.client,
                            id: call.id,
                            response: spec_unavailable(call.request),
                        }),
                    )],
                }]
            &&& !core.ops.contains_key(op)
            &&& !core.flights.inflight.contains_key(fid)
        }),
{
    lemma_origin_write_unavailable_replies_once(
        node.core,
        fid,
        op,
        at,
        message,
    );
    reveal(spec_node_step);
    reveal_with_fuel(spec_effects, 8);
    reveal(spec_effect);
}

/// A wrong-shaped Store answer follows the same one-failure/no-Send adapter
/// path, with the production unexpected-response error.
pub proof fn lemma_origin_write_mismatched_node_replies_once_no_send(
    node: NodeV,
    fid: u64,
    op: u64,
    call: BoundaryCall,
    at: u64,
)
    requires
        origin_write_failure_ready(node, fid, op, call),
    ensures
        ({
            let response = StoreRes::Del { result: Ok(()) };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            };
            let core_event = EventSpec::Store {
                op,
                response,
                clock: at,
            };
            let core = crate::handler::spec_on_event(
                node.core,
                core_event,
            ).0;
            let pending = spec_take_pending(node.pending, call.id).1;
            &&& spec_node_step(node, at, event)
                == seq![StepResultV {
                    state: LocalV::Node(NodeV {
                        core,
                        pending,
                        ..node
                    }),
                    send: seq![(
                        Pid::Outside,
                        Message::Reply(Output::Response {
                            client: call.client,
                            id: call.id,
                            response: spec_unavailable(call.request),
                        }),
                    )],
                }]
            &&& !core.ops.contains_key(op)
            &&& !core.flights.inflight.contains_key(fid)
        }),
{
    lemma_origin_write_mismatched_response_replies_once(
        node.core,
        fid,
        op,
        at,
    );
    reveal(spec_node_step);
    reveal_with_fuel(spec_effects, 8);
    reveal(spec_effect);
}

/// The unavailable-CAS failure is an actual Rover transition carrying one
/// boundary Reply envelope and preserving every unrelated local lane.
pub proof fn lemma_origin_write_unavailable_rover_step_replies_once_no_send(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    fid: u64,
    op: u64,
    call: BoundaryCall,
    message: String,
    at: u64,
)
    requires
        before.now <= at,
        0 <= node_slot < before.process.len(),
        before.process[node_slot].0 == Pid::Node(0),
        before.process[node_slot].1 is Node,
        origin_write_failure_ready(
            before.process[node_slot].1->Node_0,
            fid,
            op,
            call,
        ),
        event_valid(
            before,
            Pid::Node(0),
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op,
                    response: StoreRes::PutIfMatch {
                        result: Err(StoreError::Unavailable(message)),
                    },
                },
            },
        ),
    ensures
        ({
            let node = before.process[node_slot].1->Node_0;
            let response = StoreRes::PutIfMatch {
                result: Err(StoreError::Unavailable(message)),
            };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            };
            let core = crate::handler::spec_on_event(
                node.core,
                EventSpec::Store { op, response, clock: at },
            ).0;
            let result = StepResultV {
                state: LocalV::Node(NodeV {
                    core,
                    pending: spec_take_pending(
                        node.pending,
                        call.id,
                    ).1,
                    ..node
                }),
                send: seq![(
                    Pid::Outside,
                    Message::Reply(Output::Response {
                        client: call.client,
                        id: call.id,
                        response: spec_unavailable(call.request),
                    }),
                )],
            };
            let after = land(
                before,
                node_slot,
                Pid::Node(0),
                at,
                result,
            );
            &&& step(
                ProductionModel,
                config,
                before,
                Label::Process {
                    process: Pid::Node(0),
                    at,
                    event,
                    send: result.send,
                },
                after,
            )
            &&& forall|j: int|
                0 <= j < before.process.len() && j != node_slot
                    ==> #[trigger] after.process[j]
                        == before.process[j]
        }),
{
    let node = before.process[node_slot].1->Node_0;
    let response = StoreRes::PutIfMatch {
        result: Err(StoreError::Unavailable(message)),
    };
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes { op, response },
    };
    let core = crate::handler::spec_on_event(
        node.core,
        EventSpec::Store { op, response, clock: at },
    ).0;
    let result = StepResultV {
        state: LocalV::Node(NodeV {
            core,
            pending: spec_take_pending(node.pending, call.id).1,
            ..node
        }),
        send: seq![(
            Pid::Outside,
            Message::Reply(Output::Response {
                client: call.client,
                id: call.id,
                response: spec_unavailable(call.request),
            }),
        )],
    };
    lemma_origin_write_unavailable_node_replies_once_no_send(
        node,
        fid,
        op,
        call,
        message,
        at,
    );
    lemma_node_rover_step_preserves_unrelated_lanes(
        config,
        before,
        node_slot,
        at,
        event,
        result,
    );
}

/// The wrong-shaped Store answer is likewise one actual Rover failure Reply
/// with no application Send and full unrelated-lane framing.
pub proof fn lemma_origin_write_mismatched_rover_step_replies_once_no_send(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    fid: u64,
    op: u64,
    call: BoundaryCall,
    at: u64,
)
    requires
        before.now <= at,
        0 <= node_slot < before.process.len(),
        before.process[node_slot].0 == Pid::Node(0),
        before.process[node_slot].1 is Node,
        origin_write_failure_ready(
            before.process[node_slot].1->Node_0,
            fid,
            op,
            call,
        ),
        event_valid(
            before,
            Pid::Node(0),
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op,
                    response: StoreRes::Del { result: Ok(()) },
                },
            },
        ),
    ensures
        ({
            let node = before.process[node_slot].1->Node_0;
            let response = StoreRes::Del { result: Ok(()) };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            };
            let core = crate::handler::spec_on_event(
                node.core,
                EventSpec::Store { op, response, clock: at },
            ).0;
            let result = StepResultV {
                state: LocalV::Node(NodeV {
                    core,
                    pending: spec_take_pending(
                        node.pending,
                        call.id,
                    ).1,
                    ..node
                }),
                send: seq![(
                    Pid::Outside,
                    Message::Reply(Output::Response {
                        client: call.client,
                        id: call.id,
                        response: spec_unavailable(call.request),
                    }),
                )],
            };
            let after = land(
                before,
                node_slot,
                Pid::Node(0),
                at,
                result,
            );
            &&& step(
                ProductionModel,
                config,
                before,
                Label::Process {
                    process: Pid::Node(0),
                    at,
                    event,
                    send: result.send,
                },
                after,
            )
            &&& forall|j: int|
                0 <= j < before.process.len() && j != node_slot
                    ==> #[trigger] after.process[j]
                        == before.process[j]
        }),
{
    let node = before.process[node_slot].1->Node_0;
    let response = StoreRes::Del { result: Ok(()) };
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes { op, response },
    };
    let core = crate::handler::spec_on_event(
        node.core,
        EventSpec::Store { op, response, clock: at },
    ).0;
    let result = StepResultV {
        state: LocalV::Node(NodeV {
            core,
            pending: spec_take_pending(node.pending, call.id).1,
            ..node
        }),
        send: seq![(
            Pid::Outside,
            Message::Reply(Output::Response {
                client: call.client,
                id: call.id,
                response: spec_unavailable(call.request),
            }),
        )],
    };
    lemma_origin_write_mismatched_node_replies_once_no_send(
        node,
        fid,
        op,
        call,
        at,
    );
    lemma_node_rover_step_preserves_unrelated_lanes(
        config,
        before,
        node_slot,
        at,
        event,
        result,
    );
}

pub open spec fn normal_origin_store_delivery_ready(
    before: World<ProductionModel>,
    at: u64,
    store_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
) -> bool {
    let node = before.process[0].1->Node_0;
    let request = normal_origin_get_request(node, origin);
    &&& normal_origin_slice_ready(before, at, call, origin)
    &&& before.process.len() > 1
    &&& before.process[1].0 == Pid::Store
    &&& before.process[1].1 is Store
    &&& at <= store_at
    &&& !before.process[1].1->Store_0.seen.contains((
        Pid::Node(0),
        node.core.next_op,
    ))
    &&& request.deep_view() == StoreReqSpec::Get {
        key: crate::keys::spec_doc_key(
            node.core.keys.prefix,
            origin,
        ),
    }
}

pub open spec fn normal_origin_store_delivered_world(
    before: World<ProductionModel>,
    at: u64,
    store_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
) -> World<ProductionModel> {
    let node = before.process[0].1->Node_0;
    let store = before.process[1].1->Store_0;
    let request = normal_origin_get_request(node, origin);
    land(
        normal_origin_admitted_world(before, at, call, origin),
        1,
        Pid::Store,
        store_at,
        fresh_store_delivery_result(
            store,
            Pid::Node(0),
            node.core.next_op,
            request,
        ),
    )
}

/// The first two real Rover process transitions: Node admission emits the
/// hidden Get, then the production Store consumes that exact envelope.
pub open spec fn normal_origin_get_store_delivery_rover_steps(
    config: crate::Config,
    before: World<ProductionModel>,
    at: u64,
    store_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
) -> bool {
    let node = before.process[0].1->Node_0;
    let store = before.process[1].1->Store_0;
    let request = normal_origin_get_request(node, origin);
    let admitted =
        normal_origin_admitted_world(before, at, call, origin);
    let store_result = fresh_store_delivery_result(
        store,
        Pid::Node(0),
        node.core.next_op,
        request,
    );
    let delivered = normal_origin_store_delivered_world(
        before,
        at,
        store_at,
        call,
        origin,
    );
    &&& normal_origin_store_delivery_ready(
        before,
        at,
        store_at,
        call,
        origin,
    )
    &&& normal_origin_request_rover_step(
        config,
        before,
        at,
        call,
        origin,
        admitted,
    )
    &&& step(
        ProductionModel,
        config,
        admitted,
        Label::Process {
            process: Pid::Store,
            at: store_at,
            event: ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: Message::StoreReq {
                    op: node.core.next_op,
                    request,
                },
            },
            send: store_result.send,
        },
        delivered,
    )
}

#[verifier::rlimit(30)]
pub proof fn lemma_normal_origin_get_store_delivery_rover_steps(
    config: crate::Config,
    before: World<ProductionModel>,
    at: u64,
    store_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
)
    requires
        normal_origin_store_delivery_ready(
            before,
            at,
            store_at,
            call,
            origin,
        ),
    ensures
        normal_origin_get_store_delivery_rover_steps(
            config,
            before,
            at,
            store_at,
            call,
            origin,
        ),
{
    let node = before.process[0].1->Node_0;
    let store = before.process[1].1->Store_0;
    let request = normal_origin_get_request(node, origin);
    let admitted =
        normal_origin_admitted_world(before, at, call, origin);
    let admission_result =
        normal_origin_admission_result(node, at, call, origin);
    let result = fresh_store_delivery_result(
        store,
        Pid::Node(0),
        node.core.next_op,
        request,
    );
    let envelope = echod_rover::rover::Envelope {
        sender: Pid::Node(0),
        recipient: Pid::Store,
        message: Message::StoreReq {
            op: node.core.next_op,
            request,
        },
    };
    lemma_normal_origin_request_rover_step(
        config,
        before,
        at,
        call,
        origin,
    );
    lemma_fresh_store_request_delivery(
        store,
        Pid::Node(0),
        node.core.next_op,
        request,
    );
    assert(admission_result.send == seq![(
        Pid::Store,
        Message::StoreReq {
            op: node.core.next_op,
            request,
        },
    )]);
    assert(echod_rover::rover::semantics::envelopes(
        Pid::Node(0),
        admission_result.send,
    ) =~= seq![envelope]);
    assert(admitted.network == before.network + seq![envelope]);
    let k = before.network.len() as int;
    vstd::seq::lemma_seq_add_index2(
        before.network,
        seq![envelope],
        k,
    );
    assert(admitted.network[k] == envelope);
    assert(event_valid(
        admitted,
        Pid::Store,
        ProcessEvent::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq {
                op: node.core.next_op,
                request,
            },
        },
    ));
    assert(is_process(ProductionModel, admitted, Pid::Store)) by {
        assert(admitted.process[1].0 == Pid::Store);
    }
    assert(admitted.process[1] == before.process[1]);
    assert(admitted.process[1].1 == LocalV::Store(store));
    let store_event = ProcessEvent::Receive {
        sender: Pid::Node(0),
        message: Message::StoreReq {
            op: node.core.next_op,
            request,
        },
    };
    assert(spec_store_step(store, store_event) == seq![result]);
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Store,
        admitted.process[1].1,
        store_at,
        store_event,
    ) == seq![result]);
    assert(0 <= 1int < admitted.process.len());
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Store,
        admitted.process[1].1,
        store_at,
        store_event,
    ).len() == 1);
    echod_concrete::simulation::lemma_process_step(
        ProductionModel,
        config,
        admitted,
        1,
        store_at,
        store_event,
        0,
    );
    assert(normal_origin_store_delivered_world(
        before,
        at,
        store_at,
        call,
        origin,
    ) == land(
        admitted,
        1,
        Pid::Store,
        store_at,
        result,
    ));
}

pub open spec fn normal_origin_get_response_result(
    node: NodeV,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    response_at: u64,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
) -> StepResultV<LocalV, Pid, Message> {
    let admitted =
        normal_origin_admission_result(node, at, call, origin)
            .state->Node_0;
    let event = EventSpec::Store {
        op: node.core.next_op,
        response: StoreRes::Get {
            result: Ok(Some((bytes, etag))),
        },
        clock: response_at,
    };
    let (core, _) = crate::handler::spec_on_event(admitted.core, event);
    let process_call =
        spec_call(call, TargetSpec::Origin(origin), at);
    let (after_body, _, _, _) =
        echod_concrete::node::spec_request_transition(
            spec_stored_body(loaded.document),
            process_call.request,
            at,
            node.core.cfg.retry_timeout,
            REQUEST_SWEEP_STEPS as nat,
        );
    let after_document = echod_concrete::node::spec_advance_stored(
        loaded.document,
        after_body,
        at,
    );
    let write = StoreReqSpec::PutIfMatch {
        key: crate::keys::spec_doc_key(
            node.core.keys.prefix,
            origin,
        ),
        body: spec_encode(after_document),
        etag: etag.deep_view(),
    };
    StepResultV {
        state: LocalV::Node(NodeV {
            core,
            pending: admitted.pending,
            wake: admitted.wake,
        }),
        send: seq![(
            Pid::Store,
            Message::StoreReq {
                op: node.core.next_op.wrapping_add(1),
                request: spec_store_request(write),
            },
        )],
    }
}

/// The Node continuation for the matching successful Get StoreRes. It uses
/// the same production `spec_on_event` and adapter effect interpretation as
/// executable `Node::step`.
pub proof fn lemma_normal_origin_successful_get_node_step(
    node: NodeV,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    response_at: u64,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
)
    requires
        at <= response_at,
        crate::rover::spec_target(call.request)
            == Some(TargetSpec::Origin(origin)),
        spec_decode_workflow(bytes@) == Ok(loaded),
        normal_origin_get_write_ready(
            node.core,
            spec_call(call, TargetSpec::Origin(origin), at),
            origin,
            at,
            loaded,
            etag,
        ),
    ensures
        ({
            let admitted =
                normal_origin_admission_result(node, at, call, origin)
                    .state->Node_0;
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: node.core.next_op,
                    response: StoreRes::Get {
                        result: Ok(Some((bytes, etag))),
                    },
                },
            };
            let result = normal_origin_get_response_result(
                node,
                at,
                call,
                origin,
                response_at,
                bytes,
                etag,
                loaded,
            );
            &&& spec_node_step(admitted, response_at, event)
                == seq![result]
            &&& result.state->Node_0.core.ops.contains_key(
                node.core.next_op.wrapping_add(1),
            )
            &&& result.state->Node_0.core.ops[
                node.core.next_op.wrapping_add(1)
            ] == crate::state::Owner::Flight(node.core.next_flight)
            &&& result.state->Node_0.core.flights.inflight.contains_key(
                node.core.next_flight,
            )
            &&& result.state->Node_0.core.flights.inflight[
                node.core.next_flight
            ].phase is Origin
            &&& well_formed(
                result.state->Node_0.core.flights.inflight[
                    node.core.next_flight
                ].phase->Origin_commit.after,
            )
        }),
{
    let process_call =
        spec_call(call, TargetSpec::Origin(origin), at);
    lemma_normal_origin_successful_get_issues_put_if_match(
        node.core,
        process_call,
        origin,
        at,
        response_at,
        bytes,
        etag,
        loaded,
    );
    reveal(spec_node_step);
    reveal_with_fuel(spec_effects, 3);
    reveal(spec_effect);
}

pub open spec fn normal_origin_get_to_write_ready(
    before: World<ProductionModel>,
    at: u64,
    store_at: u64,
    response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
) -> bool {
    let node = before.process[0].1->Node_0;
    let store = before.process[1].1->Store_0;
    let request = normal_origin_get_request(node, origin);
    &&& normal_origin_store_delivery_ready(
        before,
        at,
        store_at,
        call,
        origin,
    )
    &&& store_at <= response_at
    &&& spec_apply(store, request).1 == StoreRes::Get {
        result: Ok(Some((bytes, etag))),
    }
    &&& spec_decode_workflow(bytes@) == Ok(loaded)
    &&& normal_origin_get_write_ready(
        node.core,
        spec_call(call, TargetSpec::Origin(origin), at),
        origin,
        at,
        loaded,
        etag,
    )
}

pub open spec fn normal_origin_write_issued_world(
    before: World<ProductionModel>,
    at: u64,
    store_at: u64,
    response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
) -> World<ProductionModel> {
    land(
        normal_origin_store_delivered_world(
            before,
            at,
            store_at,
            call,
            origin,
        ),
        0,
        Pid::Node(0),
        response_at,
        normal_origin_get_response_result(
            before.process[0].1->Node_0,
            at,
            call,
            origin,
            response_at,
            bytes,
            etag,
            loaded,
        ),
    )
}

/// Three real hidden Rover process transitions, from external request
/// admission through Store Get delivery and the matching successful Get
/// response, ending when the Node emits its `PutIfMatch`.
pub open spec fn normal_origin_get_to_conditional_write_rover_steps(
    config: crate::Config,
    before: World<ProductionModel>,
    at: u64,
    store_at: u64,
    response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
) -> bool {
    let node = before.process[0].1->Node_0;
    let delivered = normal_origin_store_delivered_world(
        before,
        at,
        store_at,
        call,
        origin,
    );
    let result = normal_origin_get_response_result(
        node,
        at,
        call,
        origin,
        response_at,
        bytes,
        etag,
        loaded,
    );
    let response = StoreRes::Get {
        result: Ok(Some((bytes, etag))),
    };
    &&& normal_origin_get_to_write_ready(
        before,
        at,
        store_at,
        response_at,
        call,
        origin,
        bytes,
        etag,
        loaded,
    )
    &&& normal_origin_get_store_delivery_rover_steps(
        config,
        before,
        at,
        store_at,
        call,
        origin,
    )
    &&& step(
        ProductionModel,
        config,
        delivered,
        Label::Process {
            process: Pid::Node(0),
            at: response_at,
            event: ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: node.core.next_op,
                    response,
                },
            },
            send: result.send,
        },
        normal_origin_write_issued_world(
            before,
            at,
            store_at,
            response_at,
            call,
            origin,
            bytes,
            etag,
            loaded,
        ),
    )
}

#[verifier::rlimit(40)]
pub proof fn lemma_normal_origin_get_to_conditional_write_rover_steps(
    config: crate::Config,
    before: World<ProductionModel>,
    at: u64,
    store_at: u64,
    response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
)
    requires
        normal_origin_get_to_write_ready(
            before,
            at,
            store_at,
            response_at,
            call,
            origin,
            bytes,
            etag,
            loaded,
        ),
    ensures
        normal_origin_get_to_conditional_write_rover_steps(
            config,
            before,
            at,
            store_at,
            response_at,
            call,
            origin,
            bytes,
            etag,
            loaded,
        ),
{
    let node = before.process[0].1->Node_0;
    let store = before.process[1].1->Store_0;
    let request = normal_origin_get_request(node, origin);
    let admitted =
        normal_origin_admitted_world(before, at, call, origin);
    let delivered = normal_origin_store_delivered_world(
        before,
        at,
        store_at,
        call,
        origin,
    );
    let result = normal_origin_get_response_result(
        node,
        at,
        call,
        origin,
        response_at,
        bytes,
        etag,
        loaded,
    );
    let response = StoreRes::Get {
        result: Ok(Some((bytes, etag))),
    };
    let store_result = fresh_store_delivery_result(
        store,
        Pid::Node(0),
        node.core.next_op,
        request,
    );
    let response_envelope = echod_rover::rover::Envelope {
        sender: Pid::Store,
        recipient: Pid::Node(0),
        message: Message::StoreRes {
            op: node.core.next_op,
            response,
        },
    };
    lemma_normal_origin_get_store_delivery_rover_steps(
        config,
        before,
        at,
        store_at,
        call,
        origin,
    );
    lemma_normal_origin_successful_get_node_step(
        node,
        at,
        call,
        origin,
        response_at,
        bytes,
        etag,
        loaded,
    );
    lemma_normal_origin_successful_get_issues_put_if_match(
        node.core,
        spec_call(call, TargetSpec::Origin(origin), at),
        origin,
        at,
        response_at,
        bytes,
        etag,
        loaded,
    );
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes {
            op: node.core.next_op,
            response,
        },
    };
    assert(spec_apply(store, request).1 == response);
    assert(store_result.send == seq![(
        Pid::Node(0),
        Message::StoreRes {
            op: node.core.next_op,
            response,
        },
    )]);
    assert(echod_rover::rover::semantics::envelopes(
        Pid::Store,
        store_result.send,
    ) =~= seq![response_envelope]);
    assert(delivered.network
        == admitted.network + seq![response_envelope]);
    let response_index = admitted.network.len() as int;
    vstd::seq::lemma_seq_add_index2(
        admitted.network,
        seq![response_envelope],
        response_index,
    );
    assert(delivered.network[response_index] == response_envelope);
    assert(event_valid(
        delivered,
        Pid::Node(0),
        event,
    ));
    assert(delivered.process[0].0 == Pid::Node(0));
    assert(is_process(
        ProductionModel,
        delivered,
        Pid::Node(0),
    )) by {
        assert(delivered.process[0].0 == Pid::Node(0));
    }
    assert(delivered.process[0].1
        == normal_origin_admission_result(
            node,
            at,
            call,
            origin,
        ).state);
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Node(0),
        delivered.process[0].1,
        response_at,
        event,
    ) == seq![result]);
    echod_concrete::simulation::lemma_process_step(
        ProductionModel,
        config,
        delivered,
        0,
        response_at,
        event,
        0,
    );
    assert(normal_origin_write_issued_world(
        before,
        at,
        store_at,
        response_at,
        call,
        origin,
        bytes,
        etag,
        loaded,
    ) == land(
        delivered,
        0,
        Pid::Node(0),
        response_at,
        result,
    ));
}

pub open spec fn normal_origin_put_request(
    node: NodeV,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    loaded: LoadedSpec,
    etag: Etag,
) -> StoreReq {
    let process_call =
        spec_call(call, TargetSpec::Origin(origin), at);
    let (after_body, _, _, _) =
        echod_concrete::node::spec_request_transition(
            spec_stored_body(loaded.document),
            process_call.request,
            at,
            node.core.cfg.retry_timeout,
            REQUEST_SWEEP_STEPS as nat,
        );
    let after_document = echod_concrete::node::spec_advance_stored(
        loaded.document,
        after_body,
        at,
    );
    spec_store_request(StoreReqSpec::PutIfMatch {
        key: crate::keys::spec_doc_key(
            node.core.keys.prefix,
            origin,
        ),
        body: spec_encode(after_document),
        etag: etag.deep_view(),
    })
}

pub open spec fn normal_origin_write_response_result(
    issued: NodeV,
    op: u64,
    response_at: u64,
    written_etag: Etag,
) -> StepResultV<LocalV, Pid, Message> {
    let event = EventSpec::Store {
        op,
        response: StoreRes::PutIfMatch {
            result: Ok(written_etag),
        },
        clock: response_at,
    };
    let (core, effects) =
        crate::handler::spec_on_event(issued.core, event);
    let (node, send) = spec_effects(
        NodeV { core, ..issued },
        response_at,
        effects,
    );
    StepResultV {
        state: LocalV::Node(node),
        send,
    }
}

pub open spec fn normal_origin_delete_response_result(
    waiting: NodeV,
    op: u64,
    response_at: u64,
) -> StepResultV<LocalV, Pid, Message> {
    let event = EventSpec::Store {
        op,
        response: StoreRes::Del { result: Ok(()) },
        clock: response_at,
    };
    let (core, effects) =
        crate::handler::spec_on_event(waiting.core, event);
    let (node, send) = spec_effects(
        NodeV { core, ..waiting },
        response_at,
        effects,
    );
    StepResultV {
        state: LocalV::Node(node),
        send,
    }
}

/// The successful CAS response is the final production Node continuation
/// when the commit has no previous deadline key.
#[verifier::rlimit(40)]
pub proof fn lemma_normal_origin_direct_write_response_node_step(
    node: NodeV,
    at: u64,
    get_response_at: u64,
    write_response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
    written_etag: Etag,
)
    requires
        at <= get_response_at <= write_response_at,
        pending_id_fresh(node.pending, call.id),
        crate::rover::spec_target(call.request)
            == Some(TargetSpec::Origin(origin)),
        spec_decode_workflow(bytes@) == Ok(loaded),
        normal_origin_get_write_ready(
            node.core,
            spec_call(call, TargetSpec::Origin(origin), at),
            origin,
            at,
            loaded,
            etag,
        ),
        normal_origin_previous_deadline_key(
            node.core,
            spec_call(call, TargetSpec::Origin(origin), at),
            origin,
            at,
            get_response_at,
            bytes,
            etag,
        ) is None,
    ensures
        ({
            let issued = normal_origin_get_response_result(
                node,
                at,
                call,
                origin,
                get_response_at,
                bytes,
                etag,
                loaded,
            ).state->Node_0;
            let op = node.core.next_op.wrapping_add(1);
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op,
                    response: StoreRes::PutIfMatch {
                        result: Ok(written_etag),
                    },
                },
            };
            let result = normal_origin_write_response_result(
                issued,
                op,
                write_response_at,
                written_etag,
            );
            let (_, response, _, _) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(loaded.document),
                    call.request,
                    at,
                    node.core.cfg.retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                );
            &&& spec_node_step(issued, write_response_at, event)
                == seq![result]
            &&& result.send.len() > 0
            &&& result.send.last() == (
                Pid::Outside,
                Message::Reply(Output::Response {
                    client: call.client,
                    id: call.id,
                    response,
                }),
            )
        }),
{
    lemma_normal_origin_successful_get_node_step(
        node,
        at,
        call,
        origin,
        get_response_at,
        bytes,
        etag,
        loaded,
    );
    lemma_normal_origin_successful_get_issues_put_if_match(
        node.core,
        spec_call(call, TargetSpec::Origin(origin), at),
        origin,
        at,
        get_response_at,
        bytes,
        etag,
        loaded,
    );
    let issued = normal_origin_get_response_result(
        node,
        at,
        call,
        origin,
        get_response_at,
        bytes,
        etag,
        loaded,
    ).state->Node_0;
    let op = node.core.next_op.wrapping_add(1);
    lemma_successful_origin_write_completes_directly(
        issued.core,
        node.core.next_flight,
        op,
        write_response_at,
        written_etag,
    );
    lemma_take_pending_fresh_push(node.pending, call);
    reveal(spec_node_step);
    reveal(spec_effects);
    reveal(spec_effect);
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes {
            op,
            response: StoreRes::PutIfMatch {
                result: Ok(written_etag),
            },
        },
    };
    let result = normal_origin_write_response_result(
        issued,
        op,
        write_response_at,
        written_etag,
    );
    assert(spec_node_step(issued, write_response_at, event)
        == seq![result]);
    let core_event = EventSpec::Store {
        op,
        response: StoreRes::PutIfMatch {
            result: Ok(written_etag),
        },
        clock: write_response_at,
    };
    let (core, effects) =
        crate::handler::spec_on_event(issued.core, core_event);
    assert(effects.len() > 0);
    assert(no_reply_effects(effects.drop_last()));
    assert(effects.last() == normal_request_reply_effect(
        issued.core.flights.inflight[node.core.next_flight],
        issued.core.flights.inflight[
            node.core.next_flight
        ].phase->Origin_done,
    ));
    let prefix = effects.drop_last();
    let before_effects = NodeV { core, ..issued };
    lemma_no_reply_effects_preserve_pending(
        before_effects,
        write_response_at,
        prefix,
    );
    assert(before_effects.pending
        == node.pending.push((call.id, call)));
    let (before_reply, prefix_send) = spec_effects(
        before_effects,
        write_response_at,
        prefix,
    );
    assert(before_reply.pending
        == node.pending.push((call.id, call)));
    assert(spec_take_pending(before_reply.pending, call.id).0
        == Some(call));
    let (_, response, _, _) =
        echod_concrete::node::spec_request_transition(
            spec_stored_body(loaded.document),
            call.request,
            at,
            node.core.cfg.retry_timeout,
            REQUEST_SWEEP_STEPS as nat,
        );
    assert(effects.last() == crate::types::EffectSpec::Reply {
        id: call.id,
        response: Ok(AnswerSpec::Step {
            kind: Seq::empty(),
            corr: call.client@,
            action_kind: None,
            response,
            why: issued.core.flights.inflight[
                node.core.next_flight
            ].phase->Origin_done.why,
        }),
    });
    assert(spec_effects(before_effects, write_response_at, effects)
        == spec_effect(
            before_reply,
            write_response_at,
            effects.last(),
            prefix_send,
        )) by {
        reveal(spec_effects);
    }
    assert(spec_effect(
        before_reply,
        write_response_at,
        effects.last(),
        prefix_send,
    ).1 == prefix_send.push((
        Pid::Outside,
        Message::Reply(Output::Response {
            client: call.client,
            id: call.id,
            response,
        }),
    ))) by {
        reveal(spec_effect);
    }
    assert(result.send
        == prefix_send.push((
            Pid::Outside,
            Message::Reply(Output::Response {
                client: call.client,
                id: call.id,
                response,
            }),
        )));
    assert(result.send.len() > 0);
    assert(result.send.last() == (
        Pid::Outside,
        Message::Reply(Output::Response {
            client: call.client,
            id: call.id,
            response,
        }),
    ));
}

/// The successful CAS response emits the exact previous-deadline-key delete
/// when the production decision replaced an armed deadline.
#[verifier::rlimit(15)]
pub proof fn lemma_normal_origin_previous_key_write_response_node_step(
    node: NodeV,
    at: u64,
    get_response_at: u64,
    write_response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
    written_etag: Etag,
    previous: AKey,
)
    requires
        at <= get_response_at <= write_response_at,
        pending_id_fresh(node.pending, call.id),
        crate::rover::spec_target(call.request)
            == Some(TargetSpec::Origin(origin)),
        spec_decode_workflow(bytes@) == Ok(loaded),
        normal_origin_get_write_ready(
            node.core,
            spec_call(call, TargetSpec::Origin(origin), at),
            origin,
            at,
            loaded,
            etag,
        ),
        normal_origin_previous_deadline_key(
            node.core,
            spec_call(call, TargetSpec::Origin(origin), at),
            origin,
            at,
            get_response_at,
            bytes,
            etag,
        ) == Some(previous),
    ensures
        ({
            let issued = normal_origin_get_response_result(
                node,
                at,
                call,
                origin,
                get_response_at,
                bytes,
                etag,
                loaded,
            ).state->Node_0;
            let write_op = node.core.next_op.wrapping_add(1);
            let delete_op = node.core.next_op.wrapping_add(2);
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: write_op,
                    response: StoreRes::PutIfMatch {
                        result: Ok(written_etag),
                    },
                },
            };
            let result = normal_origin_write_response_result(
                issued,
                write_op,
                write_response_at,
                written_etag,
            );
            let waiting = result.state->Node_0;
            let delete_name = waiting.core.flights.inflight[
                node.core.next_flight
            ].phase->Origin_commit.issued->Some_0->Key_name;
            &&& spec_node_step(issued, write_response_at, event)
                == seq![result]
            &&& result.send.len() > 0
            &&& result.send.last() == (
                Pid::Store,
                Message::StoreReq {
                    op: delete_op,
                    request: spec_store_request(
                        StoreReqSpec::Del { key: delete_name },
                    ),
                },
            )
        }),
{
    lemma_normal_origin_successful_get_node_step(
        node,
        at,
        call,
        origin,
        get_response_at,
        bytes,
        etag,
        loaded,
    );
    lemma_normal_origin_successful_get_issues_put_if_match(
        node.core,
        spec_call(call, TargetSpec::Origin(origin), at),
        origin,
        at,
        get_response_at,
        bytes,
        etag,
        loaded,
    );
    let issued = normal_origin_get_response_result(
        node,
        at,
        call,
        origin,
        get_response_at,
        bytes,
        etag,
        loaded,
    ).state->Node_0;
    let write_op = node.core.next_op.wrapping_add(1);
    let delete_op = node.core.next_op.wrapping_add(2);
    lemma_successful_origin_write_issues_previous_key_delete(
        issued.core,
        node.core.next_flight,
        write_op,
        write_response_at,
        written_etag,
        previous,
    );
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes {
            op: write_op,
            response: StoreRes::PutIfMatch {
                result: Ok(written_etag),
            },
        },
    };
    let result = normal_origin_write_response_result(
        issued,
        write_op,
        write_response_at,
        written_etag,
    );
    reveal(spec_node_step);
    assert(spec_node_step(issued, write_response_at, event)
        == seq![result]);
    let core_event = EventSpec::Store {
        op: write_op,
        response: StoreRes::PutIfMatch {
            result: Ok(written_etag),
        },
        clock: write_response_at,
    };
    let (core, effects) =
        crate::handler::spec_on_event(issued.core, core_event);
    let waiting = result.state->Node_0;
    lemma_effects_preserve_core(
        NodeV { core, ..issued },
        write_response_at,
        effects,
    );
    assert(waiting.core == core);
    let delete_name = core.flights.inflight[
        node.core.next_flight
    ].phase->Origin_commit.issued->Some_0->Key_name;
    assert(no_reply_effects(effects));
    lemma_no_reply_effects_preserve_pending(
        NodeV { core, ..issued },
        write_response_at,
        effects,
    );
    assert(waiting.pending == issued.pending);
    assert(effects.len() > 0);
    let prefix = effects.drop_last();
    let (before_delete, prefix_send) = spec_effects(
        NodeV { core, ..issued },
        write_response_at,
        prefix,
    );
    assert(spec_effects(
        NodeV { core, ..issued },
        write_response_at,
        effects,
    ) == spec_effect(
        before_delete,
        write_response_at,
        effects.last(),
        prefix_send,
    )) by {
        reveal(spec_effects);
    }
    assert(spec_effect(
        before_delete,
        write_response_at,
        effects.last(),
        prefix_send,
    ).1 == prefix_send.push((
        Pid::Store,
        Message::StoreReq {
            op: delete_op,
            request: spec_store_request(
                StoreReqSpec::Del { key: delete_name },
            ),
        },
    ))) by {
        reveal(spec_effect);
    }
    assert(result.send == prefix_send.push((
        Pid::Store,
        Message::StoreReq {
            op: delete_op,
            request: spec_store_request(
                StoreReqSpec::Del { key: delete_name },
            ),
        },
    )));
    assert(result.send.len() > 0);
    assert(result.send.last() == (
        Pid::Store,
        Message::StoreReq {
            op: delete_op,
            request: spec_store_request(
                StoreReqSpec::Del { key: delete_name },
            ),
        },
    ));
}

/// The matching successful delete response closes the previous-key branch
/// and interprets the production Reply as the original Rover boundary call.
#[verifier::rlimit(50)]
pub proof fn lemma_normal_origin_previous_key_delete_response_node_step(
    node: NodeV,
    at: u64,
    get_response_at: u64,
    write_response_at: u64,
    delete_response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
    written_etag: Etag,
    previous: AKey,
)
    requires
        at <= get_response_at <= write_response_at,
        write_response_at <= delete_response_at,
        pending_id_fresh(node.pending, call.id),
        crate::rover::spec_target(call.request)
            == Some(TargetSpec::Origin(origin)),
        spec_decode_workflow(bytes@) == Ok(loaded),
        normal_origin_get_write_ready(
            node.core,
            spec_call(call, TargetSpec::Origin(origin), at),
            origin,
            at,
            loaded,
            etag,
        ),
        normal_origin_previous_deadline_key(
            node.core,
            spec_call(call, TargetSpec::Origin(origin), at),
            origin,
            at,
            get_response_at,
            bytes,
            etag,
        ) == Some(previous),
    ensures
        ({
            let issued = normal_origin_get_response_result(
                node,
                at,
                call,
                origin,
                get_response_at,
                bytes,
                etag,
                loaded,
            ).state->Node_0;
            let write_op = node.core.next_op.wrapping_add(1);
            let delete_op = node.core.next_op.wrapping_add(2);
            let waiting = normal_origin_write_response_result(
                issued,
                write_op,
                write_response_at,
                written_etag,
            ).state->Node_0;
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: delete_op,
                    response: StoreRes::Del { result: Ok(()) },
                },
            };
            let result = normal_origin_delete_response_result(
                waiting,
                delete_op,
                delete_response_at,
            );
            let (_, response, _, _) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(loaded.document),
                    call.request,
                    at,
                    node.core.cfg.retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                );
            &&& spec_node_step(waiting, delete_response_at, event)
                == seq![result]
            &&& result.send.len() > 0
            &&& result.send.last() == (
                Pid::Outside,
                Message::Reply(Output::Response {
                    client: call.client,
                    id: call.id,
                    response,
                }),
            )
        }),
{
    lemma_normal_origin_previous_key_write_response_node_step(
        node,
        at,
        get_response_at,
        write_response_at,
        call,
        origin,
        bytes,
        etag,
        loaded,
        written_etag,
        previous,
    );
    let issued = normal_origin_get_response_result(
        node,
        at,
        call,
        origin,
        get_response_at,
        bytes,
        etag,
        loaded,
    ).state->Node_0;
    let write_op = node.core.next_op.wrapping_add(1);
    let delete_op = node.core.next_op.wrapping_add(2);
    lemma_normal_origin_successful_get_node_step(
        node,
        at,
        call,
        origin,
        get_response_at,
        bytes,
        etag,
        loaded,
    );
    lemma_normal_origin_successful_get_issues_put_if_match(
        node.core,
        spec_call(call, TargetSpec::Origin(origin), at),
        origin,
        at,
        get_response_at,
        bytes,
        etag,
        loaded,
    );
    lemma_successful_origin_write_issues_previous_key_delete(
        issued.core,
        node.core.next_flight,
        write_op,
        write_response_at,
        written_etag,
        previous,
    );
    let waiting = normal_origin_write_response_result(
        issued,
        write_op,
        write_response_at,
        written_etag,
    ).state->Node_0;
    let write_core_event = EventSpec::Store {
        op: write_op,
        response: StoreRes::PutIfMatch {
            result: Ok(written_etag),
        },
        clock: write_response_at,
    };
    let (waiting_core, write_effects) =
        crate::handler::spec_on_event(issued.core, write_core_event);
    lemma_effects_preserve_core(
        NodeV { core: waiting_core, ..issued },
        write_response_at,
        write_effects,
    );
    lemma_no_reply_effects_preserve_pending(
        NodeV { core: waiting_core, ..issued },
        write_response_at,
        write_effects,
    );
    assert(waiting.core == waiting_core);
    assert(waiting.pending == issued.pending);
    assert(issued.pending == node.pending.push((call.id, call)));
    lemma_successful_previous_key_delete_completes(
        waiting.core,
        node.core.next_flight,
        delete_op,
        delete_response_at,
    );
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes {
            op: delete_op,
            response: StoreRes::Del { result: Ok(()) },
        },
    };
    let result = normal_origin_delete_response_result(
        waiting,
        delete_op,
        delete_response_at,
    );
    reveal(spec_node_step);
    assert(spec_node_step(waiting, delete_response_at, event)
        == seq![result]);
    let core_event = EventSpec::Store {
        op: delete_op,
        response: StoreRes::Del { result: Ok(()) },
        clock: delete_response_at,
    };
    let (core, effects) =
        crate::handler::spec_on_event(waiting.core, core_event);
    assert(effects.len() > 0);
    assert(no_reply_effects(effects.drop_last()));
    let prefix = effects.drop_last();
    let before_effects = NodeV { core, ..waiting };
    lemma_no_reply_effects_preserve_pending(
        before_effects,
        delete_response_at,
        prefix,
    );
    lemma_take_pending_fresh_push(node.pending, call);
    assert(before_effects.pending
        == node.pending.push((call.id, call)));
    let (before_reply, prefix_send) = spec_effects(
        before_effects,
        delete_response_at,
        prefix,
    );
    assert(before_reply.pending
        == node.pending.push((call.id, call)));
    assert(spec_take_pending(before_reply.pending, call.id).0
        == Some(call));
    let (_, response, _, _) =
        echod_concrete::node::spec_request_transition(
            spec_stored_body(loaded.document),
            call.request,
            at,
            node.core.cfg.retry_timeout,
            REQUEST_SWEEP_STEPS as nat,
        );
    assert(effects.last() == crate::types::EffectSpec::Reply {
        id: call.id,
        response: Ok(AnswerSpec::Step {
            kind: Seq::empty(),
            corr: call.client@,
            action_kind: None,
            response,
            why: waiting.core.flights.inflight[
                node.core.next_flight
            ].phase->Origin_done.why,
        }),
    });
    assert(spec_effects(before_effects, delete_response_at, effects)
        == spec_effect(
            before_reply,
            delete_response_at,
            effects.last(),
            prefix_send,
        )) by {
        reveal(spec_effects);
    }
    assert(spec_effect(
        before_reply,
        delete_response_at,
        effects.last(),
        prefix_send,
    ).1 == prefix_send.push((
        Pid::Outside,
        Message::Reply(Output::Response {
            client: call.client,
            id: call.id,
            response,
        }),
    ))) by {
        reveal(spec_effect);
    }
    assert(result.send == prefix_send.push((
        Pid::Outside,
        Message::Reply(Output::Response {
            client: call.client,
            id: call.id,
            response,
        }),
    )));
}

pub open spec fn normal_origin_put_delivered_world(
    issued_world: World<ProductionModel>,
    store_at: u64,
    op: u64,
    request: StoreReq,
) -> World<ProductionModel> {
    let store = issued_world.process[1].1->Store_0;
    land(
        issued_world,
        1,
        Pid::Store,
        store_at,
        fresh_store_delivery_result(
            store,
            Pid::Node(0),
            op,
            request,
        ),
    )
}

/// Exact bounded preconditions for the no-previous-key Rover suffix. The
/// starting world is the world that emitted the CAS in the proved Get slice;
/// the two event-valid premises name the actual hidden PutIfMatch and its
/// matching StoreRes envelopes.
pub open spec fn normal_origin_direct_put_completion_ready(
    issued_world: World<ProductionModel>,
    node: NodeV,
    at: u64,
    get_response_at: u64,
    store_at: u64,
    write_response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
    written_etag: Etag,
) -> bool {
    let issued = normal_origin_get_response_result(
        node,
        at,
        call,
        origin,
        get_response_at,
        bytes,
        etag,
        loaded,
    ).state->Node_0;
    let op = node.core.next_op.wrapping_add(1);
    let request = normal_origin_put_request(
        node,
        at,
        call,
        origin,
        loaded,
        etag,
    );
    let store = issued_world.process[1].1->Store_0;
    let delivered = normal_origin_put_delivered_world(
        issued_world,
        store_at,
        op,
        request,
    );
    let response = StoreRes::PutIfMatch {
        result: Ok(written_etag),
    };
    &&& issued_world.process.len() > 1
    &&& issued_world.process[0]
        == (Pid::Node(0), LocalV::Node(issued))
    &&& issued_world.process[1].0 == Pid::Store
    &&& issued_world.process[1].1 is Store
    &&& issued_world.now <= store_at
    &&& store_at <= write_response_at
    &&& at <= get_response_at <= write_response_at
    &&& pending_id_fresh(node.pending, call.id)
    &&& crate::rover::spec_target(call.request)
        == Some(TargetSpec::Origin(origin))
    &&& spec_decode_workflow(bytes@) == Ok(loaded)
    &&& normal_origin_get_write_ready(
        node.core,
        spec_call(call, TargetSpec::Origin(origin), at),
        origin,
        at,
        loaded,
        etag,
    )
    &&& normal_origin_previous_deadline_key(
        node.core,
        spec_call(call, TargetSpec::Origin(origin), at),
        origin,
        at,
        get_response_at,
        bytes,
        etag,
    ) is None
    &&& request.deep_view() == StoreReqSpec::PutIfMatch {
        key: crate::keys::spec_doc_key(node.core.keys.prefix, origin),
        body: spec_encode(
            echod_concrete::node::spec_advance_stored(
                loaded.document,
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(loaded.document),
                    call.request,
                    at,
                    node.core.cfg.retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                ).0,
                at,
            ),
        ),
        etag: etag.deep_view(),
    }
    &&& !store.seen.contains((Pid::Node(0), op))
    &&& spec_apply(store, request).1 == response
    &&& event_valid(
        issued_world,
        Pid::Store,
        ProcessEvent::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq { op, request },
        },
    )
    &&& event_valid(
        delivered,
        Pid::Node(0),
        ProcessEvent::Receive {
            sender: Pid::Store,
            message: Message::StoreRes { op, response },
        },
    )
}

/// Two actual Rover transitions close the no-previous-key suffix: the Store
/// applies the emitted CAS, then the Node consumes that exact successful
/// response and emits the final boundary Reply. `land` makes network growth
/// append-only and the explicit frame conjunct preserves every unrelated
/// process lane.
#[verifier::rlimit(20)]
pub proof fn lemma_normal_origin_direct_put_delivery_and_reply_rover_steps(
    config: crate::Config,
    issued_world: World<ProductionModel>,
    node: NodeV,
    at: u64,
    get_response_at: u64,
    store_at: u64,
    write_response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
    written_etag: Etag,
)
    requires
        normal_origin_direct_put_completion_ready(
            issued_world,
            node,
            at,
            get_response_at,
            store_at,
            write_response_at,
            call,
            origin,
            bytes,
            etag,
            loaded,
            written_etag,
        ),
    ensures
        ({
            let issued = issued_world.process[0].1->Node_0;
            let store = issued_world.process[1].1->Store_0;
            let op = node.core.next_op.wrapping_add(1);
            let request = normal_origin_put_request(
                node,
                at,
                call,
                origin,
                loaded,
                etag,
            );
            let store_result = fresh_store_delivery_result(
                store,
                Pid::Node(0),
                op,
                request,
            );
            let delivered = normal_origin_put_delivered_world(
                issued_world,
                store_at,
                op,
                request,
            );
            let response = StoreRes::PutIfMatch {
                result: Ok(written_etag),
            };
            let node_event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            };
            let node_result = normal_origin_write_response_result(
                issued,
                op,
                write_response_at,
                written_etag,
            );
            let completed = land(
                delivered,
                0,
                Pid::Node(0),
                write_response_at,
                node_result,
            );
            &&& step(
                ProductionModel,
                config,
                issued_world,
                Label::Process {
                    process: Pid::Store,
                    at: store_at,
                    event: ProcessEvent::Receive {
                        sender: Pid::Node(0),
                        message: Message::StoreReq { op, request },
                    },
                    send: store_result.send,
                },
                delivered,
            )
            &&& step(
                ProductionModel,
                config,
                delivered,
                Label::Process {
                    process: Pid::Node(0),
                    at: write_response_at,
                    event: node_event,
                    send: node_result.send,
                },
                completed,
            )
            &&& completed.network == delivered.network
                + echod_rover::rover::semantics::envelopes(
                    Pid::Node(0),
                    node_result.send,
                )
            &&& forall|i: int|
                0 <= i < issued_world.process.len()
                    && i != 0 && i != 1
                ==> completed.process[i] == issued_world.process[i]
        }),
{
    let issued = issued_world.process[0].1->Node_0;
    let store = issued_world.process[1].1->Store_0;
    let op = node.core.next_op.wrapping_add(1);
    let request = normal_origin_put_request(
        node,
        at,
        call,
        origin,
        loaded,
        etag,
    );
    let delivered = normal_origin_put_delivered_world(
        issued_world,
        store_at,
        op,
        request,
    );
    let response = StoreRes::PutIfMatch {
        result: Ok(written_etag),
    };
    let node_event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes { op, response },
    };
    let node_result = normal_origin_write_response_result(
        issued,
        op,
        write_response_at,
        written_etag,
    );
    lemma_fresh_store_rover_step(
        config,
        issued_world,
        1,
        store_at,
        Pid::Node(0),
        op,
        request,
    );
    lemma_normal_origin_direct_write_response_node_step(
        node,
        at,
        get_response_at,
        write_response_at,
        call,
        origin,
        bytes,
        etag,
        loaded,
        written_etag,
    );
    assert(delivered.process[0] == issued_world.process[0]);
    lemma_node_rover_step(
        config,
        delivered,
        0,
        write_response_at,
        node_event,
        node_result,
    );
    let completed = land(
        delivered,
        0,
        Pid::Node(0),
        write_response_at,
        node_result,
    );
    assert forall|i: int|
        0 <= i < issued_world.process.len() && i != 0 && i != 1
        implies completed.process[i] == issued_world.process[i] by {
        assert(delivered.process[i] == issued_world.process[i]);
    }
}

/// Exact bounded preconditions for the previous-key suffix. Every request,
/// response, and freshness fact is tied to the deterministic world produced
/// by the preceding real Rover transition.
pub open spec fn normal_origin_previous_key_put_delete_completion_ready(
    issued_world: World<ProductionModel>,
    node: NodeV,
    at: u64,
    get_response_at: u64,
    put_store_at: u64,
    write_response_at: u64,
    delete_store_at: u64,
    delete_response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
    written_etag: Etag,
    previous: AKey,
) -> bool {
    let issued = normal_origin_get_response_result(
        node,
        at,
        call,
        origin,
        get_response_at,
        bytes,
        etag,
        loaded,
    ).state->Node_0;
    let write_op = node.core.next_op.wrapping_add(1);
    let delete_op = node.core.next_op.wrapping_add(2);
    let put = normal_origin_put_request(
        node,
        at,
        call,
        origin,
        loaded,
        etag,
    );
    let put_store = issued_world.process[1].1->Store_0;
    let put_delivered = normal_origin_put_delivered_world(
        issued_world,
        put_store_at,
        write_op,
        put,
    );
    let write_response = StoreRes::PutIfMatch {
        result: Ok(written_etag),
    };
    let write_result = normal_origin_write_response_result(
        issued,
        write_op,
        write_response_at,
        written_etag,
    );
    let delete_issued = land(
        put_delivered,
        0,
        Pid::Node(0),
        write_response_at,
        write_result,
    );
    let waiting = write_result.state->Node_0;
    let delete_name = waiting.core.flights.inflight[
        node.core.next_flight
    ].phase->Origin_commit.issued->Some_0->Key_name;
    let delete = spec_store_request(
        StoreReqSpec::Del { key: delete_name },
    );
    let delete_store = delete_issued.process[1].1->Store_0;
    let delete_delivered = land(
        delete_issued,
        1,
        Pid::Store,
        delete_store_at,
        fresh_store_delivery_result(
            delete_store,
            Pid::Node(0),
            delete_op,
            delete,
        ),
    );
    &&& issued_world.process.len() > 1
    &&& issued_world.process[0]
        == (Pid::Node(0), LocalV::Node(issued))
    &&& issued_world.process[1].0 == Pid::Store
    &&& issued_world.process[1].1 is Store
    &&& issued_world.now <= put_store_at
    &&& put_store_at <= write_response_at
    &&& write_response_at <= delete_store_at
    &&& delete_store_at <= delete_response_at
    &&& at <= get_response_at <= write_response_at
    &&& pending_id_fresh(node.pending, call.id)
    &&& crate::rover::spec_target(call.request)
        == Some(TargetSpec::Origin(origin))
    &&& spec_decode_workflow(bytes@) == Ok(loaded)
    &&& normal_origin_get_write_ready(
        node.core,
        spec_call(call, TargetSpec::Origin(origin), at),
        origin,
        at,
        loaded,
        etag,
    )
    &&& normal_origin_previous_deadline_key(
        node.core,
        spec_call(call, TargetSpec::Origin(origin), at),
        origin,
        at,
        get_response_at,
        bytes,
        etag,
    ) == Some(previous)
    &&& !put_store.seen.contains((Pid::Node(0), write_op))
    &&& spec_apply(put_store, put).1 == write_response
    &&& event_valid(
        issued_world,
        Pid::Store,
        ProcessEvent::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq {
                op: write_op,
                request: put,
            },
        },
    )
    &&& event_valid(
        put_delivered,
        Pid::Node(0),
        ProcessEvent::Receive {
            sender: Pid::Store,
            message: Message::StoreRes {
                op: write_op,
                response: write_response,
            },
        },
    )
    &&& delete.deep_view()
        == StoreReqSpec::Del { key: delete_name }
    &&& !delete_store.seen.contains((Pid::Node(0), delete_op))
    &&& spec_apply(delete_store, delete).1
        == StoreRes::Del { result: Ok(()) }
    &&& event_valid(
        delete_issued,
        Pid::Store,
        ProcessEvent::Receive {
            sender: Pid::Node(0),
            message: Message::StoreReq {
                op: delete_op,
                request: delete,
            },
        },
    )
    &&& event_valid(
        delete_delivered,
        Pid::Node(0),
        ProcessEvent::Receive {
            sender: Pid::Store,
            message: Message::StoreRes {
                op: delete_op,
                response: StoreRes::Del { result: Ok(()) },
            },
        },
    )
}

/// Four real Rover transitions close the previous-key suffix: CAS delivery,
/// successful CAS response and exact Del issuance, Del delivery, and the
/// successful Del response ending in the original boundary Reply.
#[verifier::rlimit(30)]
pub proof fn lemma_normal_origin_previous_key_put_delete_and_reply_rover_steps(
    config: crate::Config,
    issued_world: World<ProductionModel>,
    node: NodeV,
    at: u64,
    get_response_at: u64,
    put_store_at: u64,
    write_response_at: u64,
    delete_store_at: u64,
    delete_response_at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    bytes: Vec<u8>,
    etag: Etag,
    loaded: LoadedSpec,
    written_etag: Etag,
    previous: AKey,
)
    requires
        normal_origin_previous_key_put_delete_completion_ready(
            issued_world,
            node,
            at,
            get_response_at,
            put_store_at,
            write_response_at,
            delete_store_at,
            delete_response_at,
            call,
            origin,
            bytes,
            etag,
            loaded,
            written_etag,
            previous,
        ),
    ensures
        ({
            let issued = issued_world.process[0].1->Node_0;
            let put_store = issued_world.process[1].1->Store_0;
            let write_op = node.core.next_op.wrapping_add(1);
            let delete_op = node.core.next_op.wrapping_add(2);
            let put = normal_origin_put_request(
                node,
                at,
                call,
                origin,
                loaded,
                etag,
            );
            let put_store_result = fresh_store_delivery_result(
                put_store,
                Pid::Node(0),
                write_op,
                put,
            );
            let put_delivered = normal_origin_put_delivered_world(
                issued_world,
                put_store_at,
                write_op,
                put,
            );
            let write_response = StoreRes::PutIfMatch {
                result: Ok(written_etag),
            };
            let write_result = normal_origin_write_response_result(
                issued,
                write_op,
                write_response_at,
                written_etag,
            );
            let delete_issued = land(
                put_delivered,
                0,
                Pid::Node(0),
                write_response_at,
                write_result,
            );
            let waiting = write_result.state->Node_0;
            let delete_name = waiting.core.flights.inflight[
                node.core.next_flight
            ].phase->Origin_commit.issued->Some_0->Key_name;
            let delete = spec_store_request(
                StoreReqSpec::Del { key: delete_name },
            );
            let delete_store = delete_issued.process[1].1->Store_0;
            let delete_store_result = fresh_store_delivery_result(
                delete_store,
                Pid::Node(0),
                delete_op,
                delete,
            );
            let delete_delivered = land(
                delete_issued,
                1,
                Pid::Store,
                delete_store_at,
                delete_store_result,
            );
            let delete_result = normal_origin_delete_response_result(
                waiting,
                delete_op,
                delete_response_at,
            );
            let completed = land(
                delete_delivered,
                0,
                Pid::Node(0),
                delete_response_at,
                delete_result,
            );
            &&& step(
                ProductionModel,
                config,
                issued_world,
                Label::Process {
                    process: Pid::Store,
                    at: put_store_at,
                    event: ProcessEvent::Receive {
                        sender: Pid::Node(0),
                        message: Message::StoreReq {
                            op: write_op,
                            request: put,
                        },
                    },
                    send: put_store_result.send,
                },
                put_delivered,
            )
            &&& step(
                ProductionModel,
                config,
                put_delivered,
                Label::Process {
                    process: Pid::Node(0),
                    at: write_response_at,
                    event: ProcessEvent::Receive {
                        sender: Pid::Store,
                        message: Message::StoreRes {
                            op: write_op,
                            response: write_response,
                        },
                    },
                    send: write_result.send,
                },
                delete_issued,
            )
            &&& step(
                ProductionModel,
                config,
                delete_issued,
                Label::Process {
                    process: Pid::Store,
                    at: delete_store_at,
                    event: ProcessEvent::Receive {
                        sender: Pid::Node(0),
                        message: Message::StoreReq {
                            op: delete_op,
                            request: delete,
                        },
                    },
                    send: delete_store_result.send,
                },
                delete_delivered,
            )
            &&& step(
                ProductionModel,
                config,
                delete_delivered,
                Label::Process {
                    process: Pid::Node(0),
                    at: delete_response_at,
                    event: ProcessEvent::Receive {
                        sender: Pid::Store,
                        message: Message::StoreRes {
                            op: delete_op,
                            response: StoreRes::Del { result: Ok(()) },
                        },
                    },
                    send: delete_result.send,
                },
                completed,
            )
            &&& completed.network == delete_delivered.network
                + echod_rover::rover::semantics::envelopes(
                    Pid::Node(0),
                    delete_result.send,
                )
            &&& forall|i: int|
                0 <= i < issued_world.process.len()
                    && i != 0 && i != 1
                ==> completed.process[i] == issued_world.process[i]
        }),
{
    let issued = issued_world.process[0].1->Node_0;
    let put_store = issued_world.process[1].1->Store_0;
    let write_op = node.core.next_op.wrapping_add(1);
    let delete_op = node.core.next_op.wrapping_add(2);
    let put = normal_origin_put_request(
        node,
        at,
        call,
        origin,
        loaded,
        etag,
    );
    let put_delivered = normal_origin_put_delivered_world(
        issued_world,
        put_store_at,
        write_op,
        put,
    );
    let write_response = StoreRes::PutIfMatch {
        result: Ok(written_etag),
    };
    let write_event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes {
            op: write_op,
            response: write_response,
        },
    };
    let write_result = normal_origin_write_response_result(
        issued,
        write_op,
        write_response_at,
        written_etag,
    );
    let delete_issued = land(
        put_delivered,
        0,
        Pid::Node(0),
        write_response_at,
        write_result,
    );
    let waiting = write_result.state->Node_0;
    let delete_name = waiting.core.flights.inflight[
        node.core.next_flight
    ].phase->Origin_commit.issued->Some_0->Key_name;
    let delete = spec_store_request(
        StoreReqSpec::Del { key: delete_name },
    );
    let delete_store = delete_issued.process[1].1->Store_0;
    let delete_delivered = land(
        delete_issued,
        1,
        Pid::Store,
        delete_store_at,
        fresh_store_delivery_result(
            delete_store,
            Pid::Node(0),
            delete_op,
            delete,
        ),
    );
    let delete_event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: Message::StoreRes {
            op: delete_op,
            response: StoreRes::Del { result: Ok(()) },
        },
    };
    let delete_result = normal_origin_delete_response_result(
        waiting,
        delete_op,
        delete_response_at,
    );
    lemma_fresh_store_rover_step(
        config,
        issued_world,
        1,
        put_store_at,
        Pid::Node(0),
        write_op,
        put,
    );
    lemma_normal_origin_previous_key_write_response_node_step(
        node,
        at,
        get_response_at,
        write_response_at,
        call,
        origin,
        bytes,
        etag,
        loaded,
        written_etag,
        previous,
    );
    lemma_node_rover_step(
        config,
        put_delivered,
        0,
        write_response_at,
        write_event,
        write_result,
    );
    lemma_fresh_store_rover_step(
        config,
        delete_issued,
        1,
        delete_store_at,
        Pid::Node(0),
        delete_op,
        delete,
    );
    lemma_normal_origin_previous_key_delete_response_node_step(
        node,
        at,
        get_response_at,
        write_response_at,
        delete_response_at,
        call,
        origin,
        bytes,
        etag,
        loaded,
        written_etag,
        previous,
    );
    lemma_node_rover_step(
        config,
        delete_delivered,
        0,
        delete_response_at,
        delete_event,
        delete_result,
    );
    let completed = land(
        delete_delivered,
        0,
        Pid::Node(0),
        delete_response_at,
        delete_result,
    );
    assert forall|i: int|
        0 <= i < issued_world.process.len() && i != 0 && i != 1
        implies completed.process[i] == issued_world.process[i] by {
        assert(put_delivered.process[i] == issued_world.process[i]);
        assert(delete_issued.process[i] == put_delivered.process[i]);
        assert(delete_delivered.process[i] == delete_issued.process[i]);
    }
}

/// The bounded normal-request happy path: the actual Rover admission step is
/// paired with the already-proved production document decision on the same
/// request and logical origin key. This theorem intentionally does not claim
/// that the load and conditional-write Store steps have already occurred.
pub proof fn lemma_normal_origin_request_happy_path_slice(
    config: crate::Config,
    before: World<ProductionModel>,
    at: u64,
    call: BoundaryCall,
    origin: Seq<char>,
    document: StoredDocumentV,
    abstract_store: AbstractStoreV,
)
    requires
        normal_origin_slice_ready(before, at, call, origin),
        well_formed(document),
        routed(document, call.request),
        echod_concrete::node::spec_key(call.request)
            == Some(crate::refinement::logical_key(
                TargetSpec::Origin(origin),
            )),
        doc_rel(
            crate::refinement::logical_key(
                TargetSpec::Origin(origin),
            ),
            spec_stored_body(document),
            abstract_store,
        ),
        finite_store(abstract_store),
        echod_concrete::node::spec_stored_committed_at(document) <= at,
        at <= MAX_TIME,
        0 < config.retry_timeout <= MAX_TIME,
        safe_effect_config(at, config.retry_timeout),
        document_ids_bounded(document),
    ensures
        ({
            let key = crate::refinement::logical_key(
                TargetSpec::Origin(origin),
            );
            let after_document = on_request(
                document,
                call.request,
                at,
                config.retry_timeout,
                REQUEST_SWEEP_STEPS as nat,
            );
            let (_, _, _, notes) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(document),
                    call.request,
                    at,
                    config.retry_timeout,
                    REQUEST_SWEEP_STEPS as nat,
                );
            let rover_after = land(
                before,
                0,
                Pid::Node(0),
                at,
                normal_origin_admission_result(
                    before.process[0].1->Node_0,
                    at,
                    call,
                    origin,
                ),
            );
            &&& normal_origin_request_rover_step(
                config,
                before,
                at,
                call,
                origin,
                rover_after,
            )
            &&& request_agrees(
                abstract_config(config),
                call.request,
                key,
                spec_stored_body(document),
                abstract_store,
                at,
            )
            &&& well_formed(after_document)
            &&& effects_match(document, after_document, notes)
        }),
{
    lemma_normal_origin_request_rover_step(
        config,
        before,
        at,
        call,
        origin,
    );
    lemma_normal_request_matches_abstract_handler(
        abstract_config(config),
        document,
        call.request,
        crate::refinement::logical_key(
            TargetSpec::Origin(origin),
        ),
        abstract_store,
        at,
    );
}

/// The requested trace-inclusion statement, now naming the production model.
pub open spec fn desired_refinement(config: crate::Config) -> bool {
    refines(
        ProductionModel,
        config,
        AbstractModel,
        abstract_config(config),
    )
}

/// The precise remaining bridge: exhibit one relation that couples the real
/// process world to the abstract world, relates the two initial worlds, and is
/// preserved by every production-backed Rover step.
///
/// This is a proposition, not an assumption and not a theorem claim.
pub open spec fn forward_simulation_obligation(config: crate::Config) -> bool {
    exists|relation: spec_fn(
        World<ProductionModel>,
        World<AbstractModel>,
    ) -> bool| {
        &&& relation(
            initial(ProductionModel, config),
            initial(AbstractModel, abstract_config(config)),
        )
        &&& simulation(
            ProductionModel,
            config,
            AbstractModel,
            abstract_config(config),
            relation,
        )
    }
}

/// Once the production-world relation is supplied and its preservation
/// proved, Rover's generic theorem closes the requested trace refinement.
/// This theorem adds no premise beyond the explicit bridge obligation above.
pub proof fn lemma_obligation_implies_refinement(config: crate::Config)
    requires
        forward_simulation_obligation(config),
    ensures
        desired_refinement(config),
{
    let relation = choose|relation: spec_fn(
        World<ProductionModel>,
        World<AbstractModel>,
    ) -> bool| {
        &&& relation(
            initial(ProductionModel, config),
            initial(AbstractModel, abstract_config(config)),
        )
        &&& simulation(
            ProductionModel,
            config,
            AbstractModel,
            abstract_config(config),
            relation,
        )
    };
    concrete_refines_abstract(
        ProductionModel,
        config,
        AbstractModel,
        abstract_config(config),
        relation,
    );
}

} // verus!
