//! Refinement target for the production-backed Rover model.
//!
//! The existing concrete-to-abstract proof cannot simply be renamed: its
//! relation is over `echod_concrete::model::NodeV`, while the production model
//! now steps [`crate::state::StateSpec`] with caches, concurrent flights,
//! membership refresh, wake replacement, and the full store-call sequence.
//! This module records the exact theorem target and reuses the already-proved
//! handler/effect agreement without claiming the missing world invariant. It
//! also proves the deterministic startup Wake and successful membership
//! announcement completion as real Rover process steps matched by empty
//! abstract executions.
//! It also proves two bounded slices
//! of the real Rover transition relation: a quiet empty task heartbeat and
//! the admission/cache-miss load of one normal origin request. The latter is
//! composed with the already-proved document decision theorem, but does not
//! claim the still-missing StoreRes/commit world invariant.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::refinement::{
    document_ids_bounded,
    lemma_empty_heartbeat_core_step,
    lemma_normal_origin_request_starts_load,
    lemma_normal_request_matches_abstract_handler,
    normal_origin_request_ready,
    quiet_request_ready,
};
#[cfg(verus_keep_ghost)]
use crate::rover::{
    spec_call, spec_effect, spec_effects, spec_node_step,
    spec_initial_node, spec_store_request, spec_take_pending, LocalV, Message,
    Model as ProductionModel, NodeV, LocalV as ProductionLocalV,
    Message as ProductionMessage, NodeV as ProductionNodeV,
};
#[cfg(verus_keep_ghost)]
use crate::state::{Owner, S};
#[cfg(verus_keep_ghost)]
use crate::state_node::RefreshSpec;
#[cfg(verus_keep_ghost)]
use crate::state_timers::ListingSpec;
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;
#[cfg(verus_keep_ghost)]
use crate::types::{
    AnswerSpec, Armed, EffectSpec, EventSpec, RequestEventSpec,
};
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
use echod_concrete::node::spec_stored_body;
#[cfg(verus_keep_ghost)]
use echod_concrete::quick_n_dirty::{on_request, routed};
#[cfg(verus_keep_ghost)]
use echod_concrete::model::Pid;
#[cfg(verus_keep_ghost)]
use echod_concrete::relation::agreement;
#[cfg(verus_keep_ghost)]
use echod_concrete::store::{StoreReq, StoreReqSpec, StoreRes, StoreV};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::refinement::{
    concrete_refines_abstract, end, matches, project, refines, simulation,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{
    event_valid, initial, is_process, land, legal, step, Execution, Label,
    StepResultV, World,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::{Envelope, ProcessEvent, RoverModel};
#[cfg(verus_keep_ghost)]
use echod_types::{Response, StatusRes, MAX_TIME};

verus! {

/// The abstract service configuration implemented by one production node.
pub open spec fn abstract_config(config: crate::Config) -> ServerConfig {
    ServerConfig {
        retry_timeout: config.retry_timeout,
    }
}

proof fn lemma_node_zero_lands_first_outcome(
    config: crate::Config,
    before: World<ProductionModel>,
    node: ProductionNodeV,
    at: u64,
    event: ProcessEvent<Pid, ProductionMessage>,
)
    requires
        before.process.len() > 0,
        before.process[0]
            == (Pid::Node(0), ProductionLocalV::Node(node)),
        before.now <= at,
        event_valid(before, Pid::Node(0), event),
        spec_node_step(node, at, event).len() > 0,
    ensures
        ({
            let outcomes = spec_node_step(node, at, event);
            let outcome = outcomes[0];
            let label = Label::Process {
                process: Pid::Node(0),
                at,
                event,
                send: outcome.send,
            };
            step(
                ProductionModel,
                config,
                before,
                label,
                land(
                    before,
                    0,
                    Pid::Node(0),
                    at,
                    outcome,
                ),
            )
        }),
{
    reveal(step);
    reveal(echod_rover::rover::semantics::is_process);
    assert(Pid::Node(0) != ProductionModel.spec_outside());
    assert(before.process[0].0 == Pid::Node(0));
    assert(exists|i: int|
        0 <= i < before.process.len()
            && #[trigger] before.process[i].0 == Pid::Node(0)) by {
        let i: int = 0;
    }
    assert(echod_rover::rover::semantics::is_process(
        ProductionModel,
        before,
        Pid::Node(0),
    ));
    let outcomes = spec_node_step(node, at, event);
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Node(0),
        before.process[0].1,
        at,
        event,
    ) == outcomes);
    let m = ProductionModel;
    assert(exists|i: int, j: int|
        #![trigger m.spec_on_event(
            config,
            Pid::Node(0),
            before.process[i].1,
            at,
            event,
        )[j]]
    {
        &&& 0 <= i < before.process.len()
        &&& before.process[i].0 == Pid::Node(0)
        &&& {
            let produced = m.spec_on_event(
                config,
                Pid::Node(0),
                before.process[i].1,
                at,
                event,
            );
            &&& 0 <= j < produced.len()
            &&& produced[j].send == outcomes[0].send
            &&& land(
                before,
                i,
                Pid::Node(0),
                at,
                produced[j],
            ) == land(
                before,
                0,
                Pid::Node(0),
                at,
                outcomes[0],
            )
        }
    }) by {
        let i: int = 0;
        let j: int = 0;
    }
}

proof fn lemma_store_one_lands_first_outcome(
    config: crate::Config,
    before: World<ProductionModel>,
    store: StoreV,
    at: u64,
    event: ProcessEvent<Pid, ProductionMessage>,
)
    requires
        before.process.len() > 1,
        before.process[1]
            == (Pid::Store, ProductionLocalV::Store(store)),
        before.now <= at,
        event_valid(before, Pid::Store, event),
        crate::rover::spec_store_step(store, event).len() > 0,
    ensures
        ({
            let outcomes =
                crate::rover::spec_store_step(store, event);
            let outcome = outcomes[0];
            let label = Label::Process {
                process: Pid::Store,
                at,
                event,
                send: outcome.send,
            };
            step(
                ProductionModel,
                config,
                before,
                label,
                land(before, 1, Pid::Store, at, outcome),
            )
        }),
{
    reveal(step);
    reveal(echod_rover::rover::semantics::is_process);
    assert(Pid::Store != ProductionModel.spec_outside());
    assert(before.process[1].0 == Pid::Store);
    assert(exists|i: int|
        0 <= i < before.process.len()
            && #[trigger] before.process[i].0 == Pid::Store) by {
        let i: int = 1;
    }
    assert(echod_rover::rover::semantics::is_process(
        ProductionModel,
        before,
        Pid::Store,
    ));
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Store,
        before.process[1].1,
        at,
        event,
    ) == crate::rover::spec_store_step(store, event));
    let outcomes = crate::rover::spec_store_step(store, event);
    let m = ProductionModel;
    assert(exists|i: int, j: int|
        #![trigger m.spec_on_event(
            config,
            Pid::Store,
            before.process[i].1,
            at,
            event,
        )[j]]
        {
            &&& 0 <= i < before.process.len()
            &&& before.process[i].0 == Pid::Store
            &&& {
                let produced = m.spec_on_event(
                    config,
                    Pid::Store,
                    before.process[i].1,
                    at,
                    event,
                );
                &&& 0 <= j < produced.len()
                &&& produced[j].send == outcomes[0].send
                &&& land(
                    before,
                    i,
                    Pid::Store,
                    at,
                    produced[j],
                ) == land(
                    before,
                    1,
                    Pid::Store,
                    at,
                    outcomes[0],
                )
            }
        }) by {
        let i: int = 1;
        let j: int = 0;
    }
    let outcome = outcomes[0];
    let label = Label::Process {
        process: Pid::Store,
        at,
        event,
        send: outcome.send,
    };
    assert(step(
        ProductionModel,
        config,
        before,
        label,
        land(before, 1, Pid::Store, at, outcome),
    ));
}

/// One actual production Store request delivery followed by its response
/// delivery to the node. The model's standard node/store slots are used; the
/// rest of the world and append-only network are arbitrary, so unrelated
/// production lanes and messages are framed by the two `land` updates.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn lemma_production_store_round_trip_steps(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    store_slot: int,
    node: ProductionNodeV,
    store: StoreV,
    op: u64,
    request: StoreReq,
    store_at: u64,
    node_at: u64,
)
    requires
        0 <= node_slot < before.process.len(),
        0 <= store_slot < before.process.len(),
        node_slot == 0,
        store_slot == 1,
        before.process[node_slot]
            == (Pid::Node(0), ProductionLocalV::Node(node)),
        before.process[store_slot]
            == (Pid::Store, ProductionLocalV::Store(store)),
        before.now <= store_at,
        store_at <= node_at,
        !store.seen.contains((Pid::Node(0), op)),
        before.network.contains(Envelope {
            sender: Pid::Node(0),
            recipient: Pid::Store,
            message: ProductionMessage::StoreReq { op, request },
        }),
    ensures
        ({
            let request_event = ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: ProductionMessage::StoreReq { op, request },
            };
            let store_outcome =
                crate::rover::spec_store_step(store, request_event)[0];
            let store_label = Label::Process {
                process: Pid::Store,
                at: store_at,
                event: request_event,
                send: store_outcome.send,
            };
            let after_store = land(
                before,
                store_slot,
                Pid::Store,
                store_at,
                store_outcome,
            );
            let response = match store_outcome.send[0].1 {
                ProductionMessage::StoreRes { response, .. } => response,
                _ => echod_concrete::store::spec_apply(
                    store,
                    request,
                ).1,
            };
            let response_event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: ProductionMessage::StoreRes { op, response },
            };
            let node_outcome =
                spec_node_step(node, node_at, response_event)[0];
            let node_label = Label::Process {
                process: Pid::Node(0),
                at: node_at,
                event: response_event,
                send: node_outcome.send,
            };
            let after_node = land(
                after_store,
                node_slot,
                Pid::Node(0),
                node_at,
                node_outcome,
            );
            &&& crate::rover::spec_store_step(
                store,
                request_event,
            ).len() == 1
            &&& store_outcome.send.len() == 1
            &&& match store_outcome.send[0] {
                (
                    Pid::Node(0),
                    ProductionMessage::StoreRes {
                        op: response_op,
                        ..
                    },
                ) => response_op == op,
                _ => false,
            }
            &&& spec_node_step(
                node,
                node_at,
                response_event,
            ).len() == 1
            &&& step(
                ProductionModel,
                config,
                before,
                store_label,
                after_store,
            )
            &&& step(
                ProductionModel,
                config,
                after_store,
                node_label,
                after_node,
            )
            &&& after_node.network
                == before.network
                    + echod_rover::rover::semantics::envelopes(
                        Pid::Store,
                        store_outcome.send,
                    )
                    + echod_rover::rover::semantics::envelopes(
                        Pid::Node(0),
                        node_outcome.send,
                    )
        }),
{
    let request_event = ProcessEvent::Receive {
        sender: Pid::Node(0),
        message: ProductionMessage::StoreReq { op, request },
    };
    let store_outcomes =
        crate::rover::spec_store_step(store, request_event);
    reveal(crate::rover::spec_store_step);
    assert(store_outcomes.len() == 1);
    let store_outcome = store_outcomes[0];
    assert(store_outcome.send.len() == 1);
    let store_label = Label::Process {
        process: Pid::Store,
        at: store_at,
        event: request_event,
        send: store_outcome.send,
    };
    let after_store = land(
        before,
        store_slot,
        Pid::Store,
        store_at,
        store_outcome,
    );
    assert(event_valid(before, Pid::Store, request_event));
    lemma_store_one_lands_first_outcome(
        config,
        before,
        store,
        store_at,
        request_event,
    );

    let response = match store_outcome.send[0].1 {
        ProductionMessage::StoreRes { response, .. } => response,
        _ => echod_concrete::store::spec_apply(
            store,
            request,
        ).1,
    };
    let response_event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    reveal(echod_rover::rover::semantics::land);
    reveal(echod_rover::rover::semantics::envelopes);
    reveal(event_valid);
    assert(store_outcome.send =~= seq![(
        Pid::Node(0),
        ProductionMessage::StoreRes { op, response },
    )]);
    assert(after_store.network
        =~= before.network.push(Envelope {
            sender: Pid::Store,
            recipient: Pid::Node(0),
            message: ProductionMessage::StoreRes {
                op,
                response,
            },
        }));
    assert(after_store.network[before.network.len() as int]
        == Envelope {
            sender: Pid::Store,
            recipient: Pid::Node(0),
            message: ProductionMessage::StoreRes {
                op,
                response,
            },
        });
    assert(event_valid(after_store, Pid::Node(0), response_event));
    let node_outcomes = spec_node_step(node, node_at, response_event);
    assert(node_outcomes.len() == 1);
    let node_outcome = node_outcomes[0];
    let node_label = Label::Process {
        process: Pid::Node(0),
        at: node_at,
        event: response_event,
        send: node_outcome.send,
    };
    let after_node = land(
        after_store,
        node_slot,
        Pid::Node(0),
        node_at,
        node_outcome,
    );
    lemma_node_zero_lands_first_outcome(
        config,
        after_store,
        node,
        node_at,
        response_event,
    );
}

/// A Rover process step updates exactly its selected process slot.
pub proof fn lemma_land_frames_other_process<S, M>(
    before: echod_rover::rover::semantics::WorldV<Pid, S, M>,
    slot: int,
    process: Pid,
    at: u64,
    outcome: StepResultV<S, Pid, M>,
    other: int,
)
    requires
        0 <= slot < before.process.len(),
        0 <= other < before.process.len(),
        other != slot,
    ensures
        land(
            before,
            slot,
            process,
            at,
            outcome,
        ).process[other] == before.process[other],
{
    reveal(echod_rover::rover::semantics::land);
}

/// The exact four real Rover steps for the split document commit: origin
/// request delivery, origin response delivery, schedule request delivery, and
/// schedule response delivery. The node/store slots are updated in place while
/// every unrelated process slot and pre-existing network envelope is framed.
pub open spec fn production_split_store_trace(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    store_slot: int,
    node: ProductionNodeV,
    store: StoreV,
    origin_op: u64,
    origin_request: StoreReq,
    schedule_op: u64,
    schedule_request: StoreReq,
    origin_store_at: u64,
    origin_node_at: u64,
    schedule_store_at: u64,
    schedule_node_at: u64,
) -> bool {
    let origin_request_event = ProcessEvent::Receive {
        sender: Pid::Node(0),
        message: ProductionMessage::StoreReq {
            op: origin_op,
            request: origin_request,
        },
    };
    let origin_store_outcome =
        crate::rover::spec_store_step(store, origin_request_event)[0];
    let origin_store_label = Label::Process {
        process: Pid::Store,
        at: origin_store_at,
        event: origin_request_event,
        send: origin_store_outcome.send,
    };
    let after_origin_store = land(
        before,
        store_slot,
        Pid::Store,
        origin_store_at,
        origin_store_outcome,
    );
    let origin_response =
        crate::rover::spec_store_step(
            store,
            origin_request_event,
        )[0].send[0].1;
    let origin_response_event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: origin_response,
    };
    let origin_node_outcome =
        spec_node_step(node, origin_node_at, origin_response_event)[0];
    let origin_node_label = Label::Process {
        process: Pid::Node(0),
        at: origin_node_at,
        event: origin_response_event,
        send: origin_node_outcome.send,
    };
    let after_origin_node = land(
        after_origin_store,
        node_slot,
        Pid::Node(0),
        origin_node_at,
        origin_node_outcome,
    );
    let origin_node = match origin_node_outcome.state {
        ProductionLocalV::Node(next) => next,
        _ => node,
    };
    let origin_store = match origin_store_outcome.state {
        ProductionLocalV::Store(next) => next,
        _ => store,
    };
    let schedule_request_event = ProcessEvent::Receive {
        sender: Pid::Node(0),
        message: ProductionMessage::StoreReq {
            op: schedule_op,
            request: schedule_request,
        },
    };
    let schedule_store_outcome =
        crate::rover::spec_store_step(
            origin_store,
            schedule_request_event,
        )[0];
    let schedule_store_label = Label::Process {
        process: Pid::Store,
        at: schedule_store_at,
        event: schedule_request_event,
        send: schedule_store_outcome.send,
    };
    let after_schedule_store = land(
        after_origin_node,
        store_slot,
        Pid::Store,
        schedule_store_at,
        schedule_store_outcome,
    );
    let schedule_response_event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: schedule_store_outcome.send[0].1,
    };
    let schedule_node_outcome = spec_node_step(
        origin_node,
        schedule_node_at,
        schedule_response_event,
    )[0];
    let schedule_node_label = Label::Process {
        process: Pid::Node(0),
        at: schedule_node_at,
        event: schedule_response_event,
        send: schedule_node_outcome.send,
    };
    let after_schedule_node = land(
        after_schedule_store,
        node_slot,
        Pid::Node(0),
        schedule_node_at,
        schedule_node_outcome,
    );
    &&& step(
        ProductionModel,
        config,
        before,
        origin_store_label,
        after_origin_store,
    )
    &&& step(
        ProductionModel,
        config,
        after_origin_store,
        origin_node_label,
        after_origin_node,
    )
    &&& step(
        ProductionModel,
        config,
        after_origin_node,
        schedule_store_label,
        after_schedule_store,
    )
    &&& step(
        ProductionModel,
        config,
        after_schedule_store,
        schedule_node_label,
        after_schedule_node,
    )
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn lemma_production_split_store_trace(
    config: crate::Config,
    before: World<ProductionModel>,
    node_slot: int,
    store_slot: int,
    node: ProductionNodeV,
    store: StoreV,
    origin_op: u64,
    origin_request: StoreReq,
    schedule_op: u64,
    schedule_request: StoreReq,
    origin_store_at: u64,
    origin_node_at: u64,
    schedule_store_at: u64,
    schedule_node_at: u64,
)
    requires
        0 <= node_slot < before.process.len(),
        0 <= store_slot < before.process.len(),
        node_slot == 0,
        store_slot == 1,
        node_slot != store_slot,
        before.process[node_slot]
            == (Pid::Node(0), ProductionLocalV::Node(node)),
        before.process[store_slot]
            == (Pid::Store, ProductionLocalV::Store(store)),
        before.now <= origin_store_at,
        origin_store_at <= origin_node_at,
        origin_node_at <= schedule_store_at,
        schedule_store_at <= schedule_node_at,
        !store.seen.contains((Pid::Node(0), origin_op)),
        before.network.contains(Envelope {
            sender: Pid::Node(0),
            recipient: Pid::Store,
            message: ProductionMessage::StoreReq {
                op: origin_op,
                request: origin_request,
            },
        }),
        ({
            let origin_request_event = ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: ProductionMessage::StoreReq {
                    op: origin_op,
                    request: origin_request,
                },
            };
            let origin_store_outcome =
                crate::rover::spec_store_step(
                    store,
                    origin_request_event,
                )[0];
            let origin_response_event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: origin_store_outcome.send[0].1,
            };
            let origin_node_outcome =
                spec_node_step(
                    node,
                    origin_node_at,
                    origin_response_event,
                )[0];
            let origin_store = match origin_store_outcome.state {
                ProductionLocalV::Store(next) => next,
                _ => store,
            };
            &&& spec_node_step(
                node,
                origin_node_at,
                origin_response_event,
            ).len() == 1
            &&& origin_node_outcome.send.contains((
                Pid::Store,
                ProductionMessage::StoreReq {
                    op: schedule_op,
                    request: schedule_request,
                },
            ))
            &&& !origin_store.seen.contains((
                Pid::Node(0),
                schedule_op,
            ))
        }),
    ensures
        production_split_store_trace(
            config,
            before,
            node_slot,
            store_slot,
            node,
            store,
            origin_op,
            origin_request,
            schedule_op,
            schedule_request,
            origin_store_at,
            origin_node_at,
            schedule_store_at,
            schedule_node_at,
        ),
{
    let origin_request_event = ProcessEvent::Receive {
        sender: Pid::Node(0),
        message: ProductionMessage::StoreReq {
            op: origin_op,
            request: origin_request,
        },
    };
    let origin_store_outcome =
        crate::rover::spec_store_step(store, origin_request_event)[0];
    lemma_production_store_round_trip_steps(
        config,
        before,
        node_slot,
        store_slot,
        node,
        store,
        origin_op,
        origin_request,
        origin_store_at,
        origin_node_at,
    );
    let after_origin_store = land(
        before,
        store_slot,
        Pid::Store,
        origin_store_at,
        origin_store_outcome,
    );
    let origin_response_event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: origin_store_outcome.send[0].1,
    };
    let origin_node_outcome =
        spec_node_step(
            node,
            origin_node_at,
            origin_response_event,
        )[0];
    let after_origin_node = land(
        after_origin_store,
        node_slot,
        Pid::Node(0),
        origin_node_at,
        origin_node_outcome,
    );
    let origin_node = match origin_node_outcome.state {
        ProductionLocalV::Node(next) => next,
        _ => node,
    };
    let origin_store = match origin_store_outcome.state {
        ProductionLocalV::Store(next) => next,
        _ => store,
    };
    assert(after_origin_node.network
        == before.network
            + echod_rover::rover::semantics::envelopes(
                Pid::Store,
                origin_store_outcome.send,
            )
            + echod_rover::rover::semantics::envelopes(
                Pid::Node(0),
                origin_node_outcome.send,
            ));
    reveal(echod_rover::rover::semantics::envelopes);
    let sent_index = choose|i: int|
        0 <= i < origin_node_outcome.send.len()
            && origin_node_outcome.send[i] == (
                Pid::Store,
                ProductionMessage::StoreReq {
                    op: schedule_op,
                    request: schedule_request,
                },
            );
    let network_index = before.network.len()
        + origin_store_outcome.send.len()
        + sent_index;
    assert(after_origin_node.network[network_index]
        == Envelope {
            sender: Pid::Node(0),
            recipient: Pid::Store,
            message: ProductionMessage::StoreReq {
                op: schedule_op,
                request: schedule_request,
            },
        });
    assert(after_origin_node.network.contains(Envelope {
        sender: Pid::Node(0),
        recipient: Pid::Store,
        message: ProductionMessage::StoreReq {
            op: schedule_op,
            request: schedule_request,
        },
    }));
    lemma_production_store_round_trip_steps(
        config,
        after_origin_node,
        node_slot,
        store_slot,
        origin_node,
        origin_store,
        schedule_op,
        schedule_request,
        schedule_store_at,
        schedule_node_at,
    );
    reveal(production_split_store_trace);
}

proof fn lemma_abstract_timeout_lands_index(
    config: ServerConfig,
    before: World<AbstractModel>,
    service_slot: int,
    state: echod_abstract::model::StateV,
    at: u64,
    index: int,
)
    requires
        0 <= service_slot < before.process.len(),
        before.process[service_slot]
            == (
                echod_abstract::model::Pid::Service,
                state,
            ),
        before.now <= at,
        0 <= index
            < echod_abstract::model::spec_run_timeout(
                config,
                state,
                at,
            ).len(),
    ensures
        ({
            let event =
                ProcessEvent::<
                    echod_abstract::model::Pid,
                    echod_abstract::Message,
                >::Timeout;
            let outcome =
                echod_abstract::model::spec_run_timeout(
                    config,
                    state,
                    at,
                )[index];
            let label = Label::Process {
                process: echod_abstract::model::Pid::Service,
                at,
                event,
                send: outcome.send,
            };
            step(
                AbstractModel,
                config,
                before,
                label,
                land(
                    before,
                    service_slot,
                    echod_abstract::model::Pid::Service,
                    at,
                    outcome,
                ),
            )
        }),
{
    let event =
        ProcessEvent::<
            echod_abstract::model::Pid,
            echod_abstract::Message,
        >::Timeout;
    let outcomes =
        echod_abstract::model::spec_run_timeout(config, state, at);
    let outcome = outcomes[index];
    let label = Label::Process {
        process: echod_abstract::model::Pid::Service,
        at,
        event,
        send: outcome.send,
    };
    reveal(step);
    reveal(echod_rover::rover::semantics::is_process);
    reveal(echod_abstract::model::spec_step);
    reveal(echod_abstract::model::spec_service);
    assert(AbstractModel.spec_on_event(
        config,
        echod_abstract::model::Pid::Service,
        before.process[service_slot].1,
        at,
        event,
    ) == outcomes);
    assert(exists|i: int, j: int|
        #![trigger AbstractModel.spec_on_event(
            config,
            echod_abstract::model::Pid::Service,
            before.process[i].1,
            at,
            event,
        )[j]]
        0 <= i < before.process.len()
            && before.process[i].0
                == echod_abstract::model::Pid::Service
            && 0 <= j < AbstractModel.spec_on_event(
                config,
                echod_abstract::model::Pid::Service,
                before.process[i].1,
                at,
                event,
            ).len()
            && AbstractModel.spec_on_event(
                config,
                echod_abstract::model::Pid::Service,
                before.process[i].1,
                at,
                event,
            )[j].send == outcome.send
            && land(
                before,
                i,
                echod_abstract::model::Pid::Service,
                at,
                AbstractModel.spec_on_event(
                    config,
                    echod_abstract::model::Pid::Service,
                    before.process[i].1,
                    at,
                    event,
                )[j],
            ) == land(
                before,
                service_slot,
                echod_abstract::model::Pid::Service,
                at,
                outcome,
            )
    ) by {
        let i = service_slot;
        let j = index;
    }
    assert(step(
        AbstractModel,
        config,
        before,
        label,
        land(
            before,
            service_slot,
            echod_abstract::model::Pid::Service,
            at,
            outcome,
        ),
    ));
}

/// Lift one finite abstract timeout trace into a silent Rover execution.
proof fn lemma_abstract_timeout_trace_world(
    config: ServerConfig,
    before: World<AbstractModel>,
    service_slot: int,
    state: echod_abstract::model::StateV,
    now: u64,
    work: Seq<echod_abstract::view::InternalV>,
) -> (after: World<AbstractModel>)
    requires
        0 <= service_slot < before.process.len(),
        before.process[service_slot]
            == (echod_abstract::model::Pid::Service, state),
        before.now <= now,
        echod_concrete::relation::timeout_trace_legal(
            config, state, now, work,
        ),
    ensures
        ({
            let trace =
                echod_concrete::relation::spec_timeout_trace(
                    config, state, now, work,
                );
            &&& after.process[service_slot]
                == (
                    echod_abstract::model::Pid::Service,
                    trace.state,
                )
            &&& matches(
                AbstractModel,
                config,
                before,
                Seq::<echod_abstract::BoundaryEvent>::empty(),
                after,
            )
        }),
    decreases work.len(),
{
    reveal(echod_concrete::relation::timeout_trace_legal);
    reveal(echod_concrete::relation::spec_timeout_trace);
    if work.len() == 0 {
        echod_concrete::simulation::lemma_empty_matches(
            config, before,
        );
        before
    } else {
        let outcome =
            echod_abstract::machine::spec_process_work(
                config, work[0], state.store, now,
            );
        if outcome.not_due {
            lemma_abstract_timeout_trace_world(
                config,
                before,
                service_slot,
                state,
                now,
                work.drop_first(),
            )
        } else {
            let result =
                echod_abstract::model::spec_due_result(
                    state, outcome,
                );
            let results =
                echod_abstract::model::spec_run_timeout(
                    config, state, now,
                );
            let index = choose|i: int|
                0 <= i < results.len()
                    && results[i] == result;
            lemma_abstract_timeout_lands_index(
                config,
                before,
                service_slot,
                state,
                now,
                index,
            );
            let event =
                ProcessEvent::<
                    echod_abstract::model::Pid,
                    echod_abstract::Message,
                >::Timeout;
            let label = Label::Process {
                process: echod_abstract::model::Pid::Service,
                at: now,
                event,
                send: result.send,
            };
            let middle = land(
                before,
                service_slot,
                echod_abstract::model::Pid::Service,
                now,
                result,
            );
            let execution = seq![(label, middle)];
            reveal(legal);
            reveal(echod_rover::rover::semantics::before);
            assert(legal(
                AbstractModel, config, before, execution,
            ));
            assert(AbstractModel.spec_observe(label)
                =~= Seq::<echod_abstract::BoundaryEvent>::empty());
            reveal_with_fuel(project, 2);
            reveal(end);
            assert(matches(
                AbstractModel,
                config,
                before,
                Seq::<echod_abstract::BoundaryEvent>::empty(),
                middle,
            ));
            let after =
                lemma_abstract_timeout_trace_world(
                    config,
                    middle,
                    service_slot,
                    result.state,
                    now,
                    work.drop_first(),
                );
            echod_concrete::simulation::lemma_silent_matches_add(
                config, before, middle, after,
            );
            after
        }
    }
}

/// The exact abstract execution represented by a split schedule fire:
/// schedule advance, occurrence insertion, then the finite timeout trace
/// corresponding to the origin's atomic bulk sweep.
pub open spec fn abstract_timeout_endpoint_index(
    config: ServerConfig,
    state: echod_abstract::model::StateV,
    now: u64,
    endpoint: echod_abstract::model::StateV,
) -> int {
    let results =
        echod_abstract::model::spec_run_timeout(config, state, now);
    choose|index: int|
        #![trigger results[index]]
        0 <= index < results.len()
            && results[index].state == endpoint
}

pub proof fn lemma_abstract_timeout_endpoint_index(
    config: ServerConfig,
    state: echod_abstract::model::StateV,
    now: u64,
    endpoint: echod_abstract::model::StateV,
)
    requires
        exists|index: int|
            #![trigger echod_abstract::model::spec_run_timeout(
                config,
                state,
                now,
            )[index]]
            0 <= index
                < echod_abstract::model::spec_run_timeout(
                    config,
                    state,
                    now,
                ).len()
                && echod_abstract::model::spec_run_timeout(
                    config,
                    state,
                    now,
                )[index].state == endpoint,
    ensures
        ({
            let results =
                echod_abstract::model::spec_run_timeout(
                    config,
                    state,
                    now,
                );
            let index = abstract_timeout_endpoint_index(
                config,
                state,
                now,
                endpoint,
            );
            &&& 0 <= index < results.len()
            &&& results[index].state == endpoint
        }),
{
}

/// The schedule and occurrence are concrete abstract timeout edges; the
/// origin closure is the finite trace corresponding to one bulk sweep.
pub proof fn lemma_abstract_schedule_fire_world_execution(
    config: ServerConfig,
    before: World<AbstractModel>,
    service_slot: int,
    schedule_key: Seq<char>,
    schedule_doc: echod_concrete::node::DocumentBodyV,
    origin_key: Seq<char>,
    origin_doc: echod_concrete::node::DocumentBodyV,
    abstract_before: echod_abstract::model::StateV,
    now: u64,
    scheduled: echod_abstract::model::StateV,
    occurred: echod_abstract::model::StateV,
    abstract_after: echod_abstract::model::StateV,
)
    requires
        0 <= service_slot < before.process.len(),
        before.process[service_slot]
            == (
                echod_abstract::model::Pid::Service,
                abstract_before,
            ),
        before.now <= now,
        crate::refinement::schedule_fire_atomic_trace(
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
    ensures
        exists|after: World<AbstractModel>|
            after.process[service_slot]
                == (
                    echod_abstract::model::Pid::Service,
                    abstract_after,
                )
            && #[trigger] matches(
                AbstractModel,
                config,
                before,
                Seq::<echod_abstract::BoundaryEvent>::empty(),
                after,
            )
{
    reveal(crate::refinement::schedule_fire_atomic_trace);
    let schedule_index =
        abstract_timeout_endpoint_index(
            config,
            abstract_before,
            now,
            scheduled,
        );
    let occurrence_index = 0int;
    assert(exists|index: int|
        #![trigger echod_abstract::model::spec_run_timeout(
            config,
            abstract_before,
            now,
        )[index]]
        0 <= index
            < echod_abstract::model::spec_run_timeout(
                config,
                abstract_before,
                now,
            ).len()
            && echod_abstract::model::spec_run_timeout(
                config,
                abstract_before,
                now,
            )[index].state == scheduled);
    lemma_abstract_timeout_endpoint_index(
        config,
        abstract_before,
        now,
        scheduled,
    );
    assert(echod_abstract::model::spec_run_timeout(
        config,
        scheduled,
        now,
    )[0].state == occurred);
    let event =
        ProcessEvent::<
            echod_abstract::model::Pid,
            echod_abstract::Message,
        >::Timeout;
    let schedule_outcome =
        echod_abstract::model::spec_run_timeout(
            config,
            abstract_before,
            now,
        )[schedule_index];
    lemma_abstract_timeout_lands_index(
        config,
        before,
        service_slot,
        abstract_before,
        now,
        schedule_index,
    );
    let schedule_label = Label::Process {
        process: echod_abstract::model::Pid::Service,
        at: now,
        event,
        send: schedule_outcome.send,
    };
    let after_schedule = land(
        before,
        service_slot,
        echod_abstract::model::Pid::Service,
        now,
        schedule_outcome,
    );
    assert(after_schedule.process[service_slot].1 == scheduled);
    let occurrence_outcome =
        echod_abstract::model::spec_run_timeout(
            config,
            scheduled,
            now,
        )[occurrence_index];
    lemma_abstract_timeout_lands_index(
        config,
        after_schedule,
        service_slot,
        scheduled,
        now,
        occurrence_index,
    );
    let occurrence_label = Label::Process {
        process: echod_abstract::model::Pid::Service,
        at: now,
        event,
        send: occurrence_outcome.send,
    };
    let after_occurrence = land(
        after_schedule,
        service_slot,
        echod_abstract::model::Pid::Service,
        now,
        occurrence_outcome,
    );
    assert(after_occurrence.process[service_slot].1 == occurred);
    let execution = seq![
        (schedule_label, after_schedule),
        (occurrence_label, after_occurrence),
    ];
    reveal(legal);
    reveal(echod_rover::rover::semantics::before);
    assert(legal(
        AbstractModel,
        config,
        before,
        execution,
    ));
    assert(AbstractModel.spec_observe(schedule_label)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());
    assert(AbstractModel.spec_observe(occurrence_label)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());
    reveal_with_fuel(project, 3);
    reveal(end);
    assert(project::<AbstractModel>(AbstractModel, execution)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());
    assert(end::<AbstractModel>(before, execution)
        == after_occurrence);
    assert(matches(
        AbstractModel,
        config,
        before,
        Seq::<echod_abstract::BoundaryEvent>::empty(),
        after_occurrence,
    ));
    let retry_work =
        choose|work: Seq<echod_abstract::view::InternalV>|
            #[trigger]
            echod_concrete::relation::timeout_trace_legal(
                config, occurred, now, work,
            ) && echod_concrete::relation::spec_timeout_trace(
                config, occurred, now, work,
            ).state == abstract_after;
    let after =
        lemma_abstract_timeout_trace_world(
            config,
            after_occurrence,
            service_slot,
            occurred,
            now,
            retry_work,
        );
    echod_concrete::simulation::lemma_silent_matches_add(
        config, before, after_occurrence, after,
    );
    assert(after.process[service_slot]
        == (
            echod_abstract::model::Pid::Service,
            abstract_after,
        ));
}

/// Irreducible full-document serialization law needed only when a future
/// global Store relation interprets bytes back into a logical document.
/// Request kind, key, etag, and body selection are deliberately absent.
pub open spec fn codec_full_write_round_trip(
    after: echod_concrete::node::StoredDocumentV,
) -> bool {
    let bytes = crate::document::spec_encode(after);
    let loaded = crate::document::LoadedSpec {
        document: after,
        change_count: 1,
        bytes: bytes.len() as u64,
    };
    match after {
        echod_concrete::node::StoredDocumentV::Workflow(_) =>
            crate::document::spec_decode_workflow(bytes) == Ok(loaded),
        echod_concrete::node::StoredDocumentV::Schedule(_) =>
            crate::document::spec_decode_schedule(bytes) == Ok(loaded),
    }
}

/// Irreducible append serialization law. `base` is the exact physical object
/// previously decoded as `before`; all CAS controls remain outside this law.
pub open spec fn codec_delta_append_round_trip(
    base: Seq<u8>,
    before: crate::document::LoadedSpec,
    after: echod_concrete::node::StoredDocumentV,
) -> bool {
    let encoded =
        crate::document::spec_encode_delta(before.document, after);
    let bytes = base + encoded.0;
    let loaded = crate::document::LoadedSpec {
        document: after,
        change_count: before.change_count.saturating_add(encoded.1),
        bytes: bytes.len() as u64,
    };
    &&& before.bytes == base.len() as u64
    &&& match before.document {
        echod_concrete::node::StoredDocumentV::Workflow(_) =>
            crate::document::spec_decode_workflow(base) == Ok(before),
        echod_concrete::node::StoredDocumentV::Schedule(_) =>
            crate::document::spec_decode_schedule(base) == Ok(before),
    }
    &&& match after {
        echod_concrete::node::StoredDocumentV::Workflow(_) =>
            crate::document::spec_decode_workflow(bytes) == Ok(loaded),
        echod_concrete::node::StoredDocumentV::Schedule(_) =>
            crate::document::spec_decode_schedule(bytes) == Ok(loaded),
    }
}

pub open spec fn commit_store_request(
    s: crate::state::S,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
    cond: Option<Seq<char>>,
) -> StoreReq {
    let settled =
        crate::refinement::settled_commit(s, commit, answer);
    crate::rover::spec_store_request(
        crate::refinement::commit_write_request(
            settled.0,
            settled.1,
            cond,
        ),
    )
}

pub open spec fn commit_store_op(
    s: crate::state::S,
    commit: crate::handler_docs::CommittingSpec,
    answer: Option<echod_concrete::store::StoreRes>,
) -> u64 {
    crate::refinement::settled_commit(s, commit, answer).0.next_op
}

pub open spec fn fire_phase_with_commit(
    phase: crate::handler_docs::PhaseSpec,
    commit: crate::handler_docs::CommittingSpec,
) -> crate::handler_docs::PhaseSpec {
    match phase {
        crate::handler_docs::PhaseSpec::FireOrigin {
            ctx,
            t,
            outbox,
            ..
        } => crate::handler_docs::PhaseSpec::FireOrigin {
            commit,
            ctx,
            t,
            outbox,
        },
        crate::handler_docs::PhaseSpec::FireSchedule { .. } =>
            crate::handler_docs::PhaseSpec::FireSchedule { commit },
        other => other,
    }
}

/// Bounded related-world lift for the split physical commit. Both executable
/// requests are now constructed from their real `CommittingSpec` write
/// phases; codec control fields are conclusions of the production sequence,
/// not caller-supplied premises.

pub proof fn lemma_split_schedule_fire_store_events_match_abstract_world(
    production_config: crate::Config,
    production_before: World<ProductionModel>,
    production_node_slot: int,
    production_store_slot: int,
    production_node: ProductionNodeV,
    production_store: StoreV,
    flight_id: u64,
    origin_write_state: crate::state::S,
    origin_phase: crate::handler_docs::PhaseSpec,
    origin_commit: crate::handler_docs::CommittingSpec,
    origin_answer: Option<echod_concrete::store::StoreRes>,
    origin_cond: Option<Seq<char>>,
    origin_idle: bool,
    schedule_write_state: crate::state::S,
    schedule_phase: crate::handler_docs::PhaseSpec,
    schedule_commit: crate::handler_docs::CommittingSpec,
    schedule_answer: Option<echod_concrete::store::StoreRes>,
    schedule_cond: Option<Seq<char>>,
    schedule_idle: bool,
    origin_store_at: u64,
    origin_node_at: u64,
    schedule_store_at: u64,
    schedule_node_at: u64,
    abstract_before_world: World<AbstractModel>,
    abstract_service_slot: int,
    schedule_key: Seq<char>,
    schedule_doc: echod_concrete::node::DocumentBodyV,
    origin_key: Seq<char>,
    origin_doc: echod_concrete::node::DocumentBodyV,
    abstract_before: echod_abstract::model::StateV,
    now: u64,
    scheduled: echod_abstract::model::StateV,
    occurred: echod_abstract::model::StateV,
    abstract_after: echod_abstract::model::StateV,
)
    requires
        crate::refinement::is_fire_origin_commit(
            origin_phase,
            origin_commit,
        ),
        crate::refinement::commit_write_phase(
            origin_write_state,
            origin_commit,
            origin_answer,
            origin_cond,
            origin_idle,
        ),
        crate::refinement::is_fire_schedule_commit(
            schedule_phase,
            schedule_commit,
        ),
        crate::refinement::commit_write_phase(
            schedule_write_state,
            schedule_commit,
            schedule_answer,
            schedule_cond,
            schedule_idle,
        ),
        ({
            let settled = crate::refinement::settled_commit(
                origin_write_state,
                origin_commit,
                origin_answer,
            );
            &&& crate::rover::store_request_bounded(
                crate::refinement::commit_write_request(
                    settled.0,
                    settled.1,
                    origin_cond,
                ),
            )
            &&& echod_concrete::node::spec_stored_body(
                settled.1.w.loaded.document,
            ) == origin_doc
            &&& echod_concrete::node::spec_stored_body(
                settled.1.after,
            ) == echod_concrete::node::spec_occurrence_transition(
                origin_doc,
                echod_concrete::node::spec_fire_schedule(
                    schedule_doc,
                    now,
                ).1[0],
                now,
                abstract_config(production_config).retry_timeout,
            ).0
        }),
        ({
            let settled = crate::refinement::settled_commit(
                schedule_write_state,
                schedule_commit,
                schedule_answer,
            );
            &&& crate::rover::store_request_bounded(
                crate::refinement::commit_write_request(
                    settled.0,
                    settled.1,
                    schedule_cond,
                ),
            )
            &&& echod_concrete::node::spec_stored_body(
                settled.1.w.loaded.document,
            ) == schedule_doc
            &&& echod_concrete::node::spec_stored_body(
                settled.1.after,
            ) == echod_concrete::node::spec_fire_schedule(
                schedule_doc,
                now,
            ).0
        }),
        0 <= production_node_slot
            < production_before.process.len(),
        0 <= production_store_slot
            < production_before.process.len(),
        production_node_slot == 0,
        production_store_slot == 1,
        production_node_slot != production_store_slot,
        production_before.process[production_node_slot]
            == (
                Pid::Node(0),
                ProductionLocalV::Node(production_node),
            ),
        production_before.process[production_store_slot]
            == (
                Pid::Store,
                ProductionLocalV::Store(production_store),
            ),
        production_node.core.flights.inflight.contains_key(flight_id),
        ({
            let advanced =
                crate::handler_docs::spec_commit_advance(
                    origin_write_state,
                    flight_id,
                    origin_commit,
                    origin_answer,
                );
            production_node.core.flights.inflight[flight_id].phase
                == fire_phase_with_commit(
                    origin_phase,
                    advanced.1,
                )
        }),
        production_before.now <= origin_store_at,
        origin_store_at <= origin_node_at,
        origin_node_at <= schedule_store_at,
        schedule_store_at <= schedule_node_at,
        !production_store.seen.contains((
            Pid::Node(0),
            commit_store_op(
                origin_write_state,
                origin_commit,
                origin_answer,
            ),
        )),
        production_before.network.contains(Envelope {
            sender: Pid::Node(0),
            recipient: Pid::Store,
            message: ProductionMessage::StoreReq {
                op: commit_store_op(
                    origin_write_state,
                    origin_commit,
                    origin_answer,
                ),
                request: commit_store_request(
                    origin_write_state,
                    origin_commit,
                    origin_answer,
                    origin_cond,
                ),
            },
        }),
        ({
            let origin_request_event = ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: ProductionMessage::StoreReq {
                    op: commit_store_op(
                        origin_write_state,
                        origin_commit,
                        origin_answer,
                    ),
                    request: commit_store_request(
                        origin_write_state,
                        origin_commit,
                        origin_answer,
                        origin_cond,
                    ),
                },
            };
            let origin_store_outcome =
                crate::rover::spec_store_step(
                    production_store,
                    origin_request_event,
                )[0];
            let origin_response_event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: origin_store_outcome.send[0].1,
            };
            let origin_node_outcome = spec_node_step(
                production_node,
                origin_node_at,
                origin_response_event,
            )[0];
            let origin_store = match origin_store_outcome.state {
                ProductionLocalV::Store(next) => next,
                _ => production_store,
            };
            let schedule_advanced =
                crate::handler_docs::spec_commit_advance(
                    schedule_write_state,
                    flight_id,
                    schedule_commit,
                    schedule_answer,
                );
            &&& spec_node_step(
                production_node,
                origin_node_at,
                origin_response_event,
            ).len() == 1
            &&& origin_node_outcome.send.contains((
                Pid::Store,
                ProductionMessage::StoreReq {
                    op: commit_store_op(
                        schedule_write_state,
                        schedule_commit,
                        schedule_answer,
                    ),
                    request: commit_store_request(
                        schedule_write_state,
                        schedule_commit,
                        schedule_answer,
                        schedule_cond,
                    ),
                },
            ))
            &&& match origin_node_outcome.state {
                ProductionLocalV::Node(next) => {
                    &&& next.core.flights.inflight
                        .contains_key(flight_id)
                    &&& next.core.flights.inflight[flight_id].phase
                        == fire_phase_with_commit(
                            schedule_phase,
                            schedule_advanced.1,
                        )
                },
                _ => false,
            }
            &&& !origin_store.seen.contains((
                Pid::Node(0),
                commit_store_op(
                    schedule_write_state,
                    schedule_commit,
                    schedule_answer,
                ),
            ))
        }),
        0 <= abstract_service_slot
            < abstract_before_world.process.len(),
        abstract_before_world.process[abstract_service_slot]
            == (
                echod_abstract::model::Pid::Service,
                abstract_before,
            ),
        abstract_before_world.now <= now,
        crate::refinement::schedule_fire_split_intermediate(
            abstract_config(production_config),
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
    ensures
        crate::refinement::commit_advance_issues_write(
            origin_write_state,
            flight_id,
            origin_commit,
            origin_answer,
            origin_cond,
            origin_idle,
        ),
        crate::refinement::commit_advance_issues_write(
            schedule_write_state,
            flight_id,
            schedule_commit,
            schedule_answer,
            schedule_cond,
            schedule_idle,
        ),
        ({
            let settled = crate::refinement::settled_commit(
                origin_write_state,
                origin_commit,
                origin_answer,
            );
            commit_store_request(
                origin_write_state,
                origin_commit,
                origin_answer,
                origin_cond,
            ).deep_view() == crate::refinement::commit_write_request(
                settled.0,
                settled.1,
                origin_cond,
            )
        }),
        ({
            let settled = crate::refinement::settled_commit(
                schedule_write_state,
                schedule_commit,
                schedule_answer,
            );
            commit_store_request(
                schedule_write_state,
                schedule_commit,
                schedule_answer,
                schedule_cond,
            ).deep_view() == crate::refinement::commit_write_request(
                settled.0,
                settled.1,
                schedule_cond,
            )
        }),
        production_split_store_trace(
            production_config,
            production_before,
            production_node_slot,
            production_store_slot,
            production_node,
            production_store,
            commit_store_op(
                origin_write_state,
                origin_commit,
                origin_answer,
            ),
            commit_store_request(
                origin_write_state,
                origin_commit,
                origin_answer,
                origin_cond,
            ),
            commit_store_op(
                schedule_write_state,
                schedule_commit,
                schedule_answer,
            ),
            commit_store_request(
                schedule_write_state,
                schedule_commit,
                schedule_answer,
                schedule_cond,
            ),
            origin_store_at,
            origin_node_at,
            schedule_store_at,
            schedule_node_at,
        ),
        exists|after: World<AbstractModel>|
            after.process[abstract_service_slot]
                == (
                    echod_abstract::model::Pid::Service,
                    abstract_after,
                )
            && #[trigger] matches(
                AbstractModel,
                abstract_config(production_config),
                abstract_before_world,
                Seq::<echod_abstract::BoundaryEvent>::empty(),
                after,
            )
{
    crate::refinement::lemma_schedule_fire_origin_phase_issues_exact_write(
        origin_write_state,
        flight_id,
        origin_phase,
        origin_commit,
        origin_answer,
        origin_cond,
        origin_idle,
    );
    crate::refinement::lemma_schedule_fire_schedule_phase_issues_exact_write(
        schedule_write_state,
        flight_id,
        schedule_phase,
        schedule_commit,
        schedule_answer,
        schedule_cond,
        schedule_idle,
    );
    let origin_settled = crate::refinement::settled_commit(
        origin_write_state,
        origin_commit,
        origin_answer,
    );
    let origin_expected = crate::refinement::commit_write_request(
        origin_settled.0,
        origin_settled.1,
        origin_cond,
    );
    crate::rover::lemma_store_request_realised(origin_expected);
    let schedule_settled = crate::refinement::settled_commit(
        schedule_write_state,
        schedule_commit,
        schedule_answer,
    );
    let schedule_expected = crate::refinement::commit_write_request(
        schedule_settled.0,
        schedule_settled.1,
        schedule_cond,
    );
    crate::rover::lemma_store_request_realised(schedule_expected);
    lemma_production_split_store_trace(
        production_config,
        production_before,
        production_node_slot,
        production_store_slot,
        production_node,
        production_store,
        commit_store_op(
            origin_write_state,
            origin_commit,
            origin_answer,
        ),
        commit_store_request(
            origin_write_state,
            origin_commit,
            origin_answer,
            origin_cond,
        ),
        commit_store_op(
            schedule_write_state,
            schedule_commit,
            schedule_answer,
        ),
        commit_store_request(
            schedule_write_state,
            schedule_commit,
            schedule_answer,
            schedule_cond,
        ),
        origin_store_at,
        origin_node_at,
        schedule_store_at,
        schedule_node_at,
    );
    lemma_abstract_schedule_fire_world_execution(
        abstract_config(production_config),
        abstract_before_world,
        abstract_service_slot,
        schedule_key,
        schedule_doc,
        origin_key,
        origin_doc,
        abstract_before,
        now,
        scheduled,
        occurred,
        abstract_after,
    );
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

/// The deterministic result selected by the production adapter's startup
/// timeout. The adapter starts with an immediately due heartbeat wake.
pub open spec fn initial_wake_outcome(
    config: crate::Config,
) -> StepResultV<ProductionLocalV, Pid, ProductionMessage> {
    spec_node_step(
        spec_initial_node(config.deep_view()),
        0,
        ProcessEvent::Timeout,
    )[0]
}

/// The corresponding real Rover process label.
pub open spec fn initial_wake_label(
    config: crate::Config,
) -> Label<Pid, ProductionMessage> {
    Label::Process {
        process: Pid::Node(0),
        at: 0,
        event: ProcessEvent::Timeout,
        send: initial_wake_outcome(config).send,
    }
}

/// The concrete world after that process result lands in the node slot.
pub open spec fn initial_wake_after(
    config: crate::Config,
) -> World<ProductionModel> {
    land(
        initial(ProductionModel, config),
        0,
        Pid::Node(0),
        0,
        initial_wake_outcome(config),
    )
}

/// Exact control-plane shape of the bounded startup slice: one membership
/// store call is emitted, its owner is retained by the production core, and
/// the timer loop remains not started.
pub open spec fn initial_wake_membership_shape(
    config: crate::Config,
) -> bool {
    let outcome = initial_wake_outcome(config);
    &&& outcome.send.len() == 1
    &&& match outcome.send[0] {
        (
            Pid::Store,
            ProductionMessage::StoreReq { op, .. },
        ) => op == 1,
        _ => false,
    }
    &&& match outcome.state {
        ProductionLocalV::Node(node) => {
            &&& node.core.out.len() == 0
            &&& node.core.ops.contains_key(1)
            &&& node.core.ops[1] == Owner::Members
            &&& node.core.ops.dom()
                == Set::<u64>::empty().insert(1)
            &&& node.core.next_op == 2
            &&& node.core.clock == 0
            &&& match node.core.node.members.refresh {
                Some(RefreshSpec::Announcing { op, now }) =>
                    op == 1 && now == 0,
                _ => false,
            }
            &&& !node.core.timers.started
            &&& node.pending.len() == 0
            &&& node.wake is None
        },
        _ => false,
    }
}

/// The real production Rover startup wake is a hidden abstract stutter.
///
/// This is deliberately a one-step slice, not a claim about an arbitrary
/// wake: once the timer wheel fires a document, the commit point must instead
/// be matched by an abstract internal transition.
pub proof fn lemma_initial_wake_membership_is_abstract_stutter(
    config: crate::Config,
)
    ensures
        initial_wake_membership_shape(config),
        step(
            ProductionModel,
            config,
            initial(ProductionModel, config),
            initial_wake_label(config),
            initial_wake_after(config),
        ),
        ProductionModel.spec_observe(initial_wake_label(config))
            == Seq::<echod_abstract::BoundaryEvent>::empty(),
        matches(
            AbstractModel,
            abstract_config(config),
            initial(AbstractModel, abstract_config(config)),
            Seq::<echod_abstract::BoundaryEvent>::empty(),
            initial(AbstractModel, abstract_config(config)),
        ),
{
    let node = spec_initial_node(config.deep_view());
    let event = ProcessEvent::Timeout;
    let outcomes = spec_node_step(node, 0, event);

    reveal(crate::handler::spec_on_event);
    reveal(crate::handler_node::spec_members_tick);
    reveal(crate::handler_node::spec_members_refresh);
    reveal(crate::handler_timers::spec_timers_run);
    reveal(crate::handler::spec_schedule_wake);
    reveal_with_fuel(crate::rover::spec_effects, 2);
    reveal(crate::rover::spec_effect);

    assert(node.core.next_op == 1);
    assert(node.core.node.members.next_heartbeat is None);
    assert(node.core.node.members.refresh is None);
    assert(!node.core.timers.started);
    assert(node.pending =~= Seq::empty());
    assert(node.wake == Some((0, Armed::Heartbeat)));

    let core_event = EventSpec::Wake {
        clock: 0,
        armed: Armed::Heartbeat,
    };
    let (core, effects) =
        crate::handler::spec_on_event(node.core, core_event);
    assert(effects.len() == 1);
    assert(effects[0] is Store);
    assert(core.ops.contains_key(1));
    assert(core.ops[1] == Owner::Members);
    assert(core.node.members.refresh is Some);
    assert(!core.timers.started);

    let base = ProductionNodeV {
        core,
        pending: node.pending,
        wake: None,
    };
    let (next, send) =
        crate::rover::spec_effects(base, 0, effects);
    assert(effects =~= seq![effects[0]]);
    assert(effects.drop_first() =~= Seq::<EffectSpec>::empty());
    match effects[0] {
        EffectSpec::Store { op, request } => {
            assert(op == 1);
            assert((next, send) == crate::rover::spec_effect(
                base,
                0,
                EffectSpec::Store { op, request },
                Seq::empty(),
            ));
            assert(next == base);
            assert(send =~= seq![(
                Pid::Store,
                ProductionMessage::StoreReq {
                    op,
                    request: crate::rover::spec_store_request(request),
                },
            )]);
        },
        _ => {
            assert(false);
        },
    }
    assert(outcomes =~= seq![StepResultV {
        state: ProductionLocalV::Node(next),
        send,
    }]);
    assert(outcomes.len() == 1);

    let outcome = outcomes[0];
    assert(outcome == initial_wake_outcome(config));
    assert(outcome.send.len() == 1);
    assert(match outcome.send[0] {
        (
            Pid::Store,
            ProductionMessage::StoreReq { op, .. },
        ) => op == 1,
        _ => false,
    });
    assert(match outcome.state {
        ProductionLocalV::Node(next) => {
            &&& next.core.out.len() == 0
            &&& next.core.ops.contains_key(1)
            &&& next.core.ops[1] == Owner::Members
            &&& next.core.ops.dom()
                == Set::<u64>::empty().insert(1)
            &&& next.core.next_op == 2
            &&& next.core.clock == 0
            &&& match next.core.node.members.refresh {
                Some(RefreshSpec::Announcing { op, now }) =>
                    op == 1 && now == 0,
                _ => false,
            }
            &&& !next.core.timers.started
            &&& next.pending.len() == 0
            &&& next.wake is None
        },
        _ => false,
    });
    assert(initial_wake_membership_shape(config));

    let concrete_before = initial(ProductionModel, config);
    let concrete_label = initial_wake_label(config);
    let concrete_after = initial_wake_after(config);
    reveal(step);
    assert(concrete_before.process[0].0 == Pid::Node(0));
    assert(concrete_before.process[0].1
        == ProductionLocalV::Node(node));
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Node(0),
        concrete_before.process[0].1,
        0,
        event,
    ) == outcomes);
    assert(step(
        ProductionModel,
        config,
        concrete_before,
        concrete_label,
        concrete_after,
    ));
    assert(ProductionModel.spec_observe(concrete_label)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());

    let abstract_before =
        initial(AbstractModel, abstract_config(config));
    let execution = Execution::<AbstractModel>::empty();
    assert(legal(
        AbstractModel,
        abstract_config(config),
        abstract_before,
        execution,
    ));
    assert(project::<AbstractModel>(AbstractModel, execution)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());
    assert(end::<AbstractModel>(abstract_before, execution)
        == abstract_before);
    assert(matches(
        AbstractModel,
        abstract_config(config),
        abstract_before,
        Seq::<echod_abstract::BoundaryEvent>::empty(),
        abstract_before,
    ));
}

/// Node state reached by the proved startup wake.
pub open spec fn startup_membership_node(
    config: crate::Config,
) -> ProductionNodeV {
    initial_wake_outcome(config).state->Node_0
}

/// The successful completion delivered for the startup announcement.
pub open spec fn startup_membership_completion_event(
) -> ProcessEvent<Pid, ProductionMessage> {
    ProcessEvent::Receive {
        sender: Pid::Store,
        message: ProductionMessage::StoreRes {
            op: 1,
            response: StoreRes::Put { result: Ok(()) },
        },
    }
}

/// Exact local precondition for a successful announcement completion. This
/// deliberately names the membership phase and owner rather than treating any
/// Store response as control-plane traffic.
pub open spec fn membership_store_completion_pre(
    node: ProductionNodeV,
    event: ProcessEvent<Pid, ProductionMessage>,
) -> bool {
    match event {
        ProcessEvent::Receive {
            sender: Pid::Store,
            message: ProductionMessage::StoreRes {
                op,
                response: StoreRes::Put { result: Ok(()) },
            },
        } => {
            &&& node.core.out.len() == 0
            &&& node.core.ops.contains_key(op)
            &&& node.core.ops[op] == Owner::Members
            &&& match node.core.node.members.refresh {
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

/// Exact local postcondition: announcement op `1` is replaced by list op `2`,
/// while every document-bearing component and the Rover shell's client state
/// remain unchanged.
pub open spec fn membership_store_completion_post(
    before: ProductionNodeV,
    outcome: StepResultV<ProductionLocalV, Pid, ProductionMessage>,
) -> bool {
    &&& outcome.send.len() == 1
    &&& match outcome.send[0] {
        (
            Pid::Store,
            ProductionMessage::StoreReq { op, .. },
        ) => op == 2,
        _ => false,
    }
    &&& match outcome.state {
        ProductionLocalV::Node(after) => {
            &&& !after.core.ops.contains_key(1)
            &&& after.core.ops.contains_key(2)
            &&& after.core.ops[2] == Owner::Members
            &&& match after.core.node.members.refresh {
                Some(RefreshSpec::Listing { op, now }) =>
                    op == 2 && now == 0,
                _ => false,
            }
            &&& after.core.node.core == before.core.node.core
            &&& after.core.cache == before.core.cache
            &&& after.core.flights == before.core.flights
            &&& after.core.timers == before.core.timers
            &&& after.pending == before.pending
            &&& after.wake == before.wake
        },
        _ => false,
    }
}

/// The production adapter's next local activity step after startup has the
/// exact membership-listing shape above.
pub proof fn lemma_startup_membership_store_completion_shape(
    config: crate::Config,
    at: u64,
)
    ensures
        ({
            let before = startup_membership_node(config);
            let event = startup_membership_completion_event();
            let outcomes = spec_node_step(before, at, event);
            &&& membership_store_completion_pre(before, event)
            &&& outcomes.len() == 1
            &&& membership_store_completion_post(
                before,
                outcomes[0],
            )
        }),
{
    lemma_initial_wake_membership_is_abstract_stutter(config);
    assert(initial_wake_membership_shape(config));
    assert(initial_wake_outcome(config).state is Node);
    let before = startup_membership_node(config);
    let event = startup_membership_completion_event();
    let outcomes = spec_node_step(before, at, event);
    assert(before.core.ops.contains_key(1));
    assert(before.core.ops[1] == Owner::Members);
    assert(before.core.ops.dom() =~= Set::<u64>::empty().insert(1));
    assert(before.core.next_op == 2);
    assert(before.core.clock == 0);
    assert(match before.core.node.members.refresh {
        Some(RefreshSpec::Announcing { op, now }) =>
            op == 1 && now == 0,
        _ => false,
    });
    assert(membership_store_completion_pre(before, event));

    reveal(crate::handler::spec_on_event);
    reveal(crate::handler_node::spec_members_tick);
    reveal(crate::handler_node::spec_members_completed);
    reveal(crate::handler_node::spec_announced);
    reveal(crate::handler::spec_schedule_wake);
    reveal_with_fuel(crate::rover::spec_effects, 2);
    reveal(crate::rover::spec_effect);

    let core_event = EventSpec::Store {
        op: 1,
        response: StoreRes::Put { result: Ok(()) },
        clock: at,
    };
    let clocked = crate::state::StateSpec {
        clock: at,
        ..before.core
    };
    let removed = crate::state::StateSpec {
        ops: clocked.ops.remove(1),
        ..clocked
    };
    assert(!removed.ops.contains_key(1));
    assert(removed.ops =~= Map::<u64, Owner>::empty());
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
    let (core, effects) =
        crate::handler::spec_on_event(before.core, core_event);
    assert(core.ops == handled.ops);
    assert(core.node.members.refresh == handled.node.members.refresh);
    assert(effects.len() == 1);
    assert(effects[0] is Store);
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

    let base = ProductionNodeV { core, ..before };
    let (next, send) =
        crate::rover::spec_effects(base, at, effects);
    assert(effects =~= seq![effects[0]]);
    assert(effects.drop_first() =~= Seq::<EffectSpec>::empty());
    match effects[0] {
        EffectSpec::Store { op, request } => {
            assert(op == 2);
            assert((next, send) == crate::rover::spec_effect(
                base,
                at,
                EffectSpec::Store { op, request },
                Seq::empty(),
            ));
            assert(next == base);
            assert(send =~= seq![(
                Pid::Store,
                ProductionMessage::StoreReq {
                    op,
                    request: crate::rover::spec_store_request(request),
                },
            )]);
        },
        _ => {
            assert(false);
        },
    }
    assert(outcomes =~= seq![StepResultV {
        state: ProductionLocalV::Node(next),
        send,
    }]);
    assert(outcomes.len() == 1);
    assert(membership_store_completion_post(
        before,
        outcomes[0],
    ));
}

/// World-step preconditions are explicit: the startup membership node occupies
/// slot zero, time is monotone, and its successful Store response is present
/// in the append-only network. Under precisely those conditions, the real
/// production process step is matched by an empty abstract execution.
pub proof fn lemma_startup_membership_store_completion_is_abstract_stutter(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    at: u64,
)
    requires
        concrete_before.process.len() > 0,
        concrete_before.process[0]
            == (
                Pid::Node(0),
                ProductionLocalV::Node(
                    startup_membership_node(config),
                ),
            ),
        concrete_before.now <= at,
        event_valid(
            concrete_before,
            Pid::Node(0),
            startup_membership_completion_event(),
        ),
    ensures
        ({
            let event = startup_membership_completion_event();
            let outcome = spec_node_step(
                startup_membership_node(config),
                at,
                event,
            )[0];
            let label = Label::Process {
                process: Pid::Node(0),
                at,
                event,
                send: outcome.send,
            };
            let concrete_after = land(
                concrete_before,
                0,
                Pid::Node(0),
                at,
                outcome,
            );
            &&& membership_store_completion_post(
                startup_membership_node(config),
                outcome,
            )
            &&& step(
                ProductionModel,
                config,
                concrete_before,
                label,
                concrete_after,
            )
            &&& ProductionModel.spec_observe(label)
                == Seq::<echod_abstract::BoundaryEvent>::empty()
            &&& matches(
                AbstractModel,
                abstract_config(config),
                abstract_before,
                Seq::<echod_abstract::BoundaryEvent>::empty(),
                abstract_before,
            )
        }),
{
    lemma_startup_membership_store_completion_shape(config, at);
    let event = startup_membership_completion_event();
    let outcomes = spec_node_step(
        startup_membership_node(config),
        at,
        event,
    );
    let outcome = outcomes[0];
    let label = Label::Process {
        process: Pid::Node(0),
        at,
        event,
        send: outcome.send,
    };
    let concrete_after = land(
        concrete_before,
        0,
        Pid::Node(0),
        at,
        outcome,
    );
    assert(membership_store_completion_post(
        startup_membership_node(config),
        outcome,
    ));

    reveal(step);
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Node(0),
        concrete_before.process[0].1,
        at,
        event,
    ) == outcomes);
    assert(step(
        ProductionModel,
        config,
        concrete_before,
        label,
        concrete_after,
    ));
    assert(ProductionModel.spec_observe(label)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());

    let execution = Execution::<AbstractModel>::empty();
    assert(legal(
        AbstractModel,
        abstract_config(config),
        abstract_before,
        execution,
    ));
    assert(project::<AbstractModel>(AbstractModel, execution)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());
    assert(end::<AbstractModel>(abstract_before, execution)
        == abstract_before);
    assert(matches(
        AbstractModel,
        abstract_config(config),
        abstract_before,
        Seq::<echod_abstract::BoundaryEvent>::empty(),
        abstract_before,
    ));
}

pub open spec fn timer_control_effects(
    effects: Seq<EffectSpec>,
) -> bool {
    forall|i: int| 0 <= i < effects.len() ==> match #[trigger] effects[i] {
        EffectSpec::Store { .. }
        | EffectSpec::Note(_)
        | EffectSpec::Wake { .. } => true,
        _ => false,
    }
}

/// Notes and local wake replacement are silent, while Store effects emit only
/// Store traffic. This removes any fixed bound on the number of bucket lists a
/// successful `ListPrefixes` response may schedule.
pub proof fn lemma_timer_control_effects_are_hidden(
    node: ProductionNodeV,
    at: u64,
    effects: Seq<EffectSpec>,
)
    requires
        timer_control_effects(effects),
    ensures
        ({
            let (after, send) =
                crate::rover::spec_effects(node, at, effects);
            &&& after.core == node.core
            &&& after.pending == node.pending
            &&& forall|i: int|
                0 <= i < send.len() ==> match #[trigger] send[i] {
                    (
                        Pid::Store,
                        ProductionMessage::StoreReq { .. },
                    ) => true,
                    _ => false,
                }
        }),
    decreases effects.len(),
{
    reveal(crate::rover::spec_effects);
    reveal(crate::rover::spec_effect);
    if effects.len() > 0 {
        let prefix = effects.drop_last();
        assert(timer_control_effects(prefix)) by {
            assert forall|i: int|
                0 <= i < prefix.len() implies match #[trigger] prefix[i] {
                    EffectSpec::Store { .. }
                    | EffectSpec::Note(_)
                    | EffectSpec::Wake { .. } => true,
                    _ => false,
                } by {
                assert(prefix[i] == effects[i]);
            }
        }
        lemma_timer_control_effects_are_hidden(node, at, prefix);
        let (before_last, sent) =
            crate::rover::spec_effects(node, at, prefix);
        match effects.last() {
            EffectSpec::Store { op, request } => {
                assert forall|i: int|
                    0 <= i < sent.push((
                        Pid::Store,
                        ProductionMessage::StoreReq {
                            op,
                            request:
                                crate::rover::spec_store_request(request),
                        },
                    )).len() implies match #[trigger] sent.push((
                        Pid::Store,
                        ProductionMessage::StoreReq {
                            op,
                            request:
                                crate::rover::spec_store_request(request),
                        },
                    ))[i] {
                        (
                            Pid::Store,
                            ProductionMessage::StoreReq { .. },
                        ) => true,
                        _ => false,
                    } by {
                    if i < sent.len() {
                        assert(sent.push((
                            Pid::Store,
                            ProductionMessage::StoreReq {
                                op,
                                request:
                                    crate::rover::spec_store_request(
                                        request,
                                    ),
                            },
                        ))[i] == sent[i]);
                    }
                }
            },
            EffectSpec::Note(_) | EffectSpec::Wake { .. } => {},
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn lemma_list_buckets_preserves_timer_activity(
    s: crate::state::S,
    prefixes: Seq<Seq<char>>,
    horizon: u64,
    pending: Map<u64, u64>,
)
    requires
        crate::refinement::timer_activity_consistent(s),
        timer_control_effects(s.out),
    ensures
        ({
            let (after, _) = crate::handler_timers::spec_list_buckets(
                s,
                prefixes,
                horizon,
                pending,
            );
            &&& crate::refinement::timer_activity_consistent(after)
            &&& after.node == s.node
            &&& after.cache == s.cache
            &&& after.flights == s.flights
            &&& after.timers == s.timers
            &&& after.loops == s.loops
            &&& after.keys == s.keys
            &&& after.cfg == s.cfg
            &&& timer_control_effects(after.out)
        }),
    decreases prefixes.len(),
{
    reveal(crate::handler_timers::spec_list_buckets);
    if prefixes.len() > 0 {
        match crate::keys::spec_parse_bucket_prefix(
            s.keys.prefix,
            prefixes[0],
        ) {
            Some(bucket) => {
                if bucket <= horizon {
                    let (next, op) = crate::state::spec_store(
                        s,
                        echod_concrete::store::StoreReqSpec::List {
                            prefix: crate::keys::spec_bucket_prefix(
                                s.keys.prefix,
                                bucket,
                            ),
                            max_keys: usize::MAX,
                        },
                        Owner::Timers,
                    );
                    assert(crate::refinement::timer_activity_consistent(
                        next,
                    ));
                    assert(timer_control_effects(next.out)) by {
                        assert forall|i: int|
                            0 <= i < next.out.len() implies match
                                #[trigger] next.out[i]
                            {
                                EffectSpec::Store { .. }
                                | EffectSpec::Note(_)
                                | EffectSpec::Wake { .. } => true,
                                _ => false,
                            } by {
                            if i < s.out.len() {
                                assert(next.out[i] == s.out[i]);
                            }
                        }
                    }
                    lemma_list_buckets_preserves_timer_activity(
                        next,
                        prefixes.drop_first(),
                        horizon,
                        pending.insert(op, bucket),
                    );
                } else {
                    lemma_list_buckets_preserves_timer_activity(
                        s,
                        prefixes.drop_first(),
                        horizon,
                        pending,
                    );
                }
            },
            None => {
                lemma_list_buckets_preserves_timer_activity(
                    s,
                    prefixes.drop_first(),
                    horizon,
                    pending,
                );
            },
        }
    }
}

pub open spec fn nonempty_timer_relist_requeues_pre(
    node: ProductionNodeV,
    at: u64,
    op: u64,
    keys: Vec<String>,
) -> bool {
    &&& node.core.out.len() == 0
    &&& node.core.ops.contains_key(op)
    &&& node.core.ops[op] == Owner::Timers
    &&& node.core.timers.started
    &&& node.core.timers.backoff_until is None
    &&& !node.core.timers.reload_pending
    &&& node.core.node.members.next_heartbeat is Some
    &&& !node.core.loops
    &&& keys.deep_view().len() > 0
    &&& crate::refinement::timer_activity_consistent(node.core)
    &&& crate::handler_timers::spec_take_bucket(
        node.core,
        keys.deep_view(),
        0,
    ).1 > 0
    &&& match node.core.timers.listing {
        Some(ListingSpec::Relist { op: expected, .. }) => {
            &&& expected == op
            &&& node.core.timers.loaded_through is Some
            &&& node.core.timers.loaded_through->Some_0
                < crate::handler_timers::spec_horizon(
                    crate::state::S { clock: at, ..node.core },
                    crate::state::spec_now(
                        crate::state::S { clock: at, ..node.core },
                    ),
                )
        },
        _ => false,
    }
}

pub open spec fn nonempty_timer_requeue_post(
    before: ProductionNodeV,
    outcome: StepResultV<ProductionLocalV, Pid, ProductionMessage>,
) -> bool {
    &&& outcome.send.len() == 1
    &&& match outcome.send[0] {
        (Pid::Store, ProductionMessage::StoreReq { .. }) => true,
        _ => false,
    }
    &&& match outcome.state {
        ProductionLocalV::Node(after) => {
            &&& after.core.node == before.core.node
            &&& after.core.cache == before.core.cache
            &&& after.core.flights == before.core.flights
            &&& crate::refinement::timer_activity_consistent(after.core)
            &&& match after.core.timers.listing {
                Some(ListingSpec::Extend { op, .. }) => {
                    &&& after.core.ops.contains_key(op)
                    &&& after.core.ops[op] == Owner::Timers
                },
                _ => false,
            }
        },
        _ => false,
    }
}

pub open spec fn nonempty_timer_prefixes_schedule_buckets_pre(
    node: ProductionNodeV,
    at: u64,
    op: u64,
    prefixes: Vec<String>,
) -> bool {
    &&& node.core.out.len() == 0
    &&& node.core.ops.contains_key(op)
    &&& node.core.ops[op] == Owner::Timers
    &&& node.core.timers.started
    &&& node.core.node.members.next_heartbeat is Some
    &&& !node.core.loops
    &&& prefixes.deep_view().len() > 0
    &&& crate::refinement::timer_activity_consistent(node.core)
    &&& match node.core.timers.listing {
        Some(ListingSpec::Prefixes {
            op: expected,
            horizon,
        }) => {
            &&& expected == op
            &&& crate::handler_timers::spec_list_buckets(
                crate::state::S {
                    clock: at,
                    ops: node.core.ops.remove(op),
                    timers: crate::state_timers::TimersSpec {
                        listing: None,
                        ..node.core.timers
                    },
                    ..node.core
                },
                prefixes.deep_view(),
                horizon,
                Map::empty(),
            ).1 != Map::<u64, u64>::empty()
        },
        _ => false,
    }
}

pub open spec fn nonempty_timer_buckets_scheduled_post(
    before: ProductionNodeV,
    outcome: StepResultV<ProductionLocalV, Pid, ProductionMessage>,
) -> bool {
    &&& forall|i: int|
        0 <= i < outcome.send.len() ==> match #[trigger] outcome.send[i] {
            (Pid::Store, ProductionMessage::StoreReq { .. }) => true,
            _ => false,
        }
    &&& match outcome.state {
        ProductionLocalV::Node(after) => {
            &&& after.core.node == before.core.node
            &&& after.core.cache == before.core.cache
            &&& after.core.flights == before.core.flights
            &&& after.core.timers.wheel
                == before.core.timers.wheel
            &&& crate::refinement::timer_activity_consistent(after.core)
            &&& match after.core.timers.listing {
                Some(ListingSpec::Buckets { pending, .. }) =>
                    pending != Map::<u64, u64>::empty(),
                _ => false,
            }
        },
        _ => false,
    }
}

#[verifier::rlimit(30)]
pub proof fn lemma_nonempty_timer_relist_completion_requeues(
    node: ProductionNodeV,
    at: u64,
    op: u64,
    keys: Vec<String>,
)
    requires
        nonempty_timer_relist_requeues_pre(node, at, op, keys),
    ensures
        ({
            let response = StoreRes::List { result: Ok(keys) };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: ProductionMessage::StoreRes { op, response },
            };
            let outcomes = spec_node_step(node, at, event);
            &&& outcomes.len() == 1
            &&& nonempty_timer_requeue_post(node, outcomes[0])
        }),
{
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler_timers::spec_timers_completed);
    reveal(crate::handler_timers::spec_relisted);
    reveal(crate::handler_timers::spec_take_bucket);
    reveal(crate::handler_timers::spec_timers_run);
    reveal(crate::handler::spec_schedule_wake);
    reveal_with_fuel(crate::rover::spec_effects, 6);
    reveal(crate::rover::spec_effect);

    let response = StoreRes::List { result: Ok(keys) };
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    let core_event = EventSpec::Store { op, response, clock: at };
    let clocked = crate::state::S { clock: at, ..node.core };
    let now = crate::state::spec_now(clocked);
    let removed = crate::state::S {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    assert(removed.timers == node.core.timers);
    let bucket = match removed.timers.listing {
        Some(ListingSpec::Relist {
            op: expected,
            bucket,
        }) => {
            assert(expected == op);
            bucket
        },
        _ => {
            assert(false);
            0
        },
    };
    let cleared = crate::state::S {
        timers: crate::state_timers::TimersSpec {
            listing: None,
            ..removed.timers
        },
        ..removed
    };
    crate::refinement::lemma_timer_activity_preserved_by_control_state(
        node.core,
        cleared,
    );
    assert(crate::refinement::timer_activity_consistent(cleared));
    assert(cleared.timers.loaded_through is Some);
    assert(cleared.timers.loaded_through->Some_0
        < crate::handler_timers::spec_horizon(cleared, now));
    crate::refinement::
        lemma_nonempty_relisted_requeues_preserves_timer_activity(
            cleared,
            bucket,
            now,
            keys,
        );
    let completed = crate::handler_timers::spec_relisted(
        cleared,
        bucket,
        now,
        response,
    );
    assert(crate::refinement::timer_activity_consistent(completed));
    assert(completed.node == node.core.node);
    assert(completed.cache == node.core.cache);
    assert(completed.flights == node.core.flights);
    assert(match completed.timers.listing {
        Some(ListingSpec::Extend { op, .. }) => {
            &&& completed.ops.contains_key(op)
            &&& completed.ops[op] == Owner::Timers
        },
        _ => false,
    });
    assert(!completed.loops);
    assert(crate::handler_timers::spec_timers_completed(
        removed,
        op,
        response,
    ) == completed);
    assert(!completed.loops);
    assert(crate::handler::spec_schedule_wake(completed) == completed);

    let (core, effects) =
        crate::handler::spec_on_event(node.core, core_event);
    assert(core == crate::state::S {
        out: Seq::empty(),
        ..completed
    });
    assert(effects == completed.out);
    assert(effects.len() == 3);
    assert(effects[0] is Note);
    assert(effects[1] is Note);
    assert(effects[2] is Store);

    let (after, send) = crate::rover::spec_effects(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );
    let outcomes = spec_node_step(node, at, event);
    assert(outcomes =~= seq![StepResultV {
        state: ProductionLocalV::Node(after),
        send,
    }]);
    assert(send.len() == 1);
    assert(match send[0] {
        (Pid::Store, ProductionMessage::StoreReq { .. }) => true,
        _ => false,
    });
    assert(after.core == core);
    assert(nonempty_timer_requeue_post(node, outcomes[0]));
}

#[verifier::rlimit(30)]
pub proof fn lemma_nonempty_timer_prefixes_completion_schedules_buckets(
    node: ProductionNodeV,
    at: u64,
    op: u64,
    prefixes: Vec<String>,
)
    requires
        nonempty_timer_prefixes_schedule_buckets_pre(
            node,
            at,
            op,
            prefixes,
        ),
    ensures
        ({
            let response =
                StoreRes::ListPrefixes { result: Ok(prefixes) };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: ProductionMessage::StoreRes { op, response },
            };
            let outcomes = spec_node_step(node, at, event);
            &&& outcomes.len() == 1
            &&& nonempty_timer_buckets_scheduled_post(
                node,
                outcomes[0],
            )
        }),
{
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler_timers::spec_timers_completed);
    reveal(crate::handler_timers::spec_prefixes_listed);
    reveal(crate::handler_timers::spec_list_buckets);
    reveal(crate::handler::spec_schedule_wake);

    let response = StoreRes::ListPrefixes { result: Ok(prefixes) };
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    let core_event = EventSpec::Store { op, response, clock: at };
    let clocked = crate::state::S { clock: at, ..node.core };
    let now = crate::state::spec_now(clocked);
    let removed = crate::state::S {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    let (horizon, expected) = match removed.timers.listing {
        Some(ListingSpec::Prefixes { op, horizon }) =>
            (horizon, op),
        _ => {
            assert(false);
            (0, 0)
        },
    };
    assert(expected == op);
    let cleared = crate::state::S {
        timers: crate::state_timers::TimersSpec {
            listing: None,
            ..removed.timers
        },
        ..removed
    };
    crate::refinement::lemma_timer_activity_preserved_by_control_state(
        node.core,
        cleared,
    );
    assert(crate::refinement::timer_activity_consistent(cleared));
    assert(timer_control_effects(cleared.out));
    lemma_list_buckets_preserves_timer_activity(
        cleared,
        prefixes.deep_view(),
        horizon,
        Map::empty(),
    );
    let (listed, pending) =
        crate::handler_timers::spec_list_buckets(
            cleared,
            prefixes.deep_view(),
            horizon,
            Map::empty(),
        );
    assert(pending != Map::<u64, u64>::empty());
    assert(crate::refinement::timer_activity_consistent(listed));
    assert(timer_control_effects(listed.out));
    let completed = crate::handler_timers::spec_with_timers(
        listed,
        crate::state_timers::TimersSpec {
            listing: Some(ListingSpec::Buckets {
                pending,
                horizon,
                loaded: 0,
                failed: None,
            }),
            ..listed.timers
        },
    );
    assert(crate::handler_timers::spec_prefixes_listed(
        cleared,
        horizon,
        now,
        response,
    ) == completed);
    assert(crate::handler_timers::spec_timers_completed(
        removed,
        op,
        response,
    ) == completed);
    assert(!completed.loops);
    assert(crate::handler::spec_schedule_wake(completed) == completed);

    let (core, effects) =
        crate::handler::spec_on_event(node.core, core_event);
    assert(core == crate::state::S {
        out: Seq::empty(),
        ..completed
    });
    assert(effects == completed.out);
    assert(timer_control_effects(effects));
    lemma_timer_control_effects_are_hidden(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );
    let (after, send) = crate::rover::spec_effects(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );
    let outcomes = spec_node_step(node, at, event);
    assert(outcomes =~= seq![StepResultV {
        state: ProductionLocalV::Node(after),
        send,
    }]);
    assert(nonempty_timer_buckets_scheduled_post(
        node,
        outcomes[0],
    ));
}

pub proof fn lemma_nonempty_timer_listing_completion_is_abstract_stutter(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    node: ProductionNodeV,
    at: u64,
    op: u64,
    response: StoreRes,
)
    requires
        concrete_before.process.len() > 0,
        concrete_before.process[0]
            == (Pid::Node(0), ProductionLocalV::Node(node)),
        concrete_before.now <= at,
        match response {
            StoreRes::ListPrefixes { result: Ok(prefixes) } =>
                nonempty_timer_prefixes_schedule_buckets_pre(
                    node,
                    at,
                    op,
                    prefixes,
                ),
            StoreRes::List { result: Ok(keys) } =>
                nonempty_timer_relist_requeues_pre(
                    node,
                    at,
                    op,
                    keys,
                ),
            _ => false,
        },
        event_valid(
            concrete_before,
            Pid::Node(0),
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: ProductionMessage::StoreRes { op, response },
            },
        ),
    ensures
        ({
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: ProductionMessage::StoreRes { op, response },
            };
            let outcome = spec_node_step(node, at, event)[0];
            let label = Label::Process {
                process: Pid::Node(0),
                at,
                event,
                send: outcome.send,
            };
            let concrete_after = land(
                concrete_before,
                0,
                Pid::Node(0),
                at,
                outcome,
            );
            &&& (nonempty_timer_requeue_post(node, outcome)
                || nonempty_timer_buckets_scheduled_post(
                    node,
                    outcome,
                ))
            &&& step(
                ProductionModel,
                config,
                concrete_before,
                label,
                concrete_after,
            )
            &&& ProductionModel.spec_observe(label)
                == Seq::<echod_abstract::BoundaryEvent>::empty()
            &&& matches(
                AbstractModel,
                abstract_config(config),
                abstract_before,
                Seq::<echod_abstract::BoundaryEvent>::empty(),
                abstract_before,
            )
        }),
{
    match response {
        StoreRes::ListPrefixes { result: Ok(prefixes) } => {
            lemma_nonempty_timer_prefixes_completion_schedules_buckets(
                node,
                at,
                op,
                prefixes,
            );
        },
        StoreRes::List { result: Ok(keys) } => {
            lemma_nonempty_timer_relist_completion_requeues(
                node,
                at,
                op,
                keys,
            );
        },
        _ => {
            assert(false);
        },
    }
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    let outcomes = spec_node_step(node, at, event);
    assert(outcomes.len() == 1);
    let outcome = outcomes[0];
    let label = Label::Process {
        process: Pid::Node(0),
        at,
        event,
        send: outcome.send,
    };
    let concrete_after = land(
        concrete_before,
        0,
        Pid::Node(0),
        at,
        outcome,
    );

    lemma_node_zero_lands_first_outcome(
        config,
        concrete_before,
        node,
        at,
        event,
    );
    reveal(step);
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Node(0),
        concrete_before.process[0].1,
        at,
        event,
    ) == outcomes);
    assert(step(
        ProductionModel,
        config,
        concrete_before,
        label,
        concrete_after,
    ));
    assert(ProductionModel.spec_observe(label)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());

    let execution = Execution::<AbstractModel>::empty();
    assert(legal(
        AbstractModel,
        abstract_config(config),
        abstract_before,
        execution,
    ));
    assert(project::<AbstractModel>(AbstractModel, execution)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());
    assert(end::<AbstractModel>(abstract_before, execution)
        == abstract_before);
    assert(matches(
        AbstractModel,
        abstract_config(config),
        abstract_before,
        Seq::<echod_abstract::BoundaryEvent>::empty(),
        abstract_before,
    ));
}

/// Exact successful payload and control state for the bounded timer listing
/// completion slice. `ListPrefixes` is accepted only for the prefix phase;
/// `List` is accepted only for extension or relisting. The returned vector is
/// exactly empty, so this slice does not smuggle an unconstrained key set into
/// the wheel proof.
pub open spec fn empty_timer_listing_completion_pre(
    node: ProductionNodeV,
    op: u64,
    response: StoreRes,
) -> bool {
    &&& node.core.out.len() == 0
    &&& node.core.ops.contains_key(op)
    &&& node.core.ops[op] == Owner::Timers
    &&& node.core.timers.started
    &&& node.core.timers.wheel.armed.len() == 0
    &&& node.core.timers.backlog.len() == 0
    &&& node.core.timers.inflight == 0
    &&& crate::refinement::timer_activity_consistent(node.core)
    &&& crate::refinement::owners_consistent(node.core)
    &&& node.core.node.members.next_heartbeat is Some
    &&& match (node.core.timers.listing, response) {
        (
            Some(ListingSpec::Prefixes { op: expected, .. }),
            StoreRes::ListPrefixes { result: Ok(prefixes) },
        ) => expected == op && prefixes.deep_view().len() == 0,
        (
            Some(ListingSpec::Extend { op: expected, .. }),
            StoreRes::List { result: Ok(keys) },
        ) | (
            Some(ListingSpec::Relist { op: expected, .. }),
            StoreRes::List { result: Ok(keys) },
        ) => expected == op && keys.deep_view().len() == 0,
        _ => false,
    }
}

/// A timer completion in this slice may leave the timer machine idle or may
/// install another hidden listing phase. It cannot dispatch document work:
/// both the ordered wheel and the due backlog remain empty.
pub open spec fn empty_timer_listing_completion_post(
    before: ProductionNodeV,
    outcome: StepResultV<ProductionLocalV, Pid, ProductionMessage>,
) -> bool {
    &&& (outcome.send.len() == 0
        || (outcome.send.len() == 1
            && match outcome.send[0] {
                (Pid::Store, ProductionMessage::StoreReq { .. }) => true,
                _ => false,
            }))
    &&& match outcome.state {
        ProductionLocalV::Node(after) => {
            &&& after.core.node == before.core.node
            &&& after.core.cache == before.core.cache
            &&& after.core.flights == before.core.flights
            &&& after.core.timers.wheel.armed.len() == 0
            &&& after.core.timers.backlog.len() == 0
            &&& after.core.timers.inflight == 0
            &&& crate::refinement::timer_activity_consistent(after.core)
            &&& match after.core.timers.listing {
                None => outcome.send.len() == 0,
                Some(ListingSpec::Prefixes { op, .. })
                | Some(ListingSpec::Extend { op, .. })
                | Some(ListingSpec::Relist { op, .. }) => {
                    &&& after.core.ops.contains_key(op)
                    &&& after.core.ops[op] == Owner::Timers
                    &&& outcome.send.len() <= 1
                },
                Some(ListingSpec::Buckets { .. }) => false,
            }
        },
        _ => false,
    }
}

pub open spec fn empty_timer_extension_scheduled(
    outcome: StepResultV<ProductionLocalV, Pid, ProductionMessage>,
) -> bool {
    &&& outcome.send.len() == 1
    &&& match outcome.send[0] {
        (Pid::Store, ProductionMessage::StoreReq { .. }) => true,
        _ => false,
    }
    &&& match outcome.state {
        ProductionLocalV::Node(after) => match after.core.timers.listing {
            Some(ListingSpec::Extend { op, .. }) => {
                &&& after.core.ops.contains_key(op)
                &&& after.core.ops[op] == Owner::Timers
            },
            _ => false,
        },
        _ => false,
    }
}

pub open spec fn empty_timer_listing_idle(
    outcome: StepResultV<ProductionLocalV, Pid, ProductionMessage>,
) -> bool {
    &&& outcome.send.len() == 0
    &&& match outcome.state {
        ProductionLocalV::Node(after) =>
            after.core.timers.listing is None,
        _ => false,
    }
}

pub open spec fn empty_timer_prefixes_requeues_pre(
    node: ProductionNodeV,
    at: u64,
    op: u64,
    prefixes: Vec<String>,
) -> bool {
    &&& empty_timer_listing_completion_pre(
        node,
        op,
        StoreRes::ListPrefixes { result: Ok(prefixes) },
    )
    &&& !node.core.loops
    &&& node.core.timers.backoff_until is None
    &&& match node.core.timers.listing {
        Some(ListingSpec::Prefixes { horizon, .. }) =>
            horizon < crate::handler_timers::spec_horizon(
            crate::state::S { clock: at, ..node.core },
            crate::state::spec_now(
                crate::state::S { clock: at, ..node.core },
            ),
        ),
        _ => false,
    }
}

pub open spec fn empty_timer_relist_idles_pre(
    node: ProductionNodeV,
    at: u64,
    op: u64,
    response: StoreRes,
) -> bool {
    &&& empty_timer_listing_completion_pre(node, op, response)
    &&& !node.core.timers.reload_pending
    &&& node.core.timers.backoff_until is None
    &&& match (node.core.timers.listing, response) {
        (
            Some(ListingSpec::Relist { bucket, .. }),
            StoreRes::List { result: Ok(_) },
        ) => {
            &&& node.core.timers.loaded_through is Some
            &&& node.core.timers.loaded_through->Some_0
                >= crate::handler_timers::spec_horizon(
                    crate::state::S { clock: at, ..node.core },
                    crate::state::spec_now(
                        crate::state::S { clock: at, ..node.core },
                    ),
                )
            &&& bucket.saturating_add(node.core.keys.bucket_ms)
                >= crate::keys::spec_bucket_of(
                    crate::state::spec_now(
                        crate::state::S { clock: at, ..node.core },
                    ),
                    node.core.keys.bucket_ms,
                )
        },
        _ => false,
    }
}

/// An empty successful `ListPrefixes` completion whose captured horizon is
/// behind the completion clock schedules the next hidden extension `List`.
#[verifier::rlimit(30)]
pub proof fn lemma_empty_timer_prefixes_completion_schedules_extend(
    node: ProductionNodeV,
    at: u64,
    op: u64,
    prefixes: Vec<String>,
)
    requires
        empty_timer_prefixes_requeues_pre(node, at, op, prefixes),
    ensures
        ({
            let response =
                StoreRes::ListPrefixes { result: Ok(prefixes) };
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: ProductionMessage::StoreRes { op, response },
            };
            let outcomes = spec_node_step(node, at, event);
            &&& outcomes.len() == 1
            &&& empty_timer_listing_completion_post(node, outcomes[0])
            &&& empty_timer_extension_scheduled(outcomes[0])
        }),
{
    let response = StoreRes::ListPrefixes { result: Ok(prefixes) };
    assert(prefixes.deep_view() =~= Seq::<Seq<char>>::empty());
    match node.core.timers.listing {
        Some(ListingSpec::Prefixes {
            op: expected,
            horizon,
        }) => {
            assert(expected == op);
            assert(horizon < crate::handler_timers::spec_horizon(
                crate::state::S { clock: at, ..node.core },
                crate::state::spec_now(
                    crate::state::S { clock: at, ..node.core },
                ),
            ));
        },
        _ => {
            assert(false);
        },
    }
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler_timers::spec_timers_completed);
    reveal(crate::handler_timers::spec_prefixes_listed);
    reveal(crate::handler_timers::spec_list_buckets);
    reveal(crate::handler_timers::spec_reloaded);
    reveal(crate::handler_timers::spec_timers_run);
    reveal(crate::handler::spec_schedule_wake);
    reveal_with_fuel(crate::rover::spec_effects, 6);
    reveal(crate::rover::spec_effect);

    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    let outcomes = spec_node_step(node, at, event);
    let core_event = EventSpec::Store {
        op,
        response,
        clock: at,
    };
    let clocked = crate::state::S { clock: at, ..node.core };
    let now = crate::state::spec_now(clocked);
    let removed = crate::state::S {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    assert(removed.timers == node.core.timers);
    assert(match removed.timers.listing {
        Some(listing) => listing.expects(op),
        None => false,
    });
    let horizon = match removed.timers.listing {
        Some(ListingSpec::Prefixes { horizon, .. }) => horizon,
        _ => 0,
    };
    let cleared = crate::state::S {
        timers: crate::state_timers::TimersSpec {
            listing: None,
            ..removed.timers
        },
        ..removed
    };
    let completed = crate::handler_timers::spec_timers_completed(
        removed,
        op,
        response,
    );
    assert(completed == crate::handler_timers::spec_prefixes_listed(
        cleared,
        horizon,
        now,
        response,
    ));
    assert(crate::handler_timers::spec_list_buckets(
        cleared,
        prefixes.deep_view(),
        horizon,
        Map::empty(),
    ) == (cleared, Map::empty()));
    assert(completed == crate::handler_timers::spec_reloaded(
        cleared,
        horizon,
        0,
        now,
    ));
    assert(completed.node == node.core.node);
    assert(completed.cache == node.core.cache);
    assert(completed.flights == node.core.flights);
    assert(completed.timers.wheel.armed.len() == 0);
    assert(completed.timers.backlog.len() == 0);
    assert(completed.timers.inflight == 0);
    assert(match completed.timers.listing {
        Some(ListingSpec::Extend { op, .. }) => {
            &&& completed.ops.contains_key(op)
            &&& completed.ops[op] == Owner::Timers
        },
        _ => false,
    });
    assert(completed.out.len() == 3);
    assert(crate::handler::spec_schedule_wake(completed) == completed);
    let (core, effects) =
        crate::handler::spec_on_event(node.core, core_event);
    assert(core == crate::state::S {
        out: Seq::empty(),
        ..completed
    });
    assert(effects == completed.out);
    let (after, send) = crate::rover::spec_effects(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );

    assert(node.core.timers.wheel.armed
        =~= Seq::<crate::state_timers::SlotSpec>::empty());
    assert(node.core.timers.backlog =~=
        Seq::<crate::state_timers::SlotSpec>::empty());
    assert(core.node == node.core.node);
    assert(core.cache == node.core.cache);
    assert(core.flights == node.core.flights);
    assert(core.timers.wheel.armed.len() == 0);
    assert(core.timers.backlog.len() == 0);
    assert(core.timers.inflight == 0);
    assert(match core.timers.listing {
        Some(ListingSpec::Extend { op, .. }) => {
            &&& core.ops.contains_key(op)
            &&& core.ops[op] == Owner::Timers
        },
        _ => false,
    });
    assert(effects.len() == 3);
    assert(effects[0] is Note);
    assert(effects[1] is Note);
    assert(effects[2] is Store);

    assert(outcomes =~= seq![StepResultV {
        state: ProductionLocalV::Node(after),
        send,
    }]);
    assert(send.len() == 1);
    assert(match send[0] {
        (Pid::Store, ProductionMessage::StoreReq { .. }) => true,
        _ => false,
    });
    assert(after.core.node == node.core.node);
    assert(after.core.cache == node.core.cache);
    assert(after.core.flights == node.core.flights);
    assert(after.core.timers.wheel.armed.len() == 0);
    assert(after.core.timers.backlog.len() == 0);
    assert(after.core.timers.inflight == 0);
    assert(crate::refinement::timers_consistent(after.core.timers));
    assert(crate::refinement::timer_wheel_keys_valid(after.core));
    assert(crate::refinement::timer_wheel_ownership_consistent(after.core));
    assert(crate::refinement::timer_activity_consistent(after.core));
    assert(match after.core.timers.listing {
        Some(ListingSpec::Extend { op, .. }) => {
            &&& after.core.ops.contains_key(op)
            &&& after.core.ops[op] == Owner::Timers
        },
        _ => false,
    });
    assert(empty_timer_listing_completion_post(
        node,
        outcomes[0],
    ));
    assert(empty_timer_extension_scheduled(outcomes[0]));
}

/// An empty successful relist `List` completion with a fully loaded horizon
/// and no further bucket to close enters `spec_fire_due`; the explicit empty
/// wheel/backlog makes that branch an idle identity rather than due dispatch.
#[verifier::rlimit(30)]
pub proof fn lemma_empty_timer_relist_completion_reaches_idle(
    node: ProductionNodeV,
    at: u64,
    op: u64,
    response: StoreRes,
)
    requires
        empty_timer_relist_idles_pre(node, at, op, response),
    ensures
        ({
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: ProductionMessage::StoreRes { op, response },
            };
            let outcomes = spec_node_step(node, at, event);
            &&& outcomes.len() == 1
            &&& empty_timer_listing_completion_post(node, outcomes[0])
            &&& empty_timer_listing_idle(outcomes[0])
        }),
{
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler_timers::spec_timers_completed);
    reveal(crate::handler_timers::spec_relisted);
    reveal(crate::handler_timers::spec_take_bucket);
    reveal(crate::handler_timers::spec_timers_run);
    reveal(crate::handler_timers::spec_fire_due);
    reveal(crate::handler_timers::spec_dispatch_due);
    reveal(crate::state_timers::spec_take_due);
    reveal(crate::state_timers::spec_due_count);
    reveal(crate::handler::spec_schedule_wake);
    reveal_with_fuel(crate::rover::spec_effects, 6);
    reveal(crate::rover::spec_effect);

    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    let outcomes = spec_node_step(node, at, event);
    let core_event = EventSpec::Store { op, response, clock: at };
    let (core, effects) =
        crate::handler::spec_on_event(node.core, core_event);
    let (after, send) = crate::rover::spec_effects(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );

    assert(node.core.timers.wheel.armed =~=
        Seq::<crate::state_timers::SlotSpec>::empty());
    assert(node.core.timers.backlog =~=
        Seq::<crate::state_timers::SlotSpec>::empty());
    crate::refinement::lemma_empty_bucket_preserves_timer_activity(
        node.core,
        0,
    );
    crate::refinement::lemma_empty_wheel_fire_due_is_idle(
        crate::state::S {
            timers: crate::state_timers::TimersSpec {
                listing: None,
                closed_through: match node.core.timers.listing {
                    Some(ListingSpec::Relist { bucket, .. }) => Some(bucket),
                    _ => node.core.timers.closed_through,
                },
                ..node.core.timers
            },
            clock: at,
            ops: node.core.ops.remove(op),
            ..node.core
        },
        crate::state::spec_now(
            crate::state::S { clock: at, ..node.core },
        ),
    );

    assert(outcomes =~= seq![StepResultV {
        state: ProductionLocalV::Node(after),
        send,
    }]);
    assert(empty_timer_listing_completion_post(node, outcomes[0]));
    assert(empty_timer_listing_idle(outcomes[0]));
}

/// These two exact completion modes are real Rover world steps whose Store
/// traffic is hidden and therefore match the empty abstract execution.
pub proof fn lemma_empty_timer_completion_is_abstract_stutter(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    node: ProductionNodeV,
    at: u64,
    op: u64,
    response: StoreRes,
)
    requires
        concrete_before.process.len() > 0,
        concrete_before.process[0]
            == (Pid::Node(0), ProductionLocalV::Node(node)),
        concrete_before.now <= at,
        match response {
            StoreRes::ListPrefixes { result: Ok(prefixes) } =>
                empty_timer_prefixes_requeues_pre(
                    node, at, op, prefixes,
                ),
            _ => false,
        }
            || empty_timer_relist_idles_pre(node, at, op, response),
        event_valid(
            concrete_before,
            Pid::Node(0),
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: ProductionMessage::StoreRes { op, response },
            },
        ),
    ensures
        ({
            let event = ProcessEvent::Receive {
                sender: Pid::Store,
                message: ProductionMessage::StoreRes { op, response },
            };
            let outcome = spec_node_step(node, at, event)[0];
            let label = Label::Process {
                process: Pid::Node(0),
                at,
                event,
                send: outcome.send,
            };
            let concrete_after = land(
                concrete_before,
                0,
                Pid::Node(0),
                at,
                outcome,
            );
            &&& empty_timer_listing_completion_post(node, outcome)
            &&& step(
                ProductionModel,
                config,
                concrete_before,
                label,
                concrete_after,
            )
            &&& ProductionModel.spec_observe(label)
                == Seq::<echod_abstract::BoundaryEvent>::empty()
            &&& matches(
                AbstractModel,
                abstract_config(config),
                abstract_before,
                Seq::<echod_abstract::BoundaryEvent>::empty(),
                abstract_before,
            )
        }),
{
    match response {
        StoreRes::ListPrefixes { result: Ok(prefixes) } => {
            if empty_timer_prefixes_requeues_pre(
                node, at, op, prefixes,
            ) {
                lemma_empty_timer_prefixes_completion_schedules_extend(
                    node, at, op, prefixes,
                );
            } else {
                lemma_empty_timer_relist_completion_reaches_idle(
                    node, at, op, response,
                );
            }
        },
        _ => {
            lemma_empty_timer_relist_completion_reaches_idle(
                node, at, op, response,
            );
        },
    }
    let event = ProcessEvent::Receive {
        sender: Pid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    let outcomes = spec_node_step(node, at, event);
    assert(outcomes.len() == 1);
    let outcome = outcomes[0];
    let label = Label::Process {
        process: Pid::Node(0),
        at,
        event,
        send: outcome.send,
    };
    let concrete_after = land(
        concrete_before,
        0,
        Pid::Node(0),
        at,
        outcome,
    );

    lemma_node_zero_lands_first_outcome(
        config,
        concrete_before,
        node,
        at,
        event,
    );
    reveal(step);
    assert(ProductionModel.spec_on_event(
        config,
        Pid::Node(0),
        concrete_before.process[0].1,
        at,
        event,
    ) == outcomes);
    assert(step(
        ProductionModel,
        config,
        concrete_before,
        label,
        concrete_after,
    ));
    assert(ProductionModel.spec_observe(label)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());

    let execution = Execution::<AbstractModel>::empty();
    assert(legal(
        AbstractModel,
        abstract_config(config),
        abstract_before,
        execution,
    ));
    assert(project::<AbstractModel>(AbstractModel, execution)
        =~= Seq::<echod_abstract::BoundaryEvent>::empty());
    assert(end::<AbstractModel>(abstract_before, execution)
        == abstract_before);
    assert(matches(
        AbstractModel,
        abstract_config(config),
        abstract_before,
        Seq::<echod_abstract::BoundaryEvent>::empty(),
        abstract_before,
    ));
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
            );
            let (_, _, _, notes) =
                echod_concrete::node::spec_request_transition(
                    spec_stored_body(document),
                    call.request,
                    at,
                    config.retry_timeout,
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
