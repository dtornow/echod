//! Refinement target for the production-backed Rover model.
//!
//! The existing concrete-to-abstract proof cannot simply be renamed: its
//! relation is over `echod_concrete::model::NodeV`, while the production model
//! now steps [`crate::state::StateSpec`] with caches, concurrent flights,
//! membership refresh, wake replacement, and the full store-call sequence.
//! This module records the exact theorem target, proves restricted world-step
//! slices, and exposes the remaining cache/concurrency frame instead of
//! claiming the missing full simulation.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::refinement::{
    active_flight_keys_distinct, cache_related, flight_lanes_consistent,
    flights_related,
    flight_id_fresh, membership_consistent, operation_id_fresh,
    operation_successor_fresh,
    owners_consistent, retained_documents_well_formed,
    timer_activity_consistent, timers_consistent,
};
#[cfg(verus_keep_ghost)]
use crate::rover::{
    LocalV as ProductionLocalV, Message as ProductionMessage,
    Model as ProductionModel, NodeV as ProductionNodeV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::{
    BoundaryEvent, Message as AbstractMessage, Model as AbstractModel,
    Output, ServerConfig,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::model::Pid as AbstractPid;
#[cfg(verus_keep_ghost)]
use echod_concrete::relation::agreement;
#[cfg(verus_keep_ghost)]
use echod_concrete::model::Pid as ProductionPid;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::{Envelope, ProcessEvent, RoverModel};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::refinement::{
    concrete_refines_abstract, matches, refines, simulation,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{
    envelopes, event_valid, initial, inject, is_process, land, observe_outside, step,
    Execution, Label, World,
};

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
// The production-world relation used by the completed slices
// ---------------------------------------------------------------------------

pub open spec fn production_node(
    world: World<ProductionModel>,
) -> ProductionNodeV {
    world.process[0].1->Node_0
}

pub open spec fn abstract_state(
    world: World<AbstractModel>,
) -> echod_abstract::model::StateV {
    world.process[0].1
}

pub open spec fn production_shaped(
    world: World<ProductionModel>,
) -> bool {
    &&& world.process.len() == 2
    &&& world.process[0].0 == ProductionPid::Node(0)
    &&& world.process[0].1 is Node
    &&& world.process[1].0 == ProductionPid::Store
    &&& world.process[1].1 is Store
}

pub open spec fn abstract_shaped(
    world: World<AbstractModel>,
) -> bool {
    &&& world.process.len() == 1
    &&& world.process[0].0 == AbstractPid::Service
}

pub open spec fn abstract_request_present(
    network: Seq<Envelope<AbstractPid, AbstractMessage>>,
    call: echod_abstract::Call,
) -> bool {
    exists|i: int|
        #![trigger network[i]]
        0 <= i < network.len()
            && network[i] == Envelope {
                sender: AbstractPid::Outside,
                recipient: AbstractPid::Service,
                message: AbstractMessage::Request(call),
            }
}

pub open spec fn abstract_output_present(
    network: Seq<Envelope<AbstractPid, AbstractMessage>>,
    output: Output,
) -> bool {
    exists|i: int|
        #![trigger network[i]]
        0 <= i < network.len()
            && network[i] == Envelope {
                sender: AbstractPid::Service,
                recipient: AbstractPid::Outside,
                message: AbstractMessage::Output(output),
            }
}

pub open spec fn request_covered(
    envelope: Envelope<ProductionPid, ProductionMessage>,
    abstract_network: Seq<Envelope<AbstractPid, AbstractMessage>>,
) -> bool {
    match envelope.message {
        ProductionMessage::Request(call) =>
            envelope.sender != ProductionPid::Outside
                || abstract_request_present(abstract_network, call),
        _ => true,
    }
}

pub open spec fn output_covered(
    envelope: Envelope<ProductionPid, ProductionMessage>,
    abstract_network: Seq<Envelope<AbstractPid, AbstractMessage>>,
) -> bool {
    match envelope.message {
        ProductionMessage::Reply(output)
        | ProductionMessage::Send(output) =>
            envelope.recipient != ProductionPid::Outside
                || abstract_output_present(abstract_network, output),
        _ => true,
    }
}

pub open spec fn boundary_covered(
    concrete: Seq<Envelope<ProductionPid, ProductionMessage>>,
    abstract_network: Seq<Envelope<AbstractPid, AbstractMessage>>,
) -> bool {
    &&& forall|i: int|
        0 <= i < concrete.len() ==>
            request_covered(#[trigger] concrete[i], abstract_network)
    &&& forall|i: int|
        0 <= i < concrete.len() ==>
            output_covered(#[trigger] concrete[i], abstract_network)
}

pub open spec fn send_boundary_covered(
    sender: ProductionPid,
    send: Seq<(ProductionPid, ProductionMessage)>,
    abstract_network: Seq<Envelope<AbstractPid, AbstractMessage>>,
) -> bool {
    forall|i: int|
        0 <= i < send.len() ==> {
            let pair = #[trigger] send[i];
            let envelope = Envelope {
                sender,
                recipient: pair.0,
                message: pair.1,
            };
            &&& request_covered(envelope, abstract_network)
            &&& output_covered(envelope, abstract_network)
        }
}

pub open spec fn internal_effect(
    effect: crate::types::EffectSpec,
) -> bool {
    match effect {
        crate::types::EffectSpec::Store { .. }
        | crate::types::EffectSpec::Wake { .. }
        | crate::types::EffectSpec::Note(_) => true,
        _ => false,
    }
}

pub open spec fn internal_effects(
    effects: Seq<crate::types::EffectSpec>,
) -> bool {
    forall|i: int|
        0 <= i < effects.len() ==>
            internal_effect(#[trigger] effects[i])
}

proof fn lemma_internal_effects_send_to_store(
    node: ProductionNodeV,
    now: u64,
    effects: Seq<crate::types::EffectSpec>,
)
    requires internal_effects(effects),
    ensures
        ({
            let (_, send) =
                crate::rover::spec_effects(node, now, effects);
            forall|i: int|
                0 <= i < send.len() ==>
                    #[trigger] send[i].0 == ProductionPid::Store
        }),
    decreases effects.len(),
{
    reveal(crate::rover::spec_effects);
    if effects.len() > 0 {
        let prefix = effects.drop_last();
        assert(internal_effects(prefix)) by {
            assert forall|i: int|
                0 <= i < prefix.len() implies
                    internal_effect(#[trigger] prefix[i]) by {
                assert(prefix[i] == effects[i]);
            };
        };
        lemma_internal_effects_send_to_store(node, now, prefix);
        let (prefix_node, prefix_send) =
            crate::rover::spec_effects(node, now, prefix);
        reveal(crate::rover::spec_effect);
        match effects.last() {
            crate::types::EffectSpec::Store { .. } => {},
            crate::types::EffectSpec::Wake { .. } => {},
            crate::types::EffectSpec::Note(_) => {},
            _ => assert(false),
        }
    }
}

proof fn lemma_store_only_send_boundary_covered(
    sender: ProductionPid,
    send: Seq<(ProductionPid, ProductionMessage)>,
    abstract_network: Seq<
        Envelope<AbstractPid, AbstractMessage>,
    >,
)
    requires
        sender != ProductionPid::Outside,
        forall|i: int|
            0 <= i < send.len() ==>
                #[trigger] send[i].0 == ProductionPid::Store,
    ensures
        send_boundary_covered(
            sender,
            send,
            abstract_network,
        ),
{
    reveal(send_boundary_covered);
    reveal(request_covered);
    reveal(output_covered);
    assert forall|i: int|
        0 <= i < send.len() implies {
            let pair = #[trigger] send[i];
            let envelope = Envelope {
                sender,
                recipient: pair.0,
                message: pair.1,
            };
            &&& request_covered(envelope, abstract_network)
            &&& output_covered(envelope, abstract_network)
        } by {
        assert(send[i].0 == ProductionPid::Store);
        match send[i].1 {
            ProductionMessage::Request(_) => {},
            ProductionMessage::Reply(_) => {},
            ProductionMessage::Send(_) => {},
            _ => {},
        }
    };
}

pub proof fn lemma_boundary_covered_append_send(
    concrete: Seq<Envelope<ProductionPid, ProductionMessage>>,
    abstract_network: Seq<Envelope<AbstractPid, AbstractMessage>>,
    sender: ProductionPid,
    send: Seq<(ProductionPid, ProductionMessage)>,
)
    requires
        boundary_covered(concrete, abstract_network),
        send_boundary_covered(sender, send, abstract_network),
    ensures
        boundary_covered(
            concrete + envelopes(sender, send),
            abstract_network,
        ),
{
    let added = envelopes(sender, send);
    assert forall|i: int|
        0 <= i < concrete.len() + added.len() implies
            request_covered(
                #[trigger] (concrete + added)[i],
                abstract_network,
            ) by {
        if i < concrete.len() {
            assert((concrete + added)[i] == concrete[i]);
        } else {
            let j = i - concrete.len();
            assert(0 <= j < added.len());
            assert(added[j] == Envelope {
                sender,
                recipient: send[j].0,
                message: send[j].1,
            });
        }
    };
    assert forall|i: int|
        0 <= i < concrete.len() + added.len() implies
            output_covered(
                #[trigger] (concrete + added)[i],
                abstract_network,
            ) by {
        if i < concrete.len() {
            assert((concrete + added)[i] == concrete[i]);
        } else {
            let j = i - concrete.len();
            assert(0 <= j < added.len());
            assert(added[j] == Envelope {
                sender,
                recipient: send[j].0,
                message: send[j].1,
            });
        }
    };
}

/// Relation over the state actually held by the production adapter. Store
/// traffic is represented in the append-only production network and in
/// `core.ops`; document state is interpreted from cache or decided flights.
pub open spec fn node_related(
    node: ProductionNodeV,
    state: echod_abstract::model::StateV,
) -> bool {
    &&& node.core.out.len() == 0
    &&& operation_id_fresh(node.core)
    &&& flight_id_fresh(node.core)
    &&& retained_documents_well_formed(node.core)
    &&& active_flight_keys_distinct(node.core.flights)
    &&& owners_consistent(node.core)
    &&& membership_consistent(node.core)
    &&& timers_consistent(node.core.timers)
    &&& flight_lanes_consistent(node.core.flights)
    &&& cache_related(node.core.cache, node.core.flights, state.store)
    &&& flights_related(node.core.flights, state.store)
    &&& state.pending.len() == 0
}

pub open spec fn world_related(
    concrete: World<ProductionModel>,
    abstract_world: World<AbstractModel>,
) -> bool {
    &&& production_shaped(concrete)
    &&& abstract_shaped(abstract_world)
    &&& abstract_world.now <= concrete.now
    &&& node_related(production_node(concrete), abstract_state(abstract_world))
    &&& boundary_covered(concrete.network, abstract_world.network)
}

/// The imported world relation strengthened with the timer wheel, backlog,
/// ownership, and key-validity invariant used by the atomic bulk/schedule
/// proofs on this branch.
pub open spec fn atomic_world_related(
    concrete: World<ProductionModel>,
    abstract_world: World<AbstractModel>,
) -> bool {
    &&& world_related(concrete, abstract_world)
    &&& timer_activity_consistent(production_node(concrete).core)
}

pub open spec fn world_link(
) -> spec_fn(
    World<ProductionModel>,
    World<AbstractModel>,
) -> bool {
    |concrete, abstract_world| world_related(concrete, abstract_world)
}

pub proof fn lemma_empty_match(
    config: ServerConfig,
    world: World<AbstractModel>,
)
    ensures
        matches(
            AbstractModel,
            config,
            world,
            Seq::<BoundaryEvent>::empty(),
            world,
        ),
{
    let execution = Execution::<AbstractModel>::empty();
    assert(echod_rover::rover::semantics::legal(
        AbstractModel,
        config,
        world,
        execution,
    ));
    assert(echod_rover::rover::refinement::project::<AbstractModel>(
        AbstractModel,
        execution,
    ) =~= Seq::<BoundaryEvent>::empty());
    assert(echod_rover::rover::refinement::end::<AbstractModel>(
        world,
        execution,
    ) == world);
}

pub proof fn lemma_one_step_match(
    config: ServerConfig,
    before: World<AbstractModel>,
    label: Label<AbstractPid, AbstractMessage>,
    after: World<AbstractModel>,
    visible: Seq<BoundaryEvent>,
)
    requires
        step(AbstractModel, config, before, label, after),
        AbstractModel.spec_observe(label) == visible,
    ensures
        matches(
            AbstractModel,
            config,
            before,
            visible,
            after,
        ),
{
    let execution = seq![(label, after)];
    assert(echod_rover::rover::semantics::legal(
        AbstractModel,
        config,
        before,
        execution,
    ));
    assert(execution.drop_last()
        =~= Execution::<AbstractModel>::empty());
    assert(execution.last().0 == label);
    assert(echod_rover::rover::refinement::project::<AbstractModel>(
        AbstractModel,
        execution.drop_last(),
    ) =~= Seq::<BoundaryEvent>::empty());
    assert(echod_rover::rover::refinement::project::<AbstractModel>(
        AbstractModel,
        execution,
    ) =~= visible);
    assert(echod_rover::rover::refinement::end::<AbstractModel>(
        before,
        execution,
    ) == after);
}

pub proof fn lemma_initial_node_related(config: crate::Config)
    ensures
        node_related(
            crate::rover::spec_initial_node(config.deep_view()),
            echod_abstract::model::StateV {
                store: echod_abstract::model::empty_store(),
                pending: Seq::empty(),
            },
        ),
{
    let node = crate::rover::spec_initial_node(config.deep_view());
    assert(node.core.out =~= Seq::<crate::types::EffectSpec>::empty());
    assert(node.core.ops
        =~= Map::<u64, crate::state::Owner>::empty());
    assert(node.core.cache.entries.len() == 0);
    assert(node.core.flights.inflight
        =~= Map::<u64, crate::handler_docs::FlightSpec>::empty());
    assert(node.core.flights.slots.dom()
        =~= Set::<Seq<char>>::empty());
    assert(node.core.node.core.members
        =~= Seq::<Seq<char>>::empty());
    assert(node.core.timers.wheel.armed
        =~= Seq::<(u64, Seq<char>)>::empty());
    assert(node.core.timers.backlog
        =~= Seq::<(u64, Seq<char>)>::empty());
}

/// The actual production adapter and the abstract Rover service start related.
pub proof fn lemma_initial_world_related(config: crate::Config)
    ensures
        world_related(
            initial(ProductionModel, config),
            initial(AbstractModel, abstract_config(config)),
        ),
{
    let concrete = initial(ProductionModel, config);
    let abstract_world =
        initial(AbstractModel, abstract_config(config));
    assert(concrete.process == ProductionModel.spec_initial(config));
    assert(abstract_world.process
        == AbstractModel.spec_initial(abstract_config(config)));
    assert(concrete.network
        =~= Seq::<Envelope<ProductionPid, ProductionMessage>>::empty());
    assert(abstract_world.network
        =~= Seq::<Envelope<AbstractPid, AbstractMessage>>::empty());
    assert(production_shaped(concrete));
    assert(abstract_shaped(abstract_world));
    assert(abstract_state(abstract_world)
        == echod_abstract::model::StateV {
            store: echod_abstract::model::empty_store(),
            pending: Seq::empty(),
        });
    lemma_initial_node_related(config);
    assert(boundary_covered(
        concrete.network,
        abstract_world.network,
    ));
}

pub proof fn lemma_initial_atomic_world_related(config: crate::Config)
    ensures
        atomic_world_related(
            initial(ProductionModel, config),
            initial(AbstractModel, abstract_config(config)),
        ),
{
    lemma_initial_world_related(config);
    crate::refinement::lemma_timer_accounting_initial();
    let concrete = initial(ProductionModel, config);
    let node = production_node(concrete);
    assert(node.core.timers
        == crate::state_timers::spec_timers_new());
    assert(node.core.timers.wheel.armed.len() == 0);
    assert(node.core.timers.backlog.len() == 0);
}

proof fn lemma_request_present_push(
    network: Seq<Envelope<AbstractPid, AbstractMessage>>,
    added: Envelope<AbstractPid, AbstractMessage>,
    call: echod_abstract::Call,
)
    requires
        abstract_request_present(network, call),
    ensures
        abstract_request_present(network.push(added), call),
{
    let i = choose|i: int|
        #![trigger network[i]]
        0 <= i < network.len()
            && network[i] == Envelope {
                sender: AbstractPid::Outside,
                recipient: AbstractPid::Service,
                message: AbstractMessage::Request(call),
            };
    assert(network.push(added)[i] == network[i]);
}

proof fn lemma_output_present_push(
    network: Seq<Envelope<AbstractPid, AbstractMessage>>,
    added: Envelope<AbstractPid, AbstractMessage>,
    output: Output,
)
    requires
        abstract_output_present(network, output),
    ensures
        abstract_output_present(network.push(added), output),
{
    let i = choose|i: int|
        #![trigger network[i]]
        0 <= i < network.len()
            && network[i] == Envelope {
                sender: AbstractPid::Service,
                recipient: AbstractPid::Outside,
                message: AbstractMessage::Output(output),
            };
    assert(network.push(added)[i] == network[i]);
}

proof fn lemma_boundary_coverage_abstract_push(
    concrete: Seq<Envelope<ProductionPid, ProductionMessage>>,
    abstract_network: Seq<Envelope<AbstractPid, AbstractMessage>>,
    added: Envelope<AbstractPid, AbstractMessage>,
)
    requires
        boundary_covered(concrete, abstract_network),
    ensures
        boundary_covered(concrete, abstract_network.push(added)),
{
    assert forall|i: int|
        0 <= i < concrete.len() implies
            request_covered(
                #[trigger] concrete[i],
                abstract_network.push(added),
            ) by {
        let envelope = concrete[i];
        match envelope.message {
            ProductionMessage::Request(call) => {
                if envelope.sender == ProductionPid::Outside {
                    lemma_request_present_push(
                        abstract_network,
                        added,
                        call,
                    );
                }
            },
            _ => {},
        }
    };
    assert forall|i: int|
        0 <= i < concrete.len() implies
            output_covered(
                #[trigger] concrete[i],
                abstract_network.push(added),
            ) by {
        let envelope = concrete[i];
        match envelope.message {
            ProductionMessage::Reply(output)
            | ProductionMessage::Send(output) => {
                if envelope.recipient == ProductionPid::Outside {
                    lemma_output_present_push(
                        abstract_network,
                        added,
                        output,
                    );
                }
            },
            _ => {},
        }
    };
}

proof fn lemma_boundary_coverage_abstract_add(
    concrete: Seq<Envelope<ProductionPid, ProductionMessage>>,
    abstract_network: Seq<Envelope<AbstractPid, AbstractMessage>>,
    added: Seq<Envelope<AbstractPid, AbstractMessage>>,
)
    requires
        boundary_covered(concrete, abstract_network),
    ensures
        boundary_covered(
            concrete,
            abstract_network + added,
        ),
    decreases added.len(),
{
    if added.len() == 0 {
        assert(abstract_network + added =~= abstract_network);
    } else {
        lemma_boundary_coverage_abstract_add(
            concrete,
            abstract_network,
            added.drop_last(),
        );
        let prefix = abstract_network + added.drop_last();
        lemma_boundary_coverage_abstract_push(
            concrete,
            prefix,
            added.last(),
        );
        assert(prefix.push(added.last())
            =~= abstract_network + added);
    }
}

proof fn lemma_boundary_covered_two_sided_append(
    concrete: Seq<Envelope<ProductionPid, ProductionMessage>>,
    abstract_network: Seq<Envelope<AbstractPid, AbstractMessage>>,
    abstract_added: Seq<Envelope<AbstractPid, AbstractMessage>>,
    sender: ProductionPid,
    send: Seq<(ProductionPid, ProductionMessage)>,
)
    requires
        boundary_covered(concrete, abstract_network),
        send_boundary_covered(
            sender,
            send,
            abstract_network + abstract_added,
        ),
    ensures
        boundary_covered(
            concrete + envelopes(sender, send),
            abstract_network + abstract_added,
        ),
{
    lemma_boundary_coverage_abstract_add(
        concrete,
        abstract_network,
        abstract_added,
    );
    lemma_boundary_covered_append_send(
        concrete,
        abstract_network + abstract_added,
        sender,
        send,
    );
}

pub open spec fn abstract_normal_step(
    config: crate::Config,
    before: World<AbstractModel>,
    call: echod_abstract::Call,
    now: u64,
) -> World<AbstractModel> {
    let state = abstract_state(before);
    let handler = echod_abstract::machine::spec_handler(
        abstract_config(config),
        call.request,
        state.store,
        now,
    );
    let outcome = echod_abstract::model::spec_request_outcome(
        state,
        call,
        handler[0],
    );
    land(
        before,
        0,
        AbstractPid::Service,
        now,
        outcome,
    )
}

/// Linearize one already-enqueued normal request through the real abstract
/// Rover process. `request_agrees` supplies the unique served handler outcome
/// and proves that normal requests enqueue no abstract internal work.
pub proof fn lemma_abstract_normal_request_step(
    config: crate::Config,
    before: World<AbstractModel>,
    call: echod_abstract::Call,
    key: Seq<char>,
    document: echod_concrete::document::StoredDocumentV,
    now: u64,
) -> (after: World<AbstractModel>)
    requires
        abstract_shaped(before),
        abstract_state(before).pending.len() == 0,
        abstract_request_present(before.network, call),
        echod_concrete::interpret::request_agrees(
            abstract_config(config),
            call.request,
            key,
            echod_concrete::node::spec_stored_body(document),
            abstract_state(before).store,
            now,
        ),
        before.now <= now,
    ensures
        after == abstract_normal_step(config, before, call, now),
        matches(
            AbstractModel,
            abstract_config(config),
            before,
            Seq::<BoundaryEvent>::empty(),
            after,
        ),
        abstract_shaped(after),
        abstract_state(after).pending.len() == 0,
        after.now == now,
        ({
            let outcomes = echod_abstract::machine::spec_handler(
                abstract_config(config),
                call.request,
                abstract_state(before).store,
                now,
            );
            &&& outcomes.len() == 1
            &&& abstract_state(after).store == outcomes[0].next
            &&& after.network == before.network + envelopes(
                AbstractPid::Service,
                echod_abstract::model::spec_send(
                    call,
                    outcomes[0].resp,
                    Seq::empty(),
                ),
            )
        }),
{
    let state = abstract_state(before);
    let handler = echod_abstract::machine::spec_handler(
        abstract_config(config),
        call.request,
        state.store,
        now,
    );
    assert(handler.len() == 1);
    assert(handler[0].work =~= Seq::empty());
    assert(handler[0].send =~= Seq::empty());
    let event = ProcessEvent::Receive {
        sender: AbstractPid::Outside,
        message: AbstractMessage::Request(call),
    };
    assert(event_valid(before, AbstractPid::Service, event)) by {
        let i = choose|i: int|
            #![trigger before.network[i]]
            0 <= i < before.network.len()
                && before.network[i] == Envelope {
                    sender: AbstractPid::Outside,
                    recipient: AbstractPid::Service,
                    message: AbstractMessage::Request(call),
                };
    };
    let outcomes = AbstractModel.spec_on_event(
        abstract_config(config),
        AbstractPid::Service,
        state,
        now,
        event,
    );
    let served = echod_abstract::model::spec_run(
        abstract_config(config),
        state,
        call,
        now,
    );
    assert(served.len() == 1);
    assert(served[0]
        == echod_abstract::model::spec_request_outcome(
            state,
            call,
            handler[0],
        ));
    assert(outcomes == served
        + echod_abstract::model::spec_losses(state, call, handler)
        + seq![echod_abstract::model::spec_shed(state, call)]);
    assert(outcomes[0] == served[0]);
    let outcome = outcomes[0];
    let after = land(
        before,
        0,
        AbstractPid::Service,
        now,
        outcome,
    );
    assert(after == abstract_normal_step(
        config,
        before,
        call,
        now,
    ));
    let label = Label::<AbstractPid, AbstractMessage>::Process {
        process: AbstractPid::Service,
        at: now,
        event,
        send: outcome.send,
    };
    assert(step(
        AbstractModel,
        abstract_config(config),
        before,
        label,
        after,
    )) by {
        reveal(step);
        assert(is_process(AbstractModel, before, AbstractPid::Service)) by {
            assert(exists|i: int|
                0 <= i < before.process.len()
                    && #[trigger] before.process[i].0
                        == AbstractPid::Service) by {
                assert(before.process[0].0 == AbstractPid::Service);
            };
        };
        assert(exists|i: int, j: int|
            #![trigger AbstractModel.spec_on_event(
                abstract_config(config),
                AbstractPid::Service,
                before.process[i].1,
                now,
                event,
            )[j]]
            {
                &&& 0 <= i < before.process.len()
                &&& before.process[i].0 == AbstractPid::Service
                &&& {
                    let actual = AbstractModel.spec_on_event(
                        abstract_config(config),
                        AbstractPid::Service,
                        before.process[i].1,
                        now,
                        event,
                    );
                    &&& 0 <= j < actual.len()
                    &&& actual[j].send == outcome.send
                    &&& after == land(
                        before,
                        i,
                        AbstractPid::Service,
                        now,
                        actual[j],
                    )
                }
            }) by {
            assert(before.process[0].1 == state);
            assert(outcomes.len() > 0);
            assert(after == land(
                before,
                0,
                AbstractPid::Service,
                now,
                outcomes[0],
            ));
        };
    };
    assert(AbstractModel.spec_observe(label)
        =~= Seq::<BoundaryEvent>::empty());
    lemma_one_step_match(
        abstract_config(config),
        before,
        label,
        after,
        Seq::empty(),
    );
    assert(outcome.send == echod_abstract::model::spec_send(
        call,
        handler[0].resp,
        Seq::empty(),
    ));
    after
}

/// A well-formed production decision candidate is the linearization point of
/// the corresponding enqueued abstract request. This theorem deliberately
/// stops before claiming the surrounding concrete world relation: cache
/// eviction and other active document lanes require the explicit frame
/// obligation below.
#[verifier::rlimit(20)]
pub proof fn lemma_normal_decision_candidate_linearizes(
    config: crate::Config,
    before: World<AbstractModel>,
    call: echod_abstract::Call,
    key: Seq<char>,
    document: echod_concrete::document::StoredDocumentV,
    now: u64,
) -> (after: World<AbstractModel>)
    requires
        abstract_shaped(before),
        abstract_state(before).pending.len() == 0,
        abstract_request_present(before.network, call),
        echod_concrete::document::well_formed(document),
        echod_concrete::quick_n_dirty::routed(
            document,
            call.request,
        ),
        echod_concrete::node::spec_key(call.request) == Some(key),
        echod_concrete::interpret::doc_rel(
            key,
            echod_concrete::node::spec_stored_body(document),
            abstract_state(before).store,
        ),
        echod_concrete::interpret::finite_store(
            abstract_state(before).store,
        ),
        echod_concrete::node::spec_stored_committed_at(document)
            <= now,
        now <= echod_types::MAX_TIME,
        0 < config.retry_timeout
            && config.retry_timeout <= echod_types::MAX_TIME,
        echod_concrete::effects::safe_effect_config(
            now,
            config.retry_timeout,
        ),
        crate::refinement::document_ids_bounded(document),
        crate::refinement::normal_request_handler_aligned(
            document,
            call.request,
            now,
            config.retry_timeout,
        ),
        before.now <= now,
    ensures
        after == abstract_normal_step(config, before, call, now),
        matches(
            AbstractModel,
            abstract_config(config),
            before,
            Seq::<BoundaryEvent>::empty(),
            after,
        ),
        abstract_shaped(after),
        abstract_state(after).pending.len() == 0,
        ({
            let outcomes = echod_abstract::machine::spec_handler(
                abstract_config(config),
                call.request,
                abstract_state(before).store,
                now,
            );
            &&& outcomes.len() == 1
            &&& abstract_state(after).store == outcomes[0].next
            &&& echod_concrete::interpret::doc_rel(
                key,
                echod_concrete::node::spec_stored_body(
                    echod_concrete::quick_n_dirty::on_request(
                        document,
                        call.request,
                        now,
                        config.retry_timeout,
                    ),
                ),
                abstract_state(after).store,
            )
            &&& echod_concrete::interpret::others_kept(
                key,
                abstract_state(before).store,
                abstract_state(after).store,
            )
            &&& echod_concrete::interpret::finite_store(
                abstract_state(after).store,
            )
        }),
{
    crate::refinement::lemma_normal_request_matches_abstract_handler(
        abstract_config(config),
        document,
        call.request,
        key,
        abstract_state(before).store,
        now,
    );
    let after = lemma_abstract_normal_request_step(
        config,
        before,
        call,
        key,
        document,
        now,
    );
    let handler = echod_abstract::machine::spec_handler(
        abstract_config(config),
        call.request,
        abstract_state(before).store,
        now,
    );
    after
}

/// The concrete successful-Get slice closed below. It identifies the original
/// request flight and requires that the actual `on_event` result has reached a
/// direct conditional document write. Store-key actions that precede the
/// document write and failed decodes are distinct slices.
pub open spec fn normal_get_direct_write_candidate(
    node: ProductionNodeV,
    call: echod_abstract::Call,
    document: echod_concrete::document::StoredDocumentV,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
    decision_now: u64,
) -> bool {
    &&& node.core.node.members.next_heartbeat is Some
    &&& node.core.out.len() == 0
    &&& node.core.ops.contains_key(op)
    &&& node.core.ops[op] == crate::state::Owner::Flight(fid)
    &&& node.core.flights.inflight.contains_key(fid)
    &&& {
        let flight = node.core.flights.inflight[fid];
        &&& flight.id == fid
        &&& flight.phase == crate::handler_docs::PhaseSpec::Loading {
            op,
            revalidating: None,
        }
        &&& flight.firing is None
        &&& !flight.debug
        &&& match flight.work {
            crate::handler_docs::WorkSpec::Request {
                id,
                kind,
                corr,
                req,
                action_kind,
                ..
            } => {
                &&& id == call.id
                &&& kind.len() == 0
                &&& corr == call.client@
                &&& req == call.request
                &&& action_kind is None
            },
            _ => false,
        }
    }
    &&& match response {
        echod_concrete::store::StoreRes::Get {
            result: Ok(_),
        } => true,
        _ => false,
    }
    &&& {
        let (core, _) = crate::handler::spec_on_event(
            node.core,
            crate::types::EventSpec::Store {
                op,
                response,
                clock: at,
            },
        );
        &&& core.flights.inflight.contains_key(fid)
        &&& match core.flights.inflight[fid].phase {
            crate::handler_docs::PhaseSpec::Origin {
                commit,
                ..
            } => {
                &&& commit.w.loaded.document == document
                &&& commit.now == decision_now
                &&& match commit.issued {
                    Some(crate::handler_docs::IssuedSpec::Write {
                        ..
                    }) => true,
                    _ => false,
                }
            },
            _ => false,
        }
    }
}

/// The document and semantic part of the node relation, separated from
/// production control facts for focused handler-path proofs.
pub open spec fn normal_decision_data_frame(
    node: ProductionNodeV,
    abstract_state: echod_abstract::model::StateV,
) -> bool {
    &&& retained_documents_well_formed(node.core)
    &&& cache_related(
        node.core.cache,
        node.core.flights,
        abstract_state.store,
    )
    &&& flights_related(node.core.flights, abstract_state.store)
}

pub open spec fn node_control_frame(node: ProductionNodeV) -> bool {
    &&& node.core.out.len() == 0
    &&& operation_id_fresh(node.core)
    &&& flight_id_fresh(node.core)
    &&& active_flight_keys_distinct(node.core.flights)
    &&& owners_consistent(node.core)
    &&& membership_consistent(node.core)
    &&& timers_consistent(node.core.timers)
    &&& flight_lanes_consistent(node.core.flights)
}

proof fn lemma_effects_preserve_core(
    node: ProductionNodeV,
    now: u64,
    effects: Seq<crate::types::EffectSpec>,
)
    ensures
        crate::rover::spec_effects(node, now, effects).0.core
            == node.core,
    decreases effects.len(),
{
    reveal(crate::rover::spec_effects);
    if effects.len() > 0 {
        lemma_effects_preserve_core(
            node,
            now,
            effects.drop_last(),
        );
        reveal(crate::rover::spec_effect);
    }
}

/// The remaining physical-read/codec premise for the successful uncached Get:
/// the concrete Store response decodes to the document used by the decision.
pub open spec fn normal_get_codec_law(
    node: ProductionNodeV,
    origin: Seq<char>,
    document: echod_concrete::document::StoredDocumentV,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
    loaded_state: crate::state::StateSpec,
    working: crate::handler_docs::WorkingSpec,
) -> bool {
    let clocked = crate::state::StateSpec {
        clock: at,
        ..node.core
    };
    let without_op = crate::state::StateSpec {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    let without_flight =
        crate::handler_docs::spec_take_flight(without_op, fid);
    &&& crate::handler_docs::spec_loaded_origin(
        without_flight,
        origin,
        None,
        response,
    ) == (loaded_state, Ok(working))
    &&& working.loaded.document == document
    &&& crate::refinement::loaded_document_well_formed(
        working.loaded,
    )
}

proof fn lemma_loaded_origin_preserves_control_fields(
    s: crate::state::StateSpec,
    origin: Seq<char>,
    response: echod_concrete::store::StoreRes,
    loaded_state: crate::state::StateSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        crate::handler_docs::spec_loaded_origin(
            s,
            origin,
            None,
            response,
        ) == (loaded_state, Ok(working)),
    ensures
        loaded_state.cfg == s.cfg,
        loaded_state.ops == s.ops,
        loaded_state.next_op == s.next_op,
        loaded_state.next_flight == s.next_flight,
        loaded_state.flights == s.flights,
        loaded_state.timers == s.timers,
        loaded_state.out == s.out,
        loaded_state.node.core.id == s.node.core.id,
        loaded_state.node.core.ttl == s.node.core.ttl,
        loaded_state.node.core.members == s.node.core.members,
        crate::refinement::cache_entries_carried_except(
            s.cache,
            loaded_state.cache,
            origin,
        ),
{
    reveal(crate::handler_docs::spec_loaded_origin);
    match response {
        echod_concrete::store::StoreRes::Get { result } => {
            match result {
                Ok(Some((bytes, etag))) => {
                    match crate::document::spec_decode_workflow(bytes@) {
                        Ok(loaded) => {
                            crate::refinement::
                                lemma_cache_put_carries_unrelated_entries(
                                    s.cache,
                                    origin,
                                    crate::cache::CachedSpec {
                                        loaded,
                                        etag: etag.deep_view(),
                                        filled_at: crate::state::spec_now(s),
                                    },
                                );
                            crate::refinement::
                                lemma_remember_preserves_control_fields(
                                    s,
                                    origin,
                                    crate::cache::CachedSpec {
                                        loaded,
                                        etag: etag.deep_view(),
                                        filled_at: crate::state::spec_now(s),
                                    },
                                );
                        },
                        Err(_) => assert(false),
                    }
                },
                Ok(None) => {},
                Err(_) => assert(false),
            }
        },
        _ => assert(false),
    }
}

/// Restricted direct-write decision law. In addition to excluding
/// pre-write key actions, it explicitly carries the still-unproved
/// production decision-body correspondence.
pub open spec fn normal_get_direct_issue_law(
    loaded_state: crate::state::StateSpec,
    working: crate::handler_docs::WorkingSpec,
    work: crate::handler_docs::WorkSpec,
    fid: u64,
    expected_after: echod_concrete::document::StoredDocumentV,
) -> bool {
    let (decided_state, commit, _) =
        crate::handler_docs::spec_decide(
            loaded_state,
            work,
            working,
        );
    let (_, issued_commit, progress) =
        crate::handler_docs::spec_commit_advance(
            decided_state,
            fid,
            commit,
            None,
        );
    &&& progress == crate::handler_docs::ProgressSpec::Issued
    &&& match issued_commit.issued {
        Some(crate::handler_docs::IssuedSpec::Write { .. }) => true,
        _ => false,
    }
    &&& echod_concrete::node::spec_stored_body(
        issued_commit.after,
    ) == echod_concrete::node::spec_stored_body(expected_after)
}

#[verifier::rlimit(30)]
proof fn lemma_normal_get_actual_shape(
    node: ProductionNodeV,
    call: echod_abstract::Call,
    origin: Seq<char>,
    document: echod_concrete::document::StoredDocumentV,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
    decision_now: u64,
    loaded_state: crate::state::StateSpec,
    working: crate::handler_docs::WorkingSpec,
    next: ProductionNodeV,
)
    requires
        node_control_frame(node),
        operation_successor_fresh(node.core),
        node.core.flights.inflight[fid].target
            == crate::target::TargetSpec::Origin(origin),
        normal_get_codec_law(
            node,
            origin,
            document,
            fid,
            op,
            response,
            at,
            loaded_state,
            working,
        ),
        normal_get_direct_issue_law(
            loaded_state,
            working,
            node.core.flights.inflight[fid].work,
            fid,
            echod_concrete::quick_n_dirty::on_request(
                document,
                call.request,
                decision_now,
                node.core.cfg.retry_timeout,
            ),
        ),
        normal_get_direct_write_candidate(
            node,
            call,
            document,
            fid,
            op,
            response,
            at,
            decision_now,
        ),
        next == ({
            let (core, effects) = crate::handler::spec_on_event(
                node.core,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: at,
                },
            );
            let (expected, _) = crate::rover::spec_effects(
                ProductionNodeV { core, ..node },
                at,
                effects,
            );
            expected
        }),
    ensures
        ({
            let flight = node.core.flights.inflight[fid];
            let (decided_state, commit, done) =
                crate::handler_docs::spec_decide(
                    loaded_state,
                    flight.work,
                    working,
                );
            let (issued_state, issued_commit, _) =
                crate::handler_docs::spec_commit_advance(
                    decided_state,
                    fid,
                    commit,
                    None,
                );
            let replacement = crate::handler_docs::FlightSpec {
                phase: crate::handler_docs::PhaseSpec::Origin {
                    commit: issued_commit,
                    done,
                },
                ..crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::Idle,
                    ..flight
                }
            };
            let before_schedule =
                crate::handler_docs::spec_inflight(
                    issued_state,
                    replacement,
                );
            let scheduled =
                crate::handler::spec_schedule_wake(before_schedule);
            next.core == crate::state::StateSpec {
                out: Seq::empty(),
                ..scheduled
            }
        }),
{
    reveal(normal_get_direct_write_candidate);
    reveal(normal_get_codec_law);
    reveal(normal_get_direct_issue_law);
    reveal(crate::handler_docs::spec_loaded_origin);
    reveal(node_control_frame);
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler_docs::spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    reveal(crate::handler_docs::spec_answered_loading);
    reveal(crate::handler_docs::spec_loaded_origin);
    reveal(crate::handler_docs::spec_run_origin);
    reveal(crate::handler_docs::spec_decide);
    reveal(crate::handler_docs::spec_commit_new);
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::handler_docs::spec_committed);
    reveal(crate::handler_docs::spec_finish);
    reveal(crate::handler_docs::spec_release);
    reveal(crate::handler_docs::spec_resume);
    reveal(crate::handler_docs::spec_commit_failed);
    reveal(crate::handler_docs::spec_retry);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_fail);
    reveal(crate::handler::spec_schedule_wake);
    let flight = node.core.flights.inflight[fid];
    let clocked = crate::state::StateSpec {
        clock: at,
        ..node.core
    };
    let without_op = crate::state::StateSpec {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    let without_flight =
        crate::handler_docs::spec_take_flight(without_op, fid);
    let (decided_state, commit, done) =
        crate::handler_docs::spec_decide(
            loaded_state,
            flight.work,
            working,
        );
    let (issued_state, issued_commit, progress) =
        crate::handler_docs::spec_commit_advance(
            decided_state,
            fid,
            commit,
            None,
        );
    assert(flight.work
        == node.core.flights.inflight[fid].work);
    assert(normal_get_direct_issue_law(
        loaded_state,
        working,
        flight.work,
        fid,
        echod_concrete::quick_n_dirty::on_request(
            document,
            call.request,
            decision_now,
            node.core.cfg.retry_timeout,
        ),
    ));
    assert(progress == crate::handler_docs::ProgressSpec::Issued);
    let (handler_core, handler_effects) =
        crate::handler::spec_on_event(
            node.core,
            crate::types::EventSpec::Store {
                op,
                response,
                clock: at,
            },
        );
    assert(handler_core.flights.inflight.contains_key(fid));
    match issued_commit.issued {
        Some(crate::handler_docs::IssuedSpec::Write {
            op: write_op,
            mode,
            change_count,
            bytes,
            len,
        }) => {
            crate::refinement::lemma_successful_get_issues_direct_write(
                without_flight,
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::Idle,
                    ..flight
                },
                origin,
                response,
                loaded_state,
                working,
                decided_state,
                commit,
                done,
                issued_state,
                issued_commit,
                write_op,
                mode,
                change_count,
                bytes,
                len,
            );
        },
        _ => assert(false),
    }
    let core = handler_core;
    let effects = handler_effects;
    lemma_effects_preserve_core(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );
    let (actual_next, _) = crate::rover::spec_effects(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );
    assert(next == actual_next);
}

#[verifier::rlimit(30)]
proof fn lemma_normal_get_actual_control(
    node: ProductionNodeV,
    call: echod_abstract::Call,
    origin: Seq<char>,
    document: echod_concrete::document::StoredDocumentV,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
    decision_now: u64,
    loaded_state: crate::state::StateSpec,
    working: crate::handler_docs::WorkingSpec,
    next: ProductionNodeV,
)
    requires
        node_control_frame(node),
        operation_successor_fresh(node.core),
        node.core.flights.inflight[fid].target
            == crate::target::TargetSpec::Origin(origin),
        normal_get_codec_law(
            node,
            origin,
            document,
            fid,
            op,
            response,
            at,
            loaded_state,
            working,
        ),
        normal_get_direct_issue_law(
            loaded_state,
            working,
            node.core.flights.inflight[fid].work,
            fid,
            echod_concrete::quick_n_dirty::on_request(
                document,
                call.request,
                decision_now,
                node.core.cfg.retry_timeout,
            ),
        ),
        normal_get_direct_write_candidate(
            node,
            call,
            document,
            fid,
            op,
            response,
            at,
            decision_now,
        ),
        next == ({
            let (core, effects) = crate::handler::spec_on_event(
                node.core,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: at,
                },
            );
            crate::rover::spec_effects(
                ProductionNodeV { core, ..node },
                at,
                effects,
            ).0
        }),
    ensures node_control_frame(next),
{
    reveal(normal_get_direct_write_candidate);
    reveal(node_control_frame);
    reveal(normal_get_codec_law);
    reveal(normal_get_direct_issue_law);
    reveal(crate::handler_docs::spec_loaded_origin);
    reveal(crate::handler_docs::spec_decide);
    reveal(crate::handler_docs::spec_commit_new);
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::handler::spec_schedule_wake);
    lemma_normal_get_actual_shape(
        node,
        call,
        origin,
        document,
        fid,
        op,
        response,
        at,
        decision_now,
        loaded_state,
        working,
        next,
    );
    let flight = node.core.flights.inflight[fid];
    let clocked = crate::state::StateSpec {
        clock: at,
        ..node.core
    };
    let without_op = crate::state::StateSpec {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    let without_flight =
        crate::handler_docs::spec_take_flight(without_op, fid);
    lemma_loaded_origin_preserves_control_fields(
        without_flight,
        origin,
        response,
        loaded_state,
        working,
    );
    let (decided_state, commit, done) =
        crate::handler_docs::spec_decide(
            loaded_state,
            flight.work,
            working,
        );
    let (issued_state, issued_commit, _) =
        crate::handler_docs::spec_commit_advance(
            decided_state,
            fid,
            commit,
            None,
        );
    let replacement = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Origin {
            commit: issued_commit,
            done,
        },
        ..crate::handler_docs::FlightSpec {
            phase: crate::handler_docs::PhaseSpec::Idle,
            ..flight
        }
    };
    let before_schedule = crate::handler_docs::spec_inflight(
        issued_state,
        replacement,
    );
    crate::refinement::
        lemma_inflight_replacement_preserves_lane_keys(
            node.core,
            fid,
            replacement,
        );
    crate::refinement::
        lemma_inflight_replacement_preserves_lane_owner(
            node.core,
            fid,
            replacement,
        );
    let scheduled =
        crate::handler::spec_schedule_wake(before_schedule);
    assert(next.core == crate::state::StateSpec {
        out: Seq::empty(),
        ..scheduled
    });
    assert(next.core.out.len() == 0);
    assert(operation_id_fresh(next.core));
    assert(flight_id_fresh(next.core));
    assert(active_flight_keys_distinct(next.core.flights));
    match issued_commit.issued {
        Some(crate::handler_docs::IssuedSpec::Write {
            op: write_op,
            ..
        }) => {
            assert(!node.core.ops.contains_key(write_op));
            assert(next.core.ops
                == node.core.ops.remove(op).insert(
                    write_op,
                    crate::state::Owner::Flight(fid),
                ));
            assert(next.core.flights.inflight
                == node.core.flights.inflight.remove(fid).insert(
                    fid,
                    replacement,
                ));
            crate::refinement::lemma_direct_write_preserves_owners(
                node.core,
                next.core,
                fid,
                op,
                write_op,
                replacement,
            );
        },
        _ => assert(false),
    }
    assert(owners_consistent(next.core));
    assert(next.core.cfg == node.core.cfg);
    assert(next.core.node.core.id == node.core.node.core.id);
    assert(next.core.node.core.ttl == node.core.node.core.ttl);
    assert(next.core.node.core.members
        == node.core.node.core.members);
    assert(node.core.node.core.members.no_duplicates());
    assert(next.core.node.core.members.no_duplicates());
    assert(membership_consistent(next.core));
    assert(timers_consistent(next.core.timers));
    assert(flight_lanes_consistent(next.core.flights));
    lemma_control_facts_imply_frame(next);
}

proof fn lemma_control_facts_imply_frame(node: ProductionNodeV)
    requires
        node.core.out.len() == 0,
        operation_id_fresh(node.core),
        flight_id_fresh(node.core),
        active_flight_keys_distinct(node.core.flights),
        owners_consistent(node.core),
        membership_consistent(node.core),
        timers_consistent(node.core.timers),
        flight_lanes_consistent(node.core.flights),
    ensures node_control_frame(node),
{
}

proof fn lemma_schedule_wake_preserves_data(
    s: crate::state::StateSpec,
)
    ensures
        crate::handler::spec_schedule_wake(s).cache == s.cache,
        crate::handler::spec_schedule_wake(s).flights == s.flights,
{
    reveal(crate::handler::spec_schedule_wake);
}

proof fn lemma_schedule_wake_preserves_internal_effects(
    s: crate::state::StateSpec,
)
    requires internal_effects(s.out),
    ensures
        internal_effects(
            crate::handler::spec_schedule_wake(s).out,
        ),
{
    reveal(crate::handler::spec_schedule_wake);
    assert forall|i: int|
        0 <= i
            < crate::handler::spec_schedule_wake(s).out.len()
        implies internal_effect(
            #[trigger]
            crate::handler::spec_schedule_wake(s).out[i],
        ) by {
        if i < s.out.len() {
            assert(
                crate::handler::spec_schedule_wake(s).out[i]
                    == s.out[i]
            );
        }
    };
}

#[verifier::rlimit(30)]
proof fn lemma_normal_get_actual_internal_effects(
    node: ProductionNodeV,
    call: echod_abstract::Call,
    origin: Seq<char>,
    document: echod_concrete::document::StoredDocumentV,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
    decision_now: u64,
    loaded_state: crate::state::StateSpec,
    working: crate::handler_docs::WorkingSpec,
)
    requires
        node_control_frame(node),
        operation_successor_fresh(node.core),
        node.core.flights.inflight[fid].target
            == crate::target::TargetSpec::Origin(origin),
        normal_get_codec_law(
            node,
            origin,
            document,
            fid,
            op,
            response,
            at,
            loaded_state,
            working,
        ),
        normal_get_direct_issue_law(
            loaded_state,
            working,
            node.core.flights.inflight[fid].work,
            fid,
            echod_concrete::quick_n_dirty::on_request(
                document,
                call.request,
                decision_now,
                node.core.cfg.retry_timeout,
            ),
        ),
        normal_get_direct_write_candidate(
            node,
            call,
            document,
            fid,
            op,
            response,
            at,
            decision_now,
        ),
    ensures
        ({
            let (_, effects) = crate::handler::spec_on_event(
                node.core,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: at,
                },
            );
            internal_effects(effects)
        }),
{
    reveal(normal_get_direct_write_candidate);
    reveal(normal_get_codec_law);
    reveal(normal_get_direct_issue_law);
    reveal(node_control_frame);
    reveal(crate::handler::spec_on_event);
    reveal(crate::handler_docs::spec_flight_completed);
    reveal(crate::handler_docs::spec_answered_phase);
    reveal(crate::handler_docs::spec_answered_loading);
    reveal(crate::handler_docs::spec_loaded_origin);
    reveal(crate::handler_docs::spec_run_origin);
    reveal(crate::handler_docs::spec_decide);
    reveal(crate::handler_docs::spec_commit_new);
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::handler::spec_schedule_wake);
    let flight = node.core.flights.inflight[fid];
    let clocked = crate::state::StateSpec {
        clock: at,
        ..node.core
    };
    let without_op = crate::state::StateSpec {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    let without_flight =
        crate::handler_docs::spec_take_flight(without_op, fid);
    lemma_loaded_origin_preserves_control_fields(
        without_flight,
        origin,
        response,
        loaded_state,
        working,
    );
    let (decided_state, commit, done) =
        crate::handler_docs::spec_decide(
            loaded_state,
            flight.work,
            working,
        );
    let (issued_state, issued_commit, progress) =
        crate::handler_docs::spec_commit_advance(
            decided_state,
            fid,
            commit,
            None,
        );
    assert(progress == crate::handler_docs::ProgressSpec::Issued);
    match issued_commit.issued {
        Some(crate::handler_docs::IssuedSpec::Write {
            op: write_op,
            mode,
            change_count,
            bytes,
            len,
        }) => {
            crate::refinement::lemma_successful_get_issues_direct_write(
                without_flight,
                crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::Idle,
                    ..flight
                },
                origin,
                response,
                loaded_state,
                working,
                decided_state,
                commit,
                done,
                issued_state,
                issued_commit,
                write_op,
                mode,
                change_count,
                bytes,
                len,
            );
        },
        _ => assert(false),
    }
    let replacement = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Origin {
            commit: issued_commit,
            done,
        },
        ..crate::handler_docs::FlightSpec {
            phase: crate::handler_docs::PhaseSpec::Idle,
            ..flight
        }
    };
    let before_schedule = crate::handler_docs::spec_inflight(
        issued_state,
        replacement,
    );
    assert(internal_effects(before_schedule.out));
    lemma_schedule_wake_preserves_internal_effects(
        before_schedule,
    );
}

#[verifier::rlimit(30)]
proof fn lemma_normal_get_actual_data_shape(
    node: ProductionNodeV,
    call: echod_abstract::Call,
    origin: Seq<char>,
    document: echod_concrete::document::StoredDocumentV,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
    decision_now: u64,
    loaded_state: crate::state::StateSpec,
    working: crate::handler_docs::WorkingSpec,
    next: ProductionNodeV,
)
    requires
        node_control_frame(node),
        operation_successor_fresh(node.core),
        node.core.flights.inflight.contains_key(fid),
        node.core.flights.inflight[fid].target
            == crate::target::TargetSpec::Origin(origin),
        normal_get_codec_law(
            node,
            origin,
            document,
            fid,
            op,
            response,
            at,
            loaded_state,
            working,
        ),
        normal_get_direct_issue_law(
            loaded_state,
            working,
            node.core.flights.inflight[fid].work,
            fid,
            echod_concrete::quick_n_dirty::on_request(
                document,
                call.request,
                decision_now,
                node.core.cfg.retry_timeout,
            ),
        ),
        normal_get_direct_write_candidate(
            node,
            call,
            document,
            fid,
            op,
            response,
            at,
            decision_now,
        ),
        next == ({
            let (core, effects) = crate::handler::spec_on_event(
                node.core,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: at,
                },
            );
            crate::rover::spec_effects(
                ProductionNodeV { core, ..node },
                at,
                effects,
            ).0
        }),
    ensures
        ({
            let flight = node.core.flights.inflight[fid];
            let (decided_state, commit, done) =
                crate::handler_docs::spec_decide(
                    loaded_state,
                    flight.work,
                    working,
                );
            let (_, issued_commit, _) =
                crate::handler_docs::spec_commit_advance(
                    decided_state,
                    fid,
                    commit,
                    None,
                );
            let replacement = crate::handler_docs::FlightSpec {
                phase: crate::handler_docs::PhaseSpec::Origin {
                    commit: issued_commit,
                    done,
                },
                ..crate::handler_docs::FlightSpec {
                    phase: crate::handler_docs::PhaseSpec::Idle,
                    ..flight
                }
            };
            &&& echod_concrete::node::spec_stored_body(
                issued_commit.after,
            ) == echod_concrete::node::spec_stored_body(
                echod_concrete::quick_n_dirty::on_request(
                    document,
                    call.request,
                    decision_now,
                    node.core.cfg.retry_timeout,
                ),
            )
            &&& crate::refinement::cache_entries_carried_except(
                node.core.cache,
                next.core.cache,
                origin,
            )
            &&& next.core.flights.inflight
                == node.core.flights.inflight.remove(fid).insert(
                    fid,
                    replacement,
                )
        }),
{
    reveal(normal_get_direct_write_candidate);
    reveal(normal_get_direct_issue_law);
    reveal(crate::handler_docs::spec_decide);
    reveal(crate::handler_docs::spec_commit_new);
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::handler::spec_schedule_wake);
    lemma_normal_get_actual_shape(
        node,
        call,
        origin,
        document,
        fid,
        op,
        response,
        at,
        decision_now,
        loaded_state,
        working,
        next,
    );
    let flight = node.core.flights.inflight[fid];
    let clocked = crate::state::StateSpec {
        clock: at,
        ..node.core
    };
    let without_op = crate::state::StateSpec {
        ops: clocked.ops.remove(op),
        ..clocked
    };
    let without_flight =
        crate::handler_docs::spec_take_flight(without_op, fid);
    lemma_loaded_origin_preserves_control_fields(
        without_flight,
        origin,
        response,
        loaded_state,
        working,
    );
    let (decided_state, commit, done) =
        crate::handler_docs::spec_decide(
            loaded_state,
            flight.work,
            working,
        );
    let (issued_state, issued_commit, progress) =
        crate::handler_docs::spec_commit_advance(
            decided_state,
            fid,
            commit,
            None,
        );
    let replacement = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Origin {
            commit: issued_commit,
            done,
        },
        ..crate::handler_docs::FlightSpec {
            phase: crate::handler_docs::PhaseSpec::Idle,
            ..flight
        }
    };
    let before_schedule = crate::handler_docs::spec_inflight(
        issued_state,
        replacement,
    );
    lemma_schedule_wake_preserves_data(before_schedule);
    assert(next.core.cache == loaded_state.cache);
    assert(echod_concrete::node::spec_stored_body(
        issued_commit.after,
    ) == echod_concrete::node::spec_stored_body(
        echod_concrete::quick_n_dirty::on_request(
            document,
            call.request,
            decision_now,
            node.core.cfg.retry_timeout,
        ),
    ));
    assert(crate::refinement::cache_entries_carried_except(
        node.core.cache,
        next.core.cache,
        origin,
    ));
    assert(next.core.flights.inflight
        == node.core.flights.inflight.remove(fid).insert(
            fid,
            replacement,
        ));
}

#[verifier::rlimit(30)]
proof fn lemma_normal_get_actual_semantic_relations(
    node: ProductionNodeV,
    call: echod_abstract::Call,
    key: Seq<char>,
    origin: Seq<char>,
    document: echod_concrete::document::StoredDocumentV,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
    decision_now: u64,
    loaded_state: crate::state::StateSpec,
    working: crate::handler_docs::WorkingSpec,
    next: ProductionNodeV,
    abstract_before: echod_abstract::view::StoreV,
    abstract_after: echod_abstract::view::StoreV,
)
    requires
        node_control_frame(node),
        operation_successor_fresh(node.core),
        cache_related(
            node.core.cache,
            node.core.flights,
            abstract_before,
        ),
        flights_related(node.core.flights, abstract_before),
        active_flight_keys_distinct(node.core.flights),
        key == crate::refinement::logical_key(
            crate::target::TargetSpec::Origin(origin),
        ),
        node.core.flights.inflight[fid].target
            == crate::target::TargetSpec::Origin(origin),
        normal_get_codec_law(
            node,
            origin,
            document,
            fid,
            op,
            response,
            at,
            loaded_state,
            working,
        ),
        normal_get_direct_issue_law(
            loaded_state,
            working,
            node.core.flights.inflight[fid].work,
            fid,
            echod_concrete::quick_n_dirty::on_request(
                document,
                call.request,
                decision_now,
                node.core.cfg.retry_timeout,
            ),
        ),
        normal_get_direct_write_candidate(
            node,
            call,
            document,
            fid,
            op,
            response,
            at,
            decision_now,
        ),
        next == ({
            let (core, effects) = crate::handler::spec_on_event(
                node.core,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: at,
                },
            );
            crate::rover::spec_effects(
                ProductionNodeV { core, ..node },
                at,
                effects,
            ).0
        }),
        echod_concrete::interpret::doc_rel(
            key,
            echod_concrete::node::spec_stored_body(
                echod_concrete::quick_n_dirty::on_request(
                    document,
                    call.request,
                    decision_now,
                    node.core.cfg.retry_timeout,
                ),
            ),
            abstract_after,
        ),
        echod_concrete::interpret::others_kept(
            key,
            abstract_before,
            abstract_after,
        ),
    ensures
        cache_related(
            next.core.cache,
            next.core.flights,
            abstract_after,
        ),
        flights_related(next.core.flights, abstract_after),
{
    lemma_normal_get_actual_data_shape(
        node,
        call,
        origin,
        document,
        fid,
        op,
        response,
        at,
        decision_now,
        loaded_state,
        working,
        next,
    );
    let flight = node.core.flights.inflight[fid];
    let (decided_state, commit, done) =
        crate::handler_docs::spec_decide(
            loaded_state,
            flight.work,
            working,
        );
    let (issued_state, issued_commit, _) =
        crate::handler_docs::spec_commit_advance(
            decided_state,
            fid,
            commit,
            None,
        );
    let replacement = crate::handler_docs::FlightSpec {
        phase: crate::handler_docs::PhaseSpec::Origin {
            commit: issued_commit,
            done,
        },
        ..crate::handler_docs::FlightSpec {
            phase: crate::handler_docs::PhaseSpec::Idle,
            ..flight
        }
    };
    crate::refinement::lemma_decision_preserves_semantic_relations(
        node.core,
        next.core,
        fid,
        origin,
        replacement,
        issued_commit.after,
        abstract_before,
        abstract_after,
    );
}

proof fn lemma_node_frames_imply_related(
    node: ProductionNodeV,
    state: echod_abstract::model::StateV,
)
    requires
        normal_decision_data_frame(node, state),
        node_control_frame(node),
        state.pending.len() == 0,
    ensures node_related(node, state),
{
}

proof fn lemma_world_frames_imply_related(
    concrete: World<ProductionModel>,
    abstract_world: World<AbstractModel>,
)
    requires
        production_shaped(concrete),
        abstract_shaped(abstract_world),
        abstract_world.now <= concrete.now,
        node_related(
            production_node(concrete),
            abstract_state(abstract_world),
        ),
        boundary_covered(concrete.network, abstract_world.network),
    ensures world_related(concrete, abstract_world),
{
}

proof fn lemma_world_related_node_facts(
    concrete: World<ProductionModel>,
    abstract_world: World<AbstractModel>,
)
    requires world_related(concrete, abstract_world),
    ensures
        node_control_frame(production_node(concrete)),
        retained_documents_well_formed(
            production_node(concrete).core,
        ),
        cache_related(
            production_node(concrete).core.cache,
            production_node(concrete).core.flights,
            abstract_state(abstract_world).store,
        ),
        flights_related(
            production_node(concrete).core.flights,
            abstract_state(abstract_world).store,
        ),
        boundary_covered(
            concrete.network,
            abstract_world.network,
        ),
{
}

proof fn lemma_store_response_node_step(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
    send: Seq<(ProductionPid, ProductionMessage)>,
    concrete_after: World<ProductionModel>,
) -> (next: ProductionNodeV)
    requires
        production_shaped(concrete_before),
        step(
            ProductionModel,
            config,
            concrete_before,
            Label::Process {
                process: ProductionPid::Node(0),
                at,
                event: ProcessEvent::Receive {
                    sender: ProductionPid::Store,
                    message: ProductionMessage::StoreRes {
                        op,
                        response,
                    },
                },
                send,
            },
            concrete_after,
        ),
    ensures
        next == production_node(concrete_after),
        ({
            let node = production_node(concrete_before);
            let (core, effects) = crate::handler::spec_on_event(
                node.core,
                crate::types::EventSpec::Store {
                    op,
                    response,
                    clock: at,
                },
            );
            let (expected, actual_send) = crate::rover::spec_effects(
                ProductionNodeV { core, ..node },
                at,
                effects,
            );
            &&& next == expected
            &&& send == actual_send
        }),
        concrete_after.process[1] == concrete_before.process[1],
        concrete_after.network
            == concrete_before.network
                + envelopes(ProductionPid::Node(0), send),
        concrete_after.now == at,
        production_shaped(concrete_after),
{
    reveal(step);
    let event = ProcessEvent::Receive {
        sender: ProductionPid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    let i = choose|i: int|
        #![trigger concrete_before.process[i]]
        exists|j: int|
        #![trigger ProductionModel.spec_on_event(
            config,
            ProductionPid::Node(0),
            concrete_before.process[i].1,
            at,
            event,
        )[j]]
        {
            &&& 0 <= i < concrete_before.process.len()
            &&& concrete_before.process[i].0
                == ProductionPid::Node(0)
            &&& {
                let outcomes = ProductionModel.spec_on_event(
                    config,
                    ProductionPid::Node(0),
                    concrete_before.process[i].1,
                    at,
                    event,
                );
                &&& 0 <= j < outcomes.len()
                &&& outcomes[j].send == send
                &&& concrete_after == land(
                    concrete_before,
                    i,
                    ProductionPid::Node(0),
                    at,
                    outcomes[j],
                )
            }
        };
    let j = choose|j: int|
        #![trigger ProductionModel.spec_on_event(
            config,
            ProductionPid::Node(0),
            concrete_before.process[i].1,
            at,
            event,
        )[j]]
        {
            let outcomes = ProductionModel.spec_on_event(
                config,
                ProductionPid::Node(0),
                concrete_before.process[i].1,
                at,
                event,
            );
            &&& 0 <= j < outcomes.len()
            &&& outcomes[j].send == send
            &&& concrete_after == land(
                concrete_before,
                i,
                ProductionPid::Node(0),
                at,
                outcomes[j],
            )
        };
    assert(i == 0);
    let node = production_node(concrete_before);
    assert(concrete_before.process[0].1
        == ProductionLocalV::Node(node));
    let outcomes = ProductionModel.spec_on_event(
        config,
        ProductionPid::Node(0),
        concrete_before.process[0].1,
        at,
        event,
    );
    assert(outcomes == crate::rover::spec_node_step(
        node,
        at,
        event,
    ));
    assert(outcomes.len() == 1);
    assert(j == 0);
    let (core, effects) = crate::handler::spec_on_event(
        node.core,
        crate::types::EventSpec::Store {
            op,
            response,
            clock: at,
        },
    );
    let (next, actual_send) = crate::rover::spec_effects(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );
    assert(send == actual_send);
    assert(concrete_after.process[0].1
        == ProductionLocalV::Node(next));
    assert(production_node(concrete_after) == next);
    assert(concrete_after.process[1]
        == concrete_before.process[1]);
    assert(concrete_after.network
        == concrete_before.network
            + envelopes(ProductionPid::Node(0), send));
    assert(concrete_after.now == at);
    assert(production_shaped(concrete_after));
    next
}

proof fn lemma_successful_get_world_frames(
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    concrete_after: World<ProductionModel>,
    abstract_after: World<AbstractModel>,
    abstract_added: Seq<Envelope<AbstractPid, AbstractMessage>>,
    send: Seq<(ProductionPid, ProductionMessage)>,
)
    requires
        world_related(concrete_before, abstract_before),
        production_shaped(concrete_before),
        abstract_shaped(abstract_before),
        abstract_state(abstract_before).pending.len() == 0,
        production_shaped(concrete_after),
        abstract_shaped(abstract_after),
        abstract_after.now <= concrete_after.now,
        abstract_state(abstract_after).pending.len() == 0,
        normal_decision_data_frame(
            production_node(concrete_after),
            abstract_state(abstract_after),
        ),
        node_control_frame(production_node(concrete_after)),
        concrete_after.network
            == concrete_before.network
                + envelopes(ProductionPid::Node(0), send),
        abstract_after.network
            == abstract_before.network + abstract_added,
        send_boundary_covered(
            ProductionPid::Node(0),
            send,
            abstract_after.network,
        ),
    ensures world_related(concrete_after, abstract_after),
{
    lemma_node_frames_imply_related(
        production_node(concrete_after),
        abstract_state(abstract_after),
    );
    lemma_boundary_covered_two_sided_append(
        concrete_before.network,
        abstract_before.network,
        abstract_added,
        ProductionPid::Node(0),
        send,
    );
    lemma_world_frames_imply_related(
        concrete_after,
        abstract_after,
    );
}

/// Actual world-step simulation for the successful uncached Get that directly
/// issues a conditional write, under the explicit concurrent/cache frame
/// above. The production label is hidden; the matching abstract execution
/// consumes the enqueued request at the production decision time.
#[verifier::rlimit(30)]
pub proof fn lemma_framed_successful_get_world_step(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    call: echod_abstract::Call,
    key: Seq<char>,
    origin: Seq<char>,
    document: echod_concrete::document::StoredDocumentV,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    decision_now: u64,
    at: u64,
    loaded_state: crate::state::StateSpec,
    working: crate::handler_docs::WorkingSpec,
    send: Seq<(ProductionPid, ProductionMessage)>,
    concrete_after: World<ProductionModel>,
    abstract_after: World<AbstractModel>,
)
    requires
        world_related(concrete_before, abstract_before),
        production_shaped(concrete_before),
        abstract_shaped(abstract_before),
        abstract_state(abstract_before).pending.len() == 0,
        production_node(concrete_before).core.cfg
            == config.deep_view(),
        abstract_request_present(abstract_before.network, call),
        operation_successor_fresh(
            production_node(concrete_before).core,
        ),
        production_node(concrete_before)
            .core.flights.inflight[fid].target
            == crate::target::TargetSpec::Origin(origin),
        key == crate::refinement::logical_key(
            crate::target::TargetSpec::Origin(origin),
        ),
        normal_get_codec_law(
            production_node(concrete_before),
            origin,
            document,
            fid,
            op,
            response,
            at,
            loaded_state,
            working,
        ),
        normal_get_direct_issue_law(
            loaded_state,
            working,
            production_node(concrete_before)
                .core.flights.inflight[fid].work,
            fid,
            echod_concrete::quick_n_dirty::on_request(
                document,
                call.request,
                decision_now,
                production_node(concrete_before)
                    .core.cfg.retry_timeout,
            ),
        ),
        normal_get_direct_write_candidate(
            production_node(concrete_before),
            call,
            document,
            fid,
            op,
            response,
            at,
            decision_now,
        ),
        abstract_after == abstract_normal_step(
            config,
            abstract_before,
            call,
            decision_now,
        ),
        retained_documents_well_formed(
            production_node(concrete_after).core,
        ),
        echod_concrete::document::well_formed(document),
        echod_concrete::quick_n_dirty::routed(
            document,
            call.request,
        ),
        echod_concrete::node::spec_key(call.request) == Some(key),
        echod_concrete::interpret::doc_rel(
            key,
            echod_concrete::node::spec_stored_body(document),
            abstract_state(abstract_before).store,
        ),
        echod_concrete::interpret::finite_store(
            abstract_state(abstract_before).store,
        ),
        echod_concrete::node::spec_stored_committed_at(document)
            <= decision_now,
        abstract_before.now <= decision_now,
        decision_now <= at,
        at <= echod_types::MAX_TIME,
        0 < config.retry_timeout
            && config.retry_timeout <= echod_types::MAX_TIME,
        echod_concrete::effects::safe_effect_config(
            decision_now,
            config.retry_timeout,
        ),
        crate::refinement::document_ids_bounded(document),
        crate::refinement::normal_request_handler_aligned(
            document,
            call.request,
            decision_now,
            config.retry_timeout,
        ),
        step(
            ProductionModel,
            config,
            concrete_before,
            Label::Process {
                process: ProductionPid::Node(0),
                at,
                event: ProcessEvent::Receive {
                    sender: ProductionPid::Store,
                    message: ProductionMessage::StoreRes {
                        op,
                        response,
                    },
                },
                send,
            },
            concrete_after,
        ),
    ensures
        abstract_after == abstract_normal_step(
            config,
            abstract_before,
            call,
            decision_now,
        ),
        matches(
            AbstractModel,
            abstract_config(config),
            abstract_before,
            Seq::<BoundaryEvent>::empty(),
            abstract_after,
        ),
        world_related(concrete_after, abstract_after),
{
    hide(world_related);
    hide(step);
    hide(normal_get_direct_write_candidate);
    hide(abstract_request_present);
    hide(echod_concrete::document::well_formed);
    hide(echod_concrete::quick_n_dirty::routed);
    hide(echod_concrete::node::spec_key);
    hide(echod_concrete::interpret::doc_rel);
    hide(echod_concrete::interpret::finite_store);
    hide(echod_concrete::node::spec_stored_committed_at);
    hide(echod_concrete::effects::safe_effect_config);
    hide(crate::refinement::document_ids_bounded);
    hide(crate::refinement::normal_request_handler_aligned);
    lemma_world_related_node_facts(
        concrete_before,
        abstract_before,
    );
    let linearized =
        lemma_normal_decision_candidate_linearizes(
            config,
            abstract_before,
            call,
            key,
            document,
            decision_now,
        );
    assert(linearized == abstract_after);
    let next = lemma_store_response_node_step(
        config,
        concrete_before,
        op,
        response,
        at,
        send,
        concrete_after,
    );
    let handler = echod_abstract::machine::spec_handler(
        abstract_config(config),
        call.request,
        abstract_state(abstract_before).store,
        decision_now,
    );
    let abstract_added = envelopes(
        AbstractPid::Service,
        echod_abstract::model::spec_send(
            call,
            handler[0].resp,
            Seq::empty(),
        ),
    );
    assert(abstract_after.network
        == abstract_before.network + abstract_added);
    lemma_normal_get_actual_control(
        production_node(concrete_before),
        call,
        origin,
        document,
        fid,
        op,
        response,
        at,
        decision_now,
        loaded_state,
        working,
        next,
    );
    lemma_normal_get_actual_semantic_relations(
        production_node(concrete_before),
        call,
        key,
        origin,
        document,
        fid,
        op,
        response,
        at,
        decision_now,
        loaded_state,
        working,
        next,
        abstract_state(abstract_before).store,
        abstract_state(abstract_after).store,
    );
    assert(normal_decision_data_frame(
        production_node(concrete_after),
        abstract_state(abstract_after),
    ));
    lemma_normal_get_actual_internal_effects(
        production_node(concrete_before),
        call,
        origin,
        document,
        fid,
        op,
        response,
        at,
        decision_now,
        loaded_state,
        working,
    );
    let (handler_core, handler_effects) =
        crate::handler::spec_on_event(
            production_node(concrete_before).core,
            crate::types::EventSpec::Store {
                op,
                response,
                clock: at,
            },
        );
    lemma_internal_effects_send_to_store(
        ProductionNodeV {
            core: handler_core,
            ..production_node(concrete_before)
        },
        at,
        handler_effects,
    );
    lemma_store_only_send_boundary_covered(
        ProductionPid::Node(0),
        send,
        abstract_after.network,
    );
    lemma_successful_get_world_frames(
        concrete_before,
        abstract_before,
        concrete_after,
        abstract_after,
        abstract_added,
        send,
    );
    assert(world_related(concrete_after, abstract_after));
}

pub open spec fn successful_conditional_response(
    response: echod_concrete::store::StoreRes,
) -> bool {
    match response {
        echod_concrete::store::StoreRes::PutIfMatch {
            result: Ok(_),
        }
        | echod_concrete::store::StoreRes::PutIfNoneMatch {
            result: Ok(_),
        }
        | echod_concrete::store::StoreRes::AppIfMatch {
            result: Ok(_),
        } => true,
        _ => false,
    }
}

pub open spec fn normal_write_commit_candidate(
    node: ProductionNodeV,
    call: echod_abstract::Call,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
) -> bool {
    &&& node.core.node.members.next_heartbeat is Some
    &&& node.core.out.len() == 0
    &&& successful_conditional_response(response)
    &&& node.core.ops.contains_key(op)
    &&& node.core.ops[op] == crate::state::Owner::Flight(fid)
    &&& node.core.flights.inflight.contains_key(fid)
    &&& {
        let flight = node.core.flights.inflight[fid];
        &&& match flight.work {
            crate::handler_docs::WorkSpec::Request {
                id,
                corr,
                req,
                ..
            } => {
                &&& id == call.id
                &&& corr == call.client@
                &&& req == call.request
            },
            _ => false,
        }
        &&& match flight.phase {
            crate::handler_docs::PhaseSpec::Origin {
                commit,
                ..
            } => match commit.issued {
                Some(crate::handler_docs::IssuedSpec::Write {
                    op: issued_op,
                    ..
                }) => issued_op == op,
                _ => false,
            },
            _ => false,
        }
    }
    &&& {
        let (_, effects) = crate::handler::spec_on_event(
            node.core,
            crate::types::EventSpec::Store {
                op,
                response,
                clock: at,
            },
        );
        exists|i: int|
            0 <= i < effects.len()
                && match #[trigger] effects[i] {
                    crate::types::EffectSpec::Reply {
                        id,
                        ..
                    } => id == call.id,
                    _ => false,
                }
    }
}

/// Actual successful conditional-write completion as an abstract stutter.
/// Reply/Send messages may be appended by this step; the explicit frame
/// requires that each is the output already emitted by the abstract handler
/// at `lemma_framed_successful_get_world_step`.
#[verifier::rlimit(30)]
pub proof fn lemma_framed_successful_write_commit_world_step(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    call: echod_abstract::Call,
    fid: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    at: u64,
    send: Seq<(ProductionPid, ProductionMessage)>,
    concrete_after: World<ProductionModel>,
)
    requires
        world_related(concrete_before, abstract_before),
        normal_write_commit_candidate(
            production_node(concrete_before),
            call,
            fid,
            op,
            response,
            at,
        ),
        normal_decision_data_frame(
            production_node(concrete_after),
            abstract_state(abstract_before),
        ),
        node_control_frame(production_node(concrete_after)),
        send_boundary_covered(
            ProductionPid::Node(0),
            send,
            abstract_before.network,
        ),
        step(
            ProductionModel,
            config,
            concrete_before,
            Label::Process {
                process: ProductionPid::Node(0),
                at,
                event: ProcessEvent::Receive {
                    sender: ProductionPid::Store,
                    message: ProductionMessage::StoreRes {
                        op,
                        response,
                    },
                },
                send,
            },
            concrete_after,
        ),
    ensures
        matches(
            AbstractModel,
            abstract_config(config),
            abstract_before,
            Seq::<BoundaryEvent>::empty(),
            abstract_before,
        ),
        world_related(concrete_after, abstract_before),
{
    reveal(step);
    let event = ProcessEvent::Receive {
        sender: ProductionPid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    let i = choose|i: int|
        #![trigger concrete_before.process[i]]
        exists|j: int|
        #![trigger ProductionModel.spec_on_event(
            config,
            ProductionPid::Node(0),
            concrete_before.process[i].1,
            at,
            event,
        )[j]]
        {
            &&& 0 <= i < concrete_before.process.len()
            &&& concrete_before.process[i].0
                == ProductionPid::Node(0)
            &&& {
                let outcomes = ProductionModel.spec_on_event(
                    config,
                    ProductionPid::Node(0),
                    concrete_before.process[i].1,
                    at,
                    event,
                );
                &&& 0 <= j < outcomes.len()
                &&& outcomes[j].send == send
                &&& concrete_after == land(
                    concrete_before,
                    i,
                    ProductionPid::Node(0),
                    at,
                    outcomes[j],
                )
            }
        };
    let j = choose|j: int|
        #![trigger ProductionModel.spec_on_event(
            config,
            ProductionPid::Node(0),
            concrete_before.process[i].1,
            at,
            event,
        )[j]]
        {
            let outcomes = ProductionModel.spec_on_event(
                config,
                ProductionPid::Node(0),
                concrete_before.process[i].1,
                at,
                event,
            );
            &&& 0 <= j < outcomes.len()
            &&& outcomes[j].send == send
            &&& concrete_after == land(
                concrete_before,
                i,
                ProductionPid::Node(0),
                at,
                outcomes[j],
            )
        };
    assert(i == 0);
    let node = production_node(concrete_before);
    assert(concrete_before.process[0].1
        == ProductionLocalV::Node(node));
    let outcomes = ProductionModel.spec_on_event(
        config,
        ProductionPid::Node(0),
        concrete_before.process[0].1,
        at,
        event,
    );
    assert(outcomes == crate::rover::spec_node_step(
        node,
        at,
        event,
    ));
    assert(outcomes.len() == 1);
    assert(j == 0);
    let (core, effects) = crate::handler::spec_on_event(
        node.core,
        crate::types::EventSpec::Store {
            op,
            response,
            clock: at,
        },
    );
    let (next, actual_send) = crate::rover::spec_effects(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );
    assert(send == actual_send);
    assert(concrete_after.process[0].1
        == ProductionLocalV::Node(next));
    assert(production_node(concrete_after) == next);
    assert(concrete_after.process[1]
        == concrete_before.process[1]);
    assert(concrete_after.network
        == concrete_before.network
            + envelopes(ProductionPid::Node(0), send));
    assert(concrete_after.now == at);
    assert(production_shaped(concrete_after));
    assert(abstract_before.now <= concrete_after.now);
    lemma_node_frames_imply_related(
        next,
        abstract_state(abstract_before),
    );
    assert(node_related(
        production_node(concrete_after),
        abstract_state(abstract_before),
    ));
    lemma_boundary_covered_append_send(
        concrete_before.network,
        abstract_before.network,
        ProductionPid::Node(0),
        send,
    );
    assert(boundary_covered(
        concrete_after.network,
        abstract_before.network,
    ));
    lemma_world_frames_imply_related(
        concrete_after,
        abstract_before,
    );
    lemma_empty_match(
        abstract_config(config),
        abstract_before,
    );
}

/// A production input label is matched by the same abstract input label.
/// This closes the first label of every request slice.
pub proof fn lemma_input_slice(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    recipient: ProductionPid,
    at: u64,
    message: ProductionMessage,
    concrete_after: World<ProductionModel>,
) -> (abstract_after: World<AbstractModel>)
    requires
        world_related(concrete_before, abstract_before),
        step(
            ProductionModel,
            config,
            concrete_before,
            Label::Input { recipient, at, message },
            concrete_after,
        ),
    ensures
        matches(
            AbstractModel,
            abstract_config(config),
            abstract_before,
            ProductionModel.spec_observe(
                Label::Input { recipient, at, message },
            ),
            abstract_after,
        ),
        world_related(concrete_after, abstract_after),
{
    reveal(step);
    assert(ProductionModel.spec_injectable(config, message));
    match message {
        ProductionMessage::Request(call) => {
            let abstract_label =
                Label::<AbstractPid, AbstractMessage>::Input {
                    recipient: AbstractPid::Service,
                    at,
                    message: AbstractMessage::Request(call),
                };
            let abstract_message = AbstractMessage::Request(call);
            let abstract_after = inject(
                abstract_before,
                AbstractPid::Outside,
                AbstractPid::Service,
                at,
                abstract_message,
            );
            assert(AbstractModel.spec_injectable(
                abstract_config(config),
                abstract_message,
            ));
            assert(step(
                AbstractModel,
                abstract_config(config),
                abstract_before,
                abstract_label,
                abstract_after,
            ));
            let visible =
                seq![BoundaryEvent::Input { at, call }];
            assert(ProductionModel.spec_observe(
                Label::Input { recipient, at, message },
            ) =~= visible);
            assert(AbstractModel.spec_observe(abstract_label)
                =~= visible);
            lemma_one_step_match(
                abstract_config(config),
                abstract_before,
                abstract_label,
                abstract_after,
                visible,
            );
            assert(concrete_after == inject(
                concrete_before,
                ProductionPid::Outside,
                recipient,
                at,
                message,
            ));
            let concrete_added = Envelope {
                sender: ProductionPid::Outside,
                recipient,
                message,
            };
            let abstract_added = Envelope {
                sender: AbstractPid::Outside,
                recipient: AbstractPid::Service,
                message: abstract_message,
            };
            assert(concrete_after.network
                == concrete_before.network.push(concrete_added));
            assert(abstract_after.network
                == abstract_before.network.push(abstract_added));
            lemma_boundary_coverage_abstract_push(
                concrete_before.network,
                abstract_before.network,
                abstract_added,
            );
            assert(abstract_request_present(
                abstract_after.network,
                call,
            )) by {
                let i = abstract_before.network.len() as int;
                assert(0 <= i < abstract_after.network.len());
                assert(abstract_after.network[i]
                    == abstract_added);
            };
            assert(request_covered(
                concrete_added,
                abstract_after.network,
            ));
            assert(output_covered(
                concrete_added,
                abstract_after.network,
            ));
            assert forall|i: int|
                0 <= i < concrete_after.network.len() implies
                    request_covered(
                        #[trigger] concrete_after.network[i],
                        abstract_after.network,
                    ) by {
                if i < concrete_before.network.len() {
                    assert(concrete_after.network[i]
                        == concrete_before.network[i]);
                } else {
                    assert(i == concrete_before.network.len());
                    assert(concrete_after.network[i]
                        == concrete_added);
                }
            };
            assert forall|i: int|
                0 <= i < concrete_after.network.len() implies
                    output_covered(
                        #[trigger] concrete_after.network[i],
                        abstract_after.network,
                    ) by {
                if i < concrete_before.network.len() {
                    assert(concrete_after.network[i]
                        == concrete_before.network[i]);
                } else {
                    assert(i == concrete_before.network.len());
                    assert(concrete_after.network[i]
                        == concrete_added);
                }
            };
            assert(concrete_after.process
                == concrete_before.process);
            assert(abstract_after.process
                == abstract_before.process);
            assert(production_node(concrete_after)
                == production_node(concrete_before));
            assert(abstract_state(abstract_after)
                == abstract_state(abstract_before));
            abstract_after
        },
        _ => {
            assert(false);
            abstract_before
        },
    }
}

/// A Reply or Send observed at the production outside is observed from the
/// already-covered abstract output envelope. Hidden outside traffic stutters.
pub proof fn lemma_outside_slice(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    sender: ProductionPid,
    at: u64,
    message: ProductionMessage,
    concrete_after: World<ProductionModel>,
) -> (abstract_after: World<AbstractModel>)
    requires
        world_related(concrete_before, abstract_before),
        step(
            ProductionModel,
            config,
            concrete_before,
            Label::Outside { sender, at, message },
            concrete_after,
        ),
    ensures
        matches(
            AbstractModel,
            abstract_config(config),
            abstract_before,
            ProductionModel.spec_observe(
                Label::Outside { sender, at, message },
            ),
            abstract_after,
        ),
        world_related(concrete_after, abstract_after),
{
    reveal(step);
    assert(concrete_after
        == observe_outside(concrete_before, at));
    let wanted = Envelope {
        sender,
        recipient: ProductionPid::Outside,
        message,
    };
    let i = choose|i: int|
        0 <= i < concrete_before.network.len()
            && #[trigger] concrete_before.network[i] == wanted;
    match message {
        ProductionMessage::Reply(output)
        | ProductionMessage::Send(output) => {
            assert(output_covered(
                concrete_before.network[i],
                abstract_before.network,
            ));
            assert(abstract_output_present(
                abstract_before.network,
                output,
            ));
            let j = choose|j: int|
                #![trigger abstract_before.network[j]]
                0 <= j < abstract_before.network.len()
                    && abstract_before.network[j] == Envelope {
                        sender: AbstractPid::Service,
                        recipient: AbstractPid::Outside,
                        message: AbstractMessage::Output(output),
                    };
            let abstract_label =
                Label::<AbstractPid, AbstractMessage>::Outside {
                    sender: AbstractPid::Service,
                    at,
                    message: AbstractMessage::Output(output),
                };
            let abstract_after =
                observe_outside(abstract_before, at);
            assert(step(
                AbstractModel,
                abstract_config(config),
                abstract_before,
                abstract_label,
                abstract_after,
            ));
            let visible =
                seq![BoundaryEvent::Output { at, output }];
            assert(ProductionModel.spec_observe(
                Label::Outside { sender, at, message },
            ) =~= visible);
            assert(AbstractModel.spec_observe(abstract_label)
                =~= visible);
            lemma_one_step_match(
                abstract_config(config),
                abstract_before,
                abstract_label,
                abstract_after,
                visible,
            );
            assert(concrete_after.process
                == concrete_before.process);
            assert(abstract_after.process
                == abstract_before.process);
            assert(concrete_after.network
                == concrete_before.network);
            assert(abstract_after.network
                == abstract_before.network);
            abstract_after
        },
        _ => {
            lemma_empty_match(
                abstract_config(config),
                abstract_before,
            );
            assert(ProductionModel.spec_observe(
                Label::Outside { sender, at, message },
            ) =~= Seq::<BoundaryEvent>::empty());
            assert(concrete_after.process
                == concrete_before.process);
            assert(concrete_after.network
                == concrete_before.network);
            abstract_before
        },
    }
}

/// Executing the adapter's store process is an abstract stutter. The step may
/// append a StoreRes envelope, but it cannot change the production node or add
/// a boundary-visible message.
pub proof fn lemma_store_process_slice(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    at: u64,
    event: ProcessEvent<ProductionPid, ProductionMessage>,
    send: Seq<(ProductionPid, ProductionMessage)>,
    concrete_after: World<ProductionModel>,
)
    requires
        world_related(concrete_before, abstract_before),
        step(
            ProductionModel,
            config,
            concrete_before,
            Label::Process {
                process: ProductionPid::Store,
                at,
                event,
                send,
            },
            concrete_after,
        ),
    ensures
        matches(
            AbstractModel,
            abstract_config(config),
            abstract_before,
            Seq::<BoundaryEvent>::empty(),
            abstract_before,
        ),
        world_related(concrete_after, abstract_before),
{
    reveal(step);
    let i = choose|i: int|
        #![trigger concrete_before.process[i]]
        exists|j: int|
        #![trigger ProductionModel.spec_on_event(
            config,
            ProductionPid::Store,
            concrete_before.process[i].1,
            at,
            event,
        )[j]]
        {
            &&& 0 <= i < concrete_before.process.len()
            &&& concrete_before.process[i].0
                == ProductionPid::Store
            &&& {
                let outcomes = ProductionModel.spec_on_event(
                    config,
                    ProductionPid::Store,
                    concrete_before.process[i].1,
                    at,
                    event,
                );
                &&& 0 <= j < outcomes.len()
                &&& outcomes[j].send == send
                &&& concrete_after == land(
                    concrete_before,
                    i,
                    ProductionPid::Store,
                    at,
                    outcomes[j],
                )
            }
        };
    let j = choose|j: int|
        #![trigger ProductionModel.spec_on_event(
            config,
            ProductionPid::Store,
            concrete_before.process[i].1,
            at,
            event,
        )[j]]
        {
            let outcomes = ProductionModel.spec_on_event(
                config,
                ProductionPid::Store,
                concrete_before.process[i].1,
                at,
                event,
            );
            &&& 0 <= j < outcomes.len()
            &&& outcomes[j].send == send
            &&& concrete_after == land(
                concrete_before,
                i,
                ProductionPid::Store,
                at,
                outcomes[j],
            )
        };
    assert(i == 1);
    assert(concrete_before.process[1].1 is Store);
    let outcomes = ProductionModel.spec_on_event(
        config,
        ProductionPid::Store,
        concrete_before.process[1].1,
        at,
        event,
    );
    assert(outcomes == crate::rover::spec_store_step(
        concrete_before.process[1].1->Store_0,
        event,
    ));
    match event {
        ProcessEvent::Receive {
            sender,
            message: ProductionMessage::StoreReq { op, request },
        } => {
            assert(outcomes.len() == 1);
            assert(j == 0);
            if concrete_before.process[1].1->Store_0
                .seen.contains((sender, op))
            {
                assert(send
                    =~= Seq::<(ProductionPid, ProductionMessage)>::empty());
            } else {
                let (_, response) =
                    echod_concrete::store::spec_apply(
                        concrete_before.process[1].1->Store_0,
                        request,
                    );
                assert(send == seq![(
                    sender,
                    ProductionMessage::StoreRes { op, response },
                )]);
            }
        },
        _ => {
            assert(outcomes.len() == 0);
            assert(false);
        },
    }
    assert(concrete_after.process.len()
        == concrete_before.process.len());
    assert(concrete_after.process[0]
        == concrete_before.process[0]);
    assert(production_node(concrete_after)
        == production_node(concrete_before));
    assert(concrete_after.network
        == concrete_before.network
            + envelopes(ProductionPid::Store, send));
    assert forall|k: int|
        concrete_before.network.len()
            <= k < concrete_after.network.len()
        implies request_covered(
            #[trigger] concrete_after.network[k],
            abstract_before.network,
        ) && output_covered(
            concrete_after.network[k],
            abstract_before.network,
        ) by {
        let added = envelopes(ProductionPid::Store, send);
        assert(concrete_after.network[k]
            == added[k - concrete_before.network.len()]);
        assert(0 <= k - concrete_before.network.len()
            < added.len());
        assert(added[k - concrete_before.network.len()].message
            is StoreRes);
    };
    assert forall|k: int|
        0 <= k < concrete_after.network.len()
        implies request_covered(
            #[trigger] concrete_after.network[k],
            abstract_before.network,
        ) by {
        if k < concrete_before.network.len() {
            assert(concrete_after.network[k]
                == concrete_before.network[k]);
        }
    };
    assert forall|k: int|
        0 <= k < concrete_after.network.len()
        implies output_covered(
            #[trigger] concrete_after.network[k],
            abstract_before.network,
        ) by {
        if k < concrete_before.network.len() {
            assert(concrete_after.network[k]
                == concrete_before.network[k]);
        }
    };
    lemma_empty_match(
        abstract_config(config),
        abstract_before,
    );
}

proof fn lemma_wake_effects_stutter(
    node: ProductionNodeV,
    now: u64,
    effects: Seq<crate::types::EffectSpec>,
)
    requires
        effects.len() <= 1,
        forall|i: int| 0 <= i < effects.len() ==>
            #[trigger] effects[i] is Wake,
    ensures
        ({
            let (next, send) =
                crate::rover::spec_effects(node, now, effects);
            &&& next.core == node.core
            &&& next.pending == node.pending
            &&& send.len() == 0
        }),
    decreases effects.len(),
{
    reveal(crate::rover::spec_effects);
    reveal(crate::rover::spec_effect);
    if effects.len() > 0 {
        assert(effects.len() == 1);
        assert(effects.drop_last()
            =~= Seq::<crate::types::EffectSpec>::empty());
        lemma_wake_effects_stutter(
            node,
            now,
            effects.drop_last(),
        );
        match effects.last() {
            crate::types::EffectSpec::Wake { .. } => {},
            _ => assert(false),
        }
    }
}

/// A Store response whose operation is unknown to a production node is an
/// actual hidden Node step. With membership already scheduled, `on_event`
/// only advances clock/wake bookkeeping, so the abstract service stutters and
/// the complete world relation is preserved.
pub proof fn lemma_unknown_store_response_slice(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
    at: u64,
    op: u64,
    response: echod_concrete::store::StoreRes,
    send: Seq<(ProductionPid, ProductionMessage)>,
    concrete_after: World<ProductionModel>,
)
    requires
        world_related(concrete_before, abstract_before),
        production_node(concrete_before)
            .core.node.members.next_heartbeat is Some,
        !production_node(concrete_before)
            .core.ops.contains_key(op),
        step(
            ProductionModel,
            config,
            concrete_before,
            Label::Process {
                process: ProductionPid::Node(0),
                at,
                event: ProcessEvent::Receive {
                    sender: ProductionPid::Store,
                    message: ProductionMessage::StoreRes {
                        op,
                        response,
                    },
                },
                send,
            },
            concrete_after,
        ),
    ensures
        matches(
            AbstractModel,
            abstract_config(config),
            abstract_before,
            Seq::<BoundaryEvent>::empty(),
            abstract_before,
        ),
        world_related(concrete_after, abstract_before),
{
    reveal(step);
    let event = ProcessEvent::Receive {
        sender: ProductionPid::Store,
        message: ProductionMessage::StoreRes { op, response },
    };
    let i = choose|i: int|
        #![trigger concrete_before.process[i]]
        exists|j: int|
        #![trigger ProductionModel.spec_on_event(
            config,
            ProductionPid::Node(0),
            concrete_before.process[i].1,
            at,
            event,
        )[j]]
        {
            &&& 0 <= i < concrete_before.process.len()
            &&& concrete_before.process[i].0
                == ProductionPid::Node(0)
            &&& {
                let outcomes = ProductionModel.spec_on_event(
                    config,
                    ProductionPid::Node(0),
                    concrete_before.process[i].1,
                    at,
                    event,
                );
                &&& 0 <= j < outcomes.len()
                &&& outcomes[j].send == send
                &&& concrete_after == land(
                    concrete_before,
                    i,
                    ProductionPid::Node(0),
                    at,
                    outcomes[j],
                )
            }
        };
    let j = choose|j: int|
        #![trigger ProductionModel.spec_on_event(
            config,
            ProductionPid::Node(0),
            concrete_before.process[i].1,
            at,
            event,
        )[j]]
        {
            let outcomes = ProductionModel.spec_on_event(
                config,
                ProductionPid::Node(0),
                concrete_before.process[i].1,
                at,
                event,
            );
            &&& 0 <= j < outcomes.len()
            &&& outcomes[j].send == send
            &&& concrete_after == land(
                concrete_before,
                i,
                ProductionPid::Node(0),
                at,
                outcomes[j],
            )
        };
    assert(i == 0);
    let node = production_node(concrete_before);
    assert(concrete_before.process[0].1
        == ProductionLocalV::Node(node));
    let outcomes = ProductionModel.spec_on_event(
        config,
        ProductionPid::Node(0),
        concrete_before.process[0].1,
        at,
        event,
    );
    assert(outcomes == crate::rover::spec_node_step(
        node,
        at,
        event,
    ));
    assert(outcomes.len() == 1);
    assert(j == 0);
    let (core, effects) = crate::handler::spec_on_event(
        node.core,
        crate::types::EventSpec::Store {
            op,
            response,
            clock: at,
        },
    );
    crate::refinement::lemma_unknown_store_response_preserves_relation_fields(
        node.core,
        op,
        response,
        at,
    );
    lemma_wake_effects_stutter(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );
    let (next, actual_send) = crate::rover::spec_effects(
        ProductionNodeV { core, ..node },
        at,
        effects,
    );
    assert(send == actual_send);
    assert(send =~= Seq::<(ProductionPid, ProductionMessage)>::empty());
    assert(next.core == core);
    assert(next.pending == node.pending);
    assert(core.ops == node.core.ops);
    assert(core.cache == node.core.cache);
    assert(core.flights == node.core.flights);
    assert(core.node == node.core.node);
    assert(core.timers == node.core.timers);
    assert(core.cfg == node.core.cfg);
    assert(core.next_op == node.core.next_op);
    assert(core.next_flight == node.core.next_flight);
    assert(core.out.len() == 0);
    assert(concrete_after.process[0].1
        == ProductionLocalV::Node(next));
    assert(production_node(concrete_after).core == core);
    assert(concrete_after.process[1]
        == concrete_before.process[1]);
    assert(concrete_after.network
        == concrete_before.network);
    assert(concrete_after.now == at);
    assert(abstract_before.now <= concrete_after.now);
    assert(production_shaped(concrete_after));
    assert(abstract_shaped(abstract_before));
    assert(node_related(
        production_node(concrete_after),
        abstract_state(abstract_before),
    )) by {
        assert(production_node(concrete_after).core.out.len() == 0);
        assert(operation_id_fresh(
            production_node(concrete_after).core,
        ));
        assert(flight_id_fresh(
            production_node(concrete_after).core,
        ));
        assert(retained_documents_well_formed(
            production_node(concrete_after).core,
        ));
        assert(active_flight_keys_distinct(
            production_node(concrete_after).core.flights,
        ));
        assert(owners_consistent(
            production_node(concrete_after).core,
        ));
        assert(membership_consistent(
            production_node(concrete_after).core,
        ));
        assert(timers_consistent(
            production_node(concrete_after).core.timers,
        ));
        assert(flight_lanes_consistent(
            production_node(concrete_after).core.flights,
        ));
        assert(cache_related(
            production_node(concrete_after).core.cache,
            production_node(concrete_after).core.flights,
            abstract_state(abstract_before).store,
        ));
        assert(flights_related(
            production_node(concrete_after).core.flights,
            abstract_state(abstract_before).store,
        ));
    };
    assert(boundary_covered(
        concrete_after.network,
        abstract_before.network,
    ));
    assert(ProductionModel.spec_observe(
        Label::Process {
            process: ProductionPid::Node(0),
            at,
            event,
            send,
        },
    ) =~= Seq::<BoundaryEvent>::empty());
    lemma_empty_match(
        abstract_config(config),
        abstract_before,
    );
}

/// Labels for which the production adapter currently has a closed world-step
/// proof. Node process steps are deliberately excluded: those are the request,
/// completion, membership, and timer cases that must be discharged separately.
pub open spec fn completed_slice(
    label: Label<ProductionPid, ProductionMessage>,
) -> bool {
    match label {
        Label::Input { .. } => true,
        Label::Outside { .. } => true,
        Label::Process { process, .. } =>
            process == ProductionPid::Store,
    }
}

pub open spec fn unknown_response_slice(
    before: World<ProductionModel>,
    label: Label<ProductionPid, ProductionMessage>,
) -> bool {
    match label {
        Label::Process {
            process: ProductionPid::Node(0),
            event: ProcessEvent::Receive {
                sender: ProductionPid::Store,
                message: ProductionMessage::StoreRes { op, .. },
            },
            ..
        } => {
            &&& production_node(before)
                .core.node.members.next_heartbeat is Some
            &&& !production_node(before)
                .core.ops.contains_key(op)
        },
        _ => false,
    }
}

pub open spec fn completed_transition(
    before: World<ProductionModel>,
    label: Label<ProductionPid, ProductionMessage>,
) -> bool {
    completed_slice(label) || unknown_response_slice(before, label)
}

/// Exhaustive Node-process arms which are not yet discharged by the generic
/// world relation. The variants follow the executable adapter's three event
/// forms and split Store completions by their production owner.
pub ghost enum OpenEventArm {
    OriginRequest,
    ScheduleRequest,
    EmptyHeartbeatRequest,
    RequestFlightStore,
    SweepFlightStore,
    ScheduleFireStore,
    MembershipStore,
    TimerStore,
    DebugStore,
    IgnoredStore,
    UnownedStore,
    HeartbeatTimeout,
    WheelTimeout,
}

pub open spec fn open_node_event_arm(
    node: ProductionNodeV,
    event: ProcessEvent<ProductionPid, ProductionMessage>,
    arm: OpenEventArm,
) -> bool {
    match arm {
        OpenEventArm::OriginRequest => match event {
            ProcessEvent::Receive {
                sender: ProductionPid::Outside,
                message: ProductionMessage::Request(call),
            } => match crate::rover::spec_target(call.request) {
                Some(crate::target::TargetSpec::Origin(_)) => true,
                _ => false,
            },
            _ => false,
        },
        OpenEventArm::ScheduleRequest => match event {
            ProcessEvent::Receive {
                sender: ProductionPid::Outside,
                message: ProductionMessage::Request(call),
            } => match crate::rover::spec_target(call.request) {
                Some(crate::target::TargetSpec::Schedule(_)) => true,
                _ => false,
            },
            _ => false,
        },
        OpenEventArm::EmptyHeartbeatRequest => match event {
            ProcessEvent::Receive {
                sender: ProductionPid::Outside,
                message: ProductionMessage::Request(call),
            } => {
                &&& crate::rover::spec_target(call.request) is None
                &&& crate::rover::spec_empty_heartbeat(call.request)
            },
            _ => false,
        },
        OpenEventArm::RequestFlightStore
        | OpenEventArm::SweepFlightStore
        | OpenEventArm::ScheduleFireStore => match event {
            ProcessEvent::Receive {
                sender: ProductionPid::Store,
                message: ProductionMessage::StoreRes { op, .. },
            } => {
                &&& node.core.ops.contains_key(op)
                &&& node.core.ops[op] is Flight
                &&& node.core.flights.inflight.contains_key(
                    node.core.ops[op]->Flight_0,
                )
                &&& match (
                    arm,
                    node.core.flights.inflight[
                        node.core.ops[op]->Flight_0
                    ].work,
                ) {
                    (
                        OpenEventArm::RequestFlightStore,
                        crate::handler_docs::WorkSpec::Request { .. },
                    ) => true,
                    (
                        OpenEventArm::SweepFlightStore,
                        crate::handler_docs::WorkSpec::Sweep { .. },
                    ) => true,
                    (
                        OpenEventArm::ScheduleFireStore,
                        crate::handler_docs::WorkSpec::Fire { .. },
                    ) => true,
                    _ => false,
                }
            },
            _ => false,
        },
        OpenEventArm::MembershipStore
        | OpenEventArm::TimerStore
        | OpenEventArm::DebugStore
        | OpenEventArm::IgnoredStore => match event {
            ProcessEvent::Receive {
                sender: ProductionPid::Store,
                message: ProductionMessage::StoreRes { op, .. },
            } => {
                &&& node.core.ops.contains_key(op)
                &&& match (arm, node.core.ops[op]) {
                    (
                        OpenEventArm::MembershipStore,
                        crate::state::Owner::Members,
                    ) => true,
                    (
                        OpenEventArm::TimerStore,
                        crate::state::Owner::Timers,
                    ) => true,
                    (
                        OpenEventArm::DebugStore,
                        crate::state::Owner::Debug,
                    ) => true,
                    (
                        OpenEventArm::IgnoredStore,
                        crate::state::Owner::Ignored,
                    ) => true,
                    _ => false,
                }
            },
            _ => false,
        },
        OpenEventArm::UnownedStore => match event {
            ProcessEvent::Receive {
                sender: ProductionPid::Store,
                message: ProductionMessage::StoreRes { op, .. },
            } => !node.core.ops.contains_key(op),
            _ => false,
        },
        OpenEventArm::HeartbeatTimeout => match event {
            ProcessEvent::Timeout => match node.wake {
                Some((_, crate::types::Armed::Heartbeat)) => true,
                _ => false,
            },
            _ => false,
        },
        OpenEventArm::WheelTimeout => match event {
            ProcessEvent::Timeout => match node.wake {
                Some((_, crate::types::Armed::Wheel)) => true,
                _ => false,
            },
            _ => false,
        },
    }
}

pub open spec fn open_transition(
    before: World<ProductionModel>,
    label: Label<ProductionPid, ProductionMessage>,
) -> bool {
    match label {
        Label::Process {
            process: ProductionPid::Node(0),
            event,
            ..
        } => {
            exists|arm: OpenEventArm|
                open_node_event_arm(production_node(before), event, arm)
        },
        _ => false,
    }
}

/// The executable node has no fourth event family. Every nonempty local node
/// step is classified by one of the finite arms above.
pub proof fn lemma_node_event_arm_is_exhaustive(
    node: ProductionNodeV,
    state: echod_abstract::model::StateV,
    at: u64,
    event: ProcessEvent<ProductionPid, ProductionMessage>,
)
    requires
        node_related(node, state),
        crate::rover::spec_node_step(node, at, event).len() > 0,
    ensures
        exists|arm: OpenEventArm|
            open_node_event_arm(node, event, arm),
{
    match event {
        ProcessEvent::Receive { sender, message } => match sender {
            ProductionPid::Outside => match message {
                ProductionMessage::Request(call) => {
                    match crate::rover::spec_target(call.request) {
                        Some(target) => match target {
                            crate::target::TargetSpec::Origin(_) => {
                                assert(open_node_event_arm(
                                    node,
                                    event,
                                    OpenEventArm::OriginRequest,
                                ));
                            },
                            crate::target::TargetSpec::Schedule(_) => {
                                assert(open_node_event_arm(
                                    node,
                                    event,
                                    OpenEventArm::ScheduleRequest,
                                ));
                            },
                        },
                        None => {
                            assert(crate::rover::spec_empty_heartbeat(
                                call.request,
                            ));
                            assert(open_node_event_arm(
                                node,
                                event,
                                OpenEventArm::EmptyHeartbeatRequest,
                            ));
                        },
                    }
                },
                _ => {
                    assert(crate::rover::spec_node_step(
                        node,
                        at,
                        event,
                    ).len() == 0);
                },
            },
            ProductionPid::Store => match message {
                ProductionMessage::StoreRes { op, .. } => {
                    if node.core.ops.contains_key(op) {
                        match node.core.ops[op] {
                            crate::state::Owner::Flight(fid) => {
                                assert(node.core.flights.inflight
                                    .contains_key(fid));
                                match node.core.flights.inflight[fid].work {
                                    crate::handler_docs::WorkSpec::Request {
                                        ..
                                    } => assert(open_node_event_arm(
                                        node,
                                        event,
                                        OpenEventArm::RequestFlightStore,
                                    )),
                                    crate::handler_docs::WorkSpec::Sweep {
                                        ..
                                    } => assert(open_node_event_arm(
                                        node,
                                        event,
                                        OpenEventArm::SweepFlightStore,
                                    )),
                                    crate::handler_docs::WorkSpec::Fire {
                                        ..
                                    } => assert(open_node_event_arm(
                                        node,
                                        event,
                                        OpenEventArm::ScheduleFireStore,
                                    )),
                                }
                            },
                            crate::state::Owner::Members =>
                                assert(open_node_event_arm(
                                    node,
                                    event,
                                    OpenEventArm::MembershipStore,
                                )),
                            crate::state::Owner::Timers =>
                                assert(open_node_event_arm(
                                    node,
                                    event,
                                    OpenEventArm::TimerStore,
                                )),
                            crate::state::Owner::Debug =>
                                assert(open_node_event_arm(
                                    node,
                                    event,
                                    OpenEventArm::DebugStore,
                                )),
                            crate::state::Owner::Ignored =>
                                assert(open_node_event_arm(
                                    node,
                                    event,
                                    OpenEventArm::IgnoredStore,
                                )),
                        }
                    } else {
                        assert(open_node_event_arm(
                            node,
                            event,
                            OpenEventArm::UnownedStore,
                        ));
                    }
                },
                _ => {
                    assert(crate::rover::spec_node_step(
                        node,
                        at,
                        event,
                    ).len() == 0);
                },
            },
            ProductionPid::Node(_) => {
                assert(crate::rover::spec_node_step(
                    node,
                    at,
                    event,
                ).len() == 0);
            },
        },
        ProcessEvent::Timeout => match node.wake {
            Some((wake_at, armed)) => {
                assert(wake_at <= at);
                match armed {
                    crate::types::Armed::Heartbeat =>
                        assert(open_node_event_arm(
                            node,
                            event,
                            OpenEventArm::HeartbeatTimeout,
                        )),
                    crate::types::Armed::Wheel =>
                        assert(open_node_event_arm(
                            node,
                            event,
                            OpenEventArm::WheelTimeout,
                        )),
                }
            },
            None => {
                assert(crate::rover::spec_node_step(
                    node,
                    at,
                    event,
                ).len() == 0);
            },
        },
    }
}

/// Actual one-step simulation for every completed slice of the production
/// adapter. This is the restricted counterpart of Rover's `simulation`
/// obligation: it quantifies over real `step` transitions and returns a
/// matching finite abstract execution, but makes the unproved Node arm
/// explicit in `completed_slice`.
pub proof fn lemma_completed_slice_step(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    label: Label<ProductionPid, ProductionMessage>,
    concrete_after: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
) -> (abstract_after: World<AbstractModel>)
    requires
        world_related(concrete_before, abstract_before),
        completed_transition(concrete_before, label),
        step(
            ProductionModel,
            config,
            concrete_before,
            label,
            concrete_after,
        ),
    ensures
        matches(
            AbstractModel,
            abstract_config(config),
            abstract_before,
            ProductionModel.spec_observe(label),
            abstract_after,
        ),
        world_related(concrete_after, abstract_after),
{
    match label {
        Label::Input { recipient, at, message } =>
            lemma_input_slice(
                config,
                concrete_before,
                abstract_before,
                recipient,
                at,
                message,
                concrete_after,
            ),
        Label::Outside { sender, at, message } =>
            lemma_outside_slice(
                config,
                concrete_before,
                abstract_before,
                sender,
                at,
                message,
                concrete_after,
            ),
        Label::Process { process, at, event, send } => {
            if process == ProductionPid::Store {
                lemma_store_process_slice(
                    config,
                    concrete_before,
                    abstract_before,
                    at,
                    event,
                    send,
                    concrete_after,
                );
            } else {
                match event {
                    ProcessEvent::Receive {
                        sender: ProductionPid::Store,
                        message: ProductionMessage::StoreRes {
                            op,
                            response,
                        },
                    } => {
                        assert(process == ProductionPid::Node(0));
                        lemma_unknown_store_response_slice(
                            config,
                            concrete_before,
                            abstract_before,
                            at,
                            op,
                            response,
                            send,
                            concrete_after,
                        );
                    },
                    _ => assert(false),
                }
            }
            abstract_before
        },
    }
}

/// A machine-checkable, restricted `simulation` statement for the completed
/// production slices. This predicate is proved below and carries no
/// existential relation premise.
pub open spec fn completed_slice_simulation(
    config: crate::Config,
) -> bool {
    forall|
        concrete_before: World<ProductionModel>,
        label: Label<ProductionPid, ProductionMessage>,
        concrete_after: World<ProductionModel>,
        abstract_before: World<AbstractModel>,
    |
        #![trigger
            world_related(concrete_before, abstract_before),
            step(
                ProductionModel,
                config,
                concrete_before,
                label,
                concrete_after,
            )
        ]
        world_related(concrete_before, abstract_before)
        && completed_transition(concrete_before, label)
        && step(
            ProductionModel,
            config,
            concrete_before,
            label,
            concrete_after,
        )
        ==> exists|abstract_after: World<AbstractModel>|
            #[trigger] matches(
                AbstractModel,
                abstract_config(config),
                abstract_before,
                ProductionModel.spec_observe(label),
                abstract_after,
            )
            && world_related(concrete_after, abstract_after)
}

pub proof fn lemma_completed_slice_simulation(config: crate::Config)
    ensures
        completed_slice_simulation(config),
{
    assert forall|
        concrete_before: World<ProductionModel>,
        label: Label<ProductionPid, ProductionMessage>,
        concrete_after: World<ProductionModel>,
        abstract_before: World<AbstractModel>,
    |
        #![trigger
            world_related(concrete_before, abstract_before),
            step(
                ProductionModel,
                config,
                concrete_before,
                label,
                concrete_after,
            )
        ]
        world_related(concrete_before, abstract_before)
        && completed_transition(concrete_before, label)
        && step(
            ProductionModel,
            config,
            concrete_before,
            label,
            concrete_after,
        )
        implies exists|abstract_after: World<AbstractModel>|
            #[trigger] matches(
                AbstractModel,
                abstract_config(config),
                abstract_before,
                ProductionModel.spec_observe(label),
                abstract_after,
            )
            && world_related(concrete_after, abstract_after) by {
        let abstract_after = lemma_completed_slice_step(
            config,
            concrete_before,
            label,
            concrete_after,
            abstract_before,
        );
    };
}

/// Every real production world step is either in the proved generic slice or
/// in exactly the finite Node frontier represented by `OpenEventArm`.
pub proof fn lemma_world_step_is_completed_or_open(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    label: Label<ProductionPid, ProductionMessage>,
    concrete_after: World<ProductionModel>,
    abstract_before: World<AbstractModel>,
)
    requires
        world_related(concrete_before, abstract_before),
        step(
            ProductionModel,
            config,
            concrete_before,
            label,
            concrete_after,
        ),
    ensures
        completed_transition(concrete_before, label)
            || open_transition(concrete_before, label),
        match label {
            Label::Process {
                process: ProductionPid::Node(0),
                ..
            } => open_transition(concrete_before, label),
            _ => true,
        },
{
    match label {
        Label::Input { .. } | Label::Outside { .. } => {
            assert(completed_slice(label));
        },
        Label::Process { process, at, event, send } => {
            if process == ProductionPid::Store {
                assert(completed_slice(label));
            } else {
                reveal(step);
                assert(production_shaped(concrete_before));
                assert(is_process(
                    ProductionModel,
                    concrete_before,
                    process,
                ));
                assert(process == ProductionPid::Node(0)) by {
                    let slot = choose|slot: int|
                        0 <= slot < concrete_before.process.len()
                            && concrete_before.process[slot].0 == process;
                    assert(slot == 0 || slot == 1);
                    if slot == 1 {
                        assert(process == ProductionPid::Store);
                    }
                };
                let i = choose|i: int|
                    #![trigger concrete_before.process[i]]
                    exists|j: int|
                    #![trigger ProductionModel.spec_on_event(
                        config,
                        process,
                        concrete_before.process[i].1,
                        at,
                        event,
                    )[j]]
                    {
                        &&& 0 <= i < concrete_before.process.len()
                        &&& concrete_before.process[i].0 == process
                        &&& {
                            let outcomes =
                                ProductionModel.spec_on_event(
                                    config,
                                    process,
                                    concrete_before.process[i].1,
                                    at,
                                    event,
                                );
                            &&& 0 <= j < outcomes.len()
                            &&& outcomes[j].send == send
                            &&& concrete_after == land(
                                concrete_before,
                                i,
                                process,
                                at,
                                outcomes[j],
                            )
                        }
                    };
                let j = choose|j: int|
                    #![trigger ProductionModel.spec_on_event(
                        config,
                        process,
                        concrete_before.process[i].1,
                        at,
                        event,
                    )[j]]
                    {
                        let outcomes = ProductionModel.spec_on_event(
                            config,
                            process,
                            concrete_before.process[i].1,
                            at,
                            event,
                        );
                        &&& 0 <= j < outcomes.len()
                        &&& outcomes[j].send == send
                        &&& concrete_after == land(
                            concrete_before,
                            i,
                            process,
                            at,
                            outcomes[j],
                        )
                    };
                assert(i == 0);
                assert(concrete_before.process[0].1
                    == ProductionLocalV::Node(
                        production_node(concrete_before),
                    ));
                let outcomes = ProductionModel.spec_on_event(
                    config,
                    process,
                    concrete_before.process[0].1,
                    at,
                    event,
                );
                assert(outcomes == crate::rover::spec_node_step(
                    production_node(concrete_before),
                    at,
                    event,
                ));
                assert(0 <= j < outcomes.len());
                lemma_node_event_arm_is_exhaustive(
                    production_node(concrete_before),
                    abstract_state(abstract_before),
                    at,
                    event,
                );
                assert(open_transition(concrete_before, label));
            }
        },
    }
}

proof fn lemma_non_node_world_step_frames_node(
    config: crate::Config,
    concrete_before: World<ProductionModel>,
    label: Label<ProductionPid, ProductionMessage>,
    concrete_after: World<ProductionModel>,
)
    requires
        production_shaped(concrete_before),
        step(
            ProductionModel,
            config,
            concrete_before,
            label,
            concrete_after,
        ),
        match label {
            Label::Process { process, .. } =>
                process != ProductionPid::Node(0),
            _ => true,
        },
    ensures
        production_node(concrete_after)
            == production_node(concrete_before),
{
    reveal(step);
    match label {
        Label::Input { .. } | Label::Outside { .. } => {},
        Label::Process { process, at, event, send } => {
            assert(process == ProductionPid::Store) by {
                assert(is_process(
                    ProductionModel,
                    concrete_before,
                    process,
                ));
                let slot = choose|slot: int|
                    0 <= slot < concrete_before.process.len()
                        && concrete_before.process[slot].0 == process;
                assert(slot == 0 || slot == 1);
            };
            let i = choose|i: int|
                #![trigger concrete_before.process[i]]
                exists|j: int|
                #![trigger ProductionModel.spec_on_event(
                    config,
                    process,
                    concrete_before.process[i].1,
                    at,
                    event,
                )[j]]
                {
                    &&& 0 <= i < concrete_before.process.len()
                    &&& concrete_before.process[i].0 == process
                    &&& {
                        let outcomes = ProductionModel.spec_on_event(
                            config,
                            process,
                            concrete_before.process[i].1,
                            at,
                            event,
                        );
                        &&& 0 <= j < outcomes.len()
                        &&& outcomes[j].send == send
                        &&& concrete_after == land(
                            concrete_before,
                            i,
                            process,
                            at,
                            outcomes[j],
                        )
                    }
                };
            assert(i == 1);
            assert(concrete_after.process[0]
                == concrete_before.process[0]);
        },
    }
}

/// The exact restricted simulation theorem available without premises about
/// unproved Node arms. It quantifies over all worlds and all interleavings;
/// excluding an open arm is enough to obtain the matching abstract execution.
pub open spec fn restricted_world_simulation(
    config: crate::Config,
) -> bool {
    forall|
        concrete_before: World<ProductionModel>,
        label: Label<ProductionPid, ProductionMessage>,
        concrete_after: World<ProductionModel>,
        abstract_before: World<AbstractModel>,
    |
        #![trigger
            atomic_world_related(concrete_before, abstract_before),
            step(
                ProductionModel,
                config,
                concrete_before,
                label,
                concrete_after,
            )
        ]
        atomic_world_related(concrete_before, abstract_before)
        && !open_transition(concrete_before, label)
        && step(
            ProductionModel,
            config,
            concrete_before,
            label,
            concrete_after,
        )
        ==> exists|abstract_after: World<AbstractModel>|
            #[trigger] matches(
                AbstractModel,
                abstract_config(config),
                abstract_before,
                ProductionModel.spec_observe(label),
                abstract_after,
            )
            && atomic_world_related(concrete_after, abstract_after)
}

pub proof fn lemma_restricted_world_simulation(config: crate::Config)
    ensures
        restricted_world_simulation(config),
{
    assert forall|
        concrete_before: World<ProductionModel>,
        label: Label<ProductionPid, ProductionMessage>,
        concrete_after: World<ProductionModel>,
        abstract_before: World<AbstractModel>,
    |
        #![trigger
            atomic_world_related(concrete_before, abstract_before),
            step(
                ProductionModel,
                config,
                concrete_before,
                label,
                concrete_after,
            )
        ]
        atomic_world_related(concrete_before, abstract_before)
        && !open_transition(concrete_before, label)
        && step(
            ProductionModel,
            config,
            concrete_before,
            label,
            concrete_after,
        )
        implies exists|abstract_after: World<AbstractModel>|
            #[trigger] matches(
                AbstractModel,
                abstract_config(config),
                abstract_before,
                ProductionModel.spec_observe(label),
                abstract_after,
            )
            && atomic_world_related(concrete_after, abstract_after) by {
        lemma_world_step_is_completed_or_open(
            config,
            concrete_before,
            label,
            concrete_after,
            abstract_before,
        );
        assert(match label {
            Label::Process { process, .. } =>
                process != ProductionPid::Node(0),
            _ => true,
        }) by {
            match label {
                Label::Process {
                    process: ProductionPid::Node(0),
                    ..
                } => assert(open_transition(
                    concrete_before,
                    label,
                )),
                _ => {},
            }
        };
        let abstract_after = lemma_completed_slice_step(
            config,
            concrete_before,
            label,
            concrete_after,
            abstract_before,
        );
        lemma_non_node_world_step_frames_node(
            config,
            concrete_before,
            label,
            concrete_after,
        );
    };
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

} // verus!
