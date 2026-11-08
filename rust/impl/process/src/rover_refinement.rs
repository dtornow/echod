//! Refinement target for the production-backed Rover model.
//!
//! The existing concrete-to-abstract proof cannot simply be renamed: its
//! relation is over `echod_concrete::model::NodeV`, while the production model
//! now steps [`crate::state::StateSpec`] with caches, concurrent flights,
//! membership refresh, wake replacement, and the full store-call sequence.
//! This module records the exact theorem target and reuses the already-proved
//! handler/effect agreement without claiming the missing world invariant. It
//! also proves the deterministic startup Wake/membership/timer-check slice as
//! a real Rover process step matched by an empty abstract execution.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::rover::Model as ProductionModel;
#[cfg(verus_keep_ghost)]
use crate::rover::{
    spec_initial_node, spec_node_step, LocalV as ProductionLocalV, Message as ProductionMessage,
    NodeV as ProductionNodeV,
};
#[cfg(verus_keep_ghost)]
use crate::state::Owner;
#[cfg(verus_keep_ghost)]
use crate::types::{Armed, EffectSpec, EventSpec};
#[cfg(verus_keep_ghost)]
use echod_abstract::{Model as AbstractModel, ServerConfig};
#[cfg(verus_keep_ghost)]
use echod_concrete::model::Pid;
#[cfg(verus_keep_ghost)]
use echod_concrete::relation::agreement;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::refinement::{
    concrete_refines_abstract, end, matches, project, refines, simulation,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{
    initial, land, legal, step, Execution, Label, StepResultV, World,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::{ProcessEvent, RoverModel};

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
            &&& node.core.ops.contains_key(1)
            &&& node.core.ops[1] == Owner::Members
            &&& node.core.node.members.refresh is Some
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
            &&& next.core.ops.contains_key(1)
            &&& next.core.ops[1] == Owner::Members
            &&& next.core.node.members.refresh is Some
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
