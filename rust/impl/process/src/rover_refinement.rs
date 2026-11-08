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
use crate::state_node::RefreshSpec;
#[cfg(verus_keep_ghost)]
use crate::state_timers::ListingSpec;
#[cfg(verus_keep_ghost)]
use crate::types::{Armed, EffectSpec, EventSpec};
#[cfg(verus_keep_ghost)]
use echod_abstract::{Model as AbstractModel, ServerConfig};
#[cfg(verus_keep_ghost)]
use echod_concrete::model::Pid;
#[cfg(verus_keep_ghost)]
use echod_concrete::relation::agreement;
#[cfg(verus_keep_ghost)]
use echod_concrete::store::StoreRes;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::refinement::{
    concrete_refines_abstract, end, matches, project, refines, simulation,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{
    event_valid, initial, land, legal, step, Execution, Label, StepResultV, World,
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
