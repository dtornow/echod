//! Refinement target for the production-backed Rover model.
//!
//! The existing concrete-to-abstract proof cannot simply be renamed: its
//! relation is over `echod_concrete::model::NodeV`, while the production model
//! now steps [`crate::state::StateSpec`] with caches, concurrent flights,
//! membership refresh, wake replacement, and the full store-call sequence.
//! This module records the exact theorem target and reuses the already-proved
//! handler/effect agreement without claiming the missing world invariant.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::rover::Model as ProductionModel;
#[cfg(verus_keep_ghost)]
use echod_abstract::{Model as AbstractModel, ServerConfig};
#[cfg(verus_keep_ghost)]
use echod_concrete::relation::agreement;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::refinement::{concrete_refines_abstract, refines, simulation};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{initial, World};

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
