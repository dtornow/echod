//! The complete Echod concrete-to-abstract trace-refinement claim.

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]
#![allow(non_shorthand_field_patterns)]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_abstract_spec::{ServerConfig, Spec as AbstractSpec};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::model::{Fleet, Spec as ConcreteSpec};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::RoverSpec::refinement::refines;

verus! {

/// Every concrete boundary trace is an abstract boundary trace, with the
/// fleet retry timeout mapped directly into the abstract server configuration.
pub open spec fn refinement_claim(concrete_config: Fleet) -> bool {
    refines(
        ConcreteSpec,
        concrete_config,
        AbstractSpec,
        ServerConfig {
            retry_timeout: concrete_config.retry_timeout,
        },
    )
}

} // verus!

mod refinement_proof;

#[cfg(verus_keep_ghost)]
pub use refinement_proof::refinement_proof;
