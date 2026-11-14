//! Production-world boundary for invariant 1.
//!
//! The initial-world fact is kept separate from core-event and Store-apply
//! proofs so finite reachability depends only on the one-step world theorem.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::initial;
#[cfg(verus_keep_ghost)]
use crate::global_store_invariants::global_inductive_store_invariants;
#[cfg(verus_keep_ghost)]
use crate::rover::Model as ProductionModel;

#[cfg(verus_keep_ghost)]
verus! {

pub proof fn lemma_initial_world_satisfies_invariant1(
    config: crate::Config,
)
    ensures
        global_inductive_store_invariants(
            initial(ProductionModel, config),
        ),
{
    crate::global_store_invariants::
        lemma_initial_global_inductive_store_invariants(config);
}

} // verus!
