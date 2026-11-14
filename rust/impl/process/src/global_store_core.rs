//! Focused core-event frame lemmas for invariant 1.
//!
//! These lemmas keep core dispatch separate from document encoding and
//! Rover-world induction.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::global_store_invariants::{
    cache_identity_provenance, production_core_control_invariants,
    retained_commit_provenance, rover_realizable_event,
};
#[cfg(verus_keep_ghost)]
use crate::rover::NodeV;

#[cfg(verus_keep_ghost)]
verus! {

/// Every realizable core event preserves the exact active operation,
/// request, certificate, lane, and allocator relation.
pub proof fn lemma_core_event_preserves_invariant1_control(
    node: NodeV,
    now: u64,
    event: crate::types::EventSpec,
)
    requires
        production_core_control_invariants(node.core),
        retained_commit_provenance(node.core),
        cache_identity_provenance(node.core),
        rover_realizable_event(node, now, event),
    ensures
        production_core_control_invariants(
            crate::handler::spec_on_event(node.core, event).0,
        ),
{
    crate::global_store_invariants::
        lemma_production_on_event_preserves_core_control(
            node,
            now,
            event,
        );
}

} // verus!
