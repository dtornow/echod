//! Integrity claims for the concrete mathematical model.
//!
//! This module deliberately contains no proof bodies.  The corresponding
//! lemmas and aggregate theorem live in `property_proof.rs`.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use rover_spec::rover::comm::{ProcessEvent, Time};
use rover_spec::rover::RoverSpec::{Proc as _, StepResultV};

use crate::model::{Config, Message, Pid, Proc};
#[cfg(verus_keep_ghost)]
use crate::model::spec_world;
use crate::node::{DocV, NodeV};
#[cfg(verus_keep_ghost)]
use crate::node::{spec_owns, spec_sorted_present};
use crate::store::StoreV;
#[cfg(verus_keep_ghost)]
use crate::store::{spec_before, spec_find};

verus! {

/// A sequence of keys is in strict lexicographic order.
pub open spec fn keys_strictly_sorted(keys: Seq<Seq<char>>) -> bool {
    forall|i: int, j: int| 0 <= i < j < keys.len()
        ==> spec_before(#[trigger] keys[i], #[trigger] keys[j])
}

/// The canonical object traversal contains every map key exactly once and in
/// strict key order.  Schedule documents contain no object-key traversal.
pub open spec fn document_object_order(doc: DocV) -> bool {
    match doc {
        DocV::Origin(map) => {
            let keys = spec_sorted_present(map);
            &&& keys_strictly_sorted(keys)
            &&& keys.no_duplicates()
            &&& forall|key: Seq<char>| #[trigger] keys.contains(key)
                <==> map.contains_key(key)
        },
        DocV::Schedule(_) => true,
    }
}

/// Cached document keys occur at most once.
pub open spec fn document_keys_unique(node: NodeV) -> bool {
    forall|i: int, j: int| 0 <= i < j < node.documents.len()
        ==> #[trigger] node.documents[i].key != #[trigger] node.documents[j].key
}

/// A node caches only document keys assigned to it.
pub open spec fn document_key_ownership(node: NodeV) -> bool {
    forall|i: int| 0 <= i < node.documents.len()
        ==> spec_owns(node, #[trigger] node.documents[i].key)
}

/// Any in-flight document is assigned to the node carrying the flight.
pub open spec fn flight_key_ownership(node: NodeV) -> bool {
    match node.flight {
        Some(flight) => spec_owns(node, flight.key),
        None => true,
    }
}

/// Operation identifiers start at one and an active operation precedes the
/// next identifier that the node will allocate.
pub open spec fn node_operation_order(node: NodeV) -> bool {
    &&& node.next_op > 0
    &&& match node.flight {
        Some(flight) => flight.op < node.next_op,
        None => true,
    }
}

/// Store entries are in strict key order.
pub open spec fn store_entries_ordered(store: StoreV) -> bool {
    forall|i: int, j: int| 0 <= i < j < store.entries.len()
        ==> spec_before(
            #[trigger] store.entries[i].key,
            #[trigger] store.entries[j].key,
        )
}

/// Store keys occur at most once.
pub open spec fn store_entries_unique(store: StoreV) -> bool {
    forall|i: int, j: int| 0 <= i < j < store.entries.len()
        ==> #[trigger] store.entries[i].key != #[trigger] store.entries[j].key
}

/// Every extant store entry has a positive version.
pub open spec fn store_versions_positive(store: StoreV) -> bool {
    forall|i: int| 0 <= i < store.entries.len()
        ==> #[trigger] store.entries[i].version > 0
}

/// The store answers each `(pid, op)` at most once.
pub open spec fn store_seen_unique(store: StoreV) -> bool {
    store.seen.no_duplicates()
}

/// Each configured node PID occurs once, followed by the unique store PID.
pub open spec fn process_layout(config: Config) -> bool {
    let world = spec_world(config);
    &&& world.len() == config.nodes as nat + 1
    &&& forall|i: int| 0 <= i < config.nodes as int
        ==> #[trigger] world[i].0 == Pid::Node(i as u64)
    &&& world[config.nodes as int].0 == Pid::Store
    &&& forall|i: int, j: int| 0 <= i < j < world.len()
        ==> #[trigger] world[i].0 != #[trigger] world[j].0
}

/// All integrity properties that apply to one concrete process.
pub open spec fn state_properties(state: Proc) -> bool {
    match state {
        Proc::Node(node) => {
            &&& document_keys_unique(node)
            &&& document_key_ownership(node)
            &&& flight_key_ownership(node)
            &&& node_operation_order(node)
        },
        Proc::Store(store) => {
            &&& store_entries_ordered(store)
            &&& store_entries_unique(store)
            &&& store_versions_positive(store)
            &&& store_seen_unique(store)
        },
    }
}

/// The per-step monotonic constraints.
pub open spec fn transition_properties(before: Proc, after: Proc) -> bool {
    match (before, after) {
        (Proc::Node(old), Proc::Node(new)) => old.next_op <= new.next_op,
        (Proc::Store(old), Proc::Store(new)) => {
            &&& forall|i: int| 0 <= i < old.entries.len() ==> {
                let old_entry = #[trigger] old.entries[i];
                let key = old_entry.key;
                match spec_find(new.entries, key, 0) {
                    Some(j) => old_entry.version <= new.entries[j].version,
                    None => true,
                }
            }
            &&& forall|seen: (Pid, u64)| old.seen.contains(seen)
                ==> new.seen.contains(seen)
        },
        _ => false,
    }
}

/// State and transition integrity for one selected local outcome.
pub open spec fn step_properties(
    before: Proc,
    outcome: StepResultV<Proc, Pid, Message>,
) -> bool {
    &&& state_properties(outcome.state)
    &&& transition_properties(before, outcome.state)
}

/// The concrete fleet starts well formed and every legal local process
/// outcome preserves the model's integrity properties.
pub open spec fn property_claim(config: Config) -> bool {
    &&& process_layout(config)
    &&& forall|doc: DocV| document_object_order(doc)
    &&& forall|i: int| 0 <= i < spec_world(config).len()
        ==> state_properties(#[trigger] spec_world(config)[i].1)
    &&& forall|before: Proc, now: Time, event: ProcessEvent<Pid, Message>, i: int|
            #![trigger before.on_event(config, now, event)[i]]
            state_properties(before)
            && 0 <= i
            && i < before.on_event(config, now, event).len()
            ==> step_properties(
                before,
                before.on_event(config, now, event)[i],
            )
}

} // verus!
