//! Local correspondence between imperative notifications and document effects.

use vstd::prelude::*;

use echod_types::{PromiseRecord, Request};

#[cfg(verus_keep_ghost)]
use crate::document::{
    document_effects, well_formed, workflow_effects, ObjV, PromiseEffectV, ProtocolEffectKeyV,
    ProtocolEffectV, StoredDocumentV,
};
#[cfg(verus_keep_ghost)]
use crate::state::{
    spec_committed_notes, spec_execute_notes, spec_keyed_notes, spec_note_key,
    spec_request_commits, spec_request_transition, spec_sorted_present, spec_stored_body,
    spec_stored_committed_at, spec_unavailable, spec_unblock_notes, spec_unblock_notes_for,
    DocumentBodyV, NoteV,
};
#[cfg(verus_keep_ghost)]
use crate::request_claim::{on_request, routed};

verus! {


pub open spec fn record_effect(record: PromiseRecord) -> PromiseEffectV {
    PromiseEffectV {
        id: record.id@,
        state: record.state,
        param: record.param,
        value: record.value,
        tags: record.tags,
        timeout_at: record.timeout_at,
        created_at: record.created_at,
        settled_at: record.settled_at,
    }
}


pub open spec fn note_effect(note: NoteV) -> ProtocolEffectV {
    match note {
        NoteV::Execute { id, version } => ProtocolEffectV::Execute { id, version },
        NoteV::Unblock { address, promise } => ProtocolEffectV::Unblock {
            promise: promise.id@,
            address,
            record: record_effect(promise),
        },
    }
}


pub open spec fn note_effects(notes: Seq<NoteV>) -> ISet<ProtocolEffectV> {
    ISet::new(|effect: ProtocolEffectV|
        exists|i: int| 0 <= i < notes.len() && note_effect(notes[i]) == effect)
}


pub open spec fn note_effect_keys(notes: Seq<NoteV>) -> Seq<ProtocolEffectKeyV> {
    notes.map_values(
        |note: NoteV| crate::document::protocol_effect_key(note_effect(note)),
    )
}


/// The assertion used by the complete request-effect theorem.
pub open spec fn effects_match(
    before: StoredDocumentV,
    after: StoredDocumentV,
    notes: Seq<NoteV>,
) -> bool {
    &&& note_effects(notes) == document_effects(before, after)
    &&& note_effect_keys(notes).no_duplicates()
}


/// Configuration condition needed to ensure that a retry rearm is strictly
/// later than the commit whose effects are being derived.
pub open spec fn safe_effect_config(now: u64, retry_timeout: u64) -> bool {
    retry_timeout > 0
        && (now as nat) + (retry_timeout as nat) <= u64::MAX as nat
}

} // verus!
