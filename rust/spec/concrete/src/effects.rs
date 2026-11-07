//! Local correspondence between imperative notifications and document effects.

use vstd::prelude::*;

use echod_types::PromiseRecord;

#[cfg(verus_keep_ghost)]
use crate::document::{
    document_effects, PromiseEffectV, ProtocolEffectKeyV, ProtocolEffectV, StoredDocumentV,
};
#[cfg(verus_keep_ghost)]
use crate::node::NoteV;

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
    notes.map_values(|note: NoteV| note_effect(note)).to_set().to_iset()
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

} // verus!
