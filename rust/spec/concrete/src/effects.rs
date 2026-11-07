//! Local correspondence between imperative notifications and document effects.

use vstd::prelude::*;

use echod_types::PromiseRecord;

#[cfg(verus_keep_ghost)]
use crate::document::{
    document_effects, PromiseEffectV, ProtocolEffectKeyV, ProtocolEffectV,
};
#[cfg(verus_keep_ghost)]
use crate::node::{DocumentBodyV, NoteV};

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

/// The assertion attached to every complete request transition.
pub open spec fn effects_match(
    before: DocumentBodyV,
    after: DocumentBodyV,
    notes: Seq<NoteV>,
    now: u64,
    retry_timeout: u64,
) -> bool {
    &&& note_effects(notes) == document_effects(before, after, now, retry_timeout)
    &&& note_effect_keys(notes).no_duplicates()
}

pub proof fn lemma_same_document_has_no_effects(
    document: DocumentBodyV,
    now: u64,
    retry_timeout: u64,
)
    ensures
        effects_match(
            document,
            document,
            Seq::<NoteV>::empty(),
            now,
            retry_timeout,
        ),
{
    match document {
        DocumentBodyV::Workflow(objects) => {
            assert forall|effect: ProtocolEffectV|
                !document_effects(
                    document,
                    document,
                    now,
                    retry_timeout,
                ).contains(effect) by {
                match effect {
                    ProtocolEffectV::Execute { id, .. } => {
                        if objects.contains_key(id) {
                            assert(objects[id] == objects[id]);
                        }
                    },
                    ProtocolEffectV::Unblock { promise, address, .. } => {
                        if objects.contains_key(promise) {
                            assert(
                                objects[promise].promise.listeners.contains(address)
                                    == objects[promise].promise.listeners.contains(address)
                            );
                        }
                    },
                }
            };
            assert(document_effects(document, document, now, retry_timeout)
                =~= ISet::<ProtocolEffectV>::empty());
        },
        DocumentBodyV::Schedule(_) => {},
    }
    assert(Seq::<NoteV>::empty()
        .map_values(|note: NoteV| note_effect(note))
        =~= Seq::<ProtocolEffectV>::empty());
    assert(note_effects(Seq::<NoteV>::empty()) =~= ISet::<ProtocolEffectV>::empty());
    assert(note_effect_keys(Seq::<NoteV>::empty()) =~= Seq::<ProtocolEffectKeyV>::empty());
}

pub proof fn lemma_schedule_has_no_effects(
    before: DocumentBodyV,
    after: DocumentBodyV,
    now: u64,
    retry_timeout: u64,
)
    requires
        before is Schedule,
    ensures
        effects_match(
            before,
            after,
            Seq::<NoteV>::empty(),
            now,
            retry_timeout,
        ),
{
    assert(document_effects(before, after, now, retry_timeout)
        =~= ISet::<ProtocolEffectV>::empty());
    assert(note_effects(Seq::<NoteV>::empty()) =~= ISet::<ProtocolEffectV>::empty());
    assert(note_effect_keys(Seq::<NoteV>::empty()) =~= Seq::<ProtocolEffectKeyV>::empty());
}

} // verus!
