//! Local correspondence between imperative notifications and document effects.

use vstd::prelude::*;

use echod_types::{PromiseRecord, Request};

#[cfg(verus_keep_ghost)]
use crate::document::{
    document_effects, well_formed, workflow_effects, ObjV, PromiseEffectV, ProtocolEffectKeyV,
    ProtocolEffectV, StoredDocumentV,
};
#[cfg(verus_keep_ghost)]
use crate::node::{
    spec_committed_notes, spec_execute_notes, spec_keyed_notes, spec_note_key,
    spec_request_commits, spec_request_transition, spec_sorted_present, spec_stored_body,
    spec_stored_committed_at, spec_unblock_notes, spec_unblock_notes_for, DocumentBodyV, NoteV,
};
#[cfg(verus_keep_ghost)]
use crate::quick_n_dirty::{on_request, routed};

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

proof fn lemma_note_keys_agree(left: NoteV, right: NoteV)
    ensures
        spec_note_key(left) == spec_note_key(right)
            <==> crate::document::protocol_effect_key(note_effect(left))
                == crate::document::protocol_effect_key(note_effect(right)),
{
}

/// Keyed-note filtering both removes duplicates and preserves that property
/// while discarding Executes consumed by the same atomic request.
pub proof fn lemma_keyed_notes_no_duplicate_effect_keys(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    count: nat,
)
    requires
        count <= notes.len(),
    ensures
        note_effect_keys(spec_keyed_notes(doc, notes, count)).no_duplicates(),
    decreases count,
{
    if count > 0 {
        let prior = spec_keyed_notes(doc, notes, (count - 1) as nat);
        let note = notes[count as int - 1];
        lemma_keyed_notes_no_duplicate_effect_keys(
            doc,
            notes,
            (count - 1) as nat,
        );
        if crate::node::spec_note_relevant(doc, note)
            && !(exists|i: int| 0 <= i < prior.len()
                && spec_note_key(prior[i]) == spec_note_key(note))
        {
            assert forall|i: int| 0 <= i < prior.len() implies
                crate::document::protocol_effect_key(note_effect(prior[i]))
                    != crate::document::protocol_effect_key(note_effect(note)) by {
                lemma_note_keys_agree(prior[i], note);
            }
            assert(note_effect_keys(prior.push(note))
                == note_effect_keys(prior).push(
                    crate::document::protocol_effect_key(note_effect(note)),
                ));
        }
    }
}

proof fn lemma_note_effects_add(first: Seq<NoteV>, second: Seq<NoteV>)
    ensures
        forall|effect: ProtocolEffectV|
            note_effects(first + second).contains(effect)
                <==> note_effects(first).contains(effect)
                    || note_effects(second).contains(effect),
{
    assert forall|effect: ProtocolEffectV|
        note_effects(first + second).contains(effect)
            <==> note_effects(first).contains(effect)
                || note_effects(second).contains(effect) by {
        if note_effects(first + second).contains(effect) {
            let i = choose|i: int| 0 <= i < (first + second).len()
                && note_effect((first + second)[i]) == effect;
            if i < first.len() {
                assert((first + second)[i] == first[i]);
                assert(note_effects(first).contains(effect));
            } else {
                assert((first + second)[i] == second[i - first.len()]);
                assert(note_effects(second).contains(effect));
            }
        }
        if note_effects(first).contains(effect) {
            let i = choose|i: int| 0 <= i < first.len()
                && note_effect(first[i]) == effect;
            assert((first + second)[i] == first[i]);
            assert(note_effects(first + second).contains(effect));
        }
        if note_effects(second).contains(effect) {
            let i = choose|i: int| 0 <= i < second.len()
                && note_effect(second[i]) == effect;
            assert((first + second)[first.len() + i] == second[i]);
            assert(note_effects(first + second).contains(effect));
        }
    };
}

proof fn lemma_note_effects_push(notes: Seq<NoteV>, note: NoteV)
    ensures
        forall|effect: ProtocolEffectV|
            note_effects(notes.push(note)).contains(effect)
                <==> note_effects(notes).contains(effect)
                    || effect == note_effect(note),
{
    lemma_note_effects_add(notes, seq![note]);
    assert(notes.push(note) =~= notes + seq![note]);
    assert forall|effect: ProtocolEffectV|
        note_effects(seq![note]).contains(effect)
            <==> effect == note_effect(note) by {
        if note_effects(seq![note]).contains(effect) {
            let i = choose|i: int| 0 <= i < 1
                && note_effect(seq![note][i]) == effect;
            assert(i == 0);
        }
        if effect == note_effect(note) {
            assert(seq![note][0] == note);
            assert(0 <= 0 < seq![note].len());
            assert(note_effects(seq![note]).contains(effect));
        }
    };
}

proof fn lemma_nodup_last_not_in_prefix<A>(values: Seq<A>, count: nat)
    requires
        0 < count <= values.len(),
        values.take(count as int).no_duplicates(),
    ensures
        !values.take(count as int - 1).contains(values[count as int - 1]),
{
    if values.take(count as int - 1).contains(values[count as int - 1]) {
        let i = choose|i: int| 0 <= i < values.take(count as int - 1).len()
            && #[trigger] values.take(count as int - 1)[i]
                == values[count as int - 1];
        assert(values.take(count as int)[i]
            == values.take(count as int)[count as int - 1]);
        assert(i != count as int - 1);
    }
}

proof fn lemma_execute_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    committed_at: u64,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= keys.len(),
        keys.take(count as int).no_duplicates(),
        forall|i: int| 0 <= i < count ==> after.contains_key(#[trigger] keys[i]),
    ensures
        ({
            let notes = spec_execute_notes(before, after, committed_at, keys, count);
            &&& forall|effect: ProtocolEffectV|
                note_effects(notes).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { id, version } =>
                        keys.take(count as int).contains(id)
                            && crate::document::offer_committed(
                                before,
                                after,
                                id,
                                committed_at,
                            )
                            && after[id].task.unwrap().version == version,
                    ProtocolEffectV::Unblock { .. } => false,
                }
            &&& note_effect_keys(notes).no_duplicates()
        }),
    decreases count,
{
    if count > 0 {
        let prior = spec_execute_notes(
            before,
            after,
            committed_at,
            keys,
            (count - 1) as nat,
        );
        let id = keys[count as int - 1];
        lemma_execute_notes(before, after, committed_at, keys, (count - 1) as nat);
        lemma_nodup_last_not_in_prefix(keys, count);
        assert(keys.take(count as int)
            == keys.take(count as int - 1).push(id));
        if crate::document::offer_committed(before, after, id, committed_at) {
            let note = NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            };
            lemma_note_effects_push(prior, note);
            lemma_note_effects_add(prior, seq![note]);
            assert(prior + seq![note] =~= prior.push(note));
            assert(spec_execute_notes(before, after, committed_at, keys, count)
                == prior.push(note));
            assert(note_effect_keys(prior.push(note))
                == note_effect_keys(prior).push(
                    ProtocolEffectKeyV::Execute { id },
                ));
            assert(!note_effect_keys(prior).contains(
                ProtocolEffectKeyV::Execute { id },
            )) by {
                if note_effect_keys(prior).contains(
                    ProtocolEffectKeyV::Execute { id },
                ) {
                    let i = choose|i: int| 0 <= i < prior.len()
                        && note_effect_keys(prior)[i]
                            == ProtocolEffectKeyV::Execute { id };
                    assert(note_effect_keys(prior)[i]
                        == crate::document::protocol_effect_key(note_effect(prior[i])));
                    assert(note_effects(prior).contains(note_effect(prior[i])));
                    match note_effect(prior[i]) {
                        ProtocolEffectV::Execute { id: prior_id, .. } => {
                            assert(prior_id == id);
                            assert(keys.take(count as int - 1).contains(prior_id));
                        },
                        ProtocolEffectV::Unblock { .. } => {
                            assert(false);
                        },
                    }
                }
            };
        } else {
            assert(spec_execute_notes(before, after, committed_at, keys, count)
                == prior);
        }
        assert forall|candidate: Seq<char>|
            keys.take(count as int).contains(candidate)
                <==> keys.take(count as int - 1).contains(candidate)
                    || candidate == id by {
            crate::simulation::lemma_push_contains(
                keys.take(count as int - 1),
                id,
                candidate,
            );
            if keys.take(count as int).contains(candidate) {
                let i = choose|i: int| 0 <= i < keys.take(count as int).len()
                    && keys.take(count as int)[i] == candidate;
                if i < count as int - 1 {
                    assert(keys.take(count as int - 1)[i] == candidate);
                } else {
                    assert(i == count as int - 1);
                }
            }
            if keys.take(count as int - 1).contains(candidate) {
                let i = choose|i: int| 0 <= i < keys.take(count as int - 1).len()
                    && #[trigger] keys.take(count as int - 1)[i] == candidate;
                assert(keys.take(count as int)[i] == candidate);
            }
        };
        assert forall|effect: ProtocolEffectV|
            note_effects(spec_execute_notes(before, after, committed_at, keys, count))
                .contains(effect) <==> match effect {
                ProtocolEffectV::Execute { id, version } =>
                    keys.take(count as int).contains(id)
                        && crate::document::offer_committed(
                            before,
                            after,
                            id,
                            committed_at,
                        )
                        && after[id].task.unwrap().version == version,
                ProtocolEffectV::Unblock { .. } => false,
            } by {
            assert(note_effects(prior).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { id, version } =>
                    keys.take(count as int - 1).contains(id)
                        && crate::document::offer_committed(
                            before,
                            after,
                            id,
                            committed_at,
                        )
                        && after[id].task.unwrap().version == version,
                ProtocolEffectV::Unblock { .. } => false,
            });
            match effect {
                ProtocolEffectV::Execute { id: effect_id, version } => {
                    if crate::document::offer_committed(
                        before,
                        after,
                        id,
                        committed_at,
                    ) {
                        let note = NoteV::Execute {
                            id,
                            version: after[id].task.unwrap().version,
                        };
                        lemma_note_effects_push(prior, note);
                        assert(spec_execute_notes(
                            before,
                            after,
                            committed_at,
                            keys,
                            count,
                        ) == prior.push(note));
                        assert(note_effects(prior.push(note)).contains(effect)
                            <==> note_effects(prior).contains(effect)
                                || effect == note_effect(note));
                        assert(effect == note_effect(note)
                            <==> effect_id == id
                                && version == after[id].task.unwrap().version);
                    } else {
                        assert(spec_execute_notes(
                            before,
                            after,
                            committed_at,
                            keys,
                            count,
                        ) == prior);
                    }
                    if effect_id == id
                        && crate::document::offer_committed(
                            before,
                            after,
                            id,
                            committed_at,
                        )
                    {
                        assert(!keys.take(count as int - 1).contains(id));
                    }
                },
                ProtocolEffectV::Unblock { .. } => {},
            }
        };
    }
}

proof fn lemma_unblock_notes_for(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    promise: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= listeners.len(),
        listeners.take(count as int).no_duplicates(),
    ensures
        ({
            let notes =
                spec_unblock_notes_for(before, after, promise, listeners, count);
            &&& forall|effect: ProtocolEffectV|
                note_effects(notes).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { .. } => false,
                    ProtocolEffectV::Unblock {
                        promise: effect_promise,
                        address,
                        record,
                    } =>
                        effect_promise == promise
                            && listeners.take(count as int).contains(address)
                            && crate::document::listener_committed(
                                before,
                                after,
                                promise,
                                address,
                            )
                            && record == crate::document::promise_effect(
                                promise,
                                after[promise].promise,
                            ),
                }
            &&& note_effect_keys(notes).no_duplicates()
        }),
    decreases count,
{
    if count > 0 {
        let prior = spec_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            (count - 1) as nat,
        );
        let address = listeners[count as int - 1];
        lemma_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            (count - 1) as nat,
        );
        lemma_nodup_last_not_in_prefix(listeners, count);
        assert(listeners.take(count as int)
            == listeners.take(count as int - 1).push(address));
        if crate::document::listener_committed(
            before,
            after,
            promise,
            address,
        ) {
            crate::interpret::lemma_string_view(promise);
            let note = NoteV::Unblock {
                address,
                promise: crate::node::spec_record(
                    crate::model::spec_string(promise),
                    after[promise].promise,
                ),
            };
            lemma_note_effects_push(prior, note);
            assert(record_effect(crate::node::spec_record(
                crate::model::spec_string(promise),
                after[promise].promise,
            )) == crate::document::promise_effect(
                promise,
                after[promise].promise,
            ));
            lemma_note_effects_add(prior, seq![note]);
            assert(prior + seq![note] =~= prior.push(note));
            assert(spec_unblock_notes_for(
                before,
                after,
                promise,
                listeners,
                count,
            ) == prior.push(note));
            assert(note_effect_keys(prior.push(note))
                == note_effect_keys(prior).push(
                    ProtocolEffectKeyV::Unblock { promise, address },
                ));
            assert(!note_effect_keys(prior).contains(
                ProtocolEffectKeyV::Unblock { promise, address },
            )) by {
                if note_effect_keys(prior).contains(
                    ProtocolEffectKeyV::Unblock { promise, address },
                ) {
                    let i = choose|i: int| 0 <= i < prior.len()
                        && note_effect_keys(prior)[i]
                            == ProtocolEffectKeyV::Unblock { promise, address };
                    assert(note_effect_keys(prior)[i]
                        == crate::document::protocol_effect_key(note_effect(prior[i])));
                    assert(note_effects(prior).contains(note_effect(prior[i])));
                    match note_effect(prior[i]) {
                        ProtocolEffectV::Unblock {
                            promise: prior_promise,
                            address: prior_address,
                            ..
                        } => {
                            assert(prior_promise == promise);
                            assert(prior_address == address);
                            assert(listeners.take(count as int - 1)
                                .contains(prior_address));
                        },
                        ProtocolEffectV::Execute { .. } => {
                            assert(false);
                        },
                    }
                }
            };
        } else {
            assert(spec_unblock_notes_for(
                before,
                after,
                promise,
                listeners,
                count,
            ) == prior);
        }
        assert forall|candidate: Seq<char>|
            listeners.take(count as int).contains(candidate)
                <==> listeners.take(count as int - 1).contains(candidate)
                    || candidate == address by {
            crate::simulation::lemma_push_contains(
                listeners.take(count as int - 1),
                address,
                candidate,
            );
            if listeners.take(count as int).contains(candidate) {
                let i = choose|i: int| 0 <= i < listeners.take(count as int).len()
                    && listeners.take(count as int)[i] == candidate;
                if i < count as int - 1 {
                    assert(listeners.take(count as int - 1)[i] == candidate);
                } else {
                    assert(i == count as int - 1);
                }
            }
            if listeners.take(count as int - 1).contains(candidate) {
                let i = choose|i: int|
                    0 <= i < listeners.take(count as int - 1).len()
                        && #[trigger] listeners.take(count as int - 1)[i] == candidate;
                assert(listeners.take(count as int)[i] == candidate);
            }
        };
        assert forall|effect: ProtocolEffectV|
            note_effects(spec_unblock_notes_for(
                before,
                after,
                promise,
                listeners,
                count,
            )).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address: effect_address,
                    record,
                } =>
                    effect_promise == promise
                        && listeners.take(count as int).contains(effect_address)
                        && crate::document::listener_committed(
                            before,
                            after,
                            promise,
                            effect_address,
                        )
                        && record == crate::document::promise_effect(
                            promise,
                            after[promise].promise,
                        ),
            } by {
            assert(note_effects(prior).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address: effect_address,
                    record,
                } =>
                    effect_promise == promise
                        && listeners.take(count as int - 1).contains(effect_address)
                        && crate::document::listener_committed(
                            before,
                            after,
                            promise,
                            effect_address,
                        )
                        && record == crate::document::promise_effect(
                            promise,
                            after[promise].promise,
                        ),
            });
            match effect {
                ProtocolEffectV::Execute { .. } => {},
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address: effect_address,
                    record,
                } => {
                    if crate::document::listener_committed(
                        before,
                        after,
                        promise,
                        address,
                    ) {
                        crate::interpret::lemma_string_view(promise);
                        let note = NoteV::Unblock {
                            address,
                            promise: crate::node::spec_record(
                                crate::model::spec_string(promise),
                                after[promise].promise,
                            ),
                        };
                        lemma_note_effects_push(prior, note);
                        assert(spec_unblock_notes_for(
                            before,
                            after,
                            promise,
                            listeners,
                            count,
                        ) == prior.push(note));
                        assert(note_effects(prior.push(note)).contains(effect)
                            <==> note_effects(prior).contains(effect)
                                || effect == note_effect(note));
                        assert(effect == note_effect(note) <==> {
                            &&& effect_promise == promise
                            &&& effect_address == address
                            &&& record == crate::document::promise_effect(
                                promise,
                                after[promise].promise,
                            )
                        });
                    } else {
                        assert(spec_unblock_notes_for(
                            before,
                            after,
                            promise,
                            listeners,
                            count,
                        ) == prior);
                    }
                },
            }
        }
    }
}

proof fn lemma_add_no_duplicates<A>(first: Seq<A>, second: Seq<A>)
    requires
        first.no_duplicates(),
        second.no_duplicates(),
        forall|i: int, j: int|
            0 <= i < first.len() && 0 <= j < second.len()
                ==> first[i] != second[j],
    ensures
        (first + second).no_duplicates(),
{
    assert forall|i: int, j: int|
        0 <= i < (first + second).len()
            && 0 <= j < (first + second).len()
            && (first + second)[i] == (first + second)[j]
                implies i == j by {
        if i < first.len() && j < first.len() {
            assert((first + second)[i] == first[i]);
            assert((first + second)[j] == first[j]);
        } else if i >= first.len() && j >= first.len() {
            assert((first + second)[i] == second[i - first.len()]);
            assert((first + second)[j] == second[j - first.len()]);
        } else if i < first.len() {
            assert((first + second)[i] == first[i]);
            assert((first + second)[j] == second[j - first.len()]);
        } else {
            assert((first + second)[j] == first[j]);
            assert((first + second)[i] == second[i - first.len()]);
        }
    };
}

proof fn lemma_unblock_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= keys.len(),
        keys.take(count as int).no_duplicates(),
        forall|i: int| 0 <= i < count ==> {
            &&& before.contains_key(#[trigger] keys[i])
            &&& before[keys[i]].promise.listeners.no_duplicates()
        },
    ensures
        ({
            let notes = spec_unblock_notes(before, after, keys, count);
            &&& forall|effect: ProtocolEffectV|
                note_effects(notes).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { .. } => false,
                    ProtocolEffectV::Unblock {
                        promise,
                        address,
                        record,
                    } =>
                        keys.take(count as int).contains(promise)
                            && crate::document::listener_committed(
                                before,
                                after,
                                promise,
                                address,
                            )
                            && record == crate::document::promise_effect(
                                promise,
                                after[promise].promise,
                            ),
                }
            &&& note_effect_keys(notes).no_duplicates()
        }),
    decreases count,
{
    if count > 0 {
        let prior = spec_unblock_notes(before, after, keys, (count - 1) as nat);
        let promise = keys[count as int - 1];
        let listeners = before[promise].promise.listeners;
        let current = spec_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            listeners.len(),
        );
        lemma_unblock_notes(before, after, keys, (count - 1) as nat);
        lemma_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            listeners.len(),
        );
        lemma_nodup_last_not_in_prefix(keys, count);
        assert(keys.take(count as int)
            == keys.take(count as int - 1).push(promise));
        assert(spec_unblock_notes(before, after, keys, count) == prior + current);
        lemma_note_effects_add(prior, current);
        assert(note_effect_keys(prior + current)
            == note_effect_keys(prior) + note_effect_keys(current));
        assert forall|i: int, j: int|
            0 <= i < note_effect_keys(prior).len()
                && 0 <= j < note_effect_keys(current).len()
                implies note_effect_keys(prior)[i] != note_effect_keys(current)[j] by {
            assert(note_effect_keys(prior)[i]
                == crate::document::protocol_effect_key(note_effect(prior[i])));
            assert(note_effect_keys(current)[j]
                == crate::document::protocol_effect_key(note_effect(current[j])));
            assert(note_effects(prior).contains(note_effect(prior[i])));
            assert(note_effects(current).contains(note_effect(current[j])));
            match (note_effect(prior[i]), note_effect(current[j])) {
                (
                    ProtocolEffectV::Unblock { promise: left, .. },
                    ProtocolEffectV::Unblock { promise: right, .. },
                ) => {
                    assert(keys.take(count as int - 1).contains(left));
                    assert(right == promise);
                    assert(left != right);
                },
                _ => {},
            }
        };
        lemma_add_no_duplicates(
            note_effect_keys(prior),
            note_effect_keys(current),
        );
        assert forall|candidate: Seq<char>|
            keys.take(count as int).contains(candidate)
                <==> keys.take(count as int - 1).contains(candidate)
                    || candidate == promise by {
            crate::simulation::lemma_push_contains(
                keys.take(count as int - 1),
                promise,
                candidate,
            );
        };
        assert forall|effect: ProtocolEffectV|
            note_effects(spec_unblock_notes(before, after, keys, count))
                .contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address,
                    record,
                } =>
                    keys.take(count as int).contains(effect_promise)
                        && crate::document::listener_committed(
                            before,
                            after,
                            effect_promise,
                            address,
                        )
                        && record == crate::document::promise_effect(
                            effect_promise,
                            after[effect_promise].promise,
                        ),
            } by {
            assert(note_effects(prior + current).contains(effect)
                <==> note_effects(prior).contains(effect)
                    || note_effects(current).contains(effect));
            lemma_note_effects_add(prior, current);
            assert(note_effects(prior).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise,
                    address,
                    record,
                } =>
                    keys.take(count as int - 1).contains(promise)
                        && crate::document::listener_committed(
                            before,
                            after,
                            promise,
                            address,
                        )
                        && record == crate::document::promise_effect(
                            promise,
                            after[promise].promise,
                        ),
            });
            assert(listeners.take(listeners.len() as int) == listeners);
            assert(note_effects(current).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address,
                    record,
                } =>
                    effect_promise == promise
                        && listeners.contains(address)
                        && crate::document::listener_committed(
                            before,
                            after,
                            promise,
                            address,
                        )
                        && record == crate::document::promise_effect(
                            promise,
                            after[promise].promise,
                        ),
            });
            match effect {
                ProtocolEffectV::Execute { .. } => {},
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address,
                    ..
                } => {
                    if effect_promise == promise
                        && crate::document::listener_committed(
                            before,
                            after,
                            promise,
                            address,
                        )
                    {
                        assert(listeners.contains(address));
                    }
                },
            }
        }
    }
}

proof fn lemma_sorted_no_duplicates(keys: Set<Seq<char>>)
    ensures
        crate::node::spec_sorted(keys).no_duplicates(),
    decreases keys.len(),
{
    if keys.len() > 0 {
        crate::timers::lemma_min_key(keys);
        let first = crate::node::spec_min_key(keys);
        let rest = keys.remove(first);
        lemma_sorted_no_duplicates(rest);
        crate::timers::lemma_sorted(rest);
        assert(!crate::node::spec_sorted(rest).contains(first)) by {
            if crate::node::spec_sorted(rest).contains(first) {
                let i = choose|i: int|
                    0 <= i < crate::node::spec_sorted(rest).len()
                        && #[trigger] crate::node::spec_sorted(rest)[i] == first;
                assert(rest.contains(first));
            }
        };
        assert(crate::node::spec_sorted(keys)
            == seq![first] + crate::node::spec_sorted(rest));
    }
}

proof fn lemma_committed_notes_match(
    before: DocumentBodyV,
    after: DocumentBodyV,
    committed_at: u64,
)
    requires
        match before {
            DocumentBodyV::Workflow(old) =>
                forall|id: Seq<char>| old.contains_key(id) ==>
                    old[id].promise.listeners.no_duplicates(),
            DocumentBodyV::Schedule(_) => true,
        },
    ensures
        ({
            let notes = spec_committed_notes(before, after, committed_at);
            &&& note_effects(notes) == match (before, after) {
                (DocumentBodyV::Workflow(old), DocumentBodyV::Workflow(new)) =>
                    workflow_effects(old, new, committed_at),
                _ => ISet::empty(),
            }
            &&& note_effect_keys(notes).no_duplicates()
        }),
{
    match (before, after) {
        (DocumentBodyV::Workflow(old), DocumentBodyV::Workflow(new)) => {
            let new_keys = spec_sorted_present(new);
            let old_keys = spec_sorted_present(old);
            crate::timers::lemma_sorted(new.dom());
            crate::timers::lemma_sorted(old.dom());
            lemma_sorted_no_duplicates(new.dom());
            lemma_sorted_no_duplicates(old.dom());
            lemma_execute_notes(
                old,
                new,
                committed_at,
                new_keys,
                new_keys.len(),
            );
            lemma_unblock_notes(old, new, old_keys, old_keys.len());
            let executes = spec_execute_notes(
                old,
                new,
                committed_at,
                new_keys,
                new_keys.len(),
            );
            let unblocks =
                spec_unblock_notes(old, new, old_keys, old_keys.len());
            lemma_note_effects_add(executes, unblocks);
            assert(new_keys.take(new_keys.len() as int) == new_keys);
            assert(old_keys.take(old_keys.len() as int) == old_keys);
            assert(note_effect_keys(executes + unblocks)
                == note_effect_keys(executes) + note_effect_keys(unblocks));
            assert forall|i: int, j: int|
                0 <= i < note_effect_keys(executes).len()
                    && 0 <= j < note_effect_keys(unblocks).len()
                    implies note_effect_keys(executes)[i]
                        != note_effect_keys(unblocks)[j] by {
                assert(note_effect_keys(executes)[i]
                    == crate::document::protocol_effect_key(
                        note_effect(executes[i]),
                    ));
                assert(note_effect_keys(unblocks)[j]
                    == crate::document::protocol_effect_key(
                        note_effect(unblocks[j]),
                    ));
                assert(note_effects(executes).contains(note_effect(executes[i])));
                assert(note_effects(unblocks).contains(note_effect(unblocks[j])));
            };
            lemma_add_no_duplicates(
                note_effect_keys(executes),
                note_effect_keys(unblocks),
            );
            assert forall|effect: ProtocolEffectV|
                note_effects(executes + unblocks).contains(effect)
                    <==> workflow_effects(old, new, committed_at).contains(effect) by {
                assert(note_effects(executes + unblocks).contains(effect)
                    <==> note_effects(executes).contains(effect)
                        || note_effects(unblocks).contains(effect));
                assert(note_effects(executes).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { id, version } =>
                        new_keys.contains(id)
                            && crate::document::offer_committed(
                                old,
                                new,
                                id,
                                committed_at,
                            )
                            && new[id].task.unwrap().version == version,
                    ProtocolEffectV::Unblock { .. } => false,
                });
                assert(note_effects(unblocks).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { .. } => false,
                    ProtocolEffectV::Unblock {
                        promise,
                        address,
                        record,
                    } =>
                        old_keys.contains(promise)
                            && crate::document::listener_committed(
                                old,
                                new,
                                promise,
                                address,
                            )
                            && record == crate::document::promise_effect(
                                promise,
                                new[promise].promise,
                            ),
                });
                match effect {
                    ProtocolEffectV::Execute { id, .. } => {
                        if new.contains_key(id) {
                            assert(new_keys.contains(id));
                        }
                        if new_keys.contains(id) {
                            let i = choose|i: int| 0 <= i < new_keys.len()
                                && #[trigger] new_keys[i] == id;
                            assert(new.dom().contains(new_keys[i]));
                            assert(new.contains_key(id));
                        }
                    },
                    ProtocolEffectV::Unblock { promise, .. } => {
                        if old.contains_key(promise) {
                            assert(old_keys.contains(promise));
                        }
                        if old_keys.contains(promise) {
                            let i = choose|i: int| 0 <= i < old_keys.len()
                                && #[trigger] old_keys[i] == promise;
                            assert(old.dom().contains(old_keys[i]));
                            assert(old.contains_key(promise));
                        }
                    },
                }
            };
            assert(note_effects(executes + unblocks)
                =~= workflow_effects(old, new, committed_at));
        },
        _ => {
            assert(spec_committed_notes(before, after, committed_at)
                =~= Seq::<NoteV>::empty());
            assert(note_effects(Seq::<NoteV>::empty())
                =~= ISet::<ProtocolEffectV>::empty());
        },
    }
}

/// Configuration condition needed to ensure that a retry rearm is strictly
/// later than the commit whose effects are being derived.
pub open spec fn safe_effect_config(now: u64, retry_timeout: u64) -> bool {
    retry_timeout > 0
        && (now as nat) + (retry_timeout as nat) <= u64::MAX as nat
}

/// Complete endpoint correspondence for one atomic request transition.
pub proof fn lemma_request_transition_effects(
    document: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
    limit: nat,
)
    requires
        well_formed(document),
        routed(document, request),
        spec_stored_committed_at(document) <= now,
        safe_effect_config(now, retry_timeout),
    ensures
        ({
            let final_document =
                on_request(document, request, now, retry_timeout, limit);
            let (_, _, _, notes) = spec_request_transition(
                spec_stored_body(document),
                request,
                now,
                retry_timeout,
                limit,
            );
            effects_match(document, final_document, notes)
        }),
{
    let initial_body = spec_stored_body(document);
    let (final_body, _, _, notes) = spec_request_transition(
        initial_body,
        request,
        now,
        retry_timeout,
        limit,
    );
    assert(match initial_body {
        DocumentBodyV::Workflow(old) =>
            forall|id: Seq<char>| old.contains_key(id) ==>
                old[id].promise.listeners.no_duplicates(),
        DocumentBodyV::Schedule(_) => true,
    }) by {
        match document {
            StoredDocumentV::Workflow(workflow) => {
                reveal(crate::document::workflow_well_formed);
                reveal(crate::document::workflow_body_well_formed);
                assert(crate::document::workflow_well_formed(workflow));
                assert(crate::document::workflow_body_well_formed(
                    workflow.document,
                    workflow.objects,
                    workflow.committed_at,
                ));
                assert forall|id: Seq<char>|
                    workflow.objects.contains_key(id) implies
                        workflow.objects[id].promise.listeners.no_duplicates() by {
                    assert({
                        &&& echod_types::origin(id) == workflow.document
                        &&& crate::document::promise_well_formed(
                            id,
                            workflow.objects[id],
                            workflow.committed_at,
                        )
                        &&& crate::document::task_well_formed(
                            workflow.objects[id],
                            workflow.committed_at,
                        )
                        &&& crate::document::callback_targets_well_formed(
                            workflow.objects,
                            workflow.objects[id],
                        )
                        &&& crate::document::suspended_rung_well_formed(
                            workflow.objects,
                            id,
                            workflow.objects[id],
                        )
                    });
                    assert(crate::document::promise_well_formed(
                        id,
                        workflow.objects[id],
                        workflow.committed_at,
                    ));
                }
            },
            StoredDocumentV::Schedule(_) => {},
        }
    };
    if spec_request_commits(
        initial_body,
        request,
        now,
        retry_timeout,
        limit,
    ) {
        assert(notes == spec_committed_notes(initial_body, final_body, now));
        lemma_committed_notes_match(initial_body, final_body, now);
        match (document, final_body) {
            (StoredDocumentV::Workflow(old), DocumentBodyV::Workflow(new)) => {
                assert(on_request(
                    StoredDocumentV::Workflow(old),
                    request,
                    now,
                    retry_timeout,
                    limit,
                ) == crate::node::spec_advance_stored(
                    StoredDocumentV::Workflow(old),
                    DocumentBodyV::Workflow(new),
                    now,
                ));
                assert(document_effects(
                    StoredDocumentV::Workflow(old),
                    on_request(
                        StoredDocumentV::Workflow(old),
                        request,
                        now,
                        retry_timeout,
                        limit,
                    ),
                ) == workflow_effects(old.objects, new, now));
            },
            (StoredDocumentV::Schedule(old), DocumentBodyV::Schedule(new)) => {
                assert(document_effects(
                    StoredDocumentV::Schedule(old),
                    on_request(
                        StoredDocumentV::Schedule(old),
                        request,
                        now,
                        retry_timeout,
                        limit,
                    ),
                ) == ISet::<ProtocolEffectV>::empty());
            },
            _ => {},
        }
    } else {
        assert(notes =~= Seq::<NoteV>::empty());
        assert(on_request(document, request, now, retry_timeout, limit) == document);
        assert(document_effects(document, document)
            =~= ISet::<ProtocolEffectV>::empty()) by {
            match document {
                StoredDocumentV::Workflow(workflow) => {
                    assert forall|effect: ProtocolEffectV|
                        !workflow_effects(
                            workflow.objects,
                            workflow.objects,
                            workflow.committed_at,
                        ).contains(effect) by {
                        match effect {
                            ProtocolEffectV::Execute { .. } => {},
                            ProtocolEffectV::Unblock { .. } => {},
                        }
                    };
                },
                StoredDocumentV::Schedule(_) => {},
            }
        };
    }
    assert(note_effects(notes)
        == document_effects(
            document,
            on_request(document, request, now, retry_timeout, limit),
        ));
    assert(note_effect_keys(notes).no_duplicates());
}

} // verus!
