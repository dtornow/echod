//! Append planning and physical-store frame lemmas.

#![cfg(verus_keep_ghost)]

use vstd::prelude::*;

use super::*;

verus! {

/// A full conditional replacement is safe from its independently encoded
/// `after` document; it does not require the decoded `before` image to equal
/// the current physical document.
pub proof fn lemma_full_rewrite_preserves_persisted_document_without_base_equality(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
)
    requires
        persisted_documents_well_formed(store, prefix),
        certificate is DocumentFull,
        request is PutIfMatch,
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
    ensures
        persisted_documents_well_formed(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
        ),
{
    lemma_invariant1_certified_store_apply_preserves(
        store,
        prefix,
        bucket_ms,
        request,
        certificate,
    );
    reveal(invariant1_certified_store_apply_preserves);
}

pub(super) proof fn lemma_insert_at_entry_source(
    entries: Seq<EntryV>,
    added: EntryV,
    start: int,
    i: int,
)
    requires
        0 <= start,
        0 <= i < echod_concrete::store::spec_insert_at(
            entries,
            added,
            start,
        ).len(),
    ensures
        ({
            let result = echod_concrete::store::spec_insert_at(
                entries,
                added,
                start,
            );
            result[i] == added
                || exists|j: int|
                    0 <= j < entries.len()
                        && entries[j] == result[i]
        }),
    decreases entries.len() - start,
{
    reveal_with_fuel(echod_concrete::store::spec_insert_at, 1);
    if start >= entries.len() {
        assert(echod_concrete::store::spec_insert_at(
            entries,
            added,
            start,
        ) == entries.push(added));
        if i < entries.len() {
            assert(entries.push(added)[i] == entries[i]);
        } else {
            assert(i == entries.len());
            assert(entries.push(added)[i] == added);
        }
    } else if echod_concrete::store::spec_before(
        added.key,
        entries[start].key,
    ) {
        let result = entries.take(start).push(added)
            + entries.skip(start);
        if i < start {
            assert(result[i] == entries[i]);
        } else if i == start {
            assert(result[i] == added);
        } else {
            assert(result[i] == entries[i - 1]);
            assert(0 <= i - 1 < entries.len());
        }
    } else {
        lemma_insert_at_entry_source(entries, added, start + 1, i);
    }
}

pub(super) proof fn lemma_find_result_valid(
    entries: Seq<EntryV>,
    key: Seq<char>,
    start: int,
)
    requires
        0 <= start,
    ensures
        match echod_concrete::store::spec_find(entries, key, start) {
            Some(i) => {
                &&& start <= i < entries.len()
                &&& entries[i].key == key
            },
            None => true,
        },
    decreases entries.len() - start,
{
    reveal_with_fuel(echod_concrete::store::spec_find, 1);
    if start < entries.len() && entries[start].key != key {
        lemma_find_result_valid(entries, key, start + 1);
    }
}

pub(super) proof fn lemma_find_result_is_first(
    entries: Seq<EntryV>,
    key: Seq<char>,
    start: int,
    found: int,
)
    requires
        0 <= start,
        echod_concrete::store::spec_find(entries, key, start)
            == Some(found),
    ensures
        start <= found < entries.len(),
        entries[found].key == key,
        forall|i: int| start <= i < found ==>
            entries[i].key != key,
    decreases entries.len() - start,
{
    reveal_with_fuel(echod_concrete::store::spec_find, 1);
    if start < entries.len() && entries[start].key != key {
        lemma_find_result_is_first(entries, key, start + 1, found);
    } else {
        assert(found == start);
    }
}

pub(super) proof fn lemma_find_exists_before_witness(
    entries: Seq<EntryV>,
    key: Seq<char>,
    start: int,
    witness: int,
)
    requires
        0 <= start <= witness < entries.len(),
        entries[witness].key == key,
    ensures
        echod_concrete::store::spec_find(entries, key, start) is Some,
    decreases witness - start,
{
    reveal_with_fuel(echod_concrete::store::spec_find, 1);
    if entries[start].key != key {
        lemma_find_exists_before_witness(
            entries,
            key,
            start + 1,
            witness,
        );
    }
}

pub(super) proof fn lemma_first_index_is_find(
    entries: Seq<EntryV>,
    key: Seq<char>,
    start: int,
    found: int,
)
    requires
        0 <= start <= found < entries.len(),
        entries[found].key == key,
        forall|i: int| start <= i < found ==>
            entries[i].key != key,
    ensures
        echod_concrete::store::spec_find(entries, key, start)
            == Some(found),
    decreases found - start,
{
    reveal_with_fuel(echod_concrete::store::spec_find, 1);
    if start < found {
        assert(entries[start].key != key);
        lemma_first_index_is_find(entries, key, start + 1, found);
    }
}

pub(super) proof fn lemma_insert_at_has_single_insertion_shape(
    entries: Seq<EntryV>,
    added: EntryV,
    start: int,
)
    requires
        0 <= start <= entries.len(),
    ensures
        exists|at: int| {
            &&& start <= at <= entries.len()
            &&& echod_concrete::store::spec_insert_at(
                entries,
                added,
                start,
            ) == entries.take(at).push(added) + entries.skip(at)
        },
    decreases entries.len() - start,
{
    reveal_with_fuel(echod_concrete::store::spec_insert_at, 1);
    if start == entries.len() {
        assert(entries.take(entries.len() as int).push(added)
            + entries.skip(entries.len() as int)
            == entries.push(added));
    } else if echod_concrete::store::spec_before(
        added.key,
        entries[start].key,
    ) {
    } else {
        lemma_insert_at_has_single_insertion_shape(
            entries,
            added,
            start + 1,
        );
        let at = choose|at: int| {
            &&& start + 1 <= at <= entries.len()
            &&& echod_concrete::store::spec_insert_at(
                entries,
                added,
                start + 1,
            ) == entries.take(at).push(added) + entries.skip(at)
        };
        assert(echod_concrete::store::spec_insert_at(
            entries,
            added,
            start,
        ) == echod_concrete::store::spec_insert_at(
            entries,
            added,
            start + 1,
        ));
        assert(exists|witness: int| {
            &&& start <= witness <= entries.len()
            &&& echod_concrete::store::spec_insert_at(
                entries,
                added,
                start,
            ) == entries.take(witness).push(added)
                + entries.skip(witness)
        }) by {
            let witness = at;
        };
    }
}

pub(super) proof fn lemma_insert_at_preserves_first_other_key(
    entries: Seq<EntryV>,
    added: EntryV,
    key: Seq<char>,
    found: int,
)
    requires
        echod_concrete::store::spec_find(entries, key, 0)
            == Some(found),
        added.key != key,
    ensures
        ({
            let next = echod_concrete::store::spec_insert_at(
                entries,
                added,
                0,
            );
            let next_found =
                echod_concrete::store::spec_find(next, key, 0).unwrap();
            &&& echod_concrete::store::spec_find(next, key, 0) is Some
            &&& next[next_found] == entries[found]
        }),
{
    lemma_find_result_is_first(entries, key, 0, found);
    lemma_insert_at_has_single_insertion_shape(entries, added, 0);
    let at = choose|at: int| {
        &&& 0 <= at <= entries.len()
        &&& echod_concrete::store::spec_insert_at(entries, added, 0)
            == entries.take(at).push(added) + entries.skip(at)
    };
    let next =
        echod_concrete::store::spec_insert_at(entries, added, 0);
    let next_found = if at <= found { found + 1 } else { found };
    assert(0 <= next_found < next.len());
    assert(next[next_found] == entries[found]);
    assert forall|i: int| 0 <= i < next_found implies
        next[i].key != key by {
        if i < at {
            assert(next[i] == entries[i]);
        } else if i == at {
            assert(next[i] == added);
        } else {
            assert(next[i] == entries[i - 1]);
        }
    };
    lemma_first_index_is_find(next, key, 0, next_found);
}

pub(super) proof fn lemma_put_preserves_first_other_key(
    entries: Seq<EntryV>,
    added: EntryV,
    key: Seq<char>,
    found: int,
)
    requires
        echod_concrete::store::spec_find(entries, key, 0)
            == Some(found),
        added.key != key,
    ensures
        ({
            let next = echod_concrete::store::spec_put(entries, added);
            let next_found =
                echod_concrete::store::spec_find(next, key, 0).unwrap();
            &&& echod_concrete::store::spec_find(next, key, 0) is Some
            &&& next[next_found] == entries[found]
        }),
{
    reveal(echod_concrete::store::spec_put);
    lemma_find_result_is_first(entries, key, 0, found);
    match echod_concrete::store::spec_find(entries, added.key, 0) {
        Some(updated) => {
            lemma_find_result_valid(entries, added.key, 0);
            assert(updated != found);
            let next = entries.update(updated, added);
            assert(next[found] == entries[found]);
            assert forall|i: int| 0 <= i < found implies
                next[i].key != key by {
                if i == updated {
                    assert(next[i] == added);
                } else {
                    assert(next[i] == entries[i]);
                }
            };
            lemma_first_index_is_find(next, key, 0, found);
        },
        None => {
            lemma_insert_at_preserves_first_other_key(
                entries,
                added,
                key,
                found,
            );
        },
    }
}

pub(super) proof fn lemma_remove_at_preserves_first_other_key(
    entries: Seq<EntryV>,
    removed: int,
    key: Seq<char>,
    found: int,
)
    requires
        0 <= removed < entries.len(),
        entries[removed].key != key,
        echod_concrete::store::spec_find(entries, key, 0)
            == Some(found),
    ensures
        ({
            let next =
                echod_concrete::store::spec_remove_at(entries, removed);
            let next_found =
                echod_concrete::store::spec_find(next, key, 0).unwrap();
            &&& echod_concrete::store::spec_find(next, key, 0) is Some
            &&& next[next_found] == entries[found]
        }),
{
    reveal(echod_concrete::store::spec_remove_at);
    lemma_find_result_is_first(entries, key, 0, found);
    assert(removed != found);
    let next = entries.take(removed) + entries.skip(removed + 1);
    let next_found = if removed < found { found - 1 } else { found };
    assert(0 <= next_found < next.len());
    assert(next[next_found] == entries[found]);
    assert forall|i: int| 0 <= i < next_found implies
        next[i].key != key by {
        if i < removed {
            assert(next[i] == entries[i]);
        } else {
            assert(next[i] == entries[i + 1]);
        }
    };
    lemma_first_index_is_find(next, key, 0, next_found);
}

pub(super) proof fn lemma_put_entry_source(
    entries: Seq<EntryV>,
    added: EntryV,
    i: int,
)
    requires
        0 <= i < echod_concrete::store::spec_put(
            entries,
            added,
        ).len(),
    ensures
        ({
            let result = echod_concrete::store::spec_put(
                entries,
                added,
            );
            result[i] == added
                || exists|j: int|
                    0 <= j < entries.len()
                        && entries[j] == result[i]
        }),
{
    lemma_find_result_valid(entries, added.key, 0);
    match echod_concrete::store::spec_find(entries, added.key, 0) {
        Some(found) => {
            if i == found {
            } else {
                assert(entries.update(found, added)[i] == entries[i]);
            }
        },
        None => {
            lemma_insert_at_entry_source(entries, added, 0, i);
        },
    }
}

pub(super) proof fn lemma_insert_at_retains_entry(
    entries: Seq<EntryV>,
    added: EntryV,
    start: int,
    j: int,
)
    requires
        0 <= start,
        0 <= j < entries.len(),
    ensures
        ({
            let result = echod_concrete::store::spec_insert_at(
                entries,
                added,
                start,
            );
            exists|i: int|
                0 <= i < result.len() && result[i] == entries[j]
        }),
    decreases entries.len() - start,
{
    reveal_with_fuel(echod_concrete::store::spec_insert_at, 1);
    if start >= entries.len() {
        assert(echod_concrete::store::spec_insert_at(
            entries,
            added,
            start,
        ) == entries.push(added));
        assert(entries.push(added)[j] == entries[j]);
        assert(exists|i: int|
            0 <= i < entries.push(added).len()
                && entries.push(added)[i] == entries[j]) by {
            assert(0 <= j < entries.push(added).len());
        };
    } else if echod_concrete::store::spec_before(
        added.key,
        entries[start].key,
    ) {
        let result = entries.take(start).push(added)
            + entries.skip(start);
        assert(echod_concrete::store::spec_insert_at(
            entries,
            added,
            start,
        ) == result);
        if j < start {
            assert(result[j] == entries[j]);
            assert(exists|i: int|
                0 <= i < result.len()
                    && result[i] == entries[j]) by {};
        } else {
            assert(result[j + 1] == entries[j]);
            assert(0 <= j + 1 < result.len());
            assert(exists|i: int|
                0 <= i < result.len()
                    && result[i] == entries[j]) by {};
        }
    } else {
        lemma_insert_at_retains_entry(entries, added, start + 1, j);
        assert(echod_concrete::store::spec_insert_at(
            entries,
            added,
            start,
        ) == echod_concrete::store::spec_insert_at(
            entries,
            added,
            start + 1,
        ));
    }
}

pub(super) proof fn lemma_insert_at_contains_added(
    entries: Seq<EntryV>,
    added: EntryV,
    start: int,
)
    requires
        0 <= start,
    ensures
        ({
            let result = echod_concrete::store::spec_insert_at(
                entries,
                added,
                start,
            );
            exists|i: int|
                0 <= i < result.len() && result[i] == added
        }),
    decreases entries.len() - start,
{
    reveal_with_fuel(echod_concrete::store::spec_insert_at, 1);
    if start >= entries.len() {
        assert(entries.push(added).last() == added);
        assert(exists|i: int|
            0 <= i < entries.push(added).len()
                && entries.push(added)[i] == added) by {
            let i = entries.len() as int;
            assert(entries.push(added)[i] == added);
        };
    } else if echod_concrete::store::spec_before(
        added.key,
        entries[start].key,
    ) {
        let result = entries.take(start).push(added)
            + entries.skip(start);
        assert(result[start] == added);
        assert(exists|i: int|
            0 <= i < result.len() && result[i] == added) by {};
    } else {
        lemma_insert_at_contains_added(entries, added, start + 1);
        let later = echod_concrete::store::spec_insert_at(
            entries,
            added,
            start + 1,
        );
        let i = choose|i: int|
            0 <= i < later.len() && later[i] == added;
        assert(echod_concrete::store::spec_insert_at(
            entries,
            added,
            start,
        ) == later);
        assert(exists|j: int|
            0 <= j
                < echod_concrete::store::spec_insert_at(
                    entries,
                    added,
                    start,
                ).len()
                && echod_concrete::store::spec_insert_at(
                    entries,
                    added,
                    start,
                )[j] == added) by {
            assert(0 <= i < later.len());
            assert(later[i] == added);
        };
    }
}

pub(super) proof fn lemma_put_contains_added(
    entries: Seq<EntryV>,
    added: EntryV,
)
    ensures
        ({
            let result = echod_concrete::store::spec_put(
                entries,
                added,
            );
            exists|i: int|
                0 <= i < result.len() && result[i] == added
        }),
{
    lemma_find_result_valid(entries, added.key, 0);
    reveal(echod_concrete::store::spec_put);
    match echod_concrete::store::spec_find(entries, added.key, 0) {
        Some(found) => {
            assert(echod_concrete::store::spec_put(entries, added)
                == entries.update(found, added));
            assert(entries.update(found, added)[found] == added);
            assert(exists|i: int|
                0 <= i < entries.update(found, added).len()
                    && entries.update(found, added)[i] == added) by {};
        },
        None => {
            lemma_insert_at_contains_added(entries, added, 0);
            assert(echod_concrete::store::spec_put(entries, added)
                == echod_concrete::store::spec_insert_at(
                    entries,
                    added,
                    0,
                ));
        },
    }
}

pub(super) proof fn lemma_put_makes_added_first(
    entries: Seq<EntryV>,
    added: EntryV,
)
    ensures
        ({
            let result = echod_concrete::store::spec_put(entries, added);
            let found = echod_concrete::store::spec_find(
                result,
                added.key,
                0,
            ).unwrap();
            &&& echod_concrete::store::spec_find(
                result,
                added.key,
                0,
            ) is Some
            &&& result[found] == added
        }),
{
    reveal(echod_concrete::store::spec_put);
    match echod_concrete::store::spec_find(entries, added.key, 0) {
        Some(found) => {
            lemma_find_result_is_first(entries, added.key, 0, found);
            lemma_find_result_valid(entries, added.key, 0);
            let next = entries.update(found, added);
            assert(next[found] == added);
            assert forall|i: int| 0 <= i < found implies
                next[i].key != added.key by {
                assert(next[i] == entries[i]);
            };
            lemma_first_index_is_find(next, added.key, 0, found);
        },
        None => {
            let next = echod_concrete::store::spec_insert_at(
                entries,
                added,
                0,
            );
            lemma_insert_at_has_single_insertion_shape(
                entries,
                added,
                0,
            );
            let at = choose|at: int| {
                &&& 0 <= at <= entries.len()
                &&& next
                    == entries.take(at).push(added)
                        + entries.skip(at)
            };
            assert(0 <= at < next.len());
            assert(next[at] == added);
            assert forall|i: int| 0 <= i < at implies
                next[i].key != added.key by {
                assert(next[i] == entries[i]);
                if entries[i].key == added.key {
                    lemma_find_exists_before_witness(
                        entries,
                        added.key,
                        0,
                        i,
                    );
                }
            };
            lemma_first_index_is_find(
                next,
                added.key,
                0,
                at,
            );
        },
    }
}

pub(super) proof fn lemma_put_retains_distinct_entry(
    entries: Seq<EntryV>,
    added: EntryV,
    j: int,
)
    requires
        0 <= j < entries.len(),
        entries[j].key != added.key,
    ensures
        ({
            let result = echod_concrete::store::spec_put(
                entries,
                added,
            );
            exists|i: int|
                0 <= i < result.len() && result[i] == entries[j]
        }),
{
    lemma_find_result_valid(entries, added.key, 0);
    reveal(echod_concrete::store::spec_put);
    match echod_concrete::store::spec_find(entries, added.key, 0) {
        Some(found) => {
            assert(echod_concrete::store::spec_put(entries, added)
                == entries.update(found, added));
            assert(j != found);
            assert(entries.update(found, added)[j] == entries[j]);
            assert(exists|i: int|
                0 <= i < entries.update(found, added).len()
                    && entries.update(found, added)[i] == entries[j]) by {
                assert(0 <= j < entries.update(found, added).len());
            };
        },
        None => {
            lemma_insert_at_retains_entry(entries, added, 0, j);
            assert(echod_concrete::store::spec_put(entries, added)
                == echod_concrete::store::spec_insert_at(
                    entries,
                    added,
                    0,
                ));
        },
    }
}

pub(super) proof fn lemma_remove_at_entry_source(
    entries: Seq<EntryV>,
    removed: int,
    i: int,
)
    requires
        0 <= removed < entries.len(),
        0 <= i < echod_concrete::store::spec_remove_at(
            entries,
            removed,
        ).len(),
    ensures
        exists|j: int|
            0 <= j < entries.len()
                && entries[j]
                    == echod_concrete::store::spec_remove_at(
                        entries,
                        removed,
                    )[i],
{
    if i < removed {
        assert(echod_concrete::store::spec_remove_at(
            entries,
            removed,
        )[i] == entries[i]);
    } else {
        assert(echod_concrete::store::spec_remove_at(
            entries,
            removed,
        )[i] == entries[i + 1]);
        assert(0 <= i + 1 < entries.len());
    }
}

pub(super) proof fn lemma_remove_at_retains_distinct_entry(
    entries: Seq<EntryV>,
    removed: int,
    j: int,
)
    requires
        0 <= removed < entries.len(),
        0 <= j < entries.len(),
        j != removed,
    ensures
        ({
            let result = echod_concrete::store::spec_remove_at(
                entries,
                removed,
            );
            exists|i: int|
                0 <= i < result.len() && result[i] == entries[j]
        }),
{
    let result =
        echod_concrete::store::spec_remove_at(entries, removed);
    if j < removed {
        assert(result[j] == entries[j]);
        assert(0 <= j < result.len());
    } else {
        assert(removed < j);
        assert(result[j - 1] == entries[j]);
        assert(0 <= j - 1 < result.len());
    }
}

pub(super) proof fn lemma_remove_retains_origin_timer_if_key_differs(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    removed: int,
    workflow: WorkflowDocumentV,
)
    requires
        0 <= removed < store.entries.len(),
        !is_timer_namespace_key(
            prefix,
            store.entries[removed].key,
        ),
        store_contains_origin_timer(
            store,
            prefix,
            bucket_ms,
            workflow,
        ),
    ensures
        store_contains_origin_timer(
            StoreV {
                entries: echod_concrete::store::spec_remove_at(
                    store.entries,
                    removed,
                ),
                ..store
            },
            prefix,
            bucket_ms,
            workflow,
        ),
{
    let witness = choose|witness: (u64, Seq<char>, int)|
        #![trigger
            store.entries[witness.2].key,
            crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                witness.0,
                witness.1,
            )
        ]
        0 <= witness.2 < store.entries.len()
            && store.entries[witness.2].key
                == crate::keys::spec_timer_key(
                    prefix,
                    bucket_ms,
                    workflow.document,
                    workflow.next_wake_at.unwrap(),
                    witness.0,
                    witness.1,
                )
            && store.entries[witness.2].body.len() == 0;
    assert(is_timer_namespace_key(
        prefix,
        store.entries[witness.2].key,
    )) by {
        lemma_origin_timer_is_timer_namespace(
            prefix,
            bucket_ms,
            workflow.document,
            workflow.next_wake_at.unwrap(),
            witness.0,
            witness.1,
        );
    };
    assert(witness.2 != removed);
    lemma_remove_at_retains_distinct_entry(
        store.entries,
        removed,
        witness.2,
    );
    let next_entries = echod_concrete::store::spec_remove_at(
        store.entries,
        removed,
    );
    let next = StoreV { entries: next_entries, ..store };
    let next_i = choose|i: int|
        0 <= i < next_entries.len()
            && next_entries[i] == store.entries[witness.2];
    assert(0 <= next_i < next_entries.len());
    assert(next_entries[next_i] == store.entries[witness.2]);
    assert(store.entries[witness.2].key
        == crate::keys::spec_timer_key(
            prefix,
            bucket_ms,
            workflow.document,
            workflow.next_wake_at.unwrap(),
            witness.0,
            witness.1,
        ));
    assert(store.entries[witness.2].body.len() == 0);
    assert(workflow.next_wake_at is Some);
    assert(exists|next_witness: (u64, Seq<char>, int)|
        #![trigger
            next_entries[next_witness.2].key,
            crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                next_witness.0,
                next_witness.1,
            )
        ]
        0 <= next_witness.2 < next_entries.len()
            && next_entries[next_witness.2].key
                == crate::keys::spec_timer_key(
                    prefix,
                    bucket_ms,
                    workflow.document,
                    workflow.next_wake_at.unwrap(),
                    next_witness.0,
                    next_witness.1,
                )
            && next_entries[next_witness.2].body.len() == 0) by {
        let next_witness = (witness.0, witness.1, next_i);
        assert(0 <= next_witness.2 < next_entries.len());
        assert(next_entries[next_witness.2].key
            == crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                next_witness.0,
                next_witness.1,
            ));
        assert(next_entries[next_witness.2].body.len() == 0);
    };
    assert(next.entries == next_entries);
    assert(exists|next_witness: (u64, Seq<char>, int)|
        #![trigger
            next.entries[next_witness.2].key,
            crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                next_witness.0,
                next_witness.1,
            )
        ]
        0 <= next_witness.2 < next.entries.len()
            && next.entries[next_witness.2].key
                == crate::keys::spec_timer_key(
                    prefix,
                    bucket_ms,
                    workflow.document,
                    workflow.next_wake_at.unwrap(),
                    next_witness.0,
                    next_witness.1,
                )
            && next.entries[next_witness.2].body.len() == 0) by {
        let next_witness = (witness.0, witness.1, next_i);
        assert(next.entries[next_witness.2]
            == next_entries[next_witness.2]);
        assert(next_entries[next_i].key
            == crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                witness.0,
                witness.1,
            ));
        assert(next_entries[next_i].body.len() == 0);
    };
}

pub(super) proof fn lemma_remove_retains_empty_key_if_distinct(
    store: StoreV,
    removed: int,
    name: Seq<char>,
)
    requires
        0 <= removed < store.entries.len(),
        store_contains_empty_key(store, name),
        store.entries[removed].key != name,
    ensures
        store_contains_empty_key(
            StoreV {
                entries: echod_concrete::store::spec_remove_at(
                    store.entries,
                    removed,
                ),
                ..store
            },
            name,
        ),
{
    reveal(store_contains_empty_key);
    let i = choose|i: int|
        0 <= i < store.entries.len()
            && store.entries[i].key == name
            && store.entries[i].body.len() == 0;
    assert(i != removed);
    let next_entries = echod_concrete::store::spec_remove_at(
        store.entries,
        removed,
    );
    let next = StoreV { entries: next_entries, ..store };
    lemma_remove_at_retains_distinct_entry(
        store.entries,
        removed,
        i,
    );
    let j = choose|j: int|
        0 <= j < next_entries.len()
            && next_entries[j] == store.entries[i];
    assert(exists|j: int|
        0 <= j < next_entries.len()
            && next_entries[j].key == name
            && next_entries[j].body.len() == 0) by {};
    assert(next.entries[j] == next_entries[j]);
    assert(exists|k: int|
        0 <= k < next.entries.len()
            && next.entries[k].key == name
            && next.entries[k].body.len() == 0) by {};
    assert(store_contains_empty_key(next, name));
}

pub(super) proof fn lemma_put_retains_empty_key_if_safe(
    store: StoreV,
    added: EntryV,
    name: Seq<char>,
)
    requires
        store_contains_empty_key(store, name),
        added.key != name || added.body.len() == 0,
    ensures
        store_contains_empty_key(
            StoreV {
                entries: echod_concrete::store::spec_put(
                    store.entries,
                    added,
                ),
                ..store
            },
            name,
        ),
{
    reveal(store_contains_empty_key);
    let old = choose|i: int|
        0 <= i < store.entries.len()
            && store.entries[i].key == name
            && store.entries[i].body.len() == 0;
    let next_entries =
        echod_concrete::store::spec_put(store.entries, added);
    let next = StoreV { entries: next_entries, ..store };
    if added.key == name {
        lemma_put_contains_added(store.entries, added);
        let i = choose|i: int|
            0 <= i < next_entries.len()
                && next_entries[i] == added;
        assert(exists|i: int|
            0 <= i < next_entries.len()
                && next_entries[i].key == name
                && next_entries[i].body.len() == 0) by {};
    } else {
        lemma_put_retains_distinct_entry(
            store.entries,
            added,
            old,
        );
        let i = choose|i: int|
            0 <= i < next_entries.len()
                && next_entries[i] == store.entries[old];
        assert(exists|i: int|
            0 <= i < next_entries.len()
                && next_entries[i].key == name
                && next_entries[i].body.len() == 0) by {};
    }
    assert(exists|i: int|
        0 <= i < next.entries.len()
            && next.entries[i].key == name
            && next.entries[i].body.len() == 0) by {
        let i = choose|i: int|
            0 <= i < next_entries.len()
                && next_entries[i].key == name
                && next_entries[i].body.len() == 0;
        assert(next.entries[i] == next_entries[i]);
    };
    assert(store_contains_empty_key(next, name));
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_put_preserves_protected_documents(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    added: EntryV,
    before_names: Set<Seq<char>>,
    after_names: Set<Seq<char>>,
)
    requires
        store_documents_protected_from_deletes(
            store,
            prefix,
            bucket_ms,
            before_names,
        ),
        after_names.subset_of(before_names),
        is_document_key(prefix, added.key) ==> (
            exists|provenance: DocumentProvenanceV|
                #[trigger] entry_has_document_provenance(
                    added,
                    prefix,
                    provenance,
                )
                && (provenance_document(provenance) is Workflow
                    && top_level_pending(
                        provenance_document(provenance)->Workflow_0,
                    ) ==> {
                        &&& provenance.required_timer is Some
                        &&& current_origin_timer_name(
                            prefix,
                            bucket_ms,
                            provenance_document(provenance)->Workflow_0,
                            provenance.required_timer.unwrap(),
                        )
                        &&& store_contains_empty_key(
                            store,
                            provenance.required_timer.unwrap(),
                        )
                        &&& forall|name: Seq<char>|
                            after_names.contains(name) ==>
                                provenance.required_timer.unwrap() != name
                    })
        ),
        !is_document_key(prefix, added.key) ==> (
            !is_timer_namespace_key(prefix, added.key)
                || added.body.len() == 0
        ),
    ensures
        store_documents_protected_from_deletes(
            StoreV {
                entries: echod_concrete::store::spec_put(
                    store.entries,
                    added,
                ),
                ..store
            },
            prefix,
            bucket_ms,
            after_names,
        ),
{
    let next = StoreV {
        entries: echod_concrete::store::spec_put(
            store.entries,
            added,
        ),
        ..store
    };
    assert forall|i: int|
        0 <= i < next.entries.len()
            && is_document_key(prefix, next.entries[i].key)
        implies exists|provenance: DocumentProvenanceV|
            #[trigger] protected_document_provenance(
                next,
                prefix,
                bucket_ms,
                i,
                after_names,
                provenance,
            ) by {
        lemma_put_entry_source(store.entries, added, i);
        if next.entries[i] == added {
            if is_document_key(prefix, added.key) {
                let provenance =
                    choose|provenance: DocumentProvenanceV|
                        entry_has_document_provenance(
                            added,
                            prefix,
                            provenance,
                        )
                        && (provenance_document(provenance) is Workflow
                            && top_level_pending(
                                provenance_document(
                                    provenance,
                                )->Workflow_0,
                            ) ==> {
                                &&& provenance.required_timer is Some
                                &&& current_origin_timer_name(
                                    prefix,
                                    bucket_ms,
                                    provenance_document(
                                        provenance,
                                    )->Workflow_0,
                                    provenance.required_timer.unwrap(),
                                )
                                &&& store_contains_empty_key(
                                    store,
                                    provenance.required_timer.unwrap(),
                                )
                                &&& forall|name: Seq<char>|
                                    after_names.contains(name) ==>
                                        provenance.required_timer.unwrap()
                                            != name
                            });
                if provenance_document(provenance) is Workflow
                    && top_level_pending(
                        provenance_document(provenance)->Workflow_0,
                    )
                {
                    reveal(current_origin_timer_name);
                    let identity = choose|identity: (u64, Seq<char>)|
                        provenance.required_timer.unwrap()
                            == crate::keys::spec_timer_key(
                                prefix,
                                bucket_ms,
                                provenance_document(
                                    provenance,
                                )->Workflow_0.document,
                                provenance_document(
                                    provenance,
                                )->Workflow_0.next_wake_at.unwrap(),
                                identity.0,
                                identity.1,
                            );
                    lemma_origin_timer_is_timer_namespace(
                        prefix,
                        bucket_ms,
                        provenance_document(provenance)->Workflow_0.document,
                        provenance_document(provenance)->Workflow_0
                            .next_wake_at.unwrap(),
                        identity.0,
                        identity.1,
                    );
                    lemma_timer_namespace_is_not_document_key(
                        prefix,
                        provenance.required_timer.unwrap(),
                    );
                    lemma_put_retains_empty_key_if_safe(
                        store,
                        added,
                        provenance.required_timer.unwrap(),
                    );
                }
                assert(protected_document_provenance(
                    next,
                    prefix,
                    bucket_ms,
                    i,
                    after_names,
                    provenance,
                ));
            } else {
                assert(false);
            }
        } else {
            let old = choose|old: int|
                0 <= old < store.entries.len()
                    && store.entries[old] == next.entries[i];
            let provenance =
                choose|provenance: DocumentProvenanceV|
                    protected_document_provenance(
                        store,
                        prefix,
                        bucket_ms,
                        old,
                        before_names,
                        provenance,
                    );
            if provenance_document(provenance) is Workflow
                && top_level_pending(
                    provenance_document(provenance)->Workflow_0,
                )
            {
                reveal(current_origin_timer_name);
                let identity = choose|identity: (u64, Seq<char>)|
                    provenance.required_timer.unwrap()
                        == crate::keys::spec_timer_key(
                            prefix,
                            bucket_ms,
                            provenance_document(
                                provenance,
                            )->Workflow_0.document,
                            provenance_document(
                                provenance,
                            )->Workflow_0.next_wake_at.unwrap(),
                            identity.0,
                            identity.1,
                        );
                lemma_origin_timer_is_timer_namespace(
                    prefix,
                    bucket_ms,
                    provenance_document(provenance)->Workflow_0.document,
                    provenance_document(provenance)->Workflow_0
                        .next_wake_at.unwrap(),
                    identity.0,
                    identity.1,
                );
                if is_document_key(prefix, added.key) {
                    lemma_timer_namespace_is_not_document_key(
                        prefix,
                        provenance.required_timer.unwrap(),
                    );
                }
                assert(added.key != provenance.required_timer.unwrap()
                    || added.body.len() == 0);
                lemma_put_retains_empty_key_if_safe(
                    store,
                    added,
                    provenance.required_timer.unwrap(),
                );
                assert forall|name: Seq<char>|
                    after_names.contains(name) implies
                        provenance.required_timer.unwrap() != name by {
                    assert(before_names.contains(name));
                };
            }
            assert(protected_document_provenance(
                next,
                prefix,
                bucket_ms,
                i,
                after_names,
                provenance,
            ));
        }
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_remove_preserves_protected_documents(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    removed: int,
    before_names: Set<Seq<char>>,
    after_names: Set<Seq<char>>,
)
    requires
        0 <= removed < store.entries.len(),
        store_documents_protected_from_deletes(
            store,
            prefix,
            bucket_ms,
            before_names,
        ),
        after_names.subset_of(before_names),
        !is_timer_namespace_key(
            prefix,
            store.entries[removed].key,
        ) || before_names.contains(store.entries[removed].key),
    ensures
        store_documents_protected_from_deletes(
            StoreV {
                entries: echod_concrete::store::spec_remove_at(
                    store.entries,
                    removed,
                ),
                ..store
            },
            prefix,
            bucket_ms,
            after_names,
        ),
{
    let next = StoreV {
        entries: echod_concrete::store::spec_remove_at(
            store.entries,
            removed,
        ),
        ..store
    };
    assert forall|i: int|
        0 <= i < next.entries.len()
            && is_document_key(prefix, next.entries[i].key)
        implies exists|provenance: DocumentProvenanceV|
            #[trigger] protected_document_provenance(
                next,
                prefix,
                bucket_ms,
                i,
                after_names,
                provenance,
            ) by {
        lemma_remove_at_entry_source(store.entries, removed, i);
        let old = choose|old: int|
            0 <= old < store.entries.len()
                && store.entries[old] == next.entries[i];
        let provenance =
            choose|provenance: DocumentProvenanceV|
                protected_document_provenance(
                    store,
                    prefix,
                    bucket_ms,
                    old,
                    before_names,
                    provenance,
                );
        if provenance_document(provenance) is Workflow
            && top_level_pending(
                provenance_document(provenance)->Workflow_0,
            )
        {
            reveal(current_origin_timer_name);
            let identity = choose|identity: (u64, Seq<char>)|
                provenance.required_timer.unwrap()
                    == crate::keys::spec_timer_key(
                        prefix,
                        bucket_ms,
                        provenance_document(
                            provenance,
                        )->Workflow_0.document,
                        provenance_document(
                            provenance,
                        )->Workflow_0.next_wake_at.unwrap(),
                        identity.0,
                        identity.1,
                    );
            lemma_origin_timer_is_timer_namespace(
                prefix,
                bucket_ms,
                provenance_document(provenance)->Workflow_0.document,
                provenance_document(provenance)->Workflow_0
                    .next_wake_at.unwrap(),
                identity.0,
                identity.1,
            );
            if is_timer_namespace_key(
                prefix,
                store.entries[removed].key,
            ) {
                assert(before_names.contains(
                    store.entries[removed].key,
                ));
            }
            assert(provenance.required_timer.unwrap()
                != store.entries[removed].key);
            lemma_remove_retains_empty_key_if_distinct(
                store,
                removed,
                provenance.required_timer.unwrap(),
            );
            assert forall|name: Seq<char>|
                after_names.contains(name) implies
                    provenance.required_timer.unwrap() != name by {
                assert(before_names.contains(name));
            };
        }
        assert(protected_document_provenance(
            next,
            prefix,
            bucket_ms,
            i,
            after_names,
            provenance,
        ));
    };
}

pub(super) proof fn lemma_timer_delete_preserves_exact_durable_timers(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    removed: int,
)
    requires
        pending_top_levels_have_exact_durable_timers(
            store,
            prefix,
            bucket_ms,
        ),
        0 <= removed < store.entries.len(),
        timer_delete_preserves_protected_keys(
            store,
            prefix,
            bucket_ms,
            store.entries[removed].key,
        ),
    ensures
        pending_top_levels_have_exact_durable_timers(
            StoreV {
                entries: echod_concrete::store::spec_remove_at(
                    store.entries,
                    removed,
                ),
                ..store
            },
            prefix,
            bucket_ms,
        ),
{
    let next_entries = echod_concrete::store::spec_remove_at(
        store.entries,
        removed,
    );
    let next = StoreV { entries: next_entries, ..store };
    assert forall|i: int|
        0 <= i < next_entries.len()
            && is_document_key(prefix, next_entries[i].key) implies
        exists|provenance: DocumentProvenanceV|
            #[trigger] entry_has_document_provenance(
                next_entries[i],
                prefix,
                provenance,
            )
            && (provenance_document(provenance) is Workflow
                && top_level_pending(
                    provenance_document(provenance)->Workflow_0,
                ) ==> {
                    &&& provenance.required_timer is Some
                    &&& current_origin_timer_name(
                        prefix,
                        bucket_ms,
                        provenance_document(provenance)->Workflow_0,
                        provenance.required_timer.unwrap(),
                    )
                    &&& store_contains_empty_key(
                        next,
                        provenance.required_timer.unwrap(),
                    )
                }) by {
        lemma_remove_at_entry_source(store.entries, removed, i);
        let old_i = choose|old_i: int|
            0 <= old_i < store.entries.len()
                && store.entries[old_i] == next_entries[i];
        let provenance = choose|provenance: DocumentProvenanceV|
            entry_has_document_provenance(
                store.entries[old_i],
                prefix,
                provenance,
            )
            && (provenance_document(provenance) is Workflow
                && top_level_pending(
                    provenance_document(provenance)->Workflow_0,
                ) ==> {
                    &&& provenance.required_timer is Some
                    &&& current_origin_timer_name(
                        prefix,
                        bucket_ms,
                        provenance_document(provenance)->Workflow_0,
                        provenance.required_timer.unwrap(),
                    )
                    &&& store_contains_empty_key(
                        store,
                        provenance.required_timer.unwrap(),
                    )
                    &&& provenance.required_timer.unwrap()
                        != store.entries[removed].key
                });
        if provenance_document(provenance) is Workflow
            && top_level_pending(
                provenance_document(provenance)->Workflow_0,
            )
        {
            assert(provenance.required_timer.unwrap()
                != store.entries[removed].key);
            lemma_remove_retains_empty_key_if_distinct(
                store,
                removed,
                provenance.required_timer.unwrap(),
            );
        }
    };
}

pub(super) proof fn lemma_nondocument_remove_preserves_documents(
    store: StoreV,
    prefix: Seq<char>,
    removed: int,
)
    requires
        persisted_documents_well_formed(store, prefix),
        0 <= removed < store.entries.len(),
        !is_document_key(prefix, store.entries[removed].key),
    ensures
        persisted_documents_well_formed(
            StoreV {
                entries: echod_concrete::store::spec_remove_at(
                    store.entries,
                    removed,
                ),
                ..store
            },
            prefix,
        ),
{
    let next_entries = echod_concrete::store::spec_remove_at(
        store.entries,
        removed,
    );
    assert forall|i: int|
        0 <= i < next_entries.len()
            && is_document_key(prefix, next_entries[i].key) implies
        exists|p: DocumentProvenanceV|
            entry_has_document_provenance(
                #[trigger] next_entries[i],
                prefix,
                p,
            ) by {
        lemma_remove_at_entry_source(store.entries, removed, i);
        let j = choose|j: int|
            0 <= j < store.entries.len()
                && store.entries[j] == next_entries[i];
    };
}

pub(super) proof fn lemma_nontimer_remove_preserves_physical_invariants(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    removed: int,
)
    requires
        persisted_documents_well_formed(store, prefix),
        pending_top_levels_have_exact_durable_timers(
            store,
            prefix,
            bucket_ms,
        ),
        0 <= removed < store.entries.len(),
        !is_document_key(prefix, store.entries[removed].key),
        !is_timer_namespace_key(
            prefix,
            store.entries[removed].key,
        ),
    ensures
        ({
            let next = StoreV {
                entries: echod_concrete::store::spec_remove_at(
                    store.entries,
                    removed,
                ),
                ..store
            };
            &&& persisted_documents_well_formed(next, prefix)
            &&& pending_top_levels_have_exact_durable_timers(
                next,
                prefix,
                bucket_ms,
            )
        }),
{
    lemma_nondocument_remove_preserves_documents(
        store,
        prefix,
        removed,
    );
    let next_entries = echod_concrete::store::spec_remove_at(
        store.entries,
        removed,
    );
    let next = StoreV { entries: next_entries, ..store };
    assert forall|i: int|
        0 <= i < next_entries.len()
            && is_document_key(prefix, next_entries[i].key) implies
        exists|p: DocumentProvenanceV|
            #[trigger] entry_has_document_provenance(
                next_entries[i],
                prefix,
                p,
            )
            && (provenance_document(p) is Workflow
                && top_level_pending(
                    provenance_document(p)->Workflow_0,
                ) ==> {
                    &&& p.required_timer is Some
                    &&& current_origin_timer_name(
                        prefix,
                        bucket_ms,
                        provenance_document(p)->Workflow_0,
                        p.required_timer.unwrap(),
                    )
                    &&& store_contains_empty_key(
                        next,
                        p.required_timer.unwrap(),
                    )
                }) by {
        lemma_remove_at_entry_source(store.entries, removed, i);
        let j = choose|j: int|
            0 <= j < store.entries.len()
                && store.entries[j] == next_entries[i];
        let p = choose|p: DocumentProvenanceV|
            entry_has_document_provenance(
                store.entries[j],
                prefix,
                p,
            )
            && (provenance_document(p) is Workflow
                && top_level_pending(
                    provenance_document(p)->Workflow_0,
                ) ==> {
                    &&& p.required_timer is Some
                    &&& current_origin_timer_name(
                        prefix,
                        bucket_ms,
                        provenance_document(p)->Workflow_0,
                        p.required_timer.unwrap(),
                    )
                    &&& store_contains_empty_key(
                        store,
                        p.required_timer.unwrap(),
                    )
                });
        if provenance_document(p) is Workflow
            && top_level_pending(
                provenance_document(p)->Workflow_0,
            ) {
            reveal(current_origin_timer_name);
            let identity = choose|identity: (u64, Seq<char>)|
                p.required_timer.unwrap()
                    == crate::keys::spec_timer_key(
                        prefix,
                        bucket_ms,
                        provenance_document(p)->Workflow_0.document,
                        provenance_document(p)->Workflow_0
                            .next_wake_at.unwrap(),
                        identity.0,
                        identity.1,
                    );
            lemma_origin_timer_is_timer_namespace(
                prefix,
                bucket_ms,
                provenance_document(p)->Workflow_0.document,
                provenance_document(p)->Workflow_0.next_wake_at.unwrap(),
                identity.0,
                identity.1,
            );
            assert(store.entries[removed].key
                != p.required_timer.unwrap());
            lemma_remove_retains_empty_key_if_distinct(
                store,
                removed,
                p.required_timer.unwrap(),
            );
        }
    };
}

pub(super) proof fn lemma_document_put_retains_origin_timer(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    added: EntryV,
    document: StoredDocumentV,
    workflow: WorkflowDocumentV,
)
    requires
        added.key == document_key(prefix, document),
        store_contains_origin_timer(
            store,
            prefix,
            bucket_ms,
            workflow,
        ),
    ensures
        store_contains_origin_timer(
            StoreV {
                entries: echod_concrete::store::spec_put(
                    store.entries,
                    added,
                ),
                ..store
            },
            prefix,
            bucket_ms,
            workflow,
        ),
{
    let witness = choose|witness: (u64, Seq<char>, int)|
        #![trigger
            store.entries[witness.2].key,
            crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                witness.0,
                witness.1,
            )
        ]
        0 <= witness.2 < store.entries.len()
            && store.entries[witness.2].key
                == crate::keys::spec_timer_key(
                    prefix,
                    bucket_ms,
                    workflow.document,
                    workflow.next_wake_at.unwrap(),
                    witness.0,
                    witness.1,
                )
            && store.entries[witness.2].body.len() == 0;
    let token = witness.0;
    let by = witness.1;
    let i = witness.2;
    match document {
        StoredDocumentV::Workflow(doc) => {
            crate::keys::lemma_timer_key_is_not_document_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                token,
                by,
                doc.document,
                false,
            );
        },
        StoredDocumentV::Schedule(doc) => {
            crate::keys::lemma_timer_key_is_not_document_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                token,
                by,
                doc.document,
                true,
            );
        },
    }
    assert(store.entries[i].key != added.key);
    lemma_put_retains_distinct_entry(store.entries, added, i);
    let next_entries =
        echod_concrete::store::spec_put(store.entries, added);
    let next = StoreV { entries: next_entries, ..store };
    let next_i = choose|next_i: int|
        0 <= next_i < next_entries.len()
            && next_entries[next_i] == store.entries[i];
    assert(exists|next_witness: (u64, Seq<char>, int)|
        #![trigger
            next_entries[next_witness.2].key,
            crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                next_witness.0,
                next_witness.1,
            )
        ]
        0 <= next_witness.2 < next_entries.len()
            && next_entries[next_witness.2].key
                == crate::keys::spec_timer_key(
                    prefix,
                    bucket_ms,
                    workflow.document,
                    workflow.next_wake_at.unwrap(),
                    next_witness.0,
                    next_witness.1,
                )
            && next_entries[next_witness.2].body.len() == 0) by {
        assert(next_entries[next_i].key
            == crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                token,
                by,
            ));
        assert(next_entries[next_i].body.len() == 0);
        let next_witness = (token, by, next_i);
        assert(0 <= next_witness.2 < next_entries.len());
        assert(next_entries[next_witness.2].key
            == crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                next_witness.0,
                next_witness.1,
            ));
        assert(next_entries[next_witness.2].body.len() == 0);
    };
    assert(workflow.next_wake_at is Some);
    assert(next.entries == next_entries);
    assert(exists|next_witness: (u64, Seq<char>, int)|
        #![trigger
            next.entries[next_witness.2].key,
            crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                next_witness.0,
                next_witness.1,
            )
        ]
        0 <= next_witness.2 < next.entries.len()
            && next.entries[next_witness.2].key
                == crate::keys::spec_timer_key(
                    prefix,
                    bucket_ms,
                    workflow.document,
                    workflow.next_wake_at.unwrap(),
                    next_witness.0,
                    next_witness.1,
                )
            && next.entries[next_witness.2].body.len() == 0) by {
        let next_witness = (token, by, next_i);
        assert(next.entries[next_witness.2]
            == next_entries[next_witness.2]);
    };
    assert(store_contains_origin_timer(
        next,
        prefix,
        bucket_ms,
        workflow,
    ));
}

pub(super) proof fn lemma_safe_nondocument_put_retains_origin_timer(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    added: EntryV,
    workflow: WorkflowDocumentV,
)
    requires
        !is_timer_namespace_key(prefix, added.key)
            || added.body.len() == 0,
        store_contains_origin_timer(
            store,
            prefix,
            bucket_ms,
            workflow,
        ),
    ensures
        store_contains_origin_timer(
            StoreV {
                entries: echod_concrete::store::spec_put(
                    store.entries,
                    added,
                ),
                ..store
            },
            prefix,
            bucket_ms,
            workflow,
        ),
{
    let witness = choose|witness: (u64, Seq<char>, int)|
        #![trigger
            store.entries[witness.2].key,
            crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                witness.0,
                witness.1,
            )
        ]
        0 <= witness.2 < store.entries.len()
            && store.entries[witness.2].key
                == crate::keys::spec_timer_key(
                    prefix,
                    bucket_ms,
                    workflow.document,
                    workflow.next_wake_at.unwrap(),
                    witness.0,
                    witness.1,
                )
            && store.entries[witness.2].body.len() == 0;
    let old = store.entries[witness.2];
    let next_entries =
        echod_concrete::store::spec_put(store.entries, added);
    let next = StoreV { entries: next_entries, ..store };
    let next_i = if old.key == added.key {
        lemma_put_contains_added(store.entries, added);
        choose|i: int|
            0 <= i < next_entries.len()
                && next_entries[i] == added
    } else {
        lemma_put_retains_distinct_entry(
            store.entries,
            added,
            witness.2,
        );
        choose|i: int|
            0 <= i < next_entries.len()
                && next_entries[i] == old
    };
    assert(0 <= next_i < next_entries.len());
    assert(is_timer_namespace_key(prefix, old.key)) by {
        lemma_origin_timer_is_timer_namespace(
            prefix,
            bucket_ms,
            workflow.document,
            workflow.next_wake_at.unwrap(),
            witness.0,
            witness.1,
        );
    };
    if old.key == added.key {
        assert(added.body.len() == 0);
    }
    assert(old.key == crate::keys::spec_timer_key(
        prefix,
        bucket_ms,
        workflow.document,
        workflow.next_wake_at.unwrap(),
        witness.0,
        witness.1,
    ));
    assert(old.body.len() == 0);
    assert(next_entries[next_i].key == old.key);
    assert(next_entries[next_i].body.len() == 0);
    assert(workflow.next_wake_at is Some);
    assert(exists|next_witness: (u64, Seq<char>, int)|
        #![trigger
            next_entries[next_witness.2].key,
            crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                next_witness.0,
                next_witness.1,
            )
        ]
        0 <= next_witness.2 < next_entries.len()
            && next_entries[next_witness.2].key
                == crate::keys::spec_timer_key(
                    prefix,
                    bucket_ms,
                    workflow.document,
                    workflow.next_wake_at.unwrap(),
                    next_witness.0,
                    next_witness.1,
                )
            && next_entries[next_witness.2].body.len() == 0) by {
        let next_witness = (witness.0, witness.1, next_i);
        assert(0 <= next_witness.2 < next_entries.len());
        assert(next_entries[next_witness.2].key
            == crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                next_witness.0,
                next_witness.1,
            ));
        assert(next_entries[next_witness.2].body.len() == 0);
    };
    assert(next.entries == next_entries);
    assert(exists|next_witness: (u64, Seq<char>, int)|
        #![trigger
            next.entries[next_witness.2].key,
            crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                next_witness.0,
                next_witness.1,
            )
        ]
        0 <= next_witness.2 < next.entries.len()
            && next.entries[next_witness.2].key
                == crate::keys::spec_timer_key(
                    prefix,
                    bucket_ms,
                    workflow.document,
                    workflow.next_wake_at.unwrap(),
                    next_witness.0,
                    next_witness.1,
                )
            && next.entries[next_witness.2].body.len() == 0) by {
        let next_witness = (witness.0, witness.1, next_i);
        assert(next.entries[next_witness.2]
            == next_entries[next_witness.2]);
        assert(next_entries[next_i].key
            == crate::keys::spec_timer_key(
                prefix,
                bucket_ms,
                workflow.document,
                workflow.next_wake_at.unwrap(),
                witness.0,
                witness.1,
            ));
        assert(next_entries[next_i].body.len() == 0);
    };
}

pub(super) proof fn lemma_nondocument_put_preserves_physical_invariants(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    added: EntryV,
)
    requires
        persisted_documents_well_formed(store, prefix),
        pending_top_levels_have_exact_durable_timers(
            store,
            prefix,
            bucket_ms,
        ),
        !is_document_key(prefix, added.key),
        !is_timer_namespace_key(prefix, added.key)
            || added.body.len() == 0,
    ensures
        ({
            let next = StoreV {
                entries: echod_concrete::store::spec_put(
                    store.entries,
                    added,
                ),
                ..store
            };
            &&& persisted_documents_well_formed(next, prefix)
            &&& pending_top_levels_have_exact_durable_timers(
                next,
                prefix,
                bucket_ms,
            )
        }),
{
    let next_entries =
        echod_concrete::store::spec_put(store.entries, added);
    let next = StoreV { entries: next_entries, ..store };
    assert forall|i: int|
        0 <= i < next_entries.len()
            && is_document_key(prefix, next_entries[i].key) implies
        exists|p: DocumentProvenanceV|
            #[trigger] entry_has_document_provenance(
                next_entries[i],
                prefix,
                p,
            )
            && (provenance_document(p) is Workflow
                && top_level_pending(
                    provenance_document(p)->Workflow_0,
                ) ==> {
                    &&& p.required_timer is Some
                    &&& current_origin_timer_name(
                        prefix,
                        bucket_ms,
                        provenance_document(p)->Workflow_0,
                        p.required_timer.unwrap(),
                    )
                    &&& store_contains_empty_key(
                        next,
                        p.required_timer.unwrap(),
                    )
                }) by {
        lemma_put_entry_source(store.entries, added, i);
        assert(next_entries[i] != added);
        let j = choose|j: int|
            0 <= j < store.entries.len()
                && store.entries[j] == next_entries[i];
        let p = choose|p: DocumentProvenanceV|
            entry_has_document_provenance(
                store.entries[j],
                prefix,
                p,
            )
            && (provenance_document(p) is Workflow
                && top_level_pending(
                    provenance_document(p)->Workflow_0,
                ) ==> {
                    &&& p.required_timer is Some
                    &&& current_origin_timer_name(
                        prefix,
                        bucket_ms,
                        provenance_document(p)->Workflow_0,
                        p.required_timer.unwrap(),
                    )
                    &&& store_contains_empty_key(
                        store,
                        p.required_timer.unwrap(),
                    )
                });
        if provenance_document(p) is Workflow
            && top_level_pending(
                provenance_document(p)->Workflow_0,
            ) {
            reveal(current_origin_timer_name);
            let identity = choose|identity: (u64, Seq<char>)|
                p.required_timer.unwrap()
                    == crate::keys::spec_timer_key(
                        prefix,
                        bucket_ms,
                        provenance_document(p)->Workflow_0.document,
                        provenance_document(p)->Workflow_0
                            .next_wake_at.unwrap(),
                        identity.0,
                        identity.1,
                    );
            lemma_origin_timer_is_timer_namespace(
                prefix,
                bucket_ms,
                provenance_document(p)->Workflow_0.document,
                provenance_document(p)->Workflow_0.next_wake_at.unwrap(),
                identity.0,
                identity.1,
            );
            assert(added.key != p.required_timer.unwrap()
                || added.body.len() == 0);
            lemma_put_retains_empty_key_if_safe(
                store,
                added,
                p.required_timer.unwrap(),
            );
        }
    };
}

pub(super) proof fn lemma_document_put_preserves_physical_invariants(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    added: EntryV,
    provenance: DocumentProvenanceV,
)
    requires
        persisted_documents_well_formed(store, prefix),
        pending_top_levels_have_exact_durable_timers(
            store,
            prefix,
            bucket_ms,
        ),
        entry_has_document_provenance(added, prefix, provenance),
        provenance_document(provenance) is Workflow
            && top_level_pending(
                provenance_document(provenance)->Workflow_0,
            ) ==> {
                &&& provenance.required_timer is Some
                &&& current_origin_timer_name(
                    prefix,
                    bucket_ms,
                    provenance_document(provenance)->Workflow_0,
                    provenance.required_timer.unwrap(),
                )
                &&& store_contains_empty_key(
                    store,
                    provenance.required_timer.unwrap(),
                )
            },
    ensures
        ({
            let next = StoreV {
                entries: echod_concrete::store::spec_put(
                    store.entries,
                    added,
                ),
                ..store
            };
            &&& persisted_documents_well_formed(next, prefix)
            &&& pending_top_levels_have_exact_durable_timers(
                next,
                prefix,
                bucket_ms,
            )
        }),
{
    let next_entries =
        echod_concrete::store::spec_put(store.entries, added);
    let next = StoreV { entries: next_entries, ..store };
    assert forall|i: int|
        0 <= i < next_entries.len()
            && is_document_key(prefix, next_entries[i].key) implies
        exists|p: DocumentProvenanceV|
            entry_has_document_provenance(
                #[trigger] next_entries[i],
                prefix,
                p,
            ) by {
        lemma_put_entry_source(store.entries, added, i);
        if next_entries[i] == added {
        } else {
            let j = choose|j: int|
                0 <= j < store.entries.len()
                    && store.entries[j] == next_entries[i];
        }
    };
    assert forall|i: int|
        0 <= i < next_entries.len()
            && is_document_key(prefix, next_entries[i].key) implies
        exists|p: DocumentProvenanceV|
            #[trigger] entry_has_document_provenance(
                next_entries[i],
                prefix,
                p,
            )
            && (provenance_document(p) is Workflow
                && top_level_pending(
                    provenance_document(p)->Workflow_0,
                ) ==> {
                    &&& p.required_timer is Some
                    &&& current_origin_timer_name(
                        prefix,
                        bucket_ms,
                        provenance_document(p)->Workflow_0,
                        p.required_timer.unwrap(),
                    )
                    &&& store_contains_empty_key(
                        next,
                        p.required_timer.unwrap(),
                    )
                }) by {
        lemma_put_entry_source(store.entries, added, i);
        let p = if next_entries[i] == added {
            provenance
        } else {
            let j = choose|j: int|
                0 <= j < store.entries.len()
                    && store.entries[j] == next_entries[i];
            choose|old: DocumentProvenanceV|
                entry_has_document_provenance(
                    store.entries[j],
                    prefix,
                    old,
                )
                && (provenance_document(old) is Workflow
                    && top_level_pending(
                        provenance_document(old)->Workflow_0,
                    ) ==> {
                        &&& old.required_timer is Some
                        &&& current_origin_timer_name(
                            prefix,
                            bucket_ms,
                            provenance_document(old)->Workflow_0,
                            old.required_timer.unwrap(),
                        )
                        &&& store_contains_empty_key(
                            store,
                            old.required_timer.unwrap(),
                        )
                    })
        };
        if provenance_document(p) is Workflow
            && top_level_pending(
                provenance_document(p)->Workflow_0,
            ) {
            reveal(current_origin_timer_name);
            let identity = choose|identity: (u64, Seq<char>)|
                p.required_timer.unwrap()
                    == crate::keys::spec_timer_key(
                        prefix,
                        bucket_ms,
                        provenance_document(p)->Workflow_0.document,
                        provenance_document(p)->Workflow_0
                            .next_wake_at.unwrap(),
                        identity.0,
                        identity.1,
                    );
            lemma_origin_timer_is_timer_namespace(
                prefix,
                bucket_ms,
                provenance_document(p)->Workflow_0.document,
                provenance_document(p)->Workflow_0.next_wake_at.unwrap(),
                identity.0,
                identity.1,
            );
            lemma_timer_namespace_is_not_document_key(
                prefix,
                p.required_timer.unwrap(),
            );
            assert(added.key != p.required_timer.unwrap());
            lemma_put_retains_empty_key_if_safe(
                store,
                added,
                p.required_timer.unwrap(),
            );
        }
    };
}

pub(super) proof fn lemma_put_preserves_invariant1_documents(
    store: StoreV,
    prefix: Seq<char>,
    added: EntryV,
    provenance: Option<DocumentProvenanceV>,
)
    requires
        persisted_documents_well_formed(store, prefix),
        is_document_key(prefix, added.key) == provenance is Some,
        provenance is Some ==>
            entry_has_document_provenance(
                added,
                prefix,
                provenance.unwrap(),
            ),
    ensures
        persisted_documents_well_formed(
            StoreV {
                entries: echod_concrete::store::spec_put(
                    store.entries,
                    added,
                ),
                ..store
            },
            prefix,
        ),
{
    let next =
        echod_concrete::store::spec_put(store.entries, added);
    assert forall|i: int|
        0 <= i < next.len()
            && is_document_key(prefix, next[i].key)
        implies exists|p: DocumentProvenanceV|
            entry_has_document_provenance(
                #[trigger] next[i],
                prefix,
                p,
            ) by {
        lemma_put_entry_source(store.entries, added, i);
        if next[i] == added {
            assert(provenance is Some);
        } else {
            let old = choose|old: int|
                0 <= old < store.entries.len()
                    && store.entries[old] == next[i];
        }
    };
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_certified_store_apply_preserves(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
)
    ensures
        certified_store_apply_preserves(
            store,
            prefix,
            bucket_ms,
            request,
            certificate,
        ),
{
    reveal(certified_store_apply_preserves);
    reveal(invariant1_store_request_safe);
    if persisted_documents_well_formed(store, prefix)
        && pending_top_levels_have_exact_durable_timers(
            store,
            prefix,
            bucket_ms,
        )
        && store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        )
    {
      match request {
        StoreReq::Get { .. }
        | StoreReq::GetIfNoneMatch { .. }
        | StoreReq::List { .. }
        | StoreReq::ListPrefixes { .. } => {},
        StoreReq::PutIfNoneMatch { key, body } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(_) => {},
                None => match certificate {
                    StoreEffectCertificateV::DocumentFull {
                        before,
                        after,
                        required_timer,
                        ..
                    } => {
                        let added = EntryV {
                            key: key@,
                            body: body@,
                            version: 1,
                        };
                        let provenance = DocumentProvenanceV {
                            full: after,
                            deltas: Seq::empty(),
                            store_version: 1,
                            required_timer,
                        };
                        lemma_full_encoding_has_provenance(
                            prefix,
                            after,
                            1,
                            required_timer,
                        );
                        assert(added == EntryV {
                            key: document_key(prefix, after),
                            body: crate::document::spec_encode(after),
                            version: 1,
                        });
                        if after is Workflow
                            && top_level_pending(after->Workflow_0)
                        {
                            lemma_named_origin_timer_is_present(
                                store,
                                prefix,
                                bucket_ms,
                                after->Workflow_0,
                                required_timer.unwrap(),
                            );
                        }
                        lemma_document_put_preserves_physical_invariants(
                            store,
                            prefix,
                            bucket_ms,
                            added,
                            provenance,
                        );
                    },
                    StoreEffectCertificateV::Other => {
                        assert(!is_document_key(prefix, key@));
                        lemma_nondocument_put_preserves_physical_invariants(
                            store,
                            prefix,
                            bucket_ms,
                            EntryV {
                                key: key@,
                                body: body@,
                                version: 1,
                            },
                        );
                    },
                    _ => {},
                },
            }
        },
        StoreReq::PutIfMatch { key, body, etag } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(found) if echod_concrete::store::spec_etag(
                    store.entries[found].body,
                ) == etag => match certificate {
                    StoreEffectCertificateV::DocumentFull {
                        before,
                        after,
                        required_timer,
                        ..
                    } => {
                        let version = echod_concrete::store::spec_bump(
                            store.entries[found].version,
                        );
                        let added = EntryV {
                            key: key@,
                            body: body@,
                            version,
                        };
                        let provenance = DocumentProvenanceV {
                            full: after,
                            deltas: Seq::empty(),
                            store_version: version,
                            required_timer,
                        };
                        lemma_full_encoding_has_provenance(
                            prefix,
                            after,
                            version,
                            required_timer,
                        );
                        assert(added == EntryV {
                            key: document_key(prefix, after),
                            body: crate::document::spec_encode(after),
                            version,
                        });
                        if after is Workflow
                            && top_level_pending(after->Workflow_0)
                        {
                            lemma_named_origin_timer_is_present(
                                store,
                                prefix,
                                bucket_ms,
                                after->Workflow_0,
                                required_timer.unwrap(),
                            );
                        }
                        lemma_document_put_preserves_physical_invariants(
                            store,
                            prefix,
                            bucket_ms,
                            added,
                            provenance,
                        );
                    },
                    StoreEffectCertificateV::Other => {
                        assert(!is_document_key(prefix, key@));
                        lemma_nondocument_put_preserves_physical_invariants(
                            store,
                            prefix,
                            bucket_ms,
                            EntryV {
                                key: key@,
                                body: body@,
                                version: echod_concrete::store::spec_bump(
                                    store.entries[found].version,
                                ),
                            },
                        );
                    },
                    _ => {},
                },
                _ => {},
            }
        },
        StoreReq::AppIfMatch {
            key,
            offset,
            body,
            etag,
        } => {
            if store.appendable {
                match echod_concrete::store::spec_find(
                    store.entries,
                    key@,
                    0,
                ) {
                    Some(found) if echod_concrete::store::spec_etag(
                        store.entries[found].body,
                    ) == etag
                        && store.entries[found].body.len() == offset => {
                        match certificate {
                            StoreEffectCertificateV::DocumentAppend {
                                before,
                                after,
                                required_timer,
                                ..
                            } => {
                                lemma_find_result_valid(
                                    store.entries,
                                    key@,
                                    0,
                                );
                                assert(is_document_key(prefix, key@)) by {
                                    match after {
                                        StoredDocumentV::Workflow(doc) => {
                                            assert(exists|origin: Seq<char>|
                                                key@ == crate::keys::spec_doc_key(
                                                    prefix,
                                                    origin,
                                                )) by {};
                                        },
                                        StoredDocumentV::Schedule(doc) => {
                                            assert(exists|id: Seq<char>|
                                                key@ == crate::keys::spec_sched_key(
                                                    prefix,
                                                    id,
                                                )) by {};
                                        },
                                    }
                                };
                                let old = choose|old: DocumentProvenanceV|
                                    entry_has_document_provenance(
                                        store.entries[found],
                                        prefix,
                                        old,
                                    )
                                    && provenance_document(old) == before;
                                let version =
                                    echod_concrete::store::spec_bump(
                                        store.entries[found].version,
                                    );
                                let added = EntryV {
                                    key: key@,
                                    body: store.entries[found].body + body@,
                                    version,
                                };
                                let provenance = DocumentProvenanceV {
                                    full: old.full,
                                    deltas: old.deltas.push(
                                        DocumentDeltaV { before, after },
                                    ),
                                    store_version: version,
                                    required_timer,
                                };
                                lemma_delta_append_extends_provenance(
                                    store.entries[found],
                                    prefix,
                                    old,
                                    before,
                                    after,
                                    version,
                                    required_timer,
                                );
                                assert(added == EntryV {
                                    body: store.entries[found].body
                                        + crate::document::spec_encode_delta(
                                            before,
                                            after,
                                        ).0,
                                    version,
                                    ..store.entries[found]
                                });
                                if after is Workflow
                                    && top_level_pending(after->Workflow_0)
                                {
                                    lemma_named_origin_timer_is_present(
                                        store,
                                        prefix,
                                        bucket_ms,
                                        after->Workflow_0,
                                        required_timer.unwrap(),
                                    );
                                }
                                lemma_document_put_preserves_physical_invariants(
                                    store,
                                    prefix,
                                    bucket_ms,
                                    added,
                                    provenance,
                                );
                            },
                            StoreEffectCertificateV::Other => {
                                assert(!is_document_key(prefix, key@));
                                lemma_nondocument_put_preserves_physical_invariants(
                                    store,
                                    prefix,
                                    bucket_ms,
                                    EntryV {
                                        key: key@,
                                        body: store.entries[found].body + body@,
                                        version:
                                            echod_concrete::store::spec_bump(
                                                store.entries[found].version,
                                            ),
                                    },
                                );
                            },
                            _ => {},
                        }
                    },
                    _ => {},
                }
            }
        },
        StoreReq::Put { key, body } => {
            let version = match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(found) => echod_concrete::store::spec_bump(
                    store.entries[found].version,
                ),
                None => 1,
            };
            let added = EntryV { key: key@, body: body@, version };
            match certificate {
                StoreEffectCertificateV::TimerPut {
                    key: timer_key,
                    name,
                } => {
                    lemma_certificate_timer_is_namespace(
                        prefix,
                        bucket_ms,
                        timer_key,
                        name,
                    );
                    lemma_timer_namespace_is_not_document_key(
                        prefix,
                        key@,
                    );
                    lemma_nondocument_put_preserves_physical_invariants(
                        store,
                        prefix,
                        bucket_ms,
                        added,
                    );
                },
                StoreEffectCertificateV::Other => {
                    lemma_nondocument_put_preserves_physical_invariants(
                        store,
                        prefix,
                        bucket_ms,
                        added,
                    );
                },
                _ => {},
            }
        },
        StoreReq::Del { key } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(removed) => {
                    lemma_find_result_valid(
                        store.entries,
                        key@,
                        0,
                    );
                    match certificate {
                        StoreEffectCertificateV::TimerDelete {
                            key: timer_key,
                            name,
                        } => {
                            lemma_certificate_timer_is_namespace(
                                prefix,
                                bucket_ms,
                                timer_key,
                                name,
                            );
                            lemma_timer_namespace_is_not_document_key(
                                prefix,
                                key@,
                            );
                            lemma_nondocument_remove_preserves_documents(
                                store,
                                prefix,
                                removed,
                            );
                            lemma_timer_delete_preserves_exact_durable_timers(
                                store,
                                prefix,
                                bucket_ms,
                                removed,
                            );
                        },
                        StoreEffectCertificateV::Other => {
                            lemma_nontimer_remove_preserves_physical_invariants(
                                store,
                                prefix,
                                bucket_ms,
                                removed,
                            );
                        },
                        _ => {},
                    }
                },
                None => {},
            }
        },
      }
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_certified_store_apply_preserves_protected_documents(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
    before_names: Set<Seq<char>>,
    after_names: Set<Seq<char>>,
)
    requires
        store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
        store_documents_protected_from_deletes(
            store,
            prefix,
            bucket_ms,
            before_names,
        ),
        after_names.subset_of(before_names),
        certificate is TimerDelete ==>
            before_names.contains(certificate->TimerDelete_name),
        certificate_required_timer(certificate) is Some ==>
            forall|name: Seq<char>|
                after_names.contains(name) ==>
                    certificate_required_timer(certificate).unwrap()
                        != name,
    ensures
        store_documents_protected_from_deletes(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            bucket_ms,
            after_names,
        ),
{
    reveal(store_request_safe);
    reveal(certificate_matches_request);
    match request {
        StoreReq::Get { .. }
        | StoreReq::GetIfNoneMatch { .. }
        | StoreReq::List { .. }
        | StoreReq::ListPrefixes { .. } => {
            lemma_protected_documents_mono(
                store,
                prefix,
                bucket_ms,
                before_names,
                after_names,
            );
        },
        StoreReq::Put { key, body } => {
            let version = match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(found) => echod_concrete::store::spec_bump(
                    store.entries[found].version,
                ),
                None => 1,
            };
            let added = EntryV { key: key@, body: body@, version };
            match certificate {
                StoreEffectCertificateV::TimerPut {
                    key: timer_key,
                    name,
                } => {
                    lemma_certificate_timer_is_namespace(
                        prefix,
                        bucket_ms,
                        timer_key,
                        name,
                    );
                    lemma_timer_namespace_is_not_document_key(
                        prefix,
                        key@,
                    );
                },
                StoreEffectCertificateV::Other => {},
                _ => assert(false),
            }
            lemma_put_preserves_protected_documents(
                store,
                prefix,
                bucket_ms,
                added,
                before_names,
                after_names,
            );
        },
        StoreReq::Del { key } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(removed) => {
                    lemma_find_result_valid(store.entries, key@, 0);
                    match certificate {
                        StoreEffectCertificateV::TimerDelete {
                            key: timer_key,
                            name,
                        } => {
                            lemma_certificate_timer_is_namespace(
                                prefix,
                                bucket_ms,
                                timer_key,
                                name,
                            );
                            assert(before_names.contains(key@));
                        },
                        StoreEffectCertificateV::Other => {},
                        _ => assert(false),
                    }
                    lemma_remove_preserves_protected_documents(
                        store,
                        prefix,
                        bucket_ms,
                        removed,
                        before_names,
                        after_names,
                    );
                },
                None => {
                    lemma_protected_documents_mono(
                        store,
                        prefix,
                        bucket_ms,
                        before_names,
                        after_names,
                    );
                },
            }
        },
        StoreReq::PutIfNoneMatch { key, body } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(_) => {
                    lemma_protected_documents_mono(
                        store,
                        prefix,
                        bucket_ms,
                        before_names,
                        after_names,
                    );
                },
                None => match certificate {
                    StoreEffectCertificateV::DocumentFull {
                        after,
                        required_timer,
                        ..
                    } => {
                        let added = EntryV {
                            key: key@,
                            body: body@,
                            version: 1,
                        };
                        let provenance = DocumentProvenanceV {
                            full: after,
                            deltas: Seq::empty(),
                            store_version: 1,
                            required_timer,
                        };
                        lemma_full_encoding_has_provenance(
                            prefix,
                            after,
                            1,
                            required_timer,
                        );
                        assert(is_document_key(prefix, added.key));
                        assert(exists|p: DocumentProvenanceV|
                            #[trigger] entry_has_document_provenance(
                                added,
                                prefix,
                                p,
                            )
                            && (provenance_document(p) is Workflow
                                && top_level_pending(
                                    provenance_document(p)->Workflow_0,
                                ) ==> {
                                    &&& p.required_timer is Some
                                    &&& current_origin_timer_name(
                                        prefix,
                                        bucket_ms,
                                        provenance_document(p)->Workflow_0,
                                        p.required_timer.unwrap(),
                                    )
                                    &&& store_contains_empty_key(
                                        store,
                                        p.required_timer.unwrap(),
                                    )
                                    &&& forall|name: Seq<char>|
                                        after_names.contains(name) ==>
                                            p.required_timer.unwrap()
                                                != name
                                })) by {
                            reveal(certificate_required_timer);
                        };
                        lemma_put_preserves_protected_documents(
                            store,
                            prefix,
                            bucket_ms,
                            added,
                            before_names,
                            after_names,
                        );
                    },
                    StoreEffectCertificateV::Other => {
                        assert(!is_document_key(prefix, key@));
                        lemma_put_preserves_protected_documents(
                            store,
                            prefix,
                            bucket_ms,
                            EntryV {
                                key: key@,
                                body: body@,
                                version: 1,
                            },
                            before_names,
                            after_names,
                        );
                    },
                    _ => assert(false),
                },
            }
        },
        StoreReq::PutIfMatch { key, body, etag } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(found) if echod_concrete::store::spec_etag(
                    store.entries[found].body,
                ) == etag => {
                    lemma_find_result_valid(
                        store.entries,
                        key@,
                        0,
                    );
                    match certificate {
                    StoreEffectCertificateV::DocumentFull {
                        after,
                        required_timer,
                        ..
                    } => {
                        let added = EntryV {
                            key: key@,
                            body: body@,
                            version: echod_concrete::store::spec_bump(
                                store.entries[found].version,
                            ),
                        };
                        lemma_full_encoding_has_provenance(
                            prefix,
                            after,
                            added.version,
                            required_timer,
                        );
                        assert(is_document_key(prefix, added.key));
                        assert(exists|p: DocumentProvenanceV|
                            #[trigger] entry_has_document_provenance(
                                added,
                                prefix,
                                p,
                            )
                            && (provenance_document(p) is Workflow
                                && top_level_pending(
                                    provenance_document(p)->Workflow_0,
                                ) ==> {
                                    &&& p.required_timer is Some
                                    &&& current_origin_timer_name(
                                        prefix,
                                        bucket_ms,
                                        provenance_document(p)->Workflow_0,
                                        p.required_timer.unwrap(),
                                    )
                                    &&& store_contains_empty_key(
                                        store,
                                        p.required_timer.unwrap(),
                                    )
                                    &&& forall|name: Seq<char>|
                                        after_names.contains(name) ==>
                                            p.required_timer.unwrap()
                                                != name
                                })) by {
                            reveal(certificate_required_timer);
                        };
                        lemma_put_preserves_protected_documents(
                            store,
                            prefix,
                            bucket_ms,
                            added,
                            before_names,
                            after_names,
                        );
                    },
                        StoreEffectCertificateV::Other => {
                            assert(!is_document_key(prefix, key@));
                            lemma_put_preserves_protected_documents(
                                store,
                                prefix,
                                bucket_ms,
                                EntryV {
                                    key: key@,
                                    body: body@,
                                    version:
                                        echod_concrete::store::spec_bump(
                                            store.entries[found].version,
                                        ),
                                },
                                before_names,
                                after_names,
                            );
                        },
                        _ => assert(false),
                    }
                },
                _ => {
                    lemma_protected_documents_mono(
                        store,
                        prefix,
                        bucket_ms,
                        before_names,
                        after_names,
                    );
                },
            }
        },
        StoreReq::AppIfMatch {
            key,
            offset,
            body,
            etag,
        } => {
            if store.appendable {
                match echod_concrete::store::spec_find(
                    store.entries,
                    key@,
                    0,
                ) {
                    Some(found) if echod_concrete::store::spec_etag(
                        store.entries[found].body,
                    ) == etag
                        && store.entries[found].body.len() == offset => {
                        match certificate {
                            StoreEffectCertificateV::DocumentAppend {
                                before,
                                after,
                                required_timer,
                                ..
                            } => {
                                lemma_find_result_valid(
                                    store.entries,
                                    key@,
                                    0,
                                );
                                let old =
                                    choose|old: DocumentProvenanceV|
                                        entry_has_document_provenance(
                                            store.entries[found],
                                            prefix,
                                            old,
                                        )
                                        && provenance_document(old) == before;
                                let added = EntryV {
                                    key: key@,
                                    body: store.entries[found].body
                                        + body@,
                                    version:
                                        echod_concrete::store::spec_bump(
                                            store.entries[found].version,
                                        ),
                                };
                                let provenance = DocumentProvenanceV {
                                    full: old.full,
                                    deltas: old.deltas.push(
                                        DocumentDeltaV { before, after },
                                    ),
                                    store_version: added.version,
                                    required_timer,
                                };
                                lemma_delta_append_extends_provenance(
                                    store.entries[found],
                                    prefix,
                                    old,
                                    before,
                                    after,
                                    added.version,
                                    required_timer,
                                );
                                assert(is_document_key(
                                    prefix,
                                    added.key,
                                ));
                                assert(exists|p: DocumentProvenanceV|
                                    #[trigger]
                                    entry_has_document_provenance(
                                        added,
                                        prefix,
                                        p,
                                    )
                                    && (provenance_document(p) is Workflow
                                        && top_level_pending(
                                            provenance_document(
                                                p,
                                            )->Workflow_0,
                                        ) ==> {
                                            &&& p.required_timer is Some
                                            &&& current_origin_timer_name(
                                                prefix,
                                                bucket_ms,
                                                provenance_document(
                                                    p,
                                                )->Workflow_0,
                                                p.required_timer.unwrap(),
                                            )
                                            &&& store_contains_empty_key(
                                                store,
                                                p.required_timer.unwrap(),
                                            )
                                            &&& forall|name: Seq<char>|
                                                after_names.contains(name)
                                                ==> p.required_timer.unwrap()
                                                    != name
                                        })) by {
                                    reveal(certificate_required_timer);
                                };
                                lemma_put_preserves_protected_documents(
                                    store,
                                    prefix,
                                    bucket_ms,
                                    added,
                                    before_names,
                                    after_names,
                                );
                            },
                            StoreEffectCertificateV::Other => {
                                assert(!is_document_key(prefix, key@));
                                lemma_put_preserves_protected_documents(
                                    store,
                                    prefix,
                                    bucket_ms,
                                    EntryV {
                                        key: key@,
                                        body: store.entries[found].body
                                            + body@,
                                        version:
                                            echod_concrete::store::spec_bump(
                                                store.entries[found].version,
                                            ),
                                    },
                                    before_names,
                                    after_names,
                                );
                            },
                            _ => assert(false),
                        }
                    },
                    _ => {
                        lemma_protected_documents_mono(
                            store,
                            prefix,
                            bucket_ms,
                            before_names,
                            after_names,
                        );
                    },
                }
            } else {
                lemma_protected_documents_mono(
                    store,
                    prefix,
                    bucket_ms,
                    before_names,
                    after_names,
                );
            }
        },
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_compatible_request_apply_retains_required_timer(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    first_request: StoreReq,
    first_certificate: StoreEffectCertificateV,
    required: Seq<char>,
    second_certificate: StoreEffectCertificateV,
)
    requires
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            first_request.deep_view(),
            first_certificate,
        ),
        store_contains_empty_key(store, required),
        is_timer_namespace_key(prefix, required),
        certificate_put_timer(second_certificate) == Some(required),
        store_certificates_compatible(
            first_certificate,
            second_certificate,
        ),
    ensures
        store_contains_empty_key(
            echod_concrete::store::spec_apply(
                store,
                first_request,
            ).0,
            required,
        ),
{
    reveal(invariant1_store_request_safe);
    reveal(invariant1_certificate_matches_request);
    reveal(certificate_exact_request);
    let next = echod_concrete::store::spec_apply(
        store,
        first_request,
    ).0;
    match first_request {
        StoreReq::Get { .. }
        | StoreReq::GetIfNoneMatch { .. }
        | StoreReq::List { .. }
        | StoreReq::ListPrefixes { .. } => {},
        StoreReq::Put { key, body } => {
            let added = EntryV {
                key: key@,
                body: body@,
                version: match echod_concrete::store::spec_find(
                    store.entries,
                    key@,
                    0,
                ) {
                    Some(found) => echod_concrete::store::spec_bump(
                        store.entries[found].version,
                    ),
                    None => 1,
                },
            };
            match first_certificate {
                StoreEffectCertificateV::TimerPut { .. } => {
                    assert(body@.len() == 0);
                },
                StoreEffectCertificateV::Other => {
                    assert(!is_timer_namespace_key(prefix, key@));
                    assert(key@ != required);
                },
                _ => assert(false),
            }
            lemma_put_retains_empty_key_if_safe(
                store,
                added,
                required,
            );
        },
        StoreReq::Del { key } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                None => {},
                Some(removed) => {
                    lemma_find_result_valid(store.entries, key@, 0);
                    match first_certificate {
                        StoreEffectCertificateV::TimerDelete { .. } => {
                            reveal(store_certificates_compatible);
                            reveal(certificate_deleted_timer);
                            assert(is_timer_namespace_key(prefix, required));
                            assert(key@ != required);
                        },
                        StoreEffectCertificateV::Other => {
                            assert(!is_timer_namespace_key(prefix, key@));
                            assert(key@ != required);
                        },
                        _ => assert(false),
                    }
                    lemma_remove_retains_empty_key_if_distinct(
                        store,
                        removed,
                        required,
                    );
                },
            }
        },
        StoreReq::PutIfNoneMatch { key, body }
        | StoreReq::PutIfMatch { key, body, .. } => {
            match first_certificate {
                StoreEffectCertificateV::DocumentFull { after, .. } => {
                    assert(key@ == document_key(prefix, after));
                    lemma_timer_namespace_is_not_document_key(
                        prefix,
                        required,
                    );
                    assert(key@ != required);
                    let version = match echod_concrete::store::spec_find(
                        store.entries,
                        key@,
                        0,
                    ) {
                        Some(found) => echod_concrete::store::spec_bump(
                            store.entries[found].version,
                        ),
                        None => 1,
                    };
                    lemma_put_retains_empty_key_if_safe(
                        store,
                        EntryV { key: key@, body: body@, version },
                        required,
                    );
                },
                StoreEffectCertificateV::Other => {
                    assert(!is_timer_namespace_key(prefix, key@));
                    assert(key@ != required);
                    let version = match echod_concrete::store::spec_find(
                        store.entries,
                        key@,
                        0,
                    ) {
                        Some(found) => echod_concrete::store::spec_bump(
                            store.entries[found].version,
                        ),
                        None => 1,
                    };
                    lemma_put_retains_empty_key_if_safe(
                        store,
                        EntryV { key: key@, body: body@, version },
                        required,
                    );
                },
                _ => assert(false),
            }
        },
        StoreReq::AppIfMatch {
            key,
            offset,
            body,
            etag,
        } => {
            match first_certificate {
                StoreEffectCertificateV::DocumentAppend { after, .. } => {
                    assert(key@ == document_key(prefix, after));
                    lemma_timer_namespace_is_not_document_key(
                        prefix,
                        required,
                    );
                    assert(key@ != required);
                },
                StoreEffectCertificateV::Other => {
                    assert(!is_timer_namespace_key(prefix, key@));
                    assert(key@ != required);
                },
                _ => assert(false),
            }
            // An append either stutters or replaces only the document key,
            // which is disjoint from the required timer key.
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(found) if store.appendable
                    && echod_concrete::store::spec_etag(
                        store.entries[found].body,
                    ) == etag
                    && store.entries[found].body.len() == offset => {
                    lemma_find_result_valid(store.entries, key@, 0);
                    let added = EntryV {
                        key: key@,
                        body: store.entries[found].body + body@,
                        version: echod_concrete::store::spec_bump(
                            store.entries[found].version,
                        ),
                    };
                    lemma_put_retains_empty_key_if_safe(
                        store,
                        added,
                        required,
                    );
                },
                _ => {},
            }
        },
    }
}

/// `spec_apply` frames an entry whose key is distinct from the key touched by
/// the request. Keeping this StoreReq split independent of certificates avoids
/// unfolding the Store and certificate algebras in the same solver query.
pub(super) proof fn lemma_store_apply_retains_entry_at_distinct_key(
    store: StoreV,
    request: StoreReq,
    index: int,
)
    requires
        0 <= index < store.entries.len(),
        match request {
            StoreReq::Put { key, .. }
            | StoreReq::Del { key }
            | StoreReq::PutIfNoneMatch { key, .. }
            | StoreReq::PutIfMatch { key, .. }
            | StoreReq::AppIfMatch { key, .. } =>
                key@ != store.entries[index].key,
            _ => true,
        },
    ensures
        ({
            let next =
                echod_concrete::store::spec_apply(store, request).0;
            exists|next_index: int|
                0 <= next_index < next.entries.len()
                    && next.entries[next_index] == store.entries[index]
        }),
{
    reveal(echod_concrete::store::spec_apply);
    match request {
        StoreReq::Get { key } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(_) => {},
                None => {},
            }
            assert(echod_concrete::store::spec_apply(store, request).0
                == store);
        },
        StoreReq::GetIfNoneMatch { key, etag } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(found) => {
                    if echod_concrete::store::spec_etag(
                        store.entries[found].body,
                    ) == etag {
                    } else {
                    }
                },
                None => {},
            }
            assert(echod_concrete::store::spec_apply(store, request).0
                == store);
        },
        StoreReq::List { .. }
        | StoreReq::ListPrefixes { .. } => {
            assert(echod_concrete::store::spec_apply(store, request).0
                == store);
        },
        StoreReq::Put { key, body } => {
            let version = match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(found) => echod_concrete::store::spec_bump(
                    store.entries[found].version,
                ),
                None => 1,
            };
            lemma_put_retains_distinct_entry(
                store.entries,
                EntryV { key: key@, body: body@, version },
                index,
            );
            assert(echod_concrete::store::spec_apply(store, request)
                .0.entries == echod_concrete::store::spec_put(
                    store.entries,
                    EntryV { key: key@, body: body@, version },
                ));
        },
        StoreReq::Del { key } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(removed) => {
                    lemma_find_result_valid(store.entries, key@, 0);
                    assert(removed != index);
                    lemma_remove_at_retains_distinct_entry(
                        store.entries,
                        removed,
                        index,
                    );
                    assert(echod_concrete::store::spec_apply(
                        store,
                        request,
                    ).0.entries
                        == echod_concrete::store::spec_remove_at(
                            store.entries,
                            removed,
                        ));
                },
                None => {
                    assert(echod_concrete::store::spec_apply(
                        store,
                        request,
                    ).0 == store);
                },
            }
        },
        StoreReq::PutIfNoneMatch { key, body } => {
            if echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) is None {
                lemma_put_retains_distinct_entry(
                    store.entries,
                    EntryV { key: key@, body: body@, version: 1 },
                    index,
                );
                assert(echod_concrete::store::spec_apply(store, request)
                    .0.entries == echod_concrete::store::spec_put(
                        store.entries,
                        EntryV { key: key@, body: body@, version: 1 },
                    ));
            } else {
                assert(echod_concrete::store::spec_apply(store, request).0
                    == store);
            }
        },
        StoreReq::PutIfMatch { key, body, etag } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(found) if echod_concrete::store::spec_etag(
                    store.entries[found].body,
                ) == etag => {
                    lemma_put_retains_distinct_entry(
                        store.entries,
                        EntryV {
                            key: key@,
                            body: body@,
                            version: echod_concrete::store::spec_bump(
                                store.entries[found].version,
                            ),
                        },
                        index,
                    );
                    assert(echod_concrete::store::spec_apply(
                        store,
                        request,
                    ).0.entries == echod_concrete::store::spec_put(
                        store.entries,
                        EntryV {
                            key: key@,
                            body: body@,
                            version: echod_concrete::store::spec_bump(
                                store.entries[found].version,
                            ),
                        },
                    ));
                },
                _ => {
                    assert(echod_concrete::store::spec_apply(
                        store,
                        request,
                    ).0 == store);
                },
            }
        },
        StoreReq::AppIfMatch {
            key,
            offset,
            body,
            etag,
        } => {
            match echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) {
                Some(found) if store.appendable
                    && echod_concrete::store::spec_etag(
                        store.entries[found].body,
                    ) == etag
                    && store.entries[found].body.len() == offset => {
                    lemma_put_retains_distinct_entry(
                        store.entries,
                        EntryV {
                            key: key@,
                            body: store.entries[found].body + body@,
                            version: echod_concrete::store::spec_bump(
                                store.entries[found].version,
                            ),
                        },
                        index,
                    );
                    assert(echod_concrete::store::spec_apply(
                        store,
                        request,
                    ).0.entries == echod_concrete::store::spec_put(
                        store.entries,
                        EntryV {
                            key: key@,
                            body: store.entries[found].body + body@,
                            version: echod_concrete::store::spec_bump(
                                store.entries[found].version,
                            ),
                        },
                    ));
                },
                _ => {
                    if store.appendable {
                    }
                    assert(echod_concrete::store::spec_apply(
                        store,
                        request,
                    ).0 == store);
                },
            }
        },
    }
}

pub(super) proof fn lemma_store_apply_preserves_first_entry_at_distinct_key(
    store: StoreV,
    request: StoreReq,
    key: Seq<char>,
    found: int,
)
    requires
        echod_concrete::store::spec_find(store.entries, key, 0)
            == Some(found),
        match request {
            StoreReq::Put { key: touched, .. }
            | StoreReq::Del { key: touched }
            | StoreReq::PutIfNoneMatch { key: touched, .. }
            | StoreReq::PutIfMatch { key: touched, .. }
            | StoreReq::AppIfMatch { key: touched, .. } =>
                touched@ != key,
            _ => true,
        },
    ensures
        ({
            let next =
                echod_concrete::store::spec_apply(store, request).0;
            let next_found =
                echod_concrete::store::spec_find(next.entries, key, 0)
                    .unwrap();
            &&& echod_concrete::store::spec_find(
                next.entries,
                key,
                0,
            ) is Some
            &&& next.entries[next_found] == store.entries[found]
        }),
{
    reveal(echod_concrete::store::spec_apply);
    match request {
        StoreReq::Get { .. }
        | StoreReq::GetIfNoneMatch { .. }
        | StoreReq::List { .. }
        | StoreReq::ListPrefixes { .. } => {},
        StoreReq::Put { key: touched, body } => {
            let added = EntryV {
                key: touched@,
                body: body@,
                version: match echod_concrete::store::spec_find(
                    store.entries,
                    touched@,
                    0,
                ) {
                    Some(i) => echod_concrete::store::spec_bump(
                        store.entries[i].version,
                    ),
                    None => 1,
                },
            };
            lemma_put_preserves_first_other_key(
                store.entries,
                added,
                key,
                found,
            );
        },
        StoreReq::Del { key: touched } => {
            match echod_concrete::store::spec_find(
                store.entries,
                touched@,
                0,
            ) {
                Some(removed) => {
                    lemma_find_result_valid(
                        store.entries,
                        touched@,
                        0,
                    );
                    lemma_remove_at_preserves_first_other_key(
                        store.entries,
                        removed,
                        key,
                        found,
                    );
                },
                None => {},
            }
        },
        StoreReq::PutIfNoneMatch { key: touched, body } => {
            if echod_concrete::store::spec_find(
                store.entries,
                touched@,
                0,
            ) is None {
                let added = EntryV {
                    key: touched@,
                    body: body@,
                    version: 1,
                };
                lemma_put_preserves_first_other_key(
                    store.entries,
                    added,
                    key,
                    found,
                );
            }
        },
        StoreReq::PutIfMatch {
            key: touched,
            body,
            etag,
        } => {
            match echod_concrete::store::spec_find(
                store.entries,
                touched@,
                0,
            ) {
                Some(i)
                    if echod_concrete::store::spec_etag(
                        store.entries[i].body,
                    ) == etag => {
                        lemma_find_result_valid(
                            store.entries,
                            touched@,
                            0,
                        );
                        let added = EntryV {
                            key: touched@,
                            body: body@,
                            version:
                                echod_concrete::store::spec_bump(
                                    store.entries[i].version,
                                ),
                        };
                        lemma_put_preserves_first_other_key(
                            store.entries,
                            added,
                            key,
                            found,
                        );
                    },
                _ => {},
            }
        },
        StoreReq::AppIfMatch {
            key: touched,
            offset,
            body,
            etag,
        } => {
            if store.appendable {
                match echod_concrete::store::spec_find(
                    store.entries,
                    touched@,
                    0,
                ) {
                    Some(i)
                        if echod_concrete::store::spec_etag(
                            store.entries[i].body,
                        ) == etag
                            && store.entries[i].body.len() == offset => {
                            lemma_find_result_valid(
                                store.entries,
                                touched@,
                                0,
                            );
                            let added = EntryV {
                                key: touched@,
                                body: store.entries[i].body + body@,
                                version:
                                    echod_concrete::store::spec_bump(
                                        store.entries[i].version,
                                    ),
                            };
                            lemma_put_preserves_first_other_key(
                                store.entries,
                                added,
                                key,
                                found,
                            );
                        },
                    _ => {},
                }
            }
        },
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_compatible_request_apply_retains_document_provenance(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    first_request: StoreReq,
    first_certificate: StoreEffectCertificateV,
    second_certificate: StoreEffectCertificateV,
    index: int,
    provenance: DocumentProvenanceV,
)
    requires
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            first_request.deep_view(),
            first_certificate,
        ),
        0 <= index < store.entries.len(),
        entry_has_document_provenance(
            store.entries[index],
            prefix,
            provenance,
        ),
        certificate_written_document(second_certificate) is Some,
        document_lane(
            certificate_written_document(second_certificate).unwrap(),
        ) == document_lane(provenance_document(provenance)),
        store_certificates_compatible(
            first_certificate,
            second_certificate,
        ),
    ensures
        ({
            let next = echod_concrete::store::spec_apply(
                store,
                first_request,
            ).0;
            exists|next_index: int|
                0 <= next_index < next.entries.len()
                    && entry_has_document_provenance(
                        next.entries[next_index],
                        prefix,
                        provenance,
                    )
        }),
        match first_request {
            StoreReq::Put { key, .. }
            | StoreReq::Del { key }
            | StoreReq::PutIfNoneMatch { key, .. }
            | StoreReq::PutIfMatch { key, .. }
            | StoreReq::AppIfMatch { key, .. } =>
                key@ != store.entries[index].key,
            _ => true,
        },
{
    reveal(invariant1_store_request_safe);
    reveal(invariant1_certificate_matches_request);
    reveal(certificate_exact_request);
    reveal(store_certificates_compatible);
    reveal(certificate_written_document);
    let old = store.entries[index];
    let target = provenance_document(provenance);
    assert(old.key == document_key(prefix, target));
    match first_request {
        StoreReq::Get { .. }
        | StoreReq::GetIfNoneMatch { .. }
        | StoreReq::List { .. }
        | StoreReq::ListPrefixes { .. } => {},
        StoreReq::Put { key, body } => {
            match first_certificate {
                StoreEffectCertificateV::TimerPut { .. } => {
                    lemma_certificate_timer_is_namespace(
                        prefix,
                        bucket_ms,
                        first_certificate->TimerPut_key,
                        key@,
                    );
                    lemma_timer_namespace_is_not_document_key(
                        prefix,
                        key@,
                    );
                },
                StoreEffectCertificateV::Other => {},
                _ => assert(false),
            }
            assert(key@ != old.key);
        },
        StoreReq::Del { key } => {
            match first_certificate {
                StoreEffectCertificateV::TimerDelete { .. } => {
                    lemma_certificate_timer_is_namespace(
                        prefix,
                        bucket_ms,
                        first_certificate->TimerDelete_key,
                        key@,
                    );
                    lemma_timer_namespace_is_not_document_key(
                        prefix,
                        key@,
                    );
                },
                StoreEffectCertificateV::Other => {},
                _ => assert(false),
            }
            assert(key@ != old.key);
        },
        StoreReq::PutIfNoneMatch { key, body }
        | StoreReq::PutIfMatch { key, body, .. } => {
            match first_certificate {
                StoreEffectCertificateV::DocumentFull { after: written, .. } => {
                    assert(certificate_written_document(first_certificate)
                        == Some(written));
                    assert(document_lane(written) != document_lane(target));
                    lemma_distinct_document_lanes_have_distinct_document_keys(
                        prefix,
                        written,
                        target,
                    );
                },
                StoreEffectCertificateV::Other => {
                    assert(!is_document_key(prefix, key@));
                },
                _ => assert(false),
            }
            assert(key@ != old.key);
        },
        StoreReq::AppIfMatch {
            key,
            offset,
            body,
            etag,
        } => {
            match first_certificate {
                StoreEffectCertificateV::DocumentAppend {
                    after: written,
                    ..
                } => {
                    assert(certificate_written_document(first_certificate)
                        == Some(written));
                    assert(document_lane(written) != document_lane(target));
                    lemma_distinct_document_lanes_have_distinct_document_keys(
                        prefix,
                        written,
                        target,
                    );
                },
                StoreEffectCertificateV::Other => {
                    assert(!is_document_key(prefix, key@));
                },
                _ => assert(false),
            }
            assert(key@ != old.key);
        },
    }
    lemma_store_apply_retains_entry_at_distinct_key(
        store,
        first_request,
        index,
    );
    let next =
        echod_concrete::store::spec_apply(store, first_request).0;
    let next_index = choose|next_index: int|
        0 <= next_index < next.entries.len()
            && next.entries[next_index] == old;
    assert(entry_has_document_provenance(
        next.entries[next_index],
        prefix,
        provenance,
    ));
}

pub(super) proof fn lemma_distinct_loaded_lane_certificate_is_compatible(
    certificate: StoreEffectCertificateV,
    loaded: crate::document::LoadedSpec,
)
    requires
        certificate_written_document(certificate) is Some,
        document_lane(loaded.document)
            != document_lane(
                certificate_written_document(certificate).unwrap(),
            ),
    ensures
        store_certificates_compatible(
            certificate,
            StoreEffectCertificateV::DocumentFull {
                before: loaded.document,
                after: loaded.document,
                required_timer: None,
                change_count: 1,
                bytes: loaded.bytes,
            },
        ),
{
    reveal(store_certificates_compatible);
    reveal(certificate_written_document);
    reveal(certificate_required_timer);
    reveal(certificate_deleted_timer);
    reveal(certificate_put_timer);
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_nonwriting_certified_apply_frames_document_entry(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
    found: int,
    provenance: DocumentProvenanceV,
)
    requires
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
        certificate_written_document(certificate) is None,
        0 <= found < store.entries.len(),
        echod_concrete::store::spec_find(
            store.entries,
            store.entries[found].key,
            0,
        ) == Some(found),
        entry_has_document_provenance(
            store.entries[found],
            prefix,
            provenance,
        ),
    ensures
        ({
            let key = store.entries[found].key;
            let next =
                echod_concrete::store::spec_apply(store, request).0;
            let next_found =
                echod_concrete::store::spec_find(next.entries, key, 0)
                    .unwrap();
            &&& echod_concrete::store::spec_find(
                next.entries,
                key,
                0,
            ) is Some
            &&& next.entries[next_found] == store.entries[found]
        }),
{
    reveal(invariant1_store_request_safe);
    reveal(invariant1_certificate_matches_request);
    reveal(certificate_exact_request);
    reveal(certificate_written_document);
    let key = store.entries[found].key;
    assert(key == document_key(prefix, provenance_document(provenance)));
    match request {
        StoreReq::Get { .. }
        | StoreReq::GetIfNoneMatch { .. }
        | StoreReq::List { .. }
        | StoreReq::ListPrefixes { .. } => {},
        StoreReq::Put { key: touched, .. }
        | StoreReq::Del { key: touched }
        | StoreReq::PutIfNoneMatch { key: touched, .. }
        | StoreReq::PutIfMatch { key: touched, .. }
        | StoreReq::AppIfMatch { key: touched, .. } => {
            match certificate {
                StoreEffectCertificateV::TimerPut { key: timer, .. }
                | StoreEffectCertificateV::TimerDelete {
                    key: timer,
                    ..
                } => {
                    lemma_certificate_timer_is_namespace(
                        prefix,
                        bucket_ms,
                        timer,
                        touched@,
                    );
                    lemma_timer_namespace_is_not_document_key(
                        prefix,
                        touched@,
                    );
                },
                StoreEffectCertificateV::Other => {
                    assert(!is_document_key(prefix, touched@));
                    reveal(is_document_key);
                },
                _ => assert(false),
            }
            assert(touched@ != key);
        },
    }
    lemma_store_apply_preserves_first_entry_at_distinct_key(
        store,
        request,
        key,
        found,
    );
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_certified_apply_frames_loaded_physical_entry(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
    loaded: crate::document::LoadedSpec,
)
    requires
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
        loaded_append_certificate(store, prefix, loaded),
        certificate_written_document(certificate) is Some
            && loaded.append_certified ==>
            document_lane(loaded.document)
                != document_lane(
                    certificate_written_document(certificate).unwrap(),
                ),
    ensures
        loaded.append_certified ==> ({
            let next = echod_concrete::store::spec_apply(store, request).0;
            let key = document_key(prefix, loaded.document);
            &&& echod_concrete::store::spec_find(store.entries, key, 0)
                is Some
            &&& echod_concrete::store::spec_find(next.entries, key, 0)
                is Some
            &&& next.entries[
                    echod_concrete::store::spec_find(
                        next.entries,
                        key,
                        0,
                    ).unwrap()
                ]
                == store.entries[
                    echod_concrete::store::spec_find(
                        store.entries,
                        key,
                        0,
                    ).unwrap()
                ]
        }),
{
    if loaded.append_certified {
        reveal(loaded_append_certificate);
        let found = echod_concrete::store::spec_find(
            store.entries,
            document_key(prefix, loaded.document),
            0,
        ).unwrap();
        lemma_find_result_valid(
            store.entries,
            document_key(prefix, loaded.document),
            0,
        );
        let provenance = choose|provenance: DocumentProvenanceV|
            entry_has_document_provenance(
                store.entries[found],
                prefix,
                provenance,
            )
                && provenance_document(provenance) == loaded.document
                && provenance_change_count(provenance.deltas)
                    == loaded.change_count
                && store.entries[found].body.len() == loaded.bytes;
        let retained_certificate =
            StoreEffectCertificateV::DocumentFull {
                before: loaded.document,
                after: loaded.document,
                required_timer: None,
                change_count: 1,
                bytes: loaded.bytes,
            };
        if certificate_written_document(certificate) is Some {
            lemma_distinct_loaded_lane_certificate_is_compatible(
                certificate,
                loaded,
            );
            lemma_compatible_request_apply_retains_document_provenance(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
                retained_certificate,
                found,
                provenance,
            );
            assert(match request {
                StoreReq::Put { key, .. }
                | StoreReq::Del { key }
                | StoreReq::PutIfNoneMatch { key, .. }
                | StoreReq::PutIfMatch { key, .. }
                | StoreReq::AppIfMatch { key, .. } =>
                    key@ != store.entries[found].key,
                _ => true,
            });
            assert(store.entries[found].key
                == document_key(prefix, loaded.document));
            lemma_store_apply_preserves_first_entry_at_distinct_key(
                store,
                request,
                document_key(prefix, loaded.document),
                found,
            );
        } else {
            lemma_nonwriting_certified_apply_frames_document_entry(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
                found,
                provenance,
            );
        }
        let next = echod_concrete::store::spec_apply(store, request).0;
        let next_found = echod_concrete::store::spec_find(
            next.entries,
            document_key(prefix, loaded.document),
            0,
        ).unwrap();
        assert(next.entries[next_found] == store.entries[found]);
        assert(entry_has_document_provenance(
            next.entries[next_found],
            prefix,
            provenance,
        ));
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_certified_apply_frames_loaded_append_certificate(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
    loaded: crate::document::LoadedSpec,
)
    requires
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
        loaded_append_certificate(store, prefix, loaded),
        certificate_written_document(certificate) is Some
            && loaded.append_certified ==>
            document_lane(loaded.document)
                != document_lane(
                    certificate_written_document(certificate).unwrap(),
                ),
    ensures
        loaded_append_certificate(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            loaded,
        ),
        loaded.append_certified ==> ({
            let next = echod_concrete::store::spec_apply(store, request).0;
            let key = document_key(prefix, loaded.document);
            &&& echod_concrete::store::spec_find(store.entries, key, 0)
                is Some
            &&& echod_concrete::store::spec_find(next.entries, key, 0)
                is Some
            &&& next.entries[
                    echod_concrete::store::spec_find(
                        next.entries,
                        key,
                        0,
                    ).unwrap()
                ].body
                == store.entries[
                    echod_concrete::store::spec_find(
                        store.entries,
                        key,
                        0,
                    ).unwrap()
                ].body
        }),
{
    lemma_certified_apply_frames_loaded_physical_entry(
        store,
        prefix,
        bucket_ms,
        request,
        certificate,
        loaded,
    );
    if loaded.append_certified {
        reveal(loaded_append_certificate);
        let found = echod_concrete::store::spec_find(
            store.entries,
            document_key(prefix, loaded.document),
            0,
        ).unwrap();
        let provenance = choose|provenance: DocumentProvenanceV|
            entry_has_document_provenance(
                store.entries[found],
                prefix,
                provenance,
            )
                && provenance_document(provenance) == loaded.document
                && provenance_change_count(provenance.deltas)
                    == loaded.change_count
                && store.entries[found].body.len() == loaded.bytes;
        let next = echod_concrete::store::spec_apply(store, request).0;
        let next_found = echod_concrete::store::spec_find(
            next.entries,
            document_key(prefix, loaded.document),
            0,
        ).unwrap();
        assert(next.entries[next_found] == store.entries[found]);
        assert(entry_has_document_provenance(
            next.entries[next_found],
            prefix,
            provenance,
        ));
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_certified_apply_frames_cached_append_certificate(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
    cached: crate::cache::CachedSpec,
)
    requires
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
        cached_append_certificate(store, prefix, cached),
        certificate_written_document(certificate) is Some
            && cached.loaded.append_certified ==>
            document_lane(cached.loaded.document)
                != document_lane(
                    certificate_written_document(certificate).unwrap(),
                ),
    ensures
        cached_append_certificate(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            cached,
        ),
{
    lemma_cached_append_certificate_implies_loaded(store, prefix, cached);
    lemma_certified_apply_frames_loaded_append_certificate(
        store,
        prefix,
        bucket_ms,
        request,
        certificate,
        cached.loaded,
    );
    reveal(cached_append_certificate);
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_active_document_write_differs_from_owned_lane(
    core: S,
    op: u64,
    fid: u64,
    lane: Seq<char>,
)
    requires
        production_core_control_body(core),
        active_operation_certificates_match_flights(core),
        core.ops.contains_key(op),
        certificate_written_document(core.store_certificates[op]) is Some,
        core.flights.inflight.contains_key(fid),
        core.flights.slots.contains_key(lane),
        core.flights.slots[lane].busy == Some(fid),
        core.flights.inflight[fid].phase.expects() != Some(op),
    ensures
        document_lane(
            certificate_written_document(
                core.store_certificates[op],
            ).unwrap(),
        ) != lane,
{
    reveal(production_core_control_body);
    reveal(noncommit_certificates_are_other);
    reveal(active_flight_owners_match_phase);
    reveal(active_operation_certificates_match_flights);
    reveal(certificate_written_document);
    reveal(certificate_lane_name);
    match core.ops[op] {
        Owner::Flight(owner) => {
            if document_lane(
                certificate_written_document(
                    core.store_certificates[op],
                ).unwrap(),
            ) == lane {
                assert(core.flights.slots[lane].busy == Some(owner));
                assert(owner == fid);
                assert(false);
            }
        },
        _ => assert(false),
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_active_document_write_differs_from_detached_owned_lane(
    core: S,
    op: u64,
    fid: u64,
    lane: Seq<char>,
)
    requires
        production_core_control_body(core),
        retained_commit_provenance(core),
        core.ops.contains_key(op),
        certificate_written_document(core.store_certificates[op]) is Some,
        !core.flights.inflight.contains_key(fid),
        core.flights.slots.contains_key(lane),
        core.flights.slots[lane].busy == Some(fid),
    ensures
        document_lane(
            certificate_written_document(
                core.store_certificates[op],
            ).unwrap(),
        ) != lane,
{
    lemma_retained_control_implies_active_operation_certificates(core);
    reveal(production_core_control_body);
    reveal(noncommit_certificates_are_other);
    reveal(active_flight_owners_match_phase);
    reveal(active_operation_certificates_match_flights);
    reveal(certificate_written_document);
    reveal(certificate_lane_name);
    match core.ops[op] {
        Owner::Flight(owner) => {
            if document_lane(
                certificate_written_document(
                    core.store_certificates[op],
                ).unwrap(),
            ) == lane {
                assert(core.flights.slots[lane].busy == Some(owner));
                assert(owner == fid);
                assert(core.flights.inflight.contains_key(fid));
                assert(false);
            }
        },
        _ => assert(false),
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_active_document_write_differs_from_noncommit_owned_lane(
    core: S,
    op: u64,
    fid: u64,
    lane: Seq<char>,
)
    requires
        production_core_control_body(core),
        active_operation_certificates_match_flights(core),
        core.ops.contains_key(op),
        certificate_written_document(core.store_certificates[op]) is Some,
        core.flights.inflight.contains_key(fid),
        core.flights.slots.contains_key(lane),
        core.flights.slots[lane].busy == Some(fid),
        match core.flights.inflight[fid].phase {
            crate::handler_docs::PhaseSpec::Origin { .. }
            | crate::handler_docs::PhaseSpec::Schedule { .. }
            | crate::handler_docs::PhaseSpec::FireIdle { .. }
            | crate::handler_docs::PhaseSpec::FireOrigin { .. }
            | crate::handler_docs::PhaseSpec::FireSchedule { .. } =>
                false,
            _ => true,
        },
    ensures
        document_lane(
            certificate_written_document(
                core.store_certificates[op],
            ).unwrap(),
        ) != lane,
{
    reveal(production_core_control_body);
    reveal(noncommit_certificates_are_other);
    reveal(active_operation_certificates_match_flights);
    reveal(certificate_written_document);
    reveal(certificate_lane_name);
    match core.ops[op] {
        Owner::Flight(owner) => {
            if document_lane(
                certificate_written_document(
                    core.store_certificates[op],
                ).unwrap(),
            ) == lane {
                assert(core.flights.slots[lane].busy == Some(owner));
                assert(owner == fid);
                assert(core.store_certificates[op]
                    == StoreEffectCertificateV::Other);
                assert(false);
            }
        },
        _ => assert(false),
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_nonwriting_commit_does_not_expect_document_write(
    core: S,
    fid: u64,
    target: crate::target::TargetSpec,
    commit: crate::handler_docs::CommittingSpec,
    op: u64,
)
    requires
        commit_attachable_provenance(core, fid, target, commit),
        core.ops.contains_key(op),
        certificate_written_document(core.store_certificates[op]) is Some,
        commit.seq.step is Start || commit.seq.step is PuttingKey,
    ensures
        commit.expects() != Some(op),
{
    reveal(commit_attachable_provenance);
    reveal(commit_candidate_provenance);
    reveal(commit_static_provenance);
    reveal(commit_issued_phase_provenance);
    reveal(commit_issued_operation_provenance);
    reveal(certificate_belongs_to_commit);
    reveal(certificate_written_document);
    if commit.expects() == Some(op) {
        match commit.issued {
            Some(crate::handler_docs::IssuedSpec::Write { .. }) => {
                assert(commit.seq.step is Writing);
                assert(false);
            },
            Some(crate::handler_docs::IssuedSpec::Key { .. }) => {
                assert(core.store_certificates[op] is TimerPut
                    || core.store_certificates[op] is TimerDelete);
                assert(false);
            },
            None => assert(false),
        }
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_certified_apply_frames_flight_append_certificates(
    store: StoreV,
    core: S,
    request: StoreReq,
    op: u64,
    fid: u64,
)
    requires
        production_core_control_body(core),
        retained_commit_provenance(core),
        active_operation_certificates_match_flights(core),
        core_retained_append_certificates(store, core),
        core.ops.contains_key(op),
        invariant1_store_request_safe(
            store,
            core.keys.prefix,
            core.keys.bucket_ms,
            request.deep_view(),
            core.store_certificates[op],
        ),
        certificate_written_document(core.store_certificates[op]) is Some,
        core.flights.inflight.contains_key(fid),
    ensures
        phase_append_certificates(
            echod_concrete::store::spec_apply(store, request).0,
            core.keys.prefix,
            core.flights.inflight[fid].phase,
        ),
{
    let certificate = core.store_certificates[op];
    let flight = core.flights.inflight[fid];
    let primary = crate::target::spec_name(flight.target);
    reveal(retained_commit_provenance);
    reveal(core_retained_append_certificates);
    assert(phase_append_certificates(
        store,
        core.keys.prefix,
        flight.phase,
    ));
    match flight.phase {
        crate::handler_docs::PhaseSpec::Idle
        | crate::handler_docs::PhaseSpec::FireLoadingSchedule { .. } => {},
        crate::handler_docs::PhaseSpec::Loading {
            revalidating: Some(cached),
            ..
        } => {
            reveal(flight_control_provenance);
            match flight.target {
                crate::target::TargetSpec::Origin(origin) => {
                    lemma_cached_origin_document_lane_matches_target(
                        origin,
                        cached,
                    );
                },
                crate::target::TargetSpec::Schedule(_) => assert(false),
            }
            lemma_active_document_write_differs_from_noncommit_owned_lane(
                core,
                op,
                fid,
                primary,
            );
            lemma_certified_apply_frames_loaded_append_certificate(
                store,
                core.keys.prefix,
                core.keys.bucket_ms,
                request,
                certificate,
                cached.loaded,
            );
        },
        crate::handler_docs::PhaseSpec::Loading {
            revalidating: None,
            ..
        } => {},
        crate::handler_docs::PhaseSpec::Origin { commit, .. }
        | crate::handler_docs::PhaseSpec::Schedule { commit, .. }
        | crate::handler_docs::PhaseSpec::FireIdle { commit }
        | crate::handler_docs::PhaseSpec::FireSchedule { commit } => {
            reveal(phase_commit_provenance);
            reveal(commit_provenance);
            if commit.seq.step is Start
                || commit.seq.step is PuttingKey
            {
                assert(commit_attachable_provenance(
                    core,
                    fid,
                    flight.target,
                    commit,
                ));
                lemma_commit_candidate_loaded_lane_matches_target(
                    core,
                    fid,
                    flight.target,
                    commit,
                );
                lemma_nonwriting_commit_does_not_expect_document_write(
                    core,
                    fid,
                    flight.target,
                    commit,
                    op,
                );
                assert(flight.phase.expects() == commit.expects());
                lemma_active_document_write_differs_from_owned_lane(
                    core,
                    op,
                    fid,
                    primary,
                );
                lemma_certified_apply_frames_loaded_append_certificate(
                    store,
                    core.keys.prefix,
                    core.keys.bucket_ms,
                    request,
                    certificate,
                    commit.w.loaded,
                );
            }
        },
        crate::handler_docs::PhaseSpec::FireWaitingOrigin(ctx) => {
            reveal(flight_submission_provenance);
            reveal(submission_provenance);
            reveal(flight_control_provenance);
            reveal(fire_context_provenance);
            match flight.work {
                crate::handler_docs::WorkSpec::Fire {
                    schedule,
                    ..
                } => {
                    lemma_working_document_lane_matches_target(
                        core.keys.prefix,
                        ctx.ws,
                        crate::target::TargetSpec::Schedule(schedule),
                    );
                },
                _ => assert(false),
            }
            lemma_active_document_write_differs_from_noncommit_owned_lane(
                core,
                op,
                fid,
                primary,
            );
            lemma_certified_apply_frames_loaded_append_certificate(
                store,
                core.keys.prefix,
                core.keys.bucket_ms,
                request,
                certificate,
                ctx.ws.loaded,
            );
        },
        crate::handler_docs::PhaseSpec::FireLoadingOrigin {
            revalidating,
            ctx,
            ..
        } => {
            reveal(flight_submission_provenance);
            reveal(submission_provenance);
            reveal(flight_control_provenance);
            reveal(fire_context_provenance);
            match flight.work {
                crate::handler_docs::WorkSpec::Fire {
                    schedule,
                    ..
                } => {
                    lemma_working_document_lane_matches_target(
                        core.keys.prefix,
                        ctx.ws,
                        crate::target::TargetSpec::Schedule(schedule),
                    );
                },
                _ => assert(false),
            }
            lemma_active_document_write_differs_from_noncommit_owned_lane(
                core,
                op,
                fid,
                primary,
            );
            lemma_certified_apply_frames_loaded_append_certificate(
                store,
                core.keys.prefix,
                core.keys.bucket_ms,
                request,
                certificate,
                ctx.ws.loaded,
            );
            match revalidating {
                Some(cached) => {
                    let secondary = crate::target::spec_name(
                        crate::target::TargetSpec::Origin(ctx.origin),
                    );
                    lemma_cached_origin_document_lane_matches_target(
                        ctx.origin,
                        cached,
                    );
                    lemma_active_document_write_differs_from_noncommit_owned_lane(
                        core,
                        op,
                        fid,
                        secondary,
                    );
                    lemma_certified_apply_frames_loaded_append_certificate(
                        store,
                        core.keys.prefix,
                        core.keys.bucket_ms,
                        request,
                        certificate,
                        cached.loaded,
                    );
                },
                None => {},
            }
        },
        crate::handler_docs::PhaseSpec::FireOrigin {
            commit,
            ctx,
            ..
        } => {
            reveal(phase_commit_provenance);
            reveal(commit_provenance);
            let secondary = crate::target::spec_name(
                crate::target::TargetSpec::Origin(ctx.origin),
            );
            assert(commit_attachable_provenance(
                core,
                fid,
                crate::target::TargetSpec::Origin(ctx.origin),
                commit,
            ));
            if commit.seq.step is Start
                || commit.seq.step is PuttingKey
            {
                lemma_commit_candidate_loaded_lane_matches_target(
                    core,
                    fid,
                    crate::target::TargetSpec::Origin(ctx.origin),
                    commit,
                );
                lemma_nonwriting_commit_does_not_expect_document_write(
                    core,
                    fid,
                    crate::target::TargetSpec::Origin(ctx.origin),
                    commit,
                    op,
                );
                assert(flight.phase.expects() == commit.expects());
                lemma_active_document_write_differs_from_owned_lane(
                    core,
                    op,
                    fid,
                    secondary,
                );
                lemma_certified_apply_frames_loaded_append_certificate(
                    store,
                    core.keys.prefix,
                    core.keys.bucket_ms,
                    request,
                    certificate,
                    commit.w.loaded,
                );
            }
            reveal(flight_submission_provenance);
            reveal(submission_provenance);
            reveal(flight_control_provenance);
            reveal(fire_context_provenance);
            match flight.work {
                crate::handler_docs::WorkSpec::Fire {
                    schedule,
                    ..
                } => {
                    lemma_working_document_lane_matches_target(
                        core.keys.prefix,
                        ctx.ws,
                        crate::target::TargetSpec::Schedule(schedule),
                    );
                    if flight.phase.expects() == Some(op) {
                        reveal(commit_attachable_provenance);
                        reveal(certificate_lane_name);
                        reveal(certificate_written_document);
                        lemma_origin_and_schedule_lanes_are_distinct(
                            ctx.origin,
                            schedule,
                        );
                    } else {
                        lemma_active_document_write_differs_from_owned_lane(
                            core,
                            op,
                            fid,
                            primary,
                        );
                    }
                },
                _ => assert(false),
            }
            lemma_certified_apply_frames_loaded_append_certificate(
                store,
                core.keys.prefix,
                core.keys.bucket_ms,
                request,
                certificate,
                ctx.ws.loaded,
            );
        },
    }
    reveal(phase_append_certificates);
    reveal(commit_loaded_append_certificate);
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_non_document_apply_frames_phase_append_certificates(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
    phase: crate::handler_docs::PhaseSpec,
)
    requires
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
        certificate_written_document(certificate) is None,
        phase_append_certificates(store, prefix, phase),
    ensures
        phase_append_certificates(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            phase,
        ),
{
    match phase {
        crate::handler_docs::PhaseSpec::Idle
        | crate::handler_docs::PhaseSpec::FireLoadingSchedule { .. } => {},
        crate::handler_docs::PhaseSpec::Loading {
            revalidating: Some(cached),
            ..
        } => {
            lemma_certified_apply_frames_loaded_append_certificate(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
                cached.loaded,
            );
        },
        crate::handler_docs::PhaseSpec::Loading {
            revalidating: None,
            ..
        } => {},
        crate::handler_docs::PhaseSpec::Origin { commit, .. }
        | crate::handler_docs::PhaseSpec::Schedule { commit, .. }
        | crate::handler_docs::PhaseSpec::FireIdle { commit }
        | crate::handler_docs::PhaseSpec::FireSchedule { commit } => {
            if commit.seq.step is Start
                || commit.seq.step is PuttingKey
            {
                lemma_certified_apply_frames_loaded_append_certificate(
                    store,
                    prefix,
                    bucket_ms,
                    request,
                    certificate,
                    commit.w.loaded,
                );
            }
        },
        crate::handler_docs::PhaseSpec::FireWaitingOrigin(ctx) => {
            lemma_certified_apply_frames_loaded_append_certificate(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
                ctx.ws.loaded,
            );
        },
        crate::handler_docs::PhaseSpec::FireLoadingOrigin {
            revalidating,
            ctx,
            ..
        } => {
            lemma_certified_apply_frames_loaded_append_certificate(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
                ctx.ws.loaded,
            );
            match revalidating {
                Some(cached) => {
                    lemma_certified_apply_frames_loaded_append_certificate(
                        store,
                        prefix,
                        bucket_ms,
                        request,
                        certificate,
                        cached.loaded,
                    );
                },
                None => {},
            }
        },
        crate::handler_docs::PhaseSpec::FireOrigin {
            commit,
            ctx,
            ..
        } => {
            if commit.seq.step is Start
                || commit.seq.step is PuttingKey
            {
                lemma_certified_apply_frames_loaded_append_certificate(
                    store,
                    prefix,
                    bucket_ms,
                    request,
                    certificate,
                    commit.w.loaded,
                );
            }
            lemma_certified_apply_frames_loaded_append_certificate(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
                ctx.ws.loaded,
            );
        },
    }
    reveal(phase_append_certificates);
    reveal(commit_loaded_append_certificate);
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_compatible_apply_preserves_append_request_safety(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
    pending_request: StoreReq,
    pending_certificate: StoreEffectCertificateV,
)
    requires
        pending_certificate is DocumentAppend,
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            pending_request.deep_view(),
            pending_certificate,
        ),
        store_certificates_compatible(certificate, pending_certificate),
    ensures
        invariant1_store_request_safe(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            bucket_ms,
            pending_request.deep_view(),
            pending_certificate,
        ),
{
    reveal(invariant1_store_request_safe);
    reveal(invariant1_certificate_matches_request);
    match pending_request {
        StoreReq::AppIfMatch { key, .. } => {
            let found = echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ).unwrap();
            lemma_find_result_valid(store.entries, key@, 0);
            let provenance = choose|provenance: DocumentProvenanceV|
                entry_has_document_provenance(
                    store.entries[found],
                    prefix,
                    provenance,
                )
                && provenance_document(provenance)
                    == pending_certificate->DocumentAppend_before;
            lemma_same_document_family_and_name_have_same_lane(
                pending_certificate->DocumentAppend_before,
                pending_certificate->DocumentAppend_after,
            );
            reveal(certificate_written_document);
            lemma_compatible_request_apply_retains_document_provenance(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
                pending_certificate,
                found,
                provenance,
            );
            lemma_store_apply_preserves_first_entry_at_distinct_key(
                store,
                request,
                key@,
                found,
            );
            let next =
                echod_concrete::store::spec_apply(store, request).0;
            let next_found = echod_concrete::store::spec_find(
                next.entries,
                key@,
                0,
            ).unwrap();
            lemma_find_result_valid(next.entries, key@, 0);
            assert(next.entries[next_found] == store.entries[found]);
            assert(entry_has_document_provenance(
                next.entries[next_found],
                prefix,
                provenance,
            ));
        },
        _ => assert(false),
    }
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_compatible_apply_preserves_full_request_safety(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
    pending_request: StoreReq,
    pending_certificate: StoreEffectCertificateV,
)
    requires
        pending_certificate is DocumentFull,
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            pending_request.deep_view(),
            pending_certificate,
        ),
        store_certificates_compatible(certificate, pending_certificate),
    ensures
        invariant1_store_request_safe(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            bucket_ms,
            pending_request.deep_view(),
            pending_certificate,
        ),
{
    reveal(invariant1_store_request_safe);
}

#[verifier::spinoff_prover]
pub(super) proof fn lemma_compatible_store_apply_preserves_response_ready(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    first_request: StoreReq,
    first_certificate: StoreEffectCertificateV,
    response: echod_concrete::store::StoreRes,
    second_certificate: StoreEffectCertificateV,
)
    requires
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            first_request.deep_view(),
            first_certificate,
        ),
        store_certificates_compatible(
            first_certificate,
            second_certificate,
        ),
        response_certificate_ready(
            store,
            prefix,
            response,
            second_certificate,
        ),
    ensures
        response_certificate_ready(
            echod_concrete::store::spec_apply(
                store,
                first_request,
            ).0,
            prefix,
            response,
            second_certificate,
        ),
{
    reveal(response_certificate_ready);
    match second_certificate {
        StoreEffectCertificateV::TimerPut { key, name } => {
            match response {
                echod_concrete::store::StoreRes::Put {
                    result: Ok(()),
                } => {
                    lemma_compatible_request_apply_retains_required_timer(
                        store,
                        prefix,
                        bucket_ms,
                        first_request,
                        first_certificate,
                        name,
                        second_certificate,
                    );
                },
                _ => {},
            }
        },
        StoreEffectCertificateV::DocumentFull { after, .. } => {
            match response {
                echod_concrete::store::StoreRes::PutIfMatch {
                    result: Ok(_),
                }
                | echod_concrete::store::StoreRes::PutIfNoneMatch {
                    result: Ok(_),
                } => {
                    let key = document_key(prefix, after);
                    let found = echod_concrete::store::spec_find(
                        store.entries,
                        key,
                        0,
                    ).unwrap();
                    lemma_find_result_valid(store.entries, key, 0);
                    let provenance =
                        choose|provenance: DocumentProvenanceV|
                            entry_has_document_provenance(
                                store.entries[found],
                                prefix,
                                provenance,
                            )
                                && provenance_document(provenance)
                                    == after
                                && provenance.required_timer
                                    == second_certificate
                                        ->DocumentFull_required_timer;
                    lemma_compatible_request_apply_retains_document_provenance(
                        store,
                        prefix,
                        bucket_ms,
                        first_request,
                        first_certificate,
                        second_certificate,
                        found,
                        provenance,
                    );
                    lemma_store_apply_preserves_first_entry_at_distinct_key(
                        store,
                        first_request,
                        key,
                        found,
                    );
                },
                _ => {},
            }
        },
        StoreEffectCertificateV::DocumentAppend { after, .. } => {
            match response {
                echod_concrete::store::StoreRes::AppIfMatch {
                    result: Ok(_),
                } => {
                    let key = document_key(prefix, after);
                    let found = echod_concrete::store::spec_find(
                        store.entries,
                        key,
                        0,
                    ).unwrap();
                    lemma_find_result_valid(store.entries, key, 0);
                    let provenance =
                        choose|provenance: DocumentProvenanceV|
                            entry_has_document_provenance(
                                store.entries[found],
                                prefix,
                                provenance,
                            )
                                && provenance_document(provenance)
                                    == after
                                && provenance.required_timer
                                    == second_certificate
                                        ->DocumentAppend_required_timer;
                    lemma_compatible_request_apply_retains_document_provenance(
                        store,
                        prefix,
                        bucket_ms,
                        first_request,
                        first_certificate,
                        second_certificate,
                        found,
                        provenance,
                    );
                    lemma_store_apply_preserves_first_entry_at_distinct_key(
                        store,
                        first_request,
                        key,
                        found,
                    );
                },
                _ => {},
            }
        },
        _ => {},
    }
}

pub(super) proof fn lemma_timer_put_apply_response_ready(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
)
    requires
        certificate is TimerPut,
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
    ensures
        response_certificate_ready(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            echod_concrete::store::spec_apply(store, request).1,
            certificate,
        ),
{
    reveal(invariant1_store_request_safe);
    reveal(invariant1_certificate_matches_request);
    reveal(certificate_exact_request);
    reveal(response_certificate_ready);
    reveal(echod_concrete::store::spec_apply);
    reveal(echod_concrete::store::spec_etag);
    match certificate {
        StoreEffectCertificateV::TimerPut { key, name } => {
            lemma_certificate_timer_is_namespace(
                prefix,
                bucket_ms,
                key,
                name,
            );
        },
        _ => assert(false),
    }
    match request {
        StoreReq::Put { key, body } => {
            let added = EntryV {
                key: key@,
                body: body@,
                version: match echod_concrete::store::spec_find(
                    store.entries,
                    key@,
                    0,
                ) {
                    Some(found) => echod_concrete::store::spec_bump(
                        store.entries[found].version,
                    ),
                    None => 1,
                },
            };
            lemma_put_contains_added(store.entries, added);
        },
        _ => assert(false),
    }
}

pub(super) proof fn lemma_document_full_create_apply_response_ready(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
)
    requires
        certificate is DocumentFull,
        request is PutIfNoneMatch,
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
    ensures
        response_certificate_ready(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            echod_concrete::store::spec_apply(store, request).1,
            certificate,
        ),
{
    reveal(invariant1_store_request_safe);
    reveal(invariant1_certificate_matches_request);
    reveal(certificate_exact_request);
    reveal(response_certificate_ready);
    reveal(echod_concrete::store::spec_apply);
    reveal(echod_concrete::store::spec_etag);
    let after = certificate->DocumentFull_after;
    let required = certificate->DocumentFull_required_timer;
    match request {
        StoreReq::PutIfNoneMatch { key, body } => {
            if echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            ) is None {
                let added = EntryV {
                    key: key@,
                    body: body@,
                    version: 1,
                };
                let provenance = DocumentProvenanceV {
                    full: after,
                    deltas: Seq::empty(),
                    store_version: added.version,
                    required_timer: required,
                };
                lemma_full_encoding_has_provenance(
                    prefix,
                    after,
                    1,
                    required,
                );
                lemma_put_contains_added(store.entries, added);
                lemma_put_makes_added_first(store.entries, added);
                let next = echod_concrete::store::spec_put(
                    store.entries,
                    added,
                );
                let i = echod_concrete::store::spec_find(
                    next,
                    added.key,
                    0,
                ).unwrap();
                assert(echod_concrete::store::spec_find(
                    next,
                    added.key,
                    0,
                ) is Some);
                lemma_find_result_valid(next, added.key, 0);
                assert(next[i] == added);
                assert(entry_has_document_provenance(
                    next[i],
                    prefix,
                    provenance,
                ));
                assert(provenance_document(provenance) == after);
                assert(provenance.required_timer == required);
                assert(provenance_change_count(provenance.deltas)
                    == certificate->DocumentFull_change_count) by {
                    reveal(provenance_change_count);
                };
                assert(added.key == document_key(prefix, after));
                assert(body@ == crate::document::spec_encode(after));
                assert(echod_concrete::store::spec_find(
                    next,
                    document_key(prefix, after),
                    0,
                ) == Some(i));
                assert(exists|ready: DocumentProvenanceV|
                    entry_has_document_provenance(
                        next[i],
                        prefix,
                        ready,
                    )
                        && provenance_document(ready) == after
                        && ready.required_timer == required
                        && provenance_change_count(ready.deltas)
                            == certificate->DocumentFull_change_count
                        && next[i].body.len()
                            == certificate->DocumentFull_bytes) by {
                    assert(next[i].body.len()
                        == certificate->DocumentFull_bytes);
                };
                assert(next[i].body == body@);
                lemma_spec_etag_has_expected_view(body@);
                assert(echod_concrete::store::spec_etag(body@).deep_view()
                    == echod_concrete::store::EtagSpec(
                        echod_concrete::store::spec_etag_chars(
                            next[i].body,
                        ),
                    ));
                assert(echod_concrete::store::spec_apply(
                    store,
                    request,
                ).0.entries == next);
            }
        },
        _ => assert(false),
    }
}

pub(super) proof fn lemma_document_full_replace_apply_response_ready(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
)
    requires
        certificate is DocumentFull,
        request is PutIfMatch,
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
    ensures
        response_certificate_ready(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            echod_concrete::store::spec_apply(store, request).1,
            certificate,
        ),
{
    reveal(invariant1_store_request_safe);
    reveal(invariant1_certificate_matches_request);
    reveal(certificate_exact_request);
    reveal(response_certificate_ready);
    reveal(echod_concrete::store::spec_apply);
    reveal(echod_concrete::store::spec_etag);
    let after = certificate->DocumentFull_after;
    let required = certificate->DocumentFull_required_timer;
    match request {
        StoreReq::PutIfMatch { key, body, etag } => {
            let found_result = echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            );
            match found_result {
                Some(found) => {
                    lemma_find_result_valid(store.entries, key@, 0);
                    if echod_concrete::store::spec_etag(
                        store.entries[found].body,
                    ) == etag {
                        let version = echod_concrete::store::spec_bump(
                            store.entries[found].version,
                        );
                        let added = EntryV {
                            key: key@,
                            body: body@,
                            version,
                        };
                        let provenance = DocumentProvenanceV {
                            full: after,
                            deltas: Seq::empty(),
                            store_version: added.version,
                            required_timer: required,
                        };
                        lemma_full_encoding_has_provenance(
                            prefix,
                            after,
                            version,
                            required,
                        );
                        lemma_put_contains_added(store.entries, added);
                        lemma_put_makes_added_first(store.entries, added);
                        let next = echod_concrete::store::spec_put(
                            store.entries,
                            added,
                        );
                        let i = echod_concrete::store::spec_find(
                            next,
                            added.key,
                            0,
                        ).unwrap();
                        assert(echod_concrete::store::spec_find(
                            next,
                            added.key,
                            0,
                        ) is Some);
                        lemma_find_result_valid(next, added.key, 0);
                        assert(next[i] == added);
                        assert(entry_has_document_provenance(
                            next[i],
                            prefix,
                            provenance,
                        ));
                        assert(provenance_document(provenance) == after);
                        assert(provenance.required_timer == required);
                        assert(provenance_change_count(provenance.deltas)
                            == certificate->DocumentFull_change_count) by {
                            reveal(provenance_change_count);
                        };
                        assert(added.key == document_key(prefix, after));
                        assert(body@ == crate::document::spec_encode(after));
                        assert(echod_concrete::store::spec_find(
                            next,
                            document_key(prefix, after),
                            0,
                        ) == Some(i));
                        assert(exists|ready: DocumentProvenanceV|
                            entry_has_document_provenance(
                                next[i],
                                prefix,
                                ready,
                            )
                                && provenance_document(ready) == after
                                && ready.required_timer == required
                                && provenance_change_count(ready.deltas)
                                    == certificate
                                        ->DocumentFull_change_count
                                && next[i].body.len()
                                    == certificate->DocumentFull_bytes) by {
                            assert(next[i].body.len()
                                == certificate->DocumentFull_bytes);
                        };
                        assert(next[i].body == body@);
                        lemma_spec_etag_has_expected_view(body@);
                        assert(echod_concrete::store::spec_etag(
                            body@,
                        ).deep_view()
                            == echod_concrete::store::EtagSpec(
                                echod_concrete::store::spec_etag_chars(
                                    next[i].body,
                                ),
                            ));
                        assert(echod_concrete::store::spec_apply(
                            store,
                            request,
                        ).0.entries == next);
                    }
                },
                _ => {},
            }
        },
        _ => assert(false),
    }
}

pub(super) proof fn lemma_document_full_apply_response_ready(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
)
    requires
        certificate is DocumentFull,
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
    ensures
        response_certificate_ready(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            echod_concrete::store::spec_apply(store, request).1,
            certificate,
        ),
{
    reveal(invariant1_store_request_safe);
    reveal(invariant1_certificate_matches_request);
    match request {
        StoreReq::PutIfNoneMatch { .. } => {
            lemma_document_full_create_apply_response_ready(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
            );
        },
        StoreReq::PutIfMatch { .. } => {
            lemma_document_full_replace_apply_response_ready(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
            );
        },
        _ => assert(false),
    }
}

#[verifier::spinoff_prover]
// A successful append extends the exact certified physical base by one delta.
pub(super) proof fn lemma_document_append_apply_response_ready(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
)
    requires
        certificate is DocumentAppend,
        persisted_documents_well_formed(store, prefix),
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
    ensures
        response_certificate_ready(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            echod_concrete::store::spec_apply(store, request).1,
            certificate,
        ),
{
    reveal(invariant1_store_request_safe);
    reveal(invariant1_certificate_matches_request);
    reveal(certificate_exact_request);
    reveal(response_certificate_ready);
    reveal(echod_concrete::store::spec_apply);
    reveal(echod_concrete::store::spec_etag);
    let before = certificate->DocumentAppend_before;
    let after = certificate->DocumentAppend_after;
    let required = certificate->DocumentAppend_required_timer;
    match request {
        StoreReq::AppIfMatch {
            key,
            offset,
            body,
            etag,
        } => {
            let found_result = echod_concrete::store::spec_find(
                store.entries,
                key@,
                0,
            );
            match found_result {
                Some(found) => {
                    lemma_find_result_valid(store.entries, key@, 0);
                    if store.appendable
                        && echod_concrete::store::spec_etag(
                            store.entries[found].body,
                        ) == etag
                        && store.entries[found].body.len() == offset
                    {
                        let old = choose|old: DocumentProvenanceV|
                            entry_has_document_provenance(
                                store.entries[found],
                                prefix,
                                old,
                            )
                            && provenance_document(old) == before
                            && provenance_change_count(old.deltas)
                                == certificate
                                ->DocumentAppend_before_change_count;
                        let version = echod_concrete::store::spec_bump(
                            store.entries[found].version,
                        );
                        let added = EntryV {
                            key: key@,
                            body: store.entries[found].body + body@,
                            version,
                        };
                        let provenance = DocumentProvenanceV {
                            full: old.full,
                            deltas: old.deltas.push(
                                DocumentDeltaV { before, after },
                            ),
                            store_version: added.version,
                            required_timer: required,
                        };
                        lemma_delta_append_extends_provenance(
                            store.entries[found],
                            prefix,
                            old,
                            before,
                            after,
                            version,
                            required,
                        );
                        lemma_put_contains_added(store.entries, added);
                        lemma_put_makes_added_first(store.entries, added);
                        let next = echod_concrete::store::spec_put(
                            store.entries,
                            added,
                        );
                        let i = echod_concrete::store::spec_find(
                            next,
                            added.key,
                            0,
                        ).unwrap();
                        assert(echod_concrete::store::spec_find(
                            next,
                            added.key,
                            0,
                        ) is Some);
                        lemma_find_result_valid(next, added.key, 0);
                        assert(next[i] == added);
                        assert(entry_has_document_provenance(
                            next[i],
                            prefix,
                            provenance,
                        ));
                        assert(provenance_document(provenance) == after);
                        assert(provenance.required_timer == required);
                        lemma_provenance_change_count_push(
                            old.deltas,
                            before,
                            after,
                        );
                        assert(provenance_change_count(provenance.deltas)
                            == certificate->DocumentAppend_change_count) by {
                            reveal(invariant1_certificate_matches_request);
                        };
                        assert(added.key == document_key(prefix, after));
                        assert(echod_concrete::store::spec_find(
                            next,
                            document_key(prefix, after),
                            0,
                        ) == Some(i));
                        assert(exists|ready: DocumentProvenanceV|
                            entry_has_document_provenance(
                                next[i],
                                prefix,
                                ready,
                            )
                                && provenance_document(ready) == after
                                && ready.required_timer == required
                                && provenance_change_count(ready.deltas)
                                    == certificate
                                        ->DocumentAppend_change_count
                                && next[i].body.len()
                                    == certificate->DocumentAppend_bytes) by {
                            assert(next[i].body.len()
                                == certificate->DocumentAppend_bytes);
                        };
                        assert(next[i].body
                            == store.entries[found].body + body@);
                        lemma_spec_etag_has_expected_view(next[i].body);
                        assert(echod_concrete::store::spec_etag(
                            next[i].body,
                        ).deep_view()
                            == echod_concrete::store::EtagSpec(
                                echod_concrete::store::spec_etag_chars(
                                    next[i].body,
                                ),
                            ));
                        assert(echod_concrete::store::spec_apply(
                            store,
                            request,
                        ).0.entries == next);
                    }
                },
                _ => {},
            }
        },
        _ => assert(false),
    }
}

pub(super) proof fn lemma_store_apply_response_ready(
    store: StoreV,
    prefix: Seq<char>,
    bucket_ms: u64,
    request: StoreReq,
    certificate: StoreEffectCertificateV,
)
    requires
        persisted_documents_well_formed(store, prefix),
        invariant1_store_request_safe(
            store,
            prefix,
            bucket_ms,
            request.deep_view(),
            certificate,
        ),
    ensures
        response_certificate_ready(
            echod_concrete::store::spec_apply(store, request).0,
            prefix,
            echod_concrete::store::spec_apply(store, request).1,
            certificate,
        ),
{
    match certificate {
        StoreEffectCertificateV::TimerPut { .. } => {
            lemma_timer_put_apply_response_ready(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
            );
        },
        StoreEffectCertificateV::DocumentFull { .. } => {
            lemma_document_full_apply_response_ready(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
            );
        },
        StoreEffectCertificateV::DocumentAppend { .. } => {
            lemma_document_append_apply_response_ready(
                store,
                prefix,
                bucket_ms,
                request,
                certificate,
            );
        },
        _ => {
            reveal(response_certificate_ready);
        },
    }
}

pub proof fn lemma_uncertified_issue_write_uses_full_rewrite(
    core: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    condition: Seq<char>,
    idle: bool,
)
    requires
        !commit.w.loaded.append_certified,
    ensures
        ({
            let issued = crate::handler_docs::spec_issue_write(
                core,
                fid,
                commit,
                Some(condition),
                idle,
            );
            issued.2 ==> {
                let op = issued.1.expects().unwrap();
                &&& issued.1.issued.unwrap() is Write
                &&& issued.1.issued.unwrap()->Write_mode
                    == crate::types::WriteMode::Rewrite
                &&& issued.0.store_requests[op] is PutIfMatch
                &&& issued.0.store_certificates[op] is DocumentFull
            }
        }),
{
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
}

} // verus!
