//! Cache append-certification preservation lemmas.

#![cfg(verus_keep_ghost)]

use vstd::prelude::*;

use super::super::*;

verus! {

pub(crate) proof fn lemma_provenance_change_count_push(
    deltas: Seq<DocumentDeltaV>,
    before: StoredDocumentV,
    after: StoredDocumentV,
)
    ensures
        provenance_change_count(
            deltas.push(DocumentDeltaV { before, after }),
        ) == provenance_change_count(deltas).saturating_add(
            crate::document::spec_encode_delta(before, after).1,
        ),
{
    let pushed = deltas.push(DocumentDeltaV { before, after });
    assert(pushed.drop_last() == deltas);
    assert(pushed.last() == (DocumentDeltaV { before, after }));
    reveal_with_fuel(provenance_change_count, 1);
}

pub(crate) proof fn lemma_spec_etag_has_expected_view(body: Seq<u8>)
    ensures
        echod_concrete::store::spec_etag(body).deep_view()
            == echod_concrete::store::EtagSpec(
                echod_concrete::store::spec_etag_chars(body),
            ),
{
    echod_concrete::store::lemma_etag_chars_len(body);
    echod_concrete::simulation::lemma_string(
        echod_concrete::store::spec_etag_chars(body),
    );
    reveal(echod_concrete::store::spec_etag);
}

pub(crate) proof fn lemma_cache_entry_document_lane_matches_origin(
    core: S,
    index: int,
)
    requires
        cache_identity_provenance(core),
        0 <= index < core.cache.entries.len(),
    ensures
        document_lane(core.cache.entries[index].cached.loaded.document)
            == crate::target::spec_name(
                crate::target::TargetSpec::Origin(
                    core.cache.entries[index].origin,
                ),
            ),
{
    reveal(cache_identity_provenance);
    reveal(crate::document::loaded_workflow_has_identity);
    reveal(document_lane);
    reveal(crate::target::spec_name);
}

pub(crate) proof fn lemma_cache_move_to_end_preserves_unique_origins(
    entries: Seq<crate::cache::EntrySpec>,
    index: int,
)
    requires
        0 <= index < entries.len(),
        forall|i: int, j: int|
            0 <= i < entries.len()
                && 0 <= j < entries.len()
                && #[trigger] entries[i].origin
                    == #[trigger] entries[j].origin ==> i == j,
    ensures
        ({
            let next = entries.remove(index).push(entries[index]);
            forall|i: int, j: int|
                0 <= i < next.len()
                    && 0 <= j < next.len()
                    && #[trigger] next[i].origin
                        == #[trigger] next[j].origin ==> i == j
        }),
{
    let next = entries.remove(index).push(entries[index]);
    assert forall|i: int, j: int|
        0 <= i < next.len()
            && 0 <= j < next.len()
            && #[trigger] next[i].origin
                == #[trigger] next[j].origin implies i == j by {
        if i < entries.len() - 1 {
            if i < index {
                assert(next[i] == entries[i]);
            } else {
                assert(next[i] == entries[i + 1]);
            }
        } else {
            assert(i == entries.len() - 1);
            assert(next[i] == entries[index]);
        }
        if j < entries.len() - 1 {
            if j < index {
                assert(next[j] == entries[j]);
            } else {
                assert(next[j] == entries[j + 1]);
            }
        } else {
            assert(j == entries.len() - 1);
            assert(next[j] == entries[index]);
        }
    };
}

pub(crate) proof fn lemma_cache_get_preserves_unique_origins(
    cache: crate::cache::CacheSpec,
    origin: Seq<char>,
)
    requires
        forall|i: int, j: int|
            0 <= i < cache.entries.len()
                && 0 <= j < cache.entries.len()
                && #[trigger] cache.entries[i].origin
                    == #[trigger] cache.entries[j].origin ==> i == j,
    ensures
        ({
            let next = crate::cache::spec_get(cache, origin).0;
            forall|i: int, j: int|
                0 <= i < next.entries.len()
                    && 0 <= j < next.entries.len()
                    && #[trigger] next.entries[i].origin
                        == #[trigger] next.entries[j].origin ==> i == j
        }),
{
    reveal(crate::cache::spec_get);
    lemma_cache_find_valid(cache.entries, origin);
    match crate::cache::spec_find(cache.entries, origin) {
        Some(i) => {
            lemma_cache_move_to_end_preserves_unique_origins(
                cache.entries,
                i,
            );
        },
        None => {},
    }
}

pub(crate) proof fn lemma_cache_get_preserves_active_write_cache_exclusion(
    core: S,
    origin: Seq<char>,
)
    requires
        active_document_writes_exclude_certified_cache(core),
    ensures
        active_document_writes_exclude_certified_cache(S {
            cache: crate::cache::spec_get(core.cache, origin).0,
            ..core
        }),
{
    reveal(active_document_writes_exclude_certified_cache);
    reveal(crate::cache::spec_get);
    lemma_cache_find_valid(core.cache.entries, origin);
    match crate::cache::spec_find(core.cache.entries, origin) {
        Some(index) => {
            let entries = core.cache.entries;
            let next = entries.remove(index).push(entries[index]);
            assert forall|op: u64, i: int|
                core.ops.contains_key(op)
                    && core.store_certificates.contains_key(op)
                    && certificate_written_document(
                        core.store_certificates[op],
                    ) is Some
                    && 0 <= i < next.len()
                    && next[i].cached.loaded.append_certified
                implies document_lane(next[i].cached.loaded.document)
                    != document_lane(
                        certificate_written_document(
                            core.store_certificates[op],
                        ).unwrap(),
                    ) by {
                if i < entries.len() - 1 {
                    if i < index {
                        assert(next[i] == entries[i]);
                    } else {
                        assert(next[i] == entries[i + 1]);
                    }
                } else {
                    assert(i == entries.len() - 1);
                    assert(next[i] == entries[index]);
                }
            };
        },
        None => {},
    }
}

pub(crate) proof fn lemma_cache_remove_preserves_unique_origins(
    cache: crate::cache::CacheSpec,
    origin: Seq<char>,
)
    requires
        forall|i: int, j: int|
            0 <= i < cache.entries.len()
                && 0 <= j < cache.entries.len()
                && #[trigger] cache.entries[i].origin
                    == #[trigger] cache.entries[j].origin ==> i == j,
    ensures
        ({
            let next = crate::cache::spec_remove(cache, origin);
            &&& forall|i: int, j: int|
                0 <= i < next.entries.len()
                    && 0 <= j < next.entries.len()
                    && #[trigger] next.entries[i].origin
                        == #[trigger] next.entries[j].origin ==> i == j
            &&& forall|i: int| 0 <= i < next.entries.len() ==>
                #[trigger] next.entries[i].origin != origin
        }),
{
    reveal(crate::cache::spec_remove);
    lemma_cache_find_valid(cache.entries, origin);
    match crate::cache::spec_find(cache.entries, origin) {
        Some(index) => {
            let next = crate::cache::spec_remove(cache, origin);
            assert forall|i: int| 0 <= i < next.entries.len()
                implies #[trigger] next.entries[i].origin != origin by {
                if i < index {
                    assert(next.entries[i] == cache.entries[i]);
                } else {
                    assert(next.entries[i] == cache.entries[i + 1]);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < next.entries.len()
                    && 0 <= j < next.entries.len()
                    && #[trigger] next.entries[i].origin
                        == #[trigger] next.entries[j].origin implies i == j by {
                if i < index {
                    assert(next.entries[i] == cache.entries[i]);
                } else {
                    assert(next.entries[i] == cache.entries[i + 1]);
                }
                if j < index {
                    assert(next.entries[j] == cache.entries[j]);
                } else {
                    assert(next.entries[j] == cache.entries[j + 1]);
                }
            };
        },
        None => {
            assert forall|i: int| 0 <= i < cache.entries.len()
                implies #[trigger] cache.entries[i].origin != origin by {};
        },
    }
}

pub(crate) proof fn lemma_cache_remove_preserves_active_write_cache_exclusion(
    core: S,
    origin: Seq<char>,
)
    requires
        active_document_writes_exclude_certified_cache(core),
    ensures
        active_document_writes_exclude_certified_cache(S {
            cache: crate::cache::spec_remove(core.cache, origin),
            ..core
        }),
{
    reveal(active_document_writes_exclude_certified_cache);
    reveal(crate::cache::spec_remove);
    lemma_cache_find_valid(core.cache.entries, origin);
    match crate::cache::spec_find(core.cache.entries, origin) {
        Some(index) => {
            let next =
                crate::cache::spec_remove(core.cache, origin).entries;
            assert forall|op: u64, i: int|
                core.ops.contains_key(op)
                    && core.store_certificates.contains_key(op)
                    && certificate_written_document(
                        core.store_certificates[op],
                    ) is Some
                    && 0 <= i < next.len()
                    && next[i].cached.loaded.append_certified
                implies document_lane(next[i].cached.loaded.document)
                    != document_lane(
                        certificate_written_document(
                            core.store_certificates[op],
                        ).unwrap(),
                    ) by {
                if i < index {
                    assert(next[i] == core.cache.entries[i]);
                } else {
                    assert(next[i] == core.cache.entries[i + 1]);
                }
            };
        },
        None => {},
    }
}

pub(crate) proof fn lemma_cache_trim_preserves_active_write_cache_exclusion(
    core: S,
    keep: Seq<char>,
)
    requires
        active_document_writes_exclude_certified_cache(core),
    ensures
        active_document_writes_exclude_certified_cache(S {
            cache: crate::cache::spec_trim(core.cache, keep).1,
            ..core
        }),
    decreases core.cache.entries.len(),
{
    reveal_with_fuel(crate::cache::spec_trim, 1);
    if (core.cache.entries.len() > core.cache.max_entries
        || core.cache.bytes > core.cache.max_bytes)
        && core.cache.entries.len() > 0
        && core.cache.entries[0].origin != keep
    {
        let dropped_cache = crate::cache::CacheSpec {
            entries: core.cache.entries.drop_first(),
            bytes: core.cache.bytes.wrapping_sub(
                core.cache.entries[0].cached.weight(),
            ),
            evictions: core.cache.evictions.wrapping_add(1),
            ..core.cache
        };
        let dropped = S { cache: dropped_cache, ..core };
        assert(active_document_writes_exclude_certified_cache(
            dropped,
        )) by {
            reveal(active_document_writes_exclude_certified_cache);
            assert forall|op: u64, i: int|
                dropped.ops.contains_key(op)
                    && dropped.store_certificates.contains_key(op)
                    && certificate_written_document(
                        dropped.store_certificates[op],
                    ) is Some
                    && 0 <= i < dropped.cache.entries.len()
                    && dropped.cache.entries[i]
                        .cached.loaded.append_certified
                implies document_lane(
                    dropped.cache.entries[i].cached.loaded.document,
                ) != document_lane(
                    certificate_written_document(
                        dropped.store_certificates[op],
                    ).unwrap(),
                ) by {
                assert(dropped.cache.entries[i]
                    == core.cache.entries[i + 1]);
            };
        };
        lemma_cache_trim_preserves_active_write_cache_exclusion(
            dropped,
            keep,
        );
    }
}

pub(crate) proof fn lemma_cache_put_preserves_active_write_cache_exclusion(
    core: S,
    origin: Seq<char>,
    cached: crate::cache::CachedSpec,
)
    requires
        active_document_writes_exclude_certified_cache(core),
        forall|op: u64|
            core.ops.contains_key(op)
                && core.store_certificates.contains_key(op)
                && certificate_written_document(
                    core.store_certificates[op],
                ) is Some
                && cached.loaded.append_certified ==>
            document_lane(cached.loaded.document)
                != document_lane(
                    certificate_written_document(
                        core.store_certificates[op],
                    ).unwrap(),
                ),
    ensures
        active_document_writes_exclude_certified_cache(S {
            cache: crate::cache::spec_put(
                core.cache,
                origin,
                cached,
            ).1,
            ..core
        }),
{
    lemma_cache_remove_preserves_active_write_cache_exclusion(
        core,
        origin,
    );
    let removed_cache = crate::cache::spec_remove(core.cache, origin);
    let removed = S { cache: removed_cache, ..core };
    let inserted_cache = crate::cache::CacheSpec {
        entries: removed.cache.entries.push(
            crate::cache::EntrySpec { origin, cached },
        ),
        bytes: removed.cache.bytes.wrapping_add(cached.weight()),
        ..removed.cache
    };
    let inserted = S { cache: inserted_cache, ..removed };
    assert(active_document_writes_exclude_certified_cache(inserted)) by {
        reveal(active_document_writes_exclude_certified_cache);
        assert forall|op: u64, i: int|
            inserted.ops.contains_key(op)
                && inserted.store_certificates.contains_key(op)
                && certificate_written_document(
                    inserted.store_certificates[op],
                ) is Some
                && 0 <= i < inserted.cache.entries.len()
                && inserted.cache.entries[i]
                    .cached.loaded.append_certified
            implies document_lane(
                inserted.cache.entries[i].cached.loaded.document,
            ) != document_lane(
                certificate_written_document(
                    inserted.store_certificates[op],
                ).unwrap(),
            ) by {
            if i < removed.cache.entries.len() {
                assert(inserted.cache.entries[i]
                    == removed.cache.entries[i]);
            } else {
                assert(i == removed.cache.entries.len());
                assert(inserted.cache.entries[i].cached == cached);
            }
        };
    };
    lemma_cache_trim_preserves_active_write_cache_exclusion(
        inserted,
        origin,
    );
    reveal(crate::cache::spec_put);
}

pub(crate) proof fn lemma_cache_trim_preserves_unique_origins(
    cache: crate::cache::CacheSpec,
    keep: Seq<char>,
)
    requires
        forall|i: int, j: int|
            0 <= i < cache.entries.len()
                && 0 <= j < cache.entries.len()
                && #[trigger] cache.entries[i].origin
                    == #[trigger] cache.entries[j].origin ==> i == j,
    ensures
        ({
            let next = crate::cache::spec_trim(cache, keep).1;
            forall|i: int, j: int|
                0 <= i < next.entries.len()
                    && 0 <= j < next.entries.len()
                    && #[trigger] next.entries[i].origin
                        == #[trigger] next.entries[j].origin ==> i == j
        }),
    decreases cache.entries.len(),
{
    reveal_with_fuel(crate::cache::spec_trim, 1);
    if (cache.entries.len() > cache.max_entries
        || cache.bytes > cache.max_bytes)
        && cache.entries.len() > 0
        && cache.entries[0].origin != keep
    {
        let next = crate::cache::CacheSpec {
            entries: cache.entries.drop_first(),
            bytes: cache.bytes.wrapping_sub(
                cache.entries[0].cached.weight(),
            ),
            evictions: cache.evictions.wrapping_add(1),
            ..cache
        };
        assert forall|i: int, j: int|
            0 <= i < next.entries.len()
                && 0 <= j < next.entries.len()
                && #[trigger] next.entries[i].origin
                    == #[trigger] next.entries[j].origin implies i == j by {
            assert(next.entries[i] == cache.entries[i + 1]);
            assert(next.entries[j] == cache.entries[j + 1]);
        };
        lemma_cache_trim_preserves_unique_origins(next, keep);
    }
}

pub(crate) proof fn lemma_cache_put_preserves_unique_origins(
    cache: crate::cache::CacheSpec,
    origin: Seq<char>,
    cached: crate::cache::CachedSpec,
)
    requires
        forall|i: int, j: int|
            0 <= i < cache.entries.len()
                && 0 <= j < cache.entries.len()
                && #[trigger] cache.entries[i].origin
                    == #[trigger] cache.entries[j].origin ==> i == j,
    ensures
        ({
            let next =
                crate::cache::spec_put(cache, origin, cached).1;
            forall|i: int, j: int|
                0 <= i < next.entries.len()
                    && 0 <= j < next.entries.len()
                    && #[trigger] next.entries[i].origin
                        == #[trigger] next.entries[j].origin ==> i == j
        }),
{
    reveal(crate::cache::spec_put);
    lemma_cache_remove_preserves_unique_origins(cache, origin);
    let removed = crate::cache::spec_remove(cache, origin);
    let inserted = crate::cache::CacheSpec {
        entries: removed.entries.push(
            crate::cache::EntrySpec { origin, cached },
        ),
        bytes: removed.bytes.wrapping_add(cached.weight()),
        ..removed
    };
    assert forall|i: int, j: int|
        0 <= i < inserted.entries.len()
            && 0 <= j < inserted.entries.len()
            && #[trigger] inserted.entries[i].origin
                == #[trigger] inserted.entries[j].origin implies i == j by {
        if i < removed.entries.len() {
            assert(inserted.entries[i] == removed.entries[i]);
        } else {
            assert(i == removed.entries.len());
            assert(inserted.entries[i].origin == origin);
        }
        if j < removed.entries.len() {
            assert(inserted.entries[j] == removed.entries[j]);
        } else {
            assert(j == removed.entries.len());
            assert(inserted.entries[j].origin == origin);
        }
    };
    lemma_cache_trim_preserves_unique_origins(inserted, origin);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_issue_write_preserves_active_write_cache_exclusion(
    state: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    cond: Option<Seq<char>>,
    idle: bool,
)
    requires
        production_core_control_body(state),
        cache_identity_provenance(state),
        match commit.after {
            StoredDocumentV::Workflow(_) =>
                document_lane(commit.after)
                    == crate::target::spec_name(
                        crate::target::TargetSpec::Origin(
                            commit.w.target,
                        ),
                    ),
            StoredDocumentV::Schedule(schedule) =>
                document_lane(commit.after)
                    == crate::target::spec_name(
                        crate::target::TargetSpec::Schedule(
                            schedule.document,
                        ),
                    ),
        },
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_issue_write(
                state,
                fid,
                commit,
                cond,
                idle,
            ).0,
        ),
{
    lemma_issue_write_preserves_cache_identity(
        state,
        fid,
        commit,
        cond,
        idle,
    );
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::cache::spec_remove);
    reveal(production_core_control_body);
    reveal(crate::production_relation::operation_allocator_consistent);
    let result = crate::handler_docs::spec_issue_write(
        state,
        fid,
        commit,
        cond,
        idle,
    );
    if well_formed(commit.after) {
        match result.2 {
            true => {
                let issued = result.1.issued.unwrap();
                let fresh = issued->Write_op;
                assert(!state.ops.contains_key(fresh));
                if commit.after is Workflow {
                    lemma_cache_remove_preserves_unique_origins(
                        state.cache,
                        commit.w.target,
                    );
                    lemma_cache_find_valid(
                        state.cache.entries,
                        commit.w.target,
                    );
                }
                reveal(active_document_writes_exclude_certified_cache);
                assert forall|op: u64, i: int|
                    result.0.ops.contains_key(op)
                        && result.0.store_certificates.contains_key(op)
                        && certificate_written_document(
                            result.0.store_certificates[op],
                        ) is Some
                        && 0 <= i < result.0.cache.entries.len()
                        && result.0.cache.entries[i]
                            .cached.loaded.append_certified
                    implies document_lane(
                        result.0.cache.entries[i].cached.loaded.document,
                    ) != document_lane(
                        certificate_written_document(
                            result.0.store_certificates[op],
                        ).unwrap(),
                    ) by {
                    lemma_cache_entry_document_lane_matches_origin(
                        result.0,
                        i,
                    );
                    if op == fresh {
                        assert(certificate_written_document(
                            result.0.store_certificates[op],
                        ) == Some(commit.after)) by {
                            reveal(certificate_written_document);
                        };
                        match commit.after {
                            StoredDocumentV::Workflow(_) => {
                                assert(result.0.cache.entries[i].origin
                                    != commit.w.target);
                                if document_lane(
                                    result.0.cache.entries[i]
                                        .cached.loaded.document,
                                ) == document_lane(commit.after) {
                                    crate::target::lemma_name_injective(
                                        crate::target::TargetSpec::Origin(
                                            result.0.cache.entries[i]
                                                .origin,
                                        ),
                                        crate::target::TargetSpec::Origin(
                                            commit.w.target,
                                        ),
                                    );
                                    assert(false);
                                }
                            },
                            StoredDocumentV::Schedule(schedule) => {
                                lemma_origin_and_schedule_lanes_are_distinct(
                                    result.0.cache.entries[i].origin,
                                    schedule.document,
                                );
                            },
                        }
                    } else {
                        assert(state.ops.contains_key(op));
                        assert(state.store_certificates.contains_key(op));
                        assert(result.0.store_certificates[op]
                            == state.store_certificates[op]);
                        if commit.after is Workflow {
                            let found = crate::cache::spec_find(
                                state.cache.entries,
                                commit.w.target,
                            );
                            match found {
                                Some(index) => {
                                    if i < index {
                                        assert(result.0.cache.entries[i]
                                            == state.cache.entries[i]);
                                    } else {
                                        assert(result.0.cache.entries[i]
                                            == state.cache.entries[i + 1]);
                                    }
                                },
                                None => {
                                    assert(result.0.cache.entries
                                        == state.cache.entries);
                                },
                            }
                        } else {
                            assert(result.0.cache == state.cache);
                        }
                    }
                };
            },
            false => {
                assert(result.0 == state);
            },
        }
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_begin_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_begin(state, flight),
        ),
{
    let cache_framed = match (flight.work, flight.target) {
        (
            crate::handler_docs::WorkSpec::Fire { .. },
            _,
        ) => state,
        (
            _,
            crate::target::TargetSpec::Origin(origin),
        ) => {
            lemma_cache_get_preserves_active_write_cache_exclusion(
                state,
                origin,
            );
            S {
                cache:
                    crate::cache::spec_get(state.cache, origin).0,
                ..state
            }
        },
        _ => state,
    };
    let next = crate::handler_docs::spec_begin(state, flight);
    assert(next.cache == cache_framed.cache) by {
        reveal(crate::handler_docs::spec_begin);
        reveal(crate::handler_docs::spec_load_origin);
        reveal(crate::handler_docs::spec_inflight);
        reveal(crate::handler_docs::spec_op_exhausted);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(crate::handler_timers::spec_timer_op_exhausted);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
    };
    assert forall|op: u64|
        next.ops.contains_key(op)
            && next.store_certificates.contains_key(op)
            && certificate_written_document(
                next.store_certificates[op],
            ) is Some implies {
                &&& cache_framed.ops.contains_key(op)
                &&& cache_framed.store_certificates.contains_key(op)
                &&& cache_framed.store_certificates[op]
                    == next.store_certificates[op]
            } by {
        reveal(crate::handler_docs::spec_begin);
        reveal(crate::handler_docs::spec_load_origin);
        reveal(crate::handler_docs::spec_inflight);
        reveal(crate::handler_docs::spec_op_exhausted);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(crate::handler_timers::spec_timer_op_exhausted);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(certificate_written_document);
        reveal(production_core_control_body);
        reveal(crate::production_relation::operation_allocator_consistent);
    };
    lemma_active_write_cache_exclusion_frames(cache_framed, next);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fire_load_origin_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    ctx: crate::handler_docs::FireCtxSpec,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_sched::spec_fire_load_origin(
                state,
                flight,
                ctx,
            ),
        ),
{
    lemma_cache_get_preserves_active_write_cache_exclusion(
        state,
        ctx.origin,
    );
    let cache_framed = S {
        cache: crate::cache::spec_get(
            state.cache,
            ctx.origin,
        ).0,
        ..state
    };
    let next = crate::handler_sched::spec_fire_load_origin(
        state,
        flight,
        ctx,
    );
    assert(next.cache == cache_framed.cache) by {
        reveal(crate::handler_sched::spec_fire_load_origin);
        reveal(crate::handler_docs::spec_load_origin);
        reveal(crate::handler_docs::spec_inflight);
        reveal(crate::handler_docs::spec_op_exhausted);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(crate::handler_timers::spec_timer_op_exhausted);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
    };
    assert forall|op: u64|
        next.ops.contains_key(op)
            && next.store_certificates.contains_key(op)
            && certificate_written_document(
                next.store_certificates[op],
            ) is Some implies {
                &&& cache_framed.ops.contains_key(op)
                &&& cache_framed.store_certificates.contains_key(op)
                &&& cache_framed.store_certificates[op]
                    == next.store_certificates[op]
            } by {
        reveal(crate::handler_sched::spec_fire_load_origin);
        reveal(crate::handler_docs::spec_load_origin);
        reveal(crate::handler_docs::spec_inflight);
        reveal(crate::handler_docs::spec_op_exhausted);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(crate::handler_timers::spec_timer_op_exhausted);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(certificate_written_document);
        reveal(production_core_control_body);
        reveal(crate::production_relation::operation_allocator_consistent);
    };
    lemma_active_write_cache_exclusion_frames(cache_framed, next);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_start_nonfire_preserves_active_write_cache_exclusion(
    state: S,
    target: crate::target::TargetSpec,
    work: crate::handler_docs::WorkSpec,
    firing: Option<crate::handler_docs::FiringSpec>,
    debug: bool,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_start(
                state,
                target,
                work,
                firing,
                debug,
            ),
        ),
{
    let allocated = crate::state::spec_flight(state);
    assert(active_document_writes_exclude_certified_cache(
        allocated.0,
    )) by {
        reveal(crate::state::spec_flight);
        reveal(active_document_writes_exclude_certified_cache);
    };
    let cache_framed = match (work, allocated.1, target) {
        (
            crate::handler_docs::WorkSpec::Fire { .. },
            _,
            _,
        ) => allocated.0,
        (
            _,
            Some(_),
            crate::target::TargetSpec::Origin(origin),
        ) => {
            lemma_cache_get_preserves_active_write_cache_exclusion(
                allocated.0,
                origin,
            );
            S {
                cache:
                    crate::cache::spec_get(allocated.0.cache, origin).0,
                ..allocated.0
            }
        },
        _ => allocated.0,
    };
    let next = crate::handler_docs::spec_start(
        state,
        target,
        work,
        firing,
        debug,
    );
    assert(next.cache == cache_framed.cache) by {
        reveal(crate::handler_docs::spec_start);
        reveal(crate::handler_docs::spec_begin);
        reveal(crate::handler_docs::spec_load_origin);
        reveal(crate::handler_docs::spec_inflight);
        reveal(crate::handler_docs::spec_op_exhausted);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(crate::handler_timers::spec_timer_op_exhausted);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(crate::state::spec_flight);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
    };
    assert forall|op: u64|
        next.ops.contains_key(op)
            && next.store_certificates.contains_key(op)
            && certificate_written_document(
                next.store_certificates[op],
            ) is Some implies {
                &&& cache_framed.ops.contains_key(op)
                &&& cache_framed.store_certificates.contains_key(op)
                &&& cache_framed.store_certificates[op]
                    == next.store_certificates[op]
            } by {
        reveal(crate::handler_docs::spec_start);
        reveal(crate::handler_docs::spec_begin);
        reveal(crate::handler_docs::spec_load_origin);
        reveal(crate::handler_docs::spec_inflight);
        reveal(crate::handler_docs::spec_op_exhausted);
        reveal(crate::handler_docs::spec_abandon_slot);
        reveal(crate::handler_timers::spec_timer_op_exhausted);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(crate::state::spec_flight);
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(certificate_written_document);
        reveal(production_core_control_body);
        reveal(crate::production_relation::operation_allocator_consistent);
    };
    lemma_active_write_cache_exclusion_frames(cache_framed, next);
}

pub(crate) proof fn lemma_submit_nonfire_preserves_active_write_cache_exclusion(
    state: S,
    target: crate::target::TargetSpec,
    work: crate::handler_docs::WorkSpec,
    firing: Option<crate::handler_docs::FiringSpec>,
    debug: bool,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_submit(
                state,
                target,
                work,
                firing,
                debug,
            ),
        ),
{
    reveal(crate::handler_docs::spec_submit);
    let staged = match work {
        crate::handler_docs::WorkSpec::Sweep { now, .. } =>
            crate::state::spec_note(
                state,
                crate::types::NoteSpec::SweepBegin {
                    flight: state.next_flight,
                    target: crate::target::spec_name(target),
                    now,
                },
            ),
        _ => state,
    };
    assert(production_core_control_body(staged)) by {
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
    };
    assert(active_document_writes_exclude_certified_cache(staged)) by {
        reveal(crate::state::spec_note);
        reveal(active_document_writes_exclude_certified_cache);
    };
    let name = crate::target::spec_name(target);
    let slot = crate::handler_docs::spec_slot_of(staged, name);
    if slot.busy is Some {
        reveal(crate::handler_docs::spec_with_slot);
        reveal(active_document_writes_exclude_certified_cache);
    } else {
        let slotted =
            crate::handler_docs::spec_with_slot(staged, name, slot);
        assert(production_core_control_body(slotted)) by {
            reveal(crate::handler_docs::spec_with_slot);
            reveal(production_core_control_body);
        };
        assert(active_document_writes_exclude_certified_cache(slotted)) by {
            reveal(crate::handler_docs::spec_with_slot);
            reveal(active_document_writes_exclude_certified_cache);
        };
        lemma_start_nonfire_preserves_active_write_cache_exclusion(
            slotted,
            target,
            work,
            firing,
            debug,
        );
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_release_preserves_active_write_cache_exclusion(
    state: S,
    name: Seq<char>,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_release(state, name),
        ),
{
    reveal(crate::handler_docs::spec_release);
    if state.flights.slots.contains_key(name) {
        let slot = state.flights.slots[name];
        if slot.queue.len() > 0 {
            let rest = slot.queue.drop_first();
            let released = crate::handler_docs::spec_with_slot(
                state,
                name,
                crate::handler_docs::SlotSpec {
                    busy: match slot.queue[0] {
                        crate::handler_docs::QueuedSpec::Waiter(fid) =>
                            Some(fid),
                        _ => None,
                    },
                    queue: rest,
                },
            );
            assert(production_core_control_body(released)) by {
                reveal(crate::handler_docs::spec_with_slot);
                reveal(production_core_control_body);
            };
            assert(active_document_writes_exclude_certified_cache(
                released,
            )) by {
                reveal(crate::handler_docs::spec_with_slot);
                reveal(active_document_writes_exclude_certified_cache);
            };
            match slot.queue[0] {
                crate::handler_docs::QueuedSpec::Work {
                    target,
                    work,
                    firing,
                    debug,
                } => {
                    lemma_start_nonfire_preserves_active_write_cache_exclusion(
                        released,
                        target,
                        work,
                        firing,
                        debug,
                    );
                },
                crate::handler_docs::QueuedSpec::Waiter(fid) => {
                    let resumed =
                        crate::handler_docs::spec_resume(released, fid);
                    if released.flights.inflight.contains_key(fid) {
                        let waiter = released.flights.inflight[fid];
                        match waiter.phase {
                            crate::handler_docs::PhaseSpec::FireWaitingOrigin(
                                ctx,
                            ) => {
                                let detached =
                                    crate::handler_docs::spec_take_flight(
                                        released,
                                        fid,
                                    );
                                assert(production_core_control_body(
                                    detached,
                                )) by {
                                    reveal(crate::handler_docs::spec_take_flight);
                                    reveal(production_core_control_body);
                                    reveal(active_flight_owners_match_phase);
                                };
                                assert(active_document_writes_exclude_certified_cache(
                                    detached,
                                )) by {
                                    reveal(crate::handler_docs::spec_take_flight);
                                    reveal(active_document_writes_exclude_certified_cache);
                                };
                                lemma_fire_load_origin_preserves_active_write_cache_exclusion(
                                    detached,
                                    crate::handler_docs::FlightSpec {
                                        phase: crate::handler_docs::PhaseSpec::Idle,
                                        ..waiter
                                    },
                                    ctx,
                                );
                            },
                            _ => {
                                reveal(crate::handler_docs::spec_resume);
                                reveal(crate::handler_docs::spec_take_flight);
                                reveal(crate::handler_docs::spec_inflight);
                                reveal(active_document_writes_exclude_certified_cache);
                            },
                        }
                    }
                    reveal(crate::handler_docs::spec_resume);
                },
            }
        }
    }
    reveal(crate::handler_docs::spec_without_slot);
    reveal(active_document_writes_exclude_certified_cache);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_timer_fired_preserves_active_write_cache_exclusion(
    state: S,
    firing: crate::handler_docs::FiringSpec,
    now: u64,
    result: Result<
        crate::types::Fired,
        Seq<char>,
    >,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_timer_fired(
                state,
                firing,
                now,
                result,
            ),
        ),
{
    let prepared = match result {
        Ok(crate::types::Fired::Deleted) =>
            crate::handler_timers::spec_with_timers(
                state,
                crate::state_timers::TimersSpec {
                    inflight: state.timers.inflight.saturating_sub(1),
                    ..state.timers
                },
            ),
        Ok(crate::types::Fired::Kept) => {
            let decremented = crate::handler_timers::spec_with_timers(
                state,
                crate::state_timers::TimersSpec {
                    inflight: state.timers.inflight.saturating_sub(1),
                    ..state.timers
                },
            );
            let rearm = crate::state_timers::spec_max(now, firing.at)
                .saturating_add(
                    crate::state_timers::RETRY_AFTER_MS,
                );
            crate::handler_timers::spec_with_timers(
                decremented,
                crate::state_timers::TimersSpec {
                    wheel: crate::state_timers::TimerWheelSpec {
                        armed: crate::state_timers::spec_arm(
                            decremented.timers.wheel.armed,
                            rearm,
                            firing.key,
                        ),
                    },
                    ..decremented.timers
                },
            )
        },
        Err(error) => {
            let decremented = crate::handler_timers::spec_with_timers(
                state,
                crate::state_timers::TimersSpec {
                    inflight: state.timers.inflight.saturating_sub(1),
                    ..state.timers
                },
            );
            let noted = crate::state::spec_note(
                decremented,
                crate::types::NoteSpec::FireFailed {
                    key: firing.key,
                    error,
                },
            );
            let rearm = crate::state_timers::spec_max(now, firing.at)
                .saturating_add(
                    crate::state_timers::RETRY_AFTER_MS,
                );
            crate::handler_timers::spec_with_timers(
                noted,
                crate::state_timers::TimersSpec {
                    wheel: crate::state_timers::TimerWheelSpec {
                        armed: crate::state_timers::spec_arm(
                            noted.timers.wheel.armed,
                            rearm,
                            firing.key,
                        ),
                    },
                    ..noted.timers
                },
            )
        },
    };
    let noted = crate::state::spec_note(
        prepared,
        crate::types::NoteSpec::TimerFire {
            kind: firing.kind,
            outcome: match result {
                Ok(crate::types::Fired::Deleted) =>
                    crate::types::FireOutcome::Deleted,
                Ok(crate::types::Fired::Kept) =>
                    crate::types::FireOutcome::Kept,
                Err(_) => crate::types::FireOutcome::Failed,
            },
            lag_ms: firing.lag,
        },
    );
    assert(production_core_control_body(noted)) by {
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
    };
    assert(active_document_writes_exclude_certified_cache(noted)) by {
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_note);
        reveal(active_document_writes_exclude_certified_cache);
    };
    lemma_dispatch_due_preserves_active_write_cache_exclusion(
        noted,
        now,
        noted.timers.backlog.len(),
    );
    reveal(crate::handler_timers::spec_timer_fired);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_finish_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    result: Result<
        crate::types::Fired,
        Seq<char>,
    >,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_finish(
                state,
                flight,
                result,
            ),
        ),
{
    let released = crate::handler_docs::spec_release(
        state,
        crate::target::spec_name(flight.target),
    );
    lemma_release_preserves_active_write_cache_exclusion(
        state,
        crate::target::spec_name(flight.target),
    );
    crate::global_store_control::
        lemma_release_preserves_core_control_body(
            state,
            crate::target::spec_name(flight.target),
        );
    let fired = match flight.firing {
        Some(firing) =>
            crate::handler_timers::spec_timer_fired(
                released,
                firing,
                crate::state::spec_now(released),
                result,
            ),
        None => released,
    };
    match flight.firing {
        Some(firing) => {
            lemma_timer_fired_preserves_active_write_cache_exclusion(
                released,
                firing,
                crate::state::spec_now(released),
                result,
            );
            lemma_timer_fired_preserves_core_control_body(
                released,
                firing,
                crate::state::spec_now(released),
                result,
            );
        },
        None => {},
    }
    assert(active_document_writes_exclude_certified_cache(fired));
    assert(production_core_control_body(fired));
    assert(fired.debug.current is None) by {
        reveal(production_core_control_body);
    };
    let next = if flight.debug {
        crate::debug::spec_debug_flight_done(
            fired,
            flight.work,
            flight.idle,
        )
    } else {
        fired
    };
    assert(next == fired) by {
        reveal(crate::debug::spec_debug_flight_done);
        reveal(crate::debug::spec_debug_tick_advance);
    };
    reveal(crate::handler_docs::spec_finish);
}

pub(crate) proof fn lemma_send_all_preserves_active_write_cache_exclusion(
    state: S,
    outbox: Seq<(Seq<char>, crate::types::MessageSpec)>,
)
    requires
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_send_all(state, outbox),
        ),
    decreases outbox.len(),
{
    reveal(crate::handler_docs::spec_send_all);
    if outbox.len() > 0 {
        let emitted = crate::state::spec_emit(
            state,
            crate::types::EffectSpec::Send {
                address: outbox[0].0,
                message: outbox[0].1,
            },
        );
        assert(active_document_writes_exclude_certified_cache(
            emitted,
        )) by {
            reveal(crate::state::spec_emit);
            reveal(active_document_writes_exclude_certified_cache);
        };
        lemma_send_all_preserves_active_write_cache_exclusion(
            emitted,
            outbox.drop_first(),
        );
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_committed_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    done: crate::handler_docs::DoneSpec,
    fired: crate::types::Fired,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_committed(
                state,
                flight,
                done,
                fired,
            ),
        ),
{
    let noted = crate::state::spec_note(
        state,
        crate::types::NoteSpec::Commit(
            crate::types::CommitOutcome::Committed,
        ),
    );
    let prepared = crate::handler_docs::spec_send_all(
        noted,
        done.outbox,
    );
    assert(active_document_writes_exclude_certified_cache(noted)) by {
        reveal(crate::state::spec_note);
        reveal(active_document_writes_exclude_certified_cache);
    };
    assert(production_core_control_body(noted)) by {
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
    };
    lemma_send_all_preserves_active_write_cache_exclusion(
        noted,
        done.outbox,
    );
    lemma_send_all_preserves_core_control_body(noted, done.outbox);
    let before_finish = match flight.work {
        crate::handler_docs::WorkSpec::Request {
            id,
            kind,
            corr,
            action_kind,
            ..
        } => crate::state::spec_emit(
            prepared,
            crate::types::EffectSpec::Reply {
                id,
                response: match done.response {
                    Some(response) => Ok(
                        crate::types::AnswerSpec::Step {
                            kind,
                            corr,
                            action_kind,
                            response,
                            why: done.why,
                        },
                    ),
                    None => Err("no answer"@),
                },
            },
        ),
        crate::handler_docs::WorkSpec::Sweep { .. } =>
            crate::state::spec_note(
                crate::state::spec_note(
                    prepared,
                    crate::types::NoteSpec::Sweep(
                        if done.did {
                            crate::types::SweepOutcome::Fired
                        } else {
                            crate::types::SweepOutcome::Idle
                        },
                    ),
                ),
                crate::types::NoteSpec::SweepEnd {
                    flight: flight.id,
                    committed: true,
                },
            ),
        crate::handler_docs::WorkSpec::Fire { .. } => prepared,
    };
    assert(production_core_control_body(before_finish)) by {
        reveal(crate::state::spec_note);
        reveal(crate::state::spec_emit);
        reveal(production_core_control_body);
    };
    assert(active_document_writes_exclude_certified_cache(
        before_finish,
    )) by {
        reveal(crate::state::spec_note);
        reveal(crate::state::spec_emit);
        reveal(active_document_writes_exclude_certified_cache);
    };
    lemma_finish_preserves_active_write_cache_exclusion(
        before_finish,
        crate::handler_docs::FlightSpec {
            idle: !done.did,
            ..flight
        },
        Ok(fired),
    );
    reveal(crate::handler_docs::spec_committed);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fail_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    error: Seq<char>,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_fail(state, flight, error),
        ),
{
    let prepared = match flight.work {
        crate::handler_docs::WorkSpec::Request { id, .. } =>
            crate::state::spec_emit(
                state,
                crate::types::EffectSpec::Reply {
                    id,
                    response: Err(error),
                },
            ),
        crate::handler_docs::WorkSpec::Sweep { .. } =>
            crate::state::spec_note(
                crate::state::spec_note(
                    state,
                    crate::types::NoteSpec::Sweep(
                        crate::types::SweepOutcome::Failed,
                    ),
                ),
                crate::types::NoteSpec::SweepEnd {
                    flight: flight.id,
                    committed: false,
                },
            ),
        crate::handler_docs::WorkSpec::Fire { .. } => state,
    };
    assert(production_core_control_body(prepared)) by {
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
    };
    assert(active_document_writes_exclude_certified_cache(prepared)) by {
        reveal(crate::state::spec_emit);
        reveal(crate::state::spec_note);
        reveal(active_document_writes_exclude_certified_cache);
    };
    lemma_finish_preserves_active_write_cache_exclusion(
        prepared,
        flight,
        Err(error),
    );
    reveal(crate::handler_docs::spec_fail);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_retry_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_retry(state, flight),
        ),
{
    let retry = crate::handler_docs::FlightSpec {
        attempt: flight.attempt.wrapping_add(1),
        ..flight
    };
    if retry.attempt > state.flights.max_retries {
        let noted = crate::state::spec_note(
            state,
            crate::types::NoteSpec::Commit(
                crate::types::CommitOutcome::Exhausted,
            ),
        );
        assert(production_core_control_body(noted)) by {
            reveal(crate::state::spec_note);
            reveal(production_core_control_body);
        };
        assert(active_document_writes_exclude_certified_cache(noted)) by {
            reveal(crate::state::spec_note);
            reveal(active_document_writes_exclude_certified_cache);
        };
        lemma_fail_preserves_active_write_cache_exclusion(
            noted,
            retry,
            "too many races on the "@
                + match retry.target {
                    crate::target::TargetSpec::Origin(_) => "document"@,
                    crate::target::TargetSpec::Schedule(_) => "schedule"@,
                },
        );
    } else {
        lemma_begin_preserves_active_write_cache_exclusion(
            state,
            retry,
        );
    }
    reveal(crate::handler_docs::spec_retry);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_commit_failed_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    error: echod_concrete::store::StoreErrorSpec,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_commit_failed(
                state,
                flight,
                error,
            ),
        ),
{
    let forgotten = match flight.target {
        crate::target::TargetSpec::Origin(origin) => {
            lemma_cache_remove_preserves_active_write_cache_exclusion(
                state,
                origin,
            );
            crate::state::spec_forget_origin(state, origin)
        },
        _ => state,
    };
    assert(production_core_control_body(forgotten)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(production_core_control_body);
    };
    assert(active_document_writes_exclude_certified_cache(forgotten)) by {
        reveal(crate::state::spec_forget_origin);
        reveal(crate::state::spec_note);
        reveal(crate::cache::spec_remove);
        reveal(active_document_writes_exclude_certified_cache);
    };
    match error {
        echod_concrete::store::StoreErrorSpec::PreconditionFailed => {
            let noted = crate::state::spec_note(
                crate::state::spec_note(
                    forgotten,
                    crate::types::NoteSpec::Commit(
                        crate::types::CommitOutcome::Raced,
                    ),
                ),
                crate::types::NoteSpec::Raced {
                    target: crate::target::spec_name(flight.target),
                    attempt: flight.attempt,
                },
            );
            assert(production_core_control_body(noted)) by {
                reveal(crate::state::spec_note);
                reveal(production_core_control_body);
            };
            assert(active_document_writes_exclude_certified_cache(
                noted,
            )) by {
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_retry_preserves_active_write_cache_exclusion(
                noted,
                flight,
            );
        },
        _ => {
            let noted = crate::state::spec_note(
                forgotten,
                crate::types::NoteSpec::Commit(
                    crate::types::CommitOutcome::Failed,
                ),
            );
            assert(production_core_control_body(noted)) by {
                reveal(crate::state::spec_note);
                reveal(production_core_control_body);
            };
            assert(active_document_writes_exclude_certified_cache(
                noted,
            )) by {
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_fail_preserves_active_write_cache_exclusion(
                noted,
                flight,
                crate::types::spec_error_text(error),
            );
        },
    }
    reveal(crate::handler_docs::spec_commit_failed);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_op_exhausted_preserves_active_write_cache_exclusion(
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_op_exhausted(state, flight),
        ),
{
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(active_document_writes_exclude_certified_cache);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_loaded_origin_preserves_active_write_cache_exclusion(
    state: S,
    origin: Seq<char>,
    revalidating: Option<crate::cache::CachedSpec>,
    response: echod_concrete::store::StoreRes,
)
    requires
        active_document_writes_exclude_certified_cache(state),
        revalidating is Some ==>
            forall|op: u64|
                state.ops.contains_key(op)
                    && state.store_certificates.contains_key(op)
                    && certificate_written_document(
                        state.store_certificates[op],
                    ) is Some
                    && revalidating.unwrap()
                        .loaded.append_certified ==>
                document_lane(
                    revalidating.unwrap().loaded.document,
                ) != document_lane(
                    certificate_written_document(
                        state.store_certificates[op],
                    ).unwrap(),
                ),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_loaded_origin(
                state,
                origin,
                revalidating,
                response,
            ).0,
        ),
{
    match revalidating {
        Some(cached) => match response {
            echod_concrete::store::StoreRes::GetIfNoneMatch {
                result: Ok(echod_concrete::store::Read::NotModified),
            } => {
                match crate::document::spec_validate_workflow_identity(
                    cached.loaded,
                    origin,
                ) {
                    Ok(loaded) => {
                        let noted = crate::state::spec_note(
                            state,
                            crate::types::NoteSpec::Cache(
                                crate::types::CacheResult::Revalidated,
                            ),
                        );
                        let refreshed = crate::cache::CachedSpec {
                            loaded,
                            filled_at: crate::state::spec_now(state),
                            ..cached
                        };
                        assert(active_document_writes_exclude_certified_cache(
                            noted,
                        )) by {
                            reveal(crate::state::spec_note);
                            reveal(active_document_writes_exclude_certified_cache);
                        };
                        assert forall|op: u64|
                            noted.ops.contains_key(op)
                                && noted.store_certificates.contains_key(op)
                                && certificate_written_document(
                                    noted.store_certificates[op],
                                ) is Some
                                && refreshed.loaded.append_certified
                            implies document_lane(
                                refreshed.loaded.document,
                            ) != document_lane(
                                certificate_written_document(
                                    noted.store_certificates[op],
                                ).unwrap(),
                            ) by {
                            reveal(crate::state::spec_note);
                            reveal(crate::document::spec_validate_workflow_identity);
                        };
                        lemma_cache_put_preserves_active_write_cache_exclusion(
                            noted,
                            origin,
                            refreshed,
                        );
                    },
                    Err(_) => {},
                }
            },
            echod_concrete::store::StoreRes::GetIfNoneMatch {
                result: Ok(echod_concrete::store::Read::Absent),
            } => {
                let noted = crate::state::spec_note(
                    state,
                    crate::types::NoteSpec::Cache(
                        crate::types::CacheResult::Absent,
                    ),
                );
                assert(active_document_writes_exclude_certified_cache(
                    noted,
                )) by {
                    reveal(crate::state::spec_note);
                    reveal(active_document_writes_exclude_certified_cache);
                };
                lemma_cache_remove_preserves_active_write_cache_exclusion(
                    noted,
                    origin,
                );
            },
            echod_concrete::store::StoreRes::GetIfNoneMatch {
                result: Ok(echod_concrete::store::Read::Body(bytes, etag)),
            } => {
                let noted = crate::state::spec_note(
                    state,
                    crate::types::NoteSpec::Cache(
                        crate::types::CacheResult::Refreshed,
                    ),
                );
                assert(active_document_writes_exclude_certified_cache(
                    noted,
                )) by {
                    reveal(crate::state::spec_note);
                    reveal(active_document_writes_exclude_certified_cache);
                };
                match crate::document::spec_decode_workflow(bytes@) {
                    Ok(decoded) => {
                        match crate::document::spec_validate_workflow_identity(
                            decoded,
                            origin,
                        ) {
                            Ok(loaded) => {
                                let refreshed = crate::cache::CachedSpec {
                                    loaded,
                                    etag: etag.deep_view(),
                                    filled_at: crate::state::spec_now(state),
                                };
                                assert(!refreshed.loaded.append_certified) by {
                                    reveal(crate::document::spec_validate_workflow_identity);
                                    crate::document::
                                        lemma_workflow_decode_success_is_well_formed(
                                            bytes@,
                                            decoded,
                                        );
                                };
                                lemma_cache_put_preserves_active_write_cache_exclusion(
                                    noted,
                                    origin,
                                    refreshed,
                                );
                            },
                            Err(_) => {},
                        }
                    },
                    Err(_) => {},
                }
            },
            _ => {},
        },
        None => match response {
            echod_concrete::store::StoreRes::Get {
                result: Ok(Some((bytes, etag))),
            } => {
                match crate::document::spec_decode_workflow(bytes@) {
                    Ok(decoded) => {
                        match crate::document::spec_validate_workflow_identity(
                            decoded,
                            origin,
                        ) {
                            Ok(loaded) => {
                                let refreshed = crate::cache::CachedSpec {
                                    loaded,
                                    etag: etag.deep_view(),
                                    filled_at: crate::state::spec_now(state),
                                };
                                assert(!refreshed.loaded.append_certified) by {
                                    reveal(crate::document::spec_validate_workflow_identity);
                                    crate::document::
                                        lemma_workflow_decode_success_is_well_formed(
                                            bytes@,
                                            decoded,
                                        );
                                };
                                lemma_cache_put_preserves_active_write_cache_exclusion(
                                    state,
                                    origin,
                                    refreshed,
                                );
                            },
                            Err(_) => {},
                        }
                    },
                    Err(_) => {},
                }
            },
            _ => {},
        },
    }
    reveal(crate::handler_docs::spec_loaded_origin);
    reveal(crate::document::spec_validate_workflow_identity);
    reveal(crate::state::spec_remember);
    reveal(crate::state::spec_forget_origin);
    reveal(crate::state::spec_note);
}

pub(crate) proof fn lemma_timer_fire_preserves_active_write_cache_exclusion(
    state: S,
    key: Seq<char>,
    at: u64,
    now: u64,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_timer_fire(
                state,
                key,
                at,
                now,
            ),
        ),
{
    reveal(crate::handler_timers::spec_timer_fire);
    match crate::keys::spec_parse_timer_key(key) {
        None => {
            reveal(crate::state::spec_note);
            reveal(active_document_writes_exclude_certified_cache);
        },
        Some(entry) => {
            if crate::handler_timers::spec_owns_entry(state, entry)
                && crate::verified::node_spec::spec_acts(
                    state.node.core,
                    entry.target(),
                    now as nat,
                )
            {
                let staged = crate::handler_timers::spec_with_timers(
                    state,
                    crate::state_timers::TimersSpec {
                        inflight:
                            state.timers.inflight.saturating_add(1),
                        ..state.timers
                    },
                );
                assert(production_core_control_body(staged)) by {
                    reveal(crate::handler_timers::spec_with_timers);
                    reveal(production_core_control_body);
                };
                assert(active_document_writes_exclude_certified_cache(
                    staged,
                )) by {
                    reveal(crate::handler_timers::spec_with_timers);
                    reveal(active_document_writes_exclude_certified_cache);
                };
                match entry {
                    crate::keys::TimerEntrySpec::Origin {
                        origin,
                        ..
                    } => {
                        lemma_submit_nonfire_preserves_active_write_cache_exclusion(
                            staged,
                            crate::target::TargetSpec::Origin(origin),
                            crate::handler_docs::WorkSpec::Sweep {
                                fired: Some(
                                    crate::verified::flight_spec::AFired {
                                        key:
                                            crate::verified::node_spec::AKey {
                                                origin: "w:"@ + origin,
                                                at: entry->Origin_deadline
                                                    as nat,
                                                token: entry->Origin_token
                                                    as nat,
                                            },
                                        by: entry->Origin_by,
                                    },
                                ),
                                now,
                            },
                            Some(crate::handler_docs::FiringSpec {
                                key,
                                at,
                                kind: crate::types::TimerKind::Origin,
                                lag: now.saturating_sub(at),
                            }),
                            false,
                        );
                    },
                    crate::keys::TimerEntrySpec::Schedule { id, .. } => {
                        lemma_submit_nonfire_preserves_active_write_cache_exclusion(
                            staged,
                            crate::target::TargetSpec::Schedule(id),
                            crate::handler_docs::WorkSpec::Fire {
                                schedule: id,
                                fired: Some(
                                    crate::verified::flight_spec::AFired {
                                        key:
                                            crate::verified::node_spec::AKey {
                                                origin: "s:"@ + id,
                                                at:
                                                    entry->Schedule_deadline
                                                        as nat,
                                                token:
                                                    entry->Schedule_token
                                                        as nat,
                                            },
                                        by: entry->Schedule_by,
                                    },
                                ),
                                now,
                            },
                            Some(crate::handler_docs::FiringSpec {
                                key,
                                at,
                                kind:
                                    crate::types::TimerKind::Schedule,
                                lag: now.saturating_sub(at),
                            }),
                            false,
                        );
                    },
                }
            } else {
                reveal(crate::handler_timers::spec_with_timers);
                reveal(crate::state::spec_note);
                reveal(active_document_writes_exclude_certified_cache);
            }
        },
    }
}

pub(crate) proof fn lemma_dispatch_due_preserves_active_write_cache_exclusion(
    state: S,
    now: u64,
    fuel: nat,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_dispatch_due(state, now, fuel),
        ),
    decreases fuel,
{
    reveal_with_fuel(crate::handler_timers::spec_dispatch_due, 1);
    if fuel > 0
        && state.timers.inflight
            < crate::state_timers::CONCURRENCY
        && state.timers.backlog.len() > 0
    {
        let staged = crate::handler_timers::spec_with_timers(
            state,
            crate::state_timers::TimersSpec {
                backlog: state.timers.backlog.drop_first(),
                ..state.timers
            },
        );
        assert(production_core_control_body(staged)) by {
            reveal(crate::handler_timers::spec_with_timers);
            reveal(production_core_control_body);
        };
        assert(active_document_writes_exclude_certified_cache(staged)) by {
            reveal(crate::handler_timers::spec_with_timers);
            reveal(active_document_writes_exclude_certified_cache);
        };
        lemma_timer_fire_preserves_active_write_cache_exclusion(
            staged,
            state.timers.backlog[0].1,
            state.timers.backlog[0].0,
            now,
        );
        let fired = crate::handler_timers::spec_timer_fire(
            staged,
            state.timers.backlog[0].1,
            state.timers.backlog[0].0,
            now,
        );
        lemma_timer_fire_preserves_core_control_body(
            staged,
            state.timers.backlog[0].1,
            state.timers.backlog[0].0,
            now,
        );
        lemma_dispatch_due_preserves_active_write_cache_exclusion(
            fired,
            now,
            (fuel - 1) as nat,
        );
    }
}

pub(crate) proof fn lemma_timers_run_preserves_active_write_cache_exclusion(
    state: S,
    now: u64,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_timers_run(state, now),
        ),
{
    reveal(crate::handler_timers::spec_timers_run);
    if state.timers.started
        && !(state.timers.listing is Some)
        && !(state.timers.backoff_until is Some
            && now < state.timers.backoff_until->Some_0)
    {
        let staged = crate::handler_timers::spec_with_timers(
            state,
            crate::state_timers::TimersSpec {
                backoff_until: None,
                ..state.timers
            },
        );
        assert(production_core_control_body(staged)) by {
            reveal(crate::handler_timers::spec_with_timers);
            reveal(production_core_control_body);
        };
        assert(active_document_writes_exclude_certified_cache(staged)) by {
            reveal(crate::handler_timers::spec_with_timers);
            reveal(active_document_writes_exclude_certified_cache);
        };
        if staged.timers.reload_pending {
            reveal(crate::handler_timers::spec_reload);
            let filtered = crate::handler_timers::spec_with_timers(
                staged,
                crate::state_timers::TimersSpec {
                    wheel: crate::state_timers::TimerWheelSpec {
                        armed: staged.timers.wheel.armed.filter(
                            |k: crate::state_timers::SlotSpec|
                                crate::handler_timers::spec_owns_key(
                                    staged,
                                    k.1,
                                ),
                        ),
                    },
                    ..staged.timers
                },
            );
            assert(production_core_control_body(filtered)) by {
                reveal(crate::handler_timers::spec_with_timers);
                reveal(production_core_control_body);
            };
            assert(active_document_writes_exclude_certified_cache(
                filtered,
            )) by {
                reveal(crate::handler_timers::spec_with_timers);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_control_store_preserves_active_write_cache_exclusion(
                filtered,
                StoreReqSpec::ListPrefixes {
                    prefix: crate::keys::spec_timer_prefix(
                        filtered.keys.prefix,
                    ),
                },
                Owner::Timers,
            );
            reveal(crate::handler_timers::spec_with_timers);
        } else if staged.timers.loaded_through is Some
            && staged.timers.loaded_through->Some_0
                < crate::handler_timers::spec_horizon(staged, now)
        {
            let bucket = staged.timers.loaded_through->Some_0
                .saturating_add(staged.keys.bucket_ms);
            lemma_control_store_preserves_active_write_cache_exclusion(
                staged,
                StoreReqSpec::List {
                    prefix: crate::keys::spec_bucket_prefix(
                        staged.keys.prefix,
                        bucket,
                    ),
                    max_keys: usize::MAX,
                },
                Owner::Timers,
            );
            reveal(crate::handler_timers::spec_with_timers);
        } else if staged.timers.closed_through is Some
            && staged.timers.closed_through->Some_0
                .saturating_add(staged.keys.bucket_ms)
                < crate::keys::spec_bucket_of(
                    now,
                    staged.keys.bucket_ms,
                )
        {
            let bucket = staged.timers.closed_through->Some_0
                .saturating_add(staged.keys.bucket_ms);
            lemma_control_store_preserves_active_write_cache_exclusion(
                staged,
                StoreReqSpec::List {
                    prefix: crate::keys::spec_bucket_prefix(
                        staged.keys.prefix,
                        bucket,
                    ),
                    max_keys: usize::MAX,
                },
                Owner::Timers,
            );
            reveal(crate::handler_timers::spec_with_timers);
        } else if staged.timers.loaded_through is Some {
            reveal(crate::handler_timers::spec_fire_due);
            let due = crate::state_timers::spec_take_due(
                staged.timers.wheel.armed,
                now,
            );
            let due_staged =
                crate::handler_timers::spec_with_timers(
                    staged,
                    crate::state_timers::TimersSpec {
                        wheel:
                            crate::state_timers::TimerWheelSpec {
                                armed: due.1,
                            },
                        backlog: staged.timers.backlog + due.0,
                        ..staged.timers
                    },
                );
            assert(production_core_control_body(due_staged)) by {
                reveal(crate::handler_timers::spec_with_timers);
                reveal(production_core_control_body);
            };
            assert(active_document_writes_exclude_certified_cache(
                due_staged,
            )) by {
                reveal(crate::handler_timers::spec_with_timers);
                reveal(active_document_writes_exclude_certified_cache);
            };
            lemma_dispatch_due_preserves_active_write_cache_exclusion(
                due_staged,
                now,
                due_staged.timers.backlog.len(),
            );
        }
    }
}

pub(crate) proof fn lemma_answered_commit_preserves_cache_identity(
    core: S,
    commit: crate::handler_docs::CommittingSpec,
    answer: echod_concrete::store::StoreRes,
)
    requires
        commit_static_provenance(core, commit),
        commit_issued_phase_provenance(commit),
        cache_identity_provenance(core),
        commit.issued is Some,
    ensures
        cache_identity_provenance(
            crate::handler_docs::spec_answered(
                core,
                crate::handler_docs::CommittingSpec {
                    issued: None,
                    ..commit
                },
                commit.issued.unwrap(),
                Some(answer),
            ).0,
        ),
{
    let unanswered = crate::handler_docs::CommittingSpec {
        issued: None,
        ..commit
    };
    let answered = crate::handler_docs::spec_answered(
        core,
        unanswered,
        commit.issued.unwrap(),
        Some(answer),
    ).0;
    match commit.issued.unwrap() {
        crate::handler_docs::IssuedSpec::Write {
            mode,
            change_count,
            bytes,
            len,
            ..
        } => match answer {
            echod_concrete::store::StoreRes::PutIfMatch {
                result: Ok(etag),
            }
            | echod_concrete::store::StoreRes::PutIfNoneMatch {
                result: Ok(etag),
            }
            | echod_concrete::store::StoreRes::AppIfMatch {
                result: Ok(etag),
            } => {
                if commit.after is Workflow {
                    let noted = crate::state::spec_note(
                        core,
                        crate::types::NoteSpec::DocumentWrite {
                            mode,
                            bytes: len,
                        },
                    );
                    let cached = crate::cache::CachedSpec {
                        loaded: crate::document::LoadedSpec {
                            document: commit.after,
                            change_count,
                            bytes,
                            append_certified: true,
                        },
                        etag: etag.deep_view(),
                        filled_at: crate::state::spec_now(core),
                    };
                    assert(crate::document::loaded_workflow_has_identity(
                        cached.loaded,
                        commit.w.target,
                    )) by {
                        reveal(crate::document::loaded_workflow_has_identity);
                        reveal(commit_static_provenance);
                        reveal(working_document_provenance);
                        reveal(working_matches_target);
                    };
                    assert(cache_identity_provenance(noted)) by {
                        reveal(crate::state::spec_note);
                        reveal(cache_identity_provenance);
                    };
                    lemma_remember_preserves_cache_identity(
                        noted,
                        commit.w.target,
                        cached,
                    );
                }
            },
            _ => {},
        },
        _ => {},
    }
    reveal(crate::handler_docs::spec_answered);
    reveal(crate::state::spec_note);
    reveal(crate::state::spec_remember);
    reveal(cache_identity_provenance);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_initial_commit_advance_preserves_remembered_timer_lanes(
    core: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
)
    requires
        remembered_timer_lanes_consistent(core),
        commit_sequence_provenance(commit),
        crate::verified::commit_spec::spec_is_commit_lane_name(
            commit.seq.origin,
        ),
        commit.issued is None,
    ensures
        remembered_timer_lanes_consistent(
            crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                None,
            ).0,
        ),
{
    reveal(commit_sequence_provenance);
    reveal(crate::handler_docs::spec_commit_sequence_origin);
    let allocated =
        crate::handler_docs::spec_allocate_arm_token(core, commit);
    assert(remembered_timer_lanes_consistent(allocated.0)) by {
        reveal(crate::handler_docs::spec_allocate_arm_token);
        reveal(crate::state::spec_token);
        reveal(remembered_timer_lanes_consistent);
    };
    let sequence = allocated.1.seq;
    let node = allocated.0.node.core;
    assert(sequence.origin == commit.seq.origin) by {
        reveal(crate::handler_docs::spec_allocate_arm_token);
        reveal(crate::state::spec_token);
    };
    assert(sequence.plan == commit.seq.plan) by {
        reveal(crate::handler_docs::spec_allocate_arm_token);
        reveal(crate::state::spec_token);
    };
    if allocated.2 {
        assert(crate::verified::commit_spec::spec_is_commit_lane_name(
            sequence.origin,
        ));
        assert(crate::verified::commit_spec::spec_keep(
            sequence.plan,
        ) is Some ==> crate::verified::commit_spec::spec_keep(
            sequence.plan,
        ).unwrap().origin == sequence.origin);
        lemma_sequence_advance_preserves_remembered_timer_lanes(
            node,
            sequence,
            None,
        );
    }
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    let advanced = crate::handler_docs::spec_commit_advance(
        core,
        fid,
        commit,
        None,
    ).0;
    if allocated.2 {
        let sequence_advanced =
            crate::verified::flight_spec::spec_advance(
                sequence,
                node,
                crate::verified::flight_spec::answer_v(
                    sequence.step,
                    None,
                ),
            );
        match sequence_advanced.2 {
            crate::verified::flight_spec::AOutcome::Act(
                crate::verified::flight_spec::AAct::PutKey(_),
            )
            | crate::verified::flight_spec::AOutcome::Act(
                crate::verified::flight_spec::AAct::Write { .. },
            )
            | crate::verified::flight_spec::AOutcome::Act(
                crate::verified::flight_spec::AAct::DeleteKey { .. },
            )
            | crate::verified::flight_spec::AOutcome::Act(
                crate::verified::flight_spec::AAct::Done { .. },
            )
            | crate::verified::flight_spec::AOutcome::Failed(_) => {},
        }
        assert(advanced.node.core == sequence_advanced.1);
    } else {
        assert(advanced.node.core == allocated.0.node.core);
    }
    assert(remembered_timer_lanes_consistent_node(
        advanced.node.core,
    )) by {
        if allocated.2 {
            let sequence_advanced =
                crate::verified::flight_spec::spec_advance(
                    sequence,
                    node,
                    crate::verified::flight_spec::answer_v(
                        sequence.step,
                        None,
                    ),
                );
            assert(remembered_timer_lanes_consistent_node(
                sequence_advanced.1,
            ));
        } else {
            assert(remembered_timer_lanes_consistent(allocated.0));
        }
    };
    assert(remembered_timer_lanes_consistent(advanced)) by {
        reveal(remembered_timer_lanes_consistent);
    };
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_detached_answered_preserves_active_write_cache_exclusion(
    core: S,
    fid: u64,
    target: crate::target::TargetSpec,
    commit: crate::handler_docs::CommittingSpec,
    answer: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(core),
        retained_commit_provenance(core),
        active_document_writes_exclude_certified_cache(core),
        !core.flights.inflight.contains_key(fid),
        commit_candidate_provenance(core, fid, target, commit),
        commit.issued is Some,
        core.flights.slots.contains_key(
            crate::target::spec_name(target),
        ),
        core.flights.slots[
            crate::target::spec_name(target)
        ].busy == Some(fid),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_answered(
                core,
                crate::handler_docs::CommittingSpec {
                    issued: None,
                    ..commit
                },
                commit.issued.unwrap(),
                Some(answer),
            ).0,
        ),
{
    let lane = crate::target::spec_name(target);
    lemma_commit_candidate_document_lane_matches_target(
        core,
        fid,
        target,
        commit,
    );
    match commit.issued.unwrap() {
        crate::handler_docs::IssuedSpec::Key { .. } => {
            let answered = crate::handler_docs::spec_answered(
                core,
                crate::handler_docs::CommittingSpec {
                    issued: None,
                    ..commit
                },
                commit.issued.unwrap(),
                Some(answer),
            ).0;
            assert(answered.cache == core.cache) by {
                reveal(crate::handler_docs::spec_answered);
                reveal(crate::state::spec_note);
            };
            assert forall|op: u64|
                answered.ops.contains_key(op)
                    && answered.store_certificates.contains_key(op)
                    && certificate_written_document(
                        answered.store_certificates[op],
                    ) is Some implies {
                        &&& core.ops.contains_key(op)
                        &&& core.store_certificates.contains_key(op)
                        &&& core.store_certificates[op]
                            == answered.store_certificates[op]
                    } by {
                reveal(crate::handler_docs::spec_answered);
                reveal(crate::state::spec_note);
            };
            lemma_active_write_cache_exclusion_frames(
                core,
                answered,
            );
        },
        crate::handler_docs::IssuedSpec::Write { .. } => {
            match answer {
                echod_concrete::store::StoreRes::PutIfMatch {
                    result: Ok(etag),
                }
                | echod_concrete::store::StoreRes::PutIfNoneMatch {
                    result: Ok(etag),
                }
                | echod_concrete::store::StoreRes::AppIfMatch {
                    result: Ok(etag),
                } => {
                    let noted = crate::state::spec_note(
                        core,
                        crate::types::NoteSpec::DocumentWrite {
                            mode: commit.issued.unwrap()->Write_mode,
                            bytes: commit.issued.unwrap()->Write_len,
                        },
                    );
                    assert(noted.cache == core.cache);
                    assert forall|op: u64|
                        noted.ops.contains_key(op)
                            && noted.store_certificates.contains_key(op)
                            && certificate_written_document(
                                noted.store_certificates[op],
                            ) is Some implies {
                                &&& core.ops.contains_key(op)
                                &&& core.store_certificates.contains_key(op)
                                &&& core.store_certificates[op]
                                    == noted.store_certificates[op]
                            } by {
                        reveal(crate::state::spec_note);
                    };
                    lemma_active_write_cache_exclusion_frames(
                        core,
                        noted,
                    );
                    if commit.after is Workflow {
                        let cached = crate::cache::CachedSpec {
                            loaded: crate::document::LoadedSpec {
                                document: commit.after,
                                change_count: commit.issued.unwrap()
                                    ->Write_change_count,
                                bytes: commit.issued.unwrap()->Write_bytes,
                                append_certified: true,
                            },
                            etag: etag.deep_view(),
                            filled_at: crate::state::spec_now(noted),
                        };
                        assert forall|op: u64|
                            noted.ops.contains_key(op)
                                && noted.store_certificates.contains_key(op)
                                && certificate_written_document(
                                    noted.store_certificates[op],
                                ) is Some
                            implies document_lane(cached.loaded.document)
                                != document_lane(
                                    certificate_written_document(
                                        noted.store_certificates[op],
                                    ).unwrap(),
                                ) by {
                            lemma_active_document_write_differs_from_detached_owned_lane(
                                core,
                                op,
                                fid,
                                lane,
                            );
                            assert(document_lane(cached.loaded.document)
                                == lane);
                        };
                        lemma_cache_put_preserves_active_write_cache_exclusion(
                            noted,
                            commit.w.target,
                            cached,
                        );
                    }
                },
                _ => {},
            }
            reveal(crate::handler_docs::spec_answered);
            reveal(crate::state::spec_note);
            reveal(crate::state::spec_remember);
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_detached_commit_advance_preserves_active_write_cache_exclusion(
    core: S,
    fid: u64,
    target: crate::target::TargetSpec,
    commit: crate::handler_docs::CommittingSpec,
    answer: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(core),
        retained_commit_provenance(core),
        cache_identity_provenance(core),
        active_document_writes_exclude_certified_cache(core),
        !core.flights.inflight.contains_key(fid),
        commit_candidate_provenance(core, fid, target, commit),
        commit.issued is Some,
        core.flights.slots.contains_key(
            crate::target::spec_name(target),
        ),
        core.flights.slots[
            crate::target::spec_name(target)
        ].busy == Some(fid),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                Some(answer),
            ).0,
        ),
{
    lemma_detached_answered_preserves_active_write_cache_exclusion(
        core,
        fid,
        target,
        commit,
        answer,
    );
    lemma_answered_commit_preserves_cache_identity(
        core,
        commit,
        answer,
    );
    lemma_commit_advance_preserves_cache_identity(
        core,
        fid,
        commit,
        Some(answer),
    );
    lemma_commit_candidate_document_lane_matches_target(
        core,
        fid,
        target,
        commit,
    );
    lemma_commit_advance_preserves_provenance(
        core,
        fid,
        target,
        commit,
        Some(answer),
    );
    let unanswered = crate::handler_docs::CommittingSpec {
        issued: None,
        ..commit
    };
    let answered_pair = crate::handler_docs::spec_answered(
        core,
        unanswered,
        commit.issued.unwrap(),
        Some(answer),
    );
    let answered = answered_pair.0;
    let allocated = crate::handler_docs::spec_allocate_arm_token(
        answered,
        answered_pair.1,
    );
    if allocated.2 {
        let sequence_advanced =
            crate::verified::flight_spec::spec_advance(
                allocated.1.seq,
                allocated.0.node.core,
                crate::verified::flight_spec::answer_v(
                    allocated.1.seq.step,
                    Some(answer),
                ),
            );
        let advanced_state = S {
            node: crate::state_node::NodeSpec {
                core: sequence_advanced.1,
                ..allocated.0.node
            },
            ..allocated.0
        };
        let advanced_commit = crate::handler_docs::CommittingSpec {
            seq: sequence_advanced.0,
            ..allocated.1
        };
        assert(active_document_writes_exclude_certified_cache(
            allocated.0,
        )) by {
            lemma_active_write_cache_exclusion_frames(
                answered,
                allocated.0,
            );
        };
        assert(active_document_writes_exclude_certified_cache(
            advanced_state,
        )) by {
            lemma_active_write_cache_exclusion_frames(
                allocated.0,
                advanced_state,
            );
        };
        match sequence_advanced.2 {
            crate::verified::flight_spec::AOutcome::Act(
                crate::verified::flight_spec::AAct::Write {
                    cond,
                    idle,
                },
            ) => {
                assert(production_core_control_body(advanced_state)) by {
                    reveal(production_core_control_body);
                    reveal(crate::production_relation::operation_allocator_consistent);
                    reveal(crate::handler_docs::spec_answered);
                    reveal(crate::handler_docs::spec_allocate_arm_token);
                    reveal(crate::state::spec_note);
                    reveal(crate::state::spec_remember);
                    reveal(crate::state::spec_token);
                    reveal(crate::verified::flight_spec::spec_advance);
                };
                assert(cache_identity_provenance(advanced_state)) by {
                    reveal(cache_identity_provenance);
                    reveal(crate::handler_docs::spec_allocate_arm_token);
                    reveal(crate::verified::flight_spec::spec_advance);
                };
                assert(match advanced_commit.after {
                    StoredDocumentV::Workflow(_) =>
                        document_lane(advanced_commit.after)
                            == crate::target::spec_name(
                                crate::target::TargetSpec::Origin(
                                    advanced_commit.w.target,
                                ),
                            ),
                    StoredDocumentV::Schedule(schedule) =>
                        document_lane(advanced_commit.after)
                            == crate::target::spec_name(
                                crate::target::TargetSpec::Schedule(
                                    schedule.document,
                                ),
                            ),
                }) by {
                    reveal(crate::handler_docs::spec_answered);
                    reveal(crate::handler_docs::spec_allocate_arm_token);
                };
                lemma_issue_write_preserves_active_write_cache_exclusion(
                    advanced_state,
                    fid,
                    advanced_commit,
                    cond,
                    idle,
                );
            },
            _ => {},
        }
    }
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_allocate_arm_token);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::verified::flight_spec::spec_advance);
    reveal(certificate_written_document);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_initial_commit_advance_preserves_active_write_cache_exclusion(
    core: S,
    fid: u64,
    target: crate::target::TargetSpec,
    commit: crate::handler_docs::CommittingSpec,
)
    requires
        production_core_control_body(core),
        cache_identity_provenance(core),
        active_document_writes_exclude_certified_cache(core),
        commit_candidate_provenance(core, fid, target, commit),
        commit.issued is None,
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                None,
            ).0,
        ),
{
    lemma_commit_candidate_document_lane_matches_target(
        core,
        fid,
        target,
        commit,
    );
    let allocated = crate::handler_docs::spec_allocate_arm_token(
        core,
        commit,
    );
    if allocated.2 {
        let sequence_advanced =
            crate::verified::flight_spec::spec_advance(
                allocated.1.seq,
                allocated.0.node.core,
                crate::verified::flight_spec::answer_v(
                    allocated.1.seq.step,
                    None,
                ),
            );
        let advanced_state = S {
            node: crate::state_node::NodeSpec {
                core: sequence_advanced.1,
                ..allocated.0.node
            },
            ..allocated.0
        };
        let advanced_commit = crate::handler_docs::CommittingSpec {
            seq: sequence_advanced.0,
            ..allocated.1
        };
        assert(active_document_writes_exclude_certified_cache(
            allocated.0,
        )) by {
            lemma_active_write_cache_exclusion_frames(
                core,
                allocated.0,
            );
        };
        assert(active_document_writes_exclude_certified_cache(
            advanced_state,
        )) by {
            lemma_active_write_cache_exclusion_frames(
                allocated.0,
                advanced_state,
            );
        };
        match sequence_advanced.2 {
            crate::verified::flight_spec::AOutcome::Act(
                crate::verified::flight_spec::AAct::Write {
                    cond,
                    idle,
                },
            ) => {
                assert(production_core_control_body(advanced_state)) by {
                    reveal(production_core_control_body);
                    reveal(crate::production_relation::operation_allocator_consistent);
                    reveal(crate::handler_docs::spec_allocate_arm_token);
                    reveal(crate::state::spec_token);
                    reveal(crate::verified::flight_spec::spec_advance);
                };
                assert(cache_identity_provenance(advanced_state)) by {
                    reveal(cache_identity_provenance);
                    reveal(crate::handler_docs::spec_allocate_arm_token);
                    reveal(crate::verified::flight_spec::spec_advance);
                };
                assert(match advanced_commit.after {
                    StoredDocumentV::Workflow(_) =>
                        document_lane(advanced_commit.after)
                            == crate::target::spec_name(
                                crate::target::TargetSpec::Origin(
                                    advanced_commit.w.target,
                                ),
                            ),
                    StoredDocumentV::Schedule(schedule) =>
                        document_lane(advanced_commit.after)
                            == crate::target::spec_name(
                                crate::target::TargetSpec::Schedule(
                                    schedule.document,
                                ),
                            ),
                }) by {
                    reveal(crate::handler_docs::spec_allocate_arm_token);
                };
                lemma_issue_write_preserves_active_write_cache_exclusion(
                    advanced_state,
                    fid,
                    advanced_commit,
                    cond,
                    idle,
                );
            },
            _ => {},
        }
    }
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_allocate_arm_token);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::verified::flight_spec::spec_advance);
    reveal(certificate_written_document);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_initial_commit_advance_write_certificate_lane_with_key(
    core: S,
    fid: u64,
    target: crate::target::TargetSpec,
    commit: crate::handler_docs::CommittingSpec,
    key: crate::verified::node_spec::AKey,
)
    requires
        commit_candidate_provenance(core, fid, target, commit),
        commit.issued is None,
        commit.seq.step is Start,
        crate::verified::commit_spec::spec_keep(commit.seq.plan)
            == Some(key),
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                None,
            );
            &&& advanced.2 is Issued
            &&& advanced.1.issued is Some
            &&& advanced.1.issued.unwrap() is Write
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                None,
            );
            let op = advanced.1.expects().unwrap();
            &&& certificate_lane_name(
                advanced.0.store_certificates[op],
            ) == Some(crate::target::spec_name(target))
            &&& certificate_lane_consistent(
                advanced.0.store_certificates[op],
            )
        }),
{
    lemma_commit_candidate_document_lane_matches_target(
        core,
        fid,
        target,
        commit,
    );
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_allocate_arm_token);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::verified::flight_spec::spec_advance);
    reveal(crate::verified::commit_spec::spec_keep);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(commit_candidate_provenance);
    reveal(commit_static_provenance);
    reveal(commit_sequence_provenance);
    reveal(certificate_lane_name);
    reveal(certificate_lane_consistent);
    reveal(certificate_required_timer);
    reveal(certificate_put_timer);
    reveal(certificate_deleted_timer);
    reveal(certificate_timer_key_lane);
    lemma_key_name_is_certificate_timer(
        core,
        key,
        core.node.core.id,
    );
    lemma_certificate_timer_name_has_lane(
        core.keys.prefix,
        core.keys.bucket_ms,
        key,
        crate::state::spec_key_name(
            core,
            key,
            core.node.core.id,
        ),
    );
    lemma_canonical_target_is_timer_key_lane(target, key);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_initial_commit_advance_write_certificate_lane_without_key(
    core: S,
    fid: u64,
    target: crate::target::TargetSpec,
    commit: crate::handler_docs::CommittingSpec,
)
    requires
        commit_candidate_provenance(core, fid, target, commit),
        commit.issued is None,
        commit.seq.step is Start,
        crate::verified::commit_spec::spec_keep(commit.seq.plan) is None,
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                None,
            );
            &&& advanced.2 is Issued
            &&& advanced.1.issued is Some
            &&& advanced.1.issued.unwrap() is Write
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                None,
            );
            let op = advanced.1.expects().unwrap();
            &&& certificate_lane_name(
                advanced.0.store_certificates[op],
            ) == Some(crate::target::spec_name(target))
            &&& certificate_lane_consistent(
                advanced.0.store_certificates[op],
            )
        }),
{
    lemma_commit_candidate_document_lane_matches_target(
        core,
        fid,
        target,
        commit,
    );
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_allocate_arm_token);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::verified::flight_spec::spec_advance);
    reveal(crate::verified::commit_spec::spec_keep);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(commit_candidate_provenance);
    reveal(commit_static_provenance);
    reveal(commit_sequence_provenance);
    reveal(certificate_lane_name);
    reveal(certificate_lane_consistent);
    reveal(certificate_required_timer);
    reveal(certificate_put_timer);
    reveal(certificate_deleted_timer);
    reveal(certificate_timer_key_lane);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_initial_commit_advance_write_certificate_lane_branch(
    core: S,
    fid: u64,
    target: crate::target::TargetSpec,
    commit: crate::handler_docs::CommittingSpec,
)
    requires
        commit_candidate_provenance(core, fid, target, commit),
        commit.issued is None,
        commit.seq.step is Start,
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                None,
            );
            &&& advanced.2 is Issued
            &&& advanced.1.issued is Some
            &&& advanced.1.issued.unwrap() is Write
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                None,
            );
            let op = advanced.1.expects().unwrap();
            &&& certificate_lane_name(
                advanced.0.store_certificates[op],
            ) == Some(crate::target::spec_name(target))
            &&& certificate_lane_consistent(
                advanced.0.store_certificates[op],
            )
        }),
{
    match crate::verified::commit_spec::spec_keep(commit.seq.plan) {
        Some(key) => {
            lemma_initial_commit_advance_write_certificate_lane_with_key(
                core,
                fid,
                target,
                commit,
                key,
            );
        },
        None => {
            lemma_initial_commit_advance_write_certificate_lane_without_key(
                core,
                fid,
                target,
                commit,
            );
        },
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_initial_commit_advance_write_operation_branch(
    core: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
)
    requires
        commit_static_provenance(core, commit),
        commit.issued is None,
        commit.seq.step is Start,
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                core, fid, commit, None,
            );
            &&& advanced.2 is Issued
            &&& advanced.1.issued is Some
            &&& advanced.1.issued.unwrap() is Write
        }),
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                core, fid, commit, None,
            );
            commit_issued_operation_provenance(
                advanced.0, fid, advanced.1,
            )
        }),
{
    reveal(crate::handler_docs::spec_commit_advance);
    reveal(crate::handler_docs::spec_allocate_arm_token);
    reveal(crate::handler_docs::spec_issue_write);
    reveal(crate::verified::flight_spec::spec_advance);
    reveal(crate::state::spec_token);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(commit_static_provenance);
    reveal(commit_issued_phase_provenance);
    reveal(commit_sequence_provenance);
    reveal(commit_issued_operation_provenance);
    reveal(certificate_belongs_to_commit);
    reveal(working_document_provenance);
    reveal(document_key);
    reveal(echod_concrete::node::spec_advance_stored);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_detached_initial_commit_advance_frames_retained_provenance(
    core: S,
    fid: u64,
    target: crate::target::TargetSpec,
    commit: crate::handler_docs::CommittingSpec,
)
    requires
        production_core_control_body(core),
        retained_commit_provenance(core),
        !core.flights.inflight.contains_key(fid),
        commit_candidate_provenance(core, fid, target, commit),
        commit.issued is None,
        commit.seq.step is Start,
    ensures
        ({
            let advanced = crate::handler_docs::spec_commit_advance(
                core,
                fid,
                commit,
                None,
            );
            &&& retained_commit_provenance(advanced.0)
            &&& advanced.0.keys == core.keys
        }),
{
    lemma_target_name_is_commit_lane(target);
    assert(commit.seq.origin == crate::target::spec_name(target)) by {
        reveal(commit_candidate_provenance);
        reveal(commit_static_provenance);
        reveal(commit_sequence_provenance);
        reveal(crate::handler_docs::spec_commit_sequence_origin);
        reveal(working_matches_target);
        reveal(working_document_provenance);
        match (target, commit.w.loaded.document) {
            (
                crate::target::TargetSpec::Origin(_),
                StoredDocumentV::Workflow(_),
            ) => {},
            (
                crate::target::TargetSpec::Schedule(_),
                StoredDocumentV::Schedule(_),
            ) => {},
            _ => assert(false),
        }
    };
    lemma_initial_commit_advance_preserves_remembered_timer_lanes(
        core,
        fid,
        commit,
    );
    lemma_commit_advance_frames_keys_and_flights(
        core,
        fid,
        commit,
        None,
    );
    lemma_commit_advance_preserves_old_operations(
        core,
        fid,
        commit,
        None,
    );
    reveal(retained_commit_provenance);
    reveal(phase_commit_provenance);
    reveal(commit_provenance);
    reveal(commit_attachable_provenance);
    reveal(commit_candidate_provenance);
    reveal(commit_static_provenance);
    reveal(commit_issued_operation_provenance);
    let advanced = crate::handler_docs::spec_commit_advance(
        core,
        fid,
        commit,
        None,
    );
    assert(advanced.0.flights == core.flights);
    assert forall|other: u64|
        advanced.0.flights.inflight.contains_key(other) implies
            phase_commit_provenance(
                advanced.0,
                other,
                advanced.0.flights.inflight[other].phase,
            ) by {
        assert(core.flights.inflight.contains_key(other));
        assert(other != fid);
        assert(phase_commit_provenance(
            core,
            other,
            core.flights.inflight[other].phase,
        ));
    };
}

pub(crate) proof fn lemma_active_write_cache_exclusion_frames(
    before: S,
    after: S,
)
    requires
        active_document_writes_exclude_certified_cache(before),
        after.cache == before.cache,
        forall|op: u64|
            after.ops.contains_key(op)
                && after.store_certificates.contains_key(op)
                && certificate_written_document(
                    after.store_certificates[op],
                ) is Some ==> {
                    &&& before.ops.contains_key(op)
                    &&& before.store_certificates.contains_key(op)
                    &&& before.store_certificates[op]
                        == after.store_certificates[op]
                },
    ensures
        active_document_writes_exclude_certified_cache(after),
{
    reveal(active_document_writes_exclude_certified_cache);
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_members_refresh_preserves_active_write_cache_exclusion(
    state: S,
    now: u64,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_members_refresh(state, now),
        ),
{
    reveal(crate::handler_node::spec_members_refresh);
    if !state.node.members.refreshing() {
        let me = crate::state_node::AnnouncementSpec {
            at: now,
            ..state.node.members.me
        };
        let staged = crate::handler_node::spec_with_members(
            state,
            crate::state_node::MembersSpec {
                me,
                ..state.node.members
            },
        );
        lemma_control_field_frame_preserves_active_write_cache_exclusion(
            state,
            staged,
        );
        lemma_members_field_update_preserves_core_control_body(
            state,
            staged.node.members,
        );
        let request = StoreReqSpec::Put {
            key: crate::keys::spec_node_key(
                staged.keys.prefix,
                me.id,
            ),
            body: crate::state_node::spec_announcement_bytes(me),
        };
        lemma_node_key_is_not_document_or_timer(
            staged.keys.prefix,
            me.id,
        );
        assert(certificate_matches_request(
            staged.keys.prefix,
            staged.keys.bucket_ms,
            request,
            StoreEffectCertificateV::Other,
        )) by {
            reveal(certificate_matches_request);
        };
        lemma_control_store_preserves_active_write_cache_exclusion(
            staged,
            request,
            Owner::Members,
        );
        lemma_nonflight_store_issue_preserves_core_control_body(
            staged,
            request,
            Owner::Members,
        );
        let issued = crate::state::spec_store(
            staged,
            request,
            Owner::Members,
        );
        match issued.1 {
            Some(_) => {
                let next = crate::handler_node::spec_with_members(
                    issued.0,
                    crate::state_node::MembersSpec {
                        refresh: Some(
                            crate::state_node::RefreshSpec::Announcing {
                                op: issued.1.unwrap(),
                                now,
                            },
                        ),
                        ..issued.0.node.members
                    },
                );
                lemma_control_field_frame_preserves_active_write_cache_exclusion(
                    issued.0,
                    next,
                );
            },
            None => {
                lemma_refresh_ended_preserves_active_write_cache_exclusion(
                    issued.0,
                    Err(crate::types::spec_exhausted()),
                );
            },
        }
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn lemma_members_tick_preserves_active_write_cache_exclusion(
    state: S,
    now: u64,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_members_tick(state, now),
        ),
{
    reveal(crate::handler_node::spec_members_tick);
    let due = match state.node.members.next_heartbeat {
        Some(t) => t <= now,
        None => true,
    };
    if !state.node.members.refreshing() && due {
        lemma_members_refresh_preserves_active_write_cache_exclusion(
            state,
            now,
        );
    }
}

pub(crate) proof fn lemma_event_prepared_preserves_active_write_cache_exclusion(
    state: S,
    clock: u64,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            spec_event_prepared(state, clock),
        ),
{
    reveal(spec_event_prepared);
    let clocked = S { clock, ..state };
    assert(active_document_writes_exclude_certified_cache(clocked)) by {
        reveal(active_document_writes_exclude_certified_cache);
    };
    assert(production_core_control_body(clocked)) by {
        reveal(production_core_control_body);
    };
    if clocked.node.members.next_heartbeat is None
        && !clocked.node.members.refreshing()
    {
        lemma_members_tick_preserves_active_write_cache_exclusion(
            clocked,
            crate::state::spec_now(clocked),
        );
    }
}

pub(crate) proof fn lemma_control_store_preserves_active_write_cache_exclusion(
    state: S,
    request: StoreReqSpec,
    owner: Owner,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::state::spec_store(state, request, owner).0,
        ),
{
    let next = crate::state::spec_store(state, request, owner).0;
    assert(next.cache == state.cache) by {
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
    };
    assert forall|op: u64|
        next.ops.contains_key(op)
            && next.store_certificates.contains_key(op)
            && certificate_written_document(
                next.store_certificates[op],
            ) is Some implies {
                &&& state.ops.contains_key(op)
                &&& state.store_certificates.contains_key(op)
                &&& state.store_certificates[op]
                    == next.store_certificates[op]
            } by {
        reveal(crate::state::spec_store);
        reveal(crate::state::spec_store_certified);
        reveal(crate::state::spec_store_raw);
        reveal(store_effect_certificate);
        reveal(certificate_written_document);
        reveal(production_core_control_body);
        reveal(crate::production_relation::operation_allocator_consistent);
    };
    lemma_active_write_cache_exclusion_frames(state, next);
}

pub(crate) proof fn lemma_control_field_frame_preserves_active_write_cache_exclusion(
    before: S,
    after: S,
)
    requires
        active_document_writes_exclude_certified_cache(before),
        after.cache == before.cache,
        after.ops == before.ops,
        after.store_certificates == before.store_certificates,
    ensures
        active_document_writes_exclude_certified_cache(after),
{
    reveal(active_document_writes_exclude_certified_cache);
}

pub(crate) proof fn lemma_read_nodes_preserves_active_write_cache_exclusion(
    state: S,
    keys: Seq<Seq<char>>,
    pending: Map<u64, bool>,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_read_nodes(state, keys, pending).0,
        ),
    decreases keys.len(),
{
    reveal(crate::handler_node::spec_read_nodes);
    if keys.len() > 0 {
        let key = keys[0];
        if crate::keys::spec_node_of_key(state.keys.prefix, key)
            != Some(state.node.members.me.id)
        {
                let request = StoreReqSpec::Get { key };
                assert(certificate_matches_request(
                    state.keys.prefix,
                    state.keys.bucket_ms,
                    request,
                    StoreEffectCertificateV::Other,
                )) by {
                    reveal(certificate_matches_request);
                };
                lemma_control_store_preserves_active_write_cache_exclusion(
                    state,
                    request,
                    Owner::Members,
                );
                lemma_nonflight_store_issue_preserves_core_control_body(
                    state,
                    request,
                    Owner::Members,
                );
                let issued = crate::state::spec_store(
                    state,
                    request,
                    Owner::Members,
                );
                match issued.1 {
                    Some(op) => {
                        lemma_read_nodes_preserves_active_write_cache_exclusion(
                            issued.0,
                            keys.drop_first(),
                            pending.insert(op, true),
                        );
                    },
                    None => {
                        lemma_read_nodes_preserves_active_write_cache_exclusion(
                            issued.0,
                            keys.drop_first(),
                            pending,
                        );
                    },
                }
        } else {
                lemma_read_nodes_preserves_active_write_cache_exclusion(
                    state,
                    keys.drop_first(),
                    pending,
                );
        }
    }
}

pub(crate) proof fn lemma_list_buckets_preserves_active_write_cache_exclusion(
    state: S,
    prefixes: Seq<Seq<char>>,
    horizon: u64,
    pending: Map<u64, u64>,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_list_buckets(
                state,
                prefixes,
                horizon,
                pending,
            ).0,
        ),
    decreases prefixes.len(),
{
    reveal(crate::handler_timers::spec_list_buckets);
    if prefixes.len() > 0 {
        match crate::keys::spec_parse_bucket_prefix(
            state.keys.prefix,
            prefixes[0],
        ) {
            Some(bucket) if bucket <= horizon => {
                let request = StoreReqSpec::List {
                    prefix: crate::keys::spec_bucket_prefix(
                        state.keys.prefix,
                        bucket,
                    ),
                    max_keys: usize::MAX,
                };
                lemma_control_store_preserves_active_write_cache_exclusion(
                    state,
                    request,
                    Owner::Timers,
                );
                lemma_nonflight_store_issue_preserves_core_control_body(
                    state,
                    request,
                    Owner::Timers,
                );
                let issued = crate::state::spec_store(
                    state,
                    request,
                    Owner::Timers,
                );
                match issued.1 {
                    Some(op) => {
                        lemma_list_buckets_preserves_active_write_cache_exclusion(
                            issued.0,
                            prefixes.drop_first(),
                            horizon,
                            pending.insert(op, bucket),
                        );
                    },
                    None => {
                        lemma_list_buckets_preserves_active_write_cache_exclusion(
                            issued.0,
                            prefixes.drop_first(),
                            horizon,
                            pending,
                        );
                    },
                }
            },
            _ => {
                lemma_list_buckets_preserves_active_write_cache_exclusion(
                    state,
                    prefixes.drop_first(),
                    horizon,
                    pending,
                );
            },
        }
    }
}

pub(crate) proof fn lemma_take_bucket_preserves_active_write_cache_exclusion(
    state: S,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_take_bucket(state, keys, count).0,
        ),
    decreases keys.len(),
{
    reveal(crate::handler_timers::spec_take_bucket);
    if keys.len() > 0 {
        match crate::keys::spec_parse_timer_key(keys[0]) {
            Some(entry)
                if crate::handler_timers::spec_owns_entry(state, entry) => {
                    let next = crate::handler_timers::spec_with_timers(
                        state,
                        crate::state_timers::TimersSpec {
                            wheel: crate::state_timers::TimerWheelSpec {
                                armed: crate::state_timers::spec_arm(
                                    state.timers.wheel.armed,
                                    entry.deadline(),
                                    keys[0],
                                ),
                            },
                            ..state.timers
                        },
                    );
                    lemma_control_field_frame_preserves_active_write_cache_exclusion(
                        state,
                        next,
                    );
                    lemma_timers_field_update_preserves_core_control_body(
                        state,
                        next.timers,
                    );
                    lemma_take_bucket_preserves_active_write_cache_exclusion(
                        next,
                        keys.drop_first(),
                        count + 1,
                    );
                },
            _ => {
                lemma_take_bucket_preserves_active_write_cache_exclusion(
                    state,
                    keys.drop_first(),
                    count,
                );
            },
        }
    }
}

pub(crate) proof fn lemma_timers_start_preserves_active_write_cache_exclusion(
    state: S,
    now: u64,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_timers_start(state, now),
        ),
{
    reveal(crate::handler_timers::spec_timers_start);
    let staged = crate::handler_timers::spec_with_timers(
        state,
        crate::state_timers::TimersSpec {
            started: true,
            bucket_ms: state.keys.bucket_ms,
            reload_pending: true,
            ..state.timers
        },
    );
    lemma_control_field_frame_preserves_active_write_cache_exclusion(
        state,
        staged,
    );
    lemma_timers_field_update_preserves_core_control_body(
        state,
        staged.timers,
    );
    lemma_timers_run_preserves_active_write_cache_exclusion(staged, now);
}

pub(crate) proof fn lemma_refresh_ended_preserves_active_write_cache_exclusion(
    state: S,
    result: Result<(), echod_concrete::store::StoreErrorSpec>,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_refresh_ended(state, result),
        ),
{
    reveal(crate::handler_node::spec_refresh_ended);
    let cleared = crate::handler_node::spec_with_members(
        state,
        crate::state_node::MembersSpec {
            refresh: None,
            ..state.node.members
        },
    );
    lemma_control_field_frame_preserves_active_write_cache_exclusion(
        state,
        cleared,
    );
    lemma_members_field_update_preserves_core_control_body(
        state,
        cleared.node.members,
    );
    let now = crate::state::spec_now(cleared);
    let noted = crate::state::spec_note(
        cleared,
        crate::types::NoteSpec::MembershipRefresh {
            ok: result is Ok,
        },
    );
    lemma_control_field_frame_preserves_active_write_cache_exclusion(
        cleared,
        noted,
    );
    lemma_note_preserves_core_control_body(
        cleared,
        crate::types::NoteSpec::MembershipRefresh {
            ok: result is Ok,
        },
    );
    let ended = match result {
        Ok(()) => {
            if !noted.node.members.read_once {
                let read = crate::handler_node::spec_with_members(
                    noted,
                    crate::state_node::MembersSpec {
                        read_once: true,
                        ..noted.node.members
                    },
                );
                lemma_control_field_frame_preserves_active_write_cache_exclusion(
                    noted,
                    read,
                );
                lemma_members_field_update_preserves_core_control_body(
                    noted,
                    read.node.members,
                );
                lemma_timers_start_preserves_active_write_cache_exclusion(
                    read,
                    now,
                );
                lemma_timers_start_preserves_core_control_body(read, now);
                crate::handler_timers::spec_timers_start(read, now)
            } else {
                noted
            }
        },
        Err(error) => {
            let failed = crate::state::spec_note(
                noted,
                crate::types::NoteSpec::RefreshFailed {
                    error: crate::types::spec_error_text(error),
                },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                noted,
                failed,
            );
            lemma_note_preserves_core_control_body(
                noted,
                crate::types::NoteSpec::RefreshFailed {
                    error: crate::types::spec_error_text(error),
                },
            );
            failed
        },
    };
    let scheduled = crate::handler_node::spec_with_members(
        ended,
        crate::state_node::MembersSpec {
            next_heartbeat: Some(
                now.saturating_add(ended.node.members.heartbeat_ms),
            ),
            ..ended.node.members
        },
    );
    lemma_control_field_frame_preserves_active_write_cache_exclusion(
        ended,
        scheduled,
    );
    lemma_members_field_update_preserves_core_control_body(
        ended,
        scheduled.node.members,
    );
    if scheduled.loops {
        lemma_timers_run_preserves_active_write_cache_exclusion(
            scheduled,
            now,
        );
    }
}

pub(crate) proof fn lemma_read_configuration_preserves_active_write_cache_exclusion(
    state: S,
    nodes: crate::state_node::RosterSpec,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_read_configuration(state, nodes),
        ),
{
    reveal(crate::handler_node::spec_read_configuration);
    let request = StoreReqSpec::Get {
        key: crate::keys::spec_members_key(state.keys.prefix),
    };
    lemma_members_key_is_not_document_or_timer(state.keys.prefix);
    assert(certificate_matches_request(
        state.keys.prefix,
        state.keys.bucket_ms,
        request,
        StoreEffectCertificateV::Other,
    )) by {
        reveal(certificate_matches_request);
    };
    lemma_control_store_preserves_active_write_cache_exclusion(
        state,
        request,
        Owner::Members,
    );
    lemma_nonflight_store_issue_preserves_core_control_body(
        state,
        request,
        Owner::Members,
    );
    let issued = crate::state::spec_store(
        state,
        request,
        Owner::Members,
    );
    match issued.1 {
        Some(_) => {
            let next = crate::handler_node::spec_with_members(
                issued.0,
                crate::state_node::MembersSpec {
                    refresh: Some(
                        crate::state_node::RefreshSpec::Config {
                            op: issued.1.unwrap(),
                            nodes,
                        },
                    ),
                    ..issued.0.node.members
                },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                issued.0,
                next,
            );
        },
        None => {
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                issued.0,
                Err(crate::types::spec_exhausted()),
            );
        },
    }
}

pub(crate) proof fn lemma_members_announced_preserves_active_write_cache_exclusion(
    state: S,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_announced(state, now, response),
        ),
{
    reveal(crate::handler_node::spec_announced);
    match response {
        echod_concrete::store::StoreRes::Put { result: Ok(()) } => {
            let request = StoreReqSpec::List {
                prefix: crate::keys::spec_node_prefix(state.keys.prefix),
                max_keys: 10_000,
            };
            lemma_control_store_preserves_active_write_cache_exclusion(
                state,
                request,
                Owner::Members,
            );
            lemma_nonflight_store_issue_preserves_core_control_body(
                state,
                request,
                Owner::Members,
            );
            let issued = crate::state::spec_store(
                state,
                request,
                Owner::Members,
            );
            match issued.1 {
                Some(_) => {
                    let next = crate::handler_node::spec_with_members(
                        issued.0,
                        crate::state_node::MembersSpec {
                            refresh: Some(
                                crate::state_node::RefreshSpec::Listing {
                                    op: issued.1.unwrap(),
                                    now,
                                },
                            ),
                            ..issued.0.node.members
                        },
                    );
                    lemma_control_field_frame_preserves_active_write_cache_exclusion(
                        issued.0,
                        next,
                    );
                },
                None => {
                    lemma_refresh_ended_preserves_active_write_cache_exclusion(
                        issued.0,
                        Err(crate::types::spec_exhausted()),
                    );
                },
            }
        },
        echod_concrete::store::StoreRes::Put {
            result: Err(error),
        } => {
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                state,
                Err(error.deep_view()),
            );
        },
        _ => {
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                state,
                Err(crate::types::spec_unexpected()),
            );
        },
    }
}

pub(crate) proof fn lemma_members_listed_preserves_active_write_cache_exclusion(
    state: S,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_listed(state, now, response),
        ),
{
    reveal(crate::handler_node::spec_listed);
    match response {
        echod_concrete::store::StoreRes::List {
            result: Ok(keys),
        } => {
            let nodes = crate::state_node::RosterSpec {
                entries: crate::state_node::spec_roster_insert(
                    Seq::empty(),
                    state.node.members.me.id,
                    state.node.members.me,
                ),
            };
            lemma_read_nodes_preserves_active_write_cache_exclusion(
                state,
                keys.deep_view(),
                Map::empty(),
            );
            lemma_read_nodes_preserves_core_control_body(
                state,
                keys.deep_view(),
                Map::empty(),
            );
            let read = crate::handler_node::spec_read_nodes(
                state,
                keys.deep_view(),
                Map::empty(),
            );
            if read.1 =~= Map::<u64, bool>::empty() {
                lemma_read_configuration_preserves_active_write_cache_exclusion(
                    read.0,
                    nodes,
                );
            } else {
                let next = crate::handler_node::spec_with_members(
                    read.0,
                    crate::state_node::MembersSpec {
                        refresh: Some(
                            crate::state_node::RefreshSpec::Reading {
                                pending: read.1,
                                nodes,
                                now,
                                failed: None,
                            },
                        ),
                        ..read.0.node.members
                    },
                );
                lemma_control_field_frame_preserves_active_write_cache_exclusion(
                    read.0,
                    next,
                );
            }
        },
        echod_concrete::store::StoreRes::List {
            result: Err(error),
        } => {
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                state,
                Err(error.deep_view()),
            );
        },
        _ => {
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                state,
                Err(crate::types::spec_unexpected()),
            );
        },
    }
}

pub(crate) proof fn lemma_write_members_preserves_active_write_cache_exclusion(
    state: S,
    configuration: crate::state_node::ConfigurationSpec,
    etag: Option<echod_concrete::store::EtagSpec>,
    nodes: crate::state_node::RosterSpec,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_write_members(
                state,
                configuration,
                etag,
                nodes,
            ),
        ),
{
    reveal(crate::handler_node::spec_write_members);
    let live = crate::state_node::spec_roster_ids(nodes.entries);
    if live != configuration.members {
        let next_config = crate::state_node::ConfigurationSpec {
            epoch: configuration.epoch.saturating_add(1),
            members: live,
        };
        let request = match etag {
            Some(tag) => StoreReqSpec::PutIfMatch {
                key: crate::keys::spec_members_key(state.keys.prefix),
                body: crate::state_node::spec_configuration_bytes(next_config),
                etag: tag,
            },
            None => StoreReqSpec::PutIfNoneMatch {
                key: crate::keys::spec_members_key(state.keys.prefix),
                body: crate::state_node::spec_configuration_bytes(next_config),
            },
        };
        lemma_members_key_is_not_document_or_timer(state.keys.prefix);
        assert(certificate_matches_request(
            state.keys.prefix,
            state.keys.bucket_ms,
            request,
            StoreEffectCertificateV::Other,
        )) by {
            reveal(certificate_matches_request);
        };
        lemma_control_store_preserves_active_write_cache_exclusion(
            state,
            request,
            Owner::Members,
        );
        lemma_nonflight_store_issue_preserves_core_control_body(
            state,
            request,
            Owner::Members,
        );
        let issued = crate::state::spec_store(
            state,
            request,
            Owner::Members,
        );
        match issued.1 {
            Some(_) => {
                let next = crate::handler_node::spec_with_members(
                    issued.0,
                    crate::state_node::MembersSpec {
                        refresh: Some(
                            crate::state_node::RefreshSpec::Writing {
                                op: issued.1.unwrap(),
                                next: next_config,
                            },
                        ),
                        ..issued.0.node.members
                    },
                );
                lemma_control_field_frame_preserves_active_write_cache_exclusion(
                    issued.0,
                    next,
                );
            },
            None => {
                lemma_refresh_ended_preserves_active_write_cache_exclusion(
                    issued.0,
                    Err(crate::types::spec_exhausted()),
                );
            },
        }
    } else {
        lemma_refresh_ended_preserves_active_write_cache_exclusion(
            state,
            Ok(()),
        );
    }
}

pub(crate) proof fn lemma_members_read_one_preserves_active_write_cache_exclusion(
    state: S,
    pending: Map<u64, bool>,
    nodes: crate::state_node::RosterSpec,
    now: u64,
    failed: Option<echod_concrete::store::StoreErrorSpec>,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_read_one(
                state,
                pending,
                nodes,
                now,
                failed,
                response,
            ),
        ),
{
    reveal(crate::handler_node::spec_read_one);
    reveal(crate::handler_node::spec_read_one_outcome);
    let staged = match response {
        echod_concrete::store::StoreRes::Get {
            result: Ok(Some((bytes, _))),
        } => match crate::state_node::spec_parse_announcement(bytes@) {
            Some(announcement) => {
                let fleet_at = if state.node.fleet_at > announcement.at {
                    state.node.fleet_at
                } else {
                    announcement.at
                };
                let observed = S {
                    node: crate::state_node::NodeSpec {
                        fleet_at,
                        ..state.node
                    },
                    ..state
                };
                lemma_control_field_frame_preserves_active_write_cache_exclusion(
                    state,
                    observed,
                );
                assert(production_core_control_body(observed)) by {
                    reveal(production_core_control_body);
                };
                if announcement.at.saturating_add(
                    observed.node.members.ttl,
                ) >= now {
                    observed
                } else if announcement.at.saturating_add(
                    (2 as u64).saturating_mul(
                        observed.node.members.ttl,
                    ),
                ) < now {
                    let request = StoreReqSpec::Del {
                        key: crate::keys::spec_node_key(
                            observed.keys.prefix,
                            announcement.id,
                        ),
                    };
                    lemma_node_key_is_not_document_or_timer(
                        observed.keys.prefix,
                        announcement.id,
                    );
                    assert(certificate_matches_request(
                        observed.keys.prefix,
                        observed.keys.bucket_ms,
                        request,
                        StoreEffectCertificateV::Other,
                    )) by {
                        reveal(certificate_matches_request);
                    };
                    lemma_control_store_preserves_active_write_cache_exclusion(
                        observed,
                        request,
                        Owner::Ignored,
                    );
                    lemma_nonflight_store_issue_preserves_core_control_body(
                        observed,
                        request,
                        Owner::Ignored,
                    );
                    crate::state::spec_store(
                        observed,
                        request,
                        Owner::Ignored,
                    ).0
                } else {
                    observed
                }
            },
            None => state,
        },
        _ => state,
    };
    assert(active_document_writes_exclude_certified_cache(staged));
    assert(production_core_control_body(staged)) by {
        lemma_members_read_one_preserves_core_control_body(
            state,
            pending,
            nodes,
            now,
            failed,
            response,
        );
    };
    if !(pending =~= Map::<u64, bool>::empty()) {
        let result = crate::handler_node::spec_read_one_outcome(
            state,
            nodes,
            now,
            failed,
            response,
        );
        let next = crate::handler_node::spec_with_members(
            result.0,
            crate::state_node::MembersSpec {
                refresh: Some(
                    crate::state_node::RefreshSpec::Reading {
                        pending,
                        nodes: result.1,
                        now,
                        failed: result.2,
                    },
                ),
                ..result.0.node.members
            },
        );
        assert(result.0 == staged);
        lemma_control_field_frame_preserves_active_write_cache_exclusion(
            result.0,
            next,
        );
    } else {
        let result = crate::handler_node::spec_read_one_outcome(
            state,
            nodes,
            now,
            failed,
            response,
        );
        assert(result.0 == staged);
        match result.2 {
            Some(error) => {
                lemma_refresh_ended_preserves_active_write_cache_exclusion(
                    result.0,
                    Err(error),
                );
            },
            None => {
                lemma_read_configuration_preserves_active_write_cache_exclusion(
                    result.0,
                    result.1,
                );
            },
        }
    }
}

pub(crate) proof fn lemma_take_on_preserves_active_write_cache_exclusion(
    state: S,
    configuration: crate::state_node::ConfigurationSpec,
    etag: Option<echod_concrete::store::EtagSpec>,
    nodes: crate::state_node::RosterSpec,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_take_on(
                state,
                configuration,
                etag,
                nodes,
            ),
        ),
{
    reveal(crate::handler_node::spec_take_on);
    let changed = !(state.node.core.read_any
        && state.node.core.epoch == configuration.epoch as nat);
    let noted = if changed {
        let next = crate::state::spec_note(
            state,
            crate::types::NoteSpec::ConfigurationRead {
                epoch: configuration.epoch,
                members: configuration.members,
            },
        );
        lemma_control_field_frame_preserves_active_write_cache_exclusion(
            state,
            next,
        );
        lemma_note_preserves_core_control_body(
            state,
            crate::types::NoteSpec::ConfigurationRead {
                epoch: configuration.epoch,
                members: configuration.members,
            },
        );
        next
    } else {
        state
    };
    let configured = S {
        node: crate::state_node::NodeSpec {
            core: crate::verified::node_spec::spec_read_config(
                noted.node.core,
                crate::state::spec_now(noted) as nat,
                configuration.epoch as nat,
                configuration.members,
            ),
            members: crate::state_node::MembersSpec {
                nodes,
                etag,
                ..noted.node.members
            },
            ..noted.node
        },
        ..noted
    };
    lemma_control_field_frame_preserves_active_write_cache_exclusion(
        noted,
        configured,
    );
    assert(production_core_control_body(configured)) by {
        reveal(production_core_control_body);
    };
    let reloading = if changed {
        let changed_note = crate::state::spec_note(
            configured,
            crate::types::NoteSpec::ConfigurationChange,
        );
        lemma_control_field_frame_preserves_active_write_cache_exclusion(
            configured,
            changed_note,
        );
        lemma_note_preserves_core_control_body(
            configured,
            crate::types::NoteSpec::ConfigurationChange,
        );
        let next = crate::handler_timers::spec_timers_membership_changed(
            changed_note,
        );
        reveal(crate::handler_timers::spec_timers_membership_changed);
        lemma_control_field_frame_preserves_active_write_cache_exclusion(
            changed_note,
            next,
        );
        lemma_timers_field_update_preserves_core_control_body(
            changed_note,
            next.timers,
        );
        next
    } else {
        configured
    };
    lemma_write_members_preserves_active_write_cache_exclusion(
        reloading,
        configuration,
        etag,
        nodes,
    );
}

pub(crate) proof fn lemma_members_configured_preserves_active_write_cache_exclusion(
    state: S,
    nodes: crate::state_node::RosterSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_configured(state, nodes, response),
        ),
{
    reveal(crate::handler_node::spec_configured);
    match response {
        echod_concrete::store::StoreRes::Get {
            result: Ok(read),
        } => {
            let parsed = match read {
                Some((bytes, etag)) => (
                    crate::state_node::spec_parse_configuration(bytes@),
                    Some(etag.deep_view()),
                ),
                None => (
                    crate::state_node::ConfigurationSpec {
                        epoch: 0,
                        members: Seq::empty(),
                    },
                    None,
                ),
            };
            lemma_take_on_preserves_active_write_cache_exclusion(
                state,
                parsed.0,
                parsed.1,
                nodes,
            );
        },
        echod_concrete::store::StoreRes::Get {
            result: Err(error),
        } => {
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                state,
                Err(error.deep_view()),
            );
        },
        _ => {
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                state,
                Err(crate::types::spec_unexpected()),
            );
        },
    }
}

pub(crate) proof fn lemma_members_written_preserves_active_write_cache_exclusion(
    state: S,
    next_config: crate::state_node::ConfigurationSpec,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_written(
                state,
                next_config,
                response,
            ),
        ),
{
    reveal(crate::handler_node::spec_written);
    match response {
        echod_concrete::store::StoreRes::PutIfMatch {
            result: Ok(_),
        }
        | echod_concrete::store::StoreRes::PutIfNoneMatch {
            result: Ok(_),
        } => {
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Written,
                ),
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                state,
                noted,
            );
            lemma_note_preserves_core_control_body(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Written,
                ),
            );
            let written = crate::state::spec_note(
                noted,
                crate::types::NoteSpec::ConfigurationWritten {
                    epoch: next_config.epoch,
                    members: next_config.members,
                },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                noted,
                written,
            );
            lemma_note_preserves_core_control_body(
                noted,
                crate::types::NoteSpec::ConfigurationWritten {
                    epoch: next_config.epoch,
                    members: next_config.members,
                },
            );
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                written,
                Ok(()),
            );
        },
        echod_concrete::store::StoreRes::PutIfMatch {
            result: Err(
                echod_concrete::store::StoreError::PreconditionFailed,
            ),
        }
        | echod_concrete::store::StoreRes::PutIfNoneMatch {
            result: Err(
                echod_concrete::store::StoreError::PreconditionFailed,
            ),
        } => {
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Conflict,
                ),
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                state,
                noted,
            );
            lemma_note_preserves_core_control_body(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Conflict,
                ),
            );
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                noted,
                Ok(()),
            );
        },
        echod_concrete::store::StoreRes::PutIfMatch {
            result: Err(error),
        }
        | echod_concrete::store::StoreRes::PutIfNoneMatch {
            result: Err(error),
        } => {
            let noted = crate::state::spec_note(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Failed,
                ),
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                state,
                noted,
            );
            lemma_note_preserves_core_control_body(
                state,
                crate::types::NoteSpec::ConfigurationWrite(
                    crate::types::ConfigWrite::Failed,
                ),
            );
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                noted,
                Err(error.deep_view()),
            );
        },
        _ => {
            lemma_refresh_ended_preserves_active_write_cache_exclusion(
                state,
                Err(crate::types::spec_unexpected()),
            );
        },
    }
}

pub(crate) proof fn lemma_members_completed_preserves_active_write_cache_exclusion(
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_node::spec_members_completed(
                state,
                op,
                response,
            ),
        ),
{
    reveal(crate::handler_node::spec_members_completed);
    match state.node.members.refresh {
        Some(refresh) if refresh.expects(op) => {
            let cleared = crate::handler_node::spec_with_members(
                state,
                crate::state_node::MembersSpec {
                    refresh: None,
                    ..state.node.members
                },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                state,
                cleared,
            );
            lemma_members_field_update_preserves_core_control_body(
                state,
                cleared.node.members,
            );
            match refresh {
                crate::state_node::RefreshSpec::Announcing {
                    now,
                    ..
                } => {
                    lemma_members_announced_preserves_active_write_cache_exclusion(
                        cleared,
                        now,
                        response,
                    );
                },
                crate::state_node::RefreshSpec::Listing { now, .. } => {
                    lemma_members_listed_preserves_active_write_cache_exclusion(
                        cleared,
                        now,
                        response,
                    );
                },
                crate::state_node::RefreshSpec::Reading {
                    pending,
                    nodes,
                    now,
                    failed,
                } => {
                    lemma_members_read_one_preserves_active_write_cache_exclusion(
                        cleared,
                        pending.remove(op),
                        nodes,
                        now,
                        failed,
                        response,
                    );
                },
                crate::state_node::RefreshSpec::Config {
                    nodes,
                    ..
                } => {
                    lemma_members_configured_preserves_active_write_cache_exclusion(
                        cleared,
                        nodes,
                        response,
                    );
                },
                crate::state_node::RefreshSpec::Writing {
                    next,
                    ..
                } => {
                    lemma_members_written_preserves_active_write_cache_exclusion(
                        cleared,
                        next,
                        response,
                    );
                },
            }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_listing_failed_preserves_active_write_cache_exclusion(
    state: S,
    error: echod_concrete::store::StoreErrorSpec,
    now: u64,
)
    requires
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_listing_failed(
                state,
                error,
                now,
            ),
        ),
{
    let next = crate::handler_timers::spec_listing_failed(
        state,
        error,
        now,
    );
    assert(next.cache == state.cache) by {
        reveal(crate::handler_timers::spec_listing_failed);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_note);
    };
    assert(next.ops == state.ops) by {
        reveal(crate::handler_timers::spec_listing_failed);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_note);
    };
    assert(next.store_certificates == state.store_certificates) by {
        reveal(crate::handler_timers::spec_listing_failed);
        reveal(crate::handler_timers::spec_with_timers);
        reveal(crate::state::spec_note);
    };
    lemma_control_field_frame_preserves_active_write_cache_exclusion(
        state,
        next,
    );
}

pub(crate) proof fn lemma_reloaded_preserves_active_write_cache_exclusion(
    state: S,
    horizon: u64,
    loaded: usize,
    now: u64,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_reloaded(
                state,
                horizon,
                loaded,
                now,
            ),
        ),
{
    reveal(crate::handler_timers::spec_reloaded);
    let updated = crate::handler_timers::spec_with_timers(
        state,
        crate::state_timers::TimersSpec {
            loaded_through: Some(horizon),
            closed_through: Some(
                crate::keys::spec_bucket_of(now, state.keys.bucket_ms)
                    .saturating_sub(state.keys.bucket_ms),
            ),
            reload_pending: false,
            ..state.timers
        },
    );
    lemma_control_field_frame_preserves_active_write_cache_exclusion(
        state,
        updated,
    );
    lemma_timers_field_update_preserves_core_control_body(
        state,
        updated.timers,
    );
    let first = crate::state::spec_note(
        updated,
        crate::types::NoteSpec::TimerListing { ok: true },
    );
    lemma_control_field_frame_preserves_active_write_cache_exclusion(
        updated,
        first,
    );
    lemma_note_preserves_core_control_body(
        updated,
        crate::types::NoteSpec::TimerListing { ok: true },
    );
    let noted = crate::state::spec_note(
        first,
        crate::types::NoteSpec::TimersLoaded {
            deadlines: loaded,
            wheel: first.timers.wheel.armed.len() as usize,
            epoch: first.node.core.epoch as u64,
        },
    );
    lemma_control_field_frame_preserves_active_write_cache_exclusion(
        first,
        noted,
    );
    lemma_note_preserves_core_control_body(
        first,
        crate::types::NoteSpec::TimersLoaded {
            deadlines: loaded,
            wheel: first.timers.wheel.armed.len() as usize,
            epoch: first.node.core.epoch as u64,
        },
    );
    lemma_timers_run_preserves_active_write_cache_exclusion(noted, now);
}

pub(crate) proof fn lemma_prefixes_listed_preserves_active_write_cache_exclusion(
    state: S,
    horizon: u64,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_prefixes_listed(
                state,
                horizon,
                now,
                response,
            ),
        ),
{
    reveal(crate::handler_timers::spec_prefixes_listed);
    match response {
        echod_concrete::store::StoreRes::ListPrefixes {
            result: Ok(prefixes),
        } => {
            lemma_list_buckets_preserves_active_write_cache_exclusion(
                state,
                prefixes.deep_view(),
                horizon,
                Map::empty(),
            );
            lemma_list_buckets_preserves_core_control_body(
                state,
                prefixes.deep_view(),
                horizon,
                Map::empty(),
            );
            let listed = crate::handler_timers::spec_list_buckets(
                state,
                prefixes.deep_view(),
                horizon,
                Map::empty(),
            );
            if listed.1 =~= Map::<u64, u64>::empty() {
                lemma_reloaded_preserves_active_write_cache_exclusion(
                    listed.0,
                    horizon,
                    0,
                    now,
                );
            } else {
                let next = crate::handler_timers::spec_with_timers(
                    listed.0,
                    crate::state_timers::TimersSpec {
                        listing: Some(
                            crate::state_timers::ListingSpec::Buckets {
                                pending: listed.1,
                                horizon,
                                loaded: 0,
                                failed: None,
                            },
                        ),
                        ..listed.0.timers
                    },
                );
                lemma_control_field_frame_preserves_active_write_cache_exclusion(
                    listed.0,
                    next,
                );
            }
        },
        echod_concrete::store::StoreRes::ListPrefixes {
            result: Err(error),
        } => {
            lemma_listing_failed_preserves_active_write_cache_exclusion(
                state,
                error.deep_view(),
                now,
            );
        },
        _ => {
            lemma_listing_failed_preserves_active_write_cache_exclusion(
                state,
                crate::types::spec_unexpected(),
                now,
            );
        },
    }
}

pub(crate) proof fn lemma_bucket_listed_preserves_active_write_cache_exclusion(
    state: S,
    pending: Map<u64, u64>,
    horizon: u64,
    loaded: usize,
    failed: Option<echod_concrete::store::StoreErrorSpec>,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_bucket_listed(
                state,
                pending,
                horizon,
                loaded,
                failed,
                now,
                response,
            ),
        ),
{
    reveal(crate::handler_timers::spec_bucket_listed);
    let staged = match response {
        echod_concrete::store::StoreRes::List {
            result: Ok(keys),
        } => {
            lemma_take_bucket_preserves_active_write_cache_exclusion(
                state,
                keys.deep_view(),
                0,
            );
            lemma_take_bucket_preserves_core_control_body(
                state,
                keys.deep_view(),
                0,
            );
            crate::handler_timers::spec_take_bucket(
                state,
                keys.deep_view(),
                0,
            ).0
        },
        _ => state,
    };
    let result = match response {
        echod_concrete::store::StoreRes::List {
            result: Ok(keys),
        } => crate::handler_timers::spec_take_bucket(
            state,
            keys.deep_view(),
            0,
        ),
        _ => (state, 0),
    };
    let final_loaded = match response {
        echod_concrete::store::StoreRes::List { result: Ok(_) } =>
            loaded.saturating_add(result.1 as usize),
        _ => loaded,
    };
    let final_failed = match response {
        echod_concrete::store::StoreRes::List { result: Ok(_) } =>
            failed,
        echod_concrete::store::StoreRes::List {
            result: Err(error),
        } => Some(error.deep_view()),
        _ => Some(crate::types::spec_unexpected()),
    };
    if !(pending =~= Map::<u64, u64>::empty()) {
        let next = crate::handler_timers::spec_with_timers(
            staged,
            crate::state_timers::TimersSpec {
                listing: Some(
                    crate::state_timers::ListingSpec::Buckets {
                        pending,
                        horizon,
                        loaded: final_loaded,
                        failed: final_failed,
                    },
                ),
                ..staged.timers
            },
        );
        lemma_control_field_frame_preserves_active_write_cache_exclusion(
            staged,
            next,
        );
    } else {
        match final_failed {
            Some(error) => {
                lemma_listing_failed_preserves_active_write_cache_exclusion(
                    staged,
                    error,
                    now,
                );
            },
            None => {
                lemma_reloaded_preserves_active_write_cache_exclusion(
                    staged,
                    horizon,
                    final_loaded,
                    now,
                );
            },
        }
    }
}

pub(crate) proof fn lemma_extended_preserves_active_write_cache_exclusion(
    state: S,
    bucket: u64,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_extended(
                state,
                bucket,
                now,
                response,
            ),
        ),
{
    reveal(crate::handler_timers::spec_extended);
    match response {
        echod_concrete::store::StoreRes::List {
            result: Ok(keys),
        } => {
            lemma_take_bucket_preserves_active_write_cache_exclusion(
                state,
                keys.deep_view(),
                0,
            );
            lemma_take_bucket_preserves_core_control_body(
                state,
                keys.deep_view(),
                0,
            );
            let taken = crate::handler_timers::spec_take_bucket(
                state,
                keys.deep_view(),
                0,
            );
            let loaded = crate::state::spec_note(
                taken.0,
                crate::types::NoteSpec::BucketLoaded {
                    bucket,
                    deadlines: taken.1 as usize,
                },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                taken.0,
                loaded,
            );
            lemma_note_preserves_core_control_body(
                taken.0,
                crate::types::NoteSpec::BucketLoaded {
                    bucket,
                    deadlines: taken.1 as usize,
                },
            );
            let noted = crate::state::spec_note(
                loaded,
                crate::types::NoteSpec::TimerListing { ok: true },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                loaded,
                noted,
            );
            lemma_note_preserves_core_control_body(
                loaded,
                crate::types::NoteSpec::TimerListing { ok: true },
            );
            let advanced = crate::handler_timers::spec_with_timers(
                noted,
                crate::state_timers::TimersSpec {
                    loaded_through: Some(bucket),
                    ..noted.timers
                },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                noted,
                advanced,
            );
            lemma_timers_field_update_preserves_core_control_body(
                noted,
                advanced.timers,
            );
            lemma_timers_run_preserves_active_write_cache_exclusion(
                advanced,
                now,
            );
        },
        echod_concrete::store::StoreRes::List {
            result: Err(error),
        } => {
            lemma_listing_failed_preserves_active_write_cache_exclusion(
                state,
                error.deep_view(),
                now,
            );
        },
        _ => {
            lemma_listing_failed_preserves_active_write_cache_exclusion(
                state,
                crate::types::spec_unexpected(),
                now,
            );
        },
    }
}

pub(crate) proof fn lemma_relisted_preserves_active_write_cache_exclusion(
    state: S,
    bucket: u64,
    now: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_relisted(
                state,
                bucket,
                now,
                response,
            ),
        ),
{
    reveal(crate::handler_timers::spec_relisted);
    match response {
        echod_concrete::store::StoreRes::List {
            result: Ok(keys),
        } => {
            lemma_take_bucket_preserves_active_write_cache_exclusion(
                state,
                keys.deep_view(),
                0,
            );
            lemma_take_bucket_preserves_core_control_body(
                state,
                keys.deep_view(),
                0,
            );
            let taken = crate::handler_timers::spec_take_bucket(
                state,
                keys.deep_view(),
                0,
            );
            let loaded = crate::state::spec_note(
                taken.0,
                crate::types::NoteSpec::BucketLoaded {
                    bucket,
                    deadlines: taken.1 as usize,
                },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                taken.0,
                loaded,
            );
            lemma_note_preserves_core_control_body(
                taken.0,
                crate::types::NoteSpec::BucketLoaded {
                    bucket,
                    deadlines: taken.1 as usize,
                },
            );
            let noted = crate::state::spec_note(
                loaded,
                crate::types::NoteSpec::TimerListing { ok: true },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                loaded,
                noted,
            );
            lemma_note_preserves_core_control_body(
                loaded,
                crate::types::NoteSpec::TimerListing { ok: true },
            );
            let advanced = crate::handler_timers::spec_with_timers(
                noted,
                crate::state_timers::TimersSpec {
                    closed_through: Some(bucket),
                    ..noted.timers
                },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                noted,
                advanced,
            );
            lemma_timers_field_update_preserves_core_control_body(
                noted,
                advanced.timers,
            );
            lemma_timers_run_preserves_active_write_cache_exclusion(
                advanced,
                now,
            );
        },
        echod_concrete::store::StoreRes::List {
            result: Err(error),
        } => {
            lemma_listing_failed_preserves_active_write_cache_exclusion(
                state,
                error.deep_view(),
                now,
            );
        },
        _ => {
            lemma_listing_failed_preserves_active_write_cache_exclusion(
                state,
                crate::types::spec_unexpected(),
                now,
            );
        },
    }
}

pub(crate) proof fn lemma_timers_completed_preserves_active_write_cache_exclusion(
    state: S,
    op: u64,
    response: echod_concrete::store::StoreRes,
)
    requires
        production_core_control_body(state),
        active_document_writes_exclude_certified_cache(state),
    ensures
        active_document_writes_exclude_certified_cache(
            crate::handler_timers::spec_timers_completed(
                state,
                op,
                response,
            ),
        ),
{
    reveal(crate::handler_timers::spec_timers_completed);
    match state.timers.listing {
        Some(listing) if listing.expects(op) => {
            let cleared = crate::handler_timers::spec_with_timers(
                state,
                crate::state_timers::TimersSpec {
                    listing: None,
                    ..state.timers
                },
            );
            lemma_control_field_frame_preserves_active_write_cache_exclusion(
                state,
                cleared,
            );
            lemma_timers_field_update_preserves_core_control_body(
                state,
                cleared.timers,
            );
            let now = crate::state::spec_now(cleared);
            match listing {
                crate::state_timers::ListingSpec::Prefixes {
                    horizon,
                    ..
                } => {
                    lemma_prefixes_listed_preserves_active_write_cache_exclusion(
                        cleared,
                        horizon,
                        now,
                        response,
                    );
                },
                crate::state_timers::ListingSpec::Buckets {
                    pending,
                    horizon,
                    loaded,
                    failed,
                } => {
                    lemma_bucket_listed_preserves_active_write_cache_exclusion(
                        cleared,
                        pending.remove(op),
                        horizon,
                        loaded,
                        failed,
                        now,
                        response,
                    );
                },
                crate::state_timers::ListingSpec::Extend {
                    bucket,
                    ..
                } => {
                    lemma_extended_preserves_active_write_cache_exclusion(
                        cleared,
                        bucket,
                        now,
                        response,
                    );
                },
                crate::state_timers::ListingSpec::Relist {
                    bucket,
                    ..
                } => {
                    lemma_relisted_preserves_active_write_cache_exclusion(
                        cleared,
                        bucket,
                        now,
                        response,
                    );
                },
            }
        },
        _ => {},
    }
}

}
