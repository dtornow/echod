//! Protocol effects derived from document closure boundaries.
//!
//! The value algebra is in `document.rs`.  This module connects it to the
//! node's imperative notifications and to a complete request transition.
//! Keeping the connection here avoids making persisted document values
//! depend on node transitions.

use vstd::prelude::*;

use echod_types::{PromiseRecord, Request};

#[cfg(verus_keep_ghost)]
use crate::document::{
    document_effects, well_formed, PromiseEffectV, ProtocolEffectKeyV, ProtocolEffectV,
    StoredDocumentV,
};
#[cfg(verus_keep_ghost)]
use crate::node::{
    spec_earliest_in, spec_handle, spec_request_commits, spec_request_document,
    spec_request_transition, spec_run_due, spec_stored_body, spec_stored_committed_at, spec_sweep,
    NoteV,
};
#[cfg(verus_keep_ghost)]
use crate::quick_n_dirty::routed;

verus! {

broadcast use vstd::iset::group_iset_lemmas;

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

pub open spec fn note_effects(notes: Seq<NoteV>) -> Seq<ProtocolEffectV> {
    notes.map_values(|note: NoteV| note_effect(note))
}

pub open spec fn note_effect_keys(notes: Seq<NoteV>) -> Seq<ProtocolEffectKeyV> {
    note_effects(notes).map_values(
        |effect: ProtocolEffectV| crate::document::protocol_effect_key(effect),
    )
}

proof fn lemma_seq_set_add<A>(first: Seq<A>, second: Seq<A>)
    ensures
        (first + second).to_set().to_iset()
            == first.to_set().to_iset().union(second.to_set().to_iset()),
{
    assert forall|value: A| (first + second).to_set().contains(value)
        <==> first.to_set().contains(value) || second.to_set().contains(value) by {
        if (first + second).to_set().contains(value) {
            let i = choose|i: int| 0 <= i < (first + second).len()
                && (first + second)[i] == value;
            if i < first.len() {
                assert(first[i] == value);
            } else {
                assert(second[i - first.len()] == value);
            }
        }
        if first.to_set().contains(value) {
            let i = choose|i: int| 0 <= i < first.len() && first[i] == value;
            assert((first + second)[i] == value);
        }
        if second.to_set().contains(value) {
            let i = choose|i: int| 0 <= i < second.len() && second[i] == value;
            assert((first + second)[first.len() + i] == value);
        }
    };
    assert((first + second).to_set().to_iset()
        =~= first.to_set().to_iset().union(second.to_set().to_iset()));
}

proof fn lemma_note_set_empty()
    ensures
        note_effects(Seq::<NoteV>::empty()).to_set().to_iset()
            == ISet::<ProtocolEffectV>::empty(),
{
    assert(note_effects(Seq::<NoteV>::empty()) =~= Seq::<ProtocolEffectV>::empty());
    assert(Seq::<ProtocolEffectV>::empty().to_set().to_iset()
        =~= ISet::<ProtocolEffectV>::empty());
}

proof fn lemma_note_set_one(note: NoteV)
    ensures
        note_effects(seq![note]).to_set().to_iset() == iset![note_effect(note)],
{
    let effect = note_effect(note);
    assert(note_effects(seq![note]) =~= seq![effect]);
    seq![effect].to_set_ensures();
    assert forall|candidate: ProtocolEffectV|
        seq![effect].to_set().contains(candidate)
            <==> iset![effect].contains(candidate) by {
        if candidate == effect {
            vstd::iset::lemma_iset_insert_same(ISet::empty(), effect);
            assert(seq![effect].to_set().contains(seq![effect][0]));
        } else {
            vstd::iset::lemma_iset_insert_different(
                ISet::<ProtocolEffectV>::empty(),
                candidate,
                effect,
            );
            if seq![effect].to_set().contains(candidate) {
                let i = choose|i: int| 0 <= i < 1 && seq![effect][i] == candidate;
                assert(i == 0);
            }
        }
    };
    assert(seq![effect].to_set().to_iset() =~= iset![effect]);
}

proof fn lemma_retry_document_effects(
    map: Map<Seq<char>, crate::document::ObjV>,
    id: Seq<char>,
    now: u64,
    retry_timeout: u64,
)
    requires
        map.contains_key(id),
        map[id].promise.state == echod_types::PromiseState::Pending,
        map[id].task is Some,
        map[id].task.unwrap().state == echod_types::TaskState::Pending,
        map[id].task.unwrap().retry_timeout_at is Some,
        map[id].task.unwrap().retry_timeout_at.unwrap() <= now,
        map[id].task.unwrap().retry_timeout_at
            != Some(crate::document::effect_rearm_at(now, retry_timeout)),
    ensures
        ({
            let task = map[id].task.unwrap();
            let changed = crate::document::ObjV {
                task: Some(crate::document::TkV {
                    retry_timeout_at: Some(
                        crate::document::effect_rearm_at(now, retry_timeout),
                    ),
                    ..task
                }),
                ..map[id]
            };
            let effect = ProtocolEffectV::Execute { id, version: task.version };
            document_effects(
                crate::document::DocumentBodyV::Workflow(map),
                crate::document::DocumentBodyV::Workflow(map.insert(id, changed)),
                now,
                retry_timeout,
            ) == iset![effect]
        }),
{
    let task = map[id].task.unwrap();
    let changed_task = crate::document::TkV {
        retry_timeout_at: Some(crate::document::effect_rearm_at(now, retry_timeout)),
        ..task
    };
    let changed = crate::document::ObjV { task: Some(changed_task), ..map[id] };
    let after = map.insert(id, changed);
    let expected = ProtocolEffectV::Execute { id, version: task.version };
    assert(changed != map[id]);
    assert forall|effect: ProtocolEffectV|
        document_effects(
            crate::document::DocumentBodyV::Workflow(map),
            crate::document::DocumentBodyV::Workflow(after),
            now,
            retry_timeout,
        ).contains(effect) <==> iset![expected].contains(effect) by {
        match effect {
            ProtocolEffectV::Execute { id: other, version } => {
                if crate::document::offer_rearmed(map, after, other, now, retry_timeout) {
                    if other != id {
                        assert(after[id] == changed);
                        assert(map.insert(
                            other,
                            crate::document::ObjV {
                                task: Some(crate::document::TkV {
                                    retry_timeout_at: Some(
                                        crate::document::effect_rearm_at(now, retry_timeout),
                                    ),
                                    ..map[other].task.unwrap()
                                }),
                                ..map[other]
                            },
                        )[id] == map[id]);
                    }
                }
            },
            ProtocolEffectV::Unblock { promise, address, .. } => {
                if crate::document::listener_unblocked(map, after, promise, address) {
                    if promise != id {
                        assert(after[id] == changed);
                        assert(map.insert(
                            promise,
                            crate::document::ObjV {
                                promise: crate::document::PromV {
                                    listeners: map[promise].promise.listeners.skip(1),
                                    ..map[promise].promise
                                },
                                ..map[promise]
                            },
                        )[id] == map[id]);
                    } else {
                        assert(after[id].task == Some(changed_task));
                        assert(map.insert(
                            id,
                            crate::document::ObjV {
                                promise: crate::document::PromV {
                                    listeners: map[id].promise.listeners.skip(1),
                                    ..map[id].promise
                                },
                                ..map[id]
                            },
                        )[id].task == map[id].task);
                    }
                }
            },
        }
    };
    assert(document_effects(
        crate::document::DocumentBodyV::Workflow(map),
        crate::document::DocumentBodyV::Workflow(after),
        now,
        retry_timeout,
    ) =~= iset![expected]);
}

proof fn lemma_listener_document_effects(
    map: Map<Seq<char>, crate::document::ObjV>,
    id: Seq<char>,
    now: u64,
    retry_timeout: u64,
)
    requires
        map.contains_key(id),
        map[id].promise.listeners.len() > 0,
    ensures
        ({
            let obj = map[id];
            let address = obj.promise.listeners[0];
            let changed = crate::document::ObjV {
                promise: crate::document::PromV {
                    listeners: obj.promise.listeners.skip(1),
                    ..obj.promise
                },
                ..obj
            };
            let record = crate::document::promise_effect(id, changed.promise);
            let effect = ProtocolEffectV::Unblock { promise: id, address, record };
            document_effects(
                crate::document::DocumentBodyV::Workflow(map),
                crate::document::DocumentBodyV::Workflow(map.insert(id, changed)),
                now,
                retry_timeout,
            ) == iset![effect]
        }),
{
    let obj = map[id];
    let address = obj.promise.listeners[0];
    let changed = crate::document::ObjV {
        promise: crate::document::PromV {
            listeners: obj.promise.listeners.skip(1),
            ..obj.promise
        },
        ..obj
    };
    let after = map.insert(id, changed);
    let record = crate::document::promise_effect(id, changed.promise);
    let expected = ProtocolEffectV::Unblock { promise: id, address, record };
    assert(changed.promise.listeners.len() < obj.promise.listeners.len());
    assert(changed != obj);
    assert forall|effect: ProtocolEffectV|
        document_effects(
            crate::document::DocumentBodyV::Workflow(map),
            crate::document::DocumentBodyV::Workflow(after),
            now,
            retry_timeout,
        ).contains(effect) <==> iset![expected].contains(effect) by {
        match effect {
            ProtocolEffectV::Execute { id: other, .. } => {
                if crate::document::offer_rearmed(map, after, other, now, retry_timeout) {
                    if other != id {
                        assert(after[id] == changed);
                        assert(map.insert(
                            other,
                            crate::document::ObjV {
                                task: Some(crate::document::TkV {
                                    retry_timeout_at: Some(
                                        crate::document::effect_rearm_at(now, retry_timeout),
                                    ),
                                    ..map[other].task.unwrap()
                                }),
                                ..map[other]
                            },
                        )[id] == map[id]);
                    } else {
                        assert(after[id].promise == changed.promise);
                        assert(map.insert(
                            id,
                            crate::document::ObjV {
                                task: Some(crate::document::TkV {
                                    retry_timeout_at: Some(
                                        crate::document::effect_rearm_at(now, retry_timeout),
                                    ),
                                    ..map[id].task.unwrap()
                                }),
                                ..map[id]
                            },
                        )[id].promise == map[id].promise);
                    }
                }
            },
            ProtocolEffectV::Unblock { promise, address: other, record: actual } => {
                if crate::document::listener_unblocked(map, after, promise, other) {
                    if promise != id {
                        assert(after[id] == changed);
                        assert(map.insert(
                            promise,
                            crate::document::ObjV {
                                promise: crate::document::PromV {
                                    listeners: map[promise].promise.listeners.skip(1),
                                    ..map[promise].promise
                                },
                                ..map[promise]
                            },
                        )[id] == map[id]);
                    }
                }
            },
        }
    };
    assert(document_effects(
        crate::document::DocumentBodyV::Workflow(map),
        crate::document::DocumentBodyV::Workflow(after),
        now,
        retry_timeout,
    ) =~= iset![expected]);
}

proof fn lemma_single_update_no_effects(
    map: Map<Seq<char>, crate::document::ObjV>,
    id: Seq<char>,
    changed: crate::document::ObjV,
    now: u64,
    retry_timeout: u64,
)
    requires
        map.contains_key(id),
        changed != map[id],
        !crate::document::offer_rearmed(
            map,
            map.insert(id, changed),
            id,
            now,
            retry_timeout,
        ),
        forall|address: Seq<char>| !crate::document::listener_unblocked(
            map,
            map.insert(id, changed),
            id,
            address,
        ),
    ensures
        document_effects(
            crate::document::DocumentBodyV::Workflow(map),
            crate::document::DocumentBodyV::Workflow(map.insert(id, changed)),
            now,
            retry_timeout,
        ) == ISet::<ProtocolEffectV>::empty(),
{
    let after = map.insert(id, changed);
    assert forall|effect: ProtocolEffectV|
        !document_effects(
            crate::document::DocumentBodyV::Workflow(map),
            crate::document::DocumentBodyV::Workflow(after),
            now,
            retry_timeout,
        ).contains(effect) by {
        match effect {
            ProtocolEffectV::Execute { id: other, .. } => {
                if crate::document::offer_rearmed(map, after, other, now, retry_timeout)
                    && other != id
                {
                    assert(after[id] == changed);
                    assert(map.insert(
                        other,
                        crate::document::ObjV {
                            task: Some(crate::document::TkV {
                                retry_timeout_at: Some(
                                    crate::document::effect_rearm_at(now, retry_timeout),
                                ),
                                ..map[other].task.unwrap()
                            }),
                            ..map[other]
                        },
                    )[id] == map[id]);
                }
            },
            ProtocolEffectV::Unblock { promise, address, .. } => {
                if crate::document::listener_unblocked(map, after, promise, address)
                    && promise != id
                {
                    assert(after[id] == changed);
                    assert(map.insert(
                        promise,
                        crate::document::ObjV {
                            promise: crate::document::PromV {
                                listeners: map[promise].promise.listeners.skip(1),
                                ..map[promise].promise
                            },
                            ..map[promise]
                        },
                    )[id] == map[id]);
                }
            },
        }
    };
    assert(document_effects(
        crate::document::DocumentBodyV::Workflow(map),
        crate::document::DocumentBodyV::Workflow(after),
        now,
        retry_timeout,
    ) =~= ISet::<ProtocolEffectV>::empty());
}

/// Effects derived from every old/new document pair in one bounded closure.
/// This mirrors only the closure's document path; it never reads its notes.
pub open spec fn closure_effects(
    doc: crate::document::DocumentBodyV,
    now: u64,
    retry_timeout: u64,
    limit: nat,
) -> ISet<ProtocolEffectV>
    decreases limit,
{
    if limit == 0 {
        ISet::empty()
    } else {
        let (next, _, _, _) = spec_run_due(doc, now, retry_timeout);
        if next == doc {
            ISet::empty()
        } else {
            document_effects(doc, next, now, retry_timeout).union(
                closure_effects(next, now, retry_timeout, (limit - 1) as nat),
            )
        }
    }
}

/// Effects of a complete request, derived only by comparing document values.
///
/// The pre-handler closure and post-handler closure are compared separately.
/// The request is needed to identify the post-handler input.  Initial/final
/// documents alone are insufficient: for example, a due pending task can be
/// rearmed (emitting Execute) in the pre-sweep and then acquired by the
/// handler, so the final acquired task no longer contains the rearm marker.
pub open spec fn request_effects(
    doc: crate::document::DocumentBodyV,
    request: Request,
    now: u64,
    retry_timeout: u64,
    limit: nat,
) -> ISet<ProtocolEffectV> {
    let (before, _, _) = spec_sweep(doc, now, retry_timeout, limit);
    if spec_earliest_in(before, now) is Some {
        ISet::empty()
    } else {
        let (handled, _) = spec_handle(before, request, now);
        let (after, _, _) = spec_sweep(handled, now, retry_timeout, limit);
        if spec_earliest_in(after, now) is Some {
            ISet::empty()
        } else {
            match spec_request_document(request) {
                Some(document) if crate::document::body_well_formed(document, after, now) =>
                    closure_effects(doc, now, retry_timeout, limit).union(
                        closure_effects(handled, now, retry_timeout, limit),
                    ),
                _ => ISet::empty(),
            }
        }
    }
}

pub open spec fn one_step_effects_match(
    doc: crate::document::DocumentBodyV,
    now: u64,
    retry_timeout: u64,
) -> bool {
    let (next, _, _, notes) = spec_run_due(doc, now, retry_timeout);
    next != doc ==> note_effects(notes).to_set().to_iset()
        == document_effects(doc, next, now, retry_timeout)
}

proof fn lemma_one_step_effects(
    doc: crate::document::DocumentBodyV,
    now: u64,
    retry_timeout: u64,
)
    ensures
        ({
            let (next, _, _, notes) = spec_run_due(doc, now, retry_timeout);
            next != doc ==> note_effects(notes).to_set().to_iset()
                == document_effects(doc, next, now, retry_timeout)
        }),
{
    let (next, _, _, notes) = spec_run_due(doc, now, retry_timeout);
    lemma_note_set_empty();
    match doc {
        crate::document::DocumentBodyV::Schedule(slot) => {
            assert(notes =~= Seq::<NoteV>::empty());
            assert(next is Schedule);
            assert(document_effects(doc, next, now, retry_timeout) =~= ISet::empty());
            assert(one_step_effects_match(doc, now, retry_timeout));
        },
        crate::document::DocumentBodyV::Workflow(map) => {
            let keys = crate::node::spec_sorted_present(map);
            crate::timers::lemma_sorted(map.dom());
            assert forall|i: int| 0 <= i < keys.len() implies
                map.contains_key(#[trigger] keys[i]) by {
                assert(map.dom().contains(keys[i]));
            };
            crate::timers::lemma_due_id(map, keys, now);
            match crate::node::spec_due_id(map, keys, now) {
                None => {
                    assert(next == doc);
                    assert(notes =~= Seq::<NoteV>::empty());
                    assert(one_step_effects_match(doc, now, retry_timeout));
                },
                Some(id) => {
                    let obj = map[id];
                    let (map2, step_notes) =
                        crate::node::spec_step_object(map, id, now, retry_timeout);
                    assert(next == crate::document::DocumentBodyV::Workflow(map2));
                    assert(notes == step_notes);
                    if obj.promise.state == echod_types::PromiseState::Pending
                        && obj.promise.timeout_at <= now
                    {
                        let changed = crate::node::spec_project_obj(obj, now);
                        assert(map2 == map.insert(id, changed));
                        assert(changed.promise.state
                            != echod_types::PromiseState::Pending);
                        assert(changed != obj);
                        assert(!crate::document::offer_rearmed(
                            map,
                            map.insert(id, changed),
                            id,
                            now,
                            retry_timeout,
                        )) by {
                            if crate::document::offer_rearmed(
                                map,
                                map.insert(id, changed),
                                id,
                                now,
                                retry_timeout,
                            ) {
                                let expected = crate::document::ObjV {
                                    task: Some(crate::document::TkV {
                                        retry_timeout_at: Some(
                                            crate::document::effect_rearm_at(
                                                now,
                                                retry_timeout,
                                            ),
                                        ),
                                        ..obj.task.unwrap()
                                    }),
                                    ..obj
                                };
                                assert(map.insert(id, changed)[id].promise
                                    == changed.promise);
                                assert(map.insert(id, expected)[id].promise
                                    == obj.promise);
                            }
                        };
                        assert forall|address: Seq<char>|
                            !crate::document::listener_unblocked(
                                map,
                                map.insert(id, changed),
                                id,
                                address,
                            ) by {
                            if crate::document::listener_unblocked(
                                map,
                                map.insert(id, changed),
                                id,
                                address,
                            ) {
                                assert(map.insert(id, changed)[id].promise.listeners
                                    == obj.promise.listeners);
                                assert(map.insert(
                                    id,
                                    crate::document::ObjV {
                                        promise: crate::document::PromV {
                                            listeners: obj.promise.listeners.skip(1),
                                            ..obj.promise
                                        },
                                        ..obj
                                    },
                                )[id].promise.listeners
                                    == obj.promise.listeners.skip(1));
                                assert(obj.promise.listeners.skip(1).len()
                                    < obj.promise.listeners.len());
                            }
                        };
                        lemma_single_update_no_effects(
                            map,
                            id,
                            changed,
                            now,
                            retry_timeout,
                        );
                        assert(notes =~= Seq::<NoteV>::empty());
                        assert(one_step_effects_match(doc, now, retry_timeout));
                    } else if obj.promise.state == echod_types::PromiseState::Pending {
                        match obj.task {
                            Some(task) if task.state == echod_types::TaskState::Acquired
                                && match task.lease_timeout_at {
                                    Some(at) => at <= now,
                                    None => false,
                                } => {
                                let changed = crate::document::ObjV {
                                    task: Some(crate::node::spec_unlease(
                                        task,
                                        echod_types::TaskState::Pending,
                                        Some(now),
                                    )),
                                    ..obj
                                };
                                assert(map2 == map.insert(id, changed));
                                assert(changed != obj);
                                assert(!crate::document::offer_rearmed(
                                    map,
                                    map.insert(id, changed),
                                    id,
                                    now,
                                    retry_timeout,
                                ));
                                assert forall|address: Seq<char>|
                                    !crate::document::listener_unblocked(
                                        map,
                                        map.insert(id, changed),
                                        id,
                                        address,
                                    ) by {
                                    if crate::document::listener_unblocked(
                                        map,
                                        map.insert(id, changed),
                                        id,
                                        address,
                                    ) {
                                        assert(map.insert(id, changed)[id].task
                                            == changed.task);
                                        assert(map.insert(
                                            id,
                                            crate::document::ObjV {
                                                promise: crate::document::PromV {
                                                    listeners: obj.promise.listeners.skip(1),
                                                    ..obj.promise
                                                },
                                                ..obj
                                            },
                                        )[id].task == obj.task);
                                        assert(changed.task != obj.task);
                                        assert(obj.promise.listeners.skip(1).len()
                                            < obj.promise.listeners.len());
                                    }
                                };
                                lemma_single_update_no_effects(
                                    map,
                                    id,
                                    changed,
                                    now,
                                    retry_timeout,
                                );
                                assert(notes =~= Seq::<NoteV>::empty());
                                assert(one_step_effects_match(doc, now, retry_timeout));
                            },
                            Some(task) if task.state == echod_types::TaskState::Pending
                                && match task.retry_timeout_at {
                                    Some(at) => at <= now,
                                    None => false,
                                } => {
                                let changed = crate::document::ObjV {
                                    task: Some(crate::document::TkV {
                                        retry_timeout_at: Some(
                                            crate::store::spec_sat_add(now, retry_timeout),
                                        ),
                                        ..task
                                    }),
                                    ..obj
                                };
                                assert(crate::document::effect_rearm_at(
                                    now,
                                    retry_timeout,
                                ) == crate::store::spec_sat_add(now, retry_timeout));
                                assert(map2 == map.insert(id, changed));
                                let note = NoteV::Execute {
                                    id,
                                    version: task.version,
                                };
                                assert(notes == seq![note]);
                                lemma_note_set_one(note);
                                if task.retry_timeout_at
                                    != Some(crate::document::effect_rearm_at(
                                        now,
                                        retry_timeout,
                                    ))
                                {
                                    lemma_retry_document_effects(
                                        map,
                                        id,
                                        now,
                                        retry_timeout,
                                    );
                                } else {
                                    assert(changed == obj);
                                    assert(map2 == map);
                                    assert(next == doc);
                                }
                                assert(one_step_effects_match(doc, now, retry_timeout));
                            },
                            _ => {
                                assert(map2 == map);
                                assert(notes =~= Seq::<NoteV>::empty());
                                assert(next == doc);
                                assert(one_step_effects_match(doc, now, retry_timeout));
                            },
                        }
                    } else if obj.promise.callbacks.len() > 0 {
                        let awaiter = obj.promise.callbacks[0];
                        let since = match obj.promise.settled_at {
                            Some(at) => at,
                            None => 0,
                        };
                        let changed = crate::document::ObjV {
                            promise: crate::document::PromV {
                                callbacks: obj.promise.callbacks.skip(1),
                                ..obj.promise
                            },
                            ..obj
                        };
                        assert(obj.promise.callbacks.skip(1).len()
                            < obj.promise.callbacks.len());
                        assert(map2 == crate::node::spec_resume(
                            map.insert(id, changed),
                            awaiter,
                            id,
                            since,
                            now,
                        ));
                        assert(notes =~= Seq::<NoteV>::empty());
                        if next != doc {
                            assert(document_effects(
                                doc,
                                next,
                                now,
                                retry_timeout,
                            ) == ISet::<ProtocolEffectV>::empty());
                        }
                        assert(one_step_effects_match(doc, now, retry_timeout));
                    } else if obj.promise.listeners.len() > 0 {
                        let address = obj.promise.listeners[0];
                        let changed = crate::document::ObjV {
                            promise: crate::document::PromV {
                                listeners: obj.promise.listeners.skip(1),
                                ..obj.promise
                            },
                            ..obj
                        };
                        assert(map2 == map.insert(id, changed));
                        lemma_listener_document_effects(
                            map,
                            id,
                            now,
                            retry_timeout,
                        );
                        crate::interpret::lemma_string_view(id);
                        let promise = crate::node::spec_record(
                            crate::model::spec_string(id),
                            obj.promise,
                        );
                        let note = NoteV::Unblock { address, promise };
                        assert(notes == seq![note]);
                        lemma_note_set_one(note);
                        assert(record_effect(promise)
                            == crate::document::promise_effect(id, changed.promise));
                        assert(one_step_effects_match(doc, now, retry_timeout));
                    } else {
                        assert(map2 == map);
                        assert(notes =~= Seq::<NoteV>::empty());
                        assert(next == doc);
                        assert(one_step_effects_match(doc, now, retry_timeout));
                    }
                },
            }
        },
    }
    if next != doc {
        assert forall|effect: ProtocolEffectV|
            note_effects(notes).to_set().contains(effect)
                <==> document_effects(doc, next, now, retry_timeout).contains(effect) by {
            match effect {
                ProtocolEffectV::Execute { .. } => {
                    assert(note_effects(notes).to_set().contains(effect)
                        <==> document_effects(
                            doc,
                            next,
                            now,
                            retry_timeout,
                        ).contains(effect));
                },
                ProtocolEffectV::Unblock { .. } => {
                    assert(note_effects(notes).to_set().contains(effect)
                        <==> document_effects(
                            doc,
                            next,
                            now,
                            retry_timeout,
                        ).contains(effect));
                },
            }
        };
        assert(note_effects(notes).to_set().to_iset()
            =~= document_effects(doc, next, now, retry_timeout));
    }
}

proof fn lemma_closure_effects(
    doc: crate::document::DocumentBodyV,
    now: u64,
    retry_timeout: u64,
    limit: nat,
)
    ensures
        ({
            let (_, _, notes) = spec_sweep(doc, now, retry_timeout, limit);
            note_effects(notes).to_set().to_iset()
                == closure_effects(doc, now, retry_timeout, limit)
        }),
    decreases limit,
{
    if limit > 0 {
        let (next, _, _, notes) = spec_run_due(doc, now, retry_timeout);
        lemma_one_step_effects(doc, now, retry_timeout);
        if next != doc {
            lemma_closure_effects(next, now, retry_timeout, (limit - 1) as nat);
            let (_, _, more) = spec_sweep(next, now, retry_timeout, (limit - 1) as nat);
            assert(note_effects(notes + more) =~= note_effects(notes) + note_effects(more));
            lemma_seq_set_add(note_effects(notes), note_effects(more));
        }
    }
}

/// Complete effect correspondence for the imperative request transition.
///
/// Under the same well-formedness, routing, and monotone-time preconditions
/// as local request preservation, the emitted sequence denotes exactly the
/// derived unordered keyed set, including each effect's payload.  The
/// executable regression suite separately checks that the imperative sequence
/// itself contains no duplicate protocol keys.
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
    ensures
        ({
            let (_, _, _, notes) = spec_request_transition(
                spec_stored_body(document),
                request,
                now,
                retry_timeout,
                limit,
            );
            &&& note_effects(notes).to_set().to_iset() == request_effects(
                spec_stored_body(document),
                request,
                now,
                retry_timeout,
                limit,
            )
        }),
{
    let doc = spec_stored_body(document);
    let (_, _, _, notes) =
        spec_request_transition(doc, request, now, retry_timeout, limit);
    if spec_request_commits(doc, request, now, retry_timeout, limit) {
        let (before, _, notes_before) = spec_sweep(doc, now, retry_timeout, limit);
        let (handled, _) = spec_handle(before, request, now);
        let (after, _, notes_after) = spec_sweep(handled, now, retry_timeout, limit);
        lemma_closure_effects(doc, now, retry_timeout, limit);
        lemma_closure_effects(handled, now, retry_timeout, limit);
        assert(notes == notes_before + notes_after);
        assert(note_effects(notes) =~= note_effects(notes_before) + note_effects(notes_after));
        lemma_seq_set_add(note_effects(notes_before), note_effects(notes_after));
    } else {
        assert(notes =~= Seq::<NoteV>::empty());
    }
    assert(note_effects(notes).to_set().to_iset()
        == request_effects(doc, request, now, retry_timeout, limit));
}

} // verus!
