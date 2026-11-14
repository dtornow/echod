//! Machine-checked proofs for the concrete integrity claims.
//! Each helper discharges one structural operation used by the public theorem;
//! no semantic step is assumed or skipped.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use echod_abstract_spec::Call;
use rover_spec::rover::comm::{ProcessEvent, Time};
use rover_spec::rover::RoverSpec::Proc as _;

use crate::rover::{
    spec_node, spec_nodes, spec_store, spec_world, Config, Message, Pid, Proc,
};
use crate::state::{
    spec_begin, spec_cached, spec_commit, spec_decide, spec_earliest_from,
    spec_earliest_key, spec_fail, spec_forget, spec_body_is_empty, spec_keep,
    spec_min_key, spec_owns, spec_remember, spec_request, spec_sorted,
    spec_store_reply, spec_timeout, CachedV, DocumentBodyV, FlightV, NodeV,
};
use crate::property_claim::*;
use crate::state::{
    spec_apply, spec_before, spec_bump, spec_find, spec_insert_at, spec_put,
    spec_remove_at, EntryV, StoreReq, StoreRes, StoreV,
};

verus! {

proof fn lemma_before_irreflexive(a: Seq<char>)
    ensures
        !spec_before(a, a),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_before_irreflexive(a.drop_first());
    }
}

proof fn lemma_before_transitive(a: Seq<char>, b: Seq<char>, c: Seq<char>)
    requires
        spec_before(a, b),
        spec_before(b, c),
    ensures
        spec_before(a, c),
    decreases a.len() + b.len() + c.len(),
{
    if a.len() > 0 && b.len() > 0 && c.len() > 0
        && a[0] == b[0] && b[0] == c[0]
    {
        lemma_before_transitive(
            a.drop_first(),
            b.drop_first(),
            c.drop_first(),
        );
    }
}

proof fn lemma_before_total(a: Seq<char>, b: Seq<char>)
    requires
        a != b,
    ensures
        spec_before(a, b) || spec_before(b, a),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        if b.len() == 0 {
            assert(a =~= b);
            assert(a == b);
        }
    } else if b.len() == 0 {
    } else if a[0] < b[0] {
    } else if b[0] < a[0] {
    } else {
        assert(a[0] == b[0]);
        if a.drop_first() == b.drop_first() {
            assert(a.drop_first().len() == a.len() - 1);
            assert(b.drop_first().len() == b.len() - 1);
            assert(a.len() == b.len());
            assert forall|i: int| 0 <= i < a.len()
                implies #[trigger] a[i] == #[trigger] b[i] by {
                if i > 0 {
                    assert(a[i] == a.drop_first()[i - 1]);
                    assert(b[i] == b.drop_first()[i - 1]);
                }
            };
            assert(a =~= b);
            assert(a == b);
        } else {
            lemma_before_total(a.drop_first(), b.drop_first());
        }
    }
}

spec fn least(keys: Set<Seq<char>>, key: Seq<char>) -> bool {
    keys.contains(key)
        && forall|other: Seq<char>| keys.contains(other)
            ==> !spec_before(other, key)
}

proof fn lemma_least_exists(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        exists|key: Seq<char>| least(keys, key),
    decreases keys.len(),
{
    let x = keys.choose();
    assert(keys.contains(x));
    let rest = keys.remove(x);
    assert(rest.len() == keys.len() - 1);
    if rest.len() == 0 {
        assert forall|other: Seq<char>| keys.contains(other)
            implies !spec_before(other, x) by {
            if other == x {
                lemma_before_irreflexive(x);
            } else {
                assert(rest.contains(other));
            }
        };
        assert(least(keys, x));
    } else {
        lemma_least_exists(rest);
        let m = choose|key: Seq<char>| least(rest, key);
        if spec_before(x, m) {
            assert forall|other: Seq<char>| keys.contains(other)
                implies !spec_before(other, x) by {
                if other == x {
                    lemma_before_irreflexive(x);
                } else {
                    assert(rest.contains(other));
                    if spec_before(other, x) {
                        lemma_before_transitive(other, x, m);
                    }
                }
            };
            assert(least(keys, x));
        } else {
            assert forall|other: Seq<char>| keys.contains(other)
                implies !spec_before(other, m) by {
                if other != x {
                    assert(rest.contains(other));
                }
            };
            assert(least(keys, m));
        }
    }
}

proof fn lemma_min_key_least(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        least(keys, spec_min_key(keys)),
{
    reveal(spec_min_key);
    lemma_least_exists(keys);
}

proof fn lemma_sorted_properties(keys: Set<Seq<char>>)
    requires
        keys.finite(),
    ensures
        ({
            let ordered = spec_sorted(keys);
            &&& keys_strictly_sorted(ordered)
            &&& ordered.no_duplicates()
            &&& forall|key: Seq<char>| #[trigger] ordered.contains(key)
                <==> keys.contains(key)
        }),
    decreases keys.len(),
{
    if keys.len() == 0 {
        assert(spec_sorted(keys) =~= Seq::<Seq<char>>::empty());
    } else {
        lemma_min_key_least(keys);
        let first = spec_min_key(keys);
        let rest = keys.remove(first);
        lemma_sorted_properties(rest);
        let tail = spec_sorted(rest);
        let ordered = seq![first] + tail;
        assert(spec_sorted(keys) == ordered);

        assert forall|key: Seq<char>| #[trigger] ordered.contains(key)
            <==> keys.contains(key) by {
            if ordered.contains(key) {
                let i = choose|i: int| 0 <= i < ordered.len()
                    && #[trigger] ordered[i] == key;
                if i == 0 {
                    assert(key == first);
                } else {
                    assert(ordered[i] == tail[i - 1]);
                    assert(tail.contains(key));
                    assert(rest.contains(key));
                }
            } else if keys.contains(key) {
                if key == first {
                    assert(ordered[0] == first);
                    assert(ordered.contains(key));
                } else {
                    assert(rest.contains(key));
                    assert(tail.contains(key));
                    let i = choose|i: int| 0 <= i < tail.len()
                        && #[trigger] tail[i] == key;
                    assert(ordered[i + 1] == tail[i]);
                    assert(ordered.contains(key));
                }
            }
        };

        assert forall|i: int, j: int| 0 <= i < j < ordered.len()
            implies spec_before(#[trigger] ordered[i], #[trigger] ordered[j]) by {
            if i == 0 {
                let other = ordered[j];
                assert(tail.contains(other));
                assert(rest.contains(other));
                assert(other != first);
                lemma_before_total(first, other);
                if spec_before(other, first) {
                    assert(!spec_before(other, first));
                }
            } else {
                assert(ordered[i] == tail[i - 1]);
                assert(ordered[j] == tail[j - 1]);
            }
        };

        assert forall|i: int, j: int|
            0 <= i < ordered.len() && 0 <= j < ordered.len() && i != j
            implies ordered[i] != ordered[j] by {
            if i < j {
                lemma_before_irreflexive(ordered[i]);
            } else {
                lemma_before_irreflexive(ordered[j]);
            }
        };
    }
}

proof fn lemma_document_object_order(doc: DocumentBodyV)
    ensures
        document_object_order(doc),
{
    match doc {
        DocumentBodyV::Workflow(map) => {
            lemma_sorted_properties(map.dom());
        },
        DocumentBodyV::Schedule(_) => {},
    }
}

proof fn lemma_nodes_layout(config: Config, id: u64)
    requires
        id <= config.nodes,
    ensures
        ({
            let nodes = spec_nodes(config, id);
            &&& nodes.len() == (config.nodes - id) as nat
            &&& forall|k: int| 0 <= k < nodes.len()
                ==> #[trigger] nodes[k].0 == Pid::Node((id + k) as u64)
            &&& forall|i: int, j: int| 0 <= i < j < nodes.len()
                ==> #[trigger] nodes[i].0 != #[trigger] nodes[j].0
        }),
    decreases config.nodes - id,
{
    if id < config.nodes {
        lemma_nodes_layout(config, (id + 1) as u64);
    }
}

proof fn lemma_process_layout(config: Config)
    ensures
        process_layout(config),
{
    lemma_nodes_layout(config, 0);
    let nodes = spec_nodes(config, 0);
    let world = spec_world(config);
    assert(world == nodes + seq![(Pid::Store, crate::rover::Proc::Store(
        crate::state::StoreV {
            entries: Seq::empty(),
            appendable: config.appendable,
            seen: Seq::empty(),
        },
    ))]);
    assert forall|i: int, j: int| 0 <= i < j < world.len()
        implies #[trigger] world[i].0 != #[trigger] world[j].0 by {
        if j < nodes.len() {
        } else {
            assert(j == nodes.len());
            assert(world[j].0 == Pid::Store);
            assert(i < nodes.len());
            assert(world[i].0 == nodes[i].0);
        }
    };
}

proof fn lemma_remember_integrity(
    node: NodeV,
    key: Seq<char>,
    body: Seq<u8>,
    etag: Option<Seq<char>>,
    i: int,
)
    requires
        document_keys_unique(node),
        document_key_ownership(node),
        spec_owns(node, key),
        0 <= i <= node.documents.len(),
        forall|k: int| 0 <= k < i
            ==> #[trigger] node.documents[k].key != key,
    ensures
        ({
            let next = NodeV {
                documents: spec_remember(node.documents, key, body, etag, i),
                ..node
            };
            document_keys_unique(next) && document_key_ownership(next)
        }),
    decreases node.documents.len() - i,
{
    let docs = node.documents;
    let next_docs = spec_remember(docs, key, body, etag, i);
    let next = NodeV { documents: next_docs, ..node };
    if i >= docs.len() {
        assert(next_docs == docs.push(CachedV { key, body, etag }));
        assert forall|j: int, k: int| 0 <= j < k < next_docs.len()
            implies #[trigger] next_docs[j].key != #[trigger] next_docs[k].key by {
            if k == docs.len() {
                assert(next_docs[j] == docs[j]);
            }
        };
        assert forall|k: int| 0 <= k < next_docs.len()
            implies spec_owns(next, #[trigger] next_docs[k].key) by {
            if k < docs.len() {
                assert(next_docs[k] == docs[k]);
                assert(spec_owns(node, docs[k].key));
            }
        };
    } else if docs[i].key == key {
        assert(next_docs == docs.update(i, CachedV { key, body, etag }));
        assert forall|j: int, k: int| 0 <= j < k < next_docs.len()
            implies #[trigger] next_docs[j].key != #[trigger] next_docs[k].key by {
            if j != i {
                assert(next_docs[j].key == docs[j].key);
            }
            if k != i {
                assert(next_docs[k].key == docs[k].key);
            }
        };
        assert forall|k: int| 0 <= k < next_docs.len()
            implies spec_owns(next, #[trigger] next_docs[k].key) by {
            if k != i {
                assert(next_docs[k] == docs[k]);
                assert(spec_owns(node, docs[k].key));
            }
        };
    } else {
        lemma_remember_integrity(node, key, body, etag, i + 1);
    }
}

proof fn lemma_forget_integrity(node: NodeV, key: Seq<char>, i: int)
    requires
        document_keys_unique(node),
        document_key_ownership(node),
        0 <= i <= node.documents.len(),
    ensures
        ({
            let next = NodeV {
                documents: spec_forget(node.documents, key, i),
                ..node
            };
            document_keys_unique(next) && document_key_ownership(next)
        }),
    decreases node.documents.len() - i,
{
    let docs = node.documents;
    let next_docs = spec_forget(docs, key, i);
    let next = NodeV { documents: next_docs, ..node };
    if i >= docs.len() {
    } else if docs[i].key == key {
        assert(next_docs == docs.take(i) + docs.skip(i + 1));
        assert forall|k: int| 0 <= k < next_docs.len()
            implies #[trigger] next_docs[k]
                == if k < i { docs[k] } else { docs[k + 1] } by {
            if k < i {
                assert(next_docs[k] == docs.take(i)[k]);
            } else {
                assert(next_docs[k] == docs.skip(i + 1)[k - i]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next_docs.len()
            implies #[trigger] next_docs[j].key != #[trigger] next_docs[k].key by {};
        assert forall|k: int| 0 <= k < next_docs.len()
            implies spec_owns(next, #[trigger] next_docs[k].key) by {};
    } else {
        lemma_forget_integrity(node, key, i + 1);
    }
}

proof fn lemma_keep_integrity(
    node: NodeV,
    key: Seq<char>,
    doc: DocumentBodyV,
    etag: Option<Seq<char>>,
)
    requires
        document_keys_unique(node),
        document_key_ownership(node),
        spec_owns(node, key),
    ensures
        ({
            let next = NodeV {
                documents: spec_keep(node.documents, key, doc, etag),
                ..node
            };
            document_keys_unique(next) && document_key_ownership(next)
        }),
{
    if spec_body_is_empty(doc) && etag is None {
        lemma_forget_integrity(node, key, 0);
    } else {
        lemma_remember_integrity(node, key, crate::state::spec_encode_body(doc), etag, 0);
    }
}

proof fn lemma_earliest_from_cached(
    node: NodeV,
    docs: Seq<CachedV>,
    i: int,
    now: Time,
    best: Option<(u64, Seq<char>)>,
)
    requires
        0 <= i <= docs.len(),
        match best {
            Some((_, key)) => exists|k: int| 0 <= k < docs.len()
                && #[trigger] docs[k].key == key,
            None => true,
        },
    ensures
        match spec_earliest_from(node, docs, i, now, best) {
            Some(key) => exists|k: int| 0 <= k < docs.len()
                && #[trigger] docs[k].key == key,
            None => true,
        },
    decreases docs.len() - i,
{
    if i < docs.len() {
        match crate::state::spec_earliest_in(
            crate::state::spec_read(docs[i].key, docs[i].body),
            now,
        ) {
            Some(at) if spec_owns(node, docs[i].key) => {
                let better = match best { None => true, Some((b, _)) => at < b };
                let next_best = if better { Some((at, docs[i].key)) } else { best };
                assert(match next_best {
                    Some((_, key)) => exists|k: int| 0 <= k < docs.len()
                        && #[trigger] docs[k].key == key,
                    None => true,
                }) by {
                    if better {
                        assert(docs[i].key == docs[i].key);
                    }
                };
                lemma_earliest_from_cached(node, docs, i + 1, now, next_best);
            },
            _ => {
                lemma_earliest_from_cached(node, docs, i + 1, now, best);
            },
        }
    }
}

proof fn lemma_earliest_owned(node: NodeV, now: Time)
    requires
        document_key_ownership(node),
    ensures
        match spec_earliest_key(node, now) {
            Some(key) => spec_owns(node, key),
            None => true,
        },
{
    lemma_earliest_from_cached(node, node.documents, 0, now, None);
    match spec_earliest_key(node, now) {
        Some(key) => {
            let i = choose|i: int| 0 <= i < node.documents.len()
                && #[trigger] node.documents[i].key == key;
            assert(spec_owns(node, node.documents[i].key));
        },
        None => {},
    }
}

proof fn lemma_commit_integrity(node: NodeV, flight: FlightV, tag: crate::state::Etag)
    requires
        state_properties(Proc::Node(node)),
        spec_owns(node, flight.key),
    ensures
        ({
            let next = spec_commit(node, flight, tag).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    match flight.decided {
        Some(body) => {
            lemma_remember_integrity(node, flight.key, body, Some(tag.0@), 0);
        },
        None => {},
    }
}

proof fn lemma_decide_integrity(node: NodeV, flight: FlightV, doc: DocumentBodyV)
    requires
        state_properties(Proc::Node(node)),
        node.flight is None,
        spec_owns(node, flight.key),
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_decide(node, flight, doc).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    let (next_doc, reply, born, notify) = match flight.job {
        crate::state::JobV::External(request) => {
            let (next, response) = crate::state::spec_handle(doc, request, flight.now);
            (next, Some(response), Seq::empty(), Seq::empty())
        },
        crate::state::JobV::Due => crate::state::spec_run_due(doc, flight.now, node.retry_timeout),
        crate::state::JobV::Occurrence(pending) => (
            crate::state::spec_occurrence(doc, pending, flight.now),
            None,
            Seq::empty(),
            Seq::empty(),
        ),
    };
    let previous = match spec_cached(node, flight.key) {
        Some(cached) => crate::state::spec_read(flight.key, cached.body),
        None => crate::state::spec_empty_body(flight.key),
    };
    if next_doc == previous && born.len() == 0 {
        lemma_keep_integrity(node, flight.key, next_doc, flight.etag);
    } else {
        assert(node.next_op < (node.next_op + 1) as u64);
    }
}

proof fn lemma_begin_integrity(
    node: NodeV,
    key: Seq<char>,
    job: crate::state::JobV,
    now: Time,
    caller: Option<(Seq<char>, u64)>,
)
    requires
        state_properties(Proc::Node(node)),
        node.flight is None,
        spec_owns(node, key),
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_begin(node, key, job, now, caller).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    match spec_cached(node, key) {
        Some(cached) => {
            lemma_decide_integrity(
                node,
                crate::state::spec_flight(0, key, cached.etag, now, caller, job),
                crate::state::spec_read(key, cached.body),
            );
        },
        None => {
            assert(node.next_op < (node.next_op + 1) as u64);
        },
    }
}

proof fn lemma_request_integrity(node: NodeV, now: Time, request: Call)
    requires
        state_properties(Proc::Node(node)),
        node.flight is None,
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_request(node, now, request).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    match crate::state::spec_key(request.request) {
        Some(key) if spec_owns(node, key) => {
            lemma_begin_integrity(
                node,
                key,
                crate::state::JobV::External(request.request),
                now,
                Some((request.client@, request.id)),
            );
        },
        _ => {},
    }
}

proof fn lemma_timeout_integrity(node: NodeV, now: Time)
    requires
        state_properties(Proc::Node(node)),
        node.flight is None,
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_timeout(node, now).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    if node.pending.len() > 0 {
        let pending = node.pending[0];
        let without = NodeV { pending: node.pending.skip(1), ..node };
        let key = crate::state::spec_origin_key(echod_types::origin(pending.promise));
        if spec_owns(without, key) {
            lemma_begin_integrity(
                without,
                key,
                crate::state::JobV::Occurrence(pending),
                now,
                None,
            );
        }
    } else {
        lemma_earliest_owned(node, now);
        match spec_earliest_key(node, now) {
            Some(key) => {
                lemma_begin_integrity(node, key, crate::state::JobV::Due, now, None);
            },
            None => {},
        }
    }
}

proof fn lemma_store_reply_integrity(
    node: NodeV,
    op: u64,
    response: StoreRes,
)
    requires
        state_properties(Proc::Node(node)),
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_store_reply(node, op, response).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    match node.flight {
        Some(flight) if flight.op == op => {
            if !flight.writing {
                match response {
                    StoreRes::Get { result: Ok(got) } => {
                        let (doc, etag) = match got {
                            Some((body, tag)) => (
                                crate::state::spec_read(flight.key, body@),
                                Some(tag.0@),
                            ),
                            None => (crate::state::spec_empty_body(flight.key), None),
                        };
                        lemma_decide_integrity(
                            NodeV { flight: None, ..node },
                            FlightV { etag, ..flight },
                            doc,
                        );
                    },
                    _ => {},
                }
            } else {
                match response {
                    StoreRes::PutIfNoneMatch { result: Ok(tag) } | StoreRes::PutIfMatch { result: Ok(tag) } => {
                        lemma_commit_integrity(node, flight, tag);
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

proof fn lemma_node_step_integrity(
    config: Config,
    node: NodeV,
    now: Time,
    event: ProcessEvent<Pid, Message>,
)
    requires
        state_properties(Proc::Node(node)),
    ensures
        forall|i: int| 0 <= i < spec_node(node, now, event).len() ==> {
            let next = #[trigger] spec_node(node, now, event)[i].state;
            &&& state_properties(next)
            &&& transition_properties(Proc::Node(node), next)
        },
{
    match event {
        ProcessEvent::Timeout => {
            match node.wake {
                Some(at) if at <= now as nat && node.flight is None
                    && node.next_op < u64::MAX => {
                    lemma_timeout_integrity(node, now);
                },
                _ => {},
            }
        },
        ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(request),
        } => {
            if node.flight is None && node.next_op != u64::MAX {
                lemma_request_integrity(node, now, request);
            }
        },
        ProcessEvent::Receive {
            sender: Pid::Store,
            message: Message::StoreRes { op, response },
        } => {
            if node.flight is Some && node.next_op != u64::MAX {
                lemma_store_reply_integrity(node, op, response);
            }
        },
        _ => {},
    }
}

proof fn lemma_find_from(entries: Seq<EntryV>, key: Seq<char>, i: int)
    requires
        0 <= i <= entries.len(),
    ensures
        match spec_find(entries, key, i) {
            Some(j) => i <= j < entries.len()
                && entries[j].key == key
                && forall|k: int| i <= k < j
                    ==> #[trigger] entries[k].key != key,
            None => forall|k: int| i <= k < entries.len()
                ==> #[trigger] entries[k].key != key,
        },
    decreases entries.len() - i,
{
    if i < entries.len() && entries[i].key != key {
        lemma_find_from(entries, key, i + 1);
    }
}

proof fn lemma_find_at(store: StoreV, i: int)
    requires
        store_entries_unique(store),
        0 <= i < store.entries.len(),
    ensures
        spec_find(store.entries, store.entries[i].key, 0) == Some(i),
{
    lemma_find_from(store.entries, store.entries[i].key, 0);
    match spec_find(store.entries, store.entries[i].key, 0) {
        Some(j) => {
            if j < i {
                assert(store.entries[j].key != store.entries[i].key);
            } else if j > i {
                assert(store.entries[i].key != store.entries[i].key);
            }
        },
        None => {
            assert(store.entries[i].key != store.entries[i].key);
        },
    }
}

proof fn lemma_find_absent(entries: Seq<EntryV>, key: Seq<char>)
    requires
        forall|i: int| 0 <= i < entries.len()
            ==> #[trigger] entries[i].key != key,
    ensures
        spec_find(entries, key, 0) is None,
{
    lemma_find_from(entries, key, 0);
}

proof fn lemma_insert_integrity(
    store: StoreV,
    entry: EntryV,
    i: int,
)
    requires
        store_entries_ordered(store),
        store_entries_unique(store),
        store_versions_positive(store),
        entry.version > 0,
        0 <= i <= store.entries.len(),
        forall|k: int| 0 <= k < store.entries.len()
            ==> #[trigger] store.entries[k].key != entry.key,
        forall|k: int| 0 <= k < i
            ==> spec_before(#[trigger] store.entries[k].key, entry.key),
    ensures
        ({
            let next = StoreV {
                entries: spec_insert_at(store.entries, entry, i),
                ..store
            };
            &&& store_entries_ordered(next)
            &&& store_entries_unique(next)
            &&& store_versions_positive(next)
            &&& forall|k: int| 0 <= k < store.entries.len() ==> {
                let old = #[trigger] store.entries[k];
                match spec_find(next.entries, old.key, 0) {
                    Some(j) => next.entries[j].version == old.version,
                    None => false,
                }
            }
        }),
    decreases store.entries.len() - i,
{
    let entries = store.entries;
    let next_entries = spec_insert_at(entries, entry, i);
    let next = StoreV { entries: next_entries, ..store };
    if i >= entries.len() {
        assert(next_entries == entries.push(entry));
        assert forall|j: int, k: int| 0 <= j < k < next_entries.len()
            implies spec_before(
                #[trigger] next_entries[j].key,
                #[trigger] next_entries[k].key,
            ) by {
            if k == entries.len() {
                assert(next_entries[j] == entries[j]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next_entries.len()
            implies #[trigger] next_entries[j].key
                != #[trigger] next_entries[k].key by {
            if k == entries.len() {
                assert(next_entries[j] == entries[j]);
            }
        };
        assert forall|k: int| 0 <= k < next_entries.len()
            implies #[trigger] next_entries[k].version > 0 by {};
        assert forall|k: int| 0 <= k < entries.len() implies {
            let old = #[trigger] entries[k];
            match spec_find(next_entries, old.key, 0) {
                Some(j) => next_entries[j].version == old.version,
                None => false,
            }
        } by {
            let bare = StoreV { entries: next_entries, ..store };
            lemma_find_at(bare, k);
            assert(next_entries[k] == entries[k]);
        };
    } else if spec_before(entry.key, entries[i].key) {
        assert(next_entries == entries.take(i).push(entry) + entries.skip(i));
        assert forall|k: int| 0 <= k < next_entries.len()
            implies #[trigger] next_entries[k] == if k < i {
                entries[k]
            } else if k == i {
                entry
            } else {
                entries[k - 1]
            } by {
            if k < i {
                assert(next_entries[k] == entries.take(i).push(entry)[k]);
            } else if k == i {
                assert(next_entries[k] == entries.take(i).push(entry)[k]);
            } else {
                assert(next_entries[k] == entries.skip(i)[k - i - 1]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next_entries.len()
            implies spec_before(
                #[trigger] next_entries[j].key,
                #[trigger] next_entries[k].key,
            ) by {
            if j < i && k == i {
            } else if j == i {
                if k > i + 1 {
                    lemma_before_transitive(
                        entry.key,
                        entries[i].key,
                        entries[k - 1].key,
                    );
                }
            } else if j < i && k > i {
                assert(next_entries[j] == entries[j]);
                assert(next_entries[k] == entries[k - 1]);
            } else if j > i {
                assert(next_entries[j] == entries[j - 1]);
                assert(next_entries[k] == entries[k - 1]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next_entries.len()
            implies #[trigger] next_entries[j].key
                != #[trigger] next_entries[k].key by {
            lemma_before_irreflexive(next_entries[j].key);
        };
        assert forall|k: int| 0 <= k < next_entries.len()
            implies #[trigger] next_entries[k].version > 0 by {};
        assert forall|k: int| 0 <= k < entries.len() implies {
            let old = #[trigger] entries[k];
            match spec_find(next_entries, old.key, 0) {
                Some(j) => next_entries[j].version == old.version,
                None => false,
            }
        } by {
            let bare = StoreV { entries: next_entries, ..store };
            if k < i {
                lemma_find_at(bare, k);
            } else {
                lemma_find_at(bare, k + 1);
            }
        };
    } else {
        lemma_before_total(entry.key, entries[i].key);
        assert(spec_before(entries[i].key, entry.key));
        lemma_insert_integrity(store, entry, i + 1);
    }
}

proof fn lemma_put_integrity(store: StoreV, entry: EntryV)
    requires
        store_entries_ordered(store),
        store_entries_unique(store),
        store_versions_positive(store),
        entry.version > 0,
        match spec_find(store.entries, entry.key, 0) {
            Some(i) => store.entries[i].version <= entry.version,
            None => true,
        },
    ensures
        ({
            let next = StoreV { entries: spec_put(store.entries, entry), ..store };
            &&& store_entries_ordered(next)
            &&& store_entries_unique(next)
            &&& store_versions_positive(next)
            &&& forall|k: int| 0 <= k < store.entries.len() ==> {
                let old = #[trigger] store.entries[k];
                match spec_find(next.entries, old.key, 0) {
                    Some(j) => old.version <= next.entries[j].version,
                    None => false,
                }
            }
        }),
{
    lemma_find_from(store.entries, entry.key, 0);
    match spec_find(store.entries, entry.key, 0) {
        Some(i) => {
            let next_entries = store.entries.update(i, entry);
            let next = StoreV { entries: next_entries, ..store };
            assert forall|k: int| 0 <= k < next_entries.len()
                implies #[trigger] next_entries[k].key == store.entries[k].key by {};
            assert(store_entries_ordered(next));
            assert(store_entries_unique(next));
            assert(store_versions_positive(next));
            assert forall|k: int| 0 <= k < store.entries.len() implies {
                let old = #[trigger] store.entries[k];
                match spec_find(next_entries, old.key, 0) {
                    Some(j) => old.version <= next_entries[j].version,
                    None => false,
                }
            } by {
                lemma_find_at(next, k);
            };
        },
        None => {
            assert forall|k: int| 0 <= k < store.entries.len()
                implies #[trigger] store.entries[k].key != entry.key by {};
            lemma_insert_integrity(store, entry, 0);
        },
    }
}

proof fn lemma_remove_integrity(store: StoreV, i: int)
    requires
        state_properties(Proc::Store(store)),
        0 <= i < store.entries.len(),
    ensures
        ({
            let next = StoreV { entries: spec_remove_at(store.entries, i), ..store };
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    let entries = store.entries;
    let next_entries = spec_remove_at(entries, i);
    let next = StoreV { entries: next_entries, ..store };
    assert forall|k: int| 0 <= k < next_entries.len()
        implies #[trigger] next_entries[k] == if k < i {
            entries[k]
        } else {
            entries[k + 1]
        } by {
        if k < i {
            assert(next_entries[k] == entries.take(i)[k]);
        } else {
            assert(next_entries[k] == entries.skip(i + 1)[k - i]);
        }
    };
    assert(store_entries_ordered(next));
    assert(store_entries_unique(next));
    assert(store_versions_positive(next));
    assert forall|k: int| 0 <= k < entries.len() implies {
        let old = #[trigger] entries[k];
        match spec_find(next_entries, old.key, 0) {
            Some(j) => old.version <= next_entries[j].version,
            None => true,
        }
    } by {
        if k < i {
            assert(next_entries[k] == entries[k]);
            lemma_find_at(next, k);
            assert(spec_find(next_entries, entries[k].key, 0) == Some(k));
        } else if k > i {
            assert(next_entries[k - 1] == entries[k]);
            lemma_find_at(next, k - 1);
            assert(spec_find(next_entries, entries[k].key, 0) == Some(k - 1));
        } else {
            assert forall|j: int| 0 <= j < next_entries.len()
                implies #[trigger] next_entries[j].key != entries[k].key by {
                if j < i {
                    assert(next_entries[j] == entries[j]);
                    assert(entries[j].key != entries[i].key);
                } else {
                    assert(next_entries[j] == entries[j + 1]);
                    assert(entries[i].key != entries[j + 1].key);
                }
            };
            lemma_find_absent(next_entries, entries[k].key);
        }
    };
}

proof fn lemma_store_stutter(store: StoreV)
    requires
        state_properties(Proc::Store(store)),
    ensures
        transition_properties(Proc::Store(store), Proc::Store(store)),
{
    assert forall|i: int| 0 <= i < store.entries.len() implies {
        let old = #[trigger] store.entries[i];
        match spec_find(store.entries, old.key, 0) {
            Some(j) => old.version <= store.entries[j].version,
            None => true,
        }
    } by {
        lemma_find_at(store, i);
    };
}

proof fn lemma_apply_put_none(store: StoreV, key: String, body: Vec<u8>)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::PutIfNoneMatch { key, body };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    lemma_store_stutter(store);
    match spec_find(store.entries, key@, 0) {
        Some(_) => {},
        None => {
            lemma_put_integrity(
                store,
                EntryV { key: key@, body: body@, version: 1 },
            );
        },
    }
}

#[verifier::rlimit(10)]
proof fn lemma_apply_put_match(
    store: StoreV,
    key: String,
    body: Vec<u8>,
    etag: crate::state::Etag,
)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::PutIfMatch { key, body, etag };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    lemma_store_stutter(store);
    let request = StoreReq::PutIfMatch { key, body, etag };
    let next = spec_apply(store, request).0;
    match spec_find(store.entries, key@, 0) {
        Some(i) if crate::state::spec_etag(store.entries[i].body) == etag => {
            assert(spec_bump(store.entries[i].version) >= store.entries[i].version);
            assert(spec_bump(store.entries[i].version) > 0);
            let entry = EntryV {
                key: key@,
                body: body@,
                version: spec_bump(store.entries[i].version),
            };
            lemma_put_integrity(
                store,
                entry,
            );
            assert(next == StoreV { entries: spec_put(store.entries, entry), ..store });
        },
        _ => {
            assert(next == store);
        },
    }
}

#[verifier::rlimit(10)]
proof fn lemma_apply_append(
    store: StoreV,
    key: String,
    offset: u64,
    body: Vec<u8>,
    etag: crate::state::Etag,
)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::AppIfMatch { key, offset, body, etag };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    lemma_store_stutter(store);
    let request = StoreReq::AppIfMatch { key, offset, body, etag };
    let next = spec_apply(store, request).0;
    if store.appendable {
        match spec_find(store.entries, key@, 0) {
            Some(i) if crate::state::spec_etag(store.entries[i].body) == etag
                && store.entries[i].body.len() == offset => {
                assert(spec_bump(store.entries[i].version) >= store.entries[i].version);
                assert(spec_bump(store.entries[i].version) > 0);
                let entry = EntryV {
                    key: key@,
                    body: store.entries[i].body + body@,
                    version: spec_bump(store.entries[i].version),
                };
                lemma_put_integrity(store, entry);
                assert(next == StoreV { entries: spec_put(store.entries, entry), ..store });
            },
            _ => {
                assert(next == store);
            },
        }
    } else {
        assert(next == store);
    }
}

proof fn lemma_apply_put(store: StoreV, key: String, body: Vec<u8>)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::Put { key, body };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    let version = match spec_find(store.entries, key@, 0) {
        Some(i) => spec_bump(store.entries[i].version),
        None => 1,
    };
    assert(version > 0);
    match spec_find(store.entries, key@, 0) {
        Some(i) => assert(version >= store.entries[i].version),
        None => {},
    }
    lemma_put_integrity(store, EntryV { key: key@, body: body@, version });
}

proof fn lemma_apply_delete(store: StoreV, key: String)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::Del { key };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    lemma_store_stutter(store);
    match spec_find(store.entries, key@, 0) {
        Some(i) => {
            lemma_find_from(store.entries, key@, 0);
            lemma_remove_integrity(store, i);
        },
        None => {},
    }
}

proof fn lemma_apply_integrity(store: StoreV, request: StoreReq)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    match request {
        StoreReq::PutIfNoneMatch { key, body } =>
            lemma_apply_put_none(store, key, body),
        StoreReq::PutIfMatch { key, body, etag } =>
            lemma_apply_put_match(store, key, body, etag),
        StoreReq::AppIfMatch { key, offset, body, etag } =>
            lemma_apply_append(store, key, offset, body, etag),
        StoreReq::Put { key, body } => lemma_apply_put(store, key, body),
        StoreReq::Del { key } => lemma_apply_delete(store, key),
        _ => lemma_store_stutter(store),
    }
}

proof fn lemma_store_step_integrity(
    store: StoreV,
    event: ProcessEvent<Pid, Message>,
)
    requires
        state_properties(Proc::Store(store)),
    ensures
        forall|i: int| 0 <= i < spec_store(store, event).len() ==> {
            let next = #[trigger] spec_store(store, event)[i].state;
            &&& state_properties(next)
            &&& transition_properties(Proc::Store(store), next)
        },
{
    match event {
        ProcessEvent::Receive {
            sender,
            message: Message::StoreReq { op, request },
        } => {
            if store.seen.contains((sender, op)) {
                lemma_store_stutter(store);
            } else {
                lemma_apply_integrity(store, request);
                let applied = spec_apply(store, request).0;
                let next = StoreV {
                    seen: store.seen.push((sender, op)),
                    ..applied
                };
                assert(next.seen.no_duplicates()) by {
                    assert forall|i: int, j: int|
                        0 <= i < next.seen.len()
                            && 0 <= j < next.seen.len()
                            && i != j
                        implies #[trigger] next.seen[i]
                            != #[trigger] next.seen[j] by {
                        if i < store.seen.len() && j < store.seen.len() {
                        } else if i < store.seen.len() {
                            assert(next.seen[j] == (sender, op));
                        } else {
                            assert(next.seen[i] == (sender, op));
                        }
                    };
                };
                assert(store_entries_ordered(next));
                assert(store_entries_unique(next));
                assert(store_versions_positive(next));
                assert forall|i: int| 0 <= i < store.entries.len() implies {
                    let old = #[trigger] store.entries[i];
                    match spec_find(next.entries, old.key, 0) {
                        Some(j) => old.version <= next.entries[j].version,
                        None => true,
                    }
                } by {};
                assert forall|seen: (Pid, u64)| store.seen.contains(seen)
                    implies next.seen.contains(seen) by {
                    let i = choose|i: int| 0 <= i < store.seen.len()
                        && #[trigger] store.seen[i] == seen;
                    assert(next.seen[i] == store.seen[i]);
                };
                assert(state_properties(Proc::Store(next)));
                assert(transition_properties(
                    Proc::Store(store),
                    Proc::Store(next),
                ));
            }
        },
        _ => {},
    }
}

proof fn lemma_initial_node(config: Config, id: u64)
    ensures
        state_properties(Proc::Node(crate::rover::spec_initial_node(config, id))),
{
}

proof fn lemma_initial_nodes(config: Config, id: u64)
    requires
        id <= config.nodes,
    ensures
        forall|i: int| 0 <= i < spec_nodes(config, id).len()
            ==> state_properties(#[trigger] spec_nodes(config, id)[i].1),
    decreases config.nodes - id,
{
    if id < config.nodes {
        lemma_initial_node(config, id);
        lemma_initial_nodes(config, (id + 1) as u64);
        let nodes = spec_nodes(config, id);
        let tail = spec_nodes(config, (id + 1) as u64);
        assert(nodes == seq![(
            Pid::Node(id),
            Proc::Node(crate::rover::spec_initial_node(config, id)),
        )] + tail);
        assert forall|i: int| 0 <= i < nodes.len()
            implies state_properties(#[trigger] nodes[i].1) by {
            if i == 0 {
                assert(nodes[0].1
                    == Proc::Node(crate::rover::spec_initial_node(config, id)));
            } else {
                assert(nodes[i] == tail[i - 1]);
            }
        };
    }
}

proof fn lemma_initial_world(config: Config)
    ensures
        forall|i: int| 0 <= i < spec_world(config).len()
            ==> state_properties(#[trigger] spec_world(config)[i].1),
{
    lemma_initial_nodes(config, 0);
}

/// Every configured concrete fleet and every selected process response satisfy
/// the integrity claim.
pub proof fn property_proof(config: Config)
    ensures
        property_claim(config),
{
    lemma_process_layout(config);
    assert forall|doc: DocumentBodyV| document_object_order(doc) by {
        lemma_document_object_order(doc);
    };
    lemma_initial_world(config);
    assert forall|before: Proc, now: Time, event: ProcessEvent<Pid, Message>, i: int|
        #![trigger before.on_event(config, now, event)[i]]
        state_properties(before)
        && 0 <= i
        && i < before.on_event(config, now, event).len()
        implies step_properties(
            before,
            before.on_event(config, now, event)[i],
        ) by {
        match before {
            Proc::Node(node) => {
                lemma_node_step_integrity(config, node, now, event);
            },
            Proc::Store(store) => {
                lemma_store_step_integrity(store, event);
            },
        }
    };
}

} // verus!
