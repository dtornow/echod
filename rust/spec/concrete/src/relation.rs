//! The simulation relation, in full.
//!
//! The abstract service holds one store. Each concrete node holds the
//! documents of the keys it owns, and one flight. The abstract store is
//! what the owners hold: under a key, the document its owner has cached, or
//! the empty document; and while the owner's flight is on that key, the
//! document that flight decides. A node decides from its cache, or from a
//! read of a key it has never written, which the store still holds absent.
//! So the decision is fixed the moment the flight begins, at the time the
//! handler runs with, and the abstract step is taken there. The store's
//! write, and the node's reply when the write lands, change nothing the
//! relation reads: the reply was put on the abstract network when the
//! flight began. [`related`] is that coupling, with the facts about caches,
//! flights, and store traffic that keep it.
//!
//! [`agreement`] is what remains of the handlers: one request, one due
//! step, or one occurrence, on a document and on the abstract store it
//! reads as, do the same thing. `interpret` proves it for the promise
//! handlers. Cargo erases these bodies; a Verus run is what checks them.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::interpret::{doc_rel, finite_store, others_kept, request_agrees};
#[cfg(verus_keep_ghost)]
use crate::model::{
    Fleet, LocalV, Message as CMessage, Model as CModel, NodeV, Pid as CPid, spec_string,
    StoreV as CStore,
};
#[cfg(verus_keep_ghost)]
use crate::node::{
    CachedV, DocV, FlightV, JobV, NoteV, PendingV, spec_cached, spec_empty_doc, spec_encode,
    spec_handle, spec_key, spec_occurrence, spec_origin_key, spec_owns, spec_read, spec_request_notes,
    spec_run_due,
};
#[cfg(verus_keep_ghost)]
use crate::store::{Etag, spec_etag, spec_etag_chars, spec_find, spec_fnv, StoreCall, StoreOutcome};
#[cfg(verus_keep_ghost)]
use echod_abstract::machine::{spec_create_if_absent, spec_handler};
#[cfg(verus_keep_ghost)]
use echod_abstract::model::{Model as AModel, Pid as APid, spec_run_timeout, StateV};
#[cfg(verus_keep_ghost)]
use echod_abstract::protocol::Message as AMessage;
#[cfg(verus_keep_ghost)]
use echod_abstract::view::{InternalV, StoreV as AStore};
#[cfg(verus_keep_ghost)]
use echod_abstract::{Dispatch, Output, ServerConfig};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{is_process, World};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::{Envelope, RoverModel};
#[cfg(verus_keep_ghost)]
use echod_rover::Sched;
#[cfg(verus_keep_ghost)]
use echod_types::{origin, Request, Response};

verus! {

// ---------------------------------------------------------------------------
// Shape
// ---------------------------------------------------------------------------

/// The node in slot `i`.
pub open spec fn node_at(world: World<CModel>, i: int) -> NodeV {
    world.process[i].1->Node_0
}

/// The store, in the slot after the nodes.
pub open spec fn store_at(fleet: Fleet, world: World<CModel>) -> CStore {
    world.process[fleet.nodes as int].1->Store_0
}

/// Slots `0 .. nodes` are the nodes, each at its own address; the last slot
/// is the store. The world `initial` builds has this shape and a step keeps it.
pub open spec fn shaped(fleet: Fleet, world: World<CModel>) -> bool {
    &&& world.process.len() == fleet.nodes + 1
    &&& forall|i: int|
        0 <= i < fleet.nodes ==> {
            &&& #[trigger] world.process[i].0 == CPid::Node(i as u64)
            &&& world.process[i].1 is Node
            &&& node_at(world, i).address == i
            &&& node_at(world, i).nodes == fleet.nodes
            &&& node_at(world, i).retry_timeout == fleet.retry_timeout
        }
    &&& world.process[fleet.nodes as int].0 == CPid::Store
    &&& world.process[fleet.nodes as int].1 is Store
}

/// The abstract world has the one service slot.
pub open spec fn single(world: World<AModel>) -> bool {
    world.process.len() == 1 && world.process[0].0 == APid::Service
}

pub open spec fn astate(world: World<AModel>) -> StateV {
    world.process[0].1
}

pub proof fn lemma_single_present(world: World<AModel>)
    requires
        single(world),
    ensures
        is_process(AModel, world, APid::Service),
{
    assert(AModel.spec_outside() == APid::Outside);
    assert(world.process[0].0 == APid::Service);
}

// ---------------------------------------------------------------------------
// What a node holds, and what its flight decides
// ---------------------------------------------------------------------------

/// The document a node decides from: its cache, or the empty document.
pub open spec fn loaded(node: NodeV, key: Seq<char>) -> DocV {
    match spec_cached(node, key) {
        Some(cached) => spec_read(key, cached.body),
        None => spec_empty_doc(key),
    }
}

/// What `spec_decide` computes from a flight and the document it loaded,
/// at the node's retry timeout: the next document, the reply, the
/// occurrences born, the dispatches.
/// Opaque: it holds the whole handler semantics, read where a proof needs it.
#[verifier::opaque]
pub open spec fn decision(flight: FlightV, doc: DocV, retry_timeout: u64) -> (
    DocV,
    Option<Response>,
    Seq<PendingV>,
    Seq<NoteV>,
) {
    match flight.job {
        JobV::External(request) => {
            let (next, response) = spec_handle(doc, request, flight.now, retry_timeout);
            (next, Some(response), Seq::empty(), spec_request_notes(doc, request, flight.now, retry_timeout))
        },
        JobV::Due => spec_run_due(doc, flight.now, retry_timeout),
        JobV::Occurrence(pending) => (
            spec_occurrence(doc, pending, flight.now),
            None,
            Seq::empty(),
            Seq::empty(),
        ),
    }
}

/// The document a node stands for under `key`: what its flight on that key
/// decides, else what it holds.
pub open spec fn intended(node: NodeV, key: Seq<char>) -> DocV {
    match node.flight {
        Some(flight) if flight.key == key => decision(flight, loaded(node, key), node.retry_timeout).0,
        _ => loaded(node, key),
    }
}

/// The slot of the node that owns `key`.
pub open spec fn owner(fleet: Fleet, key: Seq<char>) -> int {
    (spec_fnv(key) % fleet.nodes) as int
}

/// The document the concrete world stands for under `key`.
pub open spec fn effective(fleet: Fleet, world: World<CModel>, key: Seq<char>) -> DocV {
    if fleet.nodes == 0 {
        spec_empty_doc(key)
    } else {
        intended(node_at(world, owner(fleet, key)), key)
    }
}

/// Lean's `StoreRep`: under every key, the concrete world reads as the
/// abstract store.
pub open spec fn store_interpreted(fleet: Fleet, world: World<CModel>, s: AStore) -> bool {
    forall|key: Seq<char>| #[trigger] doc_rel(key, effective(fleet, world, key), s)
}

// ---------------------------------------------------------------------------
// Occurrences
// ---------------------------------------------------------------------------

/// The occurrences a node's flight will append when its write lands.
pub open spec fn born_of(node: NodeV) -> Seq<PendingV> {
    match node.flight {
        Some(flight) => decision(flight, loaded(node, flight.key), node.retry_timeout).2,
        None => Seq::empty(),
    }
}

/// The occurrences a node owes: queued, or born in its flight.
pub open spec fn occurrences(node: NodeV) -> Seq<PendingV> {
    node.pending + born_of(node)
}

/// A concrete occurrence, as the abstract queue holds it.
pub open spec fn as_item(p: PendingV) -> Sched<InternalV> {
    Sched::Timer(
        p.at,
        InternalV::Occurrence {
            promise: p.promise,
            at: p.at,
            timeout: p.timeout,
            param: p.param,
            tags: p.tags,
        },
    )
}

pub open spec fn items(occurrences: Seq<PendingV>) -> Seq<Sched<InternalV>> {
    occurrences.map_values(|p: PendingV| as_item(p))
}

/// How many times `item` is owed by the nodes from slot `i` on.
pub open spec fn owed(fleet: Fleet, world: World<CModel>, item: Sched<InternalV>, i: int) -> nat
    decreases fleet.nodes - i,
{
    if i < 0 || i >= fleet.nodes {
        0
    } else {
        items(occurrences(node_at(world, i))).to_multiset().count(item) + owed(
            fleet,
            world,
            item,
            i + 1,
        )
    }
}

/// Every occurrence a node owes is queued at the service. The service may
/// hold more: an occurrence a node dropped stays queued there.
pub open spec fn pending_covered(fleet: Fleet, world: World<CModel>, state: StateV) -> bool {
    forall|item: Sched<InternalV>|
        #[trigger] owed(fleet, world, item, 0) <= state.pending.to_multiset().count(item)
}

// ---------------------------------------------------------------------------
// Flights
// ---------------------------------------------------------------------------

pub open spec fn reply_output(client: Seq<char>, id: u64, response: Response) -> Output {
    Output::Response { client: spec_string(client), id, response }
}

pub open spec fn note_output(note: NoteV) -> Output {
    match note {
        NoteV::Execute { id, version } => Output::Dispatch(Dispatch::Execute {
            id: spec_string(id),
            version,
        }),
        NoteV::Unblock { address, promise } => Output::Dispatch(Dispatch::Unblock {
            address: spec_string(address),
            promise,
        }),
    }
}

/// `output` was sent by the service to the outside.
pub open spec fn service_output(network: Seq<Envelope<APid, AMessage>>, output: Output) -> bool {
    exists|j: int|
        #![trigger network[j]]
        0 <= j < network.len() && network[j] == Envelope {
            sender: APid::Service,
            recipient: APid::Outside,
            message: AMessage::Output(output),
        }
}

/// The reply a flight will send, if it answers a caller.
pub open spec fn flight_reply(flight: FlightV, reply: Option<Response>) -> Option<
    (Seq<char>, u64, Response),
> {
    match (flight.caller, reply) {
        (Some((client, id)), Some(response)) => Some((client, id, response)),
        _ => None,
    }
}

/// What a node's flight will send is already on the abstract network.
pub open spec fn flight_outputs_covered(
    node: NodeV,
    network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    match node.flight {
        None => true,
        Some(flight) => {
            let (_, reply, _, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
            &&& match flight_reply(flight, reply) {
                Some((client, id, response)) => service_output(
                    network,
                    reply_output(client, id, response),
                ),
                None => true,
            }
            &&& forall|k: int|
                0 <= k < notes.len() ==> service_output(network, note_output(#[trigger] notes[k]))
        },
    }
}

/// The key a flight is on is the key its job names.
pub open spec fn job_keyed(flight: FlightV) -> bool {
    match flight.job {
        JobV::External(request) => flight.caller is Some && spec_key(request) == Some(flight.key),
        JobV::Due => flight.caller is None,
        JobV::Occurrence(pending) => flight.caller is None && flight.key == spec_origin_key(
            origin(pending.promise),
        ),
    }
}

pub open spec fn cached_etag(node: NodeV, key: Seq<char>) -> Option<Seq<char>> {
    match spec_cached(node, key) {
        Some(cached) => cached.etag,
        None => None,
    }
}

/// A flight is on a key the node owns, carries an op the node has issued,
/// and, once writing, carries what `spec_decide` computed from what the
/// node holds. A reading flight is on a key the node does not hold.
pub open spec fn flight_ok(node: NodeV) -> bool {
    match node.flight {
        None => true,
        Some(flight) => {
            let (next, reply, born, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
            &&& spec_owns(node, flight.key)
            &&& flight.op < node.next_op
            &&& job_keyed(flight)
            &&& if !flight.writing {
                &&& flight.etag is None
                &&& spec_cached(node, flight.key) is None
            } else {
                &&& flight.etag == cached_etag(node, flight.key)
                &&& flight.decided == Some(spec_encode(next))
                &&& flight.born == born
                &&& flight.notify == notes
                &&& flight.reply == flight_reply(flight, reply)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Caches and the store
// ---------------------------------------------------------------------------

/// The bytes the store holds under `key`.
pub open spec fn physical(store: CStore, key: Seq<char>) -> Option<Seq<u8>> {
    match spec_find(store.entries, key, 0) {
        Some(i) => Some(store.entries[i].body),
        None => None,
    }
}

/// Node `i`'s write on `key` has landed and the node has not yet heard.
pub open spec fn applied_write(i: int, node: NodeV, store: CStore, key: Seq<char>) -> bool {
    match node.flight {
        Some(flight) => {
            &&& flight.key == key
            &&& flight.writing
            &&& store.seen.contains((CPid::Node(i as u64), flight.op))
        },
        None => false,
    }
}

/// A cached document is encoded, and the store holds the same bytes under
/// the etag the cache quotes. A cache entry without an etag is a key the
/// store holds absent.
pub open spec fn cache_entry_ok(key: Seq<char>, cached: CachedV, store: CStore) -> bool {
    &&& cached.body == spec_encode(spec_read(key, cached.body))
    &&& match cached.etag {
        Some(etag) => physical(store, key) == Some(cached.body) && etag == spec_etag_chars(
            cached.body,
        ),
        None => physical(store, key) is None,
    }
}

/// On every key node `i` owns, the store holds the write the node is
/// waiting to hear about, else agrees with the node's cache.
pub open spec fn cache_ok(i: int, node: NodeV, store: CStore) -> bool {
    forall|key: Seq<char>|
        spec_owns(node, key) ==> if applied_write(i, node, store, key) {
            physical(store, key) == node.flight.unwrap().decided
        } else {
            match #[trigger] spec_cached(node, key) {
                Some(cached) => cache_entry_ok(key, cached, store),
                None => physical(store, key) is None,
            }
        }
}

/// A node caches only keys it owns, each once.
pub open spec fn cache_owned(node: NodeV) -> bool {
    &&& forall|k: int|
        0 <= k < node.documents.len() ==> spec_owns(
            node,
            #[trigger] node.documents[k].key,
        )
    &&& forall|j: int, k: int|
        0 <= j < k < node.documents.len() ==> #[trigger] node.documents[j].key
            != #[trigger] node.documents[k].key
}

/// The store's entries name each key once.
pub open spec fn entries_distinct(store: CStore) -> bool {
    forall|j: int, k: int|
        0 <= j < k < store.entries.len() ==> #[trigger] store.entries[j].key
            != #[trigger] store.entries[k].key
}

pub open spec fn node_ok(i: int, node: NodeV, store: CStore) -> bool {
    &&& flight_ok(node)
    &&& cache_owned(node)
    &&& cache_ok(i, node, store)
}

// ---------------------------------------------------------------------------
// Store traffic
// ---------------------------------------------------------------------------

pub open spec fn flight_op(node: NodeV) -> Option<u64> {
    match node.flight {
        Some(flight) => Some(flight.op),
        None => None,
    }
}

/// The call a flight sent: a read of its key, or the conditional write of
/// what it decided.
pub open spec fn request_of(flight: FlightV) -> StoreCall {
    if !flight.writing {
        StoreCall::Get { key: spec_string(flight.key) }
    } else {
        match flight.etag {
            Some(chars) => StoreCall::PutIfMatch {
                key: spec_string(flight.key),
                body: crate::model::spec_bytes(flight.decided.unwrap()),
                etag: Etag(spec_string(chars)),
            },
            None => StoreCall::PutIfNoneMatch {
                key: spec_string(flight.key),
                body: crate::model::spec_bytes(flight.decided.unwrap()),
            },
        }
    }
}

/// The reply the store gives a flight's call, once the caches agree with
/// the store.
pub open spec fn outcome_of(flight: FlightV) -> StoreOutcome {
    if flight.writing {
        StoreOutcome::Written(spec_etag(flight.decided.unwrap()))
    } else {
        StoreOutcome::Got(None)
    }
}

/// Every store request on the network is from a node, under an op that
/// node has issued. One the store has not answered is the node's open
/// flight's call. One under the open flight's op is that flight's call.
pub open spec fn requests_ok(fleet: Fleet, world: World<CModel>) -> bool {
    forall|k: int|
        0 <= k < world.network.len() ==> match (#[trigger] world.network[k]).message {
            CMessage::StoreReq { op, call } => {
                let env = world.network[k];
                &&& env.recipient == CPid::Store
                &&& env.sender is Node
                &&& {
                    let i = env.sender->Node_0 as int;
                    let node = node_at(world, i);
                    &&& 0 <= i < fleet.nodes
                    &&& op < node.next_op
                    &&& (flight_op(node) == Some(op) ==> call == request_of(node.flight.unwrap()))
                    &&& (!store_at(fleet, world).seen.contains((env.sender, op)) ==> flight_op(node)
                        == Some(op))
                }
            },
            _ => true,
        }
}

/// Every store reply on the network answers a node under an op the store
/// has executed. One under the node's open flight's op is the reply
/// [`outcome_of`] says.
pub open spec fn replies_ok(fleet: Fleet, world: World<CModel>) -> bool {
    forall|k: int|
        0 <= k < world.network.len() ==> match (#[trigger] world.network[k]).message {
            CMessage::StoreReply { op, outcome } => {
                let env = world.network[k];
                &&& env.sender == CPid::Store
                &&& env.recipient is Node
                &&& {
                    let i = env.recipient->Node_0 as int;
                    let node = node_at(world, i);
                    &&& 0 <= i < fleet.nodes
                    &&& store_at(fleet, world).seen.contains((env.recipient, op))
                    &&& (flight_op(node) == Some(op) ==> outcome == outcome_of(
                        node.flight.unwrap(),
                    ))
                }
            },
            _ => true,
        }
}

/// A request envelope under `(sender, op)` is on the network.
pub open spec fn requested(world: World<CModel>, sender: CPid, op: u64) -> bool {
    exists|k: int|
        #![trigger world.network[k]]
        0 <= k < world.network.len() && world.network[k].sender == sender
            && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
            && world.network[k].message->StoreReq_op == op
}

/// Every op the store has executed was requested.
pub open spec fn seen_ok(fleet: Fleet, world: World<CModel>) -> bool {
    forall|pair: (CPid, u64)|
        #[trigger] store_at(fleet, world).seen.contains(pair) ==> requested(world, pair.0, pair.1)
}

/// The facts of the concrete world alone.
pub open spec fn inv(fleet: Fleet, world: World<CModel>) -> bool {
    &&& shaped(fleet, world)
    &&& entries_distinct(store_at(fleet, world))
    &&& forall|i: int|
        0 <= i < fleet.nodes ==> #[trigger] node_ok(i, node_at(world, i), store_at(fleet, world))
    &&& requests_ok(fleet, world)
    &&& replies_ok(fleet, world)
    &&& seen_ok(fleet, world)
}

// ---------------------------------------------------------------------------
// The boundary
// ---------------------------------------------------------------------------

/// `call` was injected at the service.
pub open spec fn service_request(network: Seq<Envelope<APid, AMessage>>, call: echod_abstract::Call) -> bool {
    exists|j: int|
        #![trigger network[j]]
        0 <= j < network.len() && network[j] == Envelope {
            sender: APid::Outside,
            recipient: APid::Service,
            message: AMessage::Request(call),
        }
}

/// A client request on the concrete network has the same call on the service.
pub open spec fn carried_request(
    env: Envelope<CPid, CMessage>,
    network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    match env.message {
        CMessage::Request(call) => env.sender != CPid::Outside || service_request(network, call),
        _ => true,
    }
}

/// An output addressed to the concrete outside was sent by the service.
pub open spec fn carried_output(
    env: Envelope<CPid, CMessage>,
    network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    match env.message {
        CMessage::Output(output) => {
            env.recipient != CPid::Outside || service_output(network, output)
        },
        _ => true,
    }
}

pub open spec fn requests_covered(
    concrete: Seq<Envelope<CPid, CMessage>>,
    abstract_network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    forall|i: int|
        #![trigger concrete[i]]
        0 <= i < concrete.len() ==> carried_request(concrete[i], abstract_network)
}

pub open spec fn outputs_covered(
    concrete: Seq<Envelope<CPid, CMessage>>,
    abstract_network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    forall|i: int|
        #![trigger concrete[i]]
        0 <= i < concrete.len() ==> carried_output(concrete[i], abstract_network)
}

/// Clock, requests, and outputs: what an injected call and an observed
/// output need.
pub open spec fn coupled(concrete: World<CModel>, abstract_world: World<AModel>) -> bool {
    &&& abstract_world.now <= concrete.now
    &&& requests_covered(concrete.network, abstract_world.network)
    &&& outputs_covered(concrete.network, abstract_world.network)
}

/// The relation.
pub open spec fn related(fleet: Fleet, concrete: World<CModel>, abstract_world: World<AModel>) -> bool {
    &&& coupled(concrete, abstract_world)
    &&& single(abstract_world)
    &&& inv(fleet, concrete)
    &&& finite_store(astate(abstract_world).store)
    &&& store_interpreted(fleet, concrete, astate(abstract_world).store)
    &&& pending_covered(fleet, concrete, astate(abstract_world))
    &&& forall|i: int|
        0 <= i < fleet.nodes ==> flight_outputs_covered(
            #[trigger] node_at(concrete, i),
            abstract_world.network,
        )
}

// ---------------------------------------------------------------------------
// Agreement: the handlers, on a document and on the abstract store
// ---------------------------------------------------------------------------

/// Every request on the document it names, by `interpret::request_agrees`.
pub open spec fn requests_agree(config: ServerConfig) -> bool {
    forall|request: Request, key: Seq<char>, doc: DocV, s: AStore, now: u64|
        spec_key(request) == Some(key) && doc_rel(key, doc, s) && finite_store(s) ==> #[trigger] request_agrees(
            config,
            request,
            key,
            doc,
            s,
            now,
        )
}

pub open spec fn note_sends(notes: Seq<NoteV>) -> Seq<(APid, AMessage)> {
    notes.map_values(|note: NoteV| (APid::Outside, AMessage::Output(note_output(note))))
}

/// The due step of one document: nothing is due, or one abstract timeout
/// result does the same, sends the same dispatches, queues the same
/// occurrences, and keeps the store finite.
pub open spec fn due_agrees(
    config: ServerConfig,
    key: Seq<char>,
    doc: DocV,
    state: StateV,
    now: u64,
) -> bool {
    let (next, _, born, notes) = spec_run_due(doc, now, config.retry_timeout);
    ||| next == doc && born.len() == 0 && notes.len() == 0
    ||| exists|j: int|
        #![trigger spec_run_timeout(config, state, now)[j]]
        {
            let results = spec_run_timeout(config, state, now);
            &&& 0 <= j < results.len()
            &&& results[j].send == note_sends(notes)
            &&& results[j].state.pending == state.pending + items(born)
            &&& doc_rel(key, next, results[j].state.store)
            &&& others_kept(key, state.store, results[j].state.store)
            &&& finite_store(results[j].state.store)
        }
}

pub open spec fn dues_agree(config: ServerConfig) -> bool {
    forall|key: Seq<char>, doc: DocV, state: StateV, now: u64|
        doc_rel(key, doc, state.store) && finite_store(state.store) ==> #[trigger] due_agrees(
            config,
            key,
            doc,
            state,
            now,
        )
}

/// One occurrence on its origin document: nothing happens, or the abstract
/// occurrence step does the same.
pub open spec fn occurrence_agrees(pending: PendingV, doc: DocV, s: AStore, now: u64) -> bool {
    let key = spec_origin_key(origin(pending.promise));
    let next = spec_occurrence(doc, pending, now);
    ||| next == doc
    ||| {
        let out = spec_create_if_absent(
            s,
            pending.promise,
            pending.at,
            pending.timeout,
            pending.param,
            pending.tags,
            now,
        );
        &&& !out.not_due
        &&& out.work.len() == 0
        &&& out.send.len() == 0
        &&& doc_rel(key, next, out.next)
        &&& others_kept(key, s, out.next)
        &&& finite_store(out.next)
    }
}

pub open spec fn occurrences_agree() -> bool {
    forall|pending: PendingV, doc: DocV, s: AStore, now: u64|
        doc_rel(spec_origin_key(origin(pending.promise)), doc, s) && finite_store(s)
            ==> #[trigger] occurrence_agrees(pending, doc, s, now)
}

/// Lean's `refinement_handlers`, as one statement.
pub open spec fn agreement(config: ServerConfig) -> bool {
    requests_agree(config) && dues_agree(config) && occurrences_agree()
}

/// The abstract server's configuration a fleet implements: the service it
/// refines retries as the nodes do.
pub open spec fn abstract_config(concrete_config: Fleet) -> ServerConfig {
    ServerConfig { retry_timeout: concrete_config.retry_timeout }
}

} // verus!
