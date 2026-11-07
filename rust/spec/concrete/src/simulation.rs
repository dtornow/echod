//! Forward simulation from the concrete Rover model to the abstract one.
//!
//! The relation is `relation::related`. An injected `Request` is one abstract
//! input of that call; `Stop`, and an outside step whose message is not an
//! output, are empty abstract executions; an observed output is one abstract
//! outside step of that output. A store step is an empty abstract execution.
//! A node step that begins a flight is one abstract step, taken at the time
//! the flight's handler runs with: a served request, or one timeout result.
//! A node step that answers a call without a flight is one abstract shed, or
//! one served empty heartbeat. Every other node step is an empty abstract
//! execution: a read, a write, and the reply when the write lands change
//! nothing the relation reads.
//!
//! [`lemma_simulation`] is the simulation under [`agreement`]: the
//! handlers, the due step, and the occurrence do the same on a document and
//! on the abstract store it reads as. `handlers` and `timers` prove that
//! agreement at the configuration the node implements, and
//! [`lemma_refines`] is trace inclusion there, with nothing assumed. Cargo
//! erases these bodies; a Verus run is what checks them.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::interpret::{doc_rel, finite_store, lemma_others_same, others_kept, request_agrees};
#[cfg(verus_keep_ghost)]
use crate::model::{
    spec_bytes, spec_get, spec_initial_node as initial_node, spec_node as spec_node_step,
    spec_nodes, spec_notes, spec_notify, spec_one, spec_reply, spec_step, spec_store, spec_string,
    spec_world, EntryV, Fleet, LocalV, Message as CMessage, Model as CModel, NodeV, Pid as CPid,
    StoreV as CStore,
};
#[cfg(verus_keep_ghost)]
use crate::node::{
    axiom_decode_encode_body, spec_begin, spec_body_is_empty, spec_cached, spec_cached_from,
    spec_commit, spec_decide, spec_earliest_from, spec_earliest_key, spec_empty_body,
    spec_encode_body, spec_flight, spec_forget, spec_handle, spec_keep, spec_key, spec_occurrence,
    spec_owns, spec_preflight_error, spec_pure, spec_read, spec_remember, spec_request, spec_request_commits,
    spec_request_transition, spec_run_due, spec_store_reply, spec_sweep, spec_timeout,
    spec_unavailable, CachedV, DocumentBodyV, FlightV, JobV, NoteV, PendingV, REQUEST_STEPS,
};
#[cfg(verus_keep_ghost)]
use crate::relation::*;
#[cfg(verus_keep_ghost)]
use crate::store::{
    spec_apply, spec_etag, spec_etag_chars, spec_find, spec_put, Etag, StoreCall, StoreOutcome,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::machine::{spec_body, spec_create_if_absent, spec_handler, spec_process_work};
#[cfg(verus_keep_ghost)]
use echod_abstract::model::Pid as APid;
#[cfg(verus_keep_ghost)]
use echod_abstract::model::{
    empty_store, lemma_empty_heartbeat_is_first, lemma_shed_is_last, remove_at, spec_idle,
    spec_internal_result, spec_queue, spec_ready, spec_request_outcome, spec_run, spec_run_timeout,
    spec_send, spec_service, spec_shed, StateV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract::protocol::Message as AMessage;
#[cfg(verus_keep_ghost)]
use echod_abstract::trusted::{axiom_string_ext, axiom_string_realised};
#[cfg(verus_keep_ghost)]
use echod_abstract::view::{InOutV, InternalV, OutV, StoreV as AStore};
#[cfg(verus_keep_ghost)]
use echod_abstract::{BoundaryEvent, Call, Model as AModel, Output, ServerConfig};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::refinement::{
    concrete_refines_abstract, end, lemma_end_add, lemma_legal_add, lemma_project_add, matches,
    project, refines, simulation,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{
    before, envelopes, event_valid, initial, inject, is_process, land, legal, observe_outside,
    step, Execution, Label, StepResultV, World, WorldV,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::{Envelope, ProcessEvent, RoverModel};
#[cfg(verus_keep_ghost)]
use echod_rover::{Sched, Time};
#[cfg(verus_keep_ghost)]
use echod_types::{origin, Response};
#[cfg(verus_keep_ghost)]
use vstd::multiset::Multiset;

verus! {

broadcast use
    vstd::seq::group_seq_lemmas,
    vstd::seq_lib::group_to_multiset_ensures,
    vstd::multiset::group_multiset_axioms;

/// The concrete Rover model: the nodes and the store.
pub open spec fn concrete_model() -> CModel {
    CModel
}

/// The abstract Rover model: the one service.
pub open spec fn abstract_model() -> AModel {
    AModel
}

/// `related`, packaged as the function the generic theorem takes.
pub open spec fn link(fleet: Fleet) -> spec_fn(World<CModel>, World<AModel>) -> bool {
    |concrete: World<CModel>, abstract_world: World<AModel>| related(fleet, concrete, abstract_world)
}

pub proof fn lemma_link(fleet: Fleet, concrete: World<CModel>, abstract_world: World<AModel>)
    ensures
        link(fleet)(concrete, abstract_world) == related(fleet, concrete, abstract_world),
{
    assert(link(fleet)(concrete, abstract_world) == related(fleet, concrete, abstract_world));
}

/// `later` still contains every envelope of `earlier`, in front.
pub open spec fn extends<P, M>(later: Seq<Envelope<P, M>>, earlier: Seq<Envelope<P, M>>) -> bool {
    earlier.len() <= later.len() && forall|j: int|
        #![trigger later[j]]
        0 <= j < earlier.len() ==> later[j] == earlier[j]
}

/// The document a node holds under `key`: its cache, or the empty document.
/// `relation::loaded` is this.
pub open spec fn held(node: NodeV, key: Seq<char>) -> DocumentBodyV {
    match spec_cached(node, key) {
        Some(cached) => spec_read(key, cached.body),
        None => spec_empty_body(key),
    }
}

/// Two nodes with the same work: documents, flight, pending list, and op
/// counter. They differ at most in the process shell, `logic`, `wake`,
/// `next_request`, which the relation does not read.
pub open spec fn same_work(a: NodeV, b: NodeV) -> bool {
    a == (NodeV { logic: a.logic, wake: a.wake, next_request: a.next_request, ..b })
}

/// The flight a begin decides with, before it has an op. `decision` reads
/// only the job and the time, so every flight of this begin decides alike.
pub open spec fn probe(key: Seq<char>, now: Time, caller: Option<(Seq<char>, u64)>, job: JobV) -> FlightV {
    spec_flight(0, key, None, now, caller, job)
}

pub open spec fn reply_send(reply: Option<(Seq<char>, u64, Response)>) -> Seq<(CPid, CMessage)> {
    match reply {
        Some((client, id, response)) => seq![spec_reply(client, id, response)],
        None => Seq::empty(),
    }
}

/// The writing flight `spec_decide` opens from `flight` on `doc`.
pub open spec fn written(node: NodeV, flight: FlightV, doc: DocumentBodyV) -> FlightV {
    let (next, reply, born, notes) = decision(flight, doc, node.retry_timeout);
    FlightV {
        op: node.next_op,
        writing: true,
        born,
        reply: flight_reply(flight, reply),
        notify: notes,
        decided: Some(spec_encode_body(next)),
        ..flight
    }
}

pub open spec fn node_result(node: NodeV, send: Seq<(CPid, CMessage)>) -> StepResultV<LocalV, CPid, CMessage> {
    StepResultV { state: LocalV::Node(node), send }
}

pub open spec fn store_result(store: CStore, send: Seq<(CPid, CMessage)>) -> StepResultV<LocalV, CPid, CMessage> {
    StepResultV { state: LocalV::Store(store), send }
}

pub open spec fn node_pid(i: int) -> CPid {
    CPid::Node(i as u64)
}

pub open spec fn no_store_traffic(env: Envelope<CPid, CMessage>) -> bool {
    !(env.message is StoreReq) && !(env.message is StoreReply)
}

pub open spec fn process_label(label: Label<CPid, CMessage>) -> bool {
    match label {
        Label::Process { .. } => true,
        _ => false,
    }
}

pub open spec fn sent(sender: CPid, entry: (CPid, CMessage)) -> Envelope<CPid, CMessage> {
    Envelope { sender, recipient: entry.0, message: entry.1 }
}

/// `call` is still a client request on `network`. The network only grows.
pub open spec fn request_carried(network: Seq<Envelope<CPid, CMessage>>, call: Call) -> bool {
    exists|i: int|
        #![trigger network[i]]
        0 <= i < network.len() && network[i].sender == CPid::Outside && network[i].message
            == CMessage::Request(call)
}

pub open spec fn empty_heartbeat(call: Call) -> bool {
    match call.request {
        echod_types::Request::TaskHeartbeat(q) => q.tasks@.len() == 0,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Network arithmetic
// ---------------------------------------------------------------------------

pub proof fn lemma_inject_keeps_process<P, S, M>(
    world: WorldV<P, S, M>,
    outside: P,
    recipient: P,
    at: Time,
    message: M,
)
    ensures
        inject(world, outside, recipient, at, message).process == world.process,
{
    let after = inject(world, outside, recipient, at, message);
    assert(after.process == world.process);
}

pub proof fn lemma_observe_keeps_world<P, S, M>(world: WorldV<P, S, M>, at: Time)
    ensures
        observe_outside(world, at).process == world.process,
        observe_outside(world, at).network == world.network,
        observe_outside(world, at).now == at,
{
    let after = observe_outside(world, at);
    assert(after.process == world.process);
    assert(after.network == world.network);
    assert(after.now == at);
}

pub proof fn lemma_push_eq_add<A>(s: Seq<A>, x: A)
    ensures
        s.push(x) == s.add(Seq::<A>::empty().push(x)),
{
    let suffix = Seq::<A>::empty().push(x);
    assert(suffix.len() == 1);
    assert forall|i: int| 0 <= i < s.push(x).len() implies s.push(x)[i] == s.add(suffix)[i] by {
        if i < s.len() {
        } else {
            assert(i == s.len());
            assert(suffix[0] == x);
            assert(s.add(suffix)[i] == x);
        }
    };
    assert(s.push(x) =~= s.add(suffix));
}

pub proof fn lemma_extends_refl<P, M>(network: Seq<Envelope<P, M>>)
    ensures
        extends(network, network),
{
}

pub proof fn lemma_extends_push<P, M>(earlier: Seq<Envelope<P, M>>, added: Envelope<P, M>)
    ensures
        extends(earlier.push(added), earlier),
{
}

pub proof fn lemma_extends_add<P, M>(earlier: Seq<Envelope<P, M>>, suffix: Seq<Envelope<P, M>>)
    ensures
        extends(earlier + suffix, earlier),
{
}

pub proof fn lemma_service_output_monotone(
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
    output: Output,
)
    requires
        service_output(earlier, output),
        extends(later, earlier),
    ensures
        service_output(later, output),
{
    let j = choose|j: int|
        #![trigger earlier[j]]
        0 <= j < earlier.len() && earlier[j] == Envelope {
            sender: APid::Service,
            recipient: APid::Outside,
            message: AMessage::Output(output),
        };
    assert(later[j] == earlier[j]);
}

pub proof fn lemma_request_monotone(
    env: Envelope<CPid, CMessage>,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        carried_request(env, earlier),
        extends(later, earlier),
    ensures
        carried_request(env, later),
{
    match env.message {
        CMessage::Request(call) => {
            if env.sender == CPid::Outside {
                let j = choose|j: int|
                    #![trigger earlier[j]]
                    0 <= j < earlier.len() && earlier[j] == Envelope {
                        sender: APid::Outside,
                        recipient: APid::Service,
                        message: AMessage::Request(call),
                    };
                assert(later[j] == earlier[j]);
                assert(service_request(later, call));
            }
        },
        _ => {},
    }
}

pub proof fn lemma_service_request_monotone(
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
    call: Call,
)
    requires
        service_request(earlier, call),
        extends(later, earlier),
    ensures
        service_request(later, call),
{
    let j = choose|j: int|
        #![trigger earlier[j]]
        0 <= j < earlier.len() && earlier[j] == Envelope {
            sender: APid::Outside,
            recipient: APid::Service,
            message: AMessage::Request(call),
        };
    assert(later[j] == earlier[j]);
}

pub proof fn lemma_output_monotone(
    env: Envelope<CPid, CMessage>,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        carried_output(env, earlier),
        extends(later, earlier),
    ensures
        carried_output(env, later),
{
    match env.message {
        CMessage::Output(output) => {
            if env.recipient == CPid::Outside {
                lemma_service_output_monotone(earlier, later, output);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_append_keeps_coverage(
    before: Seq<Envelope<CPid, CMessage>>,
    suffix: Seq<Envelope<CPid, CMessage>>,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        requests_covered(before, earlier),
        outputs_covered(before, earlier),
        extends(later, earlier),
        forall|k: int|
            #![trigger suffix[k]]
            0 <= k < suffix.len() ==> carried_request(suffix[k], later) && carried_output(
                suffix[k],
                later,
            ),
    ensures
        requests_covered(before.add(suffix), later),
        outputs_covered(before.add(suffix), later),
{
    let combined = before.add(suffix);
    assert forall|i: int| 0 <= i < combined.len() implies carried_request(
        #[trigger] combined[i],
        later,
    ) && carried_output(combined[i], later) by {
        if i < before.len() {
            assert(combined[i] == before[i]);
            lemma_request_monotone(before[i], earlier, later);
            lemma_output_monotone(before[i], earlier, later);
        } else {
            let k = i - before.len();
            assert(combined[i] == suffix[k]);
        }
    };
}

pub proof fn lemma_push_keeps_coverage(
    before: Seq<Envelope<CPid, CMessage>>,
    added: Envelope<CPid, CMessage>,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        requests_covered(before, earlier),
        outputs_covered(before, earlier),
        extends(later, earlier),
        carried_request(added, later),
        carried_output(added, later),
    ensures
        requests_covered(before.push(added), later),
        outputs_covered(before.push(added), later),
{
    let suffix = Seq::<Envelope<CPid, CMessage>>::empty().push(added);
    lemma_push_eq_add(before, added);
    assert forall|k: int| 0 <= k < suffix.len() implies carried_request(
        #[trigger] suffix[k],
        later,
    ) && carried_output(suffix[k], later) by {
        assert(suffix[0] == added);
    };
    lemma_append_keeps_coverage(before, suffix, earlier, later);
}

pub proof fn lemma_pushed_request(network: Seq<Envelope<APid, AMessage>>, call: Call)
    ensures
        service_request(
            network.push(Envelope {
                sender: APid::Outside,
                recipient: APid::Service,
                message: AMessage::Request(call),
            }),
            call,
        ),
{
    let added = Envelope {
        sender: APid::Outside,
        recipient: APid::Service,
        message: AMessage::Request(call),
    };
    let later = network.push(added);
    let j = network.len() as int;
    assert(later[j] == added);
}

pub proof fn lemma_envelope_at<P, M>(sender: P, send: Seq<(P, M)>, k: int)
    requires
        0 <= k < send.len(),
    ensures
        envelopes(sender, send).len() == send.len(),
        envelopes(sender, send)[k] == (Envelope { sender, recipient: send[k].0, message: send[k].1 }),
{
}

/// The outputs of one abstract send are on the network it lands on.
pub proof fn lemma_sent_outputs(
    network: Seq<Envelope<APid, AMessage>>,
    send: Seq<(APid, AMessage)>,
    k: int,
)
    requires
        0 <= k < send.len(),
        send[k].0 == APid::Outside,
        send[k].1 is Output,
    ensures
        service_output(network + envelopes(APid::Service, send), send[k].1->Output_0),
{
    let later = network + envelopes(APid::Service, send);
    let j = network.len() + k;
    lemma_envelope_at(APid::Service, send, k);
    assert(later[j] == envelopes(APid::Service, send)[k]);
}

// ---------------------------------------------------------------------------
// One abstract step, and the empty execution
// ---------------------------------------------------------------------------

pub proof fn lemma_empty_matches(config: ServerConfig, before: World<AModel>)
    ensures
        matches(abstract_model(), config, before, Seq::<BoundaryEvent>::empty(), before),
{
    let execution = Seq::<(Label<APid, AMessage>, World<AModel>)>::empty();
    assert forall|i: int| 0 <= i < execution.len() implies #[trigger] step(
        abstract_model(),
        config,
        echod_rover::rover::semantics::before::<AModel>(before, execution, i),
        execution[i].0,
        execution[i].1,
    ) by {
        assert(false);
    };
    assert(legal(abstract_model(), config, before, execution));
    assert(project::<AModel>(abstract_model(), execution) =~= Seq::<BoundaryEvent>::empty());
    assert(end::<AModel>(before, execution) == before);
}

pub proof fn lemma_matched_step(
    config: ServerConfig,
    before: World<AModel>,
    label: Label<APid, AMessage>,
    after: World<AModel>,
    visible: Seq<BoundaryEvent>,
)
    requires
        step(abstract_model(), config, before, label, after),
        abstract_model().spec_observe(label) == visible,
    ensures
        matches(abstract_model(), config, before, visible, after),
{
    let pair = (label, after);
    let execution = Seq::<(Label<APid, AMessage>, World<AModel>)>::empty().push(pair);
    assert(execution.len() == 1);
    assert(execution[0] == pair);
    assert(execution.last() == pair);
    assert(execution.drop_last() =~= Seq::<(Label<APid, AMessage>, World<AModel>)>::empty());
    assert(project::<AModel>(abstract_model(), execution.drop_last()) =~= Seq::<BoundaryEvent>::empty());
    let empty = Seq::<BoundaryEvent>::empty();
    assert(empty.add(visible) =~= visible);
    assert(project::<AModel>(abstract_model(), execution) =~= visible);
    assert forall|i: int| 0 <= i < execution.len() implies #[trigger] step(
        abstract_model(),
        config,
        echod_rover::rover::semantics::before::<AModel>(before, execution, i),
        execution[i].0,
        execution[i].1,
    ) by {
        assert(i == 0);
        assert(echod_rover::rover::semantics::before::<AModel>(before, execution, 0) == before);
    };
    assert(legal(abstract_model(), config, before, execution));
    assert(end::<AModel>(before, execution) == after);
}

pub proof fn lemma_matches_same_visible(
    config: ServerConfig,
    before: World<AModel>,
    visible: Seq<BoundaryEvent>,
    same: Seq<BoundaryEvent>,
    after: World<AModel>,
)
    requires
        matches(abstract_model(), config, before, visible, after),
        visible == same,
    ensures
        matches(abstract_model(), config, before, same, after),
{
    let execution = choose|execution: Execution<AModel>|
        #![trigger legal(abstract_model(), config, before, execution)]
        legal(abstract_model(), config, before, execution) && project::<AModel>(abstract_model(), execution)
            == visible && end::<AModel>(before, execution) == after;
    assert(project::<AModel>(abstract_model(), execution) == same);
}

/// Concatenate two invisible abstract executions.
pub proof fn lemma_matches_trans(
    config: ServerConfig,
    first: World<AModel>,
    middle: World<AModel>,
    last: World<AModel>,
)
    requires
        matches(abstract_model(), config, first, Seq::<BoundaryEvent>::empty(), middle),
        matches(abstract_model(), config, middle, Seq::<BoundaryEvent>::empty(), last),
    ensures
        matches(abstract_model(), config, first, Seq::<BoundaryEvent>::empty(), last),
{
    let prefix = choose|execution: Execution<AModel>|
        #![trigger legal(abstract_model(), config, first, execution)]
        legal(abstract_model(), config, first, execution)
            && project::<AModel>(abstract_model(), execution) == Seq::<BoundaryEvent>::empty()
            && end::<AModel>(first, execution) == middle;
    let suffix = choose|execution: Execution<AModel>|
        #![trigger legal(abstract_model(), config, middle, execution)]
        legal(abstract_model(), config, middle, execution)
            && project::<AModel>(abstract_model(), execution) == Seq::<BoundaryEvent>::empty()
            && end::<AModel>(middle, execution) == last;
    lemma_legal_add(abstract_model(), config, first, prefix, suffix);
    lemma_project_add(abstract_model(), prefix, suffix);
    lemma_end_add::<AModel>(first, prefix, suffix);
    assert(Seq::<BoundaryEvent>::empty() + Seq::<BoundaryEvent>::empty()
        =~= Seq::<BoundaryEvent>::empty());
}

/// A process step with the outcome at `j`, stated over the model's trait: the
/// witness `step` asks for is in the form `step` names it.
pub proof fn lemma_process_step<M: RoverModel>(
    m: M,
    config: M::Config,
    world: World<M>,
    i: int,
    at: Time,
    event: ProcessEvent<M::Pid, M::Message>,
    j: int,
)
    requires
        world.now <= at,
        0 <= i < world.process.len(),
        is_process(m, world, world.process[i].0),
        event_valid(world, world.process[i].0, event),
        0 <= j < m.spec_on_event(config, world.process[i].0, world.process[i].1, at, event).len(),
    ensures
        ({
            let process = world.process[i].0;
            let outcome = m.spec_on_event(config, process, world.process[i].1, at, event)[j];
            step(
                m,
                config,
                world,
                Label::Process { process, at, event, send: outcome.send },
                land(world, i, process, at, outcome),
            )
        }),
{
    let process = world.process[i].0;
    let outcome = m.spec_on_event(config, process, world.process[i].1, at, event)[j];
    let next = land(world, i, process, at, outcome);
    assert(exists|i2: int, j2: int|
        #![trigger m.spec_on_event(config, process, world.process[i2].1, at, event)[j2]]
        {
            &&& 0 <= i2 < world.process.len()
            &&& world.process[i2].0 == process
            &&& {
                let outcomes = m.spec_on_event(config, process, world.process[i2].1, at, event);
                &&& 0 <= j2 < outcomes.len()
                &&& outcomes[j2].send == outcome.send
                &&& next == land(world, i2, process, at, outcomes[j2])
            }
        }) by {
        assert(0 <= i < world.process.len() && world.process[i].0 == process && 0 <= j
            < m.spec_on_event(config, process, world.process[i].1, at, event).len()
            && m.spec_on_event(config, process, world.process[i].1, at, event)[j].send == outcome.send
            && next == land(world, i, process, at, m.spec_on_event(config, process, world.process[i].1, at, event)[j]));
    };
    assert(step(m, config, world, Label::Process { process, at, event, send: outcome.send }, next));
}

/// One abstract process step of the service, with the outcome at `index`.
/// The world it lands in: the one slot holds the outcome's state, the
/// network grew by the outcome's sends, the clock is `at`.
pub proof fn lemma_service_step(
    config: ServerConfig,
    before_a: World<AModel>,
    at: Time,
    event: ProcessEvent<APid, AMessage>,
    index: int,
) -> (after_a: World<AModel>)
    requires
        single(before_a),
        before_a.now <= at,
        event_valid(before_a, APid::Service, event),
        0 <= index < abstract_model().spec_on_event(config, APid::Service, astate(before_a), at, event).len(),
    ensures
        ({
            let outcome = abstract_model().spec_on_event(config, APid::Service, astate(before_a), at, event)[index];
            &&& after_a == land(before_a, 0, APid::Service, at, outcome)
            &&& single(after_a)
            &&& astate(after_a) == outcome.state
            &&& after_a.network == before_a.network + envelopes(APid::Service, outcome.send)
            &&& after_a.now == at
            &&& extends(after_a.network, before_a.network)
            &&& matches(abstract_model(), config, before_a, Seq::<BoundaryEvent>::empty(), after_a)
        }),
{
    reveal(step);
    let outcomes = abstract_model().spec_on_event(config, APid::Service, astate(before_a), at, event);
    let outcome = outcomes[index];
    lemma_single_present(before_a);
    let label = Label::Process { process: APid::Service, at, event, send: outcome.send };
    let after_a = land(before_a, 0, APid::Service, at, outcome);
    assert(before_a.process[0].1 == astate(before_a));
    lemma_process_step(abstract_model(), config, before_a, 0, at, event, index);
    assert(step(abstract_model(), config, before_a, label, after_a));
    assert(abstract_model().spec_observe(label) =~= Seq::<BoundaryEvent>::empty());
    lemma_matched_step(config, before_a, label, after_a, Seq::<BoundaryEvent>::empty());
    assert(after_a.process.len() == 1);
    assert(after_a.process[0] == (APid::Service, outcome.state));
    lemma_extends_add(before_a.network, envelopes(APid::Service, outcome.send));
    after_a
}

// ---------------------------------------------------------------------------
// Finding by key
// ---------------------------------------------------------------------------

/// `spec_find` from `j` finds the first entry at or after `j` with the key.
pub proof fn lemma_find_from(entries: Seq<crate::model::EntryV>, key: Seq<char>, j: int)
    requires
        0 <= j <= entries.len(),
    ensures
        match spec_find(entries, key, j) {
            Some(i) => j <= i < entries.len() && entries[i].key == key && forall|k: int|
                j <= k < i ==> #[trigger] entries[k].key != key,
            None => forall|k: int| j <= k < entries.len() ==> #[trigger] entries[k].key != key,
        },
    decreases entries.len() - j,
{
    if j >= entries.len() {
    } else if entries[j].key == key {
    } else {
        lemma_find_from(entries, key, j + 1);
    }
}

/// The characterisation of a hit, in both directions.
pub proof fn lemma_find_is(entries: Seq<crate::model::EntryV>, key: Seq<char>, i: int)
    requires
        0 <= i < entries.len(),
        entries[i].key == key,
        forall|k: int| 0 <= k < i ==> #[trigger] entries[k].key != key,
    ensures
        spec_find(entries, key, 0) == Some(i),
{
    lemma_find_from(entries, key, 0);
    match spec_find(entries, key, 0) {
        Some(found) => {
            if found < i {
                assert(entries[found].key != key);
            } else if found > i {
                assert(entries[i].key != key);
            }
        },
        None => {
            assert(entries[i].key != key);
        },
    }
}

pub proof fn lemma_find_absent(entries: Seq<crate::model::EntryV>, key: Seq<char>)
    requires
        forall|k: int| 0 <= k < entries.len() ==> #[trigger] entries[k].key != key,
    ensures
        spec_find(entries, key, 0) == None::<int>,
{
    lemma_find_from(entries, key, 0);
    match spec_find(entries, key, 0) {
        Some(found) => {
            assert(entries[found].key != key);
        },
        None => {},
    }
}

/// `spec_cached_from` has the same shape.
pub proof fn lemma_cached_from(docs: Seq<CachedV>, key: Seq<char>, j: int)
    requires
        0 <= j <= docs.len(),
    ensures
        match spec_cached_from(docs, key, j) {
            Some(cached) => exists|i: int|
                j <= i < docs.len() && #[trigger] docs[i] == cached && cached.key == key,
            None => forall|k: int| j <= k < docs.len() ==> #[trigger] docs[k].key != key,
        },
    decreases docs.len() - j,
{
    if j >= docs.len() {
    } else if docs[j].key == key {
        assert(docs[j] == docs[j]);
    } else {
        lemma_cached_from(docs, key, j + 1);
    }
}

/// With distinct keys, a hit is the one entry with the key.
pub proof fn lemma_cached_is(docs: Seq<CachedV>, key: Seq<char>, i: int)
    requires
        0 <= i < docs.len(),
        docs[i].key == key,
        forall|j: int, k: int| 0 <= j < k < docs.len() ==> #[trigger] docs[j].key != #[trigger] docs[k].key,
    ensures
        spec_cached_from(docs, key, 0) == Some(docs[i]),
{
    lemma_cached_from(docs, key, 0);
    match spec_cached_from(docs, key, 0) {
        Some(cached) => {
            let found = choose|found: int|
                0 <= found < docs.len() && #[trigger] docs[found] == cached && cached.key == key;
            if found != i {
                if found < i {
                    assert(docs[found].key != docs[i].key);
                } else {
                    assert(docs[i].key != docs[found].key);
                }
            }
        },
        None => {
            assert(docs[i].key != key);
        },
    }
}

pub proof fn lemma_cached_absent(docs: Seq<CachedV>, key: Seq<char>)
    requires
        forall|k: int| 0 <= k < docs.len() ==> #[trigger] docs[k].key != key,
    ensures
        spec_cached_from(docs, key, 0) == None::<CachedV>,
{
    lemma_cached_from(docs, key, 0);
    match spec_cached_from(docs, key, 0) {
        Some(cached) => {
            let found = choose|found: int|
                0 <= found < docs.len() && #[trigger] docs[found] == cached && cached.key == key;
            assert(docs[found].key != key);
        },
        None => {},
    }
}

/// A key the node does not own is not cached.
pub proof fn lemma_unowned_uncached(node: NodeV, key: Seq<char>)
    requires
        cache_owned(node),
        !spec_owns(node, key),
    ensures
        spec_cached(node, key) is None,
{
    assert forall|k: int| 0 <= k < node.documents.len() implies #[trigger] node.documents[k].key
        != key by {
        assert(spec_owns(node, node.documents[k].key));
    };
    lemma_cached_absent(node.documents, key);
}

/// Remembering `key` changes the cache under `key` and nothing else, and
/// keeps the keys distinct.
pub proof fn lemma_remember(
    docs: Seq<CachedV>,
    key: Seq<char>,
    body: Seq<u8>,
    etag: Option<Seq<char>>,
    i: int,
)
    requires
        0 <= i <= docs.len(),
        forall|k: int| 0 <= k < i ==> #[trigger] docs[k].key != key,
        forall|j: int, k: int| 0 <= j < k < docs.len() ==> #[trigger] docs[j].key != #[trigger] docs[k].key,
    ensures
        ({
            let next = spec_remember(docs, key, body, etag, i);
            &&& forall|j: int, k: int| 0 <= j < k < next.len() ==> #[trigger] next[j].key != #[trigger] next[k].key
            &&& spec_cached_from(next, key, 0) == Some(CachedV { key, body, etag })
            &&& forall|other: Seq<char>| other != key ==> #[trigger] spec_cached_from(next, other, 0)
                == spec_cached_from(docs, other, 0)
            &&& forall|k: int| 0 <= k < next.len() ==> #[trigger] next[k].key == key || exists|m: int|
                0 <= m < docs.len() && #[trigger] docs[m] == next[k]
        }),
    decreases docs.len() - i,
{
    let entry = CachedV { key, body, etag };
    let next = spec_remember(docs, key, body, etag, i);
    if i >= docs.len() {
        assert(next == docs.push(entry));
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
            if k == docs.len() {
                assert(next[j] == docs[j]);
                assert(docs[j].key != key);
            }
        };
        assert forall|k: int| 0 <= k < docs.len() implies #[trigger] next[k].key != key by {
            assert(next[k] == docs[k]);
        };
        lemma_cached_is(next, key, docs.len() as int);
        assert forall|other: Seq<char>| other != key implies #[trigger] spec_cached_from(next, other, 0)
            == spec_cached_from(docs, other, 0) by {
            lemma_cached_from(docs, other, 0);
            match spec_cached_from(docs, other, 0) {
                Some(cached) => {
                    let m = choose|m: int|
                        0 <= m < docs.len() && #[trigger] docs[m] == cached && cached.key == other;
                    assert(next[m] == docs[m]);
                    lemma_cached_is(next, other, m);
                },
                None => {
                    assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != other by {
                        if k < docs.len() {
                            assert(next[k] == docs[k]);
                        }
                    };
                    lemma_cached_absent(next, other);
                },
            }
        };
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key == key || exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == next[k] by {
            if k < docs.len() {
                assert(docs[k] == next[k]);
            }
        };
    } else if docs[i].key == key {
        assert(next == docs.update(i, entry));
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
            assert(next[j].key == docs[j].key);
            assert(next[k].key == docs[k].key);
        };
        lemma_cached_is(next, key, i);
        assert forall|other: Seq<char>| other != key implies #[trigger] spec_cached_from(next, other, 0)
            == spec_cached_from(docs, other, 0) by {
            lemma_cached_from(docs, other, 0);
            match spec_cached_from(docs, other, 0) {
                Some(cached) => {
                    let m = choose|m: int|
                        0 <= m < docs.len() && #[trigger] docs[m] == cached && cached.key == other;
                    assert(m != i);
                    assert(next[m] == docs[m]);
                    lemma_cached_is(next, other, m);
                },
                None => {
                    assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != other by {
                        assert(next[k].key == docs[k].key);
                    };
                    lemma_cached_absent(next, other);
                },
            }
        };
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key == key || exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == next[k] by {
            if k != i {
                assert(docs[k] == next[k]);
            }
        };
    } else {
        lemma_remember(docs, key, body, etag, i + 1);
    }
}

/// Forgetting `key` empties the cache under `key` and changes nothing else.
pub proof fn lemma_forget(docs: Seq<CachedV>, key: Seq<char>, i: int)
    requires
        0 <= i <= docs.len(),
        forall|k: int| 0 <= k < i ==> #[trigger] docs[k].key != key,
        forall|j: int, k: int| 0 <= j < k < docs.len() ==> #[trigger] docs[j].key != #[trigger] docs[k].key,
    ensures
        ({
            let next = spec_forget(docs, key, i);
            &&& forall|j: int, k: int| 0 <= j < k < next.len() ==> #[trigger] next[j].key != #[trigger] next[k].key
            &&& spec_cached_from(next, key, 0) is None
            &&& forall|other: Seq<char>| other != key ==> #[trigger] spec_cached_from(next, other, 0)
                == spec_cached_from(docs, other, 0)
            &&& forall|k: int| 0 <= k < next.len() ==> exists|m: int|
                0 <= m < docs.len() && #[trigger] docs[m] == #[trigger] next[k]
        }),
    decreases docs.len() - i,
{
    let next = spec_forget(docs, key, i);
    if i >= docs.len() {
        assert(next == docs);
        lemma_cached_absent(docs, key);
        assert forall|k: int| 0 <= k < next.len() implies exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == #[trigger] next[k] by {
            assert(docs[k] == next[k]);
        };
    } else if docs[i].key == key {
        assert(next == docs.take(i) + docs.skip(i + 1));
        assert(next.len() == docs.len() - 1);
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k] == (if k < i {
            docs[k]
        } else {
            docs[k + 1]
        }) by {
            if k < i {
                assert(next[k] == docs.take(i)[k]);
            } else {
                assert(next[k] == docs.skip(i + 1)[k - i]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
        };
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != key by {
            if k < i {
            } else {
                assert(docs[i].key != docs[k + 1].key);
            }
        };
        lemma_cached_absent(next, key);
        assert forall|other: Seq<char>| other != key implies #[trigger] spec_cached_from(next, other, 0)
            == spec_cached_from(docs, other, 0) by {
            lemma_cached_from(docs, other, 0);
            match spec_cached_from(docs, other, 0) {
                Some(cached) => {
                    let m = choose|m: int|
                        0 <= m < docs.len() && #[trigger] docs[m] == cached && cached.key == other;
                    assert(m != i);
                    if m < i {
                        assert(next[m] == docs[m]);
                        lemma_cached_is(next, other, m);
                    } else {
                        assert(next[m - 1] == docs[m]);
                        lemma_cached_is(next, other, m - 1);
                    }
                },
                None => {
                    lemma_cached_absent(next, other);
                },
            }
        };
        assert forall|k: int| 0 <= k < next.len() implies exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == #[trigger] next[k] by {
            if k < i {
                assert(docs[k] == next[k]);
            } else {
                assert(docs[k + 1] == next[k]);
            }
        };
    } else {
        lemma_forget(docs, key, i + 1);
    }
}

/// `spec_keep` under `key`: the kept document reads as `doc`, or is gone when
/// `doc` is empty and there is no etag. Other keys are untouched.
pub proof fn lemma_keep(
    docs: Seq<CachedV>,
    key: Seq<char>,
    doc: DocumentBodyV,
    etag: Option<Seq<char>>,
)
    requires
        forall|j: int, k: int| 0 <= j < k < docs.len() ==> #[trigger] docs[j].key != #[trigger] docs[k].key,
    ensures
        ({
            let next = spec_keep(docs, key, doc, etag);
            &&& forall|j: int, k: int| 0 <= j < k < next.len() ==> #[trigger] next[j].key != #[trigger] next[k].key
            &&& (spec_body_is_empty(doc) && etag is None ==> spec_cached_from(next, key, 0) is None)
            &&& (!(spec_body_is_empty(doc) && etag is None) ==> spec_cached_from(next, key, 0) == Some(
                CachedV { key, body: spec_encode_body(doc), etag },
            ))
            &&& forall|other: Seq<char>| other != key ==> #[trigger] spec_cached_from(next, other, 0)
                == spec_cached_from(docs, other, 0)
            &&& forall|k: int| 0 <= k < next.len() ==> #[trigger] next[k].key == key || exists|m: int|
                0 <= m < docs.len() && #[trigger] docs[m] == next[k]
        }),
{
    if spec_body_is_empty(doc) && etag is None {
        lemma_forget(docs, key, 0);
        let next = spec_forget(docs, key, 0);
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key == key || exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == next[k] by {
            let m = choose|m: int| 0 <= m < docs.len() && #[trigger] docs[m] == next[k];
            assert(docs[m] == next[k]);
        };
    } else {
        lemma_remember(docs, key, spec_encode_body(doc), etag, 0);
    }
}

// ---------------------------------------------------------------------------
// The store's entries
// ---------------------------------------------------------------------------

/// Inserting an absent key: the new key is found with its body, other keys
/// read as before, and keys stay distinct.
pub proof fn lemma_insert_at(entries: Seq<crate::model::EntryV>, entry: crate::model::EntryV, i: int)
    requires
        0 <= i <= entries.len(),
        forall|k: int| 0 <= k < entries.len() ==> #[trigger] entries[k].key != entry.key,
        forall|j: int, k: int|
            0 <= j < k < entries.len() ==> #[trigger] entries[j].key != #[trigger] entries[k].key,
    ensures
        ({
            let next = crate::store::spec_insert_at(entries, entry, i);
            &&& forall|j: int, k: int| 0 <= j < k < next.len() ==> #[trigger] next[j].key != #[trigger] next[k].key
            &&& physical(crate::model::StoreV { entries: next, appendable: false, seen: Seq::empty() }, entry.key)
                == Some(entry.body)
            &&& forall|other: Seq<char>| other != entry.key ==> #[trigger] physical(
                crate::model::StoreV { entries: next, appendable: false, seen: Seq::empty() },
                other,
            ) == physical(
                crate::model::StoreV { entries, appendable: false, seen: Seq::empty() },
                other,
            )
        }),
    decreases entries.len() - i,
{
    let next = crate::store::spec_insert_at(entries, entry, i);
    let after = crate::model::StoreV { entries: next, appendable: false, seen: Seq::empty() };
    let before_store = crate::model::StoreV { entries, appendable: false, seen: Seq::empty() };
    if i >= entries.len() {
        assert(next == entries.push(entry));
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
            if k == entries.len() {
                assert(next[j] == entries[j]);
            }
        };
        assert forall|k: int| 0 <= k < entries.len() implies #[trigger] next[k].key != entry.key by {
            assert(next[k] == entries[k]);
        };
        lemma_find_is(next, entry.key, entries.len() as int);
        assert forall|other: Seq<char>| other != entry.key implies #[trigger] physical(after, other)
            == physical(before_store, other) by {
            lemma_find_from(entries, other, 0);
            match spec_find(entries, other, 0) {
                Some(m) => {
                    assert(next[m] == entries[m]);
                    assert forall|k: int| 0 <= k < m implies #[trigger] next[k].key != other by {
                        assert(next[k] == entries[k]);
                    };
                    lemma_find_is(next, other, m);
                },
                None => {
                    assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != other by {
                        if k < entries.len() {
                            assert(next[k] == entries[k]);
                        }
                    };
                    lemma_find_absent(next, other);
                },
            }
        };
    } else if crate::store::spec_before(entry.key, entries[i].key) {
        assert(next == entries.take(i).push(entry) + entries.skip(i));
        assert(next.len() == entries.len() + 1);
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k] == (if k < i {
            entries[k]
        } else if k == i {
            entry
        } else {
            entries[k - 1]
        }) by {
            if k < i {
                assert(next[k] == entries.take(i).push(entry)[k]);
            } else if k == i {
                assert(next[k] == entries.take(i).push(entry)[k]);
            } else {
                assert(next[k] == entries.skip(i)[k - i - 1]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
        };
        assert forall|k: int| 0 <= k < i implies #[trigger] next[k].key != entry.key by {
        };
        lemma_find_is(next, entry.key, i);
        assert forall|other: Seq<char>| other != entry.key implies #[trigger] physical(after, other)
            == physical(before_store, other) by {
            lemma_find_from(entries, other, 0);
            match spec_find(entries, other, 0) {
                Some(m) => {
                    if m < i {
                        assert forall|k: int| 0 <= k < m implies #[trigger] next[k].key != other by {
                        };
                        lemma_find_is(next, other, m);
                    } else {
                        assert(next[m + 1] == entries[m]);
                        assert forall|k: int| 0 <= k < m + 1 implies #[trigger] next[k].key != other by {
                        };
                        lemma_find_is(next, other, m + 1);
                    }
                },
                None => {
                    assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != other by {
                    };
                    lemma_find_absent(next, other);
                },
            }
        };
    } else {
        lemma_insert_at(entries, entry, i + 1);
    }
}

/// `spec_put`: the key reads as the new body, other keys as before, and keys
/// stay distinct.
pub proof fn lemma_put(store: crate::model::StoreV, entry: crate::model::EntryV)
    requires
        entries_distinct(store),
    ensures
        ({
            let next = crate::model::StoreV {
                entries: crate::store::spec_put(store.entries, entry),
                ..store
            };
            &&& entries_distinct(next)
            &&& physical(next, entry.key) == Some(entry.body)
            &&& forall|other: Seq<char>| other != entry.key ==> #[trigger] physical(next, other)
                == physical(store, other)
        }),
{
    let entries = store.entries;
    let next_entries = crate::store::spec_put(entries, entry);
    let next = crate::model::StoreV { entries: next_entries, ..store };
    lemma_find_from(entries, entry.key, 0);
    match spec_find(entries, entry.key, 0) {
        Some(i) => {
            assert(next_entries == entries.update(i, entry));
            assert forall|k: int| 0 <= k < next_entries.len() implies #[trigger] next_entries[k].key
                == entries[k].key by {
            };
            lemma_find_is(next_entries, entry.key, i);
            assert forall|other: Seq<char>| other != entry.key implies #[trigger] physical(next, other)
                == physical(store, other) by {
                lemma_find_from(entries, other, 0);
                match spec_find(entries, other, 0) {
                    Some(m) => {
                        assert(m != i);
                        assert(next_entries[m] == entries[m]);
                        lemma_find_is(next_entries, other, m);
                    },
                    None => {
                        lemma_find_absent(next_entries, other);
                    },
                }
            };
        },
        None => {
            lemma_insert_at(entries, entry, 0);
            let bare_next = crate::model::StoreV {
                entries: next_entries,
                appendable: false,
                seen: Seq::empty(),
            };
            let bare = crate::model::StoreV { entries, appendable: false, seen: Seq::empty() };
            assert(physical(bare_next, entry.key) == physical(next, entry.key));
            assert forall|other: Seq<char>| other != entry.key implies #[trigger] physical(next, other)
                == physical(store, other) by {
                assert(physical(bare_next, other) == physical(next, other));
                assert(physical(bare, other) == physical(store, other));
            };
        },
    }
}

// ---------------------------------------------------------------------------
// Occurrences owed
// ---------------------------------------------------------------------------

pub open spec fn owed_by(node: NodeV, item: Sched<InternalV>) -> nat {
    items(occurrences(node)).to_multiset().count(item)
}

/// `owed` from `k` is the sum over the nodes from `k`; replacing one node's
/// state moves the sum by that node's difference.
pub proof fn lemma_owed_update(
    fleet: Fleet,
    before_w: World<CModel>,
    after_w: World<CModel>,
    i: int,
    item: Sched<InternalV>,
    k: int,
)
    requires
        0 <= i < fleet.nodes,
        forall|j: int| 0 <= j < fleet.nodes && j != i ==> #[trigger] node_at(after_w, j) == node_at(before_w, j),
    ensures
        0 <= k <= i ==> owed(fleet, after_w, item, k) + owed_by(node_at(before_w, i), item) == owed(
            fleet,
            before_w,
            item,
            k,
        ) + owed_by(node_at(after_w, i), item),
        k > i ==> owed(fleet, after_w, item, k) == owed(fleet, before_w, item, k),
    decreases fleet.nodes - k,
{
    if k < 0 || k >= fleet.nodes {
    } else {
        lemma_owed_update(fleet, before_w, after_w, i, item, k + 1);
        if k != i {
            assert(node_at(after_w, k) == node_at(before_w, k));
        }
    }
}

pub proof fn lemma_owed_same(
    fleet: Fleet,
    before_w: World<CModel>,
    after_w: World<CModel>,
    item: Sched<InternalV>,
    k: int,
)
    requires
        forall|j: int| 0 <= j < fleet.nodes ==> #[trigger] node_at(after_w, j) == node_at(before_w, j),
    ensures
        owed(fleet, after_w, item, k) == owed(fleet, before_w, item, k),
    decreases fleet.nodes - k,
{
    if k < 0 || k >= fleet.nodes {
    } else {
        lemma_owed_same(fleet, before_w, after_w, item, k + 1);
    }
}

pub proof fn lemma_owed_nonneg(fleet: Fleet, world: World<CModel>, item: Sched<InternalV>, i: int, k: int)
    requires
        0 <= i < fleet.nodes,
        0 <= k <= i,
    ensures
        owed(fleet, world, item, k) >= owed_by(node_at(world, i), item),
    decreases i - k,
{
    if k < i {
        lemma_owed_nonneg(fleet, world, item, i, k + 1);
    }
}

pub proof fn lemma_add_multiset<A>(a: Seq<A>, b: Seq<A>)
    ensures
        (a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset()),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(b =~= Seq::<A>::empty());
        assert(b.to_multiset() =~= Multiset::<A>::empty());
    } else {
        let front = b.drop_last();
        assert(a + b =~= (a + front).push(b.last()));
        assert(b =~= front.push(b.last()));
        lemma_add_multiset(a, front);
    }
}

pub proof fn lemma_items_add(a: Seq<PendingV>, b: Seq<PendingV>)
    ensures
        items(a + b) =~= items(a) + items(b),
{
}

pub proof fn lemma_items_push(a: Seq<PendingV>, p: PendingV)
    ensures
        items(a.push(p)) =~= items(a).push(as_item(p)),
{
}

/// `remove_at` is `remove`.
pub proof fn lemma_remove_at<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        echod_abstract::model::remove_at(s, i) =~= s.remove(i),
{
}

// ---------------------------------------------------------------------------
// Documents
// ---------------------------------------------------------------------------

/// An empty document that reads as `s` under `key` is the empty document.
pub proof fn lemma_empty_body_rel(key: Seq<char>, doc: DocumentBodyV, s: echod_abstract::view::StoreV)
    requires
        doc_rel(key, doc, s),
        spec_body_is_empty(doc),
    ensures
        doc_rel(key, spec_empty_body(key), s),
{
    match doc {
        DocumentBodyV::Workflow(map) => {
            assert(!crate::store::spec_starts(key, crate::interpret::schedule_prefix()));
            assert(map.dom().finite());
            assert(map.dom().len() == 0);
            assert(map.dom() =~= Set::<Seq<char>>::empty());
            assert(map =~= Map::<Seq<char>, crate::node::ObjV>::empty());
            assert(spec_empty_body(key) == DocumentBodyV::Workflow(Map::<Seq<char>, crate::node::ObjV>::empty()));
        },
        DocumentBodyV::Schedule(slot) => {
            assert(slot is None);
            if crate::store::spec_starts(key, crate::interpret::schedule_prefix()) {
                assert(spec_empty_body(key) == DocumentBodyV::Schedule(None::<echod_types::Schedule>));
            } else {
                let map = Map::<Seq<char>, crate::node::ObjV>::empty();
                assert(spec_empty_body(key) == DocumentBodyV::Workflow(map));
                assert(map.dom() =~= Set::<Seq<char>>::empty());
            }
        },
    }
}

/// The owner of a key is the node that owns it.
pub proof fn lemma_owner(fleet: Fleet, world: World<CModel>, i: int, key: Seq<char>)
    requires
        shaped(fleet, world),
        0 <= i < fleet.nodes,
    ensures
        spec_owns(node_at(world, i), key) == (owner(fleet, key) == i),
{
    assert(world.process[i].0 == CPid::Node(i as u64));
    let node = node_at(world, i);
    assert(node.nodes == fleet.nodes);
    assert(node.address == i);
    assert(node.nodes as u64 == fleet.nodes);
    assert(node.address as u64 == i as u64);
}

/// The realised string and bytes.
pub proof fn lemma_string(chars: Seq<char>)
    ensures
        spec_string(chars)@ == chars,
{
    reveal(crate::model::spec_string);
    axiom_string_realised(chars);
}

pub proof fn lemma_bytes(bytes: Seq<u8>)
    ensures
        crate::model::spec_bytes(bytes)@ == bytes,
{
    reveal(crate::model::spec_bytes);
    echod_abstract::trusted::axiom_bytes_realised(bytes);
}

/// `spec_notes` sends each note's output to the outside.
pub proof fn lemma_notes(notes: Seq<NoteV>)
    ensures
        spec_notes(notes).len() == notes.len(),
        forall|k: int|
            0 <= k < notes.len() ==> #[trigger] spec_notes(notes)[k] == (
                CPid::Outside,
                CMessage::Output(note_output(notes[k])),
            ),
    decreases notes.len(),
{
    if notes.len() == 0 {
    } else {
        lemma_notes(notes.drop_first());
        assert(spec_notify(notes[0]) == (CPid::Outside, CMessage::Output(note_output(notes[0]))));
        assert forall|k: int| 0 <= k < notes.len() implies #[trigger] spec_notes(notes)[k] == (
            CPid::Outside,
            CMessage::Output(note_output(notes[k])),
        ) by {
            if k == 0 {
            } else {
                assert(spec_notes(notes)[k] == spec_notes(notes.drop_first())[k - 1]);
                assert(notes.drop_first()[k - 1] == notes[k]);
            }
        };
    }
}

/// A node's reply is the service's output of the same call.
pub proof fn lemma_reply_is_output(call: Call, response: Response)
    ensures
        spec_reply(call.client@, call.id, response) == (
            CPid::Outside,
            CMessage::Output(Output::Response { client: call.client, id: call.id, response }),
        ),
        reply_output(call.client@, call.id, response) == (Output::Response {
            client: call.client,
            id: call.id,
            response,
        }),
{
    lemma_string(call.client@);
    axiom_string_ext(spec_string(call.client@), call.client);
}

/// `decision` reads the job and the time of a flight.
pub proof fn lemma_decision_same(a: FlightV, b: FlightV, doc: DocumentBodyV, retry_timeout: u64)
    requires
        a.job == b.job,
        a.now == b.now,
    ensures
        decision(a, doc, retry_timeout) == decision(b, doc, retry_timeout),
{
    reveal(decision);
}

/// A flight that answers a caller answers the probe's caller.
pub proof fn lemma_reply_same(a: FlightV, b: FlightV, reply: Option<Response>)
    requires
        a.caller == b.caller,
    ensures
        flight_reply(a, reply) == flight_reply(b, reply),
{
}

/// The empty document is empty.
pub proof fn lemma_empty_is_empty(key: Seq<char>)
    ensures
        spec_body_is_empty(spec_empty_body(key)),
{
    if crate::store::spec_starts(key, seq!['s', '/']) {
    } else {
        let map = Map::<Seq<char>, crate::node::ObjV>::empty();
        assert(map.dom() =~= Set::<Seq<char>>::empty());
        assert(Set::<Seq<char>>::empty().len() == 0);
    }
}

/// Forgetting a key that is not cached changes nothing.
pub proof fn lemma_forget_absent(docs: Seq<CachedV>, key: Seq<char>, i: int)
    requires
        0 <= i <= docs.len(),
        forall|k: int| 0 <= k < docs.len() ==> #[trigger] docs[k].key != key,
    ensures
        spec_forget(docs, key, i) == docs,
    decreases docs.len() - i,
{
    if i >= docs.len() {
    } else {
        lemma_forget_absent(docs, key, i + 1);
    }
}

/// `spec_decide` from a reading flight: the node keeps the document and
/// answers, or opens the write of what it decided.
pub proof fn lemma_decide(node: NodeV, flight: FlightV, doc: DocumentBodyV)
    requires
        !flight.writing,
    ensures
        ({
            let (next, reply, born, notes) = decision(flight, doc, node.retry_timeout);
            let (after, send) = spec_decide(node, flight, doc);
            if next == held(node, flight.key) && born.len() == 0 {
                &&& after == NodeV {
                    flight: None,
                    documents: spec_keep(node.documents, flight.key, next, flight.etag),
                    ..node
                }
                &&& send == reply_send(flight_reply(flight, reply)) + spec_notes(notes)
            } else {
                let w = written(node, flight, doc);
                &&& after == NodeV { flight: Some(w), next_op: (node.next_op + 1) as u64, ..node }
                &&& send == seq![(CPid::Store, CMessage::StoreReq { op: node.next_op, call: request_of(w) })]
            }
        }),
{
    reveal(decision);
    let (next, reply, born, notes) = decision(flight, doc, node.retry_timeout);
    let (after, send) = spec_decide(node, flight, doc);
    if next == held(node, flight.key) && born.len() == 0 {
    } else {
        let w = written(node, flight, doc);
        assert(w.decided == Some(spec_encode_body(next)));
        assert(w.writing);
        match flight.etag {
            Some(chars) => {
                assert(request_of(w) == StoreCall::PutIfMatch {
                    key: spec_string(flight.key),
                    body: spec_bytes(spec_encode_body(next)),
                    etag: Etag(spec_string(chars)),
                });
            },
            None => {
                assert(request_of(w) == StoreCall::PutIfNoneMatch {
                    key: spec_string(flight.key),
                    body: spec_bytes(spec_encode_body(next)),
                });
            },
        }
    }
}

/// The node slots of the initial world.
pub proof fn lemma_spec_nodes(fleet: Fleet, id: u64)
    requires
        id <= fleet.nodes,
    ensures
        spec_nodes(fleet, id).len() == fleet.nodes - id,
        forall|k: int|
            0 <= k < fleet.nodes - id ==> #[trigger] spec_nodes(fleet, id)[k] == (
                CPid::Node((id + k) as u64),
                LocalV::Node(initial_node(fleet, (id + k) as u64)),
            ),
    decreases fleet.nodes - id,
{
    if id >= fleet.nodes {
    } else {
        lemma_spec_nodes(fleet, (id + 1) as u64);
        let head = seq![(CPid::Node(id), LocalV::Node(initial_node(fleet, id)))];
        let tail = spec_nodes(fleet, (id + 1) as u64);
        assert(spec_nodes(fleet, id) == head + tail);
        assert forall|k: int| 0 <= k < fleet.nodes - id implies #[trigger] spec_nodes(fleet, id)[k] == (
            CPid::Node((id + k) as u64),
            LocalV::Node(initial_node(fleet, (id + k) as u64)),
        ) by {
            if k == 0 {
                assert((head + tail)[0] == head[0]);
            } else {
                assert((head + tail)[k] == tail[k - 1]);
            }
        };
    }
}

/// `spec_queue` from `m` offers the ready item at `k >= m`.
pub proof fn lemma_queue_from(config: ServerConfig, state: StateV, now: Time, m: int, k: int)
    requires
        0 <= m <= k < state.pending.len(),
        spec_ready(spec_body(state.pending[k]), now),
        !spec_process_work(config, spec_body(state.pending[k]), state.store, now).not_due,
    ensures
        ({
            let results = spec_queue(config, state, now, m);
            let outcome = spec_process_work(config, spec_body(state.pending[k]), state.store, now);
            exists|j: int|
                0 <= j < results.len() && #[trigger] results[j] == spec_internal_result(state, k, outcome)
        }),
    decreases k - m,
{
    let results = spec_queue(config, state, now, m);
    let outcome = spec_process_work(config, spec_body(state.pending[k]), state.store, now);
    let wanted = spec_internal_result(state, k, outcome);
    if m == k {
        assert(results[0] == wanted);
    } else {
        lemma_queue_from(config, state, now, m + 1, k);
        let tail = spec_queue(config, state, now, m + 1);
        let j = choose|j: int| 0 <= j < tail.len() && #[trigger] tail[j] == wanted;
        let work = spec_body(state.pending[m]);
        let here = spec_process_work(config, work, state.store, now);
        if spec_ready(work, now) && !here.not_due {
            assert(results == seq![spec_internal_result(state, m, here)] + tail);
            assert(results[j + 1] == tail[j]);
        } else {
            assert(results == tail);
        }
    }
}

/// The service's timeout step offers the ready item at `k`: an index into
/// its outcomes whose state removed that item and sends nothing.
pub proof fn lemma_queue_offers(config: ServerConfig, state: StateV, now: Time, k: int) -> (j: int)
    requires
        0 <= k < state.pending.len(),
        spec_ready(spec_body(state.pending[k]), now),
        !spec_process_work(config, spec_body(state.pending[k]), state.store, now).not_due,
    ensures
        ({
            let outcomes = abstract_model().spec_on_event(config, APid::Service, state, now, ProcessEvent::Timeout);
            let outcome = spec_process_work(config, spec_body(state.pending[k]), state.store, now);
            &&& 0 <= j < outcomes.len()
            &&& outcomes[j] == spec_internal_result(state, k, outcome)
        }),
{
    lemma_queue_from(config, state, now, 0, k);
    let queued = spec_queue(config, state, now, 0);
    let outcome = spec_process_work(config, spec_body(state.pending[k]), state.store, now);
    let wanted = spec_internal_result(state, k, outcome);
    let j = choose|j: int| 0 <= j < queued.len() && #[trigger] queued[j] == wanted;
    let results = spec_run_timeout(config, state, now);
    assert(results == queued + crate::simulation::derived(config, state, now));
    assert(results[j] == queued[j]);
    assert(results.len() > 0);
    assert(abstract_model().spec_on_event(config, APid::Service, state, now, ProcessEvent::Timeout) == results);
    j
}

/// The second half of `spec_run_timeout`, named so the sum above reads.
pub open spec fn derived(config: ServerConfig, state: StateV, now: Time) -> Seq<StepResultV<StateV, APid, AMessage>> {
    echod_abstract::model::spec_derived(config, state, now)
}

/// A timeout result at `j` is an outcome of the service's timeout step.
pub proof fn lemma_timeout_offers(config: ServerConfig, state: StateV, now: Time, j: int)
    requires
        0 <= j < spec_run_timeout(config, state, now).len(),
    ensures
        ({
            let outcomes = abstract_model().spec_on_event(config, APid::Service, state, now, ProcessEvent::Timeout);
            &&& outcomes == spec_run_timeout(config, state, now)
            &&& 0 <= j < outcomes.len()
        }),
{
}

/// The earliest key is a cached key the node owns.
pub proof fn lemma_earliest_from(
    node: NodeV,
    docs: Seq<CachedV>,
    i: int,
    now: Time,
    best: Option<(u64, Seq<char>)>,
)
    requires
        0 <= i <= docs.len(),
    ensures
        match spec_earliest_from(node, docs, i, now, best) {
            Some(key) => (best is Some && best.unwrap().1 == key) || exists|m: int|
                i <= m < docs.len() && #[trigger] docs[m].key == key && spec_owns(node, key),
            None => true,
        },
    decreases docs.len() - i,
{
    if i >= docs.len() {
    } else if !spec_owns(node, docs[i].key) {
        lemma_earliest_from(node, docs, i + 1, now, best);
    } else {
        match crate::node::spec_earliest_in(spec_read(docs[i].key, docs[i].body), now) {
            Some(at) => {
                let better = match best {
                    None => true,
                    Some((b, _)) => at < b,
                };
                let next_best = if better { Some((at, docs[i].key)) } else { best };
                lemma_earliest_from(node, docs, i + 1, now, next_best);
                match spec_earliest_from(node, docs, i + 1, now, next_best) {
                    Some(key) => {
                        if better && key == docs[i].key {
                            assert(docs[i].key == key && spec_owns(node, key));
                        }
                    },
                    None => {},
                }
            },
            None => {
                lemma_earliest_from(node, docs, i + 1, now, best);
            },
        }
    }
}

pub proof fn lemma_earliest_cached(node: NodeV, now: Time, key: Seq<char>)
    requires
        cache_owned(node),
        spec_earliest_key(node, now) == Some(key),
    ensures
        spec_cached(node, key) is Some,
        spec_owns(node, key),
{
    lemma_earliest_from(node, node.documents, 0, now, None);
    let m = choose|m: int|
        0 <= m < node.documents.len() && #[trigger] node.documents[m].key == key && spec_owns(
            node,
            key,
        );
    lemma_cached_is(node.documents, key, m);
}

/// An item a node owes is queued at the service.
pub proof fn lemma_owed_present(fleet: Fleet, world: World<AModel>, concrete: World<CModel>, i: int, p: PendingV)
    requires
        0 <= i < fleet.nodes,
        pending_covered(fleet, concrete, astate(world)),
        node_at(concrete, i).pending.contains(p),
    ensures
        astate(world).pending.contains(as_item(p)),
{
    let node = node_at(concrete, i);
    let item = as_item(p);
    let all = items(occurrences(node));
    let k = choose|k: int| 0 <= k < node.pending.len() && node.pending[k] == p;
    assert(occurrences(node)[k] == p);
    assert(all[k] == item);
    assert(all.contains(item));
    assert(all.to_multiset().count(item) > 0);
    assert(owed_by(node, item) >= 1);
    lemma_owed_nonneg(fleet, concrete, item, i, 0);
    assert(astate(world).pending.to_multiset().count(item) >= 1);
}

/// Dropping the head of a pending list drops one of its item.
pub proof fn lemma_pending_head(pending: Seq<PendingV>, item: Sched<InternalV>)
    requires
        pending.len() > 0,
    ensures
        items(pending).to_multiset().count(item) == items(pending.skip(1)).to_multiset().count(item) + (
        if item == as_item(pending[0]) {
            1int
        } else {
            0int
        }),
{
    let all = items(pending);
    assert(pending.skip(1) =~= pending.remove(0));
    assert(items(pending.remove(0)) =~= all.remove(0));
    assert(all.remove(0).to_multiset() == all.to_multiset().remove(all[0]));
    assert(all[0] == as_item(pending[0]));
    assert(all.contains(all[0]));
    assert(all.to_multiset().count(all[0]) >= 1);
}

// ---------------------------------------------------------------------------
// Frames
// ---------------------------------------------------------------------------

/// What `land` does for a node step.
pub proof fn lemma_land_node(fleet: Fleet, cb: World<CModel>, i: int, at: Time, node2: NodeV, send: Seq<(CPid, CMessage)>)
    requires
        shaped(fleet, cb),
        0 <= i < fleet.nodes,
        node2.address == i,
        node2.nodes == fleet.nodes,
        node2.retry_timeout == fleet.retry_timeout,
    ensures
        ({
            let ca = land(cb, i, node_pid(i), at, node_result(node2, send));
            &&& shaped(fleet, ca)
            &&& node_at(ca, i) == node2
            &&& forall|k: int| 0 <= k < fleet.nodes && k != i ==> #[trigger] node_at(ca, k) == node_at(cb, k)
            &&& store_at(fleet, ca) == store_at(fleet, cb)
            &&& ca.network == cb.network + envelopes(node_pid(i), send)
            &&& ca.now == at
            &&& extends(ca.network, cb.network)
        }),
{
    let ca = land(cb, i, node_pid(i), at, node_result(node2, send));
    assert(ca.process == cb.process.update(i, (node_pid(i), LocalV::Node(node2))));
    assert(ca.process.len() == cb.process.len());
    assert(ca.process[i] == (node_pid(i), LocalV::Node(node2)));
    assert forall|k: int| 0 <= k < fleet.nodes && k != i implies #[trigger] node_at(ca, k) == node_at(cb, k) by {
        assert(ca.process[k] == cb.process[k]);
    };
    assert(ca.process[fleet.nodes as int] == cb.process[fleet.nodes as int]);
    lemma_extends_add(cb.network, envelopes(node_pid(i), send));
}

/// What `land` does for a store step.
pub proof fn lemma_land_store(fleet: Fleet, cb: World<CModel>, at: Time, store2: CStore, send: Seq<(CPid, CMessage)>)
    requires
        shaped(fleet, cb),
    ensures
        ({
            let ca = land(cb, fleet.nodes as int, CPid::Store, at, store_result(store2, send));
            &&& shaped(fleet, ca)
            &&& store_at(fleet, ca) == store2
            &&& forall|k: int| 0 <= k < fleet.nodes ==> #[trigger] node_at(ca, k) == node_at(cb, k)
            &&& ca.network == cb.network + envelopes(CPid::Store, send)
            &&& ca.now == at
            &&& extends(ca.network, cb.network)
        }),
{
    let slot = fleet.nodes as int;
    let ca = land(cb, slot, CPid::Store, at, store_result(store2, send));
    assert(ca.process == cb.process.update(slot, (CPid::Store, LocalV::Store(store2))));
    assert(ca.process[slot] == (CPid::Store, LocalV::Store(store2)));
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_at(ca, k) == node_at(cb, k) by {
        assert(ca.process[k] == cb.process[k]);
    };
    lemma_extends_add(cb.network, envelopes(CPid::Store, send));
}

pub proof fn lemma_requested_grows(
    earlier: World<CModel>,
    later: World<CModel>,
    sender: CPid,
    op: u64,
)
    requires
        requested(earlier, sender, op),
        extends(later.network, earlier.network),
    ensures
        requested(later, sender, op),
{
    let k = choose|k: int|
        #![trigger earlier.network[k]]
        0 <= k < earlier.network.len() && earlier.network[k].sender == sender
            && earlier.network[k].recipient == CPid::Store && earlier.network[k].message is StoreReq
            && earlier.network[k].message->StoreReq_op == op;
    assert(later.network[k] == earlier.network[k]);
}

/// The invariant survives a step that touched no process and added only
/// envelopes that are not store traffic.
pub proof fn lemma_invariant_grow(fleet: Fleet, cb: World<CModel>, ca: World<CModel>)
    requires
        inv(fleet, cb),
        ca.process == cb.process,
        extends(ca.network, cb.network),
        forall|k: int|
            cb.network.len() <= k < ca.network.len() ==> no_store_traffic(#[trigger] ca.network[k]),
    ensures
        inv(fleet, ca),
{
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_at(ca, k) == node_at(cb, k) by {
        assert(ca.process[k] == cb.process[k]);
    };
    assert(store_at(fleet, ca) == store_at(fleet, cb));
    assert(shaped(fleet, ca));
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
        assert(node_ok(k, node_at(cb, k), store_at(fleet, cb)));
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreReq { op, call } => {
            let env = ca.network[k];
            &&& env.recipient == CPid::Store
            &&& env.sender is Node
            &&& {
                let i = env.sender->Node_0 as int;
                let node = node_at(ca, i);
                &&& 0 <= i < fleet.nodes
                &&& op < node.next_op
                &&& (flight_op(node) == Some(op) ==> call == request_of(node.flight.unwrap()))
                &&& (!store_at(fleet, ca).seen.contains((env.sender, op)) ==> flight_op(node) == Some(op))
            }
        },
        _ => true,
    } by {
        if k < cb.network.len() {
            assert(ca.network[k] == cb.network[k]);
        } else {
            assert(no_store_traffic(ca.network[k]));
        }
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreReply { op, outcome } => {
            let env = ca.network[k];
            &&& env.sender == CPid::Store
            &&& env.recipient is Node
            &&& {
                let i = env.recipient->Node_0 as int;
                let node = node_at(ca, i);
                &&& 0 <= i < fleet.nodes
                &&& store_at(fleet, ca).seen.contains((env.recipient, op))
                &&& (flight_op(node) == Some(op) ==> outcome == outcome_of(node.flight.unwrap()))
            }
        },
        _ => true,
    } by {
        if k < cb.network.len() {
            assert(ca.network[k] == cb.network[k]);
        } else {
            assert(no_store_traffic(ca.network[k]));
        }
    };
    assert forall|pair: (CPid, u64)| #[trigger] store_at(fleet, ca).seen.contains(pair) implies requested(
        ca,
        pair.0,
        pair.1,
    ) by {
        assert(store_at(fleet, cb).seen.contains(pair));
        lemma_requested_grows(cb, ca, pair.0, pair.1);
    };
}

pub proof fn lemma_flight_outputs_monotone(
    node: NodeV,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        flight_outputs_covered(node, earlier),
        extends(later, earlier),
    ensures
        flight_outputs_covered(node, later),
{
    match node.flight {
        None => {},
        Some(flight) => {
            let (_, reply, _, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
            match flight_reply(flight, reply) {
                Some((client, id, response)) => {
                    lemma_service_output_monotone(earlier, later, reply_output(client, id, response));
                },
                None => {},
            }
            assert forall|k: int| 0 <= k < notes.len() implies service_output(later, note_output(#[trigger] notes[k])) by {
                lemma_service_output_monotone(earlier, later, note_output(notes[k]));
            };
        },
    }
}

/// The relation carries to worlds whose processes did not change.
pub proof fn lemma_carry(fleet: Fleet, cb: World<CModel>, ab: World<AModel>, ca: World<CModel>, aa: World<AModel>)
    requires
        related(fleet, cb, ab),
        ca.process == cb.process,
        aa.process == ab.process,
        extends(aa.network, ab.network),
        aa.now <= ca.now,
        requests_covered(ca.network, aa.network),
        outputs_covered(ca.network, aa.network),
        inv(fleet, ca),
    ensures
        related(fleet, ca, aa),
{
    assert(single(aa));
    assert(astate(aa) == astate(ab));
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_at(ca, k) == node_at(cb, k) by {
        assert(ca.process[k] == cb.process[k]);
    };
    assert forall|key: Seq<char>| #[trigger] doc_rel(key, effective(fleet, ca, key), astate(aa).store) by {
        assert(effective(fleet, ca, key) == effective(fleet, cb, key));
    };
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(aa).pending.to_multiset().count(item) by {
        lemma_owed_same(fleet, cb, ca, item, 0);
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), aa.network) by {
        lemma_flight_outputs_monotone(node_at(cb, k), ab.network, aa.network);
    };
}

/// What `related` says of node `i`, instantiated.
pub proof fn lemma_node_facts(fleet: Fleet, cb: World<CModel>, ab: World<AModel>, i: int)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
    ensures
        shaped(fleet, cb),
        cb.process[i].0 == CPid::Node(i as u64),
        cb.process[i].1 is Node,
        node_at(cb, i).address == i,
        node_at(cb, i).nodes == fleet.nodes,
        node_at(cb, i).retry_timeout == fleet.retry_timeout,
        node_ok(i, node_at(cb, i), store_at(fleet, cb)),
        flight_outputs_covered(node_at(cb, i), ab.network),
{
    assert(cb.process[i].0 == CPid::Node(i as u64));
    assert(node_ok(i, node_at(cb, i), store_at(fleet, cb)));
    assert(flight_outputs_covered(node_at(cb, i), ab.network));
}

/// `node_ok` reads nothing of the pending list or the shell.
pub proof fn lemma_node_ok_pending(i: int, node0: NodeV, node2: NodeV, store: CStore)
    requires
        node_ok(i, node0, store),
        same_work(node2, NodeV { pending: node2.pending, ..node0 }),
    ensures
        node_ok(i, node2, store),
{
    assert(node2.flight == node0.flight);
    assert(node2.documents == node0.documents);
    assert(node2.next_op == node0.next_op);
    assert(node2.address == node0.address);
    assert(node2.nodes == node0.nodes);
    assert(node2.retry_timeout == node0.retry_timeout);
    assert forall|key: Seq<char>| #[trigger] spec_cached(node2, key) == spec_cached(node0, key) by {
    };
    assert forall|key: Seq<char>| #[trigger] loaded(node2, key) == loaded(node0, key) by {
    };
    match node0.flight {
        None => {},
        Some(flight) => {
            assert(loaded(node2, flight.key) == loaded(node0, flight.key));
            assert(decision(flight, loaded(node2, flight.key), node2.retry_timeout) == decision(flight, loaded(node0, flight.key), node0.retry_timeout));
            assert(cached_etag(node2, flight.key) == cached_etag(node0, flight.key));
        },
    }
    assert(flight_ok(node2));
    assert(cache_owned(node2));
    assert forall|key: Seq<char>| spec_owns(node2, key) implies (if applied_write(i, node2, store, key) {
        physical(store, key) == node2.flight.unwrap().decided
    } else {
        match #[trigger] spec_cached(node2, key) {
            Some(cached) => cache_entry_ok(key, cached, store),
            None => physical(store, key) is None,
        }
    }) by {
        assert(spec_owns(node0, key));
        assert(applied_write(i, node2, store, key) == applied_write(i, node0, store, key));
    };
}

/// A node without a flight that keeps a document it had cached still
/// agrees with the store: `key` is cached again with the bytes it held,
/// every other key is cached as before.
pub proof fn lemma_cache_ok_keep(
    i: int,
    node0: NodeV,
    node2: NodeV,
    store: CStore,
    key: Seq<char>,
    c: CachedV,
    next: DocumentBodyV,
)
    requires
        cache_ok(i, node0, store),
        node0.flight is None,
        node2.flight is None,
        node2.address == node0.address,
        node2.nodes == node0.nodes,
        spec_cached(node0, key) == Some(c),
        cache_entry_ok(key, c, store),
        c.body == spec_encode_body(next),
        spec_body_is_empty(next) && c.etag is None ==> spec_cached(node2, key) is None,
        !(spec_body_is_empty(next) && c.etag is None) ==> spec_cached(node2, key) == Some(
            CachedV { key, body: spec_encode_body(next), etag: c.etag },
        ),
        forall|other: Seq<char>| other != key ==> #[trigger] spec_cached(node2, other)
            == spec_cached(node0, other),
    ensures
        cache_ok(i, node2, store),
{
    assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
        physical(store, k) == node2.flight.unwrap().decided
    } else {
        match #[trigger] spec_cached(node2, k) {
            Some(cc) => cache_entry_ok(k, cc, store),
            None => physical(store, k) is None,
        }
    }) by {
        assert(!applied_write(i, node2, store, k));
        assert(spec_owns(node0, k));
        assert(!applied_write(i, node0, store, k));
        if k == key {
            if spec_body_is_empty(next) && c.etag is None {
                assert(physical(store, key) is None);
            } else {
                lemma_cached_from(node0.documents, key, 0);
                assert(c.key == key);
                assert(CachedV { key, body: spec_encode_body(next), etag: c.etag } == c);
            }
        } else {
            assert(spec_cached(node2, k) == spec_cached(node0, k));
        }
    };
}

/// A node step that sent nothing and changed only its pending list, owing
/// no more than before, is an empty abstract execution.
pub proof fn lemma_silent(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    ca: World<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        same_work(node2, NodeV { pending: node2.pending, ..node_at(cb, i) }),
        forall|item: Sched<InternalV>| #[trigger] owed_by(node2, item) <= owed_by(node_at(cb, i), item),
        ca == land(cb, i, node_pid(i), at, node_result(node2, Seq::empty())),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_empty_matches(config, ab);
    let node0 = node_at(cb, i);
    let store = store_at(fleet, cb);
    assert(node2.flight == node0.flight);
    assert(node2.documents == node0.documents);
    assert(node2.next_op == node0.next_op);
    assert(node2.address == node0.address);
    assert(node2.nodes == node0.nodes);
    assert(shaped(fleet, cb));
    assert(cb.process[i].0 == CPid::Node(i as u64));
    lemma_land_node(fleet, cb, i, at, node2, Seq::empty());
    assert(envelopes(node_pid(i), Seq::<(CPid, CMessage)>::empty()) =~= Seq::<Envelope<CPid, CMessage>>::empty());
    assert(ca.network =~= cb.network);
    // invariant
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
        if k == i {
            assert(node_ok(i, node0, store));
            lemma_node_ok_pending(i, node0, node2, store);
        }
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreReq { op, call } => {
            let env = ca.network[k];
            &&& env.recipient == CPid::Store
            &&& env.sender is Node
            &&& {
                let n = env.sender->Node_0 as int;
                let node = node_at(ca, n);
                &&& 0 <= n < fleet.nodes
                &&& op < node.next_op
                &&& (flight_op(node) == Some(op) ==> call == request_of(node.flight.unwrap()))
                &&& (!store_at(fleet, ca).seen.contains((env.sender, op)) ==> flight_op(node) == Some(op))
            }
        },
        _ => true,
    } by {
        assert(ca.network[k] == cb.network[k]);
        match cb.network[k].message {
            CMessage::StoreReq { op, call } => {
                let n = cb.network[k].sender->Node_0 as int;
                if n == i {
                    assert(node_at(ca, n).flight == node_at(cb, n).flight);
                    assert(node_at(ca, n).next_op == node_at(cb, n).next_op);
                }
            },
            _ => {},
        }
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreReply { op, outcome } => {
            let env = ca.network[k];
            &&& env.sender == CPid::Store
            &&& env.recipient is Node
            &&& {
                let n = env.recipient->Node_0 as int;
                let node = node_at(ca, n);
                &&& 0 <= n < fleet.nodes
                &&& store_at(fleet, ca).seen.contains((env.recipient, op))
                &&& (flight_op(node) == Some(op) ==> outcome == outcome_of(node.flight.unwrap()))
            }
        },
        _ => true,
    } by {
        assert(ca.network[k] == cb.network[k]);
        match cb.network[k].message {
            CMessage::StoreReply { op, outcome } => {
                let n = cb.network[k].recipient->Node_0 as int;
                if n == i {
                    assert(node_at(ca, n).flight == node_at(cb, n).flight);
                    assert(node_at(ca, n).next_op == node_at(cb, n).next_op);
                }
            },
            _ => {},
        }
    };
    assert forall|pair: (CPid, u64)| #[trigger] store_at(fleet, ca).seen.contains(pair) implies requested(
        ca,
        pair.0,
        pair.1,
    ) by {
        lemma_requested_grows(cb, ca, pair.0, pair.1);
    };
    assert(inv(fleet, ca));
    // the store, read through the nodes
    assert forall|key: Seq<char>| #[trigger] doc_rel(key, effective(fleet, ca, key), astate(ab).store) by {
        let o = owner(fleet, key);
        if o == i {
            assert(intended(node2, key) == intended(node0, key));
        }
        assert(effective(fleet, ca, key) == effective(fleet, cb, key));
    };
    // the occurrences
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(ab).pending.to_multiset().count(item) by {
        lemma_owed_update(fleet, cb, ca, i, item, 0);
        lemma_owed_nonneg(fleet, cb, item, i, 0);
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), ab.network) by {
        if k == i {
            assert(flight_outputs_covered(node0, ab.network));
            match node2.flight {
                None => {},
                Some(flight) => {
                    assert(loaded(node2, flight.key) == loaded(node0, flight.key));
                },
            }
        }
    };
    lemma_extends_refl(ab.network);
    assert(requests_covered(ca.network, ab.network));
    assert(outputs_covered(ca.network, ab.network));
    assert(related(fleet, ca, ab));
}

/// A node step that changed nothing of the work and sent nothing.
pub proof fn lemma_same_work(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    ca: World<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        same_work(node2, node_at(cb, i)),
        ca == land(cb, i, node_pid(i), at, node_result(node2, Seq::empty())),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    let node0 = node_at(cb, i);
    assert forall|item: Sched<InternalV>| #[trigger] owed_by(node2, item) <= owed_by(node0, item) by {
        assert(occurrences(node2) == occurrences(node0));
    };
    lemma_silent(fleet, config, cb, ab, i, at, node2, ca);
}

/// The relation does not read a node's shell: a world that differs from a
/// related one in the `logic`, `wake`, `next_request` of one node is related
/// to the same abstract world.
pub proof fn lemma_shell(
    fleet: Fleet,
    config: ServerConfig,
    ca: World<CModel>,
    aa: World<AModel>,
    i: int,
    node2: NodeV,
    cs: World<CModel>,
)
    requires
        related(fleet, ca, aa),
        0 <= i < fleet.nodes,
        same_work(node2, node_at(ca, i)),
        cs.process == ca.process.update(i, (node_pid(i), LocalV::Node(node2))),
        cs.network == ca.network,
        cs.now == ca.now,
    ensures
        related(fleet, cs, aa),
{
    assert(envelopes(node_pid(i), Seq::<(CPid, CMessage)>::empty()) =~= Seq::<Envelope<CPid, CMessage>>::empty());
    assert(ca.network + envelopes(node_pid(i), Seq::<(CPid, CMessage)>::empty()) =~= ca.network);
    assert(cs == land(ca, i, node_pid(i), ca.now, node_result(node2, Seq::empty())));
    lemma_same_work(fleet, config, ca, aa, i, ca.now, node2, cs);
}

/// A node step lands `node2` where the work lemmas landed `next`, the same
/// work under a new shell: the landed worlds are related to the same
/// abstract world.
pub proof fn lemma_reshell(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    aa: World<AModel>,
    i: int,
    at: Time,
    next: NodeV,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
)
    requires
        related(fleet, land(cb, i, node_pid(i), at, node_result(next, send)), aa),
        0 <= i < fleet.nodes,
        same_work(node2, next),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        related(fleet, ca, aa),
{
    let cw = land(cb, i, node_pid(i), at, node_result(next, send));
    assert(shaped(fleet, cw));
    assert(cw.process[i] == (node_pid(i), LocalV::Node(next)));
    assert(node_at(cw, i) == next);
    assert(ca.process =~= cw.process.update(i, (node_pid(i), LocalV::Node(node2))));
    lemma_shell(fleet, config, cw, aa, i, node2, ca);
}

/// A node step that dropped the head of its pending list and sent nothing.
pub proof fn lemma_pop_silent(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    ca: World<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).pending.len() > 0,
        same_work(node2, NodeV { pending: node_at(cb, i).pending.skip(1), ..node_at(cb, i) }),
        ca == land(cb, i, node_pid(i), at, node_result(node2, Seq::empty())),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    let node0 = node_at(cb, i);
    let pending = node0.pending;
    assert forall|item: Sched<InternalV>| #[trigger] owed_by(node2, item) <= owed_by(node0, item) by {
        assert(born_of(node2) == born_of(node0));
        lemma_items_add(pending, born_of(node0));
        lemma_items_add(pending.skip(1), born_of(node0));
        lemma_add_multiset(items(pending), items(born_of(node0)));
        lemma_add_multiset(items(pending.skip(1)), items(born_of(node0)));
        lemma_pending_head(pending, item);
    };
    lemma_silent(fleet, config, cb, ab, i, at, node2, ca);
}

// ---------------------------------------------------------------------------
// A flight begins
// ---------------------------------------------------------------------------

/// The job a begin is given names the key and carries a caller as the
/// flight will.
pub open spec fn begin_keyed(key: Seq<char>, job: JobV, caller: Option<(Seq<char>, u64)>) -> bool {
    match job {
        JobV::External(request) => caller is Some && spec_key(request) == Some(key),
        JobV::Due => caller is None,
        JobV::Occurrence(pending) => caller is None && key == crate::node::spec_origin_key(
            origin(pending.promise),
        ),
    }
}

/// No op the node has not issued is one the store has seen.
pub proof fn lemma_fresh_op(fleet: Fleet, world: World<CModel>, i: int, op: u64)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        op >= node_at(world, i).next_op,
    ensures
        !store_at(fleet, world).seen.contains((node_pid(i), op)),
        !requested(world, node_pid(i), op),
{
    if requested(world, node_pid(i), op) {
        let k = choose|k: int|
            #![trigger world.network[k]]
            0 <= k < world.network.len() && world.network[k].sender == node_pid(i)
                && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
                && world.network[k].message->StoreReq_op == op;
        assert(op < node_at(world, i).next_op);
        assert(false);
    }
    if store_at(fleet, world).seen.contains((node_pid(i), op)) {
        assert(requested(world, node_pid(i), op));
        assert(false);
    }
}

/// Every op a node without a flight has issued, the store has seen.
pub proof fn lemma_idle_answered(fleet: Fleet, world: World<CModel>, i: int, op: u64)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        node_at(world, i).flight is None,
        requested(world, node_pid(i), op),
    ensures
        store_at(fleet, world).seen.contains((node_pid(i), op)),
{
    let k = choose|k: int|
        #![trigger world.network[k]]
        0 <= k < world.network.len() && world.network[k].sender == node_pid(i)
            && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
            && world.network[k].message->StoreReq_op == op;
    assert(flight_op(node_at(world, i)) is None);
}

/// Every op a node with a flight has issued, other than the flight's, the
/// store has seen.
pub proof fn lemma_busy_answered(fleet: Fleet, world: World<CModel>, i: int, op: u64)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        node_at(world, i).flight is Some,
        node_at(world, i).flight.unwrap().op != op,
        requested(world, node_pid(i), op),
    ensures
        store_at(fleet, world).seen.contains((node_pid(i), op)),
{
    let k = choose|k: int|
        #![trigger world.network[k]]
        0 <= k < world.network.len() && world.network[k].sender == node_pid(i)
            && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
            && world.network[k].message->StoreReq_op == op;
}

/// A seen op of a node is below its next op.
pub proof fn lemma_seen_issued(fleet: Fleet, world: World<CModel>, i: int, op: u64)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        store_at(fleet, world).seen.contains((node_pid(i), op)),
    ensures
        op < node_at(world, i).next_op,
{
    assert(requested(world, node_pid(i), op));
    let k = choose|k: int|
        #![trigger world.network[k]]
        0 <= k < world.network.len() && world.network[k].sender == node_pid(i)
            && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
            && world.network[k].message->StoreReq_op == op;
}

/// Store traffic on the network stays right when node `i` moves on and
/// every op it issued before is answered: the new node's next op is at
/// least the old one, its flight, if any, is on a fresh op, and the
/// envelopes added are that flight's request or no store traffic.
pub proof fn lemma_traffic_ok(
    fleet: Fleet,
    cb: World<CModel>,
    ca: World<CModel>,
    i: int,
    node2: NodeV,
)
    requires
        inv(fleet, cb),
        0 <= i < fleet.nodes,
        shaped(fleet, ca),
        node_at(ca, i) == node2,
        forall|k: int| 0 <= k < fleet.nodes && k != i ==> #[trigger] node_at(ca, k) == node_at(cb, k),
        store_at(fleet, ca) == store_at(fleet, cb),
        extends(ca.network, cb.network),
        node2.next_op >= node_at(cb, i).next_op,
        forall|op: u64| requested(cb, node_pid(i), op) ==> store_at(fleet, cb).seen.contains((node_pid(i), op)),
        match node2.flight {
            Some(flight) => flight.op >= node_at(cb, i).next_op && flight.op < node2.next_op,
            None => true,
        },
        forall|k: int|
            cb.network.len() <= k < ca.network.len() ==> no_store_traffic(#[trigger] ca.network[k]) || (
            node2.flight is Some && ca.network[k] == Envelope {
                sender: node_pid(i),
                recipient: CPid::Store,
                message: CMessage::StoreReq {
                    op: node2.flight.unwrap().op,
                    call: request_of(node2.flight.unwrap()),
                },
            }),
    ensures
        requests_ok(fleet, ca),
        replies_ok(fleet, ca),
        seen_ok(fleet, ca),
{
    let node0 = node_at(cb, i);
    let store = store_at(fleet, cb);
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreReq { op, call } => {
            let env = ca.network[k];
            &&& env.recipient == CPid::Store
            &&& env.sender is Node
            &&& {
                let n = env.sender->Node_0 as int;
                let node = node_at(ca, n);
                &&& 0 <= n < fleet.nodes
                &&& op < node.next_op
                &&& (flight_op(node) == Some(op) ==> call == request_of(node.flight.unwrap()))
                &&& (!store_at(fleet, ca).seen.contains((env.sender, op)) ==> flight_op(node) == Some(op))
            }
        },
        _ => true,
    } by {
        if k < cb.network.len() {
            assert(ca.network[k] == cb.network[k]);
            match cb.network[k].message {
                CMessage::StoreReq { op, call } => {
                    let n = cb.network[k].sender->Node_0 as int;
                    if n == i {
                        assert(requested(cb, node_pid(i), op));
                        assert(store.seen.contains((node_pid(i), op)));
                        assert(op < node0.next_op);
                        match node2.flight {
                            Some(flight) => {
                                assert(flight.op != op);
                            },
                            None => {},
                        }
                    }
                },
                _ => {},
            }
        } else {
            if !no_store_traffic(ca.network[k]) {
                let flight = node2.flight.unwrap();
                assert(ca.network[k].message == CMessage::StoreReq { op: flight.op, call: request_of(flight) });
                assert(flight_op(node2) == Some(flight.op));
            }
        }
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreReply { op, outcome } => {
            let env = ca.network[k];
            &&& env.sender == CPid::Store
            &&& env.recipient is Node
            &&& {
                let n = env.recipient->Node_0 as int;
                let node = node_at(ca, n);
                &&& 0 <= n < fleet.nodes
                &&& store_at(fleet, ca).seen.contains((env.recipient, op))
                &&& (flight_op(node) == Some(op) ==> outcome == outcome_of(node.flight.unwrap()))
            }
        },
        _ => true,
    } by {
        if k < cb.network.len() {
            assert(ca.network[k] == cb.network[k]);
            match cb.network[k].message {
                CMessage::StoreReply { op, outcome } => {
                    let n = cb.network[k].recipient->Node_0 as int;
                    if n == i {
                        lemma_seen_issued(fleet, cb, i, op);
                        match node2.flight {
                            Some(flight) => {
                                assert(flight.op != op);
                            },
                            None => {},
                        }
                    }
                },
                _ => {},
            }
        } else {
            assert(!(ca.network[k].message is StoreReply));
        }
    };
    assert forall|pair: (CPid, u64)| #[trigger] store_at(fleet, ca).seen.contains(pair) implies requested(
        ca,
        pair.0,
        pair.1,
    ) by {
        lemma_requested_grows(cb, ca, pair.0, pair.1);
    };
}

/// The store, read through the nodes, after node `i` changed what it stands
/// for under `key` and nothing else.
pub proof fn lemma_interpreted_update(
    fleet: Fleet,
    cb: World<CModel>,
    ca: World<CModel>,
    i: int,
    key: Seq<char>,
    s: AStore,
    next: AStore,
)
    requires
        shaped(fleet, cb),
        shaped(fleet, ca),
        0 <= i < fleet.nodes,
        store_interpreted(fleet, cb, s),
        forall|k: int| 0 <= k < fleet.nodes && k != i ==> #[trigger] node_at(ca, k) == node_at(cb, k),
        spec_owns(node_at(cb, i), key),
        doc_rel(key, effective(fleet, ca, key), next),
        forall|other: Seq<char>|
            other != key && spec_owns(node_at(cb, i), other) ==> #[trigger] intended(node_at(ca, i), other)
                == intended(node_at(cb, i), other),
        others_kept(key, s, next),
    ensures
        store_interpreted(fleet, ca, next),
{
    lemma_owner(fleet, cb, i, key);
    assert forall|other: Seq<char>| #[trigger] doc_rel(other, effective(fleet, ca, other), next) by {
        if other == key {
        } else {
            let o = owner(fleet, other);
            if o == i {
                lemma_owner(fleet, cb, i, other);
                assert(spec_owns(node_at(cb, i), other));
                assert(effective(fleet, ca, other) == effective(fleet, cb, other));
            } else {
                assert(effective(fleet, ca, other) == effective(fleet, cb, other));
            }
            assert(doc_rel(other, effective(fleet, cb, other), s));
        }
    };
}

/// After a flight began at node `i`, the two worlds are related: the
/// abstract world took the step the begin stands for.
pub proof fn lemma_begin_related(
    fleet: Fleet,
    cb: World<CModel>,
    ab: World<AModel>,
    ca: World<CModel>,
    aa: World<AModel>,
    i: int,
    at: Time,
    node1: NodeV,
    key: Seq<char>,
    job: JobV,
    caller: Option<(Seq<char>, u64)>,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        node1 == (NodeV { pending: node1.pending, ..node_at(cb, i) }),
        spec_owns(node1, key),
        begin_keyed(key, job, caller),
        (node2, send) == spec_begin(node1, key, job, at, caller),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
        single(aa),
        aa.now <= at,
        extends(aa.network, ab.network),
        finite_store(astate(aa).store),
        ({
            let doc = held(node1, key);
            let (next, reply, born, notes) = decision(probe(key, at, caller, job), doc, node1.retry_timeout);
            &&& doc_rel(key, next, astate(aa).store)
            &&& others_kept(key, astate(ab).store, astate(aa).store)
            &&& forall|item: Sched<InternalV>|
                owed(fleet, cb, item, 0) - owed_by(node_at(cb, i), item) + items(node1.pending + born).to_multiset().count(item)
                    <= #[trigger] astate(aa).pending.to_multiset().count(item)
            &&& match flight_reply(probe(key, at, caller, job), reply) {
                Some((client, id, response)) => service_output(aa.network, reply_output(client, id, response)),
                None => true,
            }
            &&& forall|k: int| 0 <= k < notes.len() ==> service_output(aa.network, note_output(#[trigger] notes[k]))
        }),
    ensures
        related(fleet, ca, aa),
{
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let store = store_at(fleet, cb);
    let s = astate(ab).store;
    let next_store = astate(aa).store;
    let doc = held(node1, key);
    let probe_flight = probe(key, at, caller, job);
    let (next, reply, born, notes) = decision(probe_flight, doc, node0.retry_timeout);
    let op = node0.next_op;
    assert(node1.documents == node0.documents);
    assert(node1.next_op == op);
    assert(node1.flight is None);
    assert(doc == loaded(node0, key));
    assert(spec_owns(node0, key));
    lemma_owner(fleet, cb, i, key);
    assert(effective(fleet, cb, key) == doc);
    assert(doc_rel(key, doc, s));
    lemma_land_node(fleet, cb, i, at, node2, send);
    assert(node_at(ca, i) == node2);
    assert(store_at(fleet, ca) == store);
    lemma_fresh_op(fleet, cb, i, op);
    assert forall|o: u64| requested(cb, node_pid(i), o) implies store.seen.contains((node_pid(i), o)) by {
        lemma_idle_answered(fleet, cb, i, o);
    };
    // the node after the begin
    let cached = spec_cached(node1, key);
    match cached {
        None => {
            let r = spec_flight(op, key, None, at, caller, job);
            assert(node2 == NodeV { flight: Some(r), next_op: (op + 1) as u64, ..node1 });
            assert(send == seq![spec_get(op, key)]);
            assert(request_of(r) == StoreCall::Get { key: spec_string(key) });
            lemma_decision_same(r, probe_flight, doc, node0.retry_timeout);
            lemma_reply_same(r, probe_flight, reply);
            assert(loaded(node2, key) == doc);
            assert(doc == spec_empty_body(key));
            // facts of the node
            assert(flight_ok(node2));
            assert(cache_owned(node2));
            assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
                physical(store, k) == node2.flight.unwrap().decided
            } else {
                match #[trigger] spec_cached(node2, k) {
                    Some(c) => cache_entry_ok(k, c, store),
                    None => physical(store, k) is None,
                }
            }) by {
                assert(!applied_write(i, node2, store, k));
                assert(spec_owns(node0, k));
                assert(!applied_write(i, node0, store, k));
                assert(spec_cached(node2, k) == spec_cached(node0, k));
            };
            assert(node_ok(i, node2, store));
            lemma_envelope_at(node_pid(i), send, 0);
            assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) || (
                node2.flight is Some && ca.network[k] == Envelope {
                    sender: node_pid(i),
                    recipient: CPid::Store,
                    message: CMessage::StoreReq {
                        op: node2.flight.unwrap().op,
                        call: request_of(node2.flight.unwrap()),
                    },
                }) by {
                assert(k == cb.network.len());
                assert(ca.network[k] == envelopes(node_pid(i), send)[0]);
            };
            lemma_traffic_ok(fleet, cb, ca, i, node2);
            // the store, read through the nodes
            assert(intended(node2, key) == next);
            assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
                == intended(node0, other) by {
                assert(spec_cached(node2, other) == spec_cached(node0, other));
            };
            lemma_interpreted_update(fleet, cb, ca, i, key, s, next_store);
            // the occurrences
            assert(born_of(node2) == born);
            assert(occurrences(node2) == node1.pending + born);
            // the outputs of the flight
            assert(flight_outputs_covered(node2, aa.network));
            // coverage of the new envelope
            assert forall|k: int|
                #![trigger send[k]]
                0 <= k < envelopes(node_pid(i), send).len() implies carried_request(
                envelopes(node_pid(i), send)[k],
                aa.network,
            ) && carried_output(envelopes(node_pid(i), send)[k], aa.network) by {
                assert(k == 0);
            };
            lemma_append_keeps_coverage(cb.network, envelopes(node_pid(i), send), ab.network, aa.network);
        },
        Some(c) => {
            let f = spec_flight(0, key, c.etag, at, caller, job);
            assert(doc == spec_read(key, c.body));
            assert((node2, send) == spec_decide(node1, f, doc));
            lemma_decision_same(f, probe_flight, doc, node0.retry_timeout);
            lemma_reply_same(f, probe_flight, reply);
            lemma_decide(node1, f, doc);
            assert(held(node1, key) == doc);
            assert(cache_entry_ok(key, c, store));
            assert(c.body == spec_encode_body(doc));
            if next == doc && born.len() == 0 {
                // the node keeps the document and answers
                assert(node2 == NodeV {
                    flight: None,
                    documents: spec_keep(node1.documents, key, next, c.etag),
                    ..node1
                });
                assert(send == reply_send(flight_reply(probe_flight, reply)) + spec_notes(notes));
                lemma_keep(node1.documents, key, next, c.etag);
                let docs2 = node2.documents;
                assert(flight_ok(node2));
                assert forall|k: int| 0 <= k < docs2.len() implies spec_owns(node2, #[trigger] docs2[k].key) by {
                    if docs2[k].key == key {
                    } else {
                        let m = choose|m: int| 0 <= m < node1.documents.len() && #[trigger] node1.documents[m] == docs2[k];
                        assert(spec_owns(node0, node0.documents[m].key));
                    }
                };
                assert(cache_owned(node2));
                assert(spec_cached(node0, key) == Some(c));
                assert forall|other: Seq<char>| other != key implies #[trigger] spec_cached(node2, other)
                    == spec_cached(node0, other) by {
                    assert(spec_cached_from(docs2, other, 0) == spec_cached_from(node1.documents, other, 0));
                };
                lemma_cache_ok_keep(i, node0, node2, store, key, c, next);
                assert(node_ok(i, node2, store));
                // the envelopes are outputs
                lemma_notes(notes);
                let sent = envelopes(node_pid(i), send);
                assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) || (
                    node2.flight is Some && ca.network[k] == Envelope {
                        sender: node_pid(i),
                        recipient: CPid::Store,
                        message: CMessage::StoreReq {
                            op: node2.flight.unwrap().op,
                            call: request_of(node2.flight.unwrap()),
                        },
                    }) by {
                    let m = k - cb.network.len();
                    lemma_envelope_at(node_pid(i), send, m);
                    assert(ca.network[k] == sent[m]);
                    let head = reply_send(flight_reply(probe_flight, reply));
                    if m < head.len() {
                        assert(send[m] == head[m]);
                        assert(send[m].1 is Output);
                    } else {
                        assert(send[m] == spec_notes(notes)[m - head.len()]);
                        assert(send[m].1 is Output);
                    }
                };
                lemma_traffic_ok(fleet, cb, ca, i, node2);
                // the store, read through the nodes
                if spec_body_is_empty(next) && c.etag is None {
                    assert(intended(node2, key) == spec_empty_body(key));
                    lemma_empty_body_rel(key, next, next_store);
                } else {
                    axiom_decode_encode_body(next);
                    assert(intended(node2, key) == spec_read(key, spec_encode_body(next)));
                    assert(intended(node2, key) == next);
                }
                assert(doc_rel(key, effective(fleet, ca, key), next_store));
                assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
                    == intended(node0, other) by {
                    assert(spec_cached(node2, other) == spec_cached(node0, other));
                };
                lemma_interpreted_update(fleet, cb, ca, i, key, s, next_store);
                // the occurrences
                assert(born =~= Seq::<PendingV>::empty());
                assert(occurrences(node2) =~= node1.pending + born);
                assert(flight_outputs_covered(node2, aa.network));
                // coverage of the new envelopes: each is an output the service sent
                assert forall|k: int|
                    #![trigger sent[k]]
                    0 <= k < sent.len() implies carried_request(sent[k], aa.network) && carried_output(
                    sent[k],
                    aa.network,
                ) by {
                    lemma_envelope_at(node_pid(i), send, k);
                    let head = reply_send(flight_reply(probe_flight, reply));
                    if k < head.len() {
                        let (client, id, response) = flight_reply(probe_flight, reply).unwrap();
                        assert(send[k] == spec_reply(client, id, response));
                        assert(sent[k].message == CMessage::Output(reply_output(client, id, response)));
                    } else {
                        let n = k - head.len();
                        assert(send[k] == spec_notes(notes)[n]);
                        assert(sent[k].message == CMessage::Output(note_output(notes[n])));
                    }
                };
                lemma_append_keeps_coverage(cb.network, sent, ab.network, aa.network);
            } else {
                // the node opens the write
                let w = written(node1, f, doc);
                assert(node2 == NodeV { flight: Some(w), next_op: (op + 1) as u64, ..node1 });
                assert(send == seq![(CPid::Store, CMessage::StoreReq { op, call: request_of(w) })]);
                assert(w.op == op);
                assert(w.key == key);
                assert(w.job == job);
                assert(w.now == at);
                assert(w.caller == caller);
                assert(w.etag == c.etag);
                lemma_decision_same(w, probe_flight, doc, node0.retry_timeout);
                lemma_reply_same(w, probe_flight, reply);
                assert(loaded(node2, key) == doc);
                assert(cached_etag(node2, key) == c.etag);
                assert(flight_ok(node2));
                assert(cache_owned(node2));
                assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
                    physical(store, k) == node2.flight.unwrap().decided
                } else {
                    match #[trigger] spec_cached(node2, k) {
                        Some(cc) => cache_entry_ok(k, cc, store),
                        None => physical(store, k) is None,
                    }
                }) by {
                    assert(!store.seen.contains((node_pid(i), op)));
                    assert(!applied_write(i, node2, store, k));
                    assert(spec_owns(node0, k));
                    assert(!applied_write(i, node0, store, k));
                    assert(spec_cached(node2, k) == spec_cached(node0, k));
                };
                assert(node_ok(i, node2, store));
                lemma_envelope_at(node_pid(i), send, 0);
                assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) || (
                    node2.flight is Some && ca.network[k] == Envelope {
                        sender: node_pid(i),
                        recipient: CPid::Store,
                        message: CMessage::StoreReq {
                            op: node2.flight.unwrap().op,
                            call: request_of(node2.flight.unwrap()),
                        },
                    }) by {
                    assert(k == cb.network.len());
                    assert(ca.network[k] == envelopes(node_pid(i), send)[0]);
                };
                lemma_traffic_ok(fleet, cb, ca, i, node2);
                assert(intended(node2, key) == next);
                assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
                    == intended(node0, other) by {
                    assert(spec_cached(node2, other) == spec_cached(node0, other));
                };
                lemma_interpreted_update(fleet, cb, ca, i, key, s, next_store);
                assert(born_of(node2) == born);
                assert(occurrences(node2) == node1.pending + born);
                assert(flight_outputs_covered(node2, aa.network));
                assert forall|k: int|
                    #![trigger send[k]]
                    0 <= k < envelopes(node_pid(i), send).len() implies carried_request(
                    envelopes(node_pid(i), send)[k],
                    aa.network,
                ) && carried_output(envelopes(node_pid(i), send)[k], aa.network) by {
                    assert(k == 0);
                };
                lemma_append_keeps_coverage(cb.network, envelopes(node_pid(i), send), ab.network, aa.network);
            }
        },
    }
    // what the cases share
    assert(inv(fleet, ca)) by {
        assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
            if k != i {
                assert(node_at(ca, k) == node_at(cb, k));
            }
        };
    };
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(aa).pending.to_multiset().count(item) by {
        lemma_owed_update(fleet, cb, ca, i, item, 0);
        lemma_owed_nonneg(fleet, cb, item, i, 0);
        assert(owed_by(node2, item) == items(node1.pending + born).to_multiset().count(item));
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), aa.network) by {
        if k != i {
            lemma_flight_outputs_monotone(node_at(cb, k), ab.network, aa.network);
        }
    };
    assert(coupled(ca, aa));
    assert(related(fleet, ca, aa));
}

// ---------------------------------------------------------------------------
// A client request
// ---------------------------------------------------------------------------

/// The one send of a served or shed call is the service's output of its reply.
pub proof fn lemma_send_is_reply(network: Seq<Envelope<APid, AMessage>>, call: Call, response: Response)
    ensures
        ({
            let send = spec_send(call, response, Seq::empty());
            &&& send.len() == 1
            &&& service_output(network + envelopes(APid::Service, send), reply_output(call.client@, call.id, response))
        }),
{
    let send = spec_send(call, response, Seq::empty());
    let output = Output::Response { client: call.client, id: call.id, response };
    assert(Seq::<echod_abstract::view::DispatchV>::empty().map_values(
        |dispatch: echod_abstract::view::DispatchV| (
            APid::Outside,
            AMessage::Output(Output::Dispatch(echod_abstract::view::lift_dispatch(dispatch))),
        ),
    ) =~= Seq::<(APid, AMessage)>::empty());
    assert(send =~= seq![(APid::Outside, AMessage::Output(output))]);
    assert(send[0] == (APid::Outside, AMessage::Output(output)));
    lemma_sent_outputs(network, send, 0);
    lemma_reply_is_output(call, response);
}

/// A node that answered a call without a flight, against an abstract world
/// whose state stayed and whose network carries that reply.
pub proof fn lemma_answered_idle(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    ca: World<CModel>,
    aa: World<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    call: Call,
    response: Response,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node2 == node_at(cb, i),
        ca == land(cb, i, node_pid(i), at, node_result(node2, seq![spec_reply(call.client@, call.id, response)])),
        single(aa),
        aa.process == ab.process,
        aa.now <= at,
        extends(aa.network, ab.network),
        service_output(aa.network, reply_output(call.client@, call.id, response)),
    ensures
        related(fleet, ca, aa),
{
    let send = seq![spec_reply(call.client@, call.id, response)];
    let cm = land(cb, i, node_pid(i), at, node_result(node2, Seq::empty()));
    lemma_same_work(fleet, config, cb, ab, i, at, node2, cm);
    assert(ca.process == cm.process);
    assert(envelopes(node_pid(i), Seq::<(CPid, CMessage)>::empty()) =~= Seq::<Envelope<CPid, CMessage>>::empty());
    assert(cm.network =~= cb.network);
    let sent = envelopes(node_pid(i), send);
    assert(ca.network == cm.network + sent);
    lemma_extends_add(cm.network, sent);
    lemma_envelope_at(node_pid(i), send, 0);
    assert(sent[0].message == CMessage::Output(reply_output(call.client@, call.id, response)));
    assert forall|k: int| cm.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) by {
        assert(ca.network[k] == sent[0]);
    };
    lemma_invariant_grow(fleet, cm, ca);
    assert forall|k: int|
        #![trigger sent[k]]
        0 <= k < sent.len() implies carried_request(sent[k], aa.network) && carried_output(sent[k], aa.network) by {
        assert(k == 0);
    };
    lemma_append_keeps_coverage(cm.network, sent, ab.network, aa.network);
    lemma_carry(fleet, cm, ab, ca, aa);
}

/// A call whose handler the node runs: the service serves it, with the
/// first outcome, at the same time, on the store the node's document reads as.
pub proof fn lemma_sweep_matches(
    config: ServerConfig,
    before_a: World<AModel>,
    key: Seq<char>,
    doc: DocumentBodyV,
    now: Time,
    limit: nat,
) -> (after_a: World<AModel>)
    requires
        agreement(config),
        single(before_a),
        before_a.now <= now,
        doc_rel(key, doc, astate(before_a).store),
        finite_store(astate(before_a).store),
    ensures
        ({
            let (next, born, notes) =
                spec_sweep(doc, now, config.retry_timeout, limit);
            &&& matches(
                abstract_model(),
                config,
                before_a,
                Seq::<BoundaryEvent>::empty(),
                after_a,
            )
            &&& single(after_a)
            &&& after_a.now <= now
            &&& doc_rel(key, next, astate(after_a).store)
            &&& others_kept(
                key,
                astate(before_a).store,
                astate(after_a).store,
            )
            &&& finite_store(astate(after_a).store)
            &&& astate(after_a).pending
                == astate(before_a).pending + items(born)
            &&& after_a.network
                == before_a.network
                    + envelopes(APid::Service, note_sends(notes))
        }),
    decreases limit,
{
    if limit == 0 {
        lemma_empty_matches(config, before_a);
        lemma_others_same(key, astate(before_a).store);
        assert(items(Seq::<PendingV>::empty()) =~= Seq::<Sched<InternalV>>::empty());
        assert(note_sends(Seq::<NoteV>::empty())
            =~= Seq::<(APid, AMessage)>::empty());
        assert(envelopes(
            APid::Service,
            Seq::<(APid, AMessage)>::empty(),
        ) =~= Seq::<Envelope<APid, AMessage>>::empty());
        return before_a;
    }

    let state = astate(before_a);
    let (next, _, born, notes) =
        spec_run_due(doc, now, config.retry_timeout);
    if next == doc {
        lemma_empty_matches(config, before_a);
        lemma_others_same(key, state.store);
        assert(items(Seq::<PendingV>::empty())
            =~= Seq::<Sched<InternalV>>::empty());
        assert(note_sends(Seq::<NoteV>::empty())
            =~= Seq::<(APid, AMessage)>::empty());
        assert(envelopes(
            APid::Service,
            Seq::<(APid, AMessage)>::empty(),
        )
            =~= Seq::<Envelope<APid, AMessage>>::empty());
        return before_a;
    }

    assert(dues_agree(config));
    assert(due_agrees(config, key, doc, state, now));
    let results = spec_run_timeout(config, state, now);
    let j = choose|j: int|
        {
            &&& 0 <= j < results.len()
            &&& (#[trigger] results[j]).send == note_sends(notes)
            &&& results[j].state.pending == state.pending + items(born)
            &&& doc_rel(key, next, results[j].state.store)
            &&& others_kept(key, state.store, results[j].state.store)
            &&& finite_store(results[j].state.store)
        };
    lemma_timeout_offers(config, state, now, j);
    let middle = lemma_service_step(
        config,
        before_a,
        now,
        ProcessEvent::Timeout,
        j,
    );
    assert(astate(middle) == results[j].state);
    let last = lemma_sweep_matches(
        config,
        middle,
        key,
        next,
        now,
        (limit - 1) as nat,
    );
    lemma_matches_trans(config, before_a, middle, last);

    let (_, tail_born, tail_notes) =
        spec_sweep(next, now, config.retry_timeout, (limit - 1) as nat);
    assert(items(born + tail_born) =~= items(born) + items(tail_born));
    assert(note_sends(notes + tail_notes)
        =~= note_sends(notes) + note_sends(tail_notes));
    assert(envelopes(
        APid::Service,
        note_sends(notes) + note_sends(tail_notes),
    ) =~= envelopes(APid::Service, note_sends(notes))
        + envelopes(APid::Service, note_sends(tail_notes)));
    assert((state.pending + items(born)) + items(tail_born)
        =~= state.pending + items(born + tail_born));
    assert((before_a.network + envelopes(APid::Service, note_sends(notes)))
        + envelopes(APid::Service, note_sends(tail_notes))
        =~= before_a.network
            + envelopes(APid::Service, note_sends(notes + tail_notes)));
    assert forall|other: Seq<char>, body: DocumentBodyV|
        other != key && doc_rel(other, body, state.store)
            implies #[trigger] doc_rel(other, body, astate(last).store) by {
        assert(doc_rel(other, body, astate(middle).store));
    };
    last
}

#[verifier::rlimit(100)]
pub proof fn lemma_request_commit_matches(
    config: ServerConfig,
    before_a: World<AModel>,
    key: Seq<char>,
    doc: DocumentBodyV,
    at: Time,
    call: Call,
    limit: nat,
) -> (after_a: World<AModel>)
    requires
        agreement(config),
        single(before_a),
        before_a.now <= at,
        service_request(before_a.network, call),
        spec_key(call.request) == Some(key),
        doc_rel(key, doc, astate(before_a).store),
        finite_store(astate(before_a).store),
        spec_request_commits(
            doc,
            call.request,
            at,
            config.retry_timeout,
            limit,
        ),
    ensures
        ({
            let (next, response, born, notes) = spec_request_transition(
                doc,
                call.request,
                at,
                config.retry_timeout,
                limit,
            );
            &&& matches(
                abstract_model(),
                config,
                before_a,
                Seq::<BoundaryEvent>::empty(),
                after_a,
            )
            &&& single(after_a)
            &&& after_a.now <= at
            &&& extends(after_a.network, before_a.network)
            &&& doc_rel(key, next, astate(after_a).store)
            &&& others_kept(
                key,
                astate(before_a).store,
                astate(after_a).store,
            )
            &&& finite_store(astate(after_a).store)
            &&& astate(after_a).pending
                == astate(before_a).pending + items(born)
            &&& service_output(
                after_a.network,
                reply_output(call.client@, call.id, response),
            )
            &&& forall|k: int| 0 <= k < notes.len() ==>
                service_output(
                    after_a.network,
                    note_output(#[trigger] notes[k]),
                )
        }),
{
    let state = astate(before_a);
    if spec_preflight_error(doc, call.request, at) is Some {
        let response = spec_preflight_error(doc, call.request, at).unwrap();
        assert(spec_request_transition(
            doc,
            call.request,
            at,
            config.retry_timeout,
            limit,
        ) == (
            doc,
            response,
            Seq::<PendingV>::empty(),
            Seq::<NoteV>::empty(),
        ));
        assert(spec_handle(doc, call.request, at) == (doc, response));
        assert(request_agrees(
            config,
            call.request,
            key,
            doc,
            state.store,
            at,
        ));
        let outs = spec_handler(config, call.request, state.store, at);
        assert(outs.len() == 1);
        assert(outs[0].resp == response);
        assert(outs[0].next == state.store);
        assert(outs[0].work =~= Seq::<Sched<InternalV>>::empty());
        assert(outs[0].send
            =~= Seq::<echod_abstract::view::DispatchV>::empty());
        let event = ProcessEvent::Receive {
            sender: APid::Outside,
            message: AMessage::Request(call),
        };
        assert(event_valid(before_a, APid::Service, event));
        let outcomes = abstract_model().spec_on_event(
            config,
            APid::Service,
            state,
            at,
            event,
        );
        let served = spec_run(config, state, call, at);
        assert(served.len() == 1);
        assert(outcomes[0] == served[0]);
        let handled_a = lemma_service_step(config, before_a, at, event, 0);
        assert(astate(handled_a).store == state.store);
        assert(astate(handled_a).pending == state.pending);
        lemma_others_same(key, state.store);
        lemma_send_is_reply(before_a.network, call, response);
        assert(service_output(
            handled_a.network,
            reply_output(call.client@, call.id, response),
        ));
        assert(items(Seq::<PendingV>::empty())
            =~= Seq::<Sched<InternalV>>::empty());
        return handled_a;
    }
    let (before, born_before, notes_before) =
        spec_sweep(doc, at, config.retry_timeout, limit);
    let swept_a =
        lemma_sweep_matches(config, before_a, key, doc, at, limit);
    lemma_extends_add(
        before_a.network,
        envelopes(APid::Service, note_sends(notes_before)),
    );
    lemma_service_request_monotone(before_a.network, swept_a.network, call);
    assert(request_agrees(
        config,
        call.request,
        key,
        before,
        astate(swept_a).store,
        at,
    ));
    let (handled, raw_response) = spec_handle(before, call.request, at);
    let outs = spec_handler(
        config,
        call.request,
        astate(swept_a).store,
        at,
    );
    assert(outs.len() == 1);
    assert(outs[0].resp == raw_response);
    assert(outs[0].work =~= Seq::<Sched<InternalV>>::empty());
    assert(outs[0].send
        =~= Seq::<echod_abstract::view::DispatchV>::empty());
    let event = ProcessEvent::Receive {
        sender: APid::Outside,
        message: AMessage::Request(call),
    };
    assert(event_valid(swept_a, APid::Service, event));
    let outcomes = abstract_model().spec_on_event(
        config,
        APid::Service,
        astate(swept_a),
        at,
        event,
    );
    let served = spec_run(config, astate(swept_a), call, at);
    assert(served.len() == 1);
    assert(outcomes[0] == served[0]);
    let handled_a = lemma_service_step(config, swept_a, at, event, 0);
    assert(astate(handled_a).store == outs[0].next);
    assert(doc_rel(key, handled, astate(handled_a).store));
    assert(astate(handled_a).pending == astate(swept_a).pending);
    assert(finite_store(astate(handled_a).store));

    let (after, born_after, notes_after) =
        spec_sweep(handled, at, config.retry_timeout, limit);
    let last =
        lemma_sweep_matches(config, handled_a, key, handled, at, limit);
    lemma_matches_trans(config, before_a, swept_a, handled_a);
    lemma_matches_trans(config, before_a, handled_a, last);
    let (next, response, born, notes) = spec_request_transition(
        doc,
        call.request,
        at,
        config.retry_timeout,
        limit,
    );
    assert(next == after);
    assert(response == raw_response);
    assert(born == born_before + born_after);
    assert(notes == notes_before + notes_after);
    assert(astate(last).pending == state.pending + items(born));
    assert forall|other: Seq<char>, body: DocumentBodyV|
        other != key && doc_rel(other, body, state.store)
            implies #[trigger] doc_rel(other, body, astate(last).store) by {
        assert(doc_rel(other, body, astate(swept_a).store));
        assert(doc_rel(other, body, astate(handled_a).store));
    };
    lemma_send_is_reply(swept_a.network, call, response);
    assert(service_output(
        handled_a.network,
        reply_output(call.client@, call.id, response),
    ));
    lemma_service_output_monotone(
        handled_a.network,
        last.network,
        reply_output(call.client@, call.id, response),
    );
    lemma_note_sends(before_a.network, notes_before);
    assert forall|k: int| 0 <= k < notes.len()
        implies service_output(
            last.network,
            note_output(#[trigger] notes[k]),
        ) by {
        if k < notes_before.len() {
            assert(service_output(
                swept_a.network,
                note_output(notes_before[k]),
            ));
            lemma_service_output_monotone(
                swept_a.network,
                last.network,
                note_output(notes_before[k]),
            );
        } else {
            let j = k - notes_before.len();
            lemma_note_sends(handled_a.network, notes_after);
            assert(notes[k] == notes_after[j]);
        }
    };
    last
}

#[verifier::rlimit(200)]
pub proof fn lemma_request_served(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    call: Call,
    key: Seq<char>,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
) -> (aa: World<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        service_request(ab.network, call),
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        spec_key(call.request) == Some(key),
        spec_owns(node_at(cb, i), key),
        (node2, send) == spec_begin(
            node_at(cb, i),
            key,
            JobV::External(call.request),
            at,
            Some((call.client@, call.id)),
        ),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    reveal(decision);
    let node0 = node_at(cb, i);
    let state = astate(ab);
    let s = state.store;
    let caller = Some((call.client@, call.id));
    let job = JobV::External(call.request);
    let doc = held(node0, key);
    lemma_node_facts(fleet, cb, ab, i);
    lemma_owner(fleet, cb, i, key);
    assert(effective(fleet, cb, key) == doc);
    assert(doc_rel(key, doc, s));
    assert(config.retry_timeout == node0.retry_timeout);
    let limit = REQUEST_STEPS as nat;
    let (dnext, response, born, notes) = spec_request_transition(
        doc,
        call.request,
        at,
        config.retry_timeout,
        limit,
    );
    let probe_flight = probe(key, at, caller, job);
    assert(decision(probe_flight, doc, node0.retry_timeout)
        == (dnext, Some(response), born, notes));
    assert(flight_reply(probe_flight, Some(response))
        == Some((call.client@, call.id, response)));
    let event = ProcessEvent::Receive { sender: APid::Outside, message: AMessage::Request(call) };
    assert(event_valid(ab, APid::Service, event));
    if !spec_request_commits(
        doc,
        call.request,
        at,
        config.retry_timeout,
        limit,
    ) {
        assert(dnext == doc);
        assert(response == spec_unavailable(call.request));
        assert(born =~= Seq::<PendingV>::empty());
        assert(notes =~= Seq::<NoteV>::empty());
        let outcomes =
            abstract_model().spec_on_event(config, APid::Service, state, at, event);
        lemma_shed_is_last(config, state, at, call);
        let last = outcomes.len() as int - 1;
        let aa = lemma_service_step(config, ab, at, event, last);
        assert(outcomes[last] == spec_shed(state, call));
        assert(astate(aa) == state);
        lemma_send_is_reply(ab.network, call, response);
        lemma_others_same(key, s);
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item)
                + items(node0.pending + born).to_multiset().count(item)
                <= #[trigger] astate(aa).pending.to_multiset().count(item) by {
            assert(born_of(node0) =~= Seq::<PendingV>::empty());
            assert(occurrences(node0) == node0.pending);
            assert(owed_by(node0, item)
                == items(node0.pending).to_multiset().count(item));
        };
        lemma_begin_related(
            fleet, cb, ab, ca, aa, i, at, node0, key, job, caller, node2, send,
        );
        aa
    } else {
        let aa = lemma_request_commit_matches(
            config, ab, key, doc, at, call, limit,
        );
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item)
                + items(node0.pending + born).to_multiset().count(item)
                <= #[trigger] astate(aa).pending.to_multiset().count(item) by {
            assert(born_of(node0) =~= Seq::<PendingV>::empty());
            assert(occurrences(node0) == node0.pending);
            assert(owed_by(node0, item)
                == items(node0.pending).to_multiset().count(item));
            lemma_add_multiset(state.pending, items(born));
            assert(items(node0.pending + born)
                =~= items(node0.pending) + items(born));
            lemma_add_multiset(items(node0.pending), items(born));
            assert(owed(fleet, cb, item, 0)
                <= state.pending.to_multiset().count(item));
        };
        lemma_begin_related(
            fleet, cb, ab, ca, aa, i, at, node0, key, job, caller, node2, send,
        );
        aa
    }
}

/// A client request at an idle node.
pub proof fn lemma_request(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    call: Call,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
) -> (aa: World<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        event_valid(cb, node_pid(i), ProcessEvent::Receive { sender: CPid::Outside, message: CMessage::Request(call) }),
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        (node2, send) == spec_request(node_at(cb, i), at, call),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    let node0 = node_at(cb, i);
    let state = astate(ab);
    let event = ProcessEvent::Receive { sender: APid::Outside, message: AMessage::Request(call) };
    let wanted = Envelope { sender: CPid::Outside, recipient: node_pid(i), message: CMessage::Request(call) };
    let k = choose|k: int| 0 <= k < cb.network.len() && #[trigger] cb.network[k] == wanted;
    assert(carried_request(cb.network[k], ab.network));
    assert(service_request(ab.network, call));
    let m = choose|m: int|
        #![trigger ab.network[m]]
        0 <= m < ab.network.len() && ab.network[m] == Envelope {
            sender: APid::Outside,
            recipient: APid::Service,
            message: AMessage::Request(call),
        };
    assert(event_valid(ab, APid::Service, event));
    let outcomes = abstract_model().spec_on_event(config, APid::Service, state, at, event);
    match spec_key(call.request) {
        None => {
            assert(node2 == node0);
            let response = spec_pure(call.request);
            assert(send == seq![spec_reply(call.client@, call.id, response)]);
            if empty_heartbeat(call) {
                lemma_empty_heartbeat_is_first(config, state, at, call);
                let aa = lemma_service_step(config, ab, at, event, 0);
                assert(response == Response::Status(echod_types::StatusRes { status: 200 }));
                assert(astate(aa) == state);
                assert(aa.process =~= ab.process);
                lemma_send_is_reply(ab.network, call, response);
                lemma_answered_idle(fleet, config, cb, ab, ca, aa, i, at, node2, call, response);
                aa
            } else {
                lemma_shed_is_last(config, state, at, call);
                let last = outcomes.len() as int - 1;
                let aa = lemma_service_step(config, ab, at, event, last);
                assert(outcomes[last] == spec_shed(state, call));
                assert(response == spec_unavailable(call.request));
                assert(astate(aa) == state);
                assert(aa.process =~= ab.process);
                lemma_send_is_reply(ab.network, call, response);
                lemma_answered_idle(fleet, config, cb, ab, ca, aa, i, at, node2, call, response);
                aa
            }
        },
        Some(key) => {
            if !spec_owns(node0, key) {
                assert(node2 == node0);
                let response = spec_unavailable(call.request);
                assert(send == seq![spec_reply(call.client@, call.id, response)]);
                lemma_shed_is_last(config, state, at, call);
                let last = outcomes.len() as int - 1;
                let aa = lemma_service_step(config, ab, at, event, last);
                assert(outcomes[last] == spec_shed(state, call));
                assert(astate(aa) == state);
                assert(aa.process =~= ab.process);
                lemma_send_is_reply(ab.network, call, response);
                lemma_answered_idle(fleet, config, cb, ab, ca, aa, i, at, node2, call, response);
                aa
            } else {
                lemma_request_served(fleet, config, cb, ab, i, at, call, key, node2, send, ca)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// A timeout: an occurrence, or a due step
// ---------------------------------------------------------------------------

/// One abstract step removed the item at `k` and queued nothing.
pub proof fn lemma_removed_count(pending: Seq<Sched<InternalV>>, k: int, item: Sched<InternalV>)
    requires
        0 <= k < pending.len(),
    ensures
        (remove_at(pending, k) + Seq::<Sched<InternalV>>::empty()).to_multiset().count(item) == pending.to_multiset().count(item) - (
        if item == pending[k] {
            1int
        } else {
            0int
        }),
{
    lemma_remove_at(pending, k);
    assert(remove_at(pending, k) + Seq::<Sched<InternalV>>::empty() =~= pending.remove(k));
    assert(pending.remove(k).to_multiset() == pending.to_multiset().remove(pending[k]));
    assert(pending.contains(pending[k]));
    assert(pending.to_multiset().count(pending[k]) >= 1);
}

/// A queued occurrence at an idle node that owns its origin.
pub proof fn lemma_occurrence_begin(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
) -> (aa: World<AModel>)
    requires
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        node_at(cb, i).pending.len() > 0,
        ({
            let node0 = node_at(cb, i);
            let p = node0.pending[0];
            let node1 = NodeV { pending: node0.pending.skip(1), ..node0 };
            let key = crate::node::spec_origin_key(origin(p.promise));
            &&& spec_owns(node1, key)
            &&& (node2, send) == spec_begin(node1, key, JobV::Occurrence(p), at, None)
        }),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    reveal(decision);
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let pending = node0.pending;
    let p = pending[0];
    let node1 = NodeV { pending: pending.skip(1), ..node0 };
    let key = crate::node::spec_origin_key(origin(p.promise));
    let job = JobV::Occurrence(p);
    let caller = None::<(Seq<char>, u64)>;
    let state = astate(ab);
    let s = state.store;
    let doc = held(node1, key);
    assert(doc == held(node0, key));
    assert(spec_owns(node0, key));
    lemma_owner(fleet, cb, i, key);
    assert(effective(fleet, cb, key) == doc);
    assert(doc_rel(key, doc, s));
    let next = spec_occurrence(doc, p, at);
    let probe_flight = probe(key, at, caller, job);
    let (dnext, dreply, born, notes) = decision(probe_flight, doc, node1.retry_timeout);
    assert(dnext == next);
    assert(dreply is None);
    assert(born.len() == 0);
    assert(notes.len() == 0);
    assert(flight_reply(probe_flight, dreply) is None);
    assert(occurrence_agrees(p, doc, s, at));
    assert(born_of(node0) =~= Seq::<PendingV>::empty());
    assert(born =~= Seq::<PendingV>::empty());
    assert(occurrences(node0) =~= pending);
    assert(node1.pending + born =~= pending.skip(1));
    let item_of = as_item(p);
    if next == doc {
        lemma_empty_matches(config, ab);
        lemma_others_same(key, s);
        lemma_extends_refl(ab.network);
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item) + items(node1.pending + born).to_multiset().count(item)
                <= #[trigger] astate(ab).pending.to_multiset().count(item) by {
            lemma_pending_head(pending, item);
            assert(owed_by(node0, item) == items(pending).to_multiset().count(item));
            assert(owed(fleet, cb, item, 0) <= state.pending.to_multiset().count(item));
        };
        lemma_begin_related(fleet, cb, ab, ca, ab, i, at, node1, key, job, caller, node2, send);
        ab
    } else {
        let out = spec_create_if_absent(s, p.promise, p.at, p.timeout, p.param, p.tags, at);
        assert(!out.not_due);
        assert(out.work.len() == 0);
        assert(out.send.len() == 0);
        assert(doc_rel(key, next, out.next));
        assert(others_kept(key, s, out.next));
        assert(p.at <= at);
        lemma_owed_present(fleet, ab, cb, i, p);
        let k = choose|k: int| 0 <= k < state.pending.len() && state.pending[k] == item_of;
        let work = InternalV::Occurrence {
            promise: p.promise,
            at: p.at,
            timeout: p.timeout,
            param: p.param,
            tags: p.tags,
        };
        assert(spec_body(state.pending[k]) == work);
        assert(spec_ready(work, at));
        assert(spec_process_work(config, work, s, at) == out);
        let j = lemma_queue_offers(config, state, at, k);
        let aa = lemma_service_step(config, ab, at, ProcessEvent::Timeout, j);
        let outcome = abstract_model().spec_on_event(config, APid::Service, state, at, ProcessEvent::Timeout)[j];
        assert(outcome == spec_internal_result(state, k, out));
        assert(astate(aa).store == out.next);
        assert(finite_store(astate(aa).store));
        assert(astate(aa).pending == remove_at(state.pending, k) + out.work);
        assert(out.work =~= Seq::<Sched<InternalV>>::empty());
        assert(outcome.send =~= Seq::<(APid, AMessage)>::empty());
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item) + items(node1.pending + born).to_multiset().count(item)
                <= #[trigger] astate(aa).pending.to_multiset().count(item) by {
            lemma_pending_head(pending, item);
            lemma_removed_count(state.pending, k, item);
            assert(owed_by(node0, item) == items(pending).to_multiset().count(item));
            assert(owed(fleet, cb, item, 0) <= state.pending.to_multiset().count(item));
        };
        lemma_begin_related(fleet, cb, ab, ca, aa, i, at, node1, key, job, caller, node2, send);
        aa
    }
}

/// The notes an abstract timeout result sends are on the network it lands on.
pub proof fn lemma_note_sends(network: Seq<Envelope<APid, AMessage>>, notes: Seq<NoteV>)
    ensures
        forall|k: int|
            0 <= k < notes.len() ==> service_output(
                network + envelopes(APid::Service, note_sends(notes)),
                note_output(#[trigger] notes[k]),
            ),
{
    let send = note_sends(notes);
    assert forall|k: int| 0 <= k < notes.len() implies service_output(
        network + envelopes(APid::Service, send),
        note_output(#[trigger] notes[k]),
    ) by {
        assert(send[k] == (APid::Outside, AMessage::Output(note_output(notes[k]))));
        lemma_sent_outputs(network, send, k);
    };
}

/// The due step of the earliest cached key at an idle node.
pub proof fn lemma_due_begin(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    key: Seq<char>,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
) -> (aa: World<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        node_at(cb, i).pending.len() == 0,
        spec_earliest_key(node_at(cb, i), at) == Some(key),
        (node2, send) == spec_begin(node_at(cb, i), key, JobV::Due, at, None),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    reveal(decision);
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let state = astate(ab);
    let s = state.store;
    let job = JobV::Due;
    let caller = None::<(Seq<char>, u64)>;
    lemma_earliest_cached(node0, at, key);
    lemma_owner(fleet, cb, i, key);
    let doc = held(node0, key);
    assert(effective(fleet, cb, key) == doc);
    assert(doc_rel(key, doc, s));
    let probe_flight = probe(key, at, caller, job);
    let (next, reply, born, notes) = decision(probe_flight, doc, node0.retry_timeout);
    assert(node0.retry_timeout == config.retry_timeout);
    assert((next, reply, born, notes) == spec_run_due(doc, at, config.retry_timeout));
    assert(flight_reply(probe_flight, reply) is None);
    assert(due_agrees(config, key, doc, state, at));
    assert(born_of(node0) =~= Seq::<PendingV>::empty());
    assert(occurrences(node0) =~= Seq::<PendingV>::empty());
    assert(items(Seq::<PendingV>::empty()) =~= Seq::<Sched<InternalV>>::empty());
    assert(node0.pending + born =~= born);
    if next == doc && born.len() == 0 && notes.len() == 0 {
        lemma_empty_matches(config, ab);
        lemma_others_same(key, s);
        lemma_extends_refl(ab.network);
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item) + items(node0.pending + born).to_multiset().count(item)
                <= #[trigger] astate(ab).pending.to_multiset().count(item) by {
            assert(owed_by(node0, item) == 0);
            assert(born =~= Seq::<PendingV>::empty());
            assert(items(born).to_multiset().count(item) == 0);
            assert(owed(fleet, cb, item, 0) <= state.pending.to_multiset().count(item));
        };
        lemma_begin_related(fleet, cb, ab, ca, ab, i, at, node0, key, job, caller, node2, send);
        ab
    } else {
        let results = spec_run_timeout(config, state, at);
        let j = choose|j: int|
            {
                &&& 0 <= j < results.len()
                &&& (#[trigger] results[j]).send == note_sends(notes)
                &&& results[j].state.pending == state.pending + items(born)
                &&& doc_rel(key, next, results[j].state.store)
                &&& others_kept(key, state.store, results[j].state.store)
                &&& finite_store(results[j].state.store)
            };
        lemma_timeout_offers(config, state, at, j);
        let aa = lemma_service_step(config, ab, at, ProcessEvent::Timeout, j);
        assert(astate(aa) == results[j].state);
        assert(finite_store(astate(aa).store));
        assert(aa.network == ab.network + envelopes(APid::Service, note_sends(notes)));
        lemma_note_sends(ab.network, notes);
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item) + items(node0.pending + born).to_multiset().count(item)
                <= #[trigger] astate(aa).pending.to_multiset().count(item) by {
            assert(owed_by(node0, item) == 0);
            lemma_add_multiset(state.pending, items(born));
            assert(owed(fleet, cb, item, 0) <= state.pending.to_multiset().count(item));
        };
        lemma_begin_related(fleet, cb, ab, ca, aa, i, at, node0, key, job, caller, node2, send);
        aa
    }
}

// ---------------------------------------------------------------------------
// The store answers
// ---------------------------------------------------------------------------

/// Every op a busy node issued, the store has seen, once its flight's op is.
pub proof fn lemma_all_answered(fleet: Fleet, world: World<CModel>, i: int)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        node_at(world, i).flight is Some,
        store_at(fleet, world).seen.contains((node_pid(i), node_at(world, i).flight.unwrap().op)),
    ensures
        forall|op: u64| requested(world, node_pid(i), op) ==> store_at(fleet, world).seen.contains((node_pid(i), op)),
{
    let flight = node_at(world, i).flight.unwrap();
    assert forall|op: u64| requested(world, node_pid(i), op) implies store_at(fleet, world).seen.contains((node_pid(i), op)) by {
        if op != flight.op {
            lemma_busy_answered(fleet, world, i, op);
        }
    };
}

/// The sends of a closing flight are outputs the service already sent.
pub proof fn lemma_closing_sends(
    node: NodeV,
    network: Seq<Envelope<APid, AMessage>>,
    i: int,
    send: Seq<(CPid, CMessage)>,
)
    requires
        node.flight is Some,
        flight_outputs_covered(node, network),
        ({
            let flight = node.flight.unwrap();
            let (_, reply, _, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
            send == reply_send(flight_reply(flight, reply)) + spec_notes(notes)
        }),
    ensures
        forall|k: int|
            #![trigger envelopes(node_pid(i), send)[k]]
            0 <= k < send.len() ==> no_store_traffic(envelopes(node_pid(i), send)[k]) && carried_request(
                envelopes(node_pid(i), send)[k],
                network,
            ) && carried_output(envelopes(node_pid(i), send)[k], network),
{
    let flight = node.flight.unwrap();
    let (_, reply, _, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
    let head = reply_send(flight_reply(flight, reply));
    let sent = envelopes(node_pid(i), send);
    lemma_notes(notes);
    assert forall|k: int|
        #![trigger sent[k]]
        0 <= k < send.len() implies no_store_traffic(sent[k]) && carried_request(sent[k], network) && carried_output(
        sent[k],
        network,
    ) by {
        lemma_envelope_at(node_pid(i), send, k);
        if k < head.len() {
            let (client, id, response) = flight_reply(flight, reply).unwrap();
            assert(send[k] == spec_reply(client, id, response));
            assert(sent[k].message == CMessage::Output(reply_output(client, id, response)));
        } else {
            let n = k - head.len();
            assert(send[k] == spec_notes(notes)[n]);
            assert(sent[k].message == CMessage::Output(note_output(notes[n])));
        }
    };
}

/// A flight closes: the node holds what the flight decided, owes what it
/// bore, and sends what the service already sent. An empty abstract execution.
pub proof fn lemma_flight_closed(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is Some,
        store_at(fleet, cb).seen.contains((node_pid(i), node_at(cb, i).flight.unwrap().op)),
        node2.flight is None,
        node2.next_op == node_at(cb, i).next_op,
        node2.address == node_at(cb, i).address,
        node2.nodes == node_at(cb, i).nodes,
        node2.retry_timeout == node_at(cb, i).retry_timeout,
        ({
            let node0 = node_at(cb, i);
                    let flight = node0.flight.unwrap();
            let key = flight.key;
            let (next, reply, born, notes) = decision(flight, loaded(node0, key), node0.retry_timeout);
            let docs2 = node2.documents;
            &&& node2.pending == node0.pending + born
            &&& forall|j: int, k: int| 0 <= j < k < docs2.len() ==> #[trigger] docs2[j].key != #[trigger] docs2[k].key
            &&& forall|other: Seq<char>| other != key ==> #[trigger] spec_cached(node2, other) == spec_cached(node0, other)
            &&& forall|k: int| 0 <= k < docs2.len() ==> #[trigger] docs2[k].key == key || exists|m: int|
                0 <= m < node0.documents.len() && #[trigger] node0.documents[m] == docs2[k]
            &&& loaded(node2, key) == next
            &&& match spec_cached(node2, key) {
                Some(c) => cache_entry_ok(key, c, store_at(fleet, cb)),
                None => physical(store_at(fleet, cb), key) is None,
            }
            &&& send == reply_send(flight_reply(flight, reply)) + spec_notes(notes)
        }),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_empty_matches(config, ab);
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let flight = node0.flight.unwrap();
    let key = flight.key;
    let store = store_at(fleet, cb);
    let s = astate(ab).store;
    let (next, reply, born, notes) = decision(flight, loaded(node0, key), node0.retry_timeout);
    let docs2 = node2.documents;
    assert(flight_ok(node0));
    assert(spec_owns(node0, key));
    lemma_owner(fleet, cb, i, key);
    lemma_land_node(fleet, cb, i, at, node2, send);
    lemma_all_answered(fleet, cb, i);
    // the node
    assert(flight_ok(node2));
    assert forall|k: int| 0 <= k < docs2.len() implies spec_owns(node2, #[trigger] docs2[k].key) by {
        if docs2[k].key == key {
        } else {
            let m = choose|m: int| 0 <= m < node0.documents.len() && #[trigger] node0.documents[m] == docs2[k];
            assert(spec_owns(node0, node0.documents[m].key));
        }
    };
    assert(cache_owned(node2));
    assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
        physical(store, k) == node2.flight.unwrap().decided
    } else {
        match #[trigger] spec_cached(node2, k) {
            Some(c) => cache_entry_ok(k, c, store),
            None => physical(store, k) is None,
        }
    }) by {
        assert(!applied_write(i, node2, store, k));
        assert(spec_owns(node0, k));
        if k == key {
        } else {
            assert(!applied_write(i, node0, store, k));
            assert(spec_cached(node2, k) == spec_cached(node0, k));
        }
    };
    assert(node_ok(i, node2, store));
    // the traffic
    lemma_closing_sends(node0, ab.network, i, send);
    let sent = envelopes(node_pid(i), send);
    assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) by {
        let m = k - cb.network.len();
        assert(ca.network[k] == sent[m]);
    };
    lemma_traffic_ok(fleet, cb, ca, i, node2);
    assert(inv(fleet, ca)) by {
        assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
            if k != i {
                assert(node_at(ca, k) == node_at(cb, k));
            }
        };
    };
    // the store, read through the nodes
    assert(intended(node0, key) == next);
    assert(effective(fleet, cb, key) == next);
    assert(intended(node2, key) == next);
    assert(doc_rel(key, effective(fleet, ca, key), s));
    assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
        == intended(node0, other) by {
        assert(spec_cached(node2, other) == spec_cached(node0, other));
    };
    lemma_others_same(key, s);
    lemma_interpreted_update(fleet, cb, ca, i, key, s, s);
    // the occurrences
    assert(born_of(node0) == born);
    assert(born_of(node2) =~= Seq::<PendingV>::empty());
    assert(occurrences(node2) =~= occurrences(node0));
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(ab).pending.to_multiset().count(item) by {
        assert(owed_by(node2, item) == owed_by(node0, item));
        lemma_owed_update(fleet, cb, ca, i, item, 0);
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), ab.network) by {
        if k != i {
            assert(node_at(ca, k) == node_at(cb, k));
        }
    };
    lemma_extends_refl(ab.network);
    lemma_append_keeps_coverage(cb.network, sent, ab.network, ab.network);
    assert(coupled(ca, ab));
    assert(related(fleet, ca, ab));
}

/// A read came back empty and the flight decided to write: the node opens
/// the write of the same decision. An empty abstract execution.
pub proof fn lemma_write_after_read(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is Some,
        node_at(cb, i).next_op < u64::MAX,
        !node_at(cb, i).flight.unwrap().writing,
        store_at(fleet, cb).seen.contains((node_pid(i), node_at(cb, i).flight.unwrap().op)),
        ({
            let node0 = node_at(cb, i);
            let flight = node0.flight.unwrap();
            let rest = NodeV { flight: None, ..node0 };
            let w = written(rest, flight, spec_empty_body(flight.key));
            &&& node2 == NodeV { flight: Some(w), next_op: (node0.next_op + 1) as u64, ..rest }
            &&& send == seq![(CPid::Store, CMessage::StoreReq { op: node0.next_op, call: request_of(w) })]
        }),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_empty_matches(config, ab);
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let flight = node0.flight.unwrap();
    let key = flight.key;
    let store = store_at(fleet, cb);
    let s = astate(ab).store;
    let op = node0.next_op;
    let rest = NodeV { flight: None, ..node0 };
    let doc = spec_empty_body(key);
    let w = written(rest, flight, doc);
    assert(flight_ok(node0));
    assert(spec_cached(node0, key) is None);
    assert(loaded(node0, key) == doc);
    let (next, reply, born, notes) = decision(flight, doc, node0.retry_timeout);
    assert(spec_owns(node0, key));
    lemma_owner(fleet, cb, i, key);
    lemma_land_node(fleet, cb, i, at, node2, send);
    lemma_all_answered(fleet, cb, i);
    lemma_fresh_op(fleet, cb, i, op);
    assert(w.op == op);
    assert(w.key == key);
    assert(w.job == flight.job);
    assert(w.now == flight.now);
    assert(w.caller == flight.caller);
    assert(w.etag == flight.etag);
    assert(w.writing);
    assert(w.decided == Some(spec_encode_body(next)));
    assert(w.born == born);
    assert(w.notify == notes);
    assert(w.reply == flight_reply(flight, reply));
    lemma_decision_same(w, flight, doc, node0.retry_timeout);
    lemma_reply_same(w, flight, reply);
    assert(decision(w, doc, node0.retry_timeout) == decision(flight, doc, node0.retry_timeout));
    assert(flight_reply(w, reply) == flight_reply(flight, reply));
    assert(job_keyed(w));
    assert(node2.documents == node0.documents);
    assert(loaded(node2, key) == doc);
    assert(cached_etag(node2, key) is None);
    // the node
    assert(flight_ok(node2));
    assert(cache_owned(node2));
    assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
        physical(store, k) == node2.flight.unwrap().decided
    } else {
        match #[trigger] spec_cached(node2, k) {
            Some(c) => cache_entry_ok(k, c, store),
            None => physical(store, k) is None,
        }
    }) by {
        assert(!applied_write(i, node2, store, k));
        assert(spec_owns(node0, k));
        assert(!applied_write(i, node0, store, k));
        assert(spec_cached(node2, k) == spec_cached(node0, k));
    };
    assert(node_ok(i, node2, store));
    // the traffic
    lemma_envelope_at(node_pid(i), send, 0);
    assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) || (
        node2.flight is Some && ca.network[k] == Envelope {
            sender: node_pid(i),
            recipient: CPid::Store,
            message: CMessage::StoreReq {
                op: node2.flight.unwrap().op,
                call: request_of(node2.flight.unwrap()),
            },
        }) by {
        assert(k == cb.network.len());
        assert(ca.network[k] == envelopes(node_pid(i), send)[0]);
    };
    lemma_traffic_ok(fleet, cb, ca, i, node2);
    assert(inv(fleet, ca)) by {
        assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
            if k != i {
                assert(node_at(ca, k) == node_at(cb, k));
            }
        };
    };
    // the store, read through the nodes
    assert(intended(node0, key) == next);
    assert(intended(node2, key) == next);
    assert(effective(fleet, cb, key) == next);
    assert(doc_rel(key, effective(fleet, ca, key), s));
    assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
        == intended(node0, other) by {
        assert(spec_cached(node2, other) == spec_cached(node0, other));
    };
    lemma_others_same(key, s);
    lemma_interpreted_update(fleet, cb, ca, i, key, s, s);
    // the occurrences
    assert(born_of(node0) == born);
    assert(born_of(node2) == born);
    assert(occurrences(node2) == occurrences(node0));
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(ab).pending.to_multiset().count(item) by {
        assert(owed_by(node2, item) == owed_by(node0, item));
        lemma_owed_update(fleet, cb, ca, i, item, 0);
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), ab.network) by {
        if k != i {
            assert(node_at(ca, k) == node_at(cb, k));
        } else {
            assert(flight_outputs_covered(node0, ab.network));
        }
    };
    lemma_extends_refl(ab.network);
    let sent = envelopes(node_pid(i), send);
    assert forall|k: int|
        #![trigger sent[k]]
        0 <= k < sent.len() implies carried_request(sent[k], ab.network) && carried_output(sent[k], ab.network) by {
        assert(k == 0);
    };
    lemma_append_keeps_coverage(cb.network, sent, ab.network, ab.network);
    assert(coupled(ca, ab));
    assert(related(fleet, ca, ab));
}

/// A store reply at a busy node.
pub proof fn lemma_store_reply(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    op: u64,
    outcome: StoreOutcome,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        event_valid(cb, node_pid(i), ProcessEvent::Receive { sender: CPid::Store, message: CMessage::StoreReply { op, outcome } }),
        node_at(cb, i).flight is Some,
        node_at(cb, i).next_op < u64::MAX,
        (node2, send) == spec_store_reply(node_at(cb, i), op, outcome),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let flight = node0.flight.unwrap();
    let key = flight.key;
    let store = store_at(fleet, cb);
    if flight.op != op {
        assert(node2 == node0);
        assert(send =~= Seq::<(CPid, CMessage)>::empty());
        lemma_same_work(fleet, config, cb, ab, i, at, node2, ca);
    } else {
        let wanted = Envelope {
            sender: CPid::Store,
            recipient: node_pid(i),
            message: CMessage::StoreReply { op, outcome },
        };
        let k = choose|k: int| 0 <= k < cb.network.len() && #[trigger] cb.network[k] == wanted;
        assert(store.seen.contains((node_pid(i), op)));
        assert(flight_op(node0) == Some(op));
        assert(outcome == outcome_of(flight));
        assert(flight_ok(node0));
        let doc0 = loaded(node0, key);
        let (next, reply, born, notes) = decision(flight, doc0, node0.retry_timeout);
        if !flight.writing {
            assert(outcome == StoreOutcome::Got(None));
            assert(flight.etag is None);
            assert(spec_cached(node0, key) is None);
            assert(doc0 == spec_empty_body(key));
            let rest = NodeV { flight: None, ..node0 };
            assert(FlightV { etag: None, ..flight } == flight);
            assert((node2, send) == spec_decide(rest, flight, doc0));
            lemma_decide(rest, flight, doc0);
            assert(held(rest, key) == doc0);
            if next == doc0 && born.len() == 0 {
                lemma_empty_is_empty(key);
                assert(spec_body_is_empty(next));
                assert(spec_keep(rest.documents, key, next, None) == spec_forget(rest.documents, key, 0));
                lemma_cached_from(node0.documents, key, 0);
                lemma_forget_absent(node0.documents, key, 0);
                assert(node2.documents == node0.documents);
                assert(node2.flight is None);
                assert(node2.pending == node0.pending);
                assert(born =~= Seq::<PendingV>::empty());
                assert(node2.pending == node0.pending + born);
                assert(loaded(node2, key) == doc0);
                assert(spec_cached(node2, key) is None);
                assert(!applied_write(i, node0, store, key));
                assert(physical(store, key) is None);
                assert forall|a: int, b: int| 0 <= a < b < node2.documents.len() implies #[trigger] node2.documents[a].key
                    != #[trigger] node2.documents[b].key by {
                    assert(cache_owned(node0));
                };
                assert forall|m: int| 0 <= m < node2.documents.len() implies #[trigger] node2.documents[m].key == key
                    || exists|n: int| 0 <= n < node0.documents.len() && #[trigger] node0.documents[n] == node2.documents[m] by {
                    assert(node0.documents[m] == node2.documents[m]);
                };
                lemma_flight_closed(fleet, config, cb, ab, i, at, node2, send, ca);
            } else {
                lemma_write_after_read(fleet, config, cb, ab, i, at, node2, send, ca);
            }
        } else {
            let decided = flight.decided.unwrap();
            assert(decided == spec_encode_body(next));
            let tag = spec_etag(decided);
            assert(outcome == StoreOutcome::Written(tag));
            assert((node2, send) == spec_commit(node0, flight, tag));
            lemma_string(spec_etag_chars(decided));
            let chars = spec_etag_chars(decided);
            assert(tag.0@ == chars);
            assert(node2.documents == spec_remember(node0.documents, key, decided, Some(chars), 0));
            assert(cache_owned(node0));
            lemma_remember(node0.documents, key, decided, Some(chars), 0);
            let entry = CachedV { key, body: decided, etag: Some(chars) };
            assert(spec_cached(node2, key) == Some(entry));
            axiom_decode_encode_body(next);
            assert(spec_read(key, decided) == next);
            assert(loaded(node2, key) == next);
            assert(applied_write(i, node0, store, key));
            assert(physical(store, key) == Some(decided));
            assert(cache_entry_ok(key, entry, store));
            assert(node2.pending == node0.pending + flight.born);
            assert(flight.born == born);
            assert(flight.reply == flight_reply(flight, reply));
            assert(flight.notify == notes);
            assert(send == reply_send(flight_reply(flight, reply)) + spec_notes(notes));
            lemma_flight_closed(fleet, config, cb, ab, i, at, node2, send, ca);
        }
    }
}

// ---------------------------------------------------------------------------
// The store
// ---------------------------------------------------------------------------

pub proof fn lemma_push_contains<A>(s: Seq<A>, x: A, y: A)
    ensures
        s.push(x).contains(y) == (s.contains(y) || y == x),
{
    let pushed = s.push(x);
    if pushed.contains(y) {
        let k = choose|k: int| 0 <= k < pushed.len() && pushed[k] == y;
        if k < s.len() {
            assert(s[k] == y);
        } else {
            assert(k == s.len());
        }
    }
    if s.contains(y) {
        let k = choose|k: int| 0 <= k < s.len() && s[k] == y;
        assert(pushed[k] == y);
    }
    if y == x {
        assert(pushed[s.len() as int] == x);
    }
}

/// The store's answer to the live flight's call: a read of an absent key,
/// or a write that lands.
pub proof fn lemma_store_answers(fleet: Fleet, world: World<CModel>, n: int)
    requires
        inv(fleet, world),
        0 <= n < fleet.nodes,
        node_at(world, n).flight is Some,
        !store_at(fleet, world).seen.contains((node_pid(n), node_at(world, n).flight.unwrap().op)),
    ensures
        ({
            let flight = node_at(world, n).flight.unwrap();
            let store = store_at(fleet, world);
            let (next, outcome) = spec_apply(store, request_of(flight));
            &&& outcome == outcome_of(flight)
            &&& entries_distinct(next)
            &&& next.seen == store.seen
            &&& if flight.writing {
                &&& physical(next, flight.key) == flight.decided
                &&& forall|other: Seq<char>| other != flight.key ==> #[trigger] physical(next, other) == physical(store, other)
            } else {
                next == store
            }
        }),
{
    let node = node_at(world, n);
    let flight = node.flight.unwrap();
    let key = flight.key;
    let store = store_at(fleet, world);
    assert(node_ok(n, node, store));
    assert(flight_ok(node));
    assert(spec_owns(node, key));
    assert(!applied_write(n, node, store, key));
    lemma_string(key);
    if !flight.writing {
        assert(spec_cached(node, key) is None);
        assert(physical(store, key) is None);
        assert(spec_find(store.entries, key, 0) is None);
        assert(request_of(flight) == StoreCall::Get { key: spec_string(key) });
    } else {
        let decided = flight.decided.unwrap();
        lemma_bytes(decided);
        match flight.etag {
            None => {
                assert(request_of(flight) == StoreCall::PutIfNoneMatch {
                    key: spec_string(key),
                    body: spec_bytes(decided),
                });
                match spec_cached(node, key) {
                    Some(c) => {
                        assert(c.etag is None);
                        assert(physical(store, key) is None);
                    },
                    None => {
                        assert(physical(store, key) is None);
                    },
                }
                assert(spec_find(store.entries, key, 0) is None);
                let entry = EntryV { key, body: decided, version: 1 };
                lemma_put(store, entry);
            },
            Some(chars) => {
                assert(request_of(flight) == StoreCall::PutIfMatch {
                    key: spec_string(key),
                    body: spec_bytes(decided),
                    etag: Etag(spec_string(chars)),
                });
                let c = spec_cached(node, key).unwrap();
                assert(c.etag == Some(chars));
                assert(physical(store, key) == Some(c.body));
                assert(chars == spec_etag_chars(c.body));
                let idx = spec_find(store.entries, key, 0).unwrap();
                assert(store.entries[idx].body == c.body);
                assert(spec_etag(c.body) == Etag(spec_string(chars)));
                assert(spec_etag(store.entries[idx].body) == Etag(spec_string(chars)));
                let entry = EntryV { key, body: decided, version: crate::store::spec_bump(store.entries[idx].version) };
                let (next, outcome) = spec_apply(store, request_of(flight));
                assert(next == (CStore { entries: spec_put(store.entries, entry), ..store }));
                assert(outcome == StoreOutcome::Written(spec_etag(decided)));
                lemma_put(store, entry);
                assert(physical(next, key) == Some(decided));
                assert(entries_distinct(next));
            },
        }
    }
}

/// A store step.
pub proof fn lemma_store(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    at: Time,
    event: ProcessEvent<CPid, CMessage>,
    j: int,
    ca: World<CModel>,
)
    requires
        related(fleet, cb, ab),
        cb.now <= at,
        event_valid(cb, CPid::Store, event),
        0 <= j < spec_store(store_at(fleet, cb), event).len(),
        ca == land(cb, fleet.nodes as int, CPid::Store, at, spec_store(store_at(fleet, cb), event)[j]),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_empty_matches(config, ab);
    lemma_extends_refl(ab.network);
    let store = store_at(fleet, cb);
    let slot = fleet.nodes as int;
    match event {
        ProcessEvent::Receive { sender, message: CMessage::StoreReq { op, call } } => {
            let wanted = Envelope { sender, recipient: CPid::Store, message: CMessage::StoreReq { op, call } };
            let k = choose|k: int| 0 <= k < cb.network.len() && #[trigger] cb.network[k] == wanted;
            assert(sender is Node);
            let n = sender->Node_0 as int;
            assert(0 <= n < fleet.nodes);
            assert(sender == node_pid(n));
            let node = node_at(cb, n);
            if store.seen.contains((sender, op)) {
                assert(spec_store(store, event) == spec_one(LocalV::Store(store), Seq::empty()));
                assert(j == 0);
                assert(ca == land(cb, slot, CPid::Store, at, store_result(store, Seq::empty())));
                lemma_land_store(fleet, cb, at, store, Seq::empty());
                assert(cb.process[slot] == (CPid::Store, LocalV::Store(store)));
                assert(ca.process =~= cb.process);
                assert(envelopes(CPid::Store, Seq::<(CPid, CMessage)>::empty()) =~= Seq::<Envelope<CPid, CMessage>>::empty());
                assert(ca.network =~= cb.network);
                lemma_invariant_grow(fleet, cb, ca);
                lemma_carry(fleet, cb, ab, ca, ab);
            } else {
                assert(flight_op(node) == Some(op));
                let flight = node.flight.unwrap();
                assert(flight.op == op);
                assert(call == request_of(flight));
                let key = flight.key;
                assert(node_ok(n, node, store));
                assert(flight_ok(node));
                assert(spec_owns(node, key));
                let (next, outcome) = spec_apply(store, call);
                let store2 = CStore { seen: store.seen.push((sender, op)), ..next };
                let send = seq![(sender, CMessage::StoreReply { op, outcome })];
                assert(spec_store(store, event) == spec_one(LocalV::Store(store2), send));
                assert(j == 0);
                assert(ca == land(cb, slot, CPid::Store, at, store_result(store2, send)));
                lemma_land_store(fleet, cb, at, store2, send);
                lemma_store_answers(fleet, cb, n);
                assert(outcome == outcome_of(flight));
                assert(entries_distinct(store2));
                assert forall|other: Seq<char>| #[trigger] physical(store2, other) == physical(next, other) by {};
                assert forall|x: (CPid, u64)| #[trigger] store2.seen.contains(x) == (store.seen.contains(x) || x == (sender, op)) by {
                    lemma_push_contains(store.seen, (sender, op), x);
                };
                // every node still agrees with the store
                assert forall|m: int| 0 <= m < fleet.nodes implies #[trigger] node_ok(m, node_at(ca, m), store2) by {
                    let nm = node_at(cb, m);
                    assert(node_at(ca, m) == nm);
                    assert(node_ok(m, nm, store));
                    assert forall|key2: Seq<char>| spec_owns(nm, key2) implies (if applied_write(m, nm, store2, key2) {
                        physical(store2, key2) == nm.flight.unwrap().decided
                    } else {
                        match #[trigger] spec_cached(nm, key2) {
                            Some(c) => cache_entry_ok(key2, c, store2),
                            None => physical(store2, key2) is None,
                        }
                    }) by {
                        if m == n && key2 == key {
                            if flight.writing {
                                assert(applied_write(n, node, store2, key));
                                assert(physical(store2, key) == flight.decided);
                            } else {
                                assert(!applied_write(n, node, store2, key));
                                assert(!applied_write(n, node, store, key));
                                assert(physical(store2, key) == physical(store, key));
                            }
                        } else {
                            if m != n {
                                lemma_owner(fleet, cb, m, key2);
                                lemma_owner(fleet, cb, n, key);
                                assert(key2 != key);
                                assert(applied_write(m, nm, store2, key2) == applied_write(m, nm, store, key2));
                            } else {
                                assert(key2 != key);
                                assert(applied_write(m, nm, store2, key2) == applied_write(m, nm, store, key2));
                            }
                            assert(physical(store2, key2) == physical(store, key2));
                            match spec_cached(nm, key2) {
                                Some(c) => {
                                    assert(cache_entry_ok(key2, c, store2) == cache_entry_ok(key2, c, store));
                                },
                                None => {},
                            }
                        }
                    };
                };
                // the traffic
                lemma_envelope_at(CPid::Store, send, 0);
                let sent = envelopes(CPid::Store, send);
                assert(sent[0] == Envelope { sender: CPid::Store, recipient: sender, message: CMessage::StoreReply { op, outcome } });
                assert forall|m: int| 0 <= m < ca.network.len() implies match (#[trigger] ca.network[m]).message {
                    CMessage::StoreReq { op: op2, call: call2 } => {
                        let env = ca.network[m];
                        &&& env.recipient == CPid::Store
                        &&& env.sender is Node
                        &&& {
                            let q = env.sender->Node_0 as int;
                            let nq = node_at(ca, q);
                            &&& 0 <= q < fleet.nodes
                            &&& op2 < nq.next_op
                            &&& (flight_op(nq) == Some(op2) ==> call2 == request_of(nq.flight.unwrap()))
                            &&& (!store_at(fleet, ca).seen.contains((env.sender, op2)) ==> flight_op(nq) == Some(op2))
                        }
                    },
                    _ => true,
                } by {
                    if m < cb.network.len() {
                        assert(ca.network[m] == cb.network[m]);
                        match cb.network[m].message {
                            CMessage::StoreReq { op: op2, call: call2 } => {
                                let q = cb.network[m].sender->Node_0 as int;
                                assert(node_at(ca, q) == node_at(cb, q));
                                if !store2.seen.contains((cb.network[m].sender, op2)) {
                                    assert(!store.seen.contains((cb.network[m].sender, op2)));
                                }
                            },
                            _ => {},
                        }
                    } else {
                        assert(ca.network[m] == sent[0]);
                    }
                };
                assert forall|m: int| 0 <= m < ca.network.len() implies match (#[trigger] ca.network[m]).message {
                    CMessage::StoreReply { op: op2, outcome: outcome2 } => {
                        let env = ca.network[m];
                        &&& env.sender == CPid::Store
                        &&& env.recipient is Node
                        &&& {
                            let q = env.recipient->Node_0 as int;
                            let nq = node_at(ca, q);
                            &&& 0 <= q < fleet.nodes
                            &&& store_at(fleet, ca).seen.contains((env.recipient, op2))
                            &&& (flight_op(nq) == Some(op2) ==> outcome2 == outcome_of(nq.flight.unwrap()))
                        }
                    },
                    _ => true,
                } by {
                    if m < cb.network.len() {
                        assert(ca.network[m] == cb.network[m]);
                        match cb.network[m].message {
                            CMessage::StoreReply { op: op2, outcome: outcome2 } => {
                                let q = cb.network[m].recipient->Node_0 as int;
                                assert(node_at(ca, q) == node_at(cb, q));
                                assert(store.seen.contains((cb.network[m].recipient, op2)));
                            },
                            _ => {},
                        }
                    } else {
                        assert(ca.network[m] == sent[0]);
                        assert(store2.seen.contains((sender, op)));
                        assert(node_at(ca, n) == node);
                    }
                };
                assert forall|pair: (CPid, u64)| #[trigger] store2.seen.contains(pair) implies requested(ca, pair.0, pair.1) by {
                    if store.seen.contains(pair) {
                        lemma_requested_grows(cb, ca, pair.0, pair.1);
                    } else {
                        assert(pair == (sender, op));
                        assert(ca.network[k] == wanted);
                    }
                };
                assert(inv(fleet, ca));
                // the rest reads the nodes, which did not move
                assert forall|key2: Seq<char>| #[trigger] doc_rel(key2, effective(fleet, ca, key2), astate(ab).store) by {
                    assert(effective(fleet, ca, key2) == effective(fleet, cb, key2));
                };
                assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(ab).pending.to_multiset().count(item) by {
                    lemma_owed_same(fleet, cb, ca, item, 0);
                };
                assert forall|m: int| 0 <= m < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, m), ab.network) by {
                    assert(node_at(ca, m) == node_at(cb, m));
                };
                assert forall|m: int|
                    #![trigger sent[m]]
                    0 <= m < sent.len() implies carried_request(sent[m], ab.network) && carried_output(sent[m], ab.network) by {
                    assert(m == 0);
                };
                lemma_append_keeps_coverage(cb.network, sent, ab.network, ab.network);
                assert(coupled(ca, ab));
                assert(related(fleet, ca, ab));
            }
        },
        _ => {
            assert(spec_store(store, event).len() == 0);
            assert(false);
        },
    }
}

// ---------------------------------------------------------------------------
// A node step
// ---------------------------------------------------------------------------

pub proof fn lemma_node(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    event: ProcessEvent<CPid, CMessage>,
    j: int,
    ca: World<CModel>,
) -> (aa: World<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        event_valid(cb, node_pid(i), event),
        0 <= j < spec_node_step(node_at(cb, i), at, event).len(),
        ca == land(cb, i, node_pid(i), at, spec_node_step(node_at(cb, i), at, event)[j]),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    let node = node_at(cb, i);
    let results = spec_node_step(node, at, event);
    match event {
        ProcessEvent::Timeout => {
            match node.wake {
                Some(w) => {
                    if w <= at as nat && node.flight is None && node.next_op < u64::MAX {
                        let (next, send) = spec_timeout(node, at);
                        let node2 = NodeV {
                            logic: crate::model::LogicV { clock: at as nat, last_wake: None, ..node.logic },
                            wake: crate::node::spec_wake(next),
                            ..next
                        };
                        assert(results == spec_one(LocalV::Node(node2), send));
                        assert(j == 0);
                        assert(results[0] == node_result(node2, send));
                        let cw = land(cb, i, node_pid(i), at, node_result(next, send));
                        let aa = lemma_timeout(fleet, config, cb, ab, i, at, next, send, cw);
                        lemma_reshell(fleet, config, cb, aa, i, at, next, node2, send, ca);
                        aa
                    } else if w <= at as nat {
                        assert(results == spec_one(LocalV::Node(node), Seq::empty()));
                        assert(j == 0);
                        assert(results[0] == node_result(node, Seq::empty()));
                        lemma_same_work(fleet, config, cb, ab, i, at, node, ca);
                        ab
                    } else {
                        assert(results.len() == 0);
                        assert(false);
                        ab
                    }
                },
                None => {
                    assert(results.len() == 0);
                    assert(false);
                    ab
                },
            }
        },
        ProcessEvent::Receive { sender: CPid::Outside, message: CMessage::Request(call) } => {
            if node.flight is Some || node.next_op == u64::MAX {
                assert(results == spec_one(LocalV::Node(node), Seq::empty()));
                assert(j == 0);
                assert(results[0] == node_result(node, Seq::empty()));
                lemma_same_work(fleet, config, cb, ab, i, at, node, ca);
                ab
            } else {
                let (next, send) = spec_request(node, at, call);
                let node2 = NodeV {
                    logic: crate::model::spec_clock(node.logic, at),
                    next_request: (node.next_request + 1) as u64,
                    wake: crate::node::spec_wake(next),
                    ..next
                };
                assert(results == spec_one(LocalV::Node(node2), send));
                assert(j == 0);
                assert(results[0] == node_result(node2, send));
                let cw = land(cb, i, node_pid(i), at, node_result(next, send));
                let aa = lemma_request(fleet, config, cb, ab, i, at, call, next, send, cw);
                lemma_reshell(fleet, config, cb, aa, i, at, next, node2, send, ca);
                aa
            }
        },
        ProcessEvent::Receive { sender: CPid::Store, message: CMessage::StoreReply { op, outcome } } => {
            if node.flight is None || node.next_op == u64::MAX {
                assert(results == spec_one(LocalV::Node(node), Seq::empty()));
                assert(j == 0);
                assert(results[0] == node_result(node, Seq::empty()));
                lemma_same_work(fleet, config, cb, ab, i, at, node, ca);
                ab
            } else {
                let (next, send) = spec_store_reply(node, op, outcome);
                let node2 = NodeV {
                    logic: crate::model::spec_clock(node.logic, at),
                    wake: crate::node::spec_wake(next),
                    ..next
                };
                assert(results == spec_one(LocalV::Node(node2), send));
                assert(j == 0);
                assert(results[0] == node_result(node2, send));
                let cw = land(cb, i, node_pid(i), at, node_result(next, send));
                lemma_store_reply(fleet, config, cb, ab, i, at, op, outcome, next, send, cw);
                lemma_reshell(fleet, config, cb, ab, i, at, next, node2, send, ca);
                ab
            }
        },
        ProcessEvent::Receive { sender: CPid::Outside, message: CMessage::Stop } => {
            let node2 = NodeV {
                logic: crate::model::LogicV { clock: at as nat, loops: false, stopping: true, ..node.logic },
                ..node
            };
            assert(results == spec_one(LocalV::Node(node2), Seq::empty()));
            assert(j == 0);
            assert(results[0] == node_result(node2, Seq::empty()));
            lemma_same_work(fleet, config, cb, ab, i, at, node2, ca);
            ab
        },
        _ => {
            assert(results.len() == 0);
            assert(false);
            ab
        },
    }
}

// ---------------------------------------------------------------------------
// The three labels
// ---------------------------------------------------------------------------

pub proof fn lemma_input(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    recipient: CPid,
    at: Time,
    message: CMessage,
    ca: World<CModel>,
) -> (aa: World<AModel>)
    requires
        related(fleet, cb, ab),
        step(concrete_model(), fleet, cb, Label::Input { recipient, at, message }, ca),
    ensures
        matches(abstract_model(), config, ab, concrete_model().spec_observe(Label::Input { recipient, at, message }), aa),
        related(fleet, ca, aa),
{
    reveal(step);
    let label = Label::<CPid, CMessage>::Input { recipient, at, message };
    assert(cb.now <= at);
    assert(concrete_model().spec_injectable(fleet, message));
    assert(ca == inject(cb, CPid::Outside, recipient, at, message));
    let added = Envelope { sender: CPid::Outside, recipient, message };
    assert(ca.process == cb.process);
    assert(ca.network == cb.network.push(added));
    assert(ca.now == at);
    lemma_extends_push(cb.network, added);
    assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) by {
        assert(ca.network[k] == added);
    };
    lemma_invariant_grow(fleet, cb, ca);
    match message {
        CMessage::Request(call) => {
            let amessage = AMessage::Request(call);
            let alabel = Label::<APid, AMessage>::Input { recipient: APid::Service, at, message: amessage };
            let aa = inject(ab, APid::Outside, APid::Service, at, amessage);
            lemma_single_present(ab);
            assert(abstract_model().spec_injectable(config, amessage));
            assert(step(abstract_model(), config, ab, alabel, aa));
            let visible = seq![BoundaryEvent::Input { at, call }];
            assert(abstract_model().spec_observe(alabel) =~= visible);
            assert(concrete_model().spec_observe(label) =~= visible);
            lemma_matched_step(config, ab, alabel, aa, visible);
            lemma_matches_same_visible(config, ab, visible, concrete_model().spec_observe(label), aa);
            let aenv = Envelope { sender: APid::Outside, recipient: APid::Service, message: amessage };
            assert(aa.network == ab.network.push(aenv));
            lemma_extends_push(ab.network, aenv);
            lemma_pushed_request(ab.network, call);
            assert(carried_request(added, aa.network));
            assert(carried_output(added, aa.network));
            lemma_push_keeps_coverage(cb.network, added, ab.network, aa.network);
            assert(aa.process == ab.process);
            lemma_carry(fleet, cb, ab, ca, aa);
            aa
        },
        _ => {
            lemma_empty_matches(config, ab);
            assert(concrete_model().spec_observe(label) =~= Seq::<BoundaryEvent>::empty());
            lemma_matches_same_visible(config, ab, Seq::<BoundaryEvent>::empty(), concrete_model().spec_observe(label), ab);
            lemma_extends_refl(ab.network);
            assert(carried_request(added, ab.network));
            assert(carried_output(added, ab.network));
            lemma_push_keeps_coverage(cb.network, added, ab.network, ab.network);
            lemma_carry(fleet, cb, ab, ca, ab);
            ab
        },
    }
}

pub proof fn lemma_outside(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    sender: CPid,
    at: Time,
    message: CMessage,
    ca: World<CModel>,
) -> (aa: World<AModel>)
    requires
        related(fleet, cb, ab),
        step(concrete_model(), fleet, cb, Label::Outside { sender, at, message }, ca),
    ensures
        matches(abstract_model(), config, ab, concrete_model().spec_observe(Label::Outside { sender, at, message }), aa),
        related(fleet, ca, aa),
{
    reveal(step);
    let label = Label::<CPid, CMessage>::Outside { sender, at, message };
    assert(cb.now <= at);
    assert(ca == observe_outside(cb, at));
    assert(ca.process == cb.process);
    assert(ca.network == cb.network);
    assert(ca.now == at);
    lemma_extends_refl(cb.network);
    lemma_invariant_grow(fleet, cb, ca);
    let wanted = Envelope { sender, recipient: CPid::Outside, message };
    let k = choose|k: int| 0 <= k < cb.network.len() && #[trigger] cb.network[k] == wanted;
    match message {
        CMessage::Output(output) => {
            assert(carried_output(cb.network[k], ab.network));
            assert(service_output(ab.network, output));
            let m = choose|m: int|
                #![trigger ab.network[m]]
                0 <= m < ab.network.len() && ab.network[m] == Envelope {
                    sender: APid::Service,
                    recipient: APid::Outside,
                    message: AMessage::Output(output),
                };
            let alabel = Label::<APid, AMessage>::Outside { sender: APid::Service, at, message: AMessage::Output(output) };
            let aa = observe_outside(ab, at);
            assert(step(abstract_model(), config, ab, alabel, aa));
            let visible = seq![BoundaryEvent::Output { at, output }];
            assert(abstract_model().spec_observe(alabel) =~= visible);
            assert(concrete_model().spec_observe(label) =~= visible);
            lemma_matched_step(config, ab, alabel, aa, visible);
            lemma_matches_same_visible(config, ab, visible, concrete_model().spec_observe(label), aa);
            assert(aa.process == ab.process);
            assert(aa.network == ab.network);
            lemma_extends_refl(ab.network);
            lemma_carry(fleet, cb, ab, ca, aa);
            aa
        },
        _ => {
            lemma_empty_matches(config, ab);
            assert(concrete_model().spec_observe(label) =~= Seq::<BoundaryEvent>::empty());
            lemma_matches_same_visible(config, ab, Seq::<BoundaryEvent>::empty(), concrete_model().spec_observe(label), ab);
            lemma_extends_refl(ab.network);
            lemma_carry(fleet, cb, ab, ca, ab);
            ab
        },
    }
}

pub proof fn lemma_process(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    process: CPid,
    at: Time,
    event: ProcessEvent<CPid, CMessage>,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
) -> (aa: World<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        step(concrete_model(), fleet, cb, Label::Process { process, at, event, send }, ca),
    ensures
        matches(abstract_model(), config, ab, concrete_model().spec_observe(Label::Process { process, at, event, send }), aa),
        related(fleet, ca, aa),
{
    reveal(step);
    let label = Label::<CPid, CMessage>::Process { process, at, event, send };
    assert(cb.now <= at);
    assert(event_valid(cb, process, event));
    let i = choose|i: int|
        #![trigger cb.process[i]]
        exists|j: int|
            #![trigger concrete_model().spec_on_event(fleet, process, cb.process[i].1, at, event)[j]]
            {
                &&& 0 <= i < cb.process.len()
                &&& cb.process[i].0 == process
                &&& {
                    let outcomes = concrete_model().spec_on_event(fleet, process, cb.process[i].1, at, event);
                    &&& 0 <= j < outcomes.len()
                    &&& outcomes[j].send == send
                    &&& ca == land(cb, i, process, at, outcomes[j])
                }
            };
    let j = choose|j: int|
        #![trigger concrete_model().spec_on_event(fleet, process, cb.process[i].1, at, event)[j]]
        {
            &&& 0 <= i < cb.process.len()
            &&& cb.process[i].0 == process
            &&& {
                let outcomes = concrete_model().spec_on_event(fleet, process, cb.process[i].1, at, event);
                &&& 0 <= j < outcomes.len()
                &&& outcomes[j].send == send
                &&& ca == land(cb, i, process, at, outcomes[j])
            }
        };
    let outcomes = concrete_model().spec_on_event(fleet, process, cb.process[i].1, at, event);
    assert(outcomes == spec_step(fleet, process, cb.process[i].1, at, event));
    assert(concrete_model().spec_observe(label) =~= Seq::<BoundaryEvent>::empty());
    assert(shaped(fleet, cb));
    if i < fleet.nodes {
        assert(process == node_pid(i));
        let node = node_at(cb, i);
        assert(cb.process[i].1 == LocalV::Node(node));
        assert(outcomes == spec_node_step(node, at, event));
        let aa = lemma_node(fleet, config, cb, ab, i, at, event, j, ca);
        lemma_matches_same_visible(config, ab, Seq::<BoundaryEvent>::empty(), concrete_model().spec_observe(label), aa);
        aa
    } else {
        assert(i == fleet.nodes);
        assert(process == CPid::Store);
        let store = store_at(fleet, cb);
        assert(cb.process[i].1 == LocalV::Store(store));
        assert(outcomes == spec_store(store, event));
        lemma_store(fleet, config, cb, ab, at, event, j, ca);
        lemma_matches_same_visible(config, ab, Seq::<BoundaryEvent>::empty(), concrete_model().spec_observe(label), ab);
        ab
    }
}

/// One concrete step, matched.
pub proof fn lemma_step(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    label: Label<CPid, CMessage>,
    ca: World<CModel>,
    ab: World<AModel>,
) -> (aa: World<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        step(concrete_model(), fleet, cb, label, ca),
    ensures
        matches(abstract_model(), config, ab, concrete_model().spec_observe(label), aa),
        related(fleet, ca, aa),
{
    match label {
        Label::Input { recipient, at, message } => lemma_input(fleet, config, cb, ab, recipient, at, message, ca),
        Label::Process { process, at, event, send } => lemma_process(
            fleet,
            config,
            cb,
            ab,
            process,
            at,
            event,
            send,
            ca,
        ),
        Label::Outside { sender, at, message } => lemma_outside(fleet, config, cb, ab, sender, at, message, ca),
    }
}

// ---------------------------------------------------------------------------
// The initial worlds
// ---------------------------------------------------------------------------

pub proof fn lemma_owed_zero(fleet: Fleet, world: World<CModel>, item: Sched<InternalV>, k: int)
    requires
        forall|i: int| 0 <= i < fleet.nodes ==> #[trigger] occurrences(node_at(world, i)).len() == 0,
    ensures
        owed(fleet, world, item, k) == 0,
    decreases fleet.nodes - k,
{
    if k < 0 || k >= fleet.nodes {
    } else {
        lemma_owed_zero(fleet, world, item, k + 1);
        assert(items(occurrences(node_at(world, k))) =~= Seq::<Sched<InternalV>>::empty());
        assert(Seq::<Sched<InternalV>>::empty().to_multiset() =~= Multiset::<Sched<InternalV>>::empty());
    }
}

/// The empty document reads as the empty store under every key.
pub proof fn lemma_empty_reads(key: Seq<char>)
    ensures
        doc_rel(key, spec_empty_body(key), empty_store()),
{
    let s = empty_store();
    if crate::store::spec_starts(key, seq!['s', '/']) {
        assert(spec_empty_body(key) == DocumentBodyV::Schedule(None::<echod_types::Schedule>));
        assert(!s.schedules.contains_key(key.skip(2)));
    } else {
        let map = Map::<Seq<char>, crate::node::ObjV>::empty();
        assert(spec_empty_body(key) == DocumentBodyV::Workflow(map));
        assert(map.dom() =~= Set::<Seq<char>>::empty());
        assert(Set::<Seq<char>>::empty().len() == 0);
        if crate::store::spec_starts(key, crate::interpret::origin_prefix()) {
            let o = key.skip(2);
            assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) == o implies {
                &&& s.promises.contains_key(id) == map.contains_key(id)
                &&& (map.contains_key(id) ==> crate::interpret::object_rel(
                    map[id],
                    s.promises[id],
                    crate::interpret::abstract_task(s, id),
                ))
                &&& (!map.contains_key(id) ==> !s.tasks.contains_key(id))
            } by {
                assert(!s.promises.contains_key(id));
                assert(!s.tasks.contains_key(id));
                assert(!map.contains_key(id));
            };
        }
    }
}

pub proof fn lemma_initial(fleet: Fleet, config: ServerConfig)
    ensures
        related(fleet, initial(concrete_model(), fleet), initial(abstract_model(), config)),
{
    let cw = initial(concrete_model(), fleet);
    let aw = initial(abstract_model(), config);
    assert(cw.process == spec_world(fleet));
    assert(cw.network =~= Seq::<Envelope<CPid, CMessage>>::empty());
    assert(cw.now == 0);
    assert(aw.process == seq![(APid::Service, StateV { store: empty_store(), pending: Seq::empty() })]);
    assert(aw.network =~= Seq::<Envelope<APid, AMessage>>::empty());
    assert(single(aw));
    assert(astate(aw) == StateV { store: empty_store(), pending: Seq::empty() });
    assert(empty_store().promises.dom() =~= Set::<Seq<char>>::empty());
    assert(empty_store().tasks.dom() =~= Set::<Seq<char>>::empty());
    assert(empty_store().schedules.dom() =~= Set::<Seq<char>>::empty());
    assert(finite_store(empty_store()));
    // shape
    lemma_spec_nodes(fleet, 0);
    let nodes = spec_nodes(fleet, 0);
    let store = CStore { entries: Seq::empty(), appendable: fleet.appendable, seen: Seq::empty() };
    let tail = seq![(CPid::Store, LocalV::Store(store))];
    assert(cw.process == nodes + tail);
    assert(cw.process.len() == fleet.nodes + 1);
    assert forall|i: int| 0 <= i < fleet.nodes implies #[trigger] cw.process[i] == (
        node_pid(i),
        LocalV::Node(initial_node(fleet, i as u64)),
    ) by {
        assert(cw.process[i] == nodes[i]);
    };
    assert(cw.process[fleet.nodes as int] == tail[0]);
    assert(shaped(fleet, cw));
    assert(store_at(fleet, cw) == store);
    // the facts
    assert(entries_distinct(store));
    assert forall|i: int| 0 <= i < fleet.nodes implies #[trigger] node_ok(i, node_at(cw, i), store) by {
        let node = node_at(cw, i);
        assert(node == initial_node(fleet, i as u64));
        assert(node.flight is None);
        assert(node.documents.len() == 0);
        assert(cache_owned(node));
        assert forall|key: Seq<char>| spec_owns(node, key) implies (if applied_write(i, node, store, key) {
            physical(store, key) == node.flight.unwrap().decided
        } else {
            match #[trigger] spec_cached(node, key) {
                Some(c) => cache_entry_ok(key, c, store),
                None => physical(store, key) is None,
            }
        }) by {
            assert(spec_cached(node, key) is None);
            assert(physical(store, key) is None);
        };
    };
    assert(requests_ok(fleet, cw));
    assert(replies_ok(fleet, cw));
    assert forall|pair: (CPid, u64)| #[trigger] store.seen.contains(pair) implies requested(cw, pair.0, pair.1) by {
        assert(false);
    };
    assert(inv(fleet, cw));
    // the store, read through the nodes
    assert forall|key: Seq<char>| #[trigger] doc_rel(key, effective(fleet, cw, key), empty_store()) by {
        if fleet.nodes == 0 {
        } else {
            let o = owner(fleet, key);
            let node = node_at(cw, o);
            assert(node.flight is None);
            assert(spec_cached(node, key) is None);
            assert(effective(fleet, cw, key) == spec_empty_body(key));
        }
        lemma_empty_reads(key);
    };
    // nothing owed
    assert forall|i: int| 0 <= i < fleet.nodes implies #[trigger] occurrences(node_at(cw, i)).len() == 0 by {
        let node = node_at(cw, i);
        assert(born_of(node) =~= Seq::<PendingV>::empty());
        assert(occurrences(node) =~= Seq::<PendingV>::empty());
    };
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, cw, item, 0) <= astate(aw).pending.to_multiset().count(item) by {
        lemma_owed_zero(fleet, cw, item, 0);
    };
    assert forall|i: int| 0 <= i < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(cw, i), aw.network) by {
        assert(node_at(cw, i).flight is None);
    };
    assert(requests_covered(cw.network, aw.network));
    assert(outputs_covered(cw.network, aw.network));
    assert(coupled(cw, aw));
    assert(related(fleet, cw, aw));
}

/// A timeout at an idle node.
pub proof fn lemma_timeout(
    fleet: Fleet,
    config: ServerConfig,
    cb: World<CModel>,
    ab: World<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: World<CModel>,
) -> (aa: World<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        (node2, send) == spec_timeout(node_at(cb, i), at),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    let node0 = node_at(cb, i);
    if node0.pending.len() > 0 {
        let p = node0.pending[0];
        let node1 = NodeV { pending: node0.pending.skip(1), ..node0 };
        let key = crate::node::spec_origin_key(origin(p.promise));
        if !spec_owns(node1, key) {
            assert(node2 == node1);
            assert(send =~= Seq::<(CPid, CMessage)>::empty());
            lemma_pop_silent(fleet, config, cb, ab, i, at, node2, ca);
            ab
        } else {
            lemma_occurrence_begin(fleet, config, cb, ab, i, at, node2, send, ca)
        }
    } else {
        match spec_earliest_key(node0, at) {
            Some(key) => lemma_due_begin(fleet, config, cb, ab, i, at, key, node2, send, ca),
            None => {
                assert(node2 == node0);
                assert(send =~= Seq::<(CPid, CMessage)>::empty());
                lemma_same_work(fleet, config, cb, ab, i, at, node2, ca);
                ab
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The theorem
// ---------------------------------------------------------------------------

/// Every concrete step is matched: the forward simulation.
pub proof fn lemma_simulation(fleet: Fleet, config: ServerConfig)
    requires
        config == abstract_config(fleet),
        agreement(config),
    ensures
        simulation(concrete_model(), fleet, abstract_model(), config, link(fleet)),
{
    let relation = link(fleet);
    assert forall|cb: World<CModel>, label: Label<CPid, CMessage>, ca: World<CModel>, ab: World<AModel>|
        #![trigger relation(cb, ab), step(concrete_model(), fleet, cb, label, ca)]
        relation(cb, ab) && step(concrete_model(), fleet, cb, label, ca) implies exists|aa: World<AModel>|
            #[trigger] matches(abstract_model(), config, ab, concrete_model().spec_observe(label), aa) && relation(ca, aa) by {
        lemma_link(fleet, cb, ab);
        let aa = lemma_step(fleet, config, cb, label, ca, ab);
        lemma_link(fleet, ca, aa);
        assert(matches(abstract_model(), config, ab, concrete_model().spec_observe(label), aa) && relation(ca, aa));
    };
}

/// Trace inclusion: every boundary trace of the concrete world is one of
/// the abstract world, at the abstract configuration the fleet implements:
/// the same retry timeout. The handlers, the due step, and the occurrence
/// agree by `timers::lemma_agreement`.
pub proof fn lemma_refines(concrete_config: Fleet)
    ensures
        refines(concrete_model(), concrete_config, abstract_model(), abstract_config(concrete_config)),
{
    let fleet = concrete_config;
    let config = abstract_config(fleet);
    crate::timers::lemma_agreement(config);
    lemma_initial(fleet, config);
    lemma_link(fleet, initial(concrete_model(), fleet), initial(abstract_model(), config));
    lemma_simulation(fleet, config);
    concrete_refines_abstract(concrete_model(), fleet, abstract_model(), config, link(fleet));
}

} // verus!
