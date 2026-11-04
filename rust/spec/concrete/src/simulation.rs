//! Forward simulation from the concrete Rover model to the abstract one.
//!
//! The relation is the coupling an injected call and an observed output need.
//! The abstract clock is at most the concrete clock, the service is still a
//! process, every client request on the concrete network is a request to the
//! service on the abstract network, and every output addressed to the outside
//! on the concrete network is an output from the service on the abstract
//! network.
//!
//! An injected `Request` is one abstract input of that call. `Stop`, and an
//! outside step whose message is not an output, are empty abstract executions.
//! An observed output is one abstract outside step of that output. A process
//! label observes nothing on both models. A process step that sends no output
//! to the outside appends nothing the relation mentions, so the abstract
//! execution is empty. A process step whose send is one 503 for a call still
//! on the network is one abstract shed: the service state stays and the same
//! response is appended. An empty-task heartbeat is one abstract serve of
//! status 200, and the service state stays. Every other process step that
//! sends an output to the outside is [`output_simulation`]: some finite
//! abstract execution has an empty boundary projection and leaves the worlds
//! related. [`lemma_refines`] is trace inclusion once that holds.
//!
//! The node's documents and the service store are what a proof of
//! [`output_simulation`] identifies. Inject and outside leave both process
//! lists in place, so an agreement that reads only those lists survives them.
//! A store round trip changes a process list; its abstract counterpart is part
//! of that same proof. Cargo erases these bodies; a Verus run is what checks them.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::model::{Fleet, Message as CMessage, Model as CModel, Pid as CPid};
#[cfg(verus_keep_ghost)]
use echod_abstract::model::Pid as APid;
#[cfg(verus_keep_ghost)]
use echod_abstract::protocol::Message as AMessage;
#[cfg(verus_keep_ghost)]
use echod_abstract::{BoundaryEvent, Call, Model as AModel, Output, ServerConfig};
#[cfg(verus_keep_ghost)]
use echod_types::Response;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::refinement::{
    concrete_refines_abstract, end, matches, project, refines, simulation,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{
    before, envelopes, inject, initial, is_process, land, legal, observe_outside, step, Execution,
    Label, World, WorldV,
};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::{Envelope, ProcessEvent};
#[cfg(verus_keep_ghost)]
use echod_rover::Time;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

pub open spec fn cmodel() -> CModel {
    CModel
}

pub open spec fn amodel() -> AModel {
    AModel
}

/// `related`, packaged as the function the generic theorem takes.
pub open spec fn link() -> spec_fn(World<CModel>, World<AModel>) -> bool {
    |concrete: World<CModel>, abstract_world: World<AModel>| related(concrete, abstract_world)
}

pub proof fn lemma_link(concrete: World<CModel>, abstract_world: World<AModel>)
    ensures
        link()(concrete, abstract_world) == related(concrete, abstract_world),
{
    assert(link()(concrete, abstract_world) == related(concrete, abstract_world));
}

// ---------------------------------------------------------------------------
// Relation
// ---------------------------------------------------------------------------

/// The service still occupies a slot. Abstract inputs are addressed there.
pub open spec fn service_present(world: World<AModel>) -> bool {
    is_process(amodel(), world, APid::Service)
}

/// `call` was injected at the service.
pub open spec fn service_request(network: Seq<Envelope<APid, AMessage>>, call: Call) -> bool {
    exists|j: int|
        #![trigger network[j]]
        0 <= j < network.len() && network[j] == Envelope {
            sender: APid::Outside,
            recipient: APid::Service,
            message: AMessage::Request(call),
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

/// `later` still contains every envelope of `earlier`, in front.
pub open spec fn extends(
    later: Seq<Envelope<APid, AMessage>>,
    earlier: Seq<Envelope<APid, AMessage>>,
) -> bool {
    earlier.len() <= later.len() && forall|j: int|
        #![trigger later[j]]
        0 <= j < earlier.len() ==> later[j] == earlier[j]
}

/// Abstract clock, service slot, client requests, and client outputs.
pub open spec fn related(concrete: World<CModel>, abstract_world: World<AModel>) -> bool {
    abstract_world.now <= concrete.now && service_present(abstract_world)
        && requests_covered(concrete.network, abstract_world.network)
        && outputs_covered(concrete.network, abstract_world.network)
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

/// `entry` delivers an output to the outside.
pub open spec fn client_output_entry(entry: (CPid, CMessage)) -> bool {
    entry.0 == CPid::Outside && match entry.1 {
        CMessage::Output(_) => true,
        _ => false,
    }
}

pub open spec fn sends_client_output(send: Seq<(CPid, CMessage)>) -> bool {
    exists|k: int|
        #![trigger send[k]]
        0 <= k < send.len() && client_output_entry(send[k])
}

/// `call` is still a client request on `network`. The network only grows.
pub open spec fn request_carried(network: Seq<Envelope<CPid, CMessage>>, call: Call) -> bool {
    exists|i: int|
        #![trigger network[i]]
        0 <= i < network.len() && network[i].sender == CPid::Outside && network[i].message
            == CMessage::Request(call)
}

/// One output to the outside, the response to `call`. The client string is
/// compared by its characters, which is what `spec_string` agrees on.
pub open spec fn is_reply(send: Seq<(CPid, CMessage)>, call: Call, response: Response) -> bool {
    send.len() == 1 && send[0].0 == CPid::Outside && match send[0].1 {
        CMessage::Output(Output::Response { client, id, response: got }) => {
            client@ == call.client@ && id == call.id && got == response
        },
        _ => false,
    }
}

pub open spec fn empty_heartbeat(call: Call) -> bool {
    match call.request {
        echod_types::Request::TaskHeartbeat(q) => q.tasks@.len() == 0,
        _ => false,
    }
}

/// A client reply this file matches directly. Either the send is the 503
/// shed of a call that is still on the network, or it is the 200 of an
/// empty-task heartbeat of such a call.
pub open spec fn client_reply(
    network: Seq<Envelope<CPid, CMessage>>,
    send: Seq<(CPid, CMessage)>,
) -> bool {
    exists|call: Call|
        #![trigger request_carried(network, call)]
        request_carried(network, call) && (
            is_reply(send, call, echod_abstract::model::spec_unavailable(call.request))
                || (empty_heartbeat(call) && is_reply(
                    send,
                    call,
                    Response::Status(echod_types::StatusRes { status: 200 }),
                ))
        )
}

/// A concrete process step that emits a client output, and is not one of the
/// replies [`client_reply`] already accounts for, has a matching abstract
/// execution. The boundary projection is empty because a process label
/// observes nothing. The execution restores [`related`], so each new output
/// envelope is on the abstract network afterwards.
pub open spec fn output_simulation(fleet: Fleet, config: ServerConfig) -> bool {
    forall|before_c: World<CModel>,
        process: CPid,
        at: Time,
        event: ProcessEvent<CPid, CMessage>,
        send: Seq<(CPid, CMessage)>,
        after_c: World<CModel>,
        before_a: World<AModel>|
        #![trigger
            related(before_c, before_a),
            step(
                cmodel(),
                fleet,
                before_c,
                Label::Process { process, at, event, send },
                after_c,
            )]
        related(before_c, before_a) && step(
            cmodel(),
            fleet,
            before_c,
            Label::Process { process, at, event, send },
            after_c,
        ) && sends_client_output(send) && !client_reply(before_c.network, send) ==> exists|
            after_a: World<AModel>,
        |
            #[trigger] matches(
                amodel(),
                config,
                before_a,
                Seq::<BoundaryEvent>::empty(),
                after_a,
            ) && related(after_c, after_a)
}

/// Every concrete process step, emitting or silent, has an abstract execution
/// with an empty boundary projection.
pub open spec fn process_simulation(fleet: Fleet, config: ServerConfig) -> bool {
    forall|before_c: World<CModel>,
        label: Label<CPid, CMessage>,
        after_c: World<CModel>,
        before_a: World<AModel>|
        #![trigger related(before_c, before_a), step(cmodel(), fleet, before_c, label, after_c)]
        related(before_c, before_a) && step(cmodel(), fleet, before_c, label, after_c)
            && process_label(label) ==> exists|after_a: World<AModel>|
            #[trigger] matches(
                amodel(),
                config,
                before_a,
                Seq::<BoundaryEvent>::empty(),
                after_a,
            ) && related(after_c, after_a)
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
    vstd::seq::lemma_seq_empty::<A>();
    vstd::seq::lemma_seq_push_len(Seq::<A>::empty(), x);
    vstd::seq::lemma_seq_push_len(s, x);
    vstd::seq::lemma_seq_add_len(s, suffix);
    assert(suffix.len() == 1);
    assert forall|i: int| 0 <= i < s.push(x).len() implies s.push(x)[i] == s.add(suffix)[i] by {
        if i < s.len() {
            vstd::seq::lemma_seq_push_index_different(s, x, i);
            vstd::seq::lemma_seq_add_index1(s, suffix, i);
        } else {
            assert(i == s.len());
            vstd::seq::lemma_seq_push_index_same(s, x, i);
            vstd::seq::lemma_seq_add_index2(s, suffix, i);
            vstd::seq::lemma_seq_push_index_same(Seq::<A>::empty(), x, 0);
            assert(suffix[0] == x);
            assert(s.add(suffix)[i] == x);
        }
    };
    assert(s.push(x) =~= s.add(suffix));
}

pub proof fn lemma_extends_refl(network: Seq<Envelope<APid, AMessage>>)
    ensures
        extends(network, network),
{
    assert(network.len() <= network.len());
    assert forall|j: int| 0 <= j < network.len() implies #[trigger] network[j] == network[j] by {
    };
}

pub proof fn lemma_extends_push(
    earlier: Seq<Envelope<APid, AMessage>>,
    added: Envelope<APid, AMessage>,
)
    ensures
        extends(earlier.push(added), earlier),
{
    let later = earlier.push(added);
    vstd::seq::lemma_seq_push_len(earlier, added);
    assert(earlier.len() <= later.len());
    assert forall|j: int| 0 <= j < earlier.len() implies #[trigger] later[j] == earlier[j] by {
        vstd::seq::lemma_seq_push_index_different(earlier, added, j);
    };
}

pub proof fn lemma_service_follows(before: World<AModel>, after: World<AModel>)
    requires
        service_present(before),
        after.process == before.process,
    ensures
        service_present(after),
{
    let i = choose|i: int|
        0 <= i < before.process.len() && #[trigger] before.process[i].0 == APid::Service;
    assert(after.process.len() == before.process.len());
    assert(after.process[i].0 == APid::Service);
    assert(amodel().spec_outside() == APid::Outside);
    assert(APid::Service != amodel().spec_outside());
    assert(is_process(amodel(), after, APid::Service));
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
                assert(0 <= j < earlier.len());
                assert(later[j] == earlier[j]);
                assert(service_request(later, call));
            }
        },
        _ => {},
    }
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
                let j = choose|j: int|
                    #![trigger earlier[j]]
                    0 <= j < earlier.len() && earlier[j] == Envelope {
                        sender: APid::Service,
                        recipient: APid::Outside,
                        message: AMessage::Output(output),
                    };
                assert(0 <= j < earlier.len());
                assert(later[j] == earlier[j]);
                assert(service_output(later, output));
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
    vstd::seq::lemma_seq_add_len(before, suffix);
    assert forall|i: int| 0 <= i < combined.len() implies carried_request(
        #[trigger] combined[i],
        later,
    ) by {
        if i < before.len() {
            vstd::seq::lemma_seq_add_index1(before, suffix, i);
            assert(combined[i] == before[i]);
            assert(carried_request(before[i], earlier));
            lemma_request_monotone(before[i], earlier, later);
        } else {
            vstd::seq::lemma_seq_add_index2(before, suffix, i);
            let k = i - before.len();
            assert(0 <= k < suffix.len());
            assert(combined[i] == suffix[k]);
            assert(carried_request(suffix[k], later));
        }
    };
    assert forall|i: int| 0 <= i < combined.len() implies carried_output(
        #[trigger] combined[i],
        later,
    ) by {
        if i < before.len() {
            vstd::seq::lemma_seq_add_index1(before, suffix, i);
            assert(combined[i] == before[i]);
            assert(carried_output(before[i], earlier));
            lemma_output_monotone(before[i], earlier, later);
        } else {
            vstd::seq::lemma_seq_add_index2(before, suffix, i);
            let k = i - before.len();
            assert(0 <= k < suffix.len());
            assert(combined[i] == suffix[k]);
            assert(carried_output(suffix[k], later));
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
    vstd::seq::lemma_seq_empty::<Envelope<CPid, CMessage>>();
    vstd::seq::lemma_seq_push_len(Seq::<Envelope<CPid, CMessage>>::empty(), added);
    assert(suffix.len() == 1);
    assert forall|k: int| 0 <= k < suffix.len() implies carried_request(
        #[trigger] suffix[k],
        later,
    ) && carried_output(suffix[k], later) by {
        assert(k == 0);
        vstd::seq::lemma_seq_push_index_same(Seq::<Envelope<CPid, CMessage>>::empty(), added, 0);
        assert(suffix[0] == added);
    };
    lemma_append_keeps_coverage(before, suffix, earlier, later);
    assert(before.push(added) =~= before.add(suffix));
    assert(requests_covered(before.push(added), later));
    assert(outputs_covered(before.push(added), later));
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
    vstd::seq::lemma_seq_push_len(network, added);
    vstd::seq::lemma_seq_push_index_same(network, added, j);
    assert(later[j] == added);
    assert(0 <= j < later.len());
    assert(service_request(later, call));
}

pub proof fn lemma_envelope_at(sender: CPid, send: Seq<(CPid, CMessage)>, k: int)
    requires
        0 <= k < envelopes(sender, send).len(),
    ensures
        envelopes(sender, send).len() == send.len(),
        envelopes(sender, send)[k] == sent(sender, send[k]),
{
    let suffix = envelopes(sender, send);
    let g = |i: int| sent(sender, send[i]);
    assert(suffix == Seq::new(send.len(), g));
    vstd::seq::lemma_seq_new_len(send.len(), g);
    assert(0 <= k < send.len());
    vstd::seq::lemma_seq_new_index(send.len(), g, k);
    assert(suffix[k] == g(k));
    assert(g(k) == sent(sender, send[k]));
}

// ---------------------------------------------------------------------------
// One abstract step, and the empty execution
// ---------------------------------------------------------------------------

pub proof fn lemma_empty_matches(config: ServerConfig, before: World<AModel>)
    ensures
        matches(amodel(), config, before, Seq::<BoundaryEvent>::empty(), before),
{
    let execution = Seq::<(Label<APid, AMessage>, World<AModel>)>::empty();
    vstd::seq::lemma_seq_empty::<(Label<APid, AMessage>, World<AModel>)>();
    assert(execution.len() == 0);
    assert forall|i: int| 0 <= i < execution.len() implies #[trigger] step(
        amodel(),
        config,
        before::<AModel>(before, execution, i),
        execution[i].0,
        execution[i].1,
    ) by {
        assert(0 <= i < 0);
        assert(false);
    };
    assert(legal(amodel(), config, before, execution));
    assert(project::<AModel>(amodel(), execution) =~= Seq::<BoundaryEvent>::empty());
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
        step(amodel(), config, before, label, after),
        amodel().spec_observe(label) == visible,
    ensures
        matches(amodel(), config, before, visible, after),
{
    let pair = (label, after);
    let execution = Seq::<(Label<APid, AMessage>, World<AModel>)>::empty().push(pair);
    vstd::seq::lemma_seq_empty::<(Label<APid, AMessage>, World<AModel>)>();
    vstd::seq::lemma_seq_push_len(Seq::<(Label<APid, AMessage>, World<AModel>)>::empty(), pair);
    assert(execution.len() == 1);
    vstd::seq::lemma_seq_push_index_same(
        Seq::<(Label<APid, AMessage>, World<AModel>)>::empty(),
        pair,
        0,
    );
    assert(execution[0] == pair);
    assert(execution.last() == pair);
    assert(execution.drop_last() == execution.subrange(0, 0));
    vstd::seq::lemma_seq_subrange_len(execution, 0, 0);
    assert(execution.drop_last().len() == 0);
    assert(execution.drop_last() =~= Seq::<(Label<APid, AMessage>, World<AModel>)>::empty());
    assert(project::<AModel>(amodel(), execution.drop_last()) =~= Seq::<BoundaryEvent>::empty());
    assert(execution.last().0 == label);
    let empty = Seq::<BoundaryEvent>::empty();
    vstd::seq::lemma_seq_empty::<BoundaryEvent>();
    vstd::seq::lemma_seq_add_len(empty, visible);
    assert forall|i: int| 0 <= i < visible.len() implies empty.add(visible)[i] == visible[i] by {
        vstd::seq::lemma_seq_add_index2(empty, visible, i);
    };
    assert(empty.add(visible) =~= visible);
    assert(project::<AModel>(amodel(), execution) == project::<AModel>(
        amodel(),
        execution.drop_last(),
    ) + amodel().spec_observe(execution.last().0));
    assert(project::<AModel>(amodel(), execution) =~= visible);
    assert forall|i: int| 0 <= i < execution.len() implies #[trigger] step(
        amodel(),
        config,
        before::<AModel>(before, execution, i),
        execution[i].0,
        execution[i].1,
    ) by {
        assert(i == 0);
        assert(before::<AModel>(before, execution, 0) == before);
        assert(execution[0].0 == label);
        assert(execution[0].1 == after);
    };
    assert(legal(amodel(), config, before, execution));
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
        matches(amodel(), config, before, visible, after),
        visible == same,
    ensures
        matches(amodel(), config, before, same, after),
{
    let execution = choose|execution: Execution<AModel>|
        #![trigger legal(amodel(), config, before, execution)]
        legal(amodel(), config, before, execution) && project::<AModel>(amodel(), execution)
            == visible && end::<AModel>(before, execution) == after;
    assert(project::<AModel>(amodel(), execution) == same);
    assert(legal(amodel(), config, before, execution));
    assert(end::<AModel>(before, execution) == after);
}

// ---------------------------------------------------------------------------
// Initial world
// ---------------------------------------------------------------------------

pub proof fn lemma_initial_related(fleet: Fleet, config: ServerConfig)
    ensures
        related(initial(cmodel(), fleet), initial(amodel(), config)),
{
    reveal(initial);
    let concrete = initial(cmodel(), fleet);
    let abstract_world = initial(amodel(), config);
    assert(concrete.network =~= Seq::<Envelope<CPid, CMessage>>::empty());
    assert(abstract_world.network =~= Seq::<Envelope<APid, AMessage>>::empty());
    assert(concrete.now == 0);
    assert(abstract_world.now == 0);
    assert(abstract_world.process == amodel().spec_initial(config));
    assert(amodel().spec_initial(config) =~= seq![(
        APid::Service,
        echod_abstract::model::StateV {
            store: echod_abstract::model::empty_store(),
            pending: Seq::empty(),
        },
    )]);
    assert(abstract_world.process.len() == 1);
    assert(abstract_world.process[0].0 == APid::Service);
    assert(amodel().spec_outside() == APid::Outside);
    assert(APid::Service != amodel().spec_outside());
    assert(service_present(abstract_world));
    vstd::seq::lemma_seq_empty::<Envelope<CPid, CMessage>>();
    assert(concrete.network.len() == 0);
    assert(requests_covered(concrete.network, abstract_world.network));
    assert(outputs_covered(concrete.network, abstract_world.network));
}

// ---------------------------------------------------------------------------
// Inject
// ---------------------------------------------------------------------------

pub proof fn lemma_input(
    fleet: Fleet,
    config: ServerConfig,
    before_c: World<CModel>,
    recipient: CPid,
    at: Time,
    message: CMessage,
    after_c: World<CModel>,
    before_a: World<AModel>,
)
    requires
        related(before_c, before_a),
        step(
            cmodel(),
            fleet,
            before_c,
            Label::Input { recipient, at, message },
            after_c,
        ),
    ensures
        exists|after_a: World<AModel>|
            #[trigger] matches(
                amodel(),
                config,
                before_a,
                cmodel().spec_observe(Label::Input { recipient, at, message }),
                after_a,
            ) && related(after_c, after_a),
{
    reveal(step);
    let label = Label::Input { recipient, at, message };
    assert(before_c.now <= at);
    assert(before_a.now <= before_c.now);
    assert(before_a.now <= at);
    assert(cmodel().spec_outside() == CPid::Outside);
    assert(after_c == inject(before_c, cmodel().spec_outside(), recipient, at, message));
    lemma_inject_keeps_process(
        before_c,
        cmodel().spec_outside(),
        recipient,
        at,
        message,
    );
    let added = Envelope { sender: CPid::Outside, recipient, message };
    assert(after_c.network == before_c.network.push(added));
    assert(after_c.now == at);
    assert(after_c.process == before_c.process);
    assert(cmodel().spec_injectable(fleet, message));
    match message {
        CMessage::Request(call) => {
            assert(amodel().spec_outside() == APid::Outside);
            assert(amodel().spec_injectable(config, AMessage::Request(call)));
            assert(service_present(before_a));
            let alabel = Label::Input {
                recipient: APid::Service,
                at,
                message: AMessage::Request(call),
            };
            let after_a = inject(
                before_a,
                amodel().spec_outside(),
                APid::Service,
                at,
                AMessage::Request(call),
            );
            assert(step(amodel(), config, before_a, alabel, after_a));
            let visible = seq![BoundaryEvent::Input { at, call }];
            assert(amodel().spec_observe(alabel) == visible);
            assert(cmodel().spec_observe(label) == visible);
            lemma_matched_step(config, before_a, alabel, after_a, visible);
            lemma_matches_same_visible(
                config,
                before_a,
                visible,
                cmodel().spec_observe(label),
                after_a,
            );
            let abstract_added = Envelope {
                sender: APid::Outside,
                recipient: APid::Service,
                message: AMessage::Request(call),
            };
            assert(amodel().spec_outside() == APid::Outside);
            assert(after_a.network == before_a.network.push(abstract_added));
            lemma_inject_keeps_process(
                before_a,
                amodel().spec_outside(),
                APid::Service,
                at,
                AMessage::Request(call),
            );
            assert(after_a.process == before_a.process);
            assert(after_a.now == at);
            lemma_service_follows(before_a, after_a);
            lemma_extends_push(before_a.network, abstract_added);
            lemma_pushed_request(before_a.network, call);
            assert(service_request(after_a.network, call));
            assert(added.sender == CPid::Outside);
            assert(added.message == CMessage::Request(call));
            assert(carried_request(added, after_a.network));
            assert(carried_output(added, after_a.network));
            lemma_push_keeps_coverage(
                before_c.network,
                added,
                before_a.network,
                after_a.network,
            );
            assert(after_a.now <= after_c.now);
            assert(related(after_c, after_a));
            assert(exists|finish: World<AModel>|
                #[trigger] matches(amodel(), config, before_a, cmodel().spec_observe(label), finish)
                    && related(after_c, finish));
        },
        CMessage::Stop => {
            assert(cmodel().spec_observe(label) =~= Seq::<BoundaryEvent>::empty());
            lemma_empty_matches(config, before_a);
            lemma_matches_same_visible(
                config,
                before_a,
                Seq::<BoundaryEvent>::empty(),
                cmodel().spec_observe(label),
                before_a,
            );
            lemma_extends_refl(before_a.network);
            assert(carried_request(added, before_a.network));
            assert(carried_output(added, before_a.network));
            lemma_push_keeps_coverage(
                before_c.network,
                added,
                before_a.network,
                before_a.network,
            );
            assert(service_present(before_a));
            assert(before_a.now <= after_c.now);
            assert(related(after_c, before_a));
            assert(exists|finish: World<AModel>|
                #[trigger] matches(amodel(), config, before_a, cmodel().spec_observe(label), finish)
                    && related(after_c, finish));
        },
        CMessage::Output(_) => {
            assert(cmodel().spec_injectable(fleet, message) == false);
            assert(false);
        },
        CMessage::StoreReq { .. } => {
            assert(cmodel().spec_injectable(fleet, message) == false);
            assert(false);
        },
        CMessage::StoreReply { .. } => {
            assert(cmodel().spec_injectable(fleet, message) == false);
            assert(false);
        },
    }
}

// ---------------------------------------------------------------------------
// Outside
// ---------------------------------------------------------------------------

pub proof fn lemma_outside(
    fleet: Fleet,
    config: ServerConfig,
    before_c: World<CModel>,
    sender: CPid,
    at: Time,
    message: CMessage,
    after_c: World<CModel>,
    before_a: World<AModel>,
)
    requires
        related(before_c, before_a),
        step(
            cmodel(),
            fleet,
            before_c,
            Label::Outside { sender, at, message },
            after_c,
        ),
    ensures
        exists|after_a: World<AModel>|
            #[trigger] matches(
                amodel(),
                config,
                before_a,
                cmodel().spec_observe(Label::Outside { sender, at, message }),
                after_a,
            ) && related(after_c, after_a),
{
    reveal(step);
    let label = Label::Outside { sender, at, message };
    assert(before_c.now <= at);
    assert(before_a.now <= before_c.now);
    assert(before_a.now <= at);
    assert(after_c == observe_outside(before_c, at));
    lemma_observe_keeps_world(before_c, at);
    assert(after_c.network == before_c.network);
    assert(after_c.process == before_c.process);
    assert(after_c.now == at);
    assert(cmodel().spec_outside() == CPid::Outside);
    match message {
        CMessage::Output(output) => {
            let i = choose|i: int|
                0 <= i < before_c.network.len() && #[trigger] before_c.network[i] == Envelope {
                    sender,
                    recipient: cmodel().spec_outside(),
                    message: CMessage::Output(output),
                };
            assert(outputs_covered(before_c.network, before_a.network));
            assert(before_c.network[i].recipient == CPid::Outside);
            assert(before_c.network[i].message == CMessage::Output(output));
            assert(carried_output(before_c.network[i], before_a.network));
            let j = choose|j: int|
                #![trigger before_a.network[j]]
                0 <= j < before_a.network.len() && before_a.network[j] == Envelope {
                    sender: APid::Service,
                    recipient: APid::Outside,
                    message: AMessage::Output(output),
                };
            assert(amodel().spec_outside() == APid::Outside);
            assert(before_a.network[j] == Envelope {
                sender: APid::Service,
                recipient: amodel().spec_outside(),
                message: AMessage::Output(output),
            });
            let alabel = Label::Outside {
                sender: APid::Service,
                at,
                message: AMessage::Output(output),
            };
            let after_a = observe_outside(before_a, at);
            assert(step(amodel(), config, before_a, alabel, after_a));
            let visible = seq![BoundaryEvent::Output { at, output }];
            assert(amodel().spec_observe(alabel) == visible);
            assert(cmodel().spec_observe(label) == visible);
            lemma_matched_step(config, before_a, alabel, after_a, visible);
            lemma_matches_same_visible(
                config,
                before_a,
                visible,
                cmodel().spec_observe(label),
                after_a,
            );
            lemma_observe_keeps_world(before_a, at);
            assert(after_a.process == before_a.process);
            assert(after_a.network == before_a.network);
            assert(after_a.now == at);
            lemma_service_follows(before_a, after_a);
            assert(requests_covered(after_c.network, after_a.network));
            assert(outputs_covered(after_c.network, after_a.network));
            assert(after_a.now <= after_c.now);
            assert(related(after_c, after_a));
            assert(exists|finish: World<AModel>|
                #[trigger] matches(amodel(), config, before_a, cmodel().spec_observe(label), finish)
                    && related(after_c, finish));
        },
        CMessage::Request(_) | CMessage::StoreReq { .. } | CMessage::StoreReply { .. }
            | CMessage::Stop => {
            assert(cmodel().spec_observe(label) =~= Seq::<BoundaryEvent>::empty());
            lemma_empty_matches(config, before_a);
            lemma_matches_same_visible(
                config,
                before_a,
                Seq::<BoundaryEvent>::empty(),
                cmodel().spec_observe(label),
                before_a,
            );
            assert(requests_covered(after_c.network, before_a.network));
            assert(outputs_covered(after_c.network, before_a.network));
            assert(service_present(before_a));
            assert(before_a.now <= after_c.now);
            assert(related(after_c, before_a));
            assert(exists|finish: World<AModel>|
                #[trigger] matches(amodel(), config, before_a, cmodel().spec_observe(label), finish)
                    && related(after_c, finish));
        },
    }
}

// ---------------------------------------------------------------------------
// Process steps that do not emit a client output
// ---------------------------------------------------------------------------

/// A process step whose send list has no output to the outside. The abstract
/// world stays: the new envelopes are store traffic or messages between
/// processes, and a process label observes nothing.
pub proof fn lemma_silent_process(
    fleet: Fleet,
    config: ServerConfig,
    before_c: World<CModel>,
    process: CPid,
    at: Time,
    event: ProcessEvent<CPid, CMessage>,
    send: Seq<(CPid, CMessage)>,
    after_c: World<CModel>,
    before_a: World<AModel>,
)
    requires
        related(before_c, before_a),
        step(
            cmodel(),
            fleet,
            before_c,
            Label::Process { process, at, event, send },
            after_c,
        ),
        !sends_client_output(send),
    ensures
        matches(amodel(), config, before_a, Seq::<BoundaryEvent>::empty(), before_a),
        related(after_c, before_a),
{
    reveal(step);
    let i = choose|i: int|
        #![trigger before_c.process[i]]
        exists|j: int|
            #![trigger cmodel().spec_on_event(
                fleet,
                process,
                before_c.process[i].1,
                at,
                event,
            )[j]]
            {
                &&& 0 <= i < before_c.process.len()
                &&& before_c.process[i].0 == process
                &&& {
                    let outcomes = cmodel().spec_on_event(
                        fleet,
                        process,
                        before_c.process[i].1,
                        at,
                        event,
                    );
                    &&& 0 <= j < outcomes.len()
                    &&& outcomes[j].send == send
                    &&& after_c == land(before_c, i, process, at, outcomes[j])
                }
            };
    let j = choose|j: int|
        #![trigger cmodel().spec_on_event(fleet, process, before_c.process[i].1, at, event)[j]]
        {
            &&& 0 <= i < before_c.process.len()
            &&& before_c.process[i].0 == process
            &&& {
                let outcomes = cmodel().spec_on_event(
                    fleet,
                    process,
                    before_c.process[i].1,
                    at,
                    event,
                );
                &&& 0 <= j < outcomes.len()
                &&& outcomes[j].send == send
                &&& after_c == land(before_c, i, process, at, outcomes[j])
            }
        };
    let outcome = cmodel().spec_on_event(fleet, process, before_c.process[i].1, at, event)[j];
    assert(outcome.send == send);
    assert(after_c == land(before_c, i, process, at, outcome));
    let suffix = envelopes(process, send);
    assert(after_c.network == before_c.network + suffix);
    assert(before_c.network + suffix == before_c.network.add(suffix));
    assert(after_c.now == at);
    assert(is_process(cmodel(), before_c, process));
    assert(cmodel().spec_outside() == CPid::Outside);
    assert(process != CPid::Outside);
    assert(before_c.now <= at);
    assert(before_a.now <= before_c.now);
    assert(before_a.now <= after_c.now);
    assert forall|k: int| 0 <= k < suffix.len() implies carried_request(
        #[trigger] suffix[k],
        before_a.network,
    ) && carried_output(suffix[k], before_a.network) by {
        lemma_envelope_at(process, send, k);
        assert(suffix[k] == sent(process, send[k]));
        assert(suffix[k].sender == process);
        assert(suffix[k].sender != CPid::Outside);
        assert(!client_output_entry(send[k]));
        assert(carried_request(suffix[k], before_a.network));
        assert(carried_output(suffix[k], before_a.network));
    };
    lemma_extends_refl(before_a.network);
    lemma_append_keeps_coverage(
        before_c.network,
        suffix,
        before_a.network,
        before_a.network,
    );
    assert(service_present(before_a));
    assert(related(after_c, before_a));
    lemma_empty_matches(config, before_a);
}

/// One abstract process step that answers `call` with `response` and leaves
/// the service state in place. The concrete send is that same response.
pub proof fn lemma_one_abstract_reply(
    config: ServerConfig,
    before_c: World<CModel>,
    process: CPid,
    at: Time,
    event: ProcessEvent<CPid, CMessage>,
    send: Seq<(CPid, CMessage)>,
    after_c: World<CModel>,
    before_a: World<AModel>,
    call: Call,
    response: Response,
    slot: int,
    index: int,
)
    requires
        related(before_c, before_a),
        step(
            cmodel(),
            fleet,
            before_c,
            Label::Process { process, at, event, send },
            after_c,
        ),
        request_carried(before_c.network, call),
        is_reply(send, call, response),
        0 <= slot < before_a.process.len(),
        before_a.process[slot].0 == APid::Service,
        ({
            let state = before_a.process[slot].1;
            let a_event = ProcessEvent::Receive {
                sender: APid::Outside,
                message: AMessage::Request(call),
            };
            let outcomes = amodel().spec_on_event(config, APid::Service, state, at, a_event);
            &&& 0 <= index < outcomes.len()
            &&& outcomes[index].state == state
            &&& outcomes[index].send == echod_abstract::model::spec_send(
                call,
                response,
                Seq::<echod_abstract::view::DispatchV>::empty(),
            )
        }),
    ensures
        exists|after_a: World<AModel>|
            #[trigger] matches(
                amodel(),
                config,
                before_a,
                Seq::<BoundaryEvent>::empty(),
                after_a,
            ) && related(after_c, after_a),
{
    reveal(step);
    let state = before_a.process[slot].1;
    let a_event = ProcessEvent::Receive {
        sender: APid::Outside,
        message: AMessage::Request(call),
    };
    let outcomes = amodel().spec_on_event(config, APid::Service, state, at, a_event);
    let outcome = outcomes[index];
    let output = Output::Response { client: call.client, id: call.id, response };
    assert(outcome.state == state);
    assert(outcome.send == echod_abstract::model::spec_send(
        call,
        response,
        Seq::<echod_abstract::view::DispatchV>::empty(),
    ));
    assert(outcome.send =~= seq![(APid::Outside, AMessage::Output(output))]);
    assert(before_c.now <= at);
    assert(before_a.now <= before_c.now);
    assert(before_a.now <= at);
    assert(amodel().spec_outside() == APid::Outside);
    assert(APid::Service != APid::Outside);
    assert(service_present(before_a));
    assert(is_process(amodel(), before_a, APid::Service));
    let carried = choose|i: int|
        #![trigger before_c.network[i]]
        0 <= i < before_c.network.len() && before_c.network[i].sender == CPid::Outside
            && before_c.network[i].message == CMessage::Request(call);
    assert(requests_covered(before_c.network, before_a.network));
    assert(carried_request(before_c.network[carried], before_a.network));
    assert(service_request(before_a.network, call));
    assert(event_valid(before_a, APid::Service, a_event));
    let a_label = Label::Process {
        process: APid::Service,
        at,
        event: a_event,
        send: outcome.send,
    };
    let after_a = land(before_a, slot, APid::Service, at, outcome);
    assert(step(amodel(), config, before_a, a_label, after_a));
    assert(amodel().spec_observe(a_label) =~= Seq::<BoundaryEvent>::empty());
    lemma_matched_step(
        config,
        before_a,
        a_label,
        after_a,
        Seq::<BoundaryEvent>::empty(),
    );
    assert(before_a.process[slot] == (APid::Service, state));
    assert(after_a.process == before_a.process.update(slot, before_a.process[slot]));
    assert forall|k: int| 0 <= k < before_a.process.len() implies #[trigger] after_a.process[k]
        == before_a.process[k] by {
        if k == slot {
            vstd::seq::lemma_seq_update_same(before_a.process, slot, before_a.process[slot]);
        } else {
            vstd::seq::lemma_seq_update_different(
                before_a.process,
                k,
                slot,
                before_a.process[slot],
            );
        }
    };
    assert(after_a.process =~= before_a.process);
    lemma_service_follows(before_a, after_a);
    let a_suffix = envelopes(APid::Service, outcome.send);
    assert(after_a.network == before_a.network + a_suffix);
    assert(a_suffix.len() == 1);
    assert(a_suffix[0] == Envelope {
        sender: APid::Service,
        recipient: APid::Outside,
        message: AMessage::Output(output),
    });
    let j = before_a.network.len() as int;
    vstd::seq::lemma_seq_add_len(before_a.network, a_suffix);
    vstd::seq::lemma_seq_add_index2(before_a.network, a_suffix, j);
    assert(after_a.network[j] == a_suffix[0]);
    assert(service_output(after_a.network, output));
    assert forall|k: int| 0 <= k < before_a.network.len() implies #[trigger] after_a.network[k]
        == before_a.network[k] by {
        vstd::seq::lemma_seq_add_index1(before_a.network, a_suffix, k);
    };
    assert(extends(after_a.network, before_a.network));
    let c_i = choose|i: int|
        #![trigger before_c.process[i]]
        exists|j: int|
            #![trigger cmodel().spec_on_event(fleet, process, before_c.process[i].1, at, event)[j]]
            {
                &&& 0 <= i < before_c.process.len()
                &&& before_c.process[i].0 == process
                &&& {
                    let found = cmodel().spec_on_event(
                        fleet,
                        process,
                        before_c.process[i].1,
                        at,
                        event,
                    );
                    &&& 0 <= j < found.len()
                    &&& found[j].send == send
                    &&& after_c == land(before_c, i, process, at, found[j])
                }
            };
    let c_j = choose|j: int|
        #![trigger cmodel().spec_on_event(fleet, process, before_c.process[c_i].1, at, event)[j]]
        {
            &&& 0 <= c_i < before_c.process.len()
            &&& before_c.process[c_i].0 == process
            &&& {
                let found = cmodel().spec_on_event(
                    fleet,
                    process,
                    before_c.process[c_i].1,
                    at,
                    event,
                );
                &&& 0 <= j < found.len()
                &&& found[j].send == send
                &&& after_c == land(before_c, c_i, process, at, found[j])
            }
        };
    let c_outcome = cmodel().spec_on_event(fleet, process, before_c.process[c_i].1, at, event)[c_j];
    assert(after_c == land(before_c, c_i, process, at, c_outcome));
    let c_suffix = envelopes(process, send);
    assert(after_c.network == before_c.network + c_suffix);
    assert(c_suffix.len() == 1);
    let (client_seen, id_seen, got) = match send[0].1 {
        CMessage::Output(Output::Response { client, id, response: got }) => (client, id, got),
        _ => (call.client, call.id, response),
    };
    echod_abstract::trusted::axiom_string_ext(client_seen, call.client);
    let concrete_output = Output::Response { client: client_seen, id: id_seen, response: got };
    assert(concrete_output == output);
    assert(c_suffix[0] == sent(process, send[0]));
    assert forall|k: int| 0 <= k < c_suffix.len() implies carried_request(
        #[trigger] c_suffix[k],
        after_a.network,
    ) && carried_output(c_suffix[k], after_a.network) by {
        assert(c_suffix[0].message == CMessage::Output(output));
        assert(c_suffix[0].recipient == CPid::Outside);
        assert(service_output(after_a.network, output));
        assert(carried_output(c_suffix[0], after_a.network));
        assert(carried_request(c_suffix[0], after_a.network));
    };
    lemma_append_keeps_coverage(before_c.network, c_suffix, before_a.network, after_a.network);
    assert(after_a.now == at);
    assert(after_c.now == at);
    assert(before_a.now <= after_c.now);
    assert(related(after_c, after_a));
}

/// A 503 for a call still on the network is one abstract shed. An empty-task
/// heartbeat answered 200 is one abstract serve. Either way the service state
/// stays and the boundary projection is empty.
pub proof fn lemma_client_replies(
    fleet: Fleet,
    config: ServerConfig,
    before_c: World<CModel>,
    process: CPid,
    at: Time,
    event: ProcessEvent<CPid, CMessage>,
    send: Seq<(CPid, CMessage)>,
    after_c: World<CModel>,
    before_a: World<AModel>,
)
    requires
        related(before_c, before_a),
        step(
            cmodel(),
            fleet,
            before_c,
            Label::Process { process, at, event, send },
            after_c,
        ),
        client_reply(before_c.network, send),
    ensures
        exists|after_a: World<AModel>|
            #[trigger] matches(
                amodel(),
                config,
                before_a,
                Seq::<BoundaryEvent>::empty(),
                after_a,
            ) && related(after_c, after_a),
{
    let call = choose|call: Call|
        #![trigger request_carried(before_c.network, call)]
        request_carried(before_c.network, call) && (
            is_reply(send, call, echod_abstract::model::spec_unavailable(call.request)) || (
                empty_heartbeat(call) && is_reply(
                    send,
                    call,
                    Response::Status(echod_types::StatusRes { status: 200 }),
                )
            )
        );
    let slot = choose|slot: int|
        0 <= slot < before_a.process.len() && #[trigger] before_a.process[slot].0 == APid::Service;
    let state = before_a.process[slot].1;
    let shed = echod_abstract::model::spec_unavailable(call.request);
    if is_reply(send, call, shed) {
        echod_abstract::model::lemma_shed_is_last(config, state, at, call);
        let a_event = ProcessEvent::Receive {
            sender: APid::Outside,
            message: AMessage::Request(call),
        };
        let outcomes = amodel().spec_on_event(config, APid::Service, state, at, a_event);
        let index = outcomes.len() as int - 1;
        assert(outcomes[index] == echod_abstract::model::spec_shed(state, call));
        lemma_one_abstract_reply(
            config,
            before_c,
            process,
            at,
            event,
            send,
            after_c,
            before_a,
            call,
            shed,
            slot,
            index,
        );
    } else {
        let response = Response::Status(echod_types::StatusRes { status: 200 });
        assert(empty_heartbeat(call));
        assert(is_reply(send, call, response));
        echod_abstract::model::lemma_empty_heartbeat_is_first(config, state, at, call);
        lemma_one_abstract_reply(
            config,
            before_c,
            process,
            at,
            event,
            send,
            after_c,
            before_a,
            call,
            response,
            slot,
            0,
        );
    }
}

pub proof fn lemma_process_simulation(fleet: Fleet, config: ServerConfig)
    requires
        output_simulation(fleet, config),
    ensures
        process_simulation(fleet, config),
{
    assert forall|before_c: World<CModel>,
        label: Label<CPid, CMessage>,
        after_c: World<CModel>,
        before_a: World<AModel>|
        #![trigger related(before_c, before_a), step(cmodel(), fleet, before_c, label, after_c)]
        related(before_c, before_a) && step(cmodel(), fleet, before_c, label, after_c)
            && process_label(label) implies exists|after_a: World<AModel>|
            #[trigger] matches(
                amodel(),
                config,
                before_a,
                Seq::<BoundaryEvent>::empty(),
                after_a,
            ) && related(after_c, after_a) by {
        match label {
            Label::Process { process, at, event, send } => {
                if sends_client_output(send) {
                    if client_reply(before_c.network, send) {
                        lemma_client_replies(
                            fleet,
                            config,
                            before_c,
                            process,
                            at,
                            event,
                            send,
                            after_c,
                            before_a,
                        );
                    } else {
                        assert(step(
                            cmodel(),
                            fleet,
                            before_c,
                            Label::Process { process, at, event, send },
                            after_c,
                        ));
                        assert(!client_reply(before_c.network, send));
                        assert(exists|after_a: World<AModel>|
                            #[trigger] matches(
                                amodel(),
                                config,
                                before_a,
                                Seq::<BoundaryEvent>::empty(),
                                after_a,
                            ) && related(after_c, after_a));
                    }
                } else {
                    lemma_silent_process(
                        fleet,
                        config,
                        before_c,
                        process,
                        at,
                        event,
                        send,
                        after_c,
                        before_a,
                    );
                    assert(matches(
                        amodel(),
                        config,
                        before_a,
                        Seq::<BoundaryEvent>::empty(),
                        before_a,
                    ));
                    assert(related(after_c, before_a));
                }
            },
            Label::Input { .. } | Label::Outside { .. } => {
                assert(!process_label(label));
                assert(false);
            },
        }
    };
}

// ---------------------------------------------------------------------------
// Simulation, then trace inclusion
// ---------------------------------------------------------------------------

pub proof fn lemma_simulation(fleet: Fleet, config: ServerConfig)
    requires
        process_simulation(fleet, config),
    ensures
        simulation(cmodel(), fleet, amodel(), config, link()),
{
    assert forall|before_c: World<CModel>,
        label: Label<CPid, CMessage>,
        after_c: World<CModel>,
        before_a: World<AModel>|
        #![trigger link()(before_c, before_a), step(cmodel(), fleet, before_c, label, after_c)]
        link()(before_c, before_a) && step(cmodel(), fleet, before_c, label, after_c)
            implies exists|after_a: World<AModel>| #[trigger] matches(
            amodel(),
            config,
            before_a,
            cmodel().spec_observe(label),
            after_a,
        ) && link()(after_c, after_a) by {
        lemma_link(before_c, before_a);
        assert(related(before_c, before_a));
        match label {
            Label::Input { recipient, at, message } => {
                lemma_input(
                    fleet,
                    config,
                    before_c,
                    recipient,
                    at,
                    message,
                    after_c,
                    before_a,
                );
                let observed = cmodel().spec_observe(label);
                let after_a = choose|after_a: World<AModel>|
                    #![trigger matches(amodel(), config, before_a, observed, after_a)]
                    matches(amodel(), config, before_a, observed, after_a) && related(
                        after_c,
                        after_a,
                    );
                lemma_link(after_c, after_a);
            },
            Label::Outside { sender, at, message } => {
                lemma_outside(
                    fleet,
                    config,
                    before_c,
                    sender,
                    at,
                    message,
                    after_c,
                    before_a,
                );
                let observed = cmodel().spec_observe(label);
                let after_a = choose|after_a: World<AModel>|
                    #![trigger matches(amodel(), config, before_a, observed, after_a)]
                    matches(amodel(), config, before_a, observed, after_a) && related(
                        after_c,
                        after_a,
                    );
                lemma_link(after_c, after_a);
            },
            Label::Process { .. } => {
                assert(process_label(label));
                assert(exists|after_a: World<AModel>|
                    #[trigger] matches(
                        amodel(),
                        config,
                        before_a,
                        Seq::<BoundaryEvent>::empty(),
                        after_a,
                    ) && related(after_c, after_a));
                let after_a = choose|after_a: World<AModel>|
                    #![trigger matches(
                        amodel(),
                        config,
                        before_a,
                        Seq::<BoundaryEvent>::empty(),
                        after_a,
                    )]
                    matches(
                        amodel(),
                        config,
                        before_a,
                        Seq::<BoundaryEvent>::empty(),
                        after_a,
                    ) && related(after_c, after_a);
                assert(cmodel().spec_observe(label) =~= Seq::<BoundaryEvent>::empty());
                lemma_matches_same_visible(
                    config,
                    before_a,
                    Seq::<BoundaryEvent>::empty(),
                    cmodel().spec_observe(label),
                    after_a,
                );
                lemma_link(after_c, after_a);
            },
        }
    };
}

/// Concrete boundary traces are abstract boundary traces once every
/// output-emitting process step that is not a shed or an empty heartbeat
/// has its abstract execution.
pub proof fn lemma_refines(fleet: Fleet, config: ServerConfig)
    requires
        output_simulation(fleet, config),
    ensures
        refines(cmodel(), fleet, amodel(), config),
{
    lemma_initial_related(fleet, config);
    lemma_link(initial(cmodel(), fleet), initial(amodel(), config));
    lemma_process_simulation(fleet, config);
    lemma_simulation(fleet, config);
    assert(link()(initial(cmodel(), fleet), initial(amodel(), config)));
    assert(simulation(cmodel(), fleet, amodel(), config, link()));
    concrete_refines_abstract(cmodel(), fleet, amodel(), config, link());
}

} // verus!
