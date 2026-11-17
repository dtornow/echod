//! Typed production event/effect boundary for Rover.

use vstd::prelude::*;
use crate::types::{Call, DebugCall, Event, RequestEvent};
use crate::target::Target;
use crate::verified::runtime::copy;
use crate::{Config, replay::ReplayBranch};
use rover_spec::rover::comm::ProcessEvent;
use rover_spec::rover::RoverSpec::{Spec as _, Proc as _, StepResultV};
pub use echod_concrete_spec::rover::Pid;
use echod_concrete_spec::rover::{ProductionNodeSpec, ProductionFleetSpec, ProductionPublicSpec};
pub use echod_concrete_spec::state::ProductionFleetConfig;
pub use echod_types::protocol::TimedMessage as ProtocolMessage;
pub use echod_types::Output as ProtocolOutput;
pub use echod_concrete_spec::state::{ProductionPublicCall, ProductionPublicRoute};
use echod_concrete_spec::state::{ProductionFleetModel, ProductionRoutedNodeV};
use crate::concrete::store::Store;
use crate::types::{Armed, StoreReq, StoreRes, StoreError};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::handler::{
    production_route_effects, production_routed_input, production_delivery_clock,
    production_store_failure, production_fleet_store_step,
    production_public_input, production_public_admission, production_public_outputs, production_public_rejection,
    production_public_displace, production_pending_index,
};
pub use echod_concrete_spec::state::{ProductionConfigData, ProductionModelConfig, ProductionWireMessage, ProductionEffectData};
use echod_concrete_spec::state::ProductionNodeModel;
use crate::types::{Answer, DebugBody, Effect, Message};
use crate::concrete::{DocumentBody, Obj};
pub use echod_concrete_spec::state::{
    ProductionAnswerData, ProductionDebugData, ProductionDispatchData, ProductionDocumentData,
    ProductionObjectData, ProductionPromiseData, ProductionTaskData,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::handler::production_document_data_rows;
#[cfg(verus_keep_ghost)]
use crate::concrete::document::spec_from_entries;
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::property_claim::{production_document_canonical, production_debug_canonical, production_effect_canonical};
pub use echod_concrete_spec::state::{
    ProductionCallData, ProductionDebugInput, ProductionInput, ProductionTargetData,
};

verus! {
pub type ProtocolBoundary = Result<echod_types::protocol::TimedBoundaryEvent, rover_spec::rover::comm::BoundaryEvent<Pid, ProductionWireMessage>>;

pub fn protocol_observation(label: &rover_spec::rover::RoverSpec::Label<Pid, ProductionWireMessage>) -> (result: Vec<ProtocolBoundary>)
    ensures result@ == echod_concrete_spec::handler::production_protocol_observe(*label),
{
    use rover_spec::rover::RoverSpec::Label;
    use rover_spec::rover::comm::BoundaryEvent;
    let mut result = Vec::new();
    match label {
        Label::Input { recipient, at, message } => match message {
            ProductionWireMessage::PublicRequest(call) => result.push(Ok(BoundaryEvent::Input {
                recipient: (), at: *at, message: ProtocolMessage::Request(echod_types::protocol::TimedCall {
                    call: echod_types::Call { client: copy(&call.client), id: call.id, request: copy(&call.request) },
                    offered_at: call.now, pinned: call.pinned,
                }),
            })),
            _ => result.push(Err(BoundaryEvent::Input { recipient: *recipient, at: *at, message: copy(message) })),
        },
        Label::Outside { sender, at, message } => match message {
            ProductionWireMessage::PublicResult { call, response } => {
                let response = match response {
                    Ok(ProductionAnswerData::Step { response, .. }) => Some(copy(response)),
                    Err(_) => Some(crate::concrete::document::unavailable(&call.request)),
                    Ok(ProductionAnswerData::Debug { .. }) => None,
                };
                match response {
                    Some(response) => result.push(Ok(BoundaryEvent::Output {
                        sender: (), at: *at, message: ProtocolMessage::Output(echod_types::Output::Response {
                            client: copy(&call.client), id: call.id, response,
                        }),
                    })),
                    None => result.push(Err(BoundaryEvent::Output { sender: *sender, at: *at, message: copy(message) })),
                }
            },
            ProductionWireMessage::Effect(ProductionEffectData::Send { address, message: dispatch }) => {
                let dispatch = match dispatch {
                    ProductionDispatchData::Execute { task_id, version } => echod_types::Dispatch::Execute { id: copy(task_id), version: *version },
                    ProductionDispatchData::Unblock(promise) => echod_types::Dispatch::Unblock { address: copy(address), promise: copy(promise) },
                };
                result.push(Ok(BoundaryEvent::Output { sender: (), at: *at, message: ProtocolMessage::Output(echod_types::Output::Dispatch(dispatch)) }));
            },
            _ => {},
        },
        _ => {},
    }
    result
}

#[derive(Debug, PartialEq, Eq)]
pub enum FleetBridge {
    Node { core: NodeBridge, id: u64, wake: Option<(u64, Armed)>, next_request: u64, pending: Vec<ProductionPublicRoute> },
    Store(Store),
}

impl View for FleetBridge {
    type V = ProductionFleetModel;
    open spec fn view(&self) -> Self::V {
        match self {
            Self::Node { core, id, wake, next_request, pending } => ProductionFleetModel::Node(ProductionRoutedNodeV {
                node: core@, id: *id, wake: *wake, next_request: *next_request, pending: pending@,
            }),
            Self::Store(store) => ProductionFleetModel::Store(store@),
        }
    }
}

impl FleetBridge {
    pub fn copy(&self) -> (result: Self)
        ensures result@ == self@,
    {
        match self {
            Self::Node { core, id, wake, next_request, pending } => Self::Node {
                core: core.copy(), id: *id, wake: *wake, next_request: *next_request, pending: copy(pending),
            },
            Self::Store(store) => Self::Store(store.copy()),
        }
    }
}

fn delivery_clock(input: ProductionInput, now: u64) -> (result: ProductionInput)
    ensures result == production_delivery_clock(input, now),
{
    match input {
        ProductionInput::Request { call, .. } => ProductionInput::Request { clock: now, call },
        ProductionInput::Debug { call, .. } => ProductionInput::Debug { clock: now, call },
        ProductionInput::Store { op, response, .. } => ProductionInput::Store { clock: now, op, response },
        ProductionInput::Wake { armed, .. } => ProductionInput::Wake { clock: now, armed },
    }
}

fn public_input(call: ProductionPublicCall, internal: u64, now: u64) -> (result: Option<ProductionInput>)
    ensures result == production_public_input(call, internal, now),
{
    let original_target = match crate::admission::route(&call.request) { Some(target) => target, None => return None };
    let (target, request, then) = crate::admission::normalize(original_target, call.request);
    let target = target_out(target);
    proof { echod_concrete_spec::property_proof::lemma_production_lift_target_actual(target); }
    let then = match then {
        None => None,
        Some((target, request)) => {
            let target = target_out(target);
            proof { echod_concrete_spec::property_proof::lemma_production_lift_target_actual(target); }
            Some((target, request))
        },
    };
    Some(ProductionInput::Request { clock: now, call: ProductionCallData {
        id: internal, kind: call.kind, corr: call.corr, target, request, action_kind: call.action_kind,
        now: call.now, pinned: call.pinned, then,
    }})
}

fn public_rejection(event: &ProcessEvent<Pid, ProductionWireMessage>) -> (message: Option<ProductionWireMessage>)
    ensures message == production_public_rejection(*event),
{
    if let ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::PublicRequest(call) } = event {
        if crate::admission::route(&call.request).is_none() {
            let why = crate::verified::text::text("Request data does not name an id");
            proof { echod_concrete_spec::property_proof::lemma_string_of(why); }
            let answer = ProductionAnswerData::Step {
                kind: copy(&call.kind), corr: copy(&call.corr), action_kind: copy(&call.action_kind),
                response: echod_types::Response::Status(echod_types::StatusRes { status: 400 }), why: Some(why),
            };
            return Some(ProductionWireMessage::PublicResult { call: copy(call), response: Ok(answer) });
        }
    }
    None
}

fn public_displace(mut pending: Vec<ProductionPublicRoute>, internal: u64)
    -> (result: (Vec<ProductionPublicRoute>, Vec<(Pid, ProductionWireMessage)>))
    ensures (result.0@, result.1@) == production_public_displace(pending@, internal),
    decreases pending.len(),
{
    let ghost original = pending@;
    if pending.is_empty() { return (Vec::new(), Vec::new()); }
    let first = pending.remove(0);
    proof { assert(pending@ =~= original.skip(1)); }
    let (mut rest, mut send) = public_displace(pending, internal);
    if first.internal == internal {
        let error = crate::verified::text::text("node crashed");
        proof {
            echod_concrete_spec::property_proof::lemma_string_of(error);
        }
        let mut before = Vec::new();
        before.push((Pid::Outside, ProductionWireMessage::PublicResult { call: first.call, response: Err(error) }));
        before.append(&mut send);
        (rest, before)
    } else {
        let mut kept = Vec::new();
        kept.push(first);
        kept.append(&mut rest);
        (kept, send)
    }
}

fn public_admission(next: u64, pending: &Vec<ProductionPublicRoute>, event: &ProcessEvent<Pid, ProductionWireMessage>)
    -> (result: (u64, Vec<ProductionPublicRoute>, Vec<(Pid, ProductionWireMessage)>))
    ensures (result.0, result.1@, result.2@) == production_public_admission(next, pending@, *event),
{
    if let ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::PublicRequest(call) } = event {
        let (mut pending, send) = public_displace(copy(pending), next);
        pending.push(ProductionPublicRoute { internal: next, call: copy(call) });
        (next.wrapping_add(1), pending, send)
    } else { (next, copy(pending), Vec::new()) }
}

fn pending_index(mut pending: Vec<ProductionPublicRoute>, internal: u64) -> (result: Option<usize>)
    ensures
        match result {
            None => production_pending_index(pending@, internal) == None,
            Some(i) => i < pending.len() && production_pending_index(pending@, internal) == Some(i as int),
        },
    decreases pending.len(),
{
    let ghost original = pending@;
    if pending.is_empty() { return None; }
    let first = pending.remove(0);
    if first.internal == internal { return Some(0); }
    proof { assert(pending@ =~= original.skip(1)); }
    match pending_index(pending, internal) { None => None, Some(i) => Some(i + 1) }
}

fn public_outputs(mut pending: Vec<ProductionPublicRoute>, mut packets: Vec<(Pid, ProductionWireMessage)>)
    -> (result: (Vec<ProductionPublicRoute>, Vec<(Pid, ProductionWireMessage)>))
    ensures (result.0@, result.1@) == production_public_outputs(pending@, packets@),
    decreases packets.len(),
{
    let ghost original = packets@;
    if packets.is_empty() { return (pending, Vec::new()); }
    let packet = packets.remove(0);
    let packet = match packet {
        (Pid::Outside, ProductionWireMessage::Effect(ProductionEffectData::Reply { id, response })) => {
            match pending_index(copy(&pending), id) {
                None => (Pid::Outside, ProductionWireMessage::Effect(ProductionEffectData::Reply { id, response })),
                Some(i) => {
                    let route = pending.remove(i);
                    (Pid::Outside, ProductionWireMessage::PublicResult { call: route.call, response })
                },
            }
        },
        packet => packet,
    };
    proof { assert(packets@ =~= original.skip(1)); }
    let (pending, mut rest) = public_outputs(pending, packets);
    let mut send = Vec::new();
    send.push(packet);
    send.append(&mut rest);
    (pending, send)
}

fn routed_input(wake: Option<(u64, Armed)>, next: u64, now: u64, event: &ProcessEvent<Pid, ProductionWireMessage>)
    -> (result: Option<(ProductionInput, Option<(u64, Armed)>)>)
    ensures result == production_routed_input(wake, next, now, *event),
{
    match event {
        ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::PublicRequest(call) } =>
            match public_input(copy(call), next, now) { Some(input) => Some((input, wake)), None => None },
        ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::Input(input) } =>
            match input {
                ProductionInput::Request { .. } | ProductionInput::Debug { .. } => Some((delivery_clock(copy(input), now), wake)),
                _ => None,
            },
        ProcessEvent::Receive { sender: Pid::Store, message: ProductionWireMessage::StoreReply { op, response } } =>
            Some((ProductionInput::Store { clock: now, op: *op, response: copy(response) }, wake)),
        ProcessEvent::Timeout => match wake {
            Some((at, armed)) if at <= now => Some((ProductionInput::Wake { clock: now, armed }, None)),
            _ => None,
        },
        _ => None,
    }
}

fn route_effects(wake: Option<(u64, Armed)>, now: u64, mut effects: Vec<(Pid, ProductionWireMessage)>)
    -> (result: (Option<(u64, Armed)>, Vec<(Pid, ProductionWireMessage)>))
    ensures (result.0, result.1@) == production_route_effects(wake, now, effects@),
    decreases effects.len(),
{
    let ghost original = effects@;
    let ghost original_wake = wake;
    if effects.is_empty() { return (wake, Vec::new()); }
    let (pid, message) = effects.remove(0);
    let (wake, packet) = match message {
        ProductionWireMessage::Effect(ProductionEffectData::Wake { after_ms, armed }) => {
            let at = now.saturating_add(after_ms);
            (Some((at, armed)), (pid, ProductionWireMessage::Effect(ProductionEffectData::Wake { after_ms, armed })))
        },
        ProductionWireMessage::Effect(ProductionEffectData::Store { op, request }) =>
            (wake, (Pid::Store, ProductionWireMessage::StoreCall { op, request })),
        message => (wake, (pid, message)),
    };
    proof { assert(effects@ =~= original.skip(1)); }
    let (wake, mut tail) = route_effects(wake, now, effects);
    let ghost rest = tail@;
    let mut send = Vec::new();
    send.push(packet);
    send.append(&mut tail);
    proof {
        assert(send@ =~= seq![packet] + rest);
        assert((wake, send@) == production_route_effects(original_wake, now, original));
    }
    (wake, send)
}

fn store_failure(request: &StoreReq, error: String) -> (response: StoreRes)
    ensures response == production_store_failure(*request, error),
{
    let error = StoreError::Unavailable(error);
    match request {
        StoreReq::Get { .. } => StoreRes::Get { result: Err(error) },
        StoreReq::GetIfNoneMatch { .. } => StoreRes::GetIfNoneMatch { result: Err(error) },
        StoreReq::PutIfMatch { .. } => StoreRes::PutIfMatch { result: Err(error) },
        StoreReq::PutIfNoneMatch { .. } => StoreRes::PutIfNoneMatch { result: Err(error) },
        StoreReq::AppIfMatch { .. } => StoreRes::AppIfMatch { result: Err(error) },
        StoreReq::Put { .. } => StoreRes::Put { result: Err(error) },
        StoreReq::Del { .. } => StoreRes::Del { result: Err(error) },
        StoreReq::List { .. } => StoreRes::List { result: Err(error) },
        StoreReq::ListPrefixes { .. } => StoreRes::ListPrefixes { result: Err(error) },
    }
}

fn fleet_store_step(store: &Store, fault: &Option<String>, event: &ProcessEvent<Pid, ProductionWireMessage>)
    -> (results: Vec<rover_exec::ProcResult<FleetBridge>>)
    ensures results@.map_values(|r: rover_exec::ProcResult<FleetBridge>| StepResultV { state: r.state@, send: r.send@ })
        == production_fleet_store_step(store@, *fault, *event),
{
    let mut results = Vec::new();
    if let ProcessEvent::Receive { sender: Pid::Node(id), message: ProductionWireMessage::StoreCall { op, request } } = event {
        let sender = Pid::Node(*id);
        let old_event = ProcessEvent::Receive {
            sender, message: echod_concrete_spec::state::Message::StoreReq { op: *op, request: copy(request) },
        };
        let mut pairs = store.step(&old_event);
        proof {
            let expected = echod_concrete_spec::handler::spec_store(store@, old_event);
            assert(echod_concrete_spec::handler::spec_store(store@, old_event).len() == 1);
            assert(crate::concrete::rover::store_results_v(pairs@) == expected);
            assert(pairs.len() == 1);
            assert((StepResultV { state: echod_concrete_spec::state::Proc::Store(pairs[0].0@), send: pairs[0].1@ }) == expected[0]);
        }
        let (next, mut replies) = pairs.remove(0);
        let mut send = Vec::new();
        if replies.is_empty() {
            results.push(rover_exec::ProcResult { state: FleetBridge::Store(next), send, marks: Vec::new() });
        } else {
            let (_, message) = replies.remove(0);
            match message {
                echod_concrete_spec::state::Message::StoreRes { op, response } =>
                    send.push((sender, ProductionWireMessage::StoreReply { op, response })),
                _ => { assert(false); },
            }
            results.push(rover_exec::ProcResult { state: FleetBridge::Store(next.copy()), send, marks: Vec::new() });
            if let Some(error) = fault {
                let mut before = store.copy();
                before.seen.push((sender, *op));
                let response = store_failure(request, copy(error));
                let mut send = Vec::new();
                send.push((sender, ProductionWireMessage::StoreReply { op: *op, response }));
                results.push(rover_exec::ProcResult { state: FleetBridge::Store(before), send: copy(&send), marks: Vec::new() });
                results.push(rover_exec::ProcResult { state: FleetBridge::Store(next), send, marks: Vec::new() });
            }
        }
    }
    results
}

impl rover_exec::Proc for FleetBridge {
    type Spec = ProductionFleetModel;

    fn on_event(&self, config: &ProductionFleetConfig, now: u64, event: &ProcessEvent<Pid, ProductionWireMessage>)
        -> (results: Vec<rover_exec::ProcResult<Self>>)
        ensures
            results.len() == self@.on_event(*config, now, *event).len(),
            forall|i: int| 0 <= i < results.len() ==> (StepResultV { state: results[i].state@, send: results[i].send@ })
                == self@.on_event(*config, now, *event)[i],
    {
        match self {
            Self::Store(store) => fleet_store_step(store, &config.fault, event),
            Self::Node { core, id, wake, next_request, pending } => {
                let mut results = Vec::new();
                if let Some(message) = public_rejection(event) {
                    let mut send = Vec::new();
                    send.push((Pid::Outside, message));
                    results.push(rover_exec::ProcResult { state: self.copy(), send, marks: Vec::new() });
                    return results;
                }
                if let Some((input, wake)) = routed_input(*wake, *next_request, now, event) {
                    let result = core.deliver(&input);
                    let (wake, send) = route_effects(wake, now, result.send);
                    let (next_request, pending, mut before) = public_admission(*next_request, pending, event);
                    let (pending, mut send) = public_outputs(pending, send);
                    before.append(&mut send);
                    results.push(rover_exec::ProcResult {
                        state: Self::Node { core: result.state, id: *id, wake, next_request, pending }, send: before, marks: Vec::new(),
                    });
                }
                results
            },
        }
    }
}

pub struct FleetSpec;
pub struct PublicSpec;

impl rover_exec::Spec for PublicSpec {
    type Spec = ProductionPublicSpec;
    type Proc = FleetBridge;
    open spec fn spec(&self) -> ProductionPublicSpec { ProductionPublicSpec }
    fn outside(&self) -> (pid: Pid) ensures pid == self.spec().outside(), { Pid::Outside }
    fn initial(&self, config: &ProductionFleetConfig) -> (states: Vec<(Pid, FleetBridge)>)
        ensures
            states@.map_values(|e: (Pid, FleetBridge)| (e.0, e.1@)) == self.spec().processes(*config),
            states@.map_values(|e: (Pid, FleetBridge)| e.0).no_duplicates(),
            forall|i: int| 0 <= i < states.len() ==> states[i].0 != Pid::Outside,
    {
        <FleetSpec as rover_exec::Spec>::initial(&FleetSpec, config)
    }
    fn injectable(&self, config: &ProductionFleetConfig, message: &ProductionWireMessage) -> (yes: bool)
        ensures yes == self.spec().injectable(*config, *message),
    {
        matches!(message, ProductionWireMessage::PublicRequest(_))
    }
}

impl rover_exec::Spec for FleetSpec {
    type Spec = ProductionFleetSpec;
    type Proc = FleetBridge;
    open spec fn spec(&self) -> ProductionFleetSpec { ProductionFleetSpec }
    fn outside(&self) -> (pid: Pid) ensures pid == self.spec().outside(), { Pid::Outside }

    fn initial(&self, config: &ProductionFleetConfig) -> (states: Vec<(Pid, FleetBridge)>)
        ensures
            states@.map_values(|e: (Pid, FleetBridge)| (e.0, e.1@)) == self.spec().processes(*config),
            states@.map_values(|e: (Pid, FleetBridge)| e.0).no_duplicates(),
            forall|i: int| 0 <= i < states.len() ==> states[i].0 != Pid::Outside,
    {
        let mut states: Vec<(Pid, FleetBridge)> = Vec::new();
        let mut i = 0usize;
        while i < config.nodes.len()
            invariant
                i <= config.nodes.len(),
                states.len() == i,
                forall|j: int| 0 <= j < i ==> states[j].0 == Pid::Node(j as u64),
                states@.map_values(|e: (Pid, FleetBridge)| (e.0, e.1@)) == config.nodes@.take(i as int).map(
                    |j: int, node: ProductionConfigData| (Pid::Node(j as u64), echod_concrete_spec::rover::production_initial_fleet_node(node, config.loops, j as u64))),
            decreases config.nodes.len() - i,
        {
            let ghost prefix = states@;
            let ghost index = i as int;
            let branch = ReplayBranch::new(config_in(copy(&config.nodes[i])), config.loops);
            let node = FleetBridge::Node {
                core: NodeBridge { branch }, id: i as u64, wake: Some((0, Armed::Heartbeat)),
                next_request: 1, pending: Vec::new(),
            };
            proof {
                assert(node@ == echod_concrete_spec::rover::production_initial_fleet_node(config.nodes[index], config.loops, i as u64));
            }
            states.push((Pid::Node(i as u64), node));
            i += 1;
            proof {
                assert forall|j: int| 0 <= j < i implies
                    (states[j].0, states[j].1@) == (Pid::Node(j as u64), echod_concrete_spec::rover::production_initial_fleet_node(config.nodes[j], config.loops, j as u64))
                by {
                    if j < index {
                        assert(prefix.map_values(|e: (Pid, FleetBridge)| (e.0, e.1@))[j]
                            == (Pid::Node(j as u64), echod_concrete_spec::rover::production_initial_fleet_node(config.nodes[j], config.loops, j as u64)));
                    }
                }
                assert(states@.map_values(|e: (Pid, FleetBridge)| (e.0, e.1@)) =~= config.nodes@.take(i as int).map(
                    |j: int, node: ProductionConfigData| (Pid::Node(j as u64), echod_concrete_spec::rover::production_initial_fleet_node(node, config.loops, j as u64))));
            }
        }
        states.push((Pid::Store, FleetBridge::Store(Store::empty(config.appendable))));
        proof {
            assert(config.nodes@.take(config.nodes.len() as int) =~= config.nodes@);
            assert(states@.map_values(|e: (Pid, FleetBridge)| (e.0, e.1@)) =~= self.spec().processes(*config));
            assert forall|a: int, b: int| 0 <= a < b < states.len() implies states[a].0 != states[b].0 by {
                if b < config.nodes.len() { assert(a as u64 != b as u64); }
            }
            assert forall|j: int| 0 <= j < states.len() implies states[j].0 != Pid::Outside by {}
        }
        states
    }

    fn injectable(&self, config: &ProductionFleetConfig, message: &ProductionWireMessage) -> (yes: bool)
        ensures yes == self.spec().injectable(*config, *message),
    {
        matches!(message, ProductionWireMessage::PublicRequest(_) |
            ProductionWireMessage::Input(ProductionInput::Request { .. }) | ProductionWireMessage::Input(ProductionInput::Debug { .. }))
    }
}

impl Clone for FleetBridge {
    fn clone(&self) -> Self { self.copy() }
}

pub fn config_out(config: &Config) -> (data: ProductionConfigData)
    ensures data.deep_view() == config.deep_view(),
{
    ProductionConfigData {
        node_id: copy(&config.node_id), url: copy(&config.url), prefix: copy(&config.prefix),
        compact: config.compact, appendable: config.appendable, retry_timeout: config.retry_timeout,
        timer_bucket_ms: config.timer_bucket_ms, heartbeat_ms: config.heartbeat_ms, node_ttl_ms: config.node_ttl_ms,
        cache_entries: config.cache_entries, cache_bytes: config.cache_bytes, debug: config.debug,
    }
}

fn config_in(config: ProductionConfigData) -> (data: Config)
    ensures data.deep_view() == config.deep_view(),
{
    Config {
        node_id: config.node_id, url: config.url, prefix: config.prefix,
        compact: config.compact, appendable: config.appendable, retry_timeout: config.retry_timeout,
        timer_bucket_ms: config.timer_bucket_ms, heartbeat_ms: config.heartbeat_ms, node_ttl_ms: config.node_ttl_ms,
        cache_entries: config.cache_entries, cache_bytes: config.cache_bytes, debug: config.debug,
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct NodeBridge {
    branch: ReplayBranch,
}

impl View for NodeBridge {
    type V = ProductionNodeModel;
    closed spec fn view(&self) -> Self::V {
        ProductionNodeModel { core: self.branch@ }
    }
}

impl NodeBridge {
    pub fn copy(&self) -> (result: Self)
        ensures result@ == self@,
    {
        Self { branch: self.branch.copy() }
    }

    fn deliver(&self, input: &ProductionInput) -> (result: rover_exec::ProcResult<Self>)
        ensures
            (StepResultV { state: result.state@, send: result.send@ })
                == echod_concrete_spec::handler::production_node_step(self@,
                    ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::Input(*input) })[0],
    {
                let event = event_in(copy(input));
                let (branch, mut effects) = self.branch.step(&event);
                let ghost emitted = effects.deep_view();
                let mut send = Vec::new();
                while !effects.is_empty()
                    invariant
                        send.len() + effects.len() == emitted.len(),
                        effects.deep_view() == emitted.skip(send.len() as int),
                        send@ == emitted.take(send.len() as int).map_values(|e: echod_concrete_spec::state::ProductionEffectV|
                            (Pid::Outside, ProductionWireMessage::Effect(echod_concrete_spec::handler::production_lift_effect(e)))),
                    decreases effects.len(),
                {
                    let ghost i = send.len() as int;
                    let ghost before = effects@;
                    assert(before.map_values(|e: Effect| e.deep_view()) == emitted.skip(i));
                    let raw = effects.remove(0);
                    assert(raw.deep_view() == before[0].deep_view());
                    assert(emitted.skip(i)[0] == emitted[i]);
                    let output = effect_out(raw);
                    proof {
                        assert(output.deep_view() == emitted[i]);
                        echod_concrete_spec::property_proof::lemma_production_lift_actual(output);
                    }
                    send.push((Pid::Outside, ProductionWireMessage::Effect(output)));
                    proof {
                        assert(effects@ =~= before.skip(1));
                        assert(effects.deep_view() =~= before.map_values(|e: Effect| e.deep_view()).skip(1));
                        assert(emitted.skip(i).skip(1) =~= emitted.skip(i + 1));
                        assert(emitted.take(i).push(emitted[i]) =~= emitted.take(i + 1));
                    }
                }
                proof { assert(emitted.take(emitted.len() as int) =~= emitted); }
                rover_exec::ProcResult { state: NodeBridge { branch }, send, marks: Vec::new() }
    }
}

impl rover_exec::Proc for NodeBridge {
    type Spec = ProductionNodeModel;

    fn on_event(&self, config: &ProductionModelConfig, now: u64, event: &ProcessEvent<Pid, ProductionWireMessage>)
        -> (results: Vec<rover_exec::ProcResult<Self>>)
        ensures
            results.len() == self@.on_event(*config, now, *event).len(),
            forall|i: int| 0 <= i < results.len() ==> (StepResultV {
                state: results[i].state@, send: results[i].send@,
            }) == self@.on_event(*config, now, *event)[i],
    {
        let mut results = Vec::new();
        match event {
            ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::Input(input) } =>
                results.push(self.deliver(input)),
            _ => results.push(rover_exec::ProcResult { state: self.copy(), send: Vec::new(), marks: Vec::new() }),
        }
        results
    }
}

pub struct NodeSpec;

impl rover_exec::Spec for NodeSpec {
    type Spec = ProductionNodeSpec;
    type Proc = NodeBridge;

    open spec fn spec(&self) -> ProductionNodeSpec { ProductionNodeSpec }

    fn outside(&self) -> (pid: Pid)
        ensures pid == self.spec().outside(),
    { Pid::Outside }

    fn initial(&self, config: &ProductionModelConfig) -> (states: Vec<(Pid, NodeBridge)>)
        ensures
            states@.map_values(|e: (Pid, NodeBridge)| (e.0, e.1@)) == self.spec().processes(*config),
            states@.map_values(|e: (Pid, NodeBridge)| e.0).no_duplicates(),
            forall|i: int| 0 <= i < states.len() ==> states[i].0 != Pid::Outside,
    {
        let branch = ReplayBranch::new(config_in(copy(&config.node)), config.loops);
        let mut states = Vec::new();
        states.push((Pid::Node(0), NodeBridge { branch }));
        proof {
            assert(states@.map_values(|e: (Pid, NodeBridge)| (e.0, e.1@)) =~= self.spec().processes(*config));
        }
        states
    }

    fn injectable(&self, config: &ProductionModelConfig, message: &ProductionWireMessage) -> (yes: bool)
        ensures yes == self.spec().injectable(*config, *message),
    {
        matches!(message, ProductionWireMessage::Input(_))
    }
}

#[verifier::rlimit(10)]
fn object_out(object: Obj) -> (data: ProductionObjectData)
    ensures data.deep_view() == object@,
{
    let p = object.promise;
    let promise = ProductionPromiseData {
        state: p.state, param: p.param, value: p.value, tags: p.tags,
        timeout_at: p.timeout_at, created_at: p.created_at, settled_at: p.settled_at,
        callbacks: p.callbacks, listeners: p.listeners,
    };
    proof {
        assert(promise.callbacks.deep_view() =~= crate::concrete::document::strs_v(p.callbacks@));
        assert(promise.listeners.deep_view() =~= crate::concrete::document::strs_v(p.listeners@));
        assert(promise.deep_view() == p@);
    }
    let task = match object.task {
        None => None,
        Some(t) => {
            let result = ProductionTaskData {
                state: t.state, version: t.version, pid: t.pid, ttl: t.ttl,
                lease_timeout_at: t.lease_timeout_at, retry_timeout_at: t.retry_timeout_at,
                resumes: t.resumes,
            };
            proof {
                assert(result.resumes.deep_view() =~= crate::concrete::document::strs_v(t.resumes@));
                assert(result.deep_view() == t@);
            }
            Some(result)
        },
    };
    ProductionObjectData { promise, task }
}

impl Clone for NodeBridge {
    fn clone(&self) -> Self { self.copy() }
}

proof fn rows_match(entries: Seq<(String, Obj)>)
    ensures production_document_data_rows(entries.map_values(|e: (String, Obj)| (e.0@, e.1@)))
        == spec_from_entries(entries),
    decreases entries.len(),
{
    if entries.len() > 0 {
        rows_match(entries.drop_last());
        assert(entries.map_values(|e: (String, Obj)| (e.0@, e.1@)).drop_last()
            =~= entries.drop_last().map_values(|e: (String, Obj)| (e.0@, e.1@)));
    }
}

pub fn document_out(document: DocumentBody) -> (data: ProductionDocumentData)
    ensures data.deep_view() == document.deep_view(), production_document_canonical(data),
{
    match document {
        DocumentBody::Schedule(schedule) => ProductionDocumentData::Schedule(schedule),
        DocumentBody::Workflow(objects) => {
            let ghost map = objects@;
            let mut entries = objects.into_entries();
            let ghost original = entries@;
            let mut data = Vec::new();
            while !entries.is_empty()
                invariant
                    data.len() + entries.len() == original.len(),
                    entries@ == original.skip(data.len() as int),
                    data.deep_view() == original.take(data.len() as int).map_values(|e: (String, Obj)| (e.0@, e.1@)),
                decreases entries.len(),
            {
                let ghost i = data.len() as int;
                let ghost before_data = data@;
                assert(before_data.map_values(|e: (String, ProductionObjectData)| e.deep_view())
                    == original.take(i).map_values(|e: (String, Obj)| (e.0@, e.1@)));
                let (key, object) = entries.remove(0);
                let value = object_out(object);
                assert((key@, value.deep_view()) == (original[i].0@, original[i].1@));
                data.push((key, value));
                proof {
                    assert(entries@ =~= original.skip(i + 1));
                    assert(data.deep_view() =~= before_data.map_values(|e: (String, ProductionObjectData)| e.deep_view()).push((key@, value.deep_view())));
                    assert(original.take(i + 1) =~= original.take(i).push(original[i]));
                    assert(data.deep_view() =~= original.take(i + 1).map_values(|e: (String, Obj)| (e.0@, e.1@)));
                }
            }
            proof {
                assert(original.take(original.len() as int) =~= original);
                rows_match(original);
                assert(data.deep_view() == original.map_values(|e: (String, Obj)| (e.0@, e.1@)));
                assert(data.deep_view().len() == data.len());
                assert(data.len() == original.len());
                assert forall|i: int| 0 <= i < data.len() implies #[trigger] data[i].0@ == original[i].0@ by {
                    assert(data.deep_view()[i] == (original[i].0@, original[i].1@));
                    assert(data.deep_view()[i] == (data[i].0@, data[i].1.deep_view()));
                }
                assert(data@.map_values(|e: (String, ProductionObjectData)| e.0@)
                    =~= original.map_values(|e: (String, Obj)| e.0@));
                assert(production_document_data_rows(data.deep_view()) == map);
                assert(original.map_values(|e: (String, Obj)| e.0@) == echod_concrete_spec::handler::spec_sorted_present(map));
                assert forall|i: int| 0 <= i < data.len() implies {
                    let map = production_document_data_rows(data.deep_view());
                    map.contains_key(data[i].0@) && map[data[i].0@] == #[trigger] data[i].1.deep_view()
                } by {
                    assert(data.deep_view()[i] == (original[i].0@, original[i].1@));
                }
            }
            ProductionDocumentData::Workflow(data)
        },
    }
}

fn debug_out(body: DebugBody) -> (data: ProductionDebugData)
    ensures data.deep_view() == body.deep_view(), production_debug_canonical(data),
{
    match body {
        DebugBody::Object => ProductionDebugData::Object,
        DebugBody::List => ProductionDebugData::List,
        DebugBody::Message(message) => ProductionDebugData::Message(message),
        DebugBody::Snap { mut origins, schedules } => {
            let ghost original = origins.deep_view();
            let mut data = Vec::new();
            while !origins.is_empty()
                invariant
                    data.len() + origins.len() == original.len(),
                    origins.deep_view() == original.skip(data.len() as int),
                    data.deep_view() == original.take(data.len() as int),
                    forall|j: int| 0 <= j < data.len() ==> production_document_canonical(#[trigger] data[j]),
                decreases origins.len(),
            {
                let ghost i = data.len() as int;
                let ghost before_origins = origins@;
                let ghost before_data = data@;
                assert(before_origins.map_values(|d: DocumentBody| d.deep_view()) == original.skip(i));
                assert(before_data.map_values(|d: ProductionDocumentData| d.deep_view()) == original.take(i));
                let doc = origins.remove(0);
                assert(doc.deep_view() == before_origins[0].deep_view());
                assert(original.skip(i)[0] == original[i]);
                let converted = document_out(doc);
                assert(converted.deep_view() == original[i]);
                data.push(converted);
                proof {
                    assert(origins@ =~= before_origins.skip(1));
                    assert(origins.deep_view() =~= before_origins.map_values(|d: DocumentBody| d.deep_view()).skip(1));
                    assert(data.deep_view() =~= before_data.map_values(|d: ProductionDocumentData| d.deep_view()).push(converted.deep_view()));
                    assert(original.skip(i).skip(1) =~= original.skip(i + 1));
                    assert(original.take(i).push(original[i]) =~= original.take(i + 1));
                    assert(origins.deep_view() =~= original.skip(i + 1));
                    assert(data.deep_view() =~= original.take(i + 1));
                }
            }
            proof { assert(original.take(original.len() as int) =~= original); }
            ProductionDebugData::Snap { origins: data, schedules }
        },
    }
}

pub fn effect_out(effect: Effect) -> (data: ProductionEffectData)
    ensures data.deep_view() == effect.deep_view(), production_effect_canonical(data),
{
    match effect {
        Effect::Reply { id, response } => {
            let response = match response {
                Err(error) => Err(error),
                Ok(Answer::Step { kind, corr, action_kind, response, why }) =>
                    Ok(ProductionAnswerData::Step { kind, corr, action_kind, response, why }),
                Ok(Answer::Debug { kind, corr, status, body }) =>
                    Ok(ProductionAnswerData::Debug { kind, corr, status, body: debug_out(body) }),
            };
            ProductionEffectData::Reply { id, response }
        },
        Effect::Store { op, request } => ProductionEffectData::Store { op, request },
        Effect::Wake { after_ms, armed } => ProductionEffectData::Wake { after_ms, armed },
        Effect::Note(note) => ProductionEffectData::Note(note),
        Effect::Send { address, message } => {
            let message = match message {
                Message::Execute { task_id, version } => ProductionDispatchData::Execute { task_id, version },
                Message::Unblock(promise) => ProductionDispatchData::Unblock(promise),
            };
            ProductionEffectData::Send { address, message }
        },
    }
}

fn target_in(target: ProductionTargetData) -> (result: Target)
    ensures result.deep_view() == target.deep_view(),
{
    match target {
        ProductionTargetData::Origin(id) => Target::Origin(id),
        ProductionTargetData::Schedule(id) => Target::Schedule(id),
    }
}

fn target_out(target: Target) -> (result: ProductionTargetData)
    ensures result.deep_view() == target.deep_view(),
{
    match target {
        Target::Origin(id) => ProductionTargetData::Origin(id),
        Target::Schedule(id) => ProductionTargetData::Schedule(id),
    }
}

pub fn event_in(input: ProductionInput) -> (event: Event)
    ensures event.deep_view() == input.deep_view(),
{
    match input {
        ProductionInput::Request { clock, call } => {
            let then = match call.then {
                Some((target, request)) => Some((target_in(target), request)),
                None => None,
            };
            Event::Request { clock, request: RequestEvent::Protocol(Call {
                id: call.id, kind: call.kind, corr: call.corr, target: target_in(call.target),
                request: call.request, action_kind: call.action_kind, now: call.now,
                pinned: call.pinned, then,
            }) }
        },
        ProductionInput::Debug { clock, call } => {
            let call = match call {
                ProductionDebugInput::Reset { id, kind, corr } => DebugCall::Reset { id, kind, corr },
                ProductionDebugInput::Snap { id, kind, corr } => DebugCall::Snap { id, kind, corr },
                ProductionDebugInput::Tick { id, kind, corr, time } => DebugCall::Tick { id, kind, corr, time },
            };
            Event::Request { clock, request: RequestEvent::Debug(call) }
        },
        ProductionInput::Store { clock, op, response } => Event::Store { clock, op, response },
        ProductionInput::Wake { clock, armed } => Event::Wake { clock, armed },
    }
}

pub fn event_out(event: Event) -> (input: ProductionInput)
    ensures input.deep_view() == event.deep_view(),
{
    match event {
        Event::Request { clock, request: RequestEvent::Protocol(call) } => {
            let then = match call.then {
                Some((target, request)) => Some((target_out(target), request)),
                None => None,
            };
            ProductionInput::Request { clock, call: ProductionCallData {
                id: call.id, kind: call.kind, corr: call.corr, target: target_out(call.target),
                request: call.request, action_kind: call.action_kind, now: call.now,
                pinned: call.pinned, then,
            } }
        },
        Event::Request { clock, request: RequestEvent::Debug(call) } => {
            let call = match call {
                DebugCall::Reset { id, kind, corr } => ProductionDebugInput::Reset { id, kind, corr },
                DebugCall::Snap { id, kind, corr } => ProductionDebugInput::Snap { id, kind, corr },
                DebugCall::Tick { id, kind, corr, time } => ProductionDebugInput::Tick { id, kind, corr, time },
            };
            ProductionInput::Debug { clock, call }
        },
        Event::Store { clock, op, response } => ProductionInput::Store { clock, op, response },
        Event::Wake { clock, armed } => ProductionInput::Wake { clock, armed },
    }
}

}
